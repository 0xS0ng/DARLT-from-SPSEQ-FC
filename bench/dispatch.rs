//! One sequential coordinator for root and isolated native workers.
use crate::{
    experiment::Job,
    sampling::{self},
};
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    io::{BufRead, BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    time::Instant,
};

pub struct Client {
    child: Child,
    input: BufWriter<ChildStdin>,
    output: BufReader<ChildStdout>,
    pub jobs: Vec<Job>,
    pub binary: PathBuf,
    pub op_counts_enabled: bool,
}
impl Client {
    pub fn start(binary: &Path) -> Result<Self, String> {
        let mut child = Command::new(binary)
            .env("RAYON_NUM_THREADS", "1")
            .env("OMP_NUM_THREADS", "1")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("{}: {e}", binary.display()))?;
        let input = BufWriter::new(child.stdin.take().ok_or("worker stdin missing")?);
        let mut output = BufReader::new(child.stdout.take().ok_or("worker stdout missing")?);
        let handshake = (|| -> Result<(Vec<Job>, bool), String> {
            let mut line = String::new();
            output.read_line(&mut line).map_err(|e| e.to_string())?;
            let ready: Value = serde_json::from_str(&line)
                .map_err(|e| format!("worker readiness: {e}: {line}"))?;
            if ready["event"] != "ready" || ready["protocol"] != 1 {
                return Err("worker protocol mismatch".into());
            }
            let counted = ready["op_counts_enabled"]
                .as_bool()
                .ok_or("worker did not explicitly report its counter build")?;
            if counted || ready["counter_scope_active"] != false {
                return Err("native workers must explicitly report counter feature and active scopes disabled".into());
            }
            if ready["subgroup_audit_enabled"] != false {
                return Err(
                    "native timing workers must explicitly report subgroup audit disabled".into(),
                );
            }
            let jobs = serde_json::from_value(ready["jobs"].clone()).map_err(|e| e.to_string())?;
            Ok((jobs, counted))
        })();
        let (jobs, op_counts_enabled) = match handshake {
            Ok(v) => v,
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(error);
            }
        };
        Ok(Self {
            child,
            input,
            output,
            jobs,
            binary: binary.into(),
            op_counts_enabled,
        })
    }
    pub fn call(&mut self, request: &Value) -> Result<Value, String> {
        serde_json::to_writer(&mut self.input, request).map_err(|e| e.to_string())?;
        writeln!(self.input).map_err(|e| e.to_string())?;
        self.input.flush().map_err(|e| e.to_string())?;
        let mut line = String::new();
        if self
            .output
            .read_line(&mut line)
            .map_err(|e| e.to_string())?
            == 0
        {
            return Err("native worker exited before responding".into());
        }
        serde_json::from_str(&line).map_err(|e| format!("worker response: {e}: {line}"))
    }
}
impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

pub(crate) fn write(file: &mut File, row: &Value) -> Result<(), String> {
    serde_json::to_writer(&mut *file, row).map_err(|e| e.to_string())?;
    writeln!(file).map_err(|e| e.to_string())?;
    file.flush().map_err(|e| e.to_string())
}
pub(crate) fn new_file(path: &Path) -> Result<File, String> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|e| format!("{}: {e}", path.display()))
}

/// Groups competing native profiles and schemes by the same role/phase/k.
/// All workers remain idle except the one selected for the current callback.
pub fn cohort(job: &Job) -> String {
    if let Some(s) = job.boundary["cohort"].as_str() {
        return s.into();
    }
    let stage = match job.stage.as_str() {
        "preparation" => "generation_preparation",
        "online" | "online_generation" => "generation_online",
        "verification_crypto"
        | "merchant_verify"
        | "bank_verify"
        | "inclusive_verification"
        | "inclusive_reference" => "service_verification",
        "issue_receive" | "issue_accept" => "issue_accept",
        "backend" | "backend_deposit" | "backend_redeem" => "native_backend",
        "state" | "shared_state" => "shared_state",
        other => other,
    };
    let role = match stage {
        "generation_preparation" | "generation_online" | "issue_accept" | "issue_request" => {
            "holder"
        }
        "service_verification" | "strict_decoding" | "native_backend" | "shared_state" => "service",
        _ => match job.role.as_str() {
            "client" | "user" | "agent" => "holder",
            "public" => "system",
            other => other,
        },
    };
    // Fixed-dimension schemes join the default A=10 comparison schedule. This
    // is only a scheduler key: their native workload still records null attrs.
    let attributes = job.workload["attributes"].as_u64().unwrap_or(10);
    let capacity = job.workload["n"]
        .as_u64()
        .or(job.workload["capacity"].as_u64())
        .unwrap_or(1024);
    let s = job.workload["s"].as_u64().unwrap_or(16);
    let scenario = match job.workload["scenario"].as_str().unwrap_or("fresh") {
        "post_prior512" | "post_sparse512" => "matched_prior_amount512",
        other => other,
    };
    format!(
        "{stage}/{}/{role}/{}/k{}/a{attributes}/n{capacity}/s{s}/{scenario}/A{}/size{}",
        job.substage, job.cache, job.workload["k"], job.workload["agents"], job.workload["size"]
    )
}

#[derive(Default)]
struct Projection {
    jobs: usize,
    classes: BTreeMap<&'static str, usize>,
    callbacks: usize,
    native_ns: u128,
    complete_ns: u128,
}
impl Projection {
    fn add(&mut self, job: &Job, native_ns: u64, complete_ns: u64) {
        let class = match job.class {
            sampling::SampleClass::Protocol => "protocol",
            sampling::SampleClass::SlowProtocol => "slow_protocol",
            sampling::SampleClass::Primitive => "primitive",
            sampling::SampleClass::LongCallback => "long_callback",
        };
        let callbacks = job.class.warmup() + job.class.retained();
        self.jobs += 1;
        *self.classes.entry(class).or_default() += 1;
        self.callbacks += callbacks;
        self.native_ns += u128::from(native_ns) * callbacks as u128;
        self.complete_ns += u128::from(complete_ns) * callbacks as u128;
    }
    fn value(&self) -> Value {
        json!({"jobs":self.jobs,"jobs_by_sample_class":self.classes,
            "projected_callbacks_per_attempt":self.callbacks,
            "projected_native_seconds":{"one_attempt":seconds(self.native_ns),"up_to_three_attempts":seconds(3*self.native_ns)},
            "projected_complete_wall_seconds":{"one_attempt":seconds(self.complete_ns),"up_to_three_attempts":seconds(3*self.complete_ns)}})
    }
}
fn seconds(ns: u128) -> f64 {
    // Budget summaries are deliberately coarse; they cannot serve as saved
    // single-shot latency observations for a one-job group.
    (ns as f64 / 100_000_000.0).ceil() / 10.0
}

/// Immutable fixture identity, independent of k, selected algorithm/profile,
/// prior spending, role, or whether a duplicate point appears in a scan.
fn warm_config(worker: usize, job: &Job) -> String {
    if job.scheme == "LCB24" && job.stage == "calibration" {
        return format!(
            "{worker}/LCB24/calibration/{}/{}",
            job.substage, job.workload["size"]
        );
    }
    if job.scheme == "SMA²RT" && job.workload["n_per_agent"].is_number() {
        return format!(
            "{worker}/SMA²RT/provisioning/A{}/n{}",
            job.workload["agents"], job.workload["n_per_agent"]
        );
    }
    let fields = [
        "attributes",
        "actual_business_attributes",
        "n",
        "capacity",
        "s",
        "w",
        "k_max",
        "delegatable_attributes",
        "private_attributes",
        "range_bits",
        "native_capacity_parameter",
        "native_signed_coordinates",
        "period_coordinate_count",
        "authorities",
        "threshold",
    ];
    let mut dimensions: BTreeMap<_, _> = fields
        .into_iter()
        .map(|key| (key, job.workload[key].clone()))
        .collect();
    // RP's capacity-only Factory fixes 2-of-3 key generation. Lifecycle rows
    // declare these constants; presentation rows use that same instance.
    if matches!(job.scheme.as_str(), "RP23-C" | "RP23-D") {
        for (key, value) in [("threshold", 2), ("authorities", 3)] {
            if dimensions[key].is_null() {
                dimensions.insert(key, json!(value));
            }
        }
    }
    json!({"worker":worker,"scheme":job.scheme,"dimensions":dimensions}).to_string()
}
fn primer_rank(job: &Job) -> Option<(u64, usize, usize, String)> {
    if job.substage == "whole"
        && job.cache == "hot"
        && job.scheme == "SMA²RT"
        && job.workload["n_per_agent"].is_number()
        && job.stage == "provisioning_issuer"
    {
        return Some((0, 0, 0, job.id.clone()));
    }
    if job.scheme == "LCB24" && job.stage == "calibration" && job.cache == "hot" {
        return Some((0, 0, 0, job.id.clone()));
    }
    if job.substage != "whole"
        || job.cache != "hot"
        || job.boundary["safe"] == false
        || job.boundary["reference_only"] == true
        || job.workload["genuine_prior_units"].as_u64().unwrap_or(0) != 0
        || job.workload["scenario"]
            .as_str()
            .is_some_and(|v| v != "fresh")
        || !matches!(
            job.stage.as_str(),
            "verification_crypto" | "inclusive_verification" | "merchant_verify" | "bank_verify"
        )
    {
        return None;
    }
    Some((
        job.workload["k"].as_u64().unwrap_or(u64::MAX),
        usize::from(!job.profile.to_ascii_lowercase().contains("random")),
        usize::from(job.workload["ablation"] == true) + usize::from(job.id.contains("/scan/")),
        job.id.clone(),
    ))
}
fn primers(
    jobs: &[Job],
    worker_jobs: &[Vec<Job>],
    owners: &BTreeMap<String, usize>,
) -> (Vec<(usize, Job, String)>, Vec<String>) {
    let mut needed = BTreeMap::new();
    for job in jobs {
        let worker = owners[&job.id];
        needed.insert(warm_config(worker, job), worker);
    }
    let mut selected = vec![];
    let mut unmatched = vec![];
    for (config, worker) in needed {
        let choice = worker_jobs[worker]
            .iter()
            .filter(|job| warm_config(worker, job) == config)
            .filter_map(|job| primer_rank(job).map(|rank| (rank, job)))
            .min_by(|a, b| a.0.cmp(&b.0));
        if let Some((_, job)) = choice {
            selected.push((worker, job.clone(), config));
        } else {
            unmatched.push(config);
        }
    }
    (selected, unmatched)
}

/// The transport supplies one ephemeral duration. Only projected group budgets
/// and threshold identities survive this function; individual values do not.
fn estimate_jobs(
    jobs: &[Job],
    worker_jobs: &[Vec<Job>],
    owners: &BTreeMap<String, usize>,
    startup_ns: u128,
    startup_workers: &[Value],
    mut invoke: impl FnMut(usize, &Job, &str, u64) -> Result<(Value, u64), String>,
) -> Value {
    const LONG_NS: u64 = 10_000_000_000;
    let (warm, unmatched) = primers(jobs, worker_jobs, owners);
    let mut primer_ns = 0u128;
    let mut cold_long = vec![];
    let mut failed = vec![];
    for (index, (worker, job, config)) in warm.iter().enumerate() {
        eprintln!(
            "estimate primer start {}/{} {}",
            index + 1,
            warm.len(),
            job.id
        );
        let outcome = invoke(*worker, job, "clock_free", 32_100_000 + index as u64);
        if let Ok((_, wall)) = &outcome {
            primer_ns += u128::from(*wall);
            if *wall > LONG_NS {
                cold_long.push(json!({"job":job.id,"scheme":job.scheme,"config":config,"threshold":"clock_free_complete_wall_gt_10s"}));
            }
        }
        match outcome {
            Ok((result, _))
                if result["ok"] == true
                    && result["elapsed_ns"].is_null()
                    && result["timing_enabled"] == false => {}
            Ok((result, _)) => failed
                .push(json!({"job":job.id,"phase":"clock_free_primer","error":result["error"]})),
            Err(error) => {
                failed.push(json!({"job":job.id,"phase":"clock_free_primer","error":error}))
            }
        }
    }
    let mut total = Projection::default();
    let mut cohorts: BTreeMap<String, Projection> = BTreeMap::new();
    let mut axes: BTreeMap<String, BTreeMap<String, Projection>> = BTreeMap::new();
    let (mut native_long, mut complete_long) = (vec![], vec![]);
    for (index, job) in jobs.iter().enumerate() {
        eprintln!(
            "estimate callback start {}/{} {}",
            index + 1,
            jobs.len(),
            job.id
        );
        let sampled = invoke(owners[&job.id], job, "estimate", 32_200_000 + index as u64);
        let (result, wall) = match sampled {
            Ok(v) => v,
            Err(error) => {
                failed.push(json!({"job":job.id,"phase":"estimate","error":error}));
                continue;
            }
        };
        let native = if result["ok"] == true
            && result["timing_enabled"] == false
            && result["formal_samples"] == 0
            && result["value_type"] == "duration_projection_only"
        {
            result["elapsed_ns"].as_u64()
        } else {
            None
        };
        let Some(native) = native else {
            failed.push(json!({"job":job.id,"phase":"estimate","error":result["error"]}));
            continue;
        };
        drop(result);
        let identity = json!({"job":job.id,"scheme":job.scheme,"role":job.role,"stage":job.stage,"substage":job.substage,"profile":job.profile,"class":job.class,"cache":job.cache,"cohort":cohort(job)});
        if native > LONG_NS {
            native_long.push(identity.clone());
        }
        if wall > LONG_NS {
            complete_long.push(identity);
        }
        total.add(job, native, wall);
        cohorts
            .entry(cohort(job))
            .or_default()
            .add(job, native, wall);
        for (axis, label) in [
            ("scheme", &job.scheme),
            ("role", &job.role),
            ("stage", &job.stage),
            ("cache", &job.cache),
        ] {
            axes.entry(axis.into())
                .or_default()
                .entry(label.clone())
                .or_default()
                .add(job, native, wall);
        }
    }
    let oneoff = startup_ns + primer_ns;
    json!({"status":if failed.is_empty(){"ESTIMATE_COMPLETE"}else{"ESTIMATE_INCOMPLETE"},
        "value_type":"duration_projection_only","timing_enabled":false,"formal_samples":0,
        "selected_jobs":jobs.len(),"diagnostic_callbacks_completed":total.jobs,
        "single_job_durations_retained":false,"statistical_estimates_computed":false,
        "budget_resolution_seconds":0.1,"budgets_rounded_up":true,
        "dimension_tables_are_alternative_breakdowns":true,
        "sample_plan":{"warmup_per_job":sampling::WARMUP,"retained_protocol":100,"retained_slow_protocol":20,"retained_primitive":1000,"attempt_range":[1,3],"attempt_range_is_projection":true},
        "total":total.value(),
        "projected_complete_session_wall_seconds":{"one_attempt":seconds(oneoff+total.complete_ns),"up_to_three_attempts":seconds(oneoff+3*total.complete_ns)},
        "one_off":{"startup_wall_seconds":seconds(startup_ns),"startup_workers":startup_workers,
            "clock_free_primers":warm.len(),"clock_free_primers_complete_wall_seconds_including_first_callback":seconds(primer_ns),
            "startup_and_primers_wall_seconds":seconds(oneoff),"configurations_without_eligible_primer":unmatched,
            "primer_wall_gt_10s":cold_long,"multiplied_by_sample_count":false},
        "cohorts":cohorts.into_iter().map(|(k,v)|(k,v.value())).collect::<BTreeMap<_,_>>(),
        "by_dimension":axes.into_iter().map(|(axis,groups)|(axis,groups.into_iter().map(|(k,v)|(k,v.value())).collect::<BTreeMap<_,_>>())).collect::<BTreeMap<_,_>>(),
        "selected_boundary_gt_10s":native_long,"steady_complete_wall_gt_10s":complete_long,"failures":failed})
}
pub fn run(
    binaries: &[PathBuf],
    mode: &str,
    plan: &Value,
    out: &Path,
    filter: Option<&str>,
) -> Result<Value, String> {
    if mode == "formal" {
        sampling::validate_wallclock_plan(plan).map_err(|e| e.to_string())?;
    }
    if !["inventory", "plan", "check", "estimate", "formal"].contains(&mode) {
        return Err("dispatch mode must be inventory/plan/check/estimate/formal".into());
    }
    fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let mut estimate_output = if mode == "estimate" {
        Some(new_file(&out.join("estimate_summary.json"))?)
    } else {
        None
    };
    let mut clients = vec![];
    let mut all = vec![];
    let mut owners = BTreeMap::new();
    let mut startup_ns = 0u128;
    let mut startup_workers = vec![];
    for binary in binaries {
        let startup = Instant::now();
        let client = Client::start(binary)?;
        if mode == "estimate" {
            let elapsed = startup.elapsed().as_nanos();
            startup_ns += elapsed;
            startup_workers.push(json!({"worker":binary.file_name().map(|s|s.to_string_lossy()),"wall_seconds":seconds(elapsed),"wall_gt_10s":elapsed>10_000_000_000}));
        }
        for job in &client.jobs {
            if owners.insert(job.id.clone(), clients.len()).is_some() {
                return Err(format!("duplicate native job {}", job.id));
            }
            if filter.is_none_or(|s| job.id.contains(s) || job.scheme == s) {
                all.push(job.clone());
            }
        }
        clients.push(client);
    }
    if all.is_empty() {
        return Err("no native jobs selected".into());
    }
    let fingerprints:Vec<_>=clients.iter().map(|client|{use sha2::Digest;let bytes=fs::read(&client.binary).map_err(|e|e.to_string())?;Ok(json!({"file":client.binary.file_name().map(|s|s.to_string_lossy()),"schemes":client.jobs.iter().map(|j|j.scheme.as_str()).collect::<std::collections::BTreeSet<_>>(),"sha256":format!("{:x}",sha2::Sha256::digest(bytes)),"op_counts_enabled":client.op_counts_enabled,"counter_scope_active":false}))}).collect::<Result<_,String>>()?;
    if mode == "plan" {
        let bindings = crate::campaign::plan(&all);
        let audit = crate::campaign::audit(&bindings);
        write(
            &mut new_file(&out.join("paper_task_map.json"))?,
            &json!({"bindings":bindings,"audit":audit,"worker_binaries":fingerprints,"plan":plan}),
        )?;
        write(&mut new_file(&out.join("summary.json"))?, &audit)?;
        return Ok(audit);
    }
    if mode == "formal" {
        let bindings = crate::campaign::plan(&all);
        return crate::pipeline_dispatch::run_formal(
            &mut clients,
            &owners,
            &bindings,
            plan,
            out,
            &json!(fingerprints),
        );
    }
    if mode == "estimate" {
        let worker_jobs = clients
            .iter()
            .map(|client| client.jobs.clone())
            .collect::<Vec<_>>();
        let mut summary = estimate_jobs(
            &all,
            &worker_jobs,
            &owners,
            startup_ns,
            &startup_workers,
            |worker, job, mode, trial| {
                let start = Instant::now();
                let result = clients[worker]
                    .call(&json!({"command":"run","job":job.id,"trial":trial,"mode":mode}))?;
                let complete =
                    u64::try_from(start.elapsed().as_nanos()).map_err(|e| e.to_string())?;
                Ok((result, complete))
            },
        );
        summary["worker_binaries"] = json!(fingerprints);
        summary["filter"] = json!(filter);
        write(
            estimate_output.as_mut().ok_or("estimate output missing")?,
            &summary,
        )?;
        return Ok(
            json!({"status":summary["status"],"selected_jobs":all.len(),"diagnostic_callbacks_completed":summary["diagnostic_callbacks_completed"],"timing_enabled":false,"formal_samples":0,"value_type":"duration_projection_only","summary":"estimate_summary.json"}),
        );
    }
    let inventory = json!({"protocol":1,"jobs":all,"worker_binaries":fingerprints,"plan":plan,"mode":mode,"timing_enabled":false,"formal_samples":0});
    let mut inventory_file = new_file(&out.join("inventory.json"))?;
    write(&mut inventory_file, &inventory)?;
    if mode == "inventory" {
        return Ok(json!({"status":"INVENTORY","jobs":all.len(),"formal_samples":0}));
    }
    let mut raw = new_file(&out.join("raw.jsonl"))?;
    let mut completed = 0usize;
    if mode == "check" {
        for (index, job) in all.iter().enumerate() {
            let result = clients[*owners.get(&job.id).ok_or("job owner missing")?]
                .call(&json!({"command":"run","job":job.id,"trial":index,"mode":"clock_free"}))?;
            write(
                &mut raw,
                &json!({"job":job,"observation":result,"timing_enabled":false,"formal_samples":0}),
            )?;
            if result["ok"] != true || !result["elapsed_ns"].is_null() {
                return Err(format!(
                    "native correctness job failed: {}: {result}",
                    job.id
                ));
            }
            completed += 1;
            eprintln!("native check {completed}/{} {}", all.len(), job.id);
        }
        let result = json!({"status":"PASS","executed_native_jobs":completed,"formal_samples":0,"timing_enabled":false});
        write(&mut new_file(&out.join("summary.json"))?, &result)?;
        return Ok(result);
    }
    Err("unsupported execution mode".into())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn synthetic_estimate_budgets_keep_classes_and_one_off_costs_separate() {
        let mut protocol = Job::new("small", "Dummy", "verifier", "verification_crypto");
        protocol.workload = json!({"k":1,"attributes":10});
        let mut slow = protocol.clone();
        slow.id = "slow".into();
        slow.stage = "preparation".into();
        slow.class = sampling::SampleClass::SlowProtocol;
        let mut primitive = slow.clone();
        primitive.id = "primitive".into();
        primitive.class = sampling::SampleClass::Primitive;
        let jobs = vec![protocol, slow, primitive];
        let owners = jobs.iter().map(|j| (j.id.clone(), 0)).collect();
        let mut calls = vec![];
        let result = estimate_jobs(
            &jobs,
            std::slice::from_ref(&jobs),
            &owners,
            4_000_000_000,
            &[],
            |_, job, mode, _| {
                calls.push((job.id.clone(), mode.to_string()));
                Ok(if mode == "clock_free" {
                    (
                        json!({"ok":true,"elapsed_ns":null,"timing_enabled":false}),
                        5_000_000_000,
                    )
                } else {
                    (
                        json!({"ok":true,"elapsed_ns":2_000_000_000u64,"timing_enabled":false,"formal_samples":0,"value_type":"duration_projection_only"}),
                        3_000_000_000,
                    )
                })
            },
        );
        assert_eq!(calls.len(), 4);
        assert_eq!(calls.iter().filter(|(_, m)| m == "clock_free").count(), 1);
        assert_eq!(result["total"]["projected_callbacks_per_attempt"], 1150);
        assert_eq!(
            result["total"]["projected_native_seconds"]["one_attempt"],
            2300.0
        );
        assert_eq!(
            result["total"]["projected_complete_wall_seconds"]["one_attempt"],
            3450.0
        );
        assert_eq!(
            result["projected_complete_session_wall_seconds"]["one_attempt"],
            3459.0
        );
        assert_eq!(
            result["projected_complete_session_wall_seconds"]["up_to_three_attempts"],
            10359.0
        );
        assert_eq!(result["cohorts"].as_object().unwrap().len(), 2);
        assert_eq!(result["formal_samples"], 0);
        let out =
            std::env::temp_dir().join(format!("native-estimate-synthetic-{}", std::process::id()));
        fs::create_dir(&out).unwrap();
        write(
            &mut new_file(&out.join("estimate_summary.json")).unwrap(),
            &result,
        )
        .unwrap();
        assert!(new_file(&out.join("estimate_summary.json")).is_err());
        let files = fs::read_dir(&out)
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        assert_eq!(files, ["estimate_summary.json"]);
        let text = fs::read_to_string(out.join("estimate_summary.json")).unwrap();
        for forbidden in [
            "\"elapsed_ns\"",
            "\"segments_ns\"",
            "\"mean_ns\"",
            "\"sample_sd_ns\"",
            "\"cv\"",
            "\"attempts\"",
        ] {
            assert!(!text.contains(forbidden));
        }
        fs::remove_dir_all(out).unwrap();
    }
    #[test]
    fn primers_deduplicate_configs_and_cover_native_lazy_caches() {
        let mut spec = Job::new("spec", "Dummy", "verifier", "verification_crypto");
        spec.workload = json!({"k":1,"attributes":10});
        let mut random = spec.clone();
        random.id = "random".into();
        random.profile = "Randomized".into();
        let mut scan = random.clone();
        scan.id = "scan/duplicate".into();
        let mut prior = random.clone();
        prior.id = "prior".into();
        prior.workload["scenario"] = json!("post_prior512");
        let mut distinct = random.clone();
        distinct.id = "scan/new-config".into();
        distinct.workload = json!({"k":16,"attributes":5});
        let mut missing = distinct.clone();
        missing.id = "unmatched".into();
        missing.workload["attributes"] = json!(99);
        missing.stage = "preparation".into();
        let mut jobs = vec![spec, random, scan, prior, distinct, missing];
        for size in [4, 8] {
            for backend in ["ark", "blstrs"] {
                let mut j = Job::new(
                    &format!("cal/{size}/{backend}"),
                    "LCB24",
                    "system",
                    "calibration",
                );
                j.substage = "G1_MSM".into();
                j.workload = json!({"size":size});
                jobs.push(j);
            }
        }
        for agents in [1, 2] {
            for stage in ["provisioning_issuer", "provisioning_system"] {
                let mut j = Job::new(&format!("sma/{agents}/{stage}"), "SMA²RT", "issuer", stage);
                j.workload = json!({"agents":agents,"n_per_agent":1024/agents});
                jobs.push(j);
            }
        }
        let mut separate = jobs[1].clone();
        separate.id = "worker2/random".into();
        let mut owners: BTreeMap<_, _> = jobs.iter().map(|j| (j.id.clone(), 0)).collect();
        owners.insert(separate.id.clone(), 1);
        let inventory = vec![jobs.clone(), vec![separate.clone()]];
        jobs.push(separate);
        let (warm, unmatched) = primers(&jobs, &inventory, &owners);
        assert_eq!(warm.len(), 7);
        assert_eq!(unmatched.len(), 1);
        let ids = warm
            .iter()
            .map(|(_, j, _)| j.id.as_str())
            .collect::<Vec<_>>();
        assert!(ids.contains(&"random"));
        assert!(ids.contains(&"scan/new-config"));
        assert!(!ids.contains(&"scan/duplicate"));
        assert!(!ids.contains(&"prior"));
        assert_eq!(ids.iter().filter(|id| id.starts_with("cal/")).count(), 2);
        assert_eq!(ids.iter().filter(|id| id.starts_with("sma/")).count(), 2);
        assert!(ids
            .iter()
            .filter(|id| id.starts_with("sma/"))
            .all(|id| id.ends_with("provisioning_issuer")));
        let (filtered, unmatched) = primers(&jobs[4..5], &inventory, &owners);
        assert_eq!(filtered.len(), 1);
        assert!(unmatched.is_empty());
        assert_eq!(filtered[0].1.id, "scan/new-config");
        let mut rp_setup = Job::new("rp/setup", "RP23-C", "public", "setup");
        rp_setup.workload = json!({"capacity":1024,"threshold":2,"authorities":3});
        let mut rp_verify = Job::new("rp/verify", "RP23-C", "merchant", "merchant_verify");
        rp_verify.workload = json!({"capacity":1024,"k":1});
        assert_eq!(warm_config(1, &rp_setup), warm_config(1, &rp_verify));
    }
    #[test]
    fn synthetic_long_job_lists_keep_identities_without_individual_durations() {
        let mut job = Job::new("long", "Dummy", "verifier", "verification_crypto");
        job.workload = json!({"k":1});
        let owners = BTreeMap::from([(job.id.clone(), 0)]);
        let result = estimate_jobs(
            &[job.clone()],
            &[vec![job]],
            &owners,
            0,
            &[],
            |_, _, mode, _| {
                Ok(if mode == "clock_free" {
                    (
                        json!({"ok":true,"elapsed_ns":null,"timing_enabled":false}),
                        11_000_000_000,
                    )
                } else {
                    (
                        json!({"ok":true,"elapsed_ns":11_000_000_000u64,"timing_enabled":false,"formal_samples":0,"value_type":"duration_projection_only"}),
                        12_000_000_000,
                    )
                })
            },
        );
        for key in ["selected_boundary_gt_10s", "steady_complete_wall_gt_10s"] {
            let row = &result[key][0];
            assert_eq!(row["job"], "long");
            assert!(row.get("elapsed_ns").is_none());
            assert!(row.get("seconds").is_none());
        }
        assert_eq!(
            result["one_off"]["primer_wall_gt_10s"]
                .as_array()
                .unwrap()
                .len(),
            1
        );
    }
    #[test]
    fn native_profiles_share_the_same_cohort() {
        let mut a = Job::new("a", "DARLT", "verifier", "inclusive_verification");
        a.workload = json!({"k":16,"attributes":10});
        let mut b = a.clone();
        b.id = "b".into();
        b.scheme = "SMA²RT".into();
        b.profile = "Randomized".into();
        assert_eq!(cohort(&a), cohort(&b));
        b.workload["k"] = json!(64);
        assert_ne!(cohort(&a), cohort(&b));
    }
    #[test]
    fn formal_dispatch_rejects_before_starting_any_worker() {
        let d = std::env::temp_dir().join("native-rejected-formal-dispatch");
        let r = run(
            &[PathBuf::from("/does/not/exist")],
            "formal",
            &json!({"timing_enabled":false}),
            &d,
            None,
        );
        assert!(r.unwrap_err().contains("not ready/authorized"));
        assert!(!d.exists());
    }
    #[test]
    fn native_role_and_stage_names_join_the_main_cross_scheme_schedule() {
        let mut token = Job::new("token", "DARLT", "verifier", "inclusive_verification");
        token.workload = json!({"k":16,"attributes":10,"n":1024,"s":16});
        let mut cash = Job::new("cash", "RP23-D", "merchant", "merchant_verify");
        cash.workload = json!({"k":16,"capacity":1024,"scenario":"fresh"});
        let mut bank = Job::new("bank", "LCB24", "bank", "bank_verify");
        bank.workload = json!({"k":16,"capacity":1024,"scenario":"fresh"});
        assert_eq!(cohort(&token), cohort(&cash));
        assert_eq!(cohort(&token), cohort(&bank));
        token.stage = "online_generation".into();
        token.role = "agent".into();
        cash.stage = "online".into();
        cash.role = "client".into();
        assert_eq!(cohort(&token), cohort(&cash));
    }
    #[test]
    fn received_byte_decoding_is_separate_and_role_normalized() {
        let mut token = Job::new("decode", "DARLT", "verifier", "strict_decoding");
        token.workload = json!({"k":16,"attributes":10,"n":1024,"s":16});
        token.boundary = json!({"decode_only":true});
        let mut cash = Job::new("cash", "RP23-D", "merchant", "strict_decoding");
        cash.workload = json!({"k":16,"capacity":1024,"scenario":"fresh"});
        let mut bank = Job::new("bank", "LCB24", "bank", "strict_decoding");
        bank.workload = cash.workload.clone();
        assert_eq!(cohort(&token), cohort(&cash));
        assert_eq!(cohort(&token), cohort(&bank));
        token.stage = "verification_crypto".into();
        assert_ne!(cohort(&token), cohort(&cash));
    }
}
