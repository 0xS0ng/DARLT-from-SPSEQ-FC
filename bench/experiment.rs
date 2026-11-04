//! Native experiment workers. Only the selected protocol boundary is timed;
//! fixture work, IPC and result serialization are outside that boundary.
use crate::sampling::{self, SampleClass};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::io::{self, BufRead, Write};
use std::time::Instant;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Job {
    pub id: String,
    pub scheme: String,
    pub role: String,
    pub stage: String,
    pub substage: String,
    pub cache: String,
    pub profile: String,
    pub workload: Value,
    pub boundary: Value,
    pub class: SampleClass,
}
impl Job {
    pub fn new(id: &str, scheme: &str, role: &str, stage: &str) -> Self {
        Self {
            id: id.into(),
            scheme: scheme.into(),
            role: role.into(),
            stage: stage.into(),
            substage: "whole".into(),
            cache: "hot".into(),
            profile: "Specification".into(),
            workload: json!({}),
            boundary: json!({}),
            class: SampleClass::Protocol,
        }
    }
}

/// Reject an inconsistent published verification boundary before a worker can
/// accept any run request. Native callback tests establish the corresponding
/// byte-processing behavior; these labels keep dispatch/export in agreement.
pub fn validate_verification_boundaries(jobs: &[Job]) -> Result<(), String> {
    let is_verification = |stage: &str| {
        matches!(
            stage,
            "verification_crypto"
                | "inclusive_verification"
                | "merchant_verify"
                | "bank_verify"
                | "inclusive_reference"
                | "native_read"
                | "identify"
        )
    };
    let mut verifiers = std::collections::BTreeSet::new();
    let mut decoders = std::collections::BTreeSet::new();
    for job in jobs {
        let decoding = job.boundary["decode_only"] == true;
        if decoding != (job.stage == "strict_decoding") {
            return Err(format!("{}: decode-only label and stage disagree", job.id));
        }
        if !decoding && !is_verification(&job.stage) {
            continue;
        }
        for flag in [
            "strict_decoding_included",
            "received_bytes_first",
            "subgroup_checks_included",
            "native_format_checks_included",
        ] {
            if job.boundary[flag] != true {
                return Err(format!("{}: verification boundary missing {flag}", job.id));
            }
        }
        if job.boundary["subgroup_checks_per_received_element"] != 1
            || job.boundary["received_input_provenance"] != "sealed_checked_input"
        {
            return Err(format!(
                "{}: verification requires one subgroup check and sealed received input",
                job.id
            ));
        }
        if decoding {
            if job.boundary["parent_verification_stage"].as_str().is_none() {
                return Err(format!("{}: decode-only parent stage missing", job.id));
            }
            decoders.insert(job.scheme.as_str());
        } else {
            verifiers.insert(job.scheme.as_str());
        }
    }
    if let Some(scheme) = verifiers.difference(&decoders).next() {
        return Err(format!(
            "{scheme}: verification has no independent strict decoding job"
        ));
    }
    Ok(())
}

pub type Action = Box<dyn FnOnce(&mut BoundaryClock) -> Result<Value, String>>;
pub trait Worker {
    fn jobs(&self) -> Vec<Job>;
    fn prepare(&mut self, id: &str, trial: u64) -> Result<Action, String>;
    fn prepare_pipeline(&mut self, ids: &[String], trial: u64) -> Result<Action, String> {
        if ids.len() == 1 {
            self.prepare(&ids[0], trial)
        } else {
            Err("worker has no multi-stage pipeline implementation".into())
        }
    }
    fn counter_scope_active(&self) -> bool {
        baseline_core::arithmetic::counts_active()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RunMode {
    ClockFree,
    Profile,
    Estimate,
    Formal,
}

/// Several disjoint live-interaction segments may belong to one role. Their
/// actual measured durations are summed; counterpart work between them is
/// excluded. No group counters are enabled by this recorder.
pub struct BoundaryClock {
    mode: RunMode,
    plan: Option<Value>,
    active: bool,
    segments: Vec<Option<u64>>,
    details: Vec<Value>,
    captures: std::collections::BTreeMap<String, Value>,
    darlt_details: bool,
}
impl BoundaryClock {
    pub fn new(mode: RunMode, plan: Option<Value>) -> Result<Self, String> {
        if mode == RunMode::Formal && cfg!(feature = "subgroup-audit") {
            return Err("formal sampling rejects a subgroup-audit build".into());
        }
        if mode == RunMode::Formal {
            sampling::validate_wallclock_plan(plan.as_ref().ok_or("formal plan missing")?)
                .map_err(|e| e.to_string())?;
        }
        Ok(Self {
            mode,
            plan,
            active: false,
            segments: vec![],
            details: vec![],
            captures: std::collections::BTreeMap::new(),
            darlt_details: false,
        })
    }
    fn check(&self) -> Result<(), String> {
        if self.mode == RunMode::Formal {
            sampling::validate_wallclock_plan(self.plan.as_ref().ok_or("formal plan missing")?)
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    }
    #[inline(never)]
    pub fn measure<T>(&mut self, action: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        if self.active {
            return Err("nested native timing boundary".into());
        }
        self.check()?;
        self.active = true;
        let _audit_region = crate::subgroup_audit::selected();
        let start = (self.mode != RunMode::ClockFree).then(Instant::now);
        use crate::darlt::instrumentation::{self, Mode};
        let collected = if instrumentation::is_collecting() {
            None
        } else {
            Some(if self.mode == RunMode::ClockFree {
                Mode::ClockFree
            } else if self.mode == RunMode::Formal {
                Mode::AuthorizedBoundary
            } else {
                Mode::DevelopmentProfile
            })
        };
        let (result, report) = if let Some(mode) = collected {
            let (result, report) = instrumentation::collect_boundary(
                mode,
                self.darlt_details,
                self.plan.as_ref(),
                action,
            )?;
            (result, Some(report))
        } else {
            (action(), None)
        };
        let elapsed = start
            .map(|s| u64::try_from(s.elapsed().as_nanos()).map_err(|e| e.to_string()))
            .transpose()?;
        self.active = false;
        self.segments.push(elapsed);
        if let Some(report) = report {
            let difference = elapsed
                .zip(report.partition_sum_ns)
                .map(|(total, sum)| i128::from(total) - i128::from(sum));
            self.details.push(json!({"same_execution":true,"report":report,
                "boundary_total_ns":elapsed,"outer_minus_partition_sum_ns":difference,
                "difference_scope":"outer recorder setup/finalization; consecutive inner intervals have no omitted gaps"}));
        }
        self.check()?;
        result
    }
    pub fn segments(&self) -> &[Option<u64>] {
        &self.segments
    }
    pub fn mode(&self) -> RunMode {
        self.mode
    }
    pub fn set_darlt_details(&mut self, enabled: bool) {
        self.darlt_details = enabled;
    }
    pub fn observations(&self) -> &std::collections::BTreeMap<String, Value> {
        &self.captures
    }
    /// Capture one native stage. Several live-interaction legs with the same
    /// job ID append disjoint segments to one observation, without replay.
    pub fn capture<T>(
        &mut self,
        job_id: &str,
        action: impl FnOnce(&mut BoundaryClock) -> Result<T, String>,
    ) -> Result<T, String> {
        if self.active {
            return Err("pipeline capture inside an active boundary".into());
        }
        let mut clock = Self::new(self.mode, self.plan.clone())?;
        clock.darlt_details = self.darlt_details;
        let result = action(&mut clock);
        if clock.segments.is_empty() {
            return Err(format!("{job_id}: pipeline stage has no native boundary"));
        }
        let observed = json!({"ok":result.is_ok(),"error":result.as_ref().err(),
            "elapsed_ns":clock.elapsed_ns(),"segments_ns":clock.segments,
            "segment_count":clock.segments.len(),"darlt_spans":clock.details,
            "same_execution":true,"derived":false});
        if let Some(previous) = self.captures.get_mut(job_id) {
            let ns = previous["elapsed_ns"]
                .as_u64()
                .zip(observed["elapsed_ns"].as_u64())
                .and_then(|(a, b)| a.checked_add(b));
            previous["elapsed_ns"] = json!(ns);
            previous["ok"] = json!(previous["ok"] == true && observed["ok"] == true);
            for key in ["segments_ns", "darlt_spans"] {
                previous[key]
                    .as_array_mut()
                    .ok_or("invalid stored pipeline observation")?
                    .extend(
                        observed[key]
                            .as_array()
                            .ok_or("invalid pipeline observation")?
                            .iter()
                            .cloned(),
                    );
            }
            previous["segment_count"] = json!(previous["segments_ns"]
                .as_array()
                .ok_or("segments missing")?
                .len());
            if result.is_err() {
                previous["error"] = observed["error"].clone();
            }
        } else {
            self.captures.insert(job_id.to_owned(), observed);
        }
        result
    }
    /// An overlapping report component from this same execution, never another
    /// native validation and never a difference of independently sampled means.
    pub fn capture_alias(
        &mut self,
        job_id: &str,
        source_job: &str,
        component: &str,
    ) -> Result<(), String> {
        let source = self
            .captures
            .get(source_job)
            .ok_or("alias source missing")?
            .clone();
        if component == "whole" {
            let mut alias = source;
            alias["derived"] = json!(true);
            alias["source_job"] = json!(source_job);
            alias["component"] = json!(component);
            self.captures.insert(job_id.to_owned(), alias);
            return Ok(());
        }
        let mut found = false;
        let mut total = (self.mode != RunMode::ClockFree).then_some(0u64);
        for span in source["darlt_spans"]
            .as_array()
            .ok_or("alias spans missing")?
        {
            for row in span["report"]["rows"]
                .as_array()
                .ok_or("alias report missing")?
            {
                if row["name"] == component {
                    found = true;
                    total = total
                        .zip(row["inclusive_ns"].as_u64())
                        .and_then(|(a, b)| a.checked_add(b));
                }
            }
        }
        if !found {
            return Err(format!(
                "{source_job}: component {component} was not executed"
            ));
        }
        self.captures.insert(
            job_id.to_owned(),
            json!({"ok":source["ok"],"error":source["error"],
            "elapsed_ns":total,"segments_ns":[total],"segment_count":1,"darlt_spans":[],
            "same_execution":true,"derived":true,"source_job":source_job,"component":component}),
        );
        Ok(())
    }
    /// Independent DARLT detail run. Main whole-stage jobs do not activate
    /// inner clocks. This records the actual selected span, never the total
    /// callback duration as a substitute for a missing component.
    pub fn measure_darlt_substage<T>(
        &mut self,
        name: &str,
        exclusive: bool,
        action: impl FnOnce() -> Result<T, String>,
    ) -> Result<T, String> {
        use crate::darlt::instrumentation::{self, Mode};
        if self.active {
            return Err("nested native timing boundary".into());
        }
        self.check()?;
        self.active = true;
        let _audit_region = crate::subgroup_audit::selected();
        let collected = if self.mode == RunMode::Formal {
            instrumentation::collect_authorized(
                self.plan.as_ref().ok_or("formal plan missing")?,
                action,
            )
        } else {
            instrumentation::collect(
                if self.mode == RunMode::ClockFree {
                    Mode::ClockFree
                } else {
                    Mode::DevelopmentProfile
                },
                action,
            )
        };
        self.active = false;
        let (result, report) = collected?;
        let ns = report.duration(name, exclusive)?;
        self.segments.push(ns);
        self.details
            .push(json!({"selected":name,"exclusive":exclusive,"report":report}));
        self.check()?;
        result
    }
    pub fn elapsed_ns(&self) -> Option<u64> {
        if self.mode == RunMode::ClockFree || self.segments.is_empty() {
            None
        } else {
            self.segments
                .iter()
                .try_fold(0u64, |sum, x| sum.checked_add((*x)?))
        }
    }
}

pub struct Composite {
    workers: Vec<Box<dyn Worker>>,
    jobs: Vec<Job>,
    owners: std::collections::BTreeMap<String, usize>,
}
impl Composite {
    pub fn new(workers: Vec<Box<dyn Worker>>) -> Result<Self, String> {
        let mut owners = std::collections::BTreeMap::new();
        let mut jobs = vec![];
        for (index, worker) in workers.iter().enumerate() {
            for job in worker.jobs() {
                if owners.insert(job.id.clone(), index).is_some() {
                    return Err(format!("duplicate job {}", job.id));
                }
                jobs.push(job);
            }
        }
        Ok(Self {
            workers,
            jobs,
            owners,
        })
    }
}
impl Worker for Composite {
    fn jobs(&self) -> Vec<Job> {
        self.jobs.clone()
    }
    fn counter_scope_active(&self) -> bool {
        self.workers
            .iter()
            .any(|worker| worker.counter_scope_active())
    }
    fn prepare(&mut self, id: &str, trial: u64) -> Result<Action, String> {
        let index = *self
            .owners
            .get(id)
            .ok_or_else(|| format!("unknown job {id}"))?;
        self.workers[index].prepare(id, trial)
    }
    fn prepare_pipeline(&mut self, ids: &[String], trial: u64) -> Result<Action, String> {
        let first = ids.first().ok_or("empty pipeline")?;
        let index = *self.owners.get(first).ok_or("unknown pipeline job")?;
        if ids.iter().any(|id| self.owners.get(id) != Some(&index)) {
            return Err("pipeline crosses native worker owners".into());
        }
        self.workers[index].prepare_pipeline(ids, trial)
    }
}

fn mode(value: &Value) -> Result<RunMode, String> {
    match value.as_str().unwrap_or("clock_free") {
        "clock_free" => Ok(RunMode::ClockFree),
        "profile" => Ok(RunMode::Profile),
        "estimate" => Ok(RunMode::Estimate),
        "formal" => Ok(RunMode::Formal),
        _ => Err("unknown execution mode".into()),
    }
}
fn execute(action: Action, request: &Value) -> Result<Value, String> {
    let mode = mode(&request["mode"])?;
    let plan = (!request["plan"].is_null()).then(|| request["plan"].clone());
    let mut clock = BoundaryClock::new(mode, plan)?;
    let result = action(&mut clock);
    if clock.segments.is_empty() && clock.captures.is_empty() {
        return Err("native job did not execute a measurement boundary".into());
    }
    Ok(
        json!({"ok":result.is_ok(),"result":result.as_ref().ok(),"error":result.as_ref().err(),
        "elapsed_ns":clock.elapsed_ns(),"segments_ns":clock.segments(),"segment_count":clock.segments.len(),
        "darlt_spans":clock.details,
        "pipeline_observations":clock.captures,
        "timing_enabled":mode==RunMode::Formal,"formal_samples":usize::from(mode==RunMode::Formal && request["sample_phase"]=="retained"),
        "value_type":if mode==RunMode::Estimate {"duration_projection_only"} else if mode==RunMode::Profile {"development_profiler_only"} else if mode==RunMode::Formal {"native_boundary_sample"} else {"native_callback_correctness"}}),
    )
}

/// JSON-lines IPC. Every worker measures its own native callback, so the
/// coordinator never includes subprocess or pipe latency in protocol time.
pub fn serve(mut worker: impl Worker) -> Result<(), String> {
    let jobs = worker.jobs();
    validate_verification_boundaries(&jobs)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    writeln!(out,"{}",json!({"event":"ready","protocol":1,"jobs":jobs,"timing_enabled":false,"op_counts_enabled":cfg!(feature="op-counts"),"subgroup_audit_enabled":cfg!(feature="subgroup-audit"),"counter_scope_active":worker.counter_scope_active()}))
        .map_err(|e|e.to_string())?;
    out.flush().map_err(|e| e.to_string())?;
    let mut pending: Option<Action> = None;
    for line in io::stdin().lock().lines() {
        let line = line.map_err(|e| e.to_string())?;
        let response = (|| -> Result<Value, String> {
            let request: Value = serde_json::from_str(&line).map_err(|e| e.to_string())?;
            let command = request["command"].as_str().ok_or("command missing")?;
            if worker.counter_scope_active() {
                return Err("native worker has an active operation-counter scope".into());
            }
            match command {
                "inventory" => Ok(json!({"ok":true,"jobs":worker.jobs()})),
                "pipeline" => {
                    if mode(&request["mode"])? == RunMode::Formal {
                        if cfg!(feature = "subgroup-audit") {
                            return Err("formal sampling rejects subgroup audit".into());
                        }
                        sampling::validate_wallclock_plan(&request["plan"])
                            .map_err(|e| e.to_string())?;
                    }
                    let ids: Vec<String> = serde_json::from_value(request["jobs"].clone())
                        .map_err(|e| e.to_string())?;
                    if ids.is_empty() {
                        return Err("empty pipeline request".into());
                    }
                    let action = worker.prepare_pipeline(
                        &ids,
                        request["trial"].as_u64().ok_or("pipeline trial missing")?,
                    )?;
                    execute(action, &request)
                }
                "audit" => {
                    if !cfg!(feature = "subgroup-audit") {
                        return Err("subgroup audit feature is not enabled".into());
                    }
                    let id = request["job"].as_str().ok_or("job missing")?;
                    let action = worker.prepare(id, request["trial"].as_u64().unwrap_or(0))?;
                    let (result, audit) = crate::subgroup_audit::collect_selected(|| {
                        execute(action, &json!({"mode":"clock_free"}))
                    });
                    let mut result = result?;
                    result["subgroup_audit"] =
                        serde_json::to_value(audit).map_err(|e| e.to_string())?;
                    Ok(result)
                }
                "profile" => {
                    let ids = request["jobs"]
                        .as_array()
                        .ok_or("profile jobs missing")?
                        .iter()
                        .map(|x| {
                            x.as_str()
                                .map(str::to_owned)
                                .ok_or("invalid profile job".to_string())
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if ids.is_empty() {
                        return Err("profile jobs empty".into());
                    }
                    let milliseconds = request["milliseconds"].as_u64().unwrap_or(4500);
                    if !(1..=60000).contains(&milliseconds) {
                        return Err("invalid profiler duration".into());
                    }
                    let start = Instant::now();
                    let mut calls = std::collections::BTreeMap::<String, usize>::new();
                    let mut trial = request["trial"].as_u64().unwrap_or(900_000_000);
                    while start.elapsed().as_millis() < u128::from(milliseconds) {
                        for id in &ids {
                            let action = worker.prepare(id, trial)?;
                            let mut clock = BoundaryClock::new(RunMode::Profile, None)?;
                            action(&mut clock)?;
                            if clock.segments.is_empty() {
                                return Err("profile job omitted native boundary".into());
                            }
                            *calls.entry(id.clone()).or_default() += 1;
                            trial += 1;
                        }
                    }
                    Ok(
                        json!({"ok":true,"profile_callbacks":calls,"timing_enabled":false,"formal_samples":0,"protocol_latency_samples_exported":0}),
                    )
                }
                "prepare" | "run" => {
                    if mode(&request["mode"])? == RunMode::Formal {
                        if cfg!(feature = "subgroup-audit") {
                            return Err("formal sampling rejects a subgroup-audit build".into());
                        }
                        sampling::validate_wallclock_plan(&request["plan"])
                            .map_err(|e| e.to_string())?;
                    }
                    let id = request["job"].as_str().ok_or("job missing")?;
                    let trial = request["trial"].as_u64().unwrap_or(0);
                    let action = worker.prepare(id, trial)?;
                    if command == "run" {
                        execute(action, &request)
                    } else {
                        pending = Some(action);
                        Ok(json!({"ok":true,"prepared":id}))
                    }
                }
                "execute" => execute(pending.take().ok_or("no prepared job")?, &request),
                _ => Err("unknown worker command".into()),
            }
        })();
        let value = if worker.counter_scope_active() {
            json!({"ok":false,"error":"native callback left an active operation-counter scope","timing_enabled":false})
        } else {
            match response {
                Ok(v) => v,
                Err(e) => json!({"ok":false,"error":e,"timing_enabled":false}),
            }
        };
        writeln!(out, "{value}").map_err(|e| e.to_string())?;
        out.flush().map_err(|e| e.to_string())?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn verification_catalog_requires_received_bytes_and_separate_decoder() {
        let mut verify = Job::new("verify", "test", "verifier", "verification_crypto");
        assert!(validate_verification_boundaries(&[verify.clone()]).is_err());
        verify.boundary = json!({"strict_decoding_included":true,"received_bytes_first":true,
            "subgroup_checks_included":true,"native_format_checks_included":true,
            "subgroup_checks_per_received_element":1,"received_input_provenance":"sealed_checked_input"});
        assert!(validate_verification_boundaries(&[verify.clone()]).is_err());
        let mut decode = verify.clone();
        decode.id = "decode".into();
        decode.stage = "strict_decoding".into();
        decode.boundary["decode_only"] = json!(true);
        decode.boundary["parent_verification_stage"] = json!("verification_crypto");
        validate_verification_boundaries(&[verify.clone(), decode.clone()]).unwrap();
        for stage in ["native_read", "identify"] {
            let mut full = verify.clone();
            full.stage = stage.into();
            validate_verification_boundaries(&[full.clone(), decode.clone()]).unwrap();
            full.boundary["received_bytes_first"] = json!(false);
            assert!(validate_verification_boundaries(&[full, decode.clone()]).is_err());
        }
        for flag in [
            "strict_decoding_included",
            "received_bytes_first",
            "subgroup_checks_included",
            "native_format_checks_included",
        ] {
            let mut invalid = verify.clone();
            invalid.boundary[flag] = json!(false);
            assert!(validate_verification_boundaries(&[invalid, decode.clone()]).is_err());
        }
        for (key, value) in [
            ("subgroup_checks_per_received_element", json!(2)),
            ("received_input_provenance", json!("typed")),
        ] {
            let mut invalid = verify.clone();
            invalid.boundary[key] = value;
            assert!(validate_verification_boundaries(&[invalid, decode.clone()]).is_err());
            let mut invalid = decode.clone();
            invalid.boundary[key] = Value::Null;
            assert!(validate_verification_boundaries(&[verify.clone(), invalid]).is_err());
        }
        decode.stage = "verification_crypto".into();
        assert!(validate_verification_boundaries(&[verify, decode]).is_err());
    }
    #[test]
    fn clock_free_native_segments_are_real_and_have_no_time() {
        let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
        let mut n = 0;
        clock
            .measure(|| {
                n += 1;
                Ok(())
            })
            .unwrap();
        n += 10;
        clock
            .measure(|| {
                n += 1;
                Ok(())
            })
            .unwrap();
        assert_eq!(n, 12);
        assert_eq!(clock.segments(), &[None, None]);
        assert_eq!(clock.elapsed_ns(), None);
    }
    #[test]
    fn formal_clock_rejects_unapproved_plan_before_callback() {
        assert!(
            BoundaryClock::new(RunMode::Formal, Some(json!({"timing_enabled":false}))).is_err()
        );
    }
    #[test]
    fn worker_and_export_protocol_use_real_serde_names() {
        use crate::sampling::{Outcome, Phase, Source};
        assert_eq!(
            serde_json::to_value(Source::WallClock).unwrap(),
            json!("wall_clock")
        );
        assert_eq!(
            serde_json::to_value(Outcome::Stable).unwrap(),
            json!("stable")
        );
        assert_eq!(
            serde_json::to_value(Phase::Retained).unwrap(),
            json!("retained")
        );
    }
    #[test]
    fn either_baseline_counter_layer_is_detected_without_resetting_it() {
        assert!(!baseline_core::arithmetic::counts_active());
        baseline_core::curve::start_counts();
        assert!(baseline_core::arithmetic::counts_active());
        let _ = baseline_core::curve::stop_counts();
        baseline_core::arithmetic::start_counts();
        assert!(baseline_core::arithmetic::counts_active());
        let _ = baseline_core::arithmetic::stop_counts();
        assert!(!baseline_core::arithmetic::counts_active());
    }
}
