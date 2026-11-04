//! One uninterrupted campaign of actual role/stage pipelines.
use crate::{
    campaign::{self, Binding, PipelineGroup, Use},
    dispatch::{self, Client},
    experiment::Job,
    sampling::{self, Candidate, Phase, Sampler},
};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

fn owner(group: &PipelineGroup, owners: &BTreeMap<String, usize>) -> Result<usize, String> {
    let index = *owners
        .get(&group.jobs[0].id)
        .ok_or("pipeline owner missing")?;
    if group.jobs.iter().any(|j| owners.get(&j.id) != Some(&index)) {
        return Err("pipeline crosses worker processes".into());
    }
    Ok(index)
}
fn phase_label(p: Phase) -> &'static str {
    match p {
        Phase::Warmup => "warmup",
        Phase::Retained => "retained",
    }
}
fn count(j: &Job, p: Phase) -> usize {
    match p {
        Phase::Warmup => j.class.warmup(),
        Phase::Retained => j.class.retained(),
    }
}
fn request_trial(attempt: usize, priority: u8, phase: Phase, round: usize) -> u64 {
    attempt as u64 * 1_000_000_000_000
        + u64::from(priority) * 10_000_000_000
        + u64::from(phase == Phase::Retained) * 1_000_000_000
        + round as u64
}
/// Dependency order inside each paper block. The user-facing figure order is
/// preserved while required static/issuance/materialization happens first.
fn ordered(mut groups: Vec<PipelineGroup>) -> Vec<PipelineGroup> {
    let priority_by_scheme: BTreeMap<_, _> =
        groups
            .iter()
            .fold(BTreeMap::<String, u8>::new(), |mut a, g| {
                let s = g.jobs[0].scheme.clone();
                let p = a.entry(s).or_insert(g.priority);
                *p = (*p).min(g.priority);
                a
            });
    for group in &mut groups {
        if matches!(
            campaign::family(&group.jobs[0]),
            "static" | "issuance" | "materialization" | "delegation"
        ) && group.jobs[0].scheme == "DARLT"
        {
            group.priority = group.priority.min(priority_by_scheme["DARLT"]);
        }
    }
    let rank = |g: &PipelineGroup| match campaign::family(&g.jobs[0]) {
        "calibration" => 0,
        "static" => 1,
        "issuance" => 2,
        "materialization" => 3,
        "delegation" => 4,
        "request" => 5,
        "provisioning" => 6,
        _ => 7,
    };
    groups.sort_by_key(|g| (g.priority, rank(g), g.key.clone()));
    groups
}
fn rotated_round<'a>(
    groups: &[&'a PipelineGroup],
    round: usize,
    attempt: usize,
) -> Vec<&'a PipelineGroup> {
    let mut result = Vec::with_capacity(groups.len());
    let mut begin = 0;
    while begin < groups.len() {
        let family = campaign::family(&groups[begin].jobs[0]);
        let mut end = begin + 1;
        while end < groups.len() && campaign::family(&groups[end].jobs[0]) == family {
            end += 1;
        }
        let mut peers = groups[begin..end].to_vec();
        let offset = (round + attempt - 1) % peers.len();
        peers.rotate_left(offset);
        result.extend(peers);
        begin = end;
    }
    result
}

fn collect_bytes(
    clients: &mut [Client],
    owners: &BTreeMap<String, usize>,
    group: &PipelineGroup,
    index: usize,
    plan: &Value,
    raw: &mut std::fs::File,
) -> Result<(), String> {
    sampling::validate_wallclock_plan(plan).map_err(|e| e.to_string())?;
    let ids: Vec<_> = group.jobs.iter().map(|j| j.id.clone()).collect();
    let response = clients[owner(group, owners)?].call(
        &json!({"command":"pipeline","jobs":ids,"trial":90_000_000+index,"mode":"clock_free"}),
    )?;
    if response["ok"] != true {
        return Err(format!(
            "byte-only pipeline failed {}: {}",
            group.key, response
        ));
    }
    dispatch::write(
        raw,
        &json!({"pool":group.key,"purpose":"paper_bytes_only","observation":response,"timing_enabled":false,"formal_samples":0}),
    )
}
pub fn run_formal(
    clients: &mut [Client],
    owners: &BTreeMap<String, usize>,
    rows: &[Binding],
    plan: &Value,
    out: &Path,
    fingerprints: &Value,
) -> Result<Value, String> {
    sampling::validate_wallclock_plan(plan).map_err(|e| e.to_string())?;
    let selected: Vec<_> = rows
        .iter()
        .filter(|r| r.usage == Use::Timing)
        .map(|r| r.job.clone())
        .collect();
    if selected.is_empty() {
        return Err("no paper timing tasks".into());
    }
    let mut inventory = dispatch::new_file(&out.join("inventory.json"))?;
    dispatch::write(
        &mut inventory,
        &json!({"protocol":1,"mode":"formal","plan":plan,"jobs":selected,"worker_binaries":fingerprints,"pipeline":true,"timing_enabled":false,"formal_samples":0}),
    )?;
    dispatch::write(
        &mut dispatch::new_file(&out.join("paper_task_map.json"))?,
        &json!({"bindings":rows,"audit":campaign::audit(rows)}),
    )?;
    let mut raw = dispatch::new_file(&out.join("raw.jsonl"))?;
    let mut attempts_file = dispatch::new_file(&out.join("attempts.jsonl"))?;
    let byte_groups = ordered(campaign::groups(rows, Use::CountOnly));
    // Static/issuance byte evidence is an actual upstream initialization.
    // Request-byte scans wait until the timed inventory warmup is available.
    for (index, group) in byte_groups
        .iter()
        .enumerate()
        .filter(|(_, g)| campaign::family(&g.jobs[0]) != "request")
    {
        collect_bytes(clients, owners, group, index, plan, &mut raw)?;
    }
    let mut cohorts: BTreeMap<String, Vec<Job>> = BTreeMap::new();
    for job in &selected {
        cohorts
            .entry(dispatch::cohort(job))
            .or_default()
            .push(job.clone());
    }
    let mut samplers: BTreeMap<String, Sampler> = cohorts
        .keys()
        .map(|k| (k.clone(), Sampler::default()))
        .collect();
    let mut pending: BTreeSet<String> = cohorts.keys().cloned().collect();
    let mut stable = BTreeSet::new();
    for attempt in 1..=3 {
        let active_ids: BTreeSet<_> = pending
            .iter()
            .flat_map(|c| cohorts[c].iter().map(|j| j.id.clone()))
            .collect();
        let active_rows: Vec<_> = rows
            .iter()
            .filter(|r| r.usage == Use::Timing && active_ids.contains(&r.job.id))
            .cloned()
            .collect();
        let groups = ordered(campaign::groups(&active_rows, Use::Timing));
        let mut observations: BTreeMap<(String, String, usize), u64> = BTreeMap::new();
        let priorities: BTreeSet<_> = groups.iter().map(|g| g.priority).collect();
        for priority in priorities {
            let block: Vec<_> = groups.iter().filter(|g| g.priority == priority).collect();
            for phase in [Phase::Warmup, Phase::Retained] {
                let rounds = block
                    .iter()
                    .flat_map(|g| &g.jobs)
                    .map(|j| count(j, phase))
                    .max()
                    .unwrap_or(0);
                for round in 0..rounds {
                    // Each block's dependency families are ordered, candidates
                    // within a native pipeline rotate from its request seed.
                    for group in rotated_round(&block, round, attempt) {
                        let active: Vec<_> = group
                            .jobs
                            .iter()
                            .filter_map(|j| {
                                let n = count(j, phase);
                                if phase == Phase::Warmup
                                    && j.class == sampling::SampleClass::LongCallback
                                {
                                    return (round == 0).then_some((j, 0));
                                }
                                let before = round * n / rounds;
                                let after = (round + 1) * n / rounds;
                                (after != before).then_some((j, before))
                            })
                            .collect();
                        if active.is_empty() {
                            continue;
                        }
                        sampling::validate_wallclock_plan(plan).map_err(|e| e.to_string())?;
                        let ids: Vec<_> = active.iter().map(|(j, _)| j.id.clone()).collect();
                        let trial = request_trial(attempt, priority, phase, round);
                        let result=clients[owner(group,owners)?].call(&json!({"command":"pipeline","jobs":ids,"trial":trial,"sample_phase":phase,"mode":"formal","plan":plan}))?;
                        dispatch::write(
                            &mut raw,
                            &json!({"pool":group.key,"attempt":attempt,"phase":phase,"physical_round":round,"trial":trial,"jobs":ids,"observation":result,"timing_enabled":true}),
                        )?;
                        if result["ok"] != true || result["timing_enabled"] != true {
                            return Err(format!(
                                "native pipeline failed {}: {}",
                                group.key, result
                            ));
                        }
                        let actual = result["pipeline_observations"]
                            .as_object()
                            .ok_or("pipeline omitted observations")?;
                        for (job, index) in active {
                            let observation = actual.get(&job.id).ok_or_else(|| {
                                format!("{} missing actual captured stage", job.id)
                            })?;
                            if observation["ok"] != true {
                                return Err(format!("{} rejected in native pipeline", job.id));
                            }
                            let ns = observation["elapsed_ns"]
                                .as_u64()
                                .ok_or("captured native time missing")?;
                            if observation["derived"] == true {
                                let source = observation["source_job"]
                                    .as_str()
                                    .ok_or("derived source missing")?;
                                if !actual.contains_key(source) {
                                    return Err(
                                        "alias not from this actual pipeline execution".into()
                                    );
                                }
                            }
                            if observations
                                .insert((job.id.clone(), phase_label(phase).into(), index), ns)
                                .is_some()
                            {
                                return Err("same job sample was produced twice".into());
                            }
                        }
                    }
                }
            }
            if attempt == 1 {
                for (index, group) in byte_groups.iter().enumerate().filter(|(_, g)| {
                    campaign::family(&g.jobs[0]) == "request" && g.priority == priority
                }) {
                    collect_bytes(clients, owners, group, index, plan, &mut raw)?;
                }
            }
        }
        let mut retry = BTreeSet::new();
        for label in &pending {
            let jobs = &cohorts[label];
            let candidates: Vec<_> = jobs
                .iter()
                .map(|j| Candidate {
                    name: j.id.clone(),
                    class: j.class,
                    safe: j.boundary["safe"].as_bool().unwrap_or(true),
                })
                .collect();
            let a = samplers
                .get_mut(label)
                .ok_or("cohort sampler missing")?
                .run_worker_attempt(plan, label, &candidates, |invocation| {
                    observations
                        .remove(&(
                            jobs[invocation.candidate].id.clone(),
                            phase_label(invocation.phase).into(),
                            invocation.index,
                        ))
                        .ok_or_else(|| "missing original native pipeline observation".into())
                })
                .map_err(|e| e.to_string())?;
            dispatch::write(
                &mut attempts_file,
                &json!({"cohort":label,"jobs":jobs,"attempt":a,"native_pipeline_observations":true,"replayed_durations":false}),
            )?;
            if a.outcome == sampling::Outcome::Stable {
                stable.insert(label.clone());
            } else {
                retry.insert(label.clone());
            }
        }
        if !observations.is_empty() {
            return Err("unconsumed native observations".into());
        }
        pending = retry;
        if pending.is_empty() {
            break;
        }
    }
    let result = json!({"status":if pending.is_empty(){"PASS"}else{"REMEASUREMENT_REQUIRED"},"executed_native_jobs":selected.len(),"cohorts":cohorts.len(),"stable_cohorts":stable.len(),"pipeline":true,"one_uninterrupted_session":true,"all_attempts_preserved":true,"individual_outliers_removed":false,"timing_enabled":true});
    dispatch::write(&mut dispatch::new_file(&out.join("summary.json"))?, &result)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn request_ids_are_disjoint_across_warmup_retained_and_retry() {
        let mut seen = BTreeSet::new();
        for attempt in 1..=3 {
            for priority in 0..=4 {
                for phase in [Phase::Warmup, Phase::Retained] {
                    for round in 0..1000 {
                        assert!(seen.insert(request_trial(attempt, priority, phase, round)));
                    }
                }
            }
        }
    }
    #[test]
    fn long_warmup_occurs_before_request_validation_and_five_slots_are_spread() {
        let mut retained = vec![];
        for round in 0..100 {
            let before = round * 5 / 100;
            let after = (round + 1) * 5 / 100;
            if before != after {
                retained.push((round, before));
            }
        }
        assert_eq!(retained, vec![(19, 0), (39, 1), (59, 2), (79, 3), (99, 4)]);
    }
    #[test]
    fn peer_order_rotates_without_moving_requests_before_materialization() {
        let value: Value =
            serde_json::from_str(include_str!("fixtures/job_inventory.json")).unwrap();
        let jobs: Vec<Job> = serde_json::from_value(value["jobs"].clone()).unwrap();
        let pick = |id: &str| jobs.iter().find(|j| j.id == id).unwrap().clone();
        let stock = PipelineGroup {
            key: "stock".into(),
            priority: 1,
            jobs: vec![pick("LCB24/full_inventory")],
        };
        let a = PipelineGroup {
            key: "a".into(),
            priority: 1,
            jobs: vec![pick("darlt/prepare/k16")],
        };
        let b = PipelineGroup {
            key: "b".into(),
            priority: 1,
            jobs: vec![pick("darlt/online/k16")],
        };
        let groups = vec![&stock, &a, &b];
        assert_eq!(
            rotated_round(&groups, 0, 1)
                .iter()
                .map(|g| g.key.as_str())
                .collect::<Vec<_>>(),
            vec!["stock", "a", "b"]
        );
        assert_eq!(
            rotated_round(&groups, 1, 1)
                .iter()
                .map(|g| g.key.as_str())
                .collect::<Vec<_>>(),
            vec!["stock", "b", "a"]
        );
    }
}
