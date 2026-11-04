//! Figure and table bindings with single-session sampling policy.
use crate::{experiment::Job, sampling::SampleClass};
use serde::Serialize;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};

pub const K_VALUES: [usize; 9] = [1, 2, 4, 8, 16, 32, 64, 96, 128];
pub const TABLE_K: [usize; 3] = [1, 16, 64];
pub const LONG_CALLBACKS: [&str; 12] = [
    "LCB24/full_inventory",
    "LCB24/post_sparse512/k16/preparation/Specification/hot",
    "RP23-D/setup",
    "darlt/inclusive/RandomizedAcrossBlocks/ablation/k128",
    "darlt/inclusive/RandomizedPerBlock/ablation/k128",
    "darlt/inclusive/Specification/ablation/k128",
    "darlt/verify/RandomizedAcrossBlocks/ablation/k128",
    "darlt/verify/RandomizedPerBlock/ablation/k128",
    "darlt/verify/Specification/ablation/k128",
    "darlt/provision/issuer/64",
    "darlt/provision/system/32",
    "darlt/provision/system/64",
];
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Use {
    Timing,
    Derived,
    CountOnly,
    Optional,
}
#[derive(Clone, Debug, Serialize)]
pub struct Binding {
    pub job: Job,
    pub usage: Use,
    pub publications: Vec<String>,
    pub parent_ids: Vec<String>,
    pub component: Option<String>,
    pub reason: String,
    pub priority: u8,
    pub warmup: usize,
    pub retained: usize,
}
fn k(j: &Job) -> Option<usize> {
    j.workload["k"].as_u64().map(|v| v as usize)
}
pub fn specification(j: &Job) -> bool {
    matches!(
        j.profile.as_str(),
        "Specification" | "native_sequential_specification"
    )
}
/// Algorithm identities are prescribed before timing; no speed-based selection.
pub fn fixed_verification_profile(scheme: &str) -> Option<&'static str> {
    match scheme {
        "DARLT" => Some("RandomizedAcrossBlocks"),
        "SMA²RT" => Some("safe_random_complete_batch"),
        "NIAT" => Some("native_C3_random_second_equation"),
        "CPAT" => Some("safe_random_FHS_same_metadata_cached"),
        "HinToken" => Some("safe_random_batch_by_same_issuer_cached_anchor"),
        "MSB+23" | "SLW+25" | "RP23-C" | "RP23-D" => Some("Randomized"),
        "LCB24" => Some("RandomizedCachedGtAnchor"),
        _ => None,
    }
}
fn baseline_default(j: &Job) -> bool {
    j.workload["attributes"].as_u64().is_none_or(|a| a == 10)
}
pub fn darlt_default(j: &Job) -> bool {
    j.scheme == "DARLT"
        && j.workload["n"] == 1024
        && j.workload["s"] == 16
        && j.workload["attributes"] == 10
        && j.workload["private_attributes"] == 4
        && j.workload["range_bits"].is_null()
}
fn attributes(j: &Job) -> bool {
    j.workload["attributes"]
        .as_u64()
        .is_some_and(|a| [5, 10, 15, 20, 25, 30].contains(&a))
}
fn cash(j: &Job) -> bool {
    matches!(j.scheme.as_str(), "RP23-C" | "RP23-D" | "LCB24")
}
fn add(b: &mut Binding, target: &str) {
    if !b.publications.iter().any(|s| s == target) {
        b.publications.push(target.into());
    }
}
fn choose(b: &mut Binding, u: Use, p: u8, why: &str) {
    let was_timing = b.usage == Use::Timing;
    b.usage = u;
    b.priority = if u == Use::Timing && !was_timing {
        p
    } else {
        b.priority.min(p)
    };
    b.reason = why.into();
}
fn verifier(j: &Job) -> bool {
    matches!(
        j.stage.as_str(),
        "inclusive_verification" | "merchant_verify" | "bank_verify"
    )
}
fn dimensions(j: &Job) -> Value {
    let names = [
        "n",
        "capacity",
        "s",
        "attributes",
        "private_attributes",
        "delegatable_attributes",
        "range_bits",
        "k",
        "ablation",
        "scenario",
        "agents",
        "gamma",
        "n_per_agent",
        "hidden_bit",
        "metadata_bit",
        "judge_branch",
        "size",
    ];
    let mut v = serde_json::Map::new();
    for name in names {
        if !j.workload[name].is_null() {
            v.insert(name.into(), j.workload[name].clone());
        }
    }
    if !v.contains_key("k")
        && matches!(
            j.stage.as_str(),
            "preparation" | "online_generation" | "verification_crypto" | "inclusive_verification"
        )
    {
        v.insert("k".into(), json!(16));
    }
    Value::Object(v)
}
/// The key excludes figure IDs and scan labels: one physical measurement may
/// populate several panels. Different roles, profiles and cache boundaries stay.
pub fn measurement_key(j: &Job) -> String {
    format!(
        "{}/{}/{}/{}/{}/{}/{}",
        j.scheme,
        j.role,
        j.stage,
        j.substage,
        j.cache,
        j.profile,
        dimensions(j)
    )
}
pub fn family(j: &Job) -> &'static str {
    match j.stage.as_str() {
        "calibration" => "calibration",
        "setup" | "key_generation" | "keygen" | "install" => "static",
        "issue_request" | "issue_response" | "issue_accept" | "issue_receive" => "issuance",
        "full_inventory" => "materialization",
        "provisioning_issuer" | "provisioning_system" => "provisioning",
        "delegate_request" | "delegate_send" | "delegate_receive" | "self_allocate"
        | "parent_opening" | "scope_opening" => "delegation",
        _ => "request",
    }
}
/// All k values and verifier profiles share immutable assets in this family.
/// A pipeline creates at most one live request slot at a time.
pub fn pool_key(j: &Job) -> String {
    let fields = [
        "n",
        "capacity",
        "s",
        "attributes",
        "private_attributes",
        "delegatable_attributes",
        "range_bits",
        "agents",
        "n_per_agent",
        "hidden_bit",
        "metadata_bit",
    ];
    let mut d = serde_json::Map::new();
    for key in fields {
        if !j.workload[key].is_null() {
            d.insert(key.into(), j.workload[key].clone());
        }
    }
    format!("{}/{}/{}", j.scheme, family(j), Value::Object(d))
}
pub fn plan(jobs: &[Job]) -> Vec<Binding> {
    let mut rows = Vec::with_capacity(jobs.len());
    for source in jobs {
        let mut j = source.clone();
        if LONG_CALLBACKS.contains(&j.id.as_str()) {
            j.class = SampleClass::LongCallback;
        }
        let mut b = Binding {
            warmup: j.class.warmup(),
            retained: j.class.retained(),
            job: j.clone(),
            usage: Use::Optional,
            publications: vec![],
            parent_ids: vec![],
            component: None,
            reason: "No destination in the current paper figures/tables; optional, not dispatched"
                .into(),
            priority: 255,
        };
        let kv = k(&j);
        let table = kv.is_some_and(|k| TABLE_K.contains(&k));
        let scan = kv.is_some_and(|k| K_VALUES.contains(&k));
        if kv.is_some_and(|k| !K_VALUES.contains(&k)) {
            b.reason = "Removed k value in the nine-point scan".into();
            rows.push(b);
            continue;
        }
        if j.boundary["safe"] == false || j.profile.contains("all_ones") {
            b.reason = "Reference-only unsafe aggregation; not a paper timing candidate".into();
            rows.push(b);
            continue;
        }
        if verifier(&j) && fixed_verification_profile(&j.scheme) != Some(j.profile.as_str()) {
            b.reason = "Not the prescribed fixed batch verifier; no candidates or specification verification are formally timed".into();
            rows.push(b);
            continue;
        }
        if j.scheme == "DARLT" && j.stage == "identify" && j.profile != "Randomized" {
            b.reason = "Judge uses the prescribed randomized whole-step verifier; specification is correctness-reference only".into();
            rows.push(b);
            continue;
        }
        let default = if j.scheme == "DARLT" {
            darlt_default(&j)
        } else {
            baseline_default(&j)
        };
        let darlt_scan = j.scheme == "DARLT" && j.id.contains("/scan/");
        let attr_scan = darlt_scan && j.id.contains("/attributes/");
        let range_scan = darlt_scan && j.id.contains("/range/");
        if j.stage == "calibration" {
            add(&mut b, "Calibration");
            choose(
                &mut b,
                Use::Timing,
                0,
                "Paired single-thread backend calibration",
            );
        } else if j.substage != "whole" {
            if darlt_default(&j)
                && kv == Some(16)
                && matches!(
                    j.stage.as_str(),
                    "preparation" | "online_generation" | "verification_crypto"
                )
                && (j.stage != "verification_crypto" || j.profile == "RandomizedAcrossBlocks")
            {
                add(&mut b, "Fig.7(a): default-k16 breakdown");
                choose(&mut b,Use::Derived,2,"Consecutive components from the same default-k16 native execution; no separate operation");
                b.component = Some(if j.id.ends_with("/exclusive") {
                    format!("{}:exclusive", j.substage)
                } else {
                    j.substage.clone()
                });
            } else {
                b.reason =
                    "Detailed reruns removed; only one default-k16 DARLT pipeline is decomposed"
                        .into();
            }
        } else if j.stage == "strict_decoding" {
            choose(
                &mut b,
                Use::Derived,
                1,
                "Strict decoding is recorded inside the same native verification, not rerun",
            );
            b.component = Some("receive.strict_decoding".into());
        } else if j.stage == "verification_crypto" {
            b.reason="Native crypto overlaps the inclusive acceptance used by the paper; optional independent diagnostic, not dispatched".into();
        } else if verifier(&j) {
            let expected = if cash(&j) {
                if j.scheme == "LCB24" {
                    "bank_verify"
                } else {
                    "merchant_verify"
                }
            } else {
                "inclusive_verification"
            };
            if j.stage == expected {
                if default && table && j.workload["ablation"] != true {
                    add(&mut b, "Table IV: fixed batch verification");
                    choose(&mut b,Use::Timing,1,"Prescribed fixed verifier at the three Table-IV points; no variant selection");
                }
                if default
                    && scan
                    && !specification(&j)
                    && (j.scheme == "SMA²RT" || (j.scheme == "DARLT" && !darlt_scan))
                {
                    add(&mut b, "Fig.10(a): fixed batch verifier");
                    choose(
                        &mut b,
                        Use::Timing,
                        1,
                        "One prescribed verifier for the entire nine-point curve",
                    );
                }
                if j.scheme == "DARLT" && attr_scan && !specification(&j) {
                    add(&mut b, "Fig.8(a)");
                    add(&mut b, "Fig.11(b)");
                    choose(&mut b, Use::Timing, 3, "Attribute-policy acceptance scan");
                }
                if j.scheme == "DARLT" && range_scan && !specification(&j) {
                    add(&mut b, "Fig.8(b)");
                    choose(&mut b, Use::Timing, 4, "Range-policy acceptance scan");
                }
                if j.scheme == "DARLT"
                    && default
                    && matches!(kv, Some(1 | 16))
                    && j.workload["ablation"] != true
                    && !specification(&j)
                {
                    add(&mut b, "Fig.7(a): BatchVerify");
                }
                if matches!(j.scheme.as_str(), "SMA²RT" | "MSB+23" | "SLW+25")
                    && attributes(&j)
                    && kv == Some(16)
                    && !specification(&j)
                {
                    add(&mut b, "Fig.11(b)");
                    choose(
                        &mut b,
                        Use::Timing,
                        3,
                        "Fixed attribute-policy comparison verifier",
                    );
                }
                if matches!(j.scheme.as_str(), "NIAT" | "CPAT" | "HinToken")
                    && kv == Some(16)
                    && b.usage == Use::Timing
                {
                    add(&mut b, "Fig.11(b): horizontal reference");
                }
            }
        } else if j.scheme != "DARLT"
            && default
            && kv.is_none_or(|v| v == 1)
            && canonical_byte_profile(&j)
            && matches!(
                j.stage.as_str(),
                "issue_request"
                    | "issue_response"
                    | "issue_accept"
                    | "issue_receive"
                    | "delegate_request"
                    | "delegate_send"
                    | "delegate_receive"
            )
        {
            add(
                &mut b,
                if j.stage.starts_with("issue_") {
                    "Table IV: Issue by role"
                } else {
                    "Table IV: Delegate by role"
                },
            );
            add(&mut b, "Table III: actual credential/delegation bytes");
            choose(
                &mut b,
                Use::Timing,
                1,
                "Canonical native role boundary for the existing Table-IV Issue/Delegate rows",
            );
        } else if default
            && j.stage == "metadata_read"
            && kv == Some(1)
            && matches!(j.scheme.as_str(), "SMA²RT" | "NIAT" | "CPAT" | "HinToken")
        {
            add(&mut b, "Table IV: RecoverMetadata bit0/bit1");
            choose(
                &mut b,
                Use::Timing,
                1,
                "One already verified record, each actual bit kept separate",
            );
        } else if matches!(
            j.stage.as_str(),
            "preparation" | "online_generation" | "online"
        ) {
            let table_generation = if j.stage == "preparation" {
                !matches!(j.scheme.as_str(), "NIAT" | "HinToken")
            } else {
                !matches!(j.scheme.as_str(), "NIAT" | "CPAT" | "HinToken" | "LCB24")
            };
            if default && table && table_generation {
                add(&mut b, "Table IV: spend generation");
                choose(
                    &mut b,
                    Use::Timing,
                    1,
                    "Native preparation/online boundaries",
                );
            }
            if default && scan && j.stage != "preparation" {
                add(&mut b, "Fig.10(b)");
                if b.usage == Use::Optional {
                    choose(
                        &mut b,
                        Use::CountOnly,
                        1,
                        "One clock-free native wire-generation result for communication only",
                    );
                }
            }
            if j.scheme == "DARLT" && default && matches!(kv, Some(1 | 16)) && !darlt_scan {
                add(&mut b, "Fig.7(a)");
                add(&mut b, "Fig.7(b)");
                choose(
                    &mut b,
                    Use::Timing,
                    2,
                    "Single-unit and default batch costs",
                );
            }
            if j.scheme == "DARLT" && attr_scan {
                add(&mut b, "Fig.8(a)");
                if j.stage == "online_generation" {
                    add(&mut b, "Fig.11(a)");
                }
                choose(
                    &mut b,
                    Use::Timing,
                    3,
                    "Attribute scan with its own private/delegatable split; only truly identical configurations merge",
                );
            }
            if j.scheme == "DARLT" && range_scan {
                add(&mut b, "Fig.8(b)");
                choose(&mut b, Use::Timing, 4, "Range predicate scan");
            }
            if matches!(j.scheme.as_str(), "SMA²RT" | "MSB+23" | "SLW+25")
                && attributes(&j)
                && kv == Some(16)
                && j.stage == "online_generation"
            {
                add(&mut b, "Fig.11(a)");
                choose(&mut b, Use::Timing, 3, "Attribute-policy online comparison");
            }
            if matches!(j.scheme.as_str(), "NIAT" | "CPAT" | "HinToken")
                && kv == Some(16)
                && j.stage == "online_generation"
            {
                add(&mut b, "Fig.11(a): horizontal reference");
                choose(
                    &mut b,
                    Use::Timing,
                    3,
                    "One k16 native online-delivery reference; no invented context proof",
                );
            }
        } else if matches!(
            j.stage.as_str(),
            "backend" | "backend_deposit" | "backend_redeem"
        ) && cash(&j)
            && table
        {
            add(&mut b, "Table IV: native backend and common state");
            choose(
                &mut b,
                Use::Timing,
                1,
                "Disjoint native backend: no second Groth16 verification for LCB24",
            );
        } else if matches!(j.stage.as_str(), "shared_state" | "state") && table {
            add(&mut b, "Table IV: common-state component");
            choose(&mut b,Use::Derived,1,"Actual registration segment from the same acceptance/backend, not an independent rerun");
            b.component = Some("verification.state".into());
        } else if matches!(
            j.stage.as_str(),
            "provisioning_issuer" | "provisioning_system"
        ) {
            add(
                &mut b,
                if j.stage == "provisioning_issuer" {
                    "Fig.9(b): issuer ledger"
                } else {
                    "Fig.9(b): system ledger"
                },
            );
            if j.stage == "provisioning_system" {
                add(&mut b, "Table IV: system provisioning / A");
            }
            choose(&mut b,Use::Timing,2,"Two different accounting boundaries, captured from one flow when their sample slots coincide");
        } else if j.scheme == "DARLT"
            && default
            && !darlt_scan
            && matches!(
                j.stage.as_str(),
                "setup"
                    | "key_generation"
                    | "issue_request"
                    | "issue_response"
                    | "issue_accept"
                    | "delegate_request"
                    | "parent_opening"
                    | "scope_opening"
                    | "identify"
                    | "metadata_read"
            )
        {
            add(&mut b, "Fig.7(a)");
            if matches!(
                j.stage.as_str(),
                "issue_request" | "issue_response" | "issue_accept"
            ) {
                add(&mut b, "Fig.7(b)");
                add(&mut b, "Table III: credential");
            }
            choose(&mut b, Use::Timing, 2, "Default DARLT role/algorithm cost");
        } else if j.scheme == "DARLT"
            && default
            && !darlt_scan
            && matches!(j.stage.as_str(), "delegate_send" | "delegate_receive")
        {
            add(&mut b, "Fig.9(a)");
            add(&mut b, "Table III: delegation");
            if j.workload["gamma"] == 1 {
                add(&mut b, "Fig.7(a)");
                add(&mut b, "Fig.7(b)");
            }
            choose(
                &mut b,
                Use::Timing,
                2,
                "Delegator hot/cold and delegatee by pool scope",
            );
        } else if j.scheme == "DARLT"
            && default
            && j.stage == "self_allocate"
            && j.workload["gamma"] == 1
        {
            add(&mut b, "Fig.7(a): self allocation hot/cold");
            choose(
                &mut b,
                Use::Timing,
                2,
                "One default scope; other self-allocation scans are optional",
            );
        } else if default
            && kv.is_none_or(|k| k == 1)
            && !j.id.contains("installed-for-")
            && !j.id.contains("equal-budget/")
            && canonical_byte_profile(&j)
            && matches!(
                j.stage.as_str(),
                "issue_request"
                    | "issue_response"
                    | "issue_accept"
                    | "issue_receive"
                    | "delegate_send"
                    | "delegate_receive"
                    | "install"
            )
        {
            add(
                &mut b,
                "Table III: actual credential/delegation/role parameters",
            );
            choose(
                &mut b,
                Use::CountOnly,
                2,
                "One real initialization/encoding for bytes; no timing column for this algorithm",
            );
        } else if j.scheme == "LCB24" && j.stage == "full_inventory" {
            add(&mut b, "Table IV: published offline proof inventory");
            add(&mut b, "Table III: precomputation storage");
            choose(
                &mut b,
                Use::Timing,
                1,
                "True native complete inventory generation, retained and reused downstream",
            );
        }
        if j.scheme == "DARLT" && default && !darlt_scan && b.usage == Use::Timing {
            if j.stage.starts_with("issue_") {
                add(&mut b, "Table IV: Issue by role");
                b.priority = b.priority.min(1);
            }
            if matches!(j.stage.as_str(), "delegate_send" | "delegate_receive")
                && j.workload["gamma"] == 1
            {
                add(&mut b, "Table IV: Delegate by role");
                b.priority = b.priority.min(1);
            }
            if j.stage == "metadata_read" {
                add(&mut b, "Table IV: RecoverMetadata bit0/bit1");
                b.priority = b.priority.min(1);
            }
        }
        if j.id.contains("/scan/scale/") {
            b.usage = Use::Optional;
            b.publications.clear();
            b.reason="N/s extension has no current Fig.7-11/Table-III/IV destination; optional, not dispatched".into();
            b.priority = 255;
        }
        rows.push(b);
    }
    // Merge exact boundary/config duplicates, preferring the established default
    // ID over its attribute/scale scan spelling.
    let mut keys: BTreeMap<String, usize> = BTreeMap::new();
    let mut order: Vec<_> = (0..rows.len()).collect();
    order.sort_by_key(|&i| {
        (
            rows[i].job.id.contains("/scan/"),
            rows[i].job.id.len(),
            rows[i].job.id.clone(),
        )
    });
    for i in order {
        if !matches!(rows[i].usage, Use::Timing | Use::CountOnly) {
            continue;
        }
        let key = measurement_key(&rows[i].job);
        if let Some(&p) = keys.get(&key) {
            let publications = rows[i].publications.clone();
            for target in publications {
                add(&mut rows[p], &target);
            }
            if rows[i].usage == Use::Timing {
                rows[p].usage = Use::Timing;
            }
            rows[p].priority = rows[p].priority.min(rows[i].priority);
            rows[i].usage = Use::Derived;
            rows[i].parent_ids = vec![rows[p].job.id.clone()];
            rows[i].component = Some("whole".into());
            rows[i].reason =
                "Identical measured boundary and workload; reused by all listed paper destinations"
                    .into();
        } else {
            keys.insert(key, i);
        }
    }
    // Attach same-execution components only when their actual parent is used.
    for i in 0..rows.len() {
        if rows[i].usage != Use::Derived || !rows[i].parent_ids.is_empty() {
            continue;
        }
        let j = rows[i].job.clone();
        let parents: Vec<_> = rows
            .iter()
            .filter(|p| {
                p.usage == Use::Timing
                    && p.job.scheme == j.scheme
                    && k(&p.job) == k(&j)
                    && dimensions_without_stage(&p.job) == dimensions_without_stage(&j)
                    && if matches!(j.stage.as_str(), "state" | "shared_state") {
                        p.job.stage == "inclusive_verification" || p.job.stage == "backend"
                    } else if j.stage == "strict_decoding" {
                        verifier(&p.job)
                            || p.job.stage == "native_read"
                            || p.job.stage == "identify"
                    } else {
                        p.job.id == j.id.split("/substage/").next().unwrap_or("")
                            || (p.job.stage == "inclusive_verification"
                                && j.stage == "verification_crypto"
                                && p.job.profile == j.profile)
                    }
            })
            .map(|p| p.job.id.clone())
            .collect();
        if parents.is_empty() {
            rows[i].usage = Use::Optional;
            rows[i].reason =
                "Parent measurement is optional; component is not separately dispatched".into();
            rows[i].publications.clear();
            rows[i].priority = 255;
        } else {
            rows[i].parent_ids = parents;
        }
    }
    rows
}
fn dimensions_without_stage(j: &Job) -> Value {
    let mut d = dimensions(j);
    if let Some(o) = d.as_object_mut() {
        // Missing false/null defaults denote the same native configuration; true
        // ablation is a separate received message and must never alias native.
        if o.get("ablation") == Some(&json!(false)) {
            o.remove("ablation");
        }
    }
    d
}
fn canonical_byte_profile(j: &Job) -> bool {
    match (j.scheme.as_str(), j.stage.as_str()) {
        ("NIAT", "issue_accept" | "issue_response") => j.profile == "NativeTotal",
        ("MSB+23", "issue_accept") => j.profile == "RandomizedPairingKey",
        ("MSB+23", "delegate_receive")
        | ("SLW+25", "issue_accept")
        | ("SLW+25", "delegate_receive") => j.profile == "Randomized",
        _ => true,
    }
}
#[derive(Clone, Debug, Serialize)]
pub struct PipelineGroup {
    pub key: String,
    pub priority: u8,
    pub jobs: Vec<Job>,
}
pub fn groups(rows: &[Binding], usage: Use) -> Vec<PipelineGroup> {
    let mut groups: BTreeMap<String, PipelineGroup> = BTreeMap::new();
    for row in rows.iter().filter(|r| r.usage == usage) {
        let key = pool_key(&row.job);
        let g = groups.entry(key.clone()).or_insert(PipelineGroup {
            key,
            priority: row.priority,
            jobs: vec![],
        });
        g.priority = g.priority.min(row.priority);
        g.jobs.push(row.job.clone());
    }
    let mut out: Vec<_> = groups.into_values().collect();
    for group in &mut out {
        group.jobs.sort_by_key(|j| (j.stage.clone(), j.id.clone()));
    }
    out.sort_by_key(|g| (g.priority, g.key.clone()));
    out
}
pub fn audit(rows: &[Binding]) -> Value {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for row in rows {
        *counts.entry(format!("{:?}", row.usage)).or_default() += 1;
    }
    let selected: Vec<_> = rows.iter().filter(|r| r.usage == Use::Timing).collect();
    let ids: BTreeSet<_> = selected.iter().map(|r| &r.job.id).collect();
    let pools:Vec<_>=groups(rows,Use::Timing).iter().map(|g|json!({"pool_key":g.key,"priority":g.priority,"jobs":g.jobs.iter().map(|j|j.id.clone()).collect::<Vec<_>>(),"max_live_complete_request_slots":1,"warmup_slots":g.jobs.iter().map(|j|j.class.warmup()).max().unwrap_or(0),"retained_slots":g.jobs.iter().map(|j|j.class.retained()).max().unwrap_or(0)})).collect();
    let byte_pools: Vec<_> = groups(rows, Use::CountOnly)
        .iter()
        .map(|g| json!({"pool_key":g.key,"priority":g.priority,"jobs":g.jobs.iter().map(|j|j.id.clone()).collect::<Vec<_>>(),"max_live_complete_request_slots":1,"clock_free_calls":1}))
        .collect();
    let physical = pools
        .iter()
        .map(|g| g["warmup_slots"].as_u64().unwrap() + g["retained_slots"].as_u64().unwrap())
        .sum::<u64>();
    json!({"all_jobs":rows.len(),"dispositions":counts,"timing_tasks":selected.len(),"unique_timing_ids":ids.len(),"native_pipeline_groups":pools,"byte_only_pipeline_calls":byte_pools.len(),"byte_only_pipeline_groups":byte_pools,"physical_pipeline_calls_per_attempt":physical,"logical_captured_samples_per_attempt":selected.iter().map(|r|r.warmup+r.retained).sum::<usize>(),"callbacks_per_attempt":selected.iter().map(|r|r.warmup+r.retained).sum::<usize>(),"k_values":K_VALUES,"table_k":TABLE_K,"long_callback_whitelist":LONG_CALLBACKS,"timing_enabled":false,"formal_samples":0,"optional_dispatched":0,"independent_decoder_or_fine_reruns":0})
}

#[cfg(test)]
mod tests {
    use super::*;
    fn old_jobs() -> Vec<Job> {
        let value: Value =
            serde_json::from_str(include_str!("fixtures/job_inventory.json")).unwrap();
        serde_json::from_value(value["jobs"].clone()).unwrap()
    }
    #[test]
    fn every_catalogue_entry_has_one_disposition_and_no_unmapped_job_is_timed() {
        let jobs = old_jobs();
        let rows = plan(&jobs);
        assert_eq!(rows.len(), jobs.len());
        let mut keys = BTreeSet::new();
        for row in &rows {
            if matches!(row.usage, Use::Timing | Use::CountOnly) {
                assert!(!row.publications.is_empty(), "{}", row.job.id);
                assert!(keys.insert(measurement_key(&row.job)), "{}", row.job.id);
                assert!(k(&row.job).is_none_or(|v| K_VALUES.contains(&v)));
            }
            if row.usage == Use::Timing {
                assert_ne!(row.job.stage, "verification_crypto");
                assert_ne!(row.job.stage, "strict_decoding");
                if row.job.stage != "calibration" {
                    assert_eq!(row.job.substage, "whole");
                }
            }
            if verifier(&row.job) && row.usage == Use::Timing {
                assert_eq!(
                    fixed_verification_profile(&row.job.scheme),
                    Some(row.job.profile.as_str())
                );
                assert!(!specification(&row.job));
            }
            if row.usage == Use::Derived {
                assert!(!row.parent_ids.is_empty());
            }
        }
    }
    #[test]
    fn fixed_nine_point_verifiers_and_exact_long_job_policy_are_preserved() {
        let rows = plan(&old_jobs());
        for row in &rows {
            if LONG_CALLBACKS.contains(&row.job.id.as_str()) {
                assert_eq!((row.warmup, row.retained), (1, 5));
            } else {
                assert_eq!(row.warmup, 10);
                assert_ne!(row.job.class, SampleClass::LongCallback);
            }
        }
        for mode in ["native", "ablation"] {
            for profile in ["RandomizedAcrossBlocks"] {
                for k in K_VALUES {
                    let id = format!("darlt/inclusive/{profile}/{mode}/k{k}");
                    let row = rows.iter().find(|r| r.job.id == id).unwrap();
                    assert_eq!(row.usage, Use::Timing, "{id}");
                }
            }
        }
        assert!(rows
            .iter()
            .filter(|r| r.job.id.contains("/scan/scale/"))
            .all(|r| r.usage == Use::Optional));
        for row in rows.iter().filter(|r| verifier(&r.job)) {
            if fixed_verification_profile(&row.job.scheme) != Some(row.job.profile.as_str()) {
                assert_eq!(row.usage, Use::Optional, "{}", row.job.id);
            }
        }
    }
    #[test]
    fn byte_only_native_initialization_does_not_dispatch_alternative_receive_profiles() {
        let rows = plan(&old_jobs());
        let chosen: Vec<_> = rows
            .iter()
            .filter(|r| {
                r.usage == Use::Timing && r.job.stage == "issue_accept" && r.job.scheme == "MSB+23"
            })
            .collect();
        assert_eq!(chosen.len(), 1);
        assert_eq!(chosen[0].job.profile, "RandomizedPairingKey");
        assert!(rows
            .iter()
            .filter(|r| r.job.id.contains("installed-for-"))
            .all(|r| r.usage == Use::Optional));
    }
    #[test]
    fn byte_only_installation_is_separate_from_native_request_pipelines() {
        let rows = plan(&old_jobs());
        let groups = groups(&rows, Use::CountOnly);
        let lcb_install = groups
            .iter()
            .find(|g| g.jobs.iter().any(|j| j.id == "LCB24/install"))
            .expect("LCB installation byte evidence");
        assert_eq!(family(&lcb_install.jobs[0]), "static");
        assert!(lcb_install.jobs.iter().all(|j| j.stage == "install"));
        for group in groups {
            if group.jobs.iter().any(|j| j.stage == "install") {
                assert!(group.jobs.iter().all(|j| family(j) != "request"));
            }
        }
    }
    #[test]
    fn calibration_keeps_every_backend_operator_and_size_as_distinct_actual_work() {
        let rows = plan(&old_jobs());
        let calibration: Vec<_> = rows
            .iter()
            .filter(|r| r.job.stage == "calibration")
            .collect();
        assert_eq!(calibration.len(), 42);
        assert!(calibration
            .iter()
            .all(|r| r.usage == Use::Timing && r.warmup == 10 && r.retained == 1000));
        assert_eq!(
            calibration
                .iter()
                .map(|r| measurement_key(&r.job))
                .collect::<BTreeSet<_>>()
                .len(),
            42
        );
    }

    #[test]
    fn judge_accountability_branches_and_verification_modes_are_distinct() {
        let mut jobs = old_jobs();
        for j in &mut jobs {
            if j.stage == "identify" && j.id.ends_with("randomized") {
                j.profile = "Randomized".into();
            }
        }
        let rows = plan(&jobs);
        let judges: Vec<_> = rows
            .iter()
            .filter(|r| r.job.stage == "identify" && r.job.scheme == "DARLT")
            .collect();
        assert_eq!(judges.len(), 4);
        assert_eq!(judges.iter().filter(|r| r.usage == Use::Timing).count(), 2);
        assert!(judges
            .iter()
            .filter(|r| r.usage == Use::Timing)
            .all(|r| r.job.profile == "Randomized"));
        assert_eq!(
            judges
                .iter()
                .map(|r| measurement_key(&r.job))
                .collect::<BTreeSet<_>>()
                .len(),
            4
        );
    }
    #[test]
    fn current_table_iv_keeps_issue_delegate_and_both_validated_read_bits() {
        let rows = plan(&old_jobs());
        for scheme in [
            "DARLT", "SMA²RT", "NIAT", "CPAT", "HinToken", "MSB+23", "SLW+25", "RP23-C", "RP23-D",
            "LCB24",
        ] {
            assert!(
                rows.iter().any(|r| r.job.scheme == scheme
                    && r.usage == Use::Timing
                    && r.publications
                        .iter()
                        .any(|t| t == "Table IV: Issue by role")),
                "{scheme}"
            );
        }
        for scheme in ["SMA²RT", "NIAT", "CPAT", "HinToken"] {
            assert_eq!(
                rows.iter()
                    .filter(|r| r.job.scheme == scheme
                        && r.job.stage == "metadata_read"
                        && r.usage == Use::Timing)
                    .count(),
                2
            );
        }
        for r in &rows {
            if r.job.scheme == "NIAT" && r.job.stage == "preparation" {
                assert_ne!(r.usage, Use::Timing);
            }
        }
    }
}
