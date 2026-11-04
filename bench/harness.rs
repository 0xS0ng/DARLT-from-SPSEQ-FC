//! Benchmark roles, stages and clocks.
//! ClockFree collects callback outputs without reading a clock.
//! Smoke runs one callback; Formal retains samples within a configured window.
use crate::ops;
use baseline_core::{arithmetic, encoding};
use serde::Serialize;
use serde_json::Value;
use std::{cell::Cell, fmt, time::Instant};

pub const K_VALUES: [usize; 9] = [1, 2, 4, 8, 16, 32, 64, 96, 128];
pub const TABLE_IV_K: [usize; 3] = [1, 16, 64];
pub const AGENT_VALUES: [usize; 7] = [1, 2, 4, 8, 16, 32, 64];

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub enum Scheme {
    #[serde(rename = "DARLT")]
    Darlt,
    #[serde(rename = "SMA²RT")]
    Sma2rt,
    #[serde(rename = "NIAT")]
    Niat,
    #[serde(rename = "CPAT")]
    Cpat,
    HinToken,
    #[serde(rename = "MSB+23")]
    Msb23,
    #[serde(rename = "SLW+25")]
    Slw25,
    #[serde(rename = "RP23-C")]
    Rp23C,
    #[serde(rename = "RP23-D")]
    Rp23D,
    #[serde(rename = "LCB24")]
    Lcb24,
}
impl Scheme {
    pub const ALL: [Self; 10] = [
        Self::Darlt,
        Self::Sma2rt,
        Self::Niat,
        Self::Cpat,
        Self::HinToken,
        Self::Msb23,
        Self::Slw25,
        Self::Rp23C,
        Self::Rp23D,
        Self::Lcb24,
    ];
    pub fn label(self) -> &'static str {
        match self {
            Self::Darlt => "DARLT",
            Self::Sma2rt => "SMA²RT",
            Self::Niat => "NIAT",
            Self::Cpat => "CPAT",
            Self::HinToken => "HinToken",
            Self::Msb23 => "MSB+23",
            Self::Slw25 => "SLW+25",
            Self::Rp23C => "RP23-C",
            Self::Rp23D => "RP23-D",
            Self::Lcb24 => "LCB24",
        }
    }
    pub fn adapter_present(self) -> bool {
        true
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Role {
    User,
    Issuer,
    Agent,
    Verifier,
    Merchant,
    Authority,
    Reader,
    Backend,
    System,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Stage {
    Setup,
    KeyGeneration,
    Install,
    IssueRequest,
    IssueResponse,
    IssueAccept,
    ParentOpening,
    DelegateRequest,
    DelegateSend,
    DelegateReceive,
    SelfAllocate,
    ScopeOpening,
    Preparation,
    OnlineGeneration,
    StrictDecoding,
    VerificationCrypto,
    BackendDeposit,
    BackendRedeem,
    SharedState,
    MetadataRead,
    NativeRead,
    InclusiveVerification,
    ProvisioningIssuer,
    ProvisioningSystem,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Substage {
    Whole,
    Encoding,
    StrictDecoding,
    SubgroupCheck,
    HashToGroup,
    FiatShamir,
    Polynomial,
    FieldArithmetic,
    SigmaResponse,
    StateAccess,
    ParameterInstallation,
    KeyProofInstallation,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Cache {
    Cold,
    Hot,
    NotApplicable,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Mode {
    ClockFree,
    Smoke,
    Formal,
}

/// Nullable native counts distinguish unknown facts from actual zero counts.
#[derive(Clone, Debug, Default, Serialize)]
pub struct NativeObjects {
    pub tokens: Option<usize>,
    pub intervals: Option<usize>,
    pub subtree_blocks: Option<usize>,
    pub darlt_blocks: Option<usize>,
}
#[derive(Clone, Debug, Default, Serialize)]
pub struct Workload {
    pub k: Option<usize>,
    pub n: Option<usize>,
    pub s: Option<usize>,
    pub gamma: Option<usize>,
    pub agents: Option<usize>,
    pub attributes: Option<usize>,
    pub range_bits: Option<usize>,
    pub native_objects: NativeObjects,
}
#[derive(Clone, Debug, Default, Serialize)]
pub struct Boundary {
    pub wire_encoding_included: bool,
    pub strict_decoding_included: bool,
    pub shared_state_included: bool,
    pub native_backend_included: bool,
    pub network_included: bool,
    pub persistence_included: bool,
    /// Inclusive totals and their decomposition rows must not be added again.
    pub inclusive_total: bool,
}
#[derive(Clone, Debug, Serialize)]
pub struct Label {
    pub scheme: Scheme,
    pub role: Role,
    pub stage: Stage,
    pub substage: Substage,
    pub cache: Cache,
    pub profile: String,
    pub boundary: Boundary,
}
impl Label {
    fn validate(&self, workload: &Workload) -> Result<(), Error> {
        if self.profile.is_empty() || self.profile.len() > 256 {
            return Err(Error::InvalidLabel("empty or oversized profile".into()));
        }
        for v in [
            workload.k,
            workload.n,
            workload.s,
            workload.gamma,
            workload.agents,
        ]
        .into_iter()
        .flatten()
        {
            if v == 0 {
                return Err(Error::InvalidLabel(
                    "workload dimensions must be positive".into(),
                ));
            }
        }
        if self.boundary.inclusive_total && self.substage != Substage::Whole {
            return Err(Error::InvalidLabel(
                "an inclusive total uses substage Whole".into(),
            ));
        }
        Ok(())
    }
}

/// Output bytes are obtained from complete native codec messages, never from
/// an estimated size formula. Encoding is charged where the callback executes
/// it; a saved message is still a real byte observation, not encoding time.
pub struct Output<T> {
    pub value: T,
    messages: Option<Vec<Vec<u8>>>,
}
impl<T> Output<T> {
    pub fn value(value: T) -> Self {
        Self {
            value,
            messages: None,
        }
    }
    pub fn with_messages(value: T, messages: Vec<Vec<u8>>) -> Self {
        Self {
            value,
            messages: Some(messages),
        }
    }
}
#[derive(Clone, Debug, Serialize)]
pub struct CounterObservation {
    pub root_enabled: bool,
    pub root: Option<ops::Counts>,
    pub baseline_enabled: bool,
    pub baseline: arithmetic::Counts,
}
#[derive(Clone, Debug, Serialize)]
pub struct Record {
    pub label: Label,
    pub workload: Workload,
    pub callback_completed: bool,
    pub error: Option<String>,
    pub counts: CounterObservation,
    pub actual_wire_bytes: Option<usize>,
    pub actual_message_count: Option<usize>,
    pub mode: Mode,
    pub timing_enabled: bool,
    pub value_type: &'static str,
}
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    FormalNotAuthorized,
    NestedRecorder,
    CounterScopeLost,
    InvalidLabel(String),
    Callback(String),
    Plan(String),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}
thread_local! { static ACTIVE: Cell<bool> = const { Cell::new(false) }; }

/// One outer native callback owns both counter scopes. Nested recorders on the
/// same thread are rejected, so a total cannot accidentally restart a child's
/// counters or count a nested measurement again as an independent component.
struct Scope {
    active: bool,
}
impl Scope {
    fn begin() -> Result<Self, Error> {
        if ACTIVE.with(Cell::get) || arithmetic::snapshot_counts().is_some() {
            return Err(Error::NestedRecorder);
        }
        ACTIVE.with(|a| a.set(true));
        ops::reset();
        encoding::start_counts();
        Ok(Self { active: true })
    }
    fn finish(&mut self) -> Result<CounterObservation, Error> {
        if encoding::snapshot_counts().is_none() {
            return Err(Error::CounterScopeLost);
        }
        let root = ops::stop();
        let baseline = encoding::stop_counts();
        self.active = false;
        ACTIVE.with(|a| a.set(false));
        Ok(CounterObservation {
            root_enabled: cfg!(feature = "op-counts"),
            root: cfg!(feature = "op-counts").then_some(root),
            baseline_enabled: true,
            baseline,
        })
    }
}
impl Drop for Scope {
    fn drop(&mut self) {
        if self.active {
            let _ = ops::stop();
            let _ = encoding::stop_counts();
            ACTIVE.with(|a| a.set(false));
        }
    }
}

pub struct Recorder {
    mode: Mode,
    records: Vec<Record>,
    smoke_callbacks: usize,
}
impl Recorder {
    pub fn new(mode: Mode) -> Result<Self, Error> {
        if mode == Mode::Formal {
            return Err(Error::FormalNotAuthorized);
        }
        Ok(Self {
            mode,
            records: vec![],
            smoke_callbacks: 0,
        })
    }
    pub fn records(&self) -> &[Record] {
        &self.records
    }
    pub fn into_records(self) -> Vec<Record> {
        self.records
    }
    pub fn smoke_callbacks(&self) -> usize {
        self.smoke_callbacks
    }
    pub fn formal_samples(&self) -> usize {
        0
    }

    /// Invoke the actual protocol callback. It must not reset/stop a legacy
    /// counter scope or invoke a pre-existing counter-collecting benchmark.
    /// Smoke has no exported rows or elapsed-time fields.
    pub fn record<T>(
        &mut self,
        label: Label,
        workload: Workload,
        callback: impl FnOnce() -> Result<Output<T>, String>,
    ) -> Result<T, Error> {
        label.validate(&workload)?;
        let mut scope = Scope::begin()?;
        let start = (self.mode == Mode::Smoke).then(Instant::now);
        let result = callback();
        if let Some(start) = start {
            std::hint::black_box(start.elapsed());
        }
        let counts = scope.finish()?;
        if self.mode == Mode::Smoke {
            self.smoke_callbacks += 1;
            return result.map(|o| o.value).map_err(Error::Callback);
        }
        let sizes = result
            .as_ref()
            .ok()
            .and_then(|o| o.messages.as_ref())
            .map(|messages| (messages.iter().map(Vec::len).sum(), messages.len()));
        self.records.push(Record {
            label,
            workload,
            callback_completed: result.is_ok(),
            error: result.as_ref().err().cloned(),
            counts,
            actual_wire_bytes: sizes.map(|s| s.0),
            actual_message_count: sizes.map(|s| s.1),
            mode: self.mode,
            timing_enabled: false,
            value_type: "actual_native_callback_counts_and_optional_serialized_bytes",
        });
        result.map(|o| o.value).map_err(Error::Callback)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Target {
    Figure10A,
    TableIv,
    TableIvFragmented,
    Figure9B,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Account {
    Issuer,
    WholeSystem,
}
#[derive(Clone, Debug, Serialize)]
pub struct PlannedJob {
    pub target: Target,
    pub scheme: Scheme,
    pub curve: Option<&'static str>,
    pub k: Option<usize>,
    pub agents: Option<usize>,
    pub account: Option<Account>,
    pub native_style: &'static str,
    pub units_per_agent: Option<usize>,
    pub pools_per_agent: Option<usize>,
    pub expected_issuer_interactions: Option<usize>,
    pub planned_only: bool,
}
pub const FIG10_CURVES: [(&str, Scheme, &str); 3] = [
    ("DARLT", Scheme::Darlt, "native multi-unit blocks"),
    (
        "DARLT-ablation",
        Scheme::Darlt,
        "genuine independent single-unit tokens",
    ),
    (
        "SMA2RT",
        Scheme::Sma2rt,
        "independent tokens with random batch verification",
    ),
];
/// Required configurations only; generating this matrix does not execute jobs.
pub fn planned_jobs() -> Vec<PlannedJob> {
    let mut jobs = vec![];
    for (curve, scheme, style) in FIG10_CURVES {
        for k in K_VALUES {
            jobs.push(PlannedJob {
                target: Target::Figure10A,
                scheme,
                curve: Some(curve),
                k: Some(k),
                agents: None,
                account: None,
                native_style: style,
                units_per_agent: None,
                pools_per_agent: None,
                expected_issuer_interactions: None,
                planned_only: true,
            });
        }
    }
    for scheme in Scheme::ALL {
        for k in TABLE_IV_K {
            jobs.push(PlannedJob { target: Target::TableIv, scheme, curve: None,
                k: Some(k), agents: None, account: None,
                native_style: "generation offline/online; best/spec inclusive verification; backend; actual communication",
                units_per_agent: None, pools_per_agent: None,
                expected_issuer_interactions: None, planned_only: true });
        }
    }
    for scheme in [Scheme::Rp23D, Scheme::Lcb24] {
        jobs.push(PlannedJob { target:Target::TableIvFragmented,scheme,curve:None,k:Some(16),agents:None,account:None,
            native_style:"real sparse prior spends; actual intervals/subtrees; generation, merchant verification and native backend separate",
            units_per_agent:None,pools_per_agent:None,expected_issuer_interactions:None,planned_only:true });
    }
    for scheme in [Scheme::Darlt, Scheme::Sma2rt] {
        for agents in AGENT_VALUES {
            for account in [Account::Issuer, Account::WholeSystem] {
                jobs.push(PlannedJob {
                    target: Target::Figure9B,
                    scheme,
                    curve: None,
                    k: None,
                    agents: Some(agents),
                    account: Some(account),
                    native_style: "equal total quota 1024; issuer and complete system accounts",
                    units_per_agent: Some(1024 / agents),
                    pools_per_agent: (scheme == Scheme::Darlt).then_some(64 / agents),
                    expected_issuer_interactions: Some(if scheme == Scheme::Darlt {
                        1
                    } else {
                        agents
                    }),
                    planned_only: true,
                });
            }
        }
    }
    jobs
}
#[derive(Clone, Debug, Serialize)]
pub struct SchemeCoverage {
    pub scheme: Scheme,
    pub native_adapter_present: bool,
    pub execution_location: &'static str,
    pub all_role_stage_instrumentation_complete: bool,
    pub detailed_substages_required: bool,
    pub detailed_substages_complete: Option<bool>,
    pub interval_count: Option<usize>,
    pub subtree_count: Option<usize>,
    pub status: &'static str,
}
#[derive(Clone, Debug, Serialize)]
pub struct Coverage {
    pub schemes: Vec<SchemeCoverage>,
    pub planned_job_count: usize,
    pub formal_runner_implemented: bool,
    pub sampling_core_implemented: bool,
    pub fixed_batch_verification_implemented: bool,
    pub formal_ready: bool,
    pub authorized_timing_window: Option<&'static str>,
    pub formal_samples: usize,
    pub pending: Vec<String>,
}
pub fn coverage() -> Coverage {
    let plan: Value = serde_json::from_str(include_str!("measurement_plan.json"))
        .expect("checked-in measurement plan is valid JSON");
    coverage_for_plan(&plan)
}
fn coverage_for_plan(plan: &Value) -> Coverage {
    let ready = plan["timing_enabled"].as_bool().unwrap_or(false);
    Coverage {
        schemes: Scheme::ALL
            .into_iter()
            .map(|scheme| SchemeCoverage {
                scheme,
                native_adapter_present: scheme.adapter_present(),
                execution_location:if scheme==Scheme::Lcb24 {"root_blstrs_verifier_with_isolated_arkworks_prover"}
                    else if matches!(scheme,Scheme::Rp23C|Scheme::Rp23D){"isolated_blstrs_native_crate_using_shared_runtime"}else{"root_blstrs_workspace"},
                all_role_stage_instrumentation_complete: true,
                detailed_substages_required: scheme==Scheme::Darlt,
                detailed_substages_complete: (scheme==Scheme::Darlt).then_some(true),
                interval_count: None,
                subtree_count: None,
                status: if scheme==Scheme::Lcb24 {
                    "native roles and cold/hot workers passed; Table IV bank Groth16 verification and leaf/state backend are separate; paired calibration callbacks ready"
                } else if matches!(scheme,Scheme::Rp23C|Scheme::Rp23D) {
                    "native issuance roles, prepared Spend, merchant Verify, complete Deposit and shared runtime passed; approved native boundary and sequential control checked"
                } else if scheme.adapter_present() {
                    "native role/stage/cold-hot totals, shared state and required parameter scans passed; detailed substages required only for DARLT"
                } else {
                    "native implementation and adapter pending"
                },
            })
            .collect(),
        planned_job_count: planned_jobs().len(),
        formal_runner_implemented: true,
        sampling_core_implemented: true,
        fixed_batch_verification_implemented: true,
        formal_ready: ready,
        authorized_timing_window: None,
        formal_samples: 0,
        pending: if ready { vec![] } else {
            plan["formal_ready_pending"].as_array().into_iter().flatten()
                .filter_map(|v|v.as_str().map(str::to_owned)).collect()
        },
    }
}
#[derive(Clone, Debug, Serialize)]
pub struct PlanSummary {
    pub figure10a_curves: Vec<String>,
    pub k_values: Vec<usize>,
    pub table_iv_k: Vec<usize>,
    pub planned_jobs: usize,
    pub coverage: Coverage,
}
pub fn validate_plan(plan: &Value) -> Result<PlanSummary, Error> {
    let fail = |message: &str| Error::Plan(message.into());
    let values = |p: &Value| -> Result<Vec<usize>, Error> {
        p.as_array()
            .ok_or_else(|| fail("missing integer array"))?
            .iter()
            .map(|v| {
                v.as_u64()
                    .and_then(|n| usize::try_from(n).ok())
                    .ok_or_else(|| fail("invalid positive integer"))
            })
            .collect()
    };
    let k = values(&plan["scan"]["k"])?;
    if k != K_VALUES {
        return Err(fail("k grid differs from the configured nine-point scan"));
    }
    let curve_k = values(&plan["fig10a"]["k_values"])?;
    if curve_k != k {
        return Err(fail("Fig.10(a) k grid mismatch"));
    }
    let curve_ids = plan["fig10a"]["curves"]
        .as_array()
        .ok_or_else(|| fail("Fig.10(a) curve list missing"))?
        .iter()
        .map(|v| {
            v["id"]
                .as_str()
                .map(str::to_owned)
                .ok_or_else(|| fail("curve identifier missing"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let expected: Vec<_> = FIG10_CURVES.iter().map(|v| v.0.to_owned()).collect();
    if curve_ids != expected {
        return Err(fail(
            "Fig.10(a) must contain exactly the three attribute-policy curves",
        ));
    }
    let table_k = values(&plan["table_iv"]["k_values"])?;
    if table_k != TABLE_IV_K {
        return Err(fail("Table IV k grid mismatch"));
    }
    let schemes = plan["table_iv"]["schemes"]
        .as_array()
        .ok_or_else(|| fail("Table IV schemes missing"))?
        .iter()
        .map(|v| v.as_str().ok_or_else(|| fail("Table IV scheme label")))
        .collect::<Result<Vec<_>, _>>()?;
    if schemes != Scheme::ALL.map(Scheme::label) {
        return Err(fail("Table IV must retain all ten schemes"));
    }
    if plan["session_marker"] != "timing-session"
        || !plan["timing_window"].is_null()
        || plan["formal_samples_collected"].as_u64() != Some(0)
        || plan["timing_enabled"].as_bool().is_none()
    {
        return Err(fail(
            "formal sampling requires a ready plan and active timing window",
        ));
    }
    if plan["variant_selection"]["enabled"] != false
        || plan["fixed_verification"]["speed_selection"] != false
        || plan["fixed_verification"]["candidate_timing_enabled"] != false
        || plan["fixed_verification"]["specification_timing_enabled"] != false
        || plan["fixed_verification"]["coefficients"]["bits"] != 128
    {
        return Err(fail(
            "benchmark configuration requires fixed SET128 verification without candidate or specification timing",
        ));
    }
    for scheme in Scheme::ALL {
        let label = scheme.label();
        if plan["fixed_verification"]["profiles"][label].as_str()
            != crate::campaign::fixed_verification_profile(label)
        {
            return Err(fail("prescribed fixed verifier identity mismatch"));
        }
    }
    Ok(PlanSummary {
        figure10a_curves: curve_ids,
        k_values: k,
        table_iv_k: table_k,
        planned_jobs: planned_jobs().len(),
        coverage: coverage_for_plan(plan),
    })
}
pub fn validate_current_plan() -> Result<PlanSummary, Error> {
    let plan: Value = serde_json::from_str(include_str!("measurement_plan.json"))
        .map_err(|e| Error::Plan(e.to_string()))?;
    validate_plan(&plan)
}

#[cfg(test)]
mod tests {
    use super::*;
    use blstrs::{G1Projective as G1, Scalar as S};
    use group::Group;
    fn label() -> Label {
        Label {
            scheme: Scheme::Darlt,
            role: Role::Verifier,
            stage: Stage::VerificationCrypto,
            substage: Substage::Whole,
            cache: Cache::Hot,
            profile: "real-counter-fixture".into(),
            boundary: Boundary {
                wire_encoding_included: true,
                ..Boundary::default()
            },
        }
    }
    #[test]
    fn recorder_measures_actual_calls_and_bytes_and_keeps_disabled_counts_null() {
        let g = G1::generator();
        let two = g * S::from(2);
        let mut r = Recorder::new(Mode::ClockFree).unwrap();
        let point = r
            .record(
                label(),
                Workload {
                    k: Some(1),
                    ..Workload::default()
                },
                || {
                    let p = ops::mul(g, S::from(3));
                    let _ = ops::msm1(&[g, two], &[S::from(4), S::from(5)]);
                    let _ = arithmetic::g1_mul(g, S::from(3));
                    let _ = arithmetic::sum1(&[(g, S::from(4)), (two, S::from(5))]);
                    let _ = arithmetic::hash_scalar(b"counter-fixture", b"a");
                    let _ = encoding::hash_fr(b"counter-fixture", b"b");
                    let a = encoding::snapshot_counts().unwrap();
                    let b = encoding::snapshot_counts().unwrap();
                    assert_eq!(
                        serde_json::to_value(a).unwrap(),
                        serde_json::to_value(b).unwrap()
                    );
                    Ok(Output::with_messages(p, vec![p.to_compressed().to_vec()]))
                },
            )
            .unwrap();
        assert_eq!(point, g * S::from(3));
        let row = &r.records()[0];
        assert_eq!(row.actual_wire_bytes, Some(48));
        assert_eq!(row.counts.baseline.e1, 1);
        assert_eq!(row.counts.baseline.hz, 2);
        assert_eq!(row.counts.baseline.msm_sizes, [2]);
        assert_eq!(row.counts.root_enabled, cfg!(feature = "op-counts"));
        #[cfg(feature = "op-counts")]
        {
            let counts = row.counts.root.as_ref().unwrap();
            assert_eq!(counts.g1_exponentiations, 1);
            assert_eq!(counts.msm_g1_sizes, [2]);
        }
        #[cfg(not(feature = "op-counts"))]
        assert!(row.counts.root.is_none());
        assert!(arithmetic::snapshot_counts().is_none());
        assert_eq!(r.formal_samples(), 0);
    }
    #[test]
    fn nesting_errors_and_panics_cannot_leave_counters_owned() {
        let mut outer = Recorder::new(Mode::ClockFree).unwrap();
        outer
            .record(label(), Workload::default(), || {
                let mut inner = Recorder::new(Mode::ClockFree).unwrap();
                assert_eq!(
                    inner.record(label(), Workload::default(), || Ok(Output::value(()))),
                    Err(Error::NestedRecorder)
                );
                Ok(Output::value(()))
            })
            .unwrap();
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = outer.record(
                label(),
                Workload::default(),
                || -> Result<Output<()>, String> {
                    panic!("fixture");
                },
            );
        }));
        assert!(arithmetic::snapshot_counts().is_none());
        assert!(outer
            .record(label(), Workload::default(), || Ok(Output::value(())))
            .is_ok());
        encoding::start_counts();
        let _ = arithmetic::g1_mul(G1::generator(), S::from(3));
        assert_eq!(
            outer.record(label(), Workload::default(), || Ok(Output::value(()))),
            Err(Error::NestedRecorder)
        );
        assert_eq!(encoding::stop_counts().e1, 1);
        assert_eq!(
            outer.record(label(), Workload::default(), || {
                let _ = encoding::stop_counts();
                Ok(Output::value(()))
            }),
            Err(Error::CounterScopeLost)
        );
        assert!(outer
            .record(label(), Workload::default(), || Ok(Output::value(())))
            .is_ok());
    }
    #[test]
    fn smoke_has_no_export_and_formal_has_no_bypass() {
        assert!(matches!(
            Recorder::new(Mode::Formal),
            Err(Error::FormalNotAuthorized)
        ));
        let mut smoke = Recorder::new(Mode::Smoke).unwrap();
        smoke
            .record(label(), Workload::default(), || {
                Ok(Output::value(G1::generator()))
            })
            .unwrap();
        assert!(smoke.records().is_empty());
        assert_eq!(smoke.smoke_callbacks(), 1);
        assert_eq!(smoke.formal_samples(), 0);
    }
    #[test]
    fn matrix_and_plan_are_complete_requirements_not_claimed_measurements() {
        let summary = validate_current_plan().unwrap();
        assert_eq!(summary.planned_jobs, 87);
        assert_eq!(
            coverage()
                .schemes
                .iter()
                .filter(|s| s.native_adapter_present)
                .count(),
            10
        );
        let mut plan: Value = serde_json::from_str(include_str!("measurement_plan.json")).unwrap();
        assert_eq!(
            summary.coverage.formal_ready,
            plan["timing_enabled"].as_bool().unwrap()
        );
        for ready in [false, true] {
            plan["timing_enabled"] = Value::Bool(ready);
            let checked = validate_plan(&plan).unwrap();
            assert_eq!(checked.coverage.formal_ready, ready);
            assert_eq!(checked.coverage.pending.is_empty(), ready);
            assert_eq!(checked.coverage.formal_samples, 0);
            assert!(checked.coverage.authorized_timing_window.is_none());
        }
        let jobs = planned_jobs();
        assert_eq!(
            jobs.iter()
                .filter(|j| j.target == Target::Figure10A)
                .count(),
            27
        );
        assert_eq!(
            jobs.iter().filter(|j| j.target == Target::TableIv).count(),
            30
        );
        assert_eq!(
            jobs.iter()
                .filter(|j| j.target == Target::TableIvFragmented)
                .count(),
            2
        );
        assert_eq!(
            jobs.iter().filter(|j| j.target == Target::Figure9B).count(),
            28
        );
        assert!(jobs.iter().all(|j| j.planned_only));
        for job in jobs.iter().filter(|j| j.target == Target::Figure9B) {
            assert_eq!(job.units_per_agent.unwrap() * job.agents.unwrap(), 1024);
            if job.scheme == Scheme::Darlt {
                assert_eq!(job.pools_per_agent.unwrap() * job.agents.unwrap(), 64);
            }
        }
        let mut p: Value = serde_json::from_str(include_str!("measurement_plan.json")).unwrap();
        p["fig10a"]["curves"].as_array_mut().unwrap().pop();
        assert!(validate_plan(&p).is_err());
        let mut p: Value = serde_json::from_str(include_str!("measurement_plan.json")).unwrap();
        p["timing_window"] = serde_json::json!({"label":"not authorized here"});
        assert!(validate_plan(&p).is_err());
        p["timing_window"] = Value::Null;
        p["variant_selection"]["enabled"] = Value::Bool(true);
        assert!(validate_plan(&p).is_err());
        p["variant_selection"]["enabled"] = Value::Bool(false);
        p["fixed_verification"]["coefficients"]["bits"] = serde_json::json!(255);
        assert!(validate_plan(&p).is_err());
        p["fixed_verification"]["coefficients"]["bits"] = serde_json::json!(128);
        p["fixed_verification"]["profiles"]["NIAT"] = serde_json::json!("Specification");
        assert!(validate_plan(&p).is_err());
    }
}
