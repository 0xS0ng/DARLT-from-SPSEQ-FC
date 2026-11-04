//! Retained-attempt sampling and statistics for the later authorized run.
//! Synthetic observations never consult a clock or become performance data.
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{
    collections::BTreeSet,
    fmt,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

pub const WARMUP: usize = 10;
pub const CV_LIMIT: f64 = 0.05;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SampleClass {
    Protocol,
    SlowProtocol,
    Primitive,
    LongCallback,
}
impl SampleClass {
    pub fn retained(self) -> usize {
        match self {
            Self::Protocol => 100,
            Self::SlowProtocol => 20,
            Self::Primitive => 1000,
            Self::LongCallback => 5,
        }
    }
    pub fn warmup(self) -> usize {
        if self == Self::LongCallback {
            1
        } else {
            WARMUP
        }
    }
}
#[derive(Clone, Debug, Serialize)]
pub struct Candidate {
    pub name: String,
    pub class: SampleClass,
    pub safe: bool,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Source {
    WallClock,
    Synthetic,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Phase {
    Warmup,
    Retained,
}
#[derive(Clone, Debug, Serialize)]
pub struct Invocation {
    pub attempt: usize,
    pub phase: Phase,
    pub round: usize,
    pub candidate: usize,
    pub index: usize,
}
#[derive(Clone, Debug, Serialize)]
pub struct Observation {
    pub invocation: Invocation,
    pub elapsed_ns: Option<u64>,
    pub error: Option<String>,
}
#[derive(Clone, Debug, Serialize)]
pub struct Statistics {
    pub n: usize,
    pub mean_ns: f64,
    pub sample_sd_ns: f64,
    pub cv: Option<f64>,
}
impl Statistics {
    /// Welford's sample variance, with denominator n-1; raw values stay intact.
    pub fn from_ns(values: &[u64]) -> Result<Self, Error> {
        if values.len() < 2 {
            return Err(Error("sample SD needs at least two values".into()));
        }
        let (mut mean, mut m2) = (0.0, 0.0);
        for (i, value) in values.iter().enumerate() {
            let delta = *value as f64 - mean;
            mean += delta / (i + 1) as f64;
            m2 += delta * (*value as f64 - mean);
        }
        let sd = (m2.max(0.0) / (values.len() - 1) as f64).sqrt();
        Ok(Self {
            n: values.len(),
            mean_ns: mean,
            sample_sd_ns: sd,
            cv: (mean > 0.0).then_some(sd / mean),
        })
    }
    pub fn needs_remeasurement(&self) -> bool {
        self.cv.is_none_or(|cv| cv > CV_LIMIT)
    }
}
#[derive(Clone, Debug, Serialize)]
pub struct Summary {
    pub candidate: Candidate,
    pub expected_warmups: usize,
    pub completed_warmups: usize,
    pub expected_samples: usize,
    pub completed_samples: usize,
    pub failures: usize,
    pub statistics: Option<Statistics>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Outcome {
    Stable,
    RemeasureRequired,
    CallbackFailed,
}
#[derive(Clone, Debug, Serialize)]
pub struct Attempt {
    pub number: usize,
    pub workload: String,
    pub source: Source,
    pub timing_enabled: bool,
    pub observations: Vec<Observation>,
    pub summaries: Vec<Summary>,
    pub outcome: Outcome,
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Error(pub String);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
impl std::error::Error for Error {}

fn validate_candidates(candidates: &[Candidate]) -> Result<(), Error> {
    let names: BTreeSet<_> = candidates.iter().map(|v| v.name.as_str()).collect();
    if candidates.is_empty() || names.len() != candidates.len() || names.contains("") {
        return Err(Error(
            "candidate names must be nonempty and distinct".into(),
        ));
    }
    Ok(())
}

/// Different sample counts are spread over the same rounds. At every round
/// rotate the candidate order; do not finish one complete candidate first.
pub fn schedule(candidates: &[Candidate], attempt: usize) -> Result<Vec<Invocation>, Error> {
    validate_candidates(candidates)?;
    if attempt == 0 {
        return Err(Error("attempt numbering starts at1".into()));
    }
    let mut out = vec![];
    for phase in [Phase::Warmup, Phase::Retained] {
        let counts: Vec<_> = candidates
            .iter()
            .map(|c| {
                if phase == Phase::Warmup {
                    c.class.warmup()
                } else {
                    c.class.retained()
                }
            })
            .collect();
        let rounds = *counts.iter().max().expect("nonempty candidates");
        for round in 0..rounds {
            let start = (round + attempt - 1) % candidates.len();
            for offset in 0..candidates.len() {
                let candidate = (start + offset) % candidates.len();
                let before = round * counts[candidate] / rounds;
                let after = (round + 1) * counts[candidate] / rounds;
                if after != before {
                    out.push(Invocation {
                        attempt,
                        phase,
                        round,
                        candidate,
                        index: before,
                    });
                }
            }
        }
    }
    Ok(out)
}

/// Fixture construction is outside the timed operation. Implementors own
/// native per-trial state and define the measured protocol/role boundary.
pub trait NativeOperation {
    fn prepare(&mut self, invocation: &Invocation) -> Result<(), String>;
    fn execute(&mut self, invocation: &Invocation) -> Result<(), String>;
}

struct Window {
    start: u64,
    end: Option<u64>,
}

/// Shared authorization check for isolated native workers. No timer or
/// protocol callback is reached when the plan/window has not been authorized.
pub fn validate_wallclock_plan(plan: &Value) -> Result<(), Error> {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| Error(e.to_string()))?
        .as_secs();
    Window::from_plan_at(plan, now)?.check().map_err(Error)
}
impl Window {
    fn from_plan_at(plan: &Value, now: u64) -> Result<Self, Error> {
        if plan["timing_enabled"] != true || plan["session_marker"] != "timing-session" {
            return Err(Error(
                "formal timing is not ready/authorized in this plan".into(),
            ));
        }
        for (name, expected) in [
            ("warmup", 10),
            ("retained_default", 100),
            ("retained_slow", 20),
            ("primitive", 1000),
        ] {
            if plan["sample_counts"][name].as_u64() != Some(expected) {
                return Err(Error(
                    "sampling counts differ from the specified plan".into(),
                ));
            }
        }
        let value = &plan["timing_window"];
        if value["session_marker"] != "timing-session"
            || value["label"].as_str().is_none_or(str::is_empty)
        {
            return Err(Error(
                "a documented timing-session timing window is required".into(),
            ));
        }
        let start = value["start_unix_seconds"]
            .as_u64()
            .ok_or_else(|| Error("invalid timing-window start".into()))?;
        let end = value["end_unix_seconds"].as_u64();
        if end.is_none() && plan["one_session_no_duration_limit"] != true {
            return Err(Error("unbounded timing session was not specified".into()));
        }
        if now < start || end.is_some_and(|end| start >= end || now >= end) {
            return Err(Error("outside the approved timing window".into()));
        }
        Ok(Self { start, end })
    }
    fn check(&self) -> Result<(), String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| e.to_string())?
            .as_secs();
        if now < self.start || self.end.is_some_and(|end| now >= end) {
            Err("approved timing window is not active".into())
        } else {
            Ok(())
        }
    }
}

#[derive(Default)]
pub struct Sampler {
    attempts: Vec<Attempt>,
}
impl Sampler {
    pub fn attempts(&self) -> &[Attempt] {
        &self.attempts
    }
    pub fn into_attempts(self) -> Vec<Attempt> {
        self.attempts
    }

    /// Synthetic observations without Instant or native work,
    /// source=Synthetic and timing_enabled=false regardless of the input plan.
    pub fn record_synthetic_attempt(
        &mut self,
        workload: &str,
        candidates: &[Candidate],
        mut duration: impl FnMut(&Invocation) -> Result<u64, String>,
    ) -> Result<&Attempt, Error> {
        self.collect(
            workload,
            candidates,
            Source::Synthetic,
            |invocation| match duration(invocation) {
                Ok(ns) => (Some(ns), None),
                Err(error) => (None, Some(error)),
            },
        )
    }

    /// Validate the sampling window before constructing inputs or invoking callbacks.
    pub fn run_wallclock_attempt(
        &mut self,
        plan: &Value,
        workload: &str,
        candidates: &[Candidate],
        operation: &mut impl NativeOperation,
    ) -> Result<&Attempt, Error> {
        if plan["timing_enabled"] != true || plan["timing_window"].is_null() {
            return Err(Error(
                "current plan does not authorize formal timing".into(),
            ));
        }
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| Error(e.to_string()))?
            .as_secs();
        let window = Window::from_plan_at(plan, now)?;
        self.collect(workload, candidates, Source::WallClock, |invocation| {
            if let Err(error) = window
                .check()
                .and_then(|()| operation.prepare(invocation))
                .and_then(|()| window.check())
            {
                return (None, Some(format!("prepare/window: {error}")));
            }
            let start = Instant::now();
            let result = operation.execute(invocation);
            let elapsed = start.elapsed();
            let ns = match u64::try_from(elapsed.as_nanos()) {
                Ok(ns) => ns,
                Err(_) => return (None, Some("elapsed nanoseconds overflow".into())),
            };
            let error = result
                .err()
                .map(|e| format!("execute: {e}"))
                .or_else(|| window.check().err());
            (Some(ns), error)
        })
    }

    /// The isolated worker owns the monotonic timer around its native
    /// boundary. IPC, fixture preparation and coordinator work stay outside
    /// the returned duration. The coordinator independently checks the same
    /// authorization window before and after each observation.
    pub fn run_worker_attempt(
        &mut self,
        plan: &Value,
        workload: &str,
        candidates: &[Candidate],
        mut observe: impl FnMut(&Invocation) -> Result<u64, String>,
    ) -> Result<&Attempt, Error> {
        validate_wallclock_plan(plan)?;
        self.collect(workload, candidates, Source::WallClock, |invocation| {
            if let Err(error) = validate_wallclock_plan(plan) {
                return (None, Some(error.to_string()));
            }
            let result = observe(invocation);
            match result {
                Ok(ns) => (
                    Some(ns),
                    validate_wallclock_plan(plan).err().map(|e| e.to_string()),
                ),
                Err(error) => (None, Some(error)),
            }
        })
    }

    fn collect(
        &mut self,
        workload: &str,
        candidates: &[Candidate],
        source: Source,
        mut observe: impl FnMut(&Invocation) -> (Option<u64>, Option<String>),
    ) -> Result<&Attempt, Error> {
        if workload.is_empty() {
            return Err(Error("workload label is empty".into()));
        }
        let number = self.attempts.len() + 1;
        let schedule = schedule(candidates, number)?;
        let mut observations = vec![];
        for invocation in schedule {
            let (elapsed_ns, error) = observe(&invocation);
            let failed = error.is_some();
            observations.push(Observation {
                invocation,
                elapsed_ns,
                error,
            });
            if failed {
                break;
            }
        }
        let summaries: Vec<_> = candidates
            .iter()
            .enumerate()
            .map(|(i, candidate)| {
                let rows: Vec<_> = observations
                    .iter()
                    .filter(|row| row.invocation.candidate == i)
                    .collect();
                let completed_warmups = rows
                    .iter()
                    .filter(|row| row.invocation.phase == Phase::Warmup && row.error.is_none())
                    .count();
                let values: Vec<_> = rows
                    .iter()
                    .filter(|row| row.invocation.phase == Phase::Retained && row.error.is_none())
                    .filter_map(|row| row.elapsed_ns)
                    .collect();
                Summary {
                    candidate: candidate.clone(),
                    expected_warmups: candidate.class.warmup(),
                    completed_warmups,
                    expected_samples: candidate.class.retained(),
                    completed_samples: values.len(),
                    failures: rows.iter().filter(|row| row.error.is_some()).count(),
                    statistics: Statistics::from_ns(&values).ok(),
                }
            })
            .collect();
        let outcome = if observations.iter().any(|row| row.error.is_some()) {
            Outcome::CallbackFailed
        } else if summaries.iter().any(|s| {
            s.completed_warmups != s.expected_warmups
                || s.completed_samples != s.expected_samples
                || s.statistics
                    .as_ref()
                    .is_none_or(Statistics::needs_remeasurement)
        }) {
            Outcome::RemeasureRequired
        } else {
            Outcome::Stable
        };
        self.attempts.push(Attempt {
            number,
            workload: workload.into(),
            source,
            timing_enabled: source == Source::WallClock,
            observations,
            summaries,
            outcome,
        });
        Ok(self.attempts.last().expect("just appended full attempt"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn candidate(name: &str, class: SampleClass) -> Candidate {
        Candidate {
            name: name.into(),
            class,
            safe: true,
        }
    }
    #[test]
    fn sample_sd_and_strict_cv_threshold_are_not_population_statistics() {
        let s = Statistics::from_ns(&[1, 2, 3]).unwrap();
        assert_eq!(s.mean_ns, 2.0);
        assert_eq!(s.sample_sd_ns, 1.0);
        assert_eq!(s.cv, Some(0.5));
        let threshold = Statistics::from_ns(&[95, 100, 105]).unwrap();
        assert_eq!(threshold.cv, Some(CV_LIMIT));
        assert!(!threshold.needs_remeasurement());
        assert!(Statistics::from_ns(&[94, 100, 106])
            .unwrap()
            .needs_remeasurement());
        assert!(Statistics::from_ns(&[0, 0]).unwrap().needs_remeasurement());
        assert!(Statistics::from_ns(&[1]).is_err());
    }
    #[test]
    fn different_sample_counts_are_explicit_and_spread_across_rounds() {
        let candidates = [
            candidate("ordinary", SampleClass::Protocol),
            candidate("slow", SampleClass::SlowProtocol),
            candidate("primitive", SampleClass::Primitive),
        ];
        let order = schedule(&candidates, 1).unwrap();
        assert_eq!(order.len(), 30 + 100 + 20 + 1000);
        for (i, c) in candidates.iter().enumerate() {
            assert_eq!(
                order
                    .iter()
                    .filter(|x| x.candidate == i && x.phase == Phase::Warmup)
                    .count(),
                10
            );
            let retained: Vec<_> = order
                .iter()
                .filter(|x| x.candidate == i && x.phase == Phase::Retained)
                .collect();
            assert_eq!(retained.len(), c.class.retained());
            assert_eq!(retained.last().unwrap().round, 999);
            assert_eq!(
                retained.iter().map(|x| x.index).collect::<Vec<_>>(),
                (0..c.class.retained()).collect::<Vec<_>>()
            );
        }
        let same = [
            candidate("a", SampleClass::Protocol),
            candidate("b", SampleClass::Protocol),
            candidate("c", SampleClass::Protocol),
        ];
        let order = schedule(&same, 1).unwrap();
        assert_eq!(order[0].candidate, 0);
        assert_eq!(order[3].candidate, 1);
        assert_eq!(order[6].candidate, 2);
        assert!(schedule(&[same[0].clone(), same[0].clone()], 1).is_err());
    }
    #[test]
    fn warmups_do_not_enter_statistics_and_entire_attempts_are_retained() {
        let candidates = [candidate("safe", SampleClass::Protocol)];
        let mut sampler = Sampler::default();
        let a = sampler
            .record_synthetic_attempt("k16", &candidates, |i| {
                Ok(if i.phase == Phase::Warmup {
                    1_000_000
                } else if i.index % 2 == 0 {
                    50
                } else {
                    150
                })
            })
            .unwrap();
        assert_eq!(a.outcome, Outcome::RemeasureRequired);
        assert_eq!(a.summaries[0].statistics.as_ref().unwrap().mean_ns, 100.0);
        let b = sampler
            .record_synthetic_attempt("k16", &candidates, |i| {
                Ok(if i.phase == Phase::Warmup {
                    9_999_999
                } else {
                    100
                })
            })
            .unwrap();
        assert_eq!(b.outcome, Outcome::Stable);
        assert_eq!(b.summaries[0].statistics.as_ref().unwrap().n, 100);
        assert_eq!(sampler.attempts().len(), 2);
        assert_eq!(sampler.attempts()[0].observations.len(), 110);
        assert_eq!(sampler.attempts()[1].observations.len(), 110);
        assert!(sampler
            .attempts()
            .iter()
            .all(|a| a.source == Source::Synthetic && !a.timing_enabled));
    }
    #[test]
    fn failed_callback_keeps_partial_attempt_and_next_attempt_is_whole() {
        let candidates = [candidate("safe", SampleClass::Protocol)];
        let mut sampler = Sampler::default();
        let a = sampler
            .record_synthetic_attempt("failure", &candidates, |i| {
                if i.phase == Phase::Retained && i.index == 3 {
                    Err("native proof rejected".into())
                } else {
                    Ok(100)
                }
            })
            .unwrap();
        assert_eq!(a.outcome, Outcome::CallbackFailed);
        assert_eq!(a.observations.len(), 14);
        assert_eq!(a.summaries[0].completed_samples, 3);
        assert_eq!(
            a.observations.last().unwrap().error.as_deref(),
            Some("native proof rejected")
        );
        let b = sampler
            .record_synthetic_attempt("failure", &candidates, |_| Ok(100))
            .unwrap();
        assert_eq!(b.number, 2);
        assert_eq!(b.observations.len(), 110);
        assert_eq!(sampler.attempts().len(), 2);
    }
    #[test]
    fn current_development_plan_rejects_before_any_native_work() {
        struct Never;
        impl NativeOperation for Never {
            fn prepare(&mut self, _: &Invocation) -> Result<(), String> {
                panic!("must not prepare")
            }
            fn execute(&mut self, _: &Invocation) -> Result<(), String> {
                panic!("must not time")
            }
        }
        let plan: Value = serde_json::from_str(include_str!("measurement_plan.json")).unwrap();
        let mut sampler = Sampler::default();
        assert!(sampler
            .run_wallclock_attempt(
                &plan,
                "current",
                &[candidate("x", SampleClass::Protocol)],
                &mut Never
            )
            .is_err());
        assert!(sampler.attempts().is_empty());
        let authorized = serde_json::json!({"timing_enabled":true,"session_marker":"timing-session",
            "sample_counts":{"warmup":10,"retained_default":100,"retained_slow":20,"primitive":1000},
            "timing_window":{"session_marker":"timing-session","label":"synthetic gate only","start_unix_seconds":100,"end_unix_seconds":200}});
        assert!(Window::from_plan_at(&authorized, 150).is_ok());
        assert!(Window::from_plan_at(&authorized, 99).is_err());
        assert!(Window::from_plan_at(&authorized, 200).is_err());
    }
    #[test]
    fn long_callback_has_one_warmup_and_five_fresh_retained_slots() {
        let candidates = [
            candidate("long", SampleClass::LongCallback),
            candidate("ordinary", SampleClass::Protocol),
        ];
        let slots = schedule(&candidates, 1).unwrap();
        for (index, warmup, retained) in [(0, 1, 5), (1, 10, 100)] {
            assert_eq!(
                slots
                    .iter()
                    .filter(|s| s.candidate == index && s.phase == Phase::Warmup)
                    .count(),
                warmup
            );
            assert_eq!(
                slots
                    .iter()
                    .filter(|s| s.candidate == index && s.phase == Phase::Retained)
                    .count(),
                retained
            );
        }
    }
    #[test]
    fn unbounded_single_session_still_requires_explicit_authorization_and_start() {
        let mut plan = serde_json::json!({"timing_enabled":true,"session_marker":"timing-session",
            "one_session_no_duration_limit":true,
            "sample_counts":{"warmup":10,"retained_default":100,"retained_slow":20,"primitive":1000},
            "timing_window":{"session_marker":"timing-session","label":"synthetic authorization test only","start_unix_seconds":100}});
        assert!(Window::from_plan_at(&plan, 100).is_ok());
        assert!(Window::from_plan_at(&plan, u64::MAX - 1).is_ok());
        assert!(Window::from_plan_at(&plan, 99).is_err());
        plan["one_session_no_duration_limit"] = serde_json::json!(false);
        assert!(Window::from_plan_at(&plan, 150).is_err());
        plan["one_session_no_duration_limit"] = serde_json::json!(true);
        plan["timing_enabled"] = serde_json::json!(false);
        assert!(Window::from_plan_at(&plan, 150).is_err());
    }
}
