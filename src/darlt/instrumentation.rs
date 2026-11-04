//! Opt-in native DARLT spans. Clock-free checks never read a clock.
//! Inclusive spans may nest; exclusive durations subtract their actual children.
use serde::Serialize;
use std::{cell::RefCell, collections::BTreeMap, time::Instant};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Mode {
    ClockFree,
    DevelopmentProfile,
    AuthorizedBoundary,
}

#[derive(Clone, Debug, Serialize)]
pub struct Row {
    pub name: &'static str,
    pub calls: usize,
    pub inclusive_ns: Option<u64>,
    pub exclusive_ns: Option<u64>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Report {
    pub mode: Mode,
    pub timing_enabled: bool,
    pub formal_samples: usize,
    pub rows: Vec<Row>,
    pub partitions: Vec<Partition>,
    pub partition_sum_ns: Option<u64>,
}
/// Consecutive, nonoverlapping intervals from the same native execution.
#[derive(Clone, Debug, Serialize)]
pub struct Partition {
    pub name: &'static str,
    pub elapsed_ns: Option<u64>,
}
impl Report {
    /// Sum of the named native spans. An absent hook is an error, never a
    /// substitute outer duration. Clock-free observations have no duration.
    pub fn duration(&self, name: &str, exclusive: bool) -> Result<Option<u64>, String> {
        let row = self
            .rows
            .iter()
            .find(|row| row.name == name)
            .ok_or_else(|| format!("native DARLT span {name} was not executed"))?;
        Ok(if exclusive {
            row.exclusive_ns
        } else {
            row.inclusive_ns
        })
    }
}

struct Frame {
    name: &'static str,
    start: Option<Instant>,
    child_ns: u64,
}
struct Session {
    mode: Mode,
    stack: Vec<Frame>,
    rows: BTreeMap<&'static str, Row>,
    detailed: bool,
    last: Option<Instant>,
    partitions: Vec<Partition>,
}
impl Session {
    fn advance(&mut self, now: Option<Instant>, name: &'static str) {
        let elapsed_ns = self
            .last
            .zip(now)
            .map(|(a, b)| b.duration_since(a).as_nanos().min(u64::MAX as u128) as u64);
        self.last = now;
        if let Some(last) = self.partitions.last_mut().filter(|p| p.name == name) {
            last.elapsed_ns = last.elapsed_ns.zip(elapsed_ns).map(|(a, b)| a + b);
        } else {
            self.partitions.push(Partition { name, elapsed_ns });
        }
    }
}
thread_local! {
    static SESSION: RefCell<Option<Session>> = const { RefCell::new(None) };
}

/// This guard owns no protocol data and never changes a native return value.
#[must_use]
pub struct Span {
    active: bool,
}
#[inline]
pub fn span(name: &'static str) -> Span {
    let active = SESSION.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(session) = slot.as_mut() else {
            return false;
        };
        if !session.detailed
            && !name.starts_with("receive.")
            && !name.starts_with("verification.")
            && !name.starts_with("provision.")
        {
            return false;
        }
        let now = (session.mode != Mode::ClockFree).then(Instant::now);
        let previous = session.stack.last().map_or("other", |p| p.name);
        session.advance(now, previous);
        session.stack.push(Frame {
            name,
            start: now,
            child_ns: 0,
        });
        true
    });
    Span { active }
}
impl Drop for Span {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        SESSION.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(session) = slot.as_mut() else { return };
            let now = (session.mode != Mode::ClockFree).then(Instant::now);
            let previous = session.stack.last().map_or("other", |p| p.name);
            session.advance(now, previous);
            let Some(frame) = session.stack.pop() else {
                return;
            };
            let elapsed = frame.start.zip(now).map(|(start, end)| {
                end.duration_since(start).as_nanos().min(u64::MAX as u128) as u64
            });
            if let (Some(parent), Some(ns)) = (session.stack.last_mut(), elapsed) {
                parent.child_ns = parent.child_ns.saturating_add(ns);
            }
            // A polynomial/encoding helper can call another helper with the
            // same category. Count its invocation, but do not count its whole
            // elapsed time twice in that category's inclusive total.
            let nested_same_name = session.stack.iter().any(|parent| parent.name == frame.name);
            let row = session.rows.entry(frame.name).or_insert(Row {
                name: frame.name,
                calls: 0,
                inclusive_ns: elapsed.map(|_| 0),
                exclusive_ns: elapsed.map(|_| 0),
            });
            row.calls += 1;
            if let Some(ns) = elapsed {
                if !nested_same_name {
                    *row.inclusive_ns.as_mut().expect("profile row") += ns;
                }
                *row.exclusive_ns.as_mut().expect("profile row") +=
                    ns.saturating_sub(frame.child_ns);
            }
        });
    }
}

struct Cleanup;
impl Drop for Cleanup {
    fn drop(&mut self) {
        SESSION.with(|slot| {
            slot.borrow_mut().take();
        });
    }
}

/// Collect spans from one diagnostic execution. A nested
/// session is rejected rather than resetting another callback's observations.
pub fn collect<T>(mode: Mode, action: impl FnOnce() -> T) -> Result<(T, Report), String> {
    if mode == Mode::AuthorizedBoundary {
        return Err("authorized boundary requires a validated timing plan".into());
    }
    collect_inner(mode, true, action)
}

/// A configured timing window activates a
/// retained substage sample; its validity is checked around the callback.
pub(crate) fn collect_authorized<T>(
    plan: &serde_json::Value,
    action: impl FnOnce() -> T,
) -> Result<(T, Report), String> {
    crate::sampling::validate_wallclock_plan(plan).map_err(|e| e.to_string())?;
    let result = collect_inner(Mode::AuthorizedBoundary, true, action)?;
    crate::sampling::validate_wallclock_plan(plan).map_err(|e| e.to_string())?;
    Ok(result)
}

pub(crate) fn is_collecting() -> bool {
    SESSION.with(|slot| slot.borrow().is_some())
}

pub(crate) fn collect_boundary<T>(
    mode: Mode,
    detailed: bool,
    plan: Option<&serde_json::Value>,
    action: impl FnOnce() -> T,
) -> Result<(T, Report), String> {
    // BoundaryClock validates the configured timing window around its
    // outer timer. Keep the same native boundary free of window parsing work.
    if mode == Mode::AuthorizedBoundary && plan.is_none() {
        return Err("timing plan missing".into());
    }
    collect_inner(mode, detailed, action)
}

fn collect_inner<T>(
    mode: Mode,
    detailed: bool,
    action: impl FnOnce() -> T,
) -> Result<(T, Report), String> {
    SESSION.with(|slot| -> Result<(), String> {
        let mut slot = slot.borrow_mut();
        if slot.is_some() {
            return Err("nested DARLT instrumentation session".into());
        }
        *slot = Some(Session {
            mode,
            stack: Vec::new(),
            rows: BTreeMap::new(),
            detailed,
            last: (mode != Mode::ClockFree).then(Instant::now),
            partitions: Vec::new(),
        });
        Ok(())
    })?;
    let cleanup = Cleanup;
    let output = action();
    let mut session = SESSION
        .with(|slot| slot.borrow_mut().take())
        .expect("active session");
    drop(cleanup);
    if !session.stack.is_empty() {
        return Err("unfinished DARLT instrumentation span".into());
    }
    session.advance((mode != Mode::ClockFree).then(Instant::now), "other");
    let partition_sum_ns = if mode == Mode::ClockFree {
        None
    } else {
        session
            .partitions
            .iter()
            .try_fold(0u64, |sum, p| sum.checked_add(p.elapsed_ns?))
    };
    Ok((
        output,
        Report {
            mode,
            timing_enabled: mode == Mode::AuthorizedBoundary,
            formal_samples: usize::from(mode == Mode::AuthorizedBoundary),
            rows: session.rows.into_values().collect(),
            partitions: session.partitions,
            partition_sum_ns,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn formal_spans_require_approved_plan_before_any_native_callback() {
        let mut calls = 0;
        assert!(collect(Mode::AuthorizedBoundary, || calls += 1).is_err());
        assert!(
            collect_authorized(&serde_json::json!({"timing_enabled":false}), || {
                calls += 1
            })
            .is_err()
        );
        assert_eq!(calls, 0);
    }
    #[test]
    fn disabled_and_clock_free_spans_preserve_native_outputs() {
        let plain = {
            let _span = span("disabled");
            17
        };
        let (output, report) = collect(Mode::ClockFree, || {
            let _outer = span("outer");
            {
                let _inner = span("inner");
            }
            {
                let _inner = span("inner");
            }
            17
        })
        .unwrap();
        assert_eq!(plain, output);
        assert_eq!(report.rows.len(), 2);
        assert_eq!(report.rows[0].name, "inner");
        assert_eq!(report.rows[0].calls, 2);
        assert!(report
            .rows
            .iter()
            .all(|r| r.inclusive_ns.is_none() && r.exclusive_ns.is_none()));
        assert!(!report.timing_enabled);
        assert_eq!(report.formal_samples, 0);
    }
    #[test]
    fn nested_sessions_are_rejected_without_resetting_outer() {
        let (_, report) = collect(Mode::ClockFree, || {
            let _span = span("outer");
            assert!(collect(Mode::ClockFree, || ()).is_err());
        })
        .unwrap();
        assert_eq!(report.rows[0].name, "outer");
        assert_eq!(report.rows[0].calls, 1);
    }
    #[test]
    fn synthetic_consecutive_intervals_cover_gaps_and_do_not_double_count_children() {
        use std::time::Duration;
        let base = Instant::now();
        let mut session = Session {
            mode: Mode::DevelopmentProfile,
            stack: vec![],
            rows: BTreeMap::new(),
            detailed: true,
            last: Some(base),
            partitions: vec![],
        };
        session.advance(Some(base + Duration::from_nanos(3)), "other");
        session.advance(Some(base + Duration::from_nanos(8)), "decode");
        session.advance(Some(base + Duration::from_nanos(10)), "subgroup");
        session.advance(Some(base + Duration::from_nanos(14)), "decode");
        session.advance(Some(base + Duration::from_nanos(20)), "native");
        assert_eq!(
            session
                .partitions
                .iter()
                .map(|p| p.elapsed_ns.unwrap())
                .sum::<u64>(),
            20
        );
        assert_eq!(session.partitions[2].elapsed_ns, Some(2));
    }
}
