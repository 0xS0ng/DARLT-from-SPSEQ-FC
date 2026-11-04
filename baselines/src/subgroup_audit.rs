//! Optional observation of actual subgroup-check entry points. This module
//! never controls whether checks execute. Ordinary builds compile hooks out,
//! including the point encoding used only to correlate audit events.
use blstrs::{G1Projective, G2Projective, Gt};
use serde::Serialize;

#[derive(Clone, Debug, Serialize)]
pub struct Event {
    pub kind: String,
    pub encoding_hex: String,
    pub site: String,
    pub operation: String,
}
#[derive(Clone, Debug, Default, Serialize)]
pub struct Audit {
    pub enabled: bool,
    pub events: Vec<Event>,
}

#[cfg(feature = "subgroup-audit")]
mod enabled {
    use super::*;
    use std::cell::RefCell;
    thread_local! {
        static EVENTS: RefCell<Option<Vec<Event>>> = const { RefCell::new(None) };
        static FILTER: RefCell<(bool, usize)> = const { RefCell::new((false, 0)) };
    }
    pub fn record(kind: &str, bytes: &[u8], site: &str, operation: &str) {
        if FILTER.with(|s| {
            let s = s.borrow();
            s.0 && s.1 == 0
        }) {
            return;
        }
        EVENTS.with(|slot| {
            if let Some(events) = slot.borrow_mut().as_mut() {
                let mut encoding_hex = String::with_capacity(2 * bytes.len());
                const HEX: &[u8; 16] = b"0123456789abcdef";
                for &b in bytes {
                    encoding_hex.push(HEX[(b >> 4) as usize] as char);
                    encoding_hex.push(HEX[(b & 15) as usize] as char);
                }
                events.push(Event {
                    kind: kind.into(),
                    encoding_hex,
                    site: site.into(),
                    operation: operation.into(),
                });
            }
        });
    }
    pub fn active() -> bool {
        EVENTS.with(|s| s.borrow().is_some())
    }
    pub fn collect<T>(run: impl FnOnce() -> T) -> (T, Audit) {
        collect_filtered(false, run)
    }
    pub fn collect_filtered<T>(selected_only: bool, run: impl FnOnce() -> T) -> (T, Audit) {
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                EVENTS.with(|s| {
                    s.borrow_mut().take();
                });
                FILTER.with(|s| *s.borrow_mut() = (false, 0));
            }
        }
        EVENTS.with(|s| {
            assert!(s.borrow().is_none(), "nested subgroup audit");
            *s.borrow_mut() = Some(Vec::new());
        });
        FILTER.with(|s| *s.borrow_mut() = (selected_only, 0));
        let reset = Reset;
        let result = run();
        let events = EVENTS.with(|s| s.borrow_mut().take().unwrap());
        drop(reset);
        (
            result,
            Audit {
                enabled: true,
                events,
            },
        )
    }
    pub fn enter() {
        FILTER.with(|s| s.borrow_mut().1 += 1);
    }
    pub fn leave() {
        FILTER.with(|s| s.borrow_mut().1 -= 1);
    }
}

#[inline(always)]
pub fn decode(_kind: &str, _bytes: &[u8], _site: &str) {
    #[cfg(feature = "subgroup-audit")]
    enabled::record(_kind, _bytes, _site, "checked_decode");
}
#[inline(always)]
pub fn g1(_point: &G1Projective, _site: &str) {
    #[cfg(feature = "subgroup-audit")]
    if enabled::active() {
        enabled::record("G1", &_point.to_compressed(), _site, "membership");
    }
}
#[inline(always)]
pub fn g2(_point: &G2Projective, _site: &str) {
    #[cfg(feature = "subgroup-audit")]
    if enabled::active() {
        enabled::record("G2", &_point.to_compressed(), _site, "membership");
    }
}
#[inline(always)]
pub fn gt(_point: &Gt, _site: &str) {
    #[cfg(feature = "subgroup-audit")]
    if enabled::active() {
        enabled::record("GT", &crate::curve::enct(*_point), _site, "membership");
    }
}
#[inline(always)]
pub fn unencoded(_kind: &str, _site: &str) {
    #[cfg(feature = "subgroup-audit")]
    enabled::record(_kind, &[], _site, "membership");
}
pub struct Selected;
impl Drop for Selected {
    #[inline(always)]
    fn drop(&mut self) {
        #[cfg(feature = "subgroup-audit")]
        enabled::leave();
    }
}
#[inline(always)]
pub fn selected() -> Selected {
    #[cfg(feature = "subgroup-audit")]
    enabled::enter();
    Selected
}
pub fn collect_selected<T>(run: impl FnOnce() -> T) -> (T, Audit) {
    #[cfg(feature = "subgroup-audit")]
    return enabled::collect_filtered(true, run);
    #[cfg(not(feature = "subgroup-audit"))]
    (run(), Audit::default())
}
pub fn collect<T>(run: impl FnOnce() -> T) -> (T, Audit) {
    #[cfg(feature = "subgroup-audit")]
    return enabled::collect(run);
    #[cfg(not(feature = "subgroup-audit"))]
    (run(), Audit::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn observations_cannot_disable_checks_or_count_in_an_ordinary_build() {
        let mut ran = 0;
        let (value, audit) = collect(|| {
            ran += 1;
            decode("G1", &[1, 2], "test:decoder");
            7
        });
        assert_eq!(value, 7);
        assert_eq!(ran, 1);
        assert_eq!(audit.enabled, cfg!(feature = "subgroup-audit"));
        assert_eq!(
            audit.events.len(),
            usize::from(cfg!(feature = "subgroup-audit"))
        );
    }
    #[test]
    fn selected_observation_excludes_fixture_checks_without_suppressing_them() {
        let mut ran = 0;
        let (_, audit) = collect_selected(|| {
            ran += 1;
            decode("G1", &[1], "fixture");
            {
                let _region = selected();
                ran += 1;
                decode("G1", &[2], "selected");
            }
            ran += 1;
            decode("G1", &[3], "postcondition");
        });
        assert_eq!(ran, 3);
        assert_eq!(
            audit.events.len(),
            usize::from(cfg!(feature = "subgroup-audit"))
        );
        if audit.enabled {
            assert_eq!(audit.events[0].site, "selected");
        }
    }
}
