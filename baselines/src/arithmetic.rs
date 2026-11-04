//! Profile-2 arithmetic: shortcuts are executed, never counter-only discounts.
//! Shared arithmetic and counters preserve the native operation conventions.
use crate::curve as old;
pub use crate::curve::ScalarHashDomain;
pub use crate::curve::{
    digest, enc1, enc2, encs, enct, frame, g1_add, g2_add, gt_add, hash_g1, inv, multi_pair, pair,
    random_batch_weight128, random_nonzero, random_scalar, G1HashPrefix, G1, G2, GT, S,
};
use ff::Field;
use group::Group;
use serde::Serialize;
use std::cell::RefCell;
thread_local! {static HZ:RefCell<Option<u64>>=const{RefCell::new(None)};}
#[derive(Default, Clone, Debug, Serialize)]
pub struct Counts {
    pub e1: u64,
    pub e2: u64,
    pub et: u64,
    pub p: u64,
    pub mp_calls: u64,
    pub mp_terms: u64,
    pub h1: u64,
    pub hz: u64,
    pub mul1: u64,
    pub mul2: u64,
    pub mult: u64,
    pub msm_sizes: Vec<usize>,
    pub msm2_sizes: Vec<usize>,
}
pub fn start_counts() {
    old::start_counts();
    HZ.with(|z| *z.borrow_mut() = Some(0));
}
pub fn stop_counts() -> Counts {
    let z = old::stop_counts();
    let hz = HZ.with(|v| v.borrow_mut().take().unwrap_or(0));
    Counts {
        e1: z.e1,
        e2: z.e2,
        et: z.et,
        p: z.p,
        mp_calls: z.mp_calls,
        mp_terms: z.mp_terms,
        h1: z.h1,
        hz,
        mul1: z.mul1,
        mul2: z.mul2,
        mult: z.mult,
        msm_sizes: z.msm_sizes,
        msm2_sizes: z.msm2_sizes,
    }
}
/// Read both active counter layers without resetting either one. `None`
/// means no complete arithmetic counting scope is currently active.
pub fn snapshot_counts() -> Option<Counts> {
    let z = old::snapshot_counts()?;
    let hz = HZ.with(|v| *v.borrow())?;
    Some(Counts {
        e1: z.e1,
        e2: z.e2,
        et: z.et,
        p: z.p,
        mp_calls: z.mp_calls,
        mp_terms: z.mp_terms,
        h1: z.h1,
        hz,
        mul1: z.mul1,
        mul2: z.mul2,
        mult: z.mult,
        msm_sizes: z.msm_sizes,
        msm2_sizes: z.msm2_sizes,
    })
}
/// True when either native counting layer is active; does not clone counters.
pub fn counts_active() -> bool {
    old::counts_active() || HZ.with(|v| v.borrow().is_some())
}
fn count_hz() {
    HZ.with(|v| {
        if let Some(n) = v.borrow_mut().as_mut() {
            *n += 1
        }
    });
}
pub fn g1_mul(a: G1, b: S) -> G1 {
    if b == S::ZERO {
        G1::identity()
    } else if b == S::ONE {
        a
    } else if b == -S::ONE {
        -a
    } else {
        old::g1_mul(a, b)
    }
}
pub fn g2_mul(a: G2, b: S) -> G2 {
    if b == S::ZERO {
        G2::identity()
    } else if b == S::ONE {
        a
    } else if b == -S::ONE {
        -a
    } else {
        old::g2_mul(a, b)
    }
}
pub fn gt_mul(a: GT, b: S) -> GT {
    if b == S::ZERO {
        GT::identity()
    } else if b == S::ONE {
        a
    } else if b == -S::ONE {
        -a
    } else {
        old::gt_mul(a, b)
    }
}
/// Combine scalar coefficients for equal/opposite bases, then execute the
/// resulting real backend MSM. The log records the submitted nontrivial terms.
pub fn sum1(terms: &[(G1, S)]) -> G1 {
    let mut merged: Vec<(G1, S)> = vec![];
    for &(base, scalar) in terms {
        if let Some((_, x)) = merged.iter_mut().find(|(g, _)| *g == base) {
            *x += scalar
        } else if let Some((_, x)) = merged.iter_mut().find(|(g, _)| *g == -base) {
            *x -= scalar
        } else {
            merged.push((base, scalar))
        }
    }
    let mut trivial = G1::identity();
    let mut nontrivial = vec![];
    for (g, x) in merged {
        if x == S::ONE {
            trivial = g1_add(trivial, g);
        } else if x == -S::ONE {
            trivial = g1_add(trivial, -g);
        } else if x != S::ZERO {
            nontrivial.push((g, x));
        }
    }
    g1_add(trivial, old::sum1(&nontrivial))
}
/// Equal/opposite-base simplification followed by a real G2 backend MSM.
pub fn sum2(terms: &[(G2, S)]) -> G2 {
    let mut merged: Vec<(G2, S)> = vec![];
    for &(base, scalar) in terms {
        if let Some((_, x)) = merged.iter_mut().find(|(g, _)| *g == base) {
            *x += scalar;
        } else if let Some((_, x)) = merged.iter_mut().find(|(g, _)| *g == -base) {
            *x -= scalar;
        } else {
            merged.push((base, scalar));
        }
    }
    let mut trivial = G2::identity();
    let mut nontrivial = vec![];
    for (g, x) in merged {
        if x == S::ONE {
            trivial = g2_add(trivial, g);
        } else if x == -S::ONE {
            trivial = g2_add(trivial, -g);
        } else if x != S::ZERO {
            nontrivial.push((g, x));
        }
    }
    g2_add(trivial, old::sum2(&nontrivial))
}
/// An execution-local cache; owning protocol code must not persist this object
/// across sessions. Equal/opposite scalars and bases reuse exact computed points.
#[derive(Default)]
pub struct G1Products(Vec<(G1, S, G1)>);
impl G1Products {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn mul(&mut self, g: G1, x: S) -> G1 {
        if x == S::ZERO {
            return G1::identity();
        }
        if x == S::ONE {
            return g;
        }
        if x == -S::ONE {
            return -g;
        }
        for &(base, s, value) in &self.0 {
            if (base == g && s == x) || (base == -g && s == -x) {
                return value;
            }
            if (base == g && s == -x) || (base == -g && s == x) {
                return -value;
            }
        }
        let value = g1_mul(g, x);
        self.0.push((g, x, value));
        value
    }
}
pub fn hash_scalar(tag: &[u8], input: &[u8]) -> S {
    count_hz();
    old::hash_scalar(tag, input)
}
#[derive(Clone)]
pub struct ScalarHashPrefix(old::ScalarHashPrefix);
impl ScalarHashPrefix {
    pub fn new(tag: &[u8], input_len: usize, prefix: &[u8]) -> Self {
        Self(old::ScalarHashPrefix::new(tag, input_len, prefix))
    }
    pub fn finish(&self, suffix: &[u8]) -> S {
        count_hz();
        self.0.finish(suffix)
    }
}
/// Installed immutable prefix states for public transcript lengths. Unknown
/// lengths retain the exact original transcript using a cached domain/byte prefix.
#[derive(Clone)]
pub struct CachedScalarHashPrefix {
    domain: ScalarHashDomain,
    prefix: Vec<u8>,
    states: std::collections::BTreeMap<usize, old::ScalarHashPrefix>,
}
impl CachedScalarHashPrefix {
    pub fn new(tag: &[u8], public_prefix: &[u8], suffix_lengths: &[usize]) -> Self {
        let domain = ScalarHashDomain::new(tag);
        let states = suffix_lengths
            .iter()
            .map(|&n| {
                (
                    n,
                    domain.prefix(
                        public_prefix
                            .len()
                            .checked_add(n)
                            .expect("transcript length"),
                        public_prefix,
                    ),
                )
            })
            .collect();
        Self {
            domain,
            prefix: public_prefix.to_vec(),
            states,
        }
    }
    pub fn prepared(&self, suffix_len: usize) -> ScalarHashPrefix {
        ScalarHashPrefix(self.states.get(&suffix_len).cloned().unwrap_or_else(|| {
            self.domain.prefix(
                self.prefix
                    .len()
                    .checked_add(suffix_len)
                    .expect("transcript length"),
                &self.prefix,
            )
        }))
    }
    pub fn finish(&self, suffix: &[u8]) -> S {
        self.prepared(suffix.len()).finish(suffix)
    }
}
pub fn valid1(a: G1, nonzero: bool) -> bool {
    (!nonzero || a != G1::identity()) && bool::from(a.is_on_curve()) && {
        crate::subgroup_audit::g1(&a, "arithmetic::valid1");
        bool::from(blstrs::G1Affine::from(a).is_torsion_free())
    }
}
pub fn valid2(a: G2, nonzero: bool) -> bool {
    (!nonzero || a != G2::identity()) && bool::from(a.is_on_curve()) && {
        crate::subgroup_audit::g2(&a, "arithmetic::valid2");
        bool::from(blstrs::G2Affine::from(a).is_torsion_free())
    }
}

/// Private holder-owned invocation byte cache, populated in preparation and
/// extended only for locally derived online points. Raw projective coordinates
/// are the lookup key: a compressed-encoding collision can never authenticate
/// another point. This cache supplies bytes, never skips validation.
/// Different representations of the same point safely fall back to encoding.
pub(crate) struct CanonicalPointCache {
    g1: std::collections::HashMap<[u64; 18], Vec<u8>>,
    g2: std::collections::HashMap<[u64; 36], Vec<u8>>,
}
impl CanonicalPointCache {
    pub(crate) fn new() -> Self {
        Self {
            g1: Default::default(),
            g2: Default::default(),
        }
    }
    fn key1(g: G1) -> [u64; 18] {
        let p: &blst::blst_p1 = g.as_ref();
        let mut key = [0; 18];
        key[0..6].copy_from_slice(&p.x.l);
        key[6..12].copy_from_slice(&p.y.l);
        key[12..18].copy_from_slice(&p.z.l);
        key
    }
    fn key2(g: G2) -> [u64; 36] {
        let p: &blst::blst_p2 = g.as_ref();
        let mut key = [0; 36];
        for (j, v) in [
            p.x.fp[0].l,
            p.x.fp[1].l,
            p.y.fp[0].l,
            p.y.fp[1].l,
            p.z.fp[0].l,
            p.z.fp[1].l,
        ]
        .iter()
        .enumerate()
        {
            key[j * 6..j * 6 + 6].copy_from_slice(v);
        }
        key
    }
    pub(crate) fn insert1(&mut self, g: G1) {
        self.g1.entry(Self::key1(g)).or_insert_with(|| enc1(g));
    }
    pub(crate) fn insert2(&mut self, g: G2) {
        self.g2.entry(Self::key2(g)).or_insert_with(|| enc2(g));
    }
    pub(crate) fn enc1(&self, g: G1) -> Vec<u8> {
        self.g1
            .get(&Self::key1(g))
            .cloned()
            .unwrap_or_else(|| enc1(g))
    }
    pub(crate) fn enc2(&self, g: G2) -> Vec<u8> {
        self.g2
            .get(&Self::key2(g))
            .cloned()
            .unwrap_or_else(|| enc2(g))
    }
}
#[cfg(test)]
mod canonical_cache_tests {
    use super::*;
    use group::Group;
    #[test]
    #[allow(clippy::unnecessary_get_then_check)]
    fn raw_coordinate_cache_does_not_alias_offcurve_compression() {
        let g = G1::generator();
        let bad = G1::from_raw_unchecked(g.x(), g.y() + g.z(), g.z());
        assert_eq!(bad.to_compressed(), g.to_compressed());
        assert_ne!(bad, g);
        let mut cache = CanonicalPointCache::new();
        cache.insert1(g);
        assert!(cache.g1.get(&CanonicalPointCache::key1(bad)).is_none());
        assert_eq!(cache.enc1(bad), enc1(bad));
        assert!(!valid1(bad, false));
    }
}
