//! Actual backend-call counters for the separate `op-counts` build.
//!
//! Group exponentiations count scalar multiplication operators, including
//! multiplication by zero or one when the implementation actually calls them.
//! MSMs are recorded as one call with their input size; their backend internals
//! are not counted again as individual exponentiations. Pairing input terms are
//! counted before batching, while Miller terms count the submitted backend list.
use blstrs::{
    Bls12, G1Affine, G1Projective as G1, G2Affine, G2Prepared, G2Projective as G2, Gt,
    MillerLoopResult, Scalar,
};
use group::Group;
use pairing::{MillerLoopResult as _, MultiMillerLoop};
use serde::Serialize;
use std::ops::{Mul, MulAssign};

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct Counts {
    pub g1_exponentiations: u64,
    pub g2_exponentiations: u64,
    pub gt_exponentiations: u64,
    pub pairing_input_terms: u64,
    pub pairing_calls: u64,
    pub miller_loop_terms: u64,
    pub miller_loop_calls: u64,
    pub final_exponentiations: u64,
    pub msm_g1_sizes: Vec<usize>,
    pub msm_g2_sizes: Vec<usize>,
}

#[cfg(feature = "op-counts")]
mod counter {
    use super::Counts;
    use std::cell::RefCell;

    #[derive(Default)]
    struct State {
        enabled: bool,
        counts: Counts,
    }

    thread_local! {
        static CURRENT: RefCell<State> = RefCell::new(State::default());
    }

    pub(super) fn update(change: impl FnOnce(&mut Counts)) {
        CURRENT.with(|current| {
            let mut state = current.borrow_mut();
            if state.enabled {
                change(&mut state.counts);
            }
        });
    }

    pub(super) fn reset() {
        CURRENT.with(|current| {
            let mut state = current.borrow_mut();
            state.counts = Counts::default();
            state.enabled = true;
        });
    }

    pub(super) fn snapshot() -> Counts {
        CURRENT.with(|current| current.borrow().counts.clone())
    }

    pub(super) fn stop() -> Counts {
        CURRENT.with(|current| {
            let mut state = current.borrow_mut();
            state.enabled = false;
            state.counts.clone()
        })
    }
}

/// Clear this thread's counters and start the next measured operation scope.
#[inline]
pub fn reset() {
    #[cfg(feature = "op-counts")]
    counter::reset();
}

#[inline]
pub fn snapshot() -> Counts {
    #[cfg(feature = "op-counts")]
    {
        counter::snapshot()
    }
    #[cfg(not(feature = "op-counts"))]
    {
        Counts::default()
    }
}

/// End this thread's operation scope and return its counts.
#[inline]
pub fn stop() -> Counts {
    #[cfg(feature = "op-counts")]
    {
        counter::stop()
    }
    #[cfg(not(feature = "op-counts"))]
    {
        Counts::default()
    }
}

#[cfg(feature = "op-counts")]
fn bare_type_name<T>() -> &'static str {
    let mut name = std::any::type_name::<T>();
    while let Some(rest) = name.strip_prefix('&') {
        name = rest.strip_prefix("mut ").unwrap_or(rest);
    }
    name
}

#[cfg(feature = "op-counts")]
fn record_exponentiation<L, R>() {
    if bare_type_name::<R>() != "blstrs::scalar::Scalar" {
        return;
    }
    match bare_type_name::<L>() {
        "blstrs::g1::G1Projective" | "blstrs::g1::G1Affine" => {
            counter::update(|counts| counts.g1_exponentiations += 1)
        }
        "blstrs::g2::G2Projective" | "blstrs::g2::G2Affine" => {
            counter::update(|counts| counts.g2_exponentiations += 1)
        }
        "blstrs::gt::Gt" => counter::update(|counts| counts.gt_exponentiations += 1),
        _ => {}
    }
}

#[inline(always)]
pub fn mul<L: Mul<R>, R>(left: L, right: R) -> L::Output {
    let result = left * right;
    #[cfg(feature = "op-counts")]
    record_exponentiation::<L, R>();
    result
}

#[inline(always)]
pub fn mul_assign<L: MulAssign<R>, R>(left: &mut L, right: R) {
    *left *= right;
    #[cfg(feature = "op-counts")]
    record_exponentiation::<L, R>();
}

#[inline(always)]
pub fn msm1(points: &[G1], scalars: &[Scalar]) -> G1 {
    let _span = crate::darlt::instrumentation::span("group_msm_g1");
    assert_eq!(points.len(), scalars.len(), "MSM dimension mismatch");
    if points.is_empty() {
        return G1::identity();
    }
    let result = G1::multi_exp(points, scalars);
    #[cfg(feature = "op-counts")]
    counter::update(|counts| counts.msm_g1_sizes.push(points.len()));
    result
}

#[inline(always)]
pub fn msm2(points: &[G2], scalars: &[Scalar]) -> G2 {
    let _span = crate::darlt::instrumentation::span("group_msm_g2");
    assert_eq!(points.len(), scalars.len(), "MSM dimension mismatch");
    if points.is_empty() {
        return G2::identity();
    }
    let result = G2::multi_exp(points, scalars);
    #[cfg(feature = "op-counts")]
    counter::update(|counts| counts.msm_g2_sizes.push(points.len()));
    result
}

#[inline(always)]
pub fn pairing(left: &G1Affine, right: &G2Affine) -> Gt {
    let _span = crate::darlt::instrumentation::span("pairing_full");
    let result = blstrs::pairing(left, right);
    #[cfg(feature = "op-counts")]
    counter::update(|counts| {
        counts.pairing_input_terms += 1;
        counts.pairing_calls += 1;
        counts.miller_loop_terms += 1;
        counts.miller_loop_calls += 1;
        counts.final_exponentiations += 1;
    });
    result
}

/// `input_terms` is the original equation's term count, before equal-base
/// merging; `terms.len()` is the actual list submitted to the backend.
#[inline(always)]
pub fn multi_miller_loop(
    terms: &[(&G1Affine, &G2Prepared)],
    input_terms: usize,
) -> MillerLoopResult {
    let _span = crate::darlt::instrumentation::span("miller_loop");
    let result = Bls12::multi_miller_loop(terms);
    #[cfg(feature = "op-counts")]
    counter::update(|counts| {
        counts.pairing_input_terms += input_terms as u64;
        counts.miller_loop_terms += terms.len() as u64;
        counts.miller_loop_calls += 1;
    });
    #[cfg(not(feature = "op-counts"))]
    let _ = input_terms;
    result
}

#[inline(always)]
pub fn final_exponentiation(value: &MillerLoopResult) -> Gt {
    let _span = crate::darlt::instrumentation::span("final_exponentiation");
    let result = value.final_exponentiation();
    #[cfg(feature = "op-counts")]
    counter::update(|counts| counts.final_exponentiations += 1);
    result
}

#[cfg(all(test, feature = "op-counts"))]
mod tests {
    use super::*;
    use ff::Field;
    use group::{Curve, Group};

    #[instrument_ops::count_ops]
    fn scalar_only(value: Scalar, integer: usize) -> (Scalar, usize) {
        let mut field = value * value;
        field *= value;
        (field, integer * 7)
    }

    #[instrument_ops::count_ops]
    #[allow(clippy::op_ref)]
    fn group_operations(g: G1, h: G2, target: Gt, scalar: Scalar) -> (G1, G2, Gt) {
        let mut left = g * scalar;
        left *= scalar;
        let borrowed = &g * &scalar;
        (left + borrowed, h * scalar, target * scalar)
    }

    #[instrument_ops::count_ops]
    fn vector_operations(g: G1, scalar: Scalar) -> Vec<G1> {
        vec![g * scalar, g * scalar]
    }

    #[instrument_ops::count_ops]
    fn nested_and_repeated_vector_operations(g: G1, scalar: Scalar) -> Vec<Vec<G1>> {
        vec![std::vec![g * scalar; 4], vec![g * scalar]]
    }

    #[test]
    fn field_and_integer_products_do_not_count_as_exponentiations() {
        reset();
        let result = scalar_only(Scalar::from(2), 3);
        assert_eq!(result, (Scalar::from(8), 21));
        assert_eq!(stop(), Counts::default());
    }

    #[test]
    fn actual_group_types_and_borrowed_operands_are_counted() {
        let g = G1::generator();
        let h = G2::generator();
        let target = Gt::generator();
        reset();
        let (left, right, result) = group_operations(g, h, target, Scalar::from(2));
        let counts = stop();
        assert_eq!(counts.g1_exponentiations, 3);
        assert_eq!(counts.g2_exponentiations, 1);
        assert_eq!(counts.gt_exponentiations, 1);
        assert_eq!(left, g * Scalar::from(6));
        assert_eq!(right, h * Scalar::from(2));
        assert_eq!(result, target * Scalar::from(2));
        reset();
        assert_eq!(vector_operations(g, Scalar::ONE).len(), 2);
        assert_eq!(stop().g1_exponentiations, 2);
        reset();
        let nested = nested_and_repeated_vector_operations(g, Scalar::ONE);
        assert_eq!(nested[0].len(), 4);
        assert_eq!(nested[1].len(), 1);
        // Repetition evaluates its value once and clones it, so this is two
        // real scalar-multiplication calls, rather than five.
        assert_eq!(stop().g1_exponentiations, 2);
    }

    #[test]
    fn msm_and_pairing_hooks_keep_native_call_boundaries() {
        let g = G1::generator();
        let h = G2::generator();
        let ga = g.to_affine();
        let ha = h.to_affine();
        let hp = G2Prepared::from(ha);
        reset();
        let left = msm1(&[g; 3], &[Scalar::ONE; 3]);
        let right = msm2(&[h; 2], &[Scalar::ONE; 2]);
        let single = pairing(&ga, &ha);
        let loop_result = multi_miller_loop(&[(&ga, &hp)], 7);
        let multi = final_exponentiation(&loop_result);
        let counts = stop();
        assert_eq!(left, g * Scalar::from(3));
        assert_eq!(right, h * Scalar::from(2));
        assert_eq!(single, multi);
        assert_eq!(counts.g1_exponentiations, 0);
        assert_eq!(counts.g2_exponentiations, 0);
        assert_eq!(counts.gt_exponentiations, 0);
        assert_eq!(counts.msm_g1_sizes, vec![3]);
        assert_eq!(counts.msm_g2_sizes, vec![2]);
        assert_eq!(counts.pairing_input_terms, 8);
        assert_eq!(counts.miller_loop_terms, 2);
        assert_eq!(counts.miller_loop_calls, 2);
        assert_eq!(counts.pairing_calls, 1);
        assert_eq!(counts.final_exponentiations, 2);
        let _ = msm1(&[g], &[Scalar::ONE]);
        assert_eq!(snapshot(), counts);
        assert!(serde_json::to_value(counts).unwrap().is_object());
    }

    #[test]
    fn counters_are_local_to_the_running_thread() {
        reset();
        let _ = mul(G1::generator(), Scalar::ONE);
        let child = std::thread::spawn(|| {
            reset();
            let _ = mul(G2::generator(), Scalar::ONE);
            stop()
        })
        .join()
        .unwrap();
        assert_eq!(child.g2_exponentiations, 1);
        assert_eq!(child.g1_exponentiations, 0);
        assert_eq!(stop().g1_exponentiations, 1);
    }
}
