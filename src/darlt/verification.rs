//! Fixed-step pairing batches; verifier coins are never Fiat--Shamir.
use crate::{
    common::crypto::{valid1, valid2},
    pairing_batch::{self, BatchResult, Equation},
    polynomial::S,
};
use blstrs::{G1Affine, G1Projective as G1, G2Affine, G2Prepared, G2Projective as G2, Gt};
use group::Group;
use rand::RngCore;
use std::collections::BTreeMap;
type EquationCombiner<'a> = &'a dyn Fn(&[S]) -> Equation;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Specification,
    Randomized,
}

/// Validate all fixed equations before sampling independent uniform nonzero
/// 128-bit integer weights. This API borrows immutable input; no weights are
/// returned to callers. Specification mode is a correctness reference only.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn check(
    equations: &[Equation],
    mode: Mode,
    rng: &mut impl RngCore,
) -> Result<BatchResult, String> {
    check_core(equations, mode, rng, None, None)
}
pub(super) fn check_received(
    equations: &[Equation],
    mode: Mode,
    rng: &mut impl RngCore,
    received: &super::spend::ReceivedInputs,
) -> Result<BatchResult, String> {
    check_core(equations, mode, rng, Some(received), None)
}
/// Retain a native fixed-base bilinear rewrite after the complete equation
/// list has been fixed and checked and one independent weight drawn per PPE.
/// This is internal: the combiner may only rewrite that checked conjunction.
pub(super) fn check_with_combiner(
    equations: &[Equation],
    mode: Mode,
    rng: &mut impl RngCore,
    combine: impl Fn(&[S]) -> Equation,
) -> Result<BatchResult, String> {
    check_core(equations, mode, rng, None, Some(&combine))
}
pub(super) fn check_with_combiner_received(
    equations: &[Equation],
    mode: Mode,
    rng: &mut impl RngCore,
    received: &super::spend::ReceivedInputs,
    combine: impl Fn(&[S]) -> Equation,
) -> Result<BatchResult, String> {
    check_core(equations, mode, rng, Some(received), Some(&combine))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn check_core(
    equations: &[Equation],
    mode: Mode,
    rng: &mut impl RngCore,
    received: Option<&super::spend::ReceivedInputs>,
    combine: Option<EquationCombiner<'_>>,
) -> Result<BatchResult, String> {
    if equations.is_empty() || equations.iter().any(Vec::is_empty) {
        return Err("empty equations".into());
    }
    if received.is_none() {
        for e in equations {
            for (a, b) in e {
                if !valid1(*a, false) || !valid2(*b, false) {
                    return Err("invalid pairing input".into());
                }
            }
        }
    }
    if mode == Mode::Specification {
        return match received {
            Some(checked) => pairing_batch::verify_each_received(equations, checked),
            None => pairing_batch::verify_each(equations),
        };
    }
    let input_terms = equations.iter().map(Vec::len).sum();
    let weights: Vec<S> = (0..equations.len())
        .map(|_| baseline_core::curve::random_batch_weight128(rng))
        .collect();
    let combined = combine.map_or_else(
        || combine_equations(equations, &weights),
        |combine| combine(&weights),
    );
    let combined: Equation = combined
        .into_iter()
        .filter(|(g, h)| *g != G1::identity() && *h != G2::identity())
        .collect();
    let first: Vec<_> = combined.iter().map(|(g, _)| G1Affine::from(*g)).collect();
    let second: Vec<_> = combined
        .iter()
        .map(|(_, h)| G2Prepared::from(G2Affine::from(*h)))
        .collect();
    let refs: Vec<_> = first.iter().zip(&second).collect();
    let accepted =
        crate::ops::final_exponentiation(&crate::ops::multi_miller_loop(&refs, input_terms))
            == Gt::identity();
    Ok(BatchResult {
        accepted,
        equations: equations.len(),
        input_terms,
        executed_miller_terms: combined.len(),
        final_exponentiations: 1,
    })
}
pub(super) fn combine_equations(equations: &[Equation], weights: &[S]) -> Equation {
    assert_eq!(equations.len(), weights.len());
    let mut merged: BTreeMap<[u8; 96], (Vec<G1>, Vec<S>, G2)> = BTreeMap::new();
    for (e, w) in equations.iter().zip(weights.iter().copied()) {
        for (g, h) in e {
            let entry = merged
                .entry(h.to_compressed())
                .or_insert((vec![], vec![], *h));
            entry.0.push(*g);
            entry.1.push(w);
        }
    }
    merged
        .into_values()
        .map(|(g, s, h)| (crate::ops::msm1(&g, &s), h))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn random_weights_prevent_opposite_residual_cancellation() {
        let mut rng = StdRng::seed_from_u64(20201);
        let g = G1::generator();
        let h = G2::generator();
        let bad = vec![vec![(g, h)], vec![(-g, h)]];
        for _ in 0..8 {
            assert!(!check(&bad, Mode::Randomized, &mut rng).unwrap().accepted);
        }
        let valid = vec![
            vec![(g, h), (-g, h)],
            vec![(g * S::from(7), h), (-g, h * S::from(7))],
        ];
        assert!(
            check(&valid, Mode::Specification, &mut rng)
                .unwrap()
                .accepted
        );
        let v = check(&valid, Mode::Randomized, &mut rng).unwrap();
        assert!(v.accepted);
        assert_eq!(v.final_exponentiations, 1);
    }
}
