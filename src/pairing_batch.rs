//! Native pairing-product equations checked one at a time.
use blstrs::{G1Affine, G1Projective as G1, G2Affine, G2Prepared, G2Projective as G2, Gt};
use group::Group;
use std::collections::{BTreeMap, BTreeSet};

pub type Equation = Vec<(G1, G2)>;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchResult {
    pub accepted: bool,
    pub equations: usize,
    pub input_terms: usize,
    pub executed_miller_terms: usize,
    pub final_exponentiations: usize,
}
/// Check each native pairing-product equation independently. Equal second
/// arguments may be combined within one equation, an exact bilinear rewrite.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verify_each(equations: &[Equation]) -> Result<BatchResult, String> {
    verify_each_core(equations, None)
}
pub(crate) fn verify_each_received(
    equations: &[Equation],
    checked: &crate::darlt::spend::ReceivedInputs,
) -> Result<BatchResult, String> {
    verify_each_core(equations, Some(checked))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn verify_each_core(
    equations: &[Equation],
    received: Option<&crate::darlt::spend::ReceivedInputs>,
) -> Result<BatchResult, String> {
    if equations.is_empty() || equations.iter().any(Vec::is_empty) {
        return Err("empty pairing equation".into());
    }
    let mut seen_g1 = BTreeSet::new();
    let mut seen_g2 = BTreeSet::new();
    let mut result = BatchResult {
        accepted: true,
        equations: 0,
        input_terms: 0,
        executed_miller_terms: 0,
        final_exponentiations: 0,
    };
    for terms in equations {
        let mut combined: BTreeMap<[u8; 96], (G1, G2)> = BTreeMap::new();
        for &(g, h) in terms {
            let a = g.to_compressed();
            let b = h.to_compressed();
            if received.is_none() {
                let point_g1 = G1Affine::from(g);
                if !bool::from(point_g1.is_on_curve()) {
                    return Err("invalid equation G1".into());
                }
                if seen_g1.insert(a) {
                    crate::subgroup_audit::g1(&g, "darlt/pairing_batch/G1");
                    if !bool::from(point_g1.is_torsion_free()) {
                        return Err("invalid equation G1".into());
                    }
                }
                let point_g2 = G2Affine::from(h);
                if !bool::from(point_g2.is_on_curve()) {
                    return Err("invalid equation G2".into());
                }
                if seen_g2.insert(b) {
                    crate::subgroup_audit::g2(&h, "darlt/pairing_batch/G2");
                    if !bool::from(point_g2.is_torsion_free()) {
                        return Err("invalid equation G2".into());
                    }
                }
            }
            combined.entry(b).or_insert((G1::identity(), h)).0 += g;
        }
        let pairs: Vec<_> = combined
            .into_values()
            .filter(|(g, h)| *g != G1::identity() && *h != G2::identity())
            .collect();
        let first: Vec<_> = pairs.iter().map(|(g, _)| G1Affine::from(*g)).collect();
        let second: Vec<_> = pairs
            .iter()
            .map(|(_, h)| G2Prepared::from(G2Affine::from(*h)))
            .collect();
        let refs: Vec<_> = first.iter().zip(&second).collect();
        let accepted =
            crate::ops::final_exponentiation(&crate::ops::multi_miller_loop(&refs, terms.len()))
                == Gt::identity();
        result.equations += 1;
        result.input_terms += terms.len();
        result.executed_miller_terms += pairs.len();
        result.final_exponentiations += 1;
        if !accepted {
            result.accepted = false;
            return Ok(result);
        }
    }
    Ok(result)
}
#[cfg(test)]
mod tests {
    use super::*;
    use blstrs::Scalar as S;
    #[test]
    fn distinct_valid_equations_each_get_their_own_final_exponentiation() {
        let g = G1::generator();
        let h = G2::generator();
        let a = S::from(17);
        let b = S::from(29);
        let equations = vec![vec![(g * a, h), (-g, h * a)], vec![(g * b, h), (-g, h * b)]];
        let result = verify_each(&equations).unwrap();
        assert!(result.accepted);
        assert_eq!(result.final_exponentiations, 2);
        assert_eq!(result.input_terms, 4);
        assert_eq!(result.executed_miller_terms, 4);
    }
    #[test]
    fn opposite_invalid_equations_cannot_cancel_each_other() {
        let g = G1::generator();
        let h = G2::generator();
        let equations = vec![vec![(g, h)], vec![(-g, h)]];
        assert!(!verify_each(&equations).unwrap().accepted);
        let changed = vec![vec![(g * S::from(2), h)], vec![(-g, h)]];
        assert!(!verify_each(&changed).unwrap().accepted);
        assert!(verify_each(&[]).is_err());
    }
    #[test]
    fn compressed_key_does_not_cache_curve_validity() {
        let g = G1::generator();
        let h = G2::generator();
        let one = g.z();
        let bad = (1..32)
            .find_map(|i| {
                let mut y = g.y();
                for _ in 0..i {
                    y += one;
                }
                let candidate = G1::from_raw_unchecked(g.x(), y, g.z());
                (!bool::from(G1Affine::from(candidate).is_on_curve())
                    && candidate.to_compressed() == g.to_compressed())
                .then_some(candidate)
            })
            .expect("off-curve point sharing the valid compressed cache key");
        let equations = vec![vec![(g, h), (-g, h)], vec![(bad, h), (-bad, h)]];
        assert!(verify_each(&equations).is_err());
    }
}
