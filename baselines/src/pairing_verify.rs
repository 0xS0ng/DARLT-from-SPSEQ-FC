//! Exact and verifier-random checks of pairing equations with GT targets.
use crate::arithmetic::*;
use group::Group;
use rand::RngCore;
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub struct Equation {
    pub terms: Vec<(G1, G2)>,
    pub target: GT,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode {
    Specification,
    Randomized,
}

fn valid_gt(value: GT) -> bool {
    if value == GT::default() {
        return false;
    }
    if value == GT::identity() {
        return true;
    }
    // Test the integer group order, not an Fr scalar (which would be zero).
    // Do this before torus compression: malformed Fp12 values can make the
    // upstream compression routine invert zero and panic.
    const ORDER: [u8; 32] = [
        0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8,
        0x05, 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00,
        0x00, 0x01,
    ];
    let mut accumulator = GT::identity();
    for byte in ORDER {
        for bit in (0..8).rev() {
            accumulator = accumulator + accumulator;
            if byte & (1 << bit) != 0 {
                accumulator += value;
            }
        }
    }
    let accepted = accumulator == GT::identity();
    if accepted {
        crate::subgroup_audit::gt(&value, "pairing_verify::valid_gt");
    } else {
        crate::subgroup_audit::unencoded("GT", "pairing_verify::valid_gt:nonmember-uncompressible");
    }
    accepted
}
/// Validate every dynamic point and target before requesting verifier coins.
pub fn valid_equations(equations: &[Equation]) -> bool {
    !equations.is_empty()
        && equations.iter().all(|eq| {
            eq.terms
                .iter()
                .all(|(g, h)| valid1(*g, false) && valid2(*h, false))
                && valid_gt(eq.target)
        })
}

/// All equations and targets are fixed and validated before consuming coins.
/// Native interactive callers invoke this only at their original check stage.
pub fn verify(equations: &[Equation], mode: Mode, rng: &mut impl RngCore) -> bool {
    if !valid_equations(equations) {
        return false;
    }
    verify_body(equations, mode, rng)
}
/// Protocol-private continuation for equations derived entirely from installed
/// parameters and sealed received inputs. Public arbitrary equations still use
/// `verify`, including its complete domain/membership checks.
pub(crate) fn verify_checked(equations: &[Equation], mode: Mode, rng: &mut impl RngCore) -> bool {
    !equations.is_empty() && verify_body(equations, mode, rng)
}
fn verify_body(equations: &[Equation], mode: Mode, rng: &mut impl RngCore) -> bool {
    if mode == Mode::Specification {
        return equations.iter().all(|eq| {
            let value = if eq.terms.is_empty() {
                GT::identity()
            } else {
                multi_pair(&eq.terms)
            };
            value == eq.target
        });
    }
    let weights: Vec<_> = equations
        .iter()
        .map(|_| random_batch_weight128(rng))
        .collect();
    type WeightedTerms = (G2, Vec<(G1, S)>);
    let mut grouped: BTreeMap<Vec<u8>, WeightedTerms> = BTreeMap::new();
    let mut target = GT::identity();
    for (eq, weight) in equations.iter().zip(weights) {
        if eq.target != GT::identity() {
            target = gt_add(target, gt_mul(eq.target, weight));
        }
        for &(g, h) in &eq.terms {
            grouped
                .entry(enc2(h))
                .or_insert_with(|| (h, vec![]))
                .1
                .push((g, weight));
        }
    }
    let terms: Vec<_> = grouped
        .into_values()
        .map(|(h, terms)| (sum1(&terms), h))
        .filter(|(g, h)| *g != G1::identity() && *h != G2::identity())
        .collect();
    let value = if terms.is_empty() {
        GT::identity()
    } else {
        multi_pair(&terms)
    };
    value == target
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    struct NoCoins;
    impl RngCore for NoCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("coins before input validation")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("coins before input validation")
        }
        fn fill_bytes(&mut self, _: &mut [u8]) {
            panic!("coins before input validation")
        }
        fn try_fill_bytes(&mut self, _: &mut [u8]) -> Result<(), rand::Error> {
            panic!("coins before input validation")
        }
    }
    #[test]
    fn arbitrary_targets_and_opposite_invalid_residuals() {
        let mut rng = StdRng::seed_from_u64(21201);
        let g = G1::generator();
        let h = G2::generator();
        let target = pair(g, h);
        let valid = vec![
            Equation {
                terms: vec![(g, h)],
                target,
            },
            Equation {
                terms: vec![(g * S::from(3), h)],
                target: gt_mul(target, S::from(3)),
            },
        ];
        assert!(verify(&valid, Mode::Specification, &mut NoCoins));
        assert!(verify(&valid, Mode::Randomized, &mut rng));
        let bad = vec![
            Equation {
                terms: vec![(g, h)],
                target: GT::identity(),
            },
            Equation {
                terms: vec![(-g, h)],
                target: GT::identity(),
            },
        ];
        for _ in 0..8 {
            assert!(!verify(&bad, Mode::Randomized, &mut rng));
        }
        assert!(!verify(&bad, Mode::Specification, &mut NoCoins));
        assert!(!verify(&[], Mode::Randomized, &mut NoCoins));
        assert!(!verify(
            &[Equation {
                terms: vec![],
                target: GT::default()
            }],
            Mode::Randomized,
            &mut NoCoins
        ));
        assert!(verify(
            &[Equation {
                terms: vec![],
                target: GT::identity()
            }],
            Mode::Randomized,
            &mut rng
        ));
    }
    #[test]
    fn nonzero_fp12_outside_gt_is_rejected_before_compression_or_coins() {
        let mut raw = blst::blst_fp12::default();
        // Test fixture for the public Fp12-to-Gt conversion exposed when the
        // backend's private-bench feature is enabled. Both wrappers have the
        // backend's documented transparent representation.
        let bad: GT = unsafe {
            blst::blst_fp_from_uint64(&mut raw.fp6[0].fp2[0].fp[0], [2u64, 0, 0, 0, 0, 0].as_ptr());
            std::mem::transmute(raw)
        };
        assert_ne!(bad, GT::default());
        assert!(!verify(
            &[Equation {
                terms: vec![],
                target: bad
            }],
            Mode::Randomized,
            &mut NoCoins
        ));
    }
}
