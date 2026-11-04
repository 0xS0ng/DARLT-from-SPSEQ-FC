//! Independent 128-bit nonzero verifier weights for fixed FHS signature inputs.
//! Protocol-specific proofs and policy checks are performed by each caller.
use crate::arithmetic::*;
#[cfg(test)]
use ff::Field;
use group::Group;
use rand::RngCore;

#[derive(Clone)]
pub(crate) struct FhsStatement {
    pub message: Vec<G1>,
    pub z: G1,
    pub y: G1,
    pub yh: G2,
}

/// Fix and validate the complete batch before consuming any verifier coins.
/// Two independent nonzero 128-bit weights per signature combine the two
/// native FHS equations into k+ell+1 Miller inputs and one final exponentiation.
pub(crate) fn fhs_random(key: &[G2], statements: &[FhsStatement], rng: &mut impl RngCore) -> bool {
    fhs_random_inner(key, statements, None, false, rng)
}
/// The first coordinate is a fixed generator and its installed anchor pairing
/// can be substituted exactly. This adds a GT exponent and saves one Miller.
pub(crate) fn fhs_random_with_anchor(
    key: &[G2],
    statements: &[FhsStatement],
    anchor: GT,
    rng: &mut impl RngCore,
) -> bool {
    if statements
        .iter()
        .any(|s| s.message.first() != Some(&G1::generator()))
    {
        return false;
    }
    fhs_random_inner(key, statements, Some(anchor), false, rng)
}
/// A same-metadata combination of checked native keys may be identity even
/// though each original key is nonzero. Only this first derived key permits it.
pub(crate) fn fhs_random_same_metadata(
    key: &[G2; 3],
    statements: &[FhsStatement],
    rng: &mut impl RngCore,
) -> bool {
    fhs_random_inner(key, statements, None, true, rng)
}
fn fhs_random_inner(
    key: &[G2],
    statements: &[FhsStatement],
    anchor: Option<GT>,
    derived_first_key: bool,
    rng: &mut impl RngCore,
) -> bool {
    if key.is_empty()
        || statements.is_empty()
        || key
            .iter()
            .enumerate()
            .any(|(j, &p)| !valid2(p, !derived_first_key || j != 0))
        || statements.iter().any(|s| {
            s.message.len() != key.len()
                || s.message.iter().any(|&p| !valid1(p, false))
                || !valid1(s.z, false)
                || !valid1(s.y, true)
                || !valid2(s.yh, true)
        })
    {
        return false;
    }
    fhs_random_body(key, statements, anchor, rng)
}
/// Only protocol continuations with sealed decoded tokens and installed keys
/// call these crate-private entries. Derived coordinates remain in the group.
pub(crate) fn fhs_random_checked(
    key: &[G2],
    statements: &[FhsStatement],
    rng: &mut impl RngCore,
) -> bool {
    fhs_random_checked_inner(key, statements, None, false, rng)
}
pub(crate) fn fhs_random_with_anchor_checked(
    key: &[G2],
    statements: &[FhsStatement],
    anchor: GT,
    rng: &mut impl RngCore,
) -> bool {
    if statements
        .iter()
        .any(|s| s.message.first() != Some(&G1::generator()))
    {
        return false;
    }
    fhs_random_checked_inner(key, statements, Some(anchor), false, rng)
}
pub(crate) fn fhs_random_same_metadata_checked(
    key: &[G2; 3],
    statements: &[FhsStatement],
    rng: &mut impl RngCore,
) -> bool {
    fhs_random_checked_inner(key, statements, None, true, rng)
}
fn fhs_random_checked_inner(
    key: &[G2],
    statements: &[FhsStatement],
    anchor: Option<GT>,
    derived_first_key: bool,
    rng: &mut impl RngCore,
) -> bool {
    if key.is_empty()
        || statements.is_empty()
        || key
            .iter()
            .enumerate()
            .any(|(j, p)| (!derived_first_key || j != 0) && *p == G2::identity())
        || statements.iter().any(|s| {
            s.message.len() != key.len() || s.y == G1::identity() || s.yh == G2::identity()
        })
    {
        return false;
    }
    fhs_random_body(key, statements, anchor, rng)
}
fn fhs_random_body(
    key: &[G2],
    statements: &[FhsStatement],
    anchor: Option<GT>,
    rng: &mut impl RngCore,
) -> bool {
    // Own canonical input bytes before sampling. No callback can change any
    // statement or public key after the validation/sampling boundary.
    let frozen: Vec<_> = statements.to_vec();
    let mut bytes = vec![];
    for p in key {
        bytes.extend(enc2(*p));
    }
    for s in &frozen {
        for p in &s.message {
            bytes.extend(enc1(*p));
        }
        bytes.extend(enc1(s.z));
        bytes.extend(enc1(s.y));
        bytes.extend(enc2(s.yh));
    }
    let weights: Vec<_> = frozen
        .iter()
        .map(|_| (random_batch_weight128(rng), random_batch_weight128(rng)))
        .collect();
    let mut terms: Vec<_> = frozen
        .iter()
        .zip(&weights)
        .map(|(s, (a, b))| (sum1(&[(s.z, *a), (G1::generator(), -*b)]), s.yh))
        .collect();
    terms.push((
        sum1(
            &frozen
                .iter()
                .zip(&weights)
                .map(|(s, (_, b))| (s.y, *b))
                .collect::<Vec<_>>(),
        ),
        G2::generator(),
    ));
    for (j, &x) in key.iter().enumerate().skip(usize::from(anchor.is_some())) {
        terms.push((
            -sum1(
                &frozen
                    .iter()
                    .zip(&weights)
                    .map(|(s, (a, _))| (s.message[j], *a))
                    .collect::<Vec<_>>(),
            ),
            x,
        ));
    }
    let target = anchor.map_or_else(GT::identity, |a| {
        gt_mul(a, weights.iter().map(|(w, _)| *w).sum())
    });
    multi_pair(&terms) == target
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn randomized_fhs_preserves_two_equations_and_rejects_cancelling_bad_pairs() {
        let mut rng = StdRng::seed_from_u64(20710);
        let sk = [S::from(7), S::from(11), S::from(13)];
        let pk = sk.map(|s| G2::generator() * s);
        let make = |r: S| {
            let m = vec![
                G1::generator(),
                G1::generator() * r,
                G1::generator() * (r + S::ONE),
            ];
            FhsStatement {
                z: (m[0] * sk[0] + m[1] * sk[1] + m[2] * sk[2]) * r,
                y: G1::generator() * inv(r),
                yh: G2::generator() * inv(r),
                message: m,
            }
        };
        let s = vec![make(S::from(3)), make(S::from(5))];
        assert!(fhs_random(&pk, &s, &mut rng));
        let mut bad = s.clone();
        bad[0].z += G1::generator();
        assert!(!fhs_random(&pk, &bad, &mut rng));
        let mut bad = s.clone();
        bad[0].y += G1::generator();
        bad[1].y -= G1::generator();
        assert!(!fhs_random(&pk, &bad, &mut rng));
        let mut bad = s.clone();
        bad[1].y = G1::identity();
        assert!(!fhs_random(&pk, &bad, &mut rng));
        assert!(!fhs_random(&pk, &[], &mut rng));
    }
}
