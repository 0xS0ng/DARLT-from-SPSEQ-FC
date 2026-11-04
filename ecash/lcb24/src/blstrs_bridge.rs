//! Offline conversion of the native circuit's objects to the common backend.
//! Coordinate conversion is explicit: Arkworks0.3 compressed bytes are not
//! treated as IETF encodings. Payment conversion checks both sides; key
//! installation sends canonical coordinates to one strict checked decoder.
use crate::{Bank, Payment, Result, Wallet};
use ark_bls12_381::{Fq, Fr, G1Affine, G2Affine};
use ark_ff::{BigInteger, PrimeField, Zero};
use darlt_spseq_fc::lcb24 as common;

fn fq_bytes(value: Fq) -> [u8; 48] {
    value
        .into_repr()
        .to_bytes_be()
        .try_into()
        .expect("BLS Fq is48bytes")
}
pub fn g1(value: G1Affine) -> Result<blstrs::G1Projective> {
    if !value.is_on_curve() || !value.is_in_correct_subgroup_assuming_on_curve() {
        return Err("Arkworks G1 point/subgroup rejected before bridge".into());
    }
    let mut bytes = [0; 96];
    if value.is_zero() {
        bytes[0] = 0x40;
    } else {
        bytes[..48].copy_from_slice(&fq_bytes(value.x));
        bytes[48..].copy_from_slice(&fq_bytes(value.y));
    }
    Option::from(blstrs::G1Projective::from_uncompressed(&bytes))
        .ok_or("blstrs G1 conversion rejected".into())
}
pub fn g2(value: G2Affine) -> Result<blstrs::G2Projective> {
    if !value.is_on_curve() || !value.is_in_correct_subgroup_assuming_on_curve() {
        return Err("Arkworks G2 point/subgroup rejected before bridge".into());
    }
    let mut bytes = [0; 192];
    if value.is_zero() {
        bytes[0] = 0x40;
    } else {
        for (chunk, v) in bytes
            .chunks_exact_mut(48)
            .zip([value.x.c1, value.x.c0, value.y.c1, value.y.c0])
        {
            chunk.copy_from_slice(&fq_bytes(v));
        }
    }
    Option::from(blstrs::G2Projective::from_uncompressed(&bytes))
        .ok_or("blstrs G2 conversion rejected".into())
}
pub fn scalar(value: Fr) -> Result<blstrs::Scalar> {
    let bytes: [u8; 32] = value
        .into_repr()
        .to_bytes_le()
        .try_into()
        .expect("BLS Fr is32bytes");
    Option::from(blstrs::Scalar::from_bytes_le(&bytes))
        .ok_or("blstrs Fr conversion rejected".into())
}
// These key-only serializers perform no group validation or point construction.
// The receiving immutable Key checks the actual complete coordinates once.
fn key_g1_bytes(value: G1Affine) -> [u8; 96] {
    let mut bytes = [0; 96];
    if value.is_zero() {
        bytes[0] = 0x40;
    } else {
        bytes[..48].copy_from_slice(&fq_bytes(value.x));
        bytes[48..].copy_from_slice(&fq_bytes(value.y));
    }
    bytes
}
fn key_g2_bytes(value: G2Affine) -> [u8; 192] {
    let mut bytes = [0; 192];
    if value.is_zero() {
        bytes[0] = 0x40;
    } else {
        for (chunk, v) in bytes
            .chunks_exact_mut(48)
            .zip([value.x.c1, value.x.c0, value.y.c1, value.y.c0])
        {
            chunk.copy_from_slice(&fq_bytes(v));
        }
    }
    bytes
}
pub fn key<const H: usize>(bank: &Bank<H>) -> Result<common::Key> {
    let k = &bank.verifying_key;
    if k.gamma_abc_g1.len() != 2 {
        return Err("native LCB circuit must have one public input".into());
    }
    common::Key::install_uncompressed(
        &key_g1_bytes(k.alpha_g1),
        &key_g2_bytes(k.beta_g2),
        &key_g2_bytes(k.gamma_g2),
        &key_g2_bytes(k.delta_g2),
        &[
            key_g1_bytes(k.gamma_abc_g1[0]),
            key_g1_bytes(k.gamma_abc_g1[1]),
        ],
    )
}
pub fn payment<const H: usize>(p: &Payment) -> Result<common::Payment> {
    let blocks = p
        .blocks
        .iter()
        .map(|b| {
            Ok(common::Block {
                denom: b.denom,
                seed: b.seed,
                instance: scalar(b.instance)?,
                proof: common::Proof {
                    a: g1(b.proof.a)?,
                    b: g2(b.proof.b)?,
                    c: g1(b.proof.c)?,
                },
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let out = common::Payment {
        amount: p.amount,
        blocks,
    };
    out.validate_shape::<H>()?;
    Ok(out)
}
/// Independent branches share the same proof inventory but
/// each starts with the original wallet's used bitmap. Immutable trees and
/// prepared-proof tables share RAM; sample-specific counters are independent.
pub fn fixture_branch<const H: usize>(_bank: &Bank<H>, w: &Wallet<H>) -> Result<Wallet<H>> {
    Ok(Wallet {
        master: w.master,
        leaves: w.leaves.clone(),
        tree: w.tree.clone(),
        root: w.root,
        commitment: w.commitment,
        opening: w.opening,
        signature: w.signature.clone(),
        proofs: w.proofs.clone(),
        used: w.used.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineCurve, ProjectiveCurve};
    use ark_ff::UniformRand;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use darlt_spseq_fc::{
        batch_runtime::{self, Adapter, Mode},
        common::spent::SpentStore,
        lcb24::{RandomProfile, Verifier},
    };
    use group::Group;
    struct NoCoins;
    impl ark_std::rand::RngCore for NoCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("single-equation exact check needs no coins")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("single-equation exact check needs no coins")
        }
        fn fill_bytes(&mut self, _: &mut [u8]) {
            panic!("single-equation exact check needs no coins")
        }
        fn try_fill_bytes(
            &mut self,
            _: &mut [u8],
        ) -> std::result::Result<(), ark_std::rand::Error> {
            panic!("single-equation exact check needs no coins")
        }
    }
    impl ark_std::rand::CryptoRng for NoCoins {}
    #[test]
    fn key_coordinate_transport_matches_original_checked_point_bridge() {
        let bank = Bank::<2>::setup(&mut StdRng::seed_from_u64(32035)).unwrap();
        let k = &bank.verifying_key;
        let reference = common::Key::install(
            g1(k.alpha_g1).unwrap(),
            g2(k.beta_g2).unwrap(),
            g2(k.gamma_g2).unwrap(),
            g2(k.delta_g2).unwrap(),
            [
                g1(k.gamma_abc_g1[0]).unwrap(),
                g1(k.gamma_abc_g1[1]).unwrap(),
            ],
        )
        .unwrap();
        assert_eq!(key(&bank).unwrap().bytes(), reference.bytes());
    }
    #[test]
    fn checked_coordinate_conversion_preserves_generators_scalars_and_all_leaf_bits() {
        assert_eq!(
            g1(G1Affine::prime_subgroup_generator()).unwrap(),
            blstrs::G1Projective::generator()
        );
        assert_eq!(
            g2(G2Affine::prime_subgroup_generator()).unwrap(),
            blstrs::G2Projective::generator()
        );
        assert!(bool::from(g1(G1Affine::zero()).unwrap().is_identity()));
        assert!(bool::from(g2(G2Affine::zero()).unwrap().is_identity()));
        let mut rng = StdRng::seed_from_u64(214_240_001);
        for _ in 0..32 {
            let a = Fr::rand(&mut rng);
            assert_eq!(
                g1(G1Affine::prime_subgroup_generator()
                    .mul(a.into_repr())
                    .into_affine())
                .unwrap(),
                blstrs::G1Projective::generator() * scalar(a).unwrap()
            );
            assert_eq!(
                g2(G2Affine::prime_subgroup_generator()
                    .mul(a.into_repr())
                    .into_affine())
                .unwrap(),
                blstrs::G2Projective::generator() * scalar(a).unwrap()
            );
            let mut bytes = [0; 32];
            ark_std::rand::RngCore::fill_bytes(&mut rng, &mut bytes);
            assert_eq!(
                common::leaf_scalar(&bytes),
                scalar(Fr::from_le_bytes_mod_order(&bytes)).unwrap()
            );
        }
    }
    #[test]
    fn real_native_proofs_match_common_backend_and_shared_atomic_state() {
        let mut rng = StdRng::seed_from_u64(214_240_002);
        let bank = Bank::<3>::setup(&mut rng).unwrap();
        let mut original = bank.issue_wallet(&mut rng).unwrap();
        bank.precompute_all(&mut original, &mut rng).unwrap();
        let k = key(&bank).unwrap();
        for amount in 1..=8 {
            let mut w = fixture_branch(&bank, &original).unwrap();
            let p = bank.spend_prepared(&mut w, amount).unwrap();
            let native = bank.expand_after_verification(&p).unwrap();
            let converted = payment::<3>(&p).unwrap();
            let wire = converted.encode();
            let converted = common::Payment::decode::<3>(&wire).unwrap();
            assert_eq!(native.serials, converted.redeem_serials::<3>().unwrap());
            assert_eq!(p.encode().len(), wire.len());
            if converted.blocks.len() == 1 {
                darlt_spseq_fc::ops::reset();
                k.verify::<3>(
                    std::slice::from_ref(&converted),
                    Mode::Randomized,
                    RandomProfile::PairingAnchor,
                    &mut NoCoins,
                )
                .unwrap();
                let c = darlt_spseq_fc::ops::stop();
                if cfg!(feature = "op-counts") {
                    assert_eq!(c.miller_loop_terms, 3);
                    assert_eq!(c.final_exponentiations, 1);
                    assert_eq!(c.gt_exponentiations, 0);
                    assert_eq!(c.g1_exponentiations, 0);
                    assert_eq!(c.msm_g1_sizes, vec![2]);
                }
            }
            for profile in [RandomProfile::CachedGtAnchor, RandomProfile::PairingAnchor] {
                for mode in [Mode::Specification, Mode::Randomized] {
                    let verifier = Verifier::<3>::new(&k, profile);
                    let state = SpentStore::new();
                    let a = batch_runtime::verify_and_record(
                        &verifier,
                        std::slice::from_ref(&converted.clone().checked::<3>().unwrap()),
                        b"native-cross-backend",
                        b"accepted",
                        &state,
                        mode,
                        &mut rng,
                    )
                    .unwrap();
                    assert_eq!(a.newly_registered, amount);
                    let mut bad = converted.clone();
                    bad.blocks[0].proof.a += blstrs::G1Projective::generator();
                    assert!(!verifier.verify(&[bad.checked::<3>().unwrap()], mode, &mut rng));
                    let mut bad = converted.clone();
                    bad.blocks[0].seed[0] ^= 1;
                    assert!(!verifier.verify(&[bad.checked::<3>().unwrap()], mode, &mut rng));
                }
            }
        }
    }
}
