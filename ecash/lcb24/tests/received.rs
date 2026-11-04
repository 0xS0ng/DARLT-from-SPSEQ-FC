//! Real native proofs test strict wire reception; no protocol timer is used.
use ark_std::rand::{rngs::StdRng, CryptoRng, RngCore, SeedableRng};
use darlt_spseq_fc::{
    batch_runtime::Mode,
    lcb24::{decode_received, RandomProfile},
};
use lcb24_native::{blstrs_bridge as bridge, Bank};
struct NoCoins;
impl RngCore for NoCoins {
    fn next_u32(&mut self) -> u32 {
        panic!("bad bytes reached Groth16 batch weights")
    }
    fn next_u64(&mut self) -> u64 {
        panic!("bad bytes reached Groth16 batch weights")
    }
    fn fill_bytes(&mut self, _: &mut [u8]) {
        panic!("bad bytes reached Groth16 batch weights")
    }
    fn try_fill_bytes(&mut self, _: &mut [u8]) -> Result<(), ark_std::rand::Error> {
        panic!("bad bytes reached Groth16 batch weights")
    }
}
impl CryptoRng for NoCoins {}
fn bad_g1() -> [u8; 48] {
    (1u64..256)
        .find_map(|i| {
            let mut b = [0; 48];
            b[0] = 0x80;
            b[40..].copy_from_slice(&i.to_be_bytes());
            let p =
                Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed_unchecked(&b))?;
            (!bool::from(p.is_torsion_free())).then_some(p.to_compressed())
        })
        .unwrap()
}
fn bad_g2() -> [u8; 96] {
    (1u64..256)
        .find_map(|i| {
            let mut b = [0; 96];
            b[0] = 0x80;
            b[88..].copy_from_slice(&i.to_be_bytes());
            let p =
                Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed_unchecked(&b))?;
            (!bool::from(p.is_torsion_free())).then_some(p.to_compressed())
        })
        .unwrap()
}
// Noncanonical field representatives of valid prime-order points: a decoder
// must reject x+p, rather than reducing it to the same affine coordinate.
fn fp_plus_modulus(mut x: [u8; 48]) -> [u8; 48] {
    let h="1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
    let mut carry = 0u16;
    for i in (0..48).rev() {
        let p = u8::from_str_radix(&h[2 * i..2 * i + 2], 16).unwrap();
        let v = u16::from(x[i]) + u16::from(p) + carry;
        x[i] = v as u8;
        carry = v >> 8;
    }
    assert_eq!(carry, 0);
    x
}
fn alias_g1() -> [u8; 48] {
    use group::Group;
    (1u64..256)
        .find_map(|i| {
            let mut p =
                (blstrs::G1Projective::generator() * blstrs::Scalar::from(i)).to_compressed();
            let flags = p[0] & 0xe0;
            p[0] &= 0x1f;
            let mut x = fp_plus_modulus(p);
            if x[0] & 0xe0 != 0 {
                return None;
            }
            x[0] |= flags;
            Some(x)
        })
        .unwrap()
}
fn alias_g2() -> [u8; 96] {
    use group::Group;
    let mut p = blstrs::G2Projective::generator().to_compressed();
    let x = fp_plus_modulus(p[48..].try_into().unwrap());
    p[48..].copy_from_slice(&x);
    p
}
#[test]
fn real_received_groth16_payloads_reject_bad_bytes_before_weights_and_keep_identity_format_rules() {
    let mut rng = StdRng::seed_from_u64(3124);
    let bank = Bank::<2>::setup(&mut rng).unwrap();
    let mut w = bank.issue_wallet(&mut rng).unwrap();
    bank.precompute_amount(&mut w, 3, &mut rng).unwrap();
    let p = bridge::payment::<2>(&bank.spend_prepared(&mut w, 3).unwrap()).unwrap();
    assert_eq!(p.blocks.len(), 2);
    let key = bridge::key(&bank).unwrap();
    let good = p.encode();
    for profile in [RandomProfile::CachedGtAnchor, RandomProfile::PairingAnchor] {
        for mode in [Mode::Specification, Mode::Randomized] {
            key.verify_received::<2>(&[&good], mode, profile, &mut rng)
                .unwrap();
        }
    }
    let mut malformed = vec![good[..good.len() - 1].to_vec()];
    let mut b = good.clone();
    b.push(0);
    malformed.push(b);
    let mut b = good.clone();
    b[0] = 255;
    malformed.push(b);
    let mut b = good.clone();
    b[1..9].fill(0);
    malformed.push(b);
    let mut b = good.clone();
    b[9..17].fill(0);
    malformed.push(b);
    let mut b = good.clone();
    b[17] = 3;
    malformed.push(b);
    let mut b = good.clone();
    b[50..82].fill(255);
    malformed.push(b);
    let mut b = good.clone();
    b[82..130].copy_from_slice(&bad_g1());
    malformed.push(b);
    let mut b = good.clone();
    b[130..226].copy_from_slice(&bad_g2());
    malformed.push(b);
    let mut b = good.clone();
    b[82..130].copy_from_slice(&alias_g1());
    malformed.push(b);
    let mut b = good.clone();
    b[130..226].copy_from_slice(&alias_g2());
    malformed.push(b);
    for wire in malformed {
        assert!(decode_received::<2>(&[&wire]).is_err());
        for profile in [RandomProfile::CachedGtAnchor, RandomProfile::PairingAnchor] {
            assert!(key
                .verify_received::<2>(&[&wire], Mode::Randomized, profile, &mut NoCoins)
                .is_err());
            assert!(key
                .verify_received::<2>(&[&good, &wire], Mode::Randomized, profile, &mut NoCoins)
                .is_err());
        }
    }
    let mut bad_seed = good.clone();
    bad_seed[18] ^= 1;
    assert!(decode_received::<2>(&[&bad_seed]).is_ok());
    assert!(key
        .verify_received::<2>(
            &[&bad_seed],
            Mode::Randomized,
            RandomProfile::CachedGtAnchor,
            &mut NoCoins
        )
        .is_err());
    // Native format permits identity A/B/C; a modified proof still faces every
    // Groth16 equation. Decoder acceptance is never claimed as proof acceptance.
    for (offset, len) in [(82, 48), (130, 96), (226, 48)] {
        let mut wire = good.clone();
        wire[offset..offset + len].fill(0);
        wire[offset] = 0xc0;
        let decoded = decode_received::<2>(&[&wire]).unwrap();
        assert_eq!(decoded[0].encode(), wire);
        if offset == 82 {
            assert!(key
                .verify_received::<2>(
                    &[&wire],
                    Mode::Specification,
                    RandomProfile::CachedGtAnchor,
                    &mut NoCoins
                )
                .is_err());
        }
    }
    darlt_spseq_fc::ops::reset();
    let decoded = decode_received::<2>(&[&good]).unwrap();
    let counts = darlt_spseq_fc::ops::stop();
    assert_eq!(decoded[0].encode(), good);
    assert_eq!(counts.miller_loop_terms, 0);
    assert_eq!(counts.final_exponentiations, 0);
    assert!(counts.msm_g1_sizes.is_empty() && counts.msm_g2_sizes.is_empty());
    assert_eq!(counts.gt_exponentiations, 0);
}

#[cfg(feature = "subgroup-audit")]
#[test]
fn sealed_proof_slots_are_checked_once_for_all_bank_profiles_and_inclusive_state() {
    use darlt_spseq_fc::{
        batch_runtime::{self as rt, Mode},
        common::spent::SpentStore,
        lcb24::Verifier,
        subgroup_audit,
    };
    let mut rng = StdRng::seed_from_u64(32032);
    let bank = Bank::<2>::setup(&mut rng).unwrap();
    let key = bridge::key(&bank).unwrap();
    let mut wallet = bank.issue_wallet(&mut rng).unwrap();
    bank.precompute_amount(&mut wallet, 3, &mut rng).unwrap();
    let native = bank.spend_prepared(&mut wallet, 3).unwrap();
    let p = bridge::payment::<2>(&native).unwrap();
    assert_eq!(p.blocks.len(), 2);
    let wire = p.encode();
    for profile in [RandomProfile::CachedGtAnchor, RandomProfile::PairingAnchor] {
        for mode in [Mode::Specification, Mode::Randomized] {
            let (result, audit) = subgroup_audit::collect(|| {
                key.verify_received::<2>(&[&wire], mode, profile, &mut rng)
            });
            result.unwrap();
            assert_eq!(audit.events.len(), 6);
            assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
            let verifier = Verifier::<2>::new(&key, profile);
            let store = SpentStore::new();
            let (result, audit) = subgroup_audit::collect(|| {
                let checked = decode_received::<2>(&[&wire])?;
                rt::verify_and_record(
                    &verifier,
                    &checked,
                    b"sealed-native",
                    b"accepted",
                    &store,
                    mode,
                    &mut rng,
                )
                .map_err(|e| e.to_string())
            });
            assert_eq!(result.unwrap().newly_registered, 3);
            assert_eq!(audit.events.len(), 6);
            assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
        }
    }
    let (result, audit) = subgroup_audit::collect(|| {
        key.verify::<2>(
            &[p],
            Mode::Randomized,
            RandomProfile::CachedGtAnchor,
            &mut rng,
        )
    });
    result.unwrap();
    assert_eq!(audit.events.len(), 6);
    assert!(audit.events.iter().all(|e| e.operation == "membership"));
}

#[cfg(feature = "subgroup-audit")]
#[test]
fn cold_key_coordinate_transport_checks_each_field_once_and_preserves_native_key_domains() {
    use darlt_spseq_fc::{lcb24::Key, subgroup_audit};
    use group::Group;
    let mut rng = StdRng::seed_from_u64(32034);
    let bank = Bank::<2>::setup(&mut rng).unwrap();
    let packed = bridge::key(&bank).unwrap().bytes().to_vec();
    assert_eq!(packed.len(), 441);
    let g1 = |bytes: &[u8]| {
        Option::<blstrs::G1Projective>::from(blstrs::G1Projective::from_compressed(
            bytes.try_into().unwrap(),
        ))
        .unwrap()
    };
    let g2 = |bytes: &[u8]| {
        Option::<blstrs::G2Projective>::from(blstrs::G2Projective::from_compressed(
            bytes.try_into().unwrap(),
        ))
        .unwrap()
    };
    let (a, b, g, d) = (
        g1(&packed[1..49]),
        g2(&packed[49..145]),
        g2(&packed[145..241]),
        g2(&packed[241..337]),
    );
    let i = [g1(&packed[345..393]), g1(&packed[393..441])];
    let reference = Key::install(a, b, g, d, i).unwrap();
    let (key, audit) = subgroup_audit::collect(|| bridge::key(&bank));
    assert_eq!(key.unwrap().bytes(), reference.bytes());
    assert_eq!(audit.events.len(), 6);
    assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
    assert_eq!(audit.events.iter().filter(|e| e.kind == "G1").count(), 3);
    assert_eq!(audit.events.iter().filter(|e| e.kind == "G2").count(), 3);
    let (a, b, g, d, inputs) = (
        a.to_uncompressed(),
        b.to_uncompressed(),
        g.to_uncompressed(),
        d.to_uncompressed(),
        i.map(|p| p.to_uncompressed()),
    );
    let bad1 =
        Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed_unchecked(&bad_g1()))
            .unwrap()
            .to_uncompressed();
    let bad2 =
        Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed_unchecked(&bad_g2()))
            .unwrap()
            .to_uncompressed();
    assert!(Key::install_uncompressed(&bad1, &b, &g, &d, &inputs).is_err());
    for index in 0..2 {
        let mut changed = inputs;
        changed[index] = bad1;
        assert!(Key::install_uncompressed(&a, &b, &g, &d, &changed).is_err());
    }
    let id1 = blstrs::G1Projective::identity().to_uncompressed();
    assert!(Key::install_uncompressed(&id1, &b, &g, &d, &[id1, id1]).is_ok());
    let id2 = blstrs::G2Projective::identity().to_uncompressed();
    for bad in [bad2, id2] {
        assert!(Key::install_uncompressed(&a, &bad, &g, &d, &inputs).is_err());
        assert!(Key::install_uncompressed(&a, &b, &bad, &d, &inputs).is_err());
        assert!(Key::install_uncompressed(&a, &b, &g, &bad, &inputs).is_err());
    }
    let mut alias = a;
    alias[..48].copy_from_slice(&fp_plus_modulus(a[..48].try_into().unwrap()));
    assert!(Key::install_uncompressed(&alias, &b, &g, &d, &inputs).is_err());
    let mut alias = b;
    alias[48..96].copy_from_slice(&fp_plus_modulus(b[48..96].try_into().unwrap()));
    assert!(Key::install_uncompressed(&a, &alias, &g, &d, &inputs).is_err());
}
