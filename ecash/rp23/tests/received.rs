//! Received-wire validation uses the same parser in both native verifier modes.
use rand::{rngs::StdRng, CryptoRng, RngCore, SeedableRng};
use rp23_native::{
    api::*,
    backend::{self, VerificationMode},
};
const M: [u8; 16] = [7; 16];
struct NoCoins;
impl RngCore for NoCoins {
    fn next_u32(&mut self) -> u32 {
        panic!("malformed input reached verifier weights")
    }
    fn next_u64(&mut self) -> u64 {
        panic!("malformed input reached verifier weights")
    }
    fn fill_bytes(&mut self, _: &mut [u8]) {
        panic!("malformed input reached verifier weights")
    }
    fn try_fill_bytes(&mut self, _: &mut [u8]) -> std::result::Result<(), rand::Error> {
        panic!("malformed input reached verifier weights")
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
fn identity_g1() -> [u8; 48] {
    let mut b = [0; 48];
    b[0] = 0xc0;
    b
}
fn frame<'a>(wire: &'a [u8], info: &'a PayInfo) -> ReceivedPayment<'a> {
    ReceivedPayment {
        payment_bytes: wire,
        payinfo_bytes: &info.0,
    }
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
macro_rules! check_received {
    ($ctx:expr,$kind:ident) => {{
        let ctx = $ctx;
        let info = PayInfo::new(M, [9; 16]);
        let w = ctx.issue().unwrap();
        let p = ctx.spend(&w, 3, info).unwrap();
        let good = p.encode();
        let mut rng = StdRng::seed_from_u64(31);
        for mode in [
            VerificationMode::Specification,
            VerificationMode::Randomized,
        ] {
            ctx.verify_received(&[frame(&good, &info)], &M, mode, &mut rng)
                .unwrap();
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
        b[105..153].copy_from_slice(&bad_g1());
        malformed.push(b);
        let mut b = good.clone();
        b[9..105].copy_from_slice(&bad_g2());
        malformed.push(b);
        let mut b = good.clone();
        b[105..153].copy_from_slice(&identity_g1());
        malformed.push(b);
        let mut b = good.clone();
        let n = b.len();
        b[n - 32..].fill(255);
        malformed.push(b);
        let mut b = good.clone();
        b[105..153].copy_from_slice(&alias_g1());
        malformed.push(b);
        let mut b = good.clone();
        b[9..105].copy_from_slice(&alias_g2());
        malformed.push(b);
        for b in malformed {
            assert!(ctx.decode_received(&[frame(&b, &info)], &M).is_err());
            assert!(ctx
                .verify_received(
                    &[frame(&b, &info)],
                    &M,
                    VerificationMode::Randomized,
                    &mut NoCoins
                )
                .is_err());
            // No random check of an earlier valid message may precede later decoding.
            assert!(ctx
                .verify_received(
                    &[frame(&good, &info), frame(&b, &info)],
                    &M,
                    VerificationMode::Randomized,
                    &mut NoCoins
                )
                .is_err());
        }
        for info_wire in [&info.0[..31], &[0; 33][..], &[8; 32][..]] {
            assert!(ctx
                .verify_received(
                    &[ReceivedPayment {
                        payment_bytes: &good,
                        payinfo_bytes: info_wire
                    }],
                    &M,
                    VerificationMode::Randomized,
                    &mut NoCoins
                )
                .is_err());
        }
        let mut wrong_nonce = info.0;
        wrong_nonce[31] ^= 1;
        assert!(ctx
            .verify_received(
                &[ReceivedPayment {
                    payment_bytes: &good,
                    payinfo_bytes: &wrong_nonce
                }],
                &M,
                VerificationMode::Randomized,
                &mut NoCoins
            )
            .is_err());
        // Signature second elements are not subject to the native h!=1 rule.
        // Format acceptance does not mean a modified signature is valid.
        let mut permitted_identity = good.clone();
        permitted_identity[153..201].copy_from_slice(&identity_g1());
        let decoded = $kind::decode(&permitted_identity, info, 8).unwrap();
        assert_eq!(decoded.encode(), permitted_identity);
        assert!(ctx
            .verify_received(
                &[frame(&permitted_identity, &info)],
                &M,
                VerificationMode::Specification,
                &mut rng
            )
            .is_err());
        backend::start_counts();
        let parsed = ctx.decode_received(&[frame(&good, &info)], &M).unwrap();
        let counts = backend::stop_counts();
        assert_eq!(parsed[0].encode(), good);
        assert_eq!(counts.miller_terms, 0);
        assert_eq!(counts.final_exponentiations, 0);
        assert_eq!(counts.gt_exp, 0);
        assert!(counts.g1_msm_sizes.is_empty() && counts.g2_msm_sizes.is_empty());
    }};
}
#[test]
fn compact_received_wire_is_atomic_before_weights_and_preserves_native_identity_domain() {
    check_received!(Compact::new(8).unwrap(), CompactPayment);
    let c = Compact::new(8).unwrap();
    let info = PayInfo::new(M, [3; 16]);
    let p = c.spend(&c.issue().unwrap(), 3, info).unwrap();
    let mut wire = p.encode();
    let first_range_h = 201 + 272 * 3;
    wire[first_range_h..first_range_h + 48].copy_from_slice(&identity_g1());
    assert!(c
        .verify_received(
            &[ReceivedPayment {
                payment_bytes: &wire,
                payinfo_bytes: &info.0
            }],
            &M,
            VerificationMode::Randomized,
            &mut NoCoins
        )
        .is_err());
}
#[test]
fn divisible_received_wire_is_atomic_before_weights_and_preserves_native_identity_domain() {
    check_received!(Divisible::new(8).unwrap(), DivisiblePayment);
}

#[cfg(feature = "subgroup-audit")]
#[test]
fn sealed_received_slots_are_checked_once_in_both_profiles_and_inclusive_state() {
    use darlt_spseq_fc::{
        batch_runtime::{self as rt, Adapter, Mode},
        common::spent::SpentStore,
        subgroup_audit,
    };
    use rp23_native::shared_runtime::{CompactVerifier, DivisibleVerifier};
    macro_rules! audit {
        ($ctx:expr,$verifier:ident,$g1:expr,$g2:expr) => {{
            let ctx = $ctx;
            let info = PayInfo::new(M, [32; 16]);
            let w = ctx.issue().unwrap();
            let p = ctx.spend(&w, 3, info).unwrap();
            let wire = p.encode();
            let frames = [frame(&wire, &info)];
            let mut rng = StdRng::seed_from_u64(32032);
            for mode in [
                VerificationMode::Specification,
                VerificationMode::Randomized,
            ] {
                let (result, audit) =
                    subgroup_audit::collect(|| ctx.verify_received(&frames, &M, mode, &mut rng));
                result.unwrap();
                assert_eq!(audit.events.len(), $g1 + $g2);
                assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
                assert_eq!(audit.events.iter().filter(|e| e.kind == "G1").count(), $g1);
                assert_eq!(audit.events.iter().filter(|e| e.kind == "G2").count(), $g2);
            }
            let verifier = $verifier::new(&ctx, M);
            for mode in [Mode::Specification, Mode::Randomized] {
                let store = SpentStore::new();
                let (result, audit) = subgroup_audit::collect(|| {
                    let checked = ctx.decode_received(&frames, &M)?;
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
                assert_eq!(audit.events.len(), $g1 + $g2);
                assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
            }
            // The separate mutable typed API is also safe, and checks all points once.
            let (ok, audit) = subgroup_audit::collect(|| {
                ctx.verify(&[p], &M, VerificationMode::Randomized, &mut rng)
            });
            assert!(ok);
            assert_eq!(audit.events.len(), $g1 + $g2);
            assert!(audit.events.iter().all(|e| e.operation == "membership"));
            assert!(!verifier.namespace().is_empty());
        }};
    }
    audit!(Compact::new(16).unwrap(), CompactVerifier, 18, 4);
    let d = Divisible::new(16).unwrap();
    d.install_public_pairing_bases(&[3]);
    audit!(d, DivisibleVerifier, 12, 2);
}

#[cfg(feature = "subgroup-audit")]
#[test]
fn cold_divisible_cache_reuses_immutable_parameter_provenance_and_preserves_eight_pairings() {
    use darlt_spseq_fc::subgroup_audit;
    let d = Divisible::new(16).unwrap();
    let info = PayInfo::new(M, [33; 16]);
    let p = d.spend(&d.issue().unwrap(), 3, info).unwrap();
    let wire = p.encode();
    let mut rng = StdRng::seed_from_u64(32033);
    d.clear_pairing_cache();
    backend::start_counts();
    let ((), audit) = subgroup_audit::collect(|| d.install_public_pairing_bases(&[3]));
    let counts = backend::stop_counts();
    assert!(audit.events.is_empty());
    assert_eq!((counts.miller_terms, counts.final_exponentiations), (8, 8));
    let mut results = vec![];
    for cold in [false, true] {
        if cold {
            d.clear_pairing_cache();
        }
        backend::start_counts();
        let (result, audit) = subgroup_audit::collect(|| {
            d.verify_received(
                &[frame(&wire, &info)],
                &M,
                VerificationMode::Specification,
                &mut rng,
            )
        });
        let counts = backend::stop_counts();
        result.unwrap();
        assert_eq!(audit.events.len(), 14);
        assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
        results.push(counts);
    }
    assert_eq!(results[1].miller_terms, results[0].miller_terms + 8);
    assert_eq!(
        results[1].final_exponentiations,
        results[0].final_exponentiations + 8
    );
}
