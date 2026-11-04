use baseline_core::{arithmetic::*, cdm as mv, slw25::*};
use blstrs::{G1Affine, G2Affine};
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};
use std::sync::OnceLock;
struct Fixture {
    pk: PublicKey,
    sk: IssuerSecret,
    old: Holder,
    new: Holder,
    attrs: Vec<S>,
    original: Credential,
    child: Credential,
}
fn fixture() -> &'static Fixture {
    static F: OnceLock<Fixture> = OnceLock::new();
    F.get_or_init(|| {
        let mut r = StdRng::seed_from_u64(12124);
        let (pk, sk) = setup(10, &mut r).unwrap();
        let old = Holder::generate(&mut r);
        let new = Holder::generate(&mut r);
        let attrs = (100..110).map(S::from).collect::<Vec<_>>();
        let (original, _) = run_issue(&pk, &sk, &old, &attrs, &mut r).unwrap();
        let (child, _) =
            run_delegate(&pk, &old, &new, &original, &[2, 3, 4, 5, 6, 7], &mut r).unwrap();
        Fixture {
            pk,
            sk,
            old,
            new,
            attrs,
            original,
            child,
        }
    })
}
fn head(tag: &[u8]) -> usize {
    13 + tag.len()
}
fn replace(mut bytes: Vec<u8>, start: usize, value: &[u8]) -> Vec<u8> {
    bytes[start..start + value.len()].copy_from_slice(value);
    bytes
}
fn g1_non_subgroup() -> [u8; 48] {
    (1u64..64)
        .find_map(|x| {
            let mut b = [0; 48];
            b[0] = 0x80;
            b[40..].copy_from_slice(&x.to_be_bytes());
            Option::<G1Affine>::from(G1Affine::from_compressed_unchecked(&b))
                .filter(|p| !bool::from(p.is_torsion_free()))
                .map(|_| b)
        })
        .unwrap()
}
fn be_limbs(l: [u64; 6]) -> Vec<u8> {
    l.iter().rev().flat_map(|x| x.to_be_bytes()).collect()
}
fn g2_non_subgroup() -> [u8; 96] {
    let mut b = be_limbs([
        0x26f461e944bbd3d1,
        0x298f3189a9cf6ed6,
        0x74328ad8bc2aa150,
        0x07e147f3f9e6e241,
        0x72a9b63583963fff,
        0x0158b0083c000462,
    ]);
    b.extend(be_limbs([
        0x0262cea73ea1906c,
        0x02f08540770fabd6,
        0x4ceb92d0a76057be,
        0x2199bc19c48c393d,
        0x4a151b732a6075bf,
        0x17762a3b9108c4a7,
    ]));
    b[0] |= 0x80;
    b.try_into().unwrap()
}
#[test]
fn honest_both_branches_and_full_message_wire_roundtrips() {
    let f = fixture();
    let mut r = StdRng::seed_from_u64(24);
    assert_eq!(
        receive_expected(
            &f.pk,
            &f.old,
            &f.original.encode(),
            &(2..12).collect::<Vec<_>>(),
            &f.attrs
        )
        .unwrap()
        .encode(),
        f.original.encode()
    );
    assert_eq!(
        receive(&f.pk, &f.new, &f.child.encode()).unwrap().encode(),
        f.child.encode()
    );
    for (h, c) in [(&f.old, &f.original), (&f.new, &f.child)] {
        let t = run_show(&f.pk, h, c, &[2, 3, 4], &mut r).unwrap();
        assert_eq!(t.messages.len(), 5);
        assert!(t.bytes() > 0);
    }
    let installed = PublicKey::decode_install(&f.pk.encode()).unwrap();
    assert_eq!(installed.encode(), f.pk.encode());
}
#[test]
fn every_original_and_child_signature_attribute_field_rejected_when_mutated() {
    let f = fixture();
    for (h, c, partial) in [(&f.old, &f.original, false), (&f.new, &f.child, true)] {
        let bytes = c.encode();
        let base =
            head(b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31")
                + 1
                + 8
                + 4 * c.retained().len();
        for i in 0..c.attributes().len() {
            let bad = replace(
                bytes.clone(),
                base + 32 * i,
                &(c.attributes()[i] + S::ONE).to_bytes_be(),
            );
            assert!(receive(&f.pk, h, &bad).is_err());
        }
        let point = base + 32 * c.attributes().len();
        let slots = if partial {
            vec![
                (point, 48),
                (point + 48, 48),
                (point + 96, 96),
                (point + 192, 96),
            ]
        } else {
            (0..4).map(|i| (point + 96 * i, 96)).collect()
        };
        for (offset, n) in slots {
            let val = if n == 48 {
                (G1::generator() * S::from(17)).to_compressed().to_vec()
            } else {
                (G2::generator() * S::from(17)).to_compressed().to_vec()
            };
            assert!(receive(&f.pk, h, &replace(bytes.clone(), offset, &val)).is_err());
        }
        let mut mode = bytes.clone();
        mode[head(
            b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31",
        )] = if partial { 0 } else { 1 };
        assert!(receive(&f.pk, h, &mode).is_err());
    }
    assert!(receive(&f.pk, &f.old, &f.child.encode()).is_err());
    assert!(receive(&f.pk, &f.new, &f.original.encode()).is_err());
}
#[test]
fn bad_points_subgroups_identities_and_noncanonical_fields_rejected_at_receive() {
    let f = fixture();
    let b = f.child.encode();
    let point =
        head(b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31")
            + 1
            + 8
            + 4 * 6
            + 32 * 6;
    let bg1 = g1_non_subgroup();
    let bg2 = g2_non_subgroup();
    assert!(bool::from(
        G1Affine::from_compressed_unchecked(&bg1).is_some()
    ));
    assert!(bool::from(
        G2Affine::from_compressed_unchecked(&bg2).is_some()
    ));
    assert!(receive(&f.pk, &f.new, &replace(b.clone(), point, &bg1)).is_err());
    assert!(receive(&f.pk, &f.new, &replace(b.clone(), point + 96, &bg2)).is_err());
    for bad in [[0u8; 96], [255u8; 96], G2::identity().to_compressed()] {
        assert!(receive(&f.pk, &f.new, &replace(b.clone(), point + 96, &bad)).is_err());
    }
    for bad in [[0u8; 48], [255u8; 48]] {
        assert!(receive(&f.pk, &f.new, &replace(b.clone(), point, &bad)).is_err());
    }
    let attrs =
        head(b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31")
            + 1
            + 8
            + 4 * 6;
    assert!(receive(&f.pk, &f.new, &replace(b.clone(), attrs, &[255; 32])).is_err());
    let mut tail = b.clone();
    tail.push(0);
    assert!(receive(&f.pk, &f.new, &tail).is_err());
    for len in [0, 1, 5, 13, point, point + 47, b.len() - 1] {
        assert!(receive(&f.pk, &f.new, &b[..len]).is_err());
    }
}
#[test]
fn indices_modes_and_flat_boundary_rejected() {
    let f = fixture();
    let mut r = StdRng::seed_from_u64(7);
    for keep in [vec![2, 2], vec![3, 2], vec![0, 2], vec![1, 2], vec![2, 12]] {
        assert!(delegate_prepare(&f.pk, &f.old, &f.original, &keep, &mut r).is_err());
    }
    assert!(delegate_prepare(&f.pk, &f.new, &f.child, &[2, 3], &mut r).is_err());
    for disclosed in [vec![2, 2], vec![3, 2], vec![1], vec![8], vec![12]] {
        assert!(show_prepare(&f.pk, &f.new, &f.child, &disclosed, &mut r).is_err());
    }
    let mut b = f.child.encode();
    b[head(b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31")] = 2;
    assert!(receive(&f.pk, &f.new, &b).is_err());
    let idx = head(b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31")
        + 1
        + 8;
    let b = replace(f.child.encode(), idx + 4, &2u32.to_be_bytes());
    assert!(receive(&f.pk, &f.new, &b).is_err());
}
fn live_show_with_received_prefix(mut change: impl FnMut(Vec<u8>) -> Vec<u8>) -> bool {
    let f = fixture();
    let mut rng = StdRng::seed_from_u64(100);
    let (mut prep, prefix) = show_prepare(&f.pk, &f.new, &f.child, &[2, 3, 4], &mut rng).unwrap();
    let changed = change(prefix);
    let result = (|| -> baseline_core::encoding::Result<bool> {
        let (vs, v1) = show_verifier_begin(&f.pk, &changed, &mut rng)?;
        let (ps, p2) = show_holder_first(&f.pk, &mut prep, &v1, &mut rng)?;
        let (vs, v3) = show_verifier_challenge(vs, &p2, &mut rng)?;
        let p4 = show_holder_respond(ps, &v3)?;
        show_verifier_finish(vs, &p4)
    })();
    result.unwrap_or(false)
}
#[test]
fn every_public_show_statement_field_is_checked() {
    assert!(live_show_with_received_prefix(|b| b));
    let h =
        head(b"\x53\x4c\x57\x32\x34\x2d\x73\x68\x6f\x77\x2d\x70\x72\x65\x66\x69\x78\x2d\x76\x31");
    let attr = h + 8 + 6 * 4 + 8 + 3 * 4;
    let point = attr + 3 * 32;
    for i in 0..3 {
        assert!(!live_show_with_received_prefix(|b| replace(
            b,
            attr + 32 * i,
            &S::from(991 + i as u64).to_bytes_be()
        )));
    }
    for offset in [point, point + 48] {
        let v = (G1::generator() * S::from(1001)).to_compressed();
        assert!(!live_show_with_received_prefix(|b| replace(b, offset, &v)));
    }
    for offset in [point + 96, point + 192] {
        for v in [G2::identity(), G2::generator() * S::from(1001)] {
            assert!(!live_show_with_received_prefix(|b| replace(
                b,
                offset,
                &v.to_compressed()
            )));
        }
    }
    for (offset, val) in [
        (h + 8, 1u32),
        (h + 8 + 4, 2u32),
        (h + 8 + 6 * 4 + 8, 12u32),
        (h + 8 + 5 * 4, 8u32),
        (h + 8 + 6 * 4 + 8 + 2 * 4, 6u32),
    ] {
        assert!(!live_show_with_received_prefix(|b| replace(
            b,
            offset,
            &val.to_be_bytes()
        )));
    }
}
#[test]
fn issue_request_fields_remain_bound_through_proof_and_receive() {
    let f = fixture();
    let h = head(
        b"\x53\x4c\x57\x32\x34\x2d\x69\x73\x73\x75\x65\x2d\x72\x65\x71\x75\x65\x73\x74\x2d\x76\x31",
    );
    for field in 0..12 {
        let mut r = StdRng::seed_from_u64(551 + field);
        let request = issue_request(&f.pk, &f.old, &f.attrs).unwrap();
        let changed = if field == 0 {
            replace(
                request.clone(),
                h,
                &(G2::generator() * S::from(51)).to_compressed(),
            )
        } else if field == 1 {
            replace(
                request.clone(),
                h + 96,
                &(f.old.eid() + S::ONE).to_bytes_be(),
            )
        } else {
            let i = (field - 2) as usize;
            replace(
                request.clone(),
                h + 96 + 32 + 4 + 32 * i,
                &(f.attrs[i] + S::ONE).to_bytes_be(),
            )
        };
        let result = (|| -> baseline_core::encoding::Result<Credential> {
            let (vs, v1) = issuer_begin(&f.pk, &changed, &mut r)?;
            let (ps, p2) = holder_issue_first(&f.pk, &f.old, &request, &v1, &mut r)?;
            let (vs, v3) = issuer_issue_challenge(vs, &p2, &mut r)?;
            let p4 = holder_issue_respond(ps, &v3)?;
            let c = issuer_issue_finish(&f.pk, &f.sk, vs, &p4, &mut r)?;
            receive_expected(&f.pk, &f.old, &c, &(2..12).collect::<Vec<_>>(), &f.attrs)
        })();
        assert!(result.is_err());
    }
}
#[test]
fn delegate_update_key_and_receiver_cm_fields_checked_by_live_proof() {
    let f = fixture();
    for field in 0..3 {
        let mut r = StdRng::seed_from_u64(778 + field);
        let (mut prep, prefix) =
            delegate_prepare(&f.pk, &f.old, &f.original, &[2, 3, 4, 5, 6, 7], &mut r).unwrap();
        let prefix = if field < 2 {
            replace(
                prefix,
                head(b"\x53\x4c\x57\x32\x34\x2d\x64\x65\x6c\x65\x67\x61\x74\x65\x2d\x70\x72\x65\x66\x69\x78\x2d\x76\x31") + 96 * field as usize,
                &(G2::generator() * S::from(700)).to_compressed(),
            )
        } else {
            prefix
        };
        let (cmstate, cm) = receiver_cm(&f.pk, &f.new, &prefix).unwrap();
        let cm = if field == 2 {
            replace(
                cm,
                head(b"\x53\x4c\x57\x32\x34\x2d\x72\x65\x63\x65\x69\x76\x65\x72\x2d\x63\x6d\x2d\x76\x31"),
                &(G2::generator() * S::from(701)).to_compressed(),
            )
        } else {
            cm
        };
        let result = (|| -> baseline_core::encoding::Result<Credential> {
            let (vs, v1) = delegator_begin(&mut prep, &cm, &mut r)?;
            let (ps, p2) = receiver_first(cmstate, &v1, &mut r)?;
            let (vs, v3) = delegator_challenge(vs, &p2, &mut r)?;
            let p4 = receiver_respond(ps, &v3)?;
            let c = delegator_finish(vs, &p4)?;
            receive_expected(&f.pk, &f.new, &c, &[2, 3, 4, 5, 6, 7], &f.attrs[..6])
        })();
        assert!(result.is_err());
    }
}
#[test]
fn full_live_show_final_fields_and_verifier_opening_are_rejected_when_changed() {
    let f = fixture();
    for slot in 0..12 {
        let mut r = StdRng::seed_from_u64(800 + slot);
        let (mut prep, b) = show_prepare(&f.pk, &f.new, &f.child, &[2, 3, 4], &mut r).unwrap();
        let (vs, v1) = show_verifier_begin(&f.pk, &b, &mut r).unwrap();
        let (ps, p2) = show_holder_first(&f.pk, &mut prep, &v1, &mut r).unwrap();
        let (vs, v3) = show_verifier_challenge(vs, &p2, &mut r).unwrap();
        let p4 = show_holder_respond(ps, &v3).unwrap();
        let mut last = mv::PFourth::decode(&p4).unwrap();
        if slot == 0 {
            last.true_challenge += S::ONE;
        } else if slot <= 5 {
            last.true_responses[(slot - 1) as usize] += S::ONE;
        } else {
            last.opening_responses[(slot - 6) as usize] += S::ONE;
        }
        assert!(!show_verifier_finish(vs, &last.encode()).unwrap());
    }
    let mut r = StdRng::seed_from_u64(77);
    let (mut prep, b) = show_prepare(&f.pk, &f.new, &f.child, &[2, 3, 4], &mut r).unwrap();
    let (vs, v1) = show_verifier_begin(&f.pk, &b, &mut r).unwrap();
    let (ps, p2) = show_holder_first(&f.pk, &mut prep, &v1, &mut r).unwrap();
    let (_vs, v3) = show_verifier_challenge(vs, &p2, &mut r).unwrap();
    let mut third = mv::VThird::decode(&v3).unwrap();
    third.opening_responses[0] += S::ONE;
    assert!(show_holder_respond(ps, &third.encode()).is_err());
}
#[test]
fn prepared_buffers_are_consumed_once_and_fixed_random_tape_replays() {
    let f = fixture();
    let mut r = StdRng::seed_from_u64(121);
    let mut s = r.clone();
    let (a, ai) = run_issue(&f.pk, &f.sk, &f.old, &f.attrs, &mut r).unwrap();
    let (b, bi) = run_issue(&f.pk, &f.sk, &f.old, &f.attrs, &mut s).unwrap();
    assert_eq!(a.encode(), b.encode());
    assert_eq!(ai.messages, bi.messages);
    let (a, ai) = run_delegate(&f.pk, &f.old, &f.new, &a, &[2, 3, 4, 5, 6, 7], &mut r).unwrap();
    let (b, bi) = run_delegate(&f.pk, &f.old, &f.new, &b, &[2, 3, 4, 5, 6, 7], &mut s).unwrap();
    assert_eq!(a.encode(), b.encode());
    assert_eq!(ai.messages, bi.messages);
    assert_eq!(
        run_show(&f.pk, &f.new, &a, &[2, 3, 4], &mut r)
            .unwrap()
            .messages,
        run_show(&f.pk, &f.new, &b, &[2, 3, 4], &mut s)
            .unwrap()
            .messages
    );
    let (mut issue_prepared, request) = issue_prepare(&f.pk, &f.old, &f.attrs).unwrap();
    let (_, v1) = issuer_begin(&f.pk, &request, &mut r).unwrap();
    holder_issue_first_prepared(&mut issue_prepared, &v1, &mut r).unwrap();
    assert!(holder_issue_first_prepared(&mut issue_prepared, &v1, &mut r).is_err());
    let mut offline = delegate_precompute(&f.pk, &f.old, &f.original, &mut r).unwrap();
    let (mut prep, prefix) = delegate_bind(&f.pk, &mut offline, &[2, 3, 4]).unwrap();
    assert!(delegate_bind(&f.pk, &mut offline, &[2, 3]).is_err());
    let (_, cm) = receiver_cm(&f.pk, &f.new, &prefix).unwrap();
    delegator_begin(&mut prep, &cm, &mut r).unwrap();
    assert!(delegator_begin(&mut prep, &cm, &mut r).is_err());
    let mut offline = show_precompute(&f.pk, &f.new, &f.child, &mut r).unwrap();
    let (mut prep, prefix) = show_bind(&f.pk, &mut offline, &[2, 3, 4]).unwrap();
    assert!(show_bind(&f.pk, &mut offline, &[2]).is_err());
    let (_, v1) = show_verifier_begin(&f.pk, &prefix, &mut r).unwrap();
    show_holder_first(&f.pk, &mut prep, &v1, &mut r).unwrap();
    assert!(show_holder_first(&f.pk, &mut prep, &v1, &mut r).is_err());
}
#[test]
fn source_full_field_show_zero_mask_aborts_without_retry() {
    struct Zero;
    impl rand::RngCore for Zero {
        fn next_u32(&mut self) -> u32 {
            0
        }
        fn next_u64(&mut self) -> u64 {
            0
        }
        fn fill_bytes(&mut self, b: &mut [u8]) {
            b.fill(0)
        }
        fn try_fill_bytes(&mut self, b: &mut [u8]) -> Result<(), rand::Error> {
            b.fill(0);
            Ok(())
        }
    }
    impl rand::CryptoRng for Zero {}
    let f = fixture();
    for (h, c) in [(&f.old, &f.original), (&f.new, &f.child)] {
        assert!(show_precompute(&f.pk, h, c, &mut Zero).is_err());
    }
    // eid belongs to Fr in the source registration interface.
    assert!(Holder::from_secrets(S::ONE, S::ZERO).is_ok());
    assert!(Holder::from_secrets(S::ZERO, S::ONE).is_err());
}
#[test]
fn installed_key_checks_cross_group_consistency_and_domain() {
    let f = fixture();
    let mut raw = f.pk.raw();
    raw.yh[0] += G2::generator();
    assert!(PublicKey::install(raw).is_err());
    let mut raw = f.pk.raw();
    raw.z[0][1] += G1::generator();
    assert!(PublicKey::install(raw).is_err());
    let mut raw = f.pk.raw();
    raw.x = G1::identity();
    assert!(PublicKey::install(raw).is_err());
}
