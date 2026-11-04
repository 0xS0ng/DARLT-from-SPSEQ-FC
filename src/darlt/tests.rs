use super::{
    protocol::*,
    spend::{self, Atom, Policy, Token},
    verification::Mode,
};
#[cfg(feature = "op-counts")]
use crate::ops;
use crate::polynomial::S;
use blstrs::G1Projective as G1;
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};
use std::{
    collections::BTreeSet,
    sync::{Arc, OnceLock},
};
fn instance() -> (Arc<PublicParameters>, IssuerPublic, IssuerSecret) {
    static INSTANCE: OnceLock<(Arc<PublicParameters>, IssuerPublic, IssuerSecret)> =
        OnceLock::new();
    INSTANCE
        .get_or_init(|| {
            let mut rng = StdRng::seed_from_u64(202021);
            let pp = Arc::new(
                PublicParameters::setup(1024, 16, 64, 6, 4, b"period-1", &mut rng).unwrap(),
            );
            let (ip, sk) = keygen(&pp, &mut rng).unwrap();
            install(&pp, &ip).unwrap();
            (pp, ip, sk)
        })
        .clone()
}
fn wallet(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    sk: &IssuerSecret,
    bit: usize,
    rng: &mut StdRng,
) -> Wallet {
    let (q, s) = prepare_request(
        pp,
        ip,
        S::from(91),
        &[
            S::ONE,
            S::from(21),
            S::from(22),
            S::from(23),
            S::from(24),
            S::from(25),
        ],
        &[S::from(7), S::from(8), S::from(9), S::from(10)],
        rng,
    )
    .unwrap();
    let r = issue(pp, ip, sk, &q, bit, rng).unwrap();
    accept(pp, ip, &q, &s, &r, rng).unwrap()
}
fn policy() -> Policy {
    Policy {
        period: 1,
        atoms: vec![
            Atom::Equal(0, S::ONE),
            Atom::Reveal(1, S::from(21)),
            Atom::Reveal(2, S::from(22)),
        ],
    }
}
fn token(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    h: &mut Holder,
    pos: &[usize],
    ctx: &[u8],
    rng: &mut StdRng,
) -> Token {
    let p = spend::prepare_spend(pp, ip, h, pos, &policy(), rng).unwrap();
    spend::finish_spend(pp, ip, p, ctx, rng).unwrap()
}
#[test]
fn end_to_end_all_block_sizes_and_wire_codec() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202022);
    let mut w = wallet(&pp, &ip, &sk, 1, &mut rng);
    assert!(w.openings.is_empty());
    let mut h = self_derive(&pp, &mut w, &[0, 1, 2, 3, 4, 5, 6, 7], &mut rng).unwrap();
    assert_eq!(w.openings.len(), 8);
    assert!(h.scope_openings.is_empty());
    for k in [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64] {
        let pos: Vec<_> = (0..k).collect();
        let t = token(&pp, &ip, &mut h, &pos, b"merchant-A", &mut rng);
        assert!(
            spend::valid(&pp, &ip, &t, Mode::Specification, &mut rng),
            "spec k={k}"
        );
        assert!(
            spend::valid(&pp, &ip, &t, Mode::Randomized, &mut rng),
            "random k={k}"
        );
        let bytes = t.wire_encode();
        let ledger = super::evidence::token_ledger(&t).unwrap();
        assert_eq!(
            ledger
                .iter()
                .map(|r| r["bytes"].as_u64().unwrap())
                .sum::<u64>() as usize,
            bytes.len()
        );
        assert_eq!(bytes.len(), 3478 + 320 * k); // 10-byte context in this fixture.
        let parsed = Token::wire_decode(&pp, &bytes).unwrap();
        assert_eq!(parsed.wire_encode(), bytes);
        assert!(spend::valid(&pp, &ip, &parsed, Mode::Randomized, &mut rng));
    }
}
#[test]
fn agent_receipt_mask_refresh_and_metadata_inheritance() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202023);
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let old = w.parent.clone();
    let d = derive(
        &pp,
        &mut w,
        G1::generator() * S::from(101),
        &[1, 3],
        &[true, true, true, false, false, false],
        &mut rng,
    )
    .unwrap();
    assert_ne!(d.parent[1], old[1]);
    assert_ne!(d.parent[2], old[2]);
    for j in [0, 3, 4, 5, 6, 7] {
        assert_eq!(d.parent[j], old[j]);
    }
    let mut h = complete(
        &pp,
        &ip,
        &d,
        S::from(101),
        None,
        Mode::Specification,
        &mut rng,
    )
    .unwrap();
    assert_eq!(h.pools.len(), 2);
    assert!(h.scope_openings.is_empty());
    let t = token(&pp, &ip, &mut h, &[16, 31, 48], b"agent-ctx", &mut rng);
    assert!(spend::valid(&pp, &ip, &t, Mode::Randomized, &mut rng));
    assert_eq!(
        spend::read_bit(
            &pp,
            &ip,
            &t,
            &sk.metadata_secrets,
            Mode::Specification,
            &mut rng
        ),
        Some(0)
    );
    let p = Policy {
        period: 1,
        atoms: vec![Atom::Equal(0, S::ONE), Atom::Range(6, 0, 255)],
    };
    assert!(spend::prepare_spend(&pp, &ip, &mut h, &[17], &p, &mut rng).is_err());
    for col in 0..2 {
        let mut bad = d.clone();
        bad.pools[0].openings[col] += blstrs::G2Projective::generator();
        assert!(complete(
            &pp,
            &ip,
            &bad,
            S::from(101),
            None,
            Mode::Randomized,
            &mut rng
        )
        .is_err());
    }
}
#[test]
fn private_owner_range_and_bad_policy() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202024);
    let mut w = wallet(&pp, &ip, &sk, 1, &mut rng);
    let mut h = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
    for bits in [8, 16, 32] {
        let p = Policy {
            period: 1,
            atoms: vec![
                Atom::Equal(0, S::ONE),
                Atom::Range(6, 0, (1u64 << bits) - 1),
            ],
        };
        let pre = spend::prepare_spend(&pp, &ip, &mut h, &[0], &p, &mut rng).unwrap();
        let t = spend::finish_spend(&pp, &ip, pre, b"range", &mut rng).unwrap();
        assert!(spend::valid(&pp, &ip, &t, Mode::Specification, &mut rng));
        let parsed = Token::wire_decode(&pp, &t.wire_encode()).unwrap();
        assert!(spend::valid(&pp, &ip, &parsed, Mode::Randomized, &mut rng));
    }
    let p = Policy {
        period: 1,
        atoms: vec![Atom::Equal(0, S::ONE), Atom::Range(6, 10, 11)],
    };
    assert!(spend::prepare_spend(&pp, &ip, &mut h, &[1], &p, &mut rng).is_err());
}
#[test]
fn every_new_token_component_is_bound() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202025);
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let mut h = self_derive(&pp, &mut w, &[0, 1], &mut rng).unwrap();
    let t = token(&pp, &ip, &mut h, &[0, 1, 17], b"ctx", &mut rng);
    for j in 0..13 {
        let mut bad = t.clone();
        match j {
            0 => bad.scope += G1::generator(),
            1 => bad.offset_table += G1::generator(),
            2..=4 => bad.commitments[j - 2] += G1::generator(),
            5 => bad.seed_query += G1::generator(),
            6 => bad.units[0].sn += G1::generator(),
            7 => bad.units[0].aid += G1::generator(),
            8 => bad.units[0].tu += G1::generator(),
            9 => bad.units[0].ta += G1::generator(),
            10 => bad.context.push(1),
            11 => bad.lookups.swap(0, 1),
            _ => bad.auth.signature.z += G1::generator(),
        };
        assert!(
            !spend::valid(&pp, &ip, &bad, Mode::Randomized, &mut rng),
            "mutation {j}"
        );
    }
    let mut bad = t.clone();
    bad.units[1] = bad.units[0].clone();
    assert!(!spend::valid(&pp, &ip, &bad, Mode::Specification, &mut rng));
    let mut bad = t.wire_encode();
    bad.push(0);
    assert!(Token::wire_decode(&pp, &bad).is_err());
}
#[test]
fn double_use_and_double_allocation_full_judge() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202026);
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let mut a = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
    let t1 = token(&pp, &ip, &mut a, &[0], b"ctx1", &mut rng);
    let t2 = token(&pp, &ip, &mut a, &[0], b"ctx2", &mut rng);
    assert_eq!(
        spend::judge(&pp, &ip, &t1, 0, &t2, 0, Mode::Specification, &mut rng),
        Some((spend::Responsibility::DoubleUse, G1::generator() * a.ska))
    );
    // Model a malicious allocator explicitly at the raw, crate-only layer.
    let mut b = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
    let t3 = token(&pp, &ip, &mut b, &[0], b"ctx3", &mut rng);
    assert_eq!(
        spend::judge(&pp, &ip, &t1, 0, &t3, 0, Mode::Randomized, &mut rng),
        Some((spend::Responsibility::DoubleAlloc, G1::generator() * w.sku))
    );
    assert!(spend::judge(&pp, &ip, &t1, 0, &t1, 0, Mode::Specification, &mut rng).is_none());
}
#[cfg(feature = "op-counts")]
#[test]
fn native_valid_and_judge_pairing_counts_match_protocol() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202027);
    let mut w = wallet(&pp, &ip, &sk, 1, &mut rng);
    ops::reset();
    let mut h = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
    assert_eq!(ops::stop().final_exponentiations, 0);
    let a = token(&pp, &ip, &mut h, &[0], b"ctx1", &mut rng);
    let b = token(&pp, &ip, &mut h, &[0], b"ctx2", &mut rng);
    ops::reset();
    assert!(spend::valid(&pp, &ip, &a, Mode::Specification, &mut rng));
    let c = ops::stop();
    assert_eq!((c.miller_loop_terms, c.final_exponentiations), (36, 14));
    ops::reset();
    assert!(spend::valid(&pp, &ip, &a, Mode::Randomized, &mut rng));
    let c = ops::stop();
    assert_eq!(c.final_exponentiations, 1);
    assert!(c.miller_loop_terms <= 36);
    ops::reset();
    assert!(spend::judge(&pp, &ip, &a, 0, &b, 0, Mode::Specification, &mut rng).is_some());
    let c = ops::stop();
    assert_eq!((c.miller_loop_terms, c.final_exponentiations), (72, 28));
}

#[test]
fn nine_capacity_configurations_and_six_attribute_schemas_are_valid() {
    let mut rng = StdRng::seed_from_u64(202028);
    for n in [256, 1024, 4096] {
        for s in [16, 64, 256] {
            let pp = PublicParameters::setup(n, s, 64, 6, 4, b"sweep", &mut rng).unwrap();
            let (ip, sk) = keygen(&pp, &mut rng).unwrap();
            install(&pp, &ip).unwrap();
            let mut w = wallet(&pp, &ip, &sk, 1, &mut rng);
            let gamma: Vec<_> = (0..pp.w.min(4)).collect();
            let mut h = self_derive(&pp, &mut w, &gamma, &mut rng).unwrap();
            let t = token(&pp, &ip, &mut h, &[0, 1, 2], b"sweep", &mut rng);
            assert!(
                spend::valid(&pp, &ip, &t, Mode::Specification, &mut rng),
                "N={n},s={s}"
            );
        }
    }
    for attrs in [5, 10, 15, 20, 25, 30] {
        let del = attrs * 3 / 5;
        let prv = attrs - del;
        let pp = PublicParameters::setup(1024, 16, 64, del, prv, b"attrs", &mut rng).unwrap();
        let (ip, sk) = keygen(&pp, &mut rng).unwrap();
        let mut mdel: Vec<_> = (0..del).map(|i| S::from(20 + i as u64)).collect();
        mdel[0] = S::ONE;
        let mprv = vec![S::from(7); prv];
        let (q, sec) = prepare_request(&pp, &ip, S::from(91), &mdel, &mprv, &mut rng).unwrap();
        let res = issue(&pp, &ip, &sk, &q, 0, &mut rng).unwrap();
        let mut w = accept(&pp, &ip, &q, &sec, &res, &mut rng).unwrap();
        let mut h = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
        let t = token(&pp, &ip, &mut h, &[0], b"attrs", &mut rng);
        assert!(
            spend::valid(&pp, &ip, &t, Mode::Randomized, &mut rng),
            "attrs={attrs}"
        );
    }
}
#[test]
fn actual_multi_block_requests_and_two_self_children() {
    use super::state::{split_requests, Position};
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202029);
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let mut h = self_derive(&pp, &mut w, &[0, 1, 2, 3, 4, 5, 6, 7], &mut rng).unwrap();
    for count in [96, 128] {
        let positions = (0..count)
            .map(|j| Position {
                pool: j / pp.s,
                offset: j % pp.s,
            })
            .collect();
        let chunks = split_requests(vec![([1; 32], positions)], pp.k_max).unwrap();
        assert_eq!(chunks.len(), 2);
        let mut serials = BTreeSet::new();
        for c in chunks {
            let pos: Vec<_> = c
                .positions
                .iter()
                .map(|p| p.pool * pp.s + p.offset)
                .collect();
            let t = token(&pp, &ip, &mut h, &pos, b"multi-block", &mut rng);
            assert!(spend::valid(&pp, &ip, &t, Mode::Randomized, &mut rng));
            for s in t.serials() {
                assert!(serials.insert(s));
            }
        }
        assert_eq!(serials.len(), count);
    }
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let mut a = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
    let mut b = self_derive(&pp, &mut w, &[1], &mut rng).unwrap();
    let chunks = split_requests(
        vec![
            ([1; 32], vec![Position { pool: 0, offset: 0 }]),
            ([2; 32], vec![Position { pool: 1, offset: 0 }]),
        ],
        64,
    )
    .unwrap();
    assert_eq!(chunks.len(), 2);
    for (h, p) in [(&mut a, 0), (&mut b, 16)] {
        let t = token(&pp, &ip, h, &[p], b"two-self", &mut rng);
        assert_eq!(t.units.len(), 1);
        assert!(spend::valid(&pp, &ip, &t, Mode::Specification, &mut rng));
    }
}

#[test]
fn malformed_typed_owner_and_non_subgroup_token_are_rejected() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202030);
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let mut h = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
    let t = token(&pp, &ip, &mut h, &[0], b"subgroup", &mut rng);
    let non_subgroup = (1u64..256)
        .find_map(|i| {
            let mut bytes = [0u8; 48];
            bytes[0] = 0x80;
            bytes[40..].copy_from_slice(&i.to_be_bytes());
            let p = Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed_unchecked(
                &bytes,
            ))?;
            (!bool::from(p.is_torsion_free())).then_some(G1::from(p))
        })
        .expect("non-subgroup curve point fixture");
    let mut bad = t.clone();
    bad.units[0].sn = non_subgroup;
    assert!(!spend::valid(&pp, &ip, &bad, Mode::Randomized, &mut rng));
    assert!(Token::wire_decode(&pp, &bad.wire_encode()).is_err());
    h.owner.as_mut().unwrap().mprv.clear();
    let p = Policy {
        period: 1,
        atoms: vec![Atom::Equal(0, S::ONE), Atom::Range(pp.k_del, 0, 255)],
    };
    assert!(spend::prepare_spend(&pp, &ip, &mut h, &[1], &p, &mut rng).is_err());
}
#[test]
fn recipient_proof_requires_no_parent_or_wallet() {
    let (pp, ip, _) = instance();
    let context = super::context::ProtocolContext::new(pp.clone(), Arc::new(ip)).unwrap();
    let mut a = StdRng::seed_from_u64(1);
    let mut b = StdRng::seed_from_u64(1);
    let x = context
        .delegation_request(b"sid", S::from(41), &mut a)
        .unwrap();
    let y = context
        .delegation_request(b"sid", S::from(41), &mut b)
        .unwrap();
    assert_eq!(x.encode(), y.encode());
}

#[test]
fn across_token_batch_keeps_individual_proofs_and_rejects_repeated_units() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(207_021);
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let mut h = self_derive(&pp, &mut w, &[0, 1, 2, 3, 4, 5, 6, 7], &mut rng).unwrap();
    let a = token(&pp, &ip, &mut h, &[0], b"same-merchant", &mut rng);
    let b = token(&pp, &ip, &mut h, &[1], b"same-merchant", &mut rng);
    let good = vec![a.clone(), b.clone()];
    for mode in [Mode::Specification, Mode::Randomized] {
        assert!(spend::valid_many(&pp, &ip, &good, mode, &mut rng));
        assert!(!spend::valid_many(&pp, &ip, &[], mode, &mut rng));
        assert!(!spend::valid_many(
            &pp,
            &ip,
            &[a.clone(), a.clone()],
            mode,
            &mut rng
        ));
        let mut bad = good.clone();
        bad[1].proof.z[0] += S::ONE;
        assert!(!spend::valid_many(&pp, &ip, &bad, mode, &mut rng));
        let mut bad = good.clone();
        bad[1].context.push(1);
        assert!(!spend::valid_many(&pp, &ip, &bad, mode, &mut rng));
        let mut bad = good.clone();
        bad[1].lookups[0].v_1 += S::ONE;
        assert!(!spend::valid_many(&pp, &ip, &bad, mode, &mut rng));
    }
    #[cfg(feature = "op-counts")]
    {
        ops::reset();
        assert!(spend::valid_many_installed(
            &pp,
            &ip,
            &good,
            Mode::Randomized,
            &mut rng
        ));
        let c = ops::stop();
        assert_eq!(c.pairing_input_terms, 72);
        assert_eq!(c.final_exponentiations, 1);
        ops::reset();
        assert!(spend::valid_many_installed(
            &pp,
            &ip,
            &good,
            Mode::Specification,
            &mut rng
        ));
        let c = ops::stop();
        assert_eq!(c.pairing_input_terms, 72);
        assert_eq!(c.final_exponentiations, 28);
    }
}

#[test]
fn accepted_credentials_and_caches_reject_a_different_parameter_instance() {
    let (pp, ip, sk) = instance();
    let mut rng = StdRng::seed_from_u64(202032);
    let mut w = wallet(&pp, &ip, &sk, 0, &mut rng);
    let mut h = self_derive(&pp, &mut w, &[0], &mut rng).unwrap();
    let other = PublicParameters::setup(1024, 16, 64, 6, 4, b"different-period", &mut rng).unwrap();
    assert!(w.parent_opening(&other, 0).is_err());
    assert!(h.scope_opening(&other, 0).is_err());
    assert!(spend::prepare_spend(&other, &ip, &mut h, &[0], &policy(), &mut rng).is_err());
}
