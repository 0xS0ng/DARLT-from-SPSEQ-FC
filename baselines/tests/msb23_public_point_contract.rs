use baseline_core::arithmetic::*;
use baseline_core::msb23::{pok as p, scheme as s, set_commit as sc, wire as w};
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};

fn business(t: usize) -> Vec<S> {
    (101..101 + t as u64).map(S::from).collect()
}
fn disclosure(child: bool) -> s::Disclosure {
    if child {
        s::Disclosure {
            indices: vec![1, 2],
            sets: vec![
                vec![S::from(101), S::from(102)],
                vec![s::period_attribute()],
            ],
        }
    } else {
        s::Disclosure {
            indices: vec![1],
            sets: vec![vec![S::from(101), S::from(102), S::from(103)]],
        }
    }
}
fn fixture() -> (s::Registered, s::Credential, s::Credential, StdRng) {
    let mut r = StdRng::seed_from_u64(0x007101);
    let (pp, i) = s::setup(9, &mut r).unwrap();
    let v = s::register(pp).unwrap();
    let u = s::user_keygen(&mut r);
    let a = s::user_keygen(&mut r);
    let (q, x) = s::issue_begin(&v, &u, business(9), &mut r).unwrap();
    let (c, y) = s::issue_challenge(&v, q, &mut r).unwrap();
    let (z, x) = s::issue_respond(x, c).unwrap();
    let d = s::issue_issuer(&v, &i, y, z, &mut r).unwrap();
    let root = s::issue_finish(&v, x, d, &mut r).unwrap();
    let (q, x) = s::delegate_begin(&v, &a, vec![s::period_attribute()], &mut r).unwrap();
    let d = s::delegate_sender(&v, &root, q, &mut r).unwrap();
    let child = s::delegate_finish(&v, x, d, &mut r).unwrap();
    (v, root, child, r)
}
fn alias1(g: G1) -> G1 {
    let mut y = g.y();
    for _ in 0..1000 {
        y += g.z();
        let b = G1::from_raw_unchecked(g.x(), y, g.z());
        if b.to_compressed() == g.to_compressed() && !bool::from(b.is_on_curve()) {
            return b;
        }
    }
    panic!("safe G1 encoding-collision fixture")
}
fn alias2(g: G2) -> G2 {
    let mut y = g.y();
    for _ in 0..1000 {
        y += g.z();
        let b = G2::from_raw_unchecked(g.x(), y, g.z());
        if b.to_compressed() == g.to_compressed() && !bool::from(b.is_on_curve()) {
            return b;
        }
    }
    panic!("safe G2 encoding-collision fixture")
}
// This adversarial point fixture constructs the zero field element from its curve field representation.
#[allow(clippy::eq_op)]
fn torsion1() -> G1 {
    let one = G1::generator().z();
    let b = G1::from_raw_unchecked(one - one, one + one, one);
    assert!(bool::from(b.is_on_curve()));
    assert!(!valid1(b, false));
    b
}
fn torsion2() -> G2 {
    for i in 1u64..1000 {
        let mut b = [0u8; 96];
        b[0] = 0x80;
        b[88..].copy_from_slice(&i.to_be_bytes());
        if let Some(g) = Option::<G2>::from(G2::from_compressed_unchecked(&b)) {
            if bool::from(g.is_on_curve())
                && !bool::from(blstrs::G2Affine::from(g).is_torsion_free())
            {
                return g;
            }
        }
    }
    panic!("safe G2 non-subgroup fixture")
}
fn capture<T>(f: impl FnOnce() -> T, rows: &mut Vec<Vec<u8>>) -> T {
    start_counts();
    let x = f();
    rows.push(serde_json::to_vec(&stop_counts()).unwrap());
    x
}
// Same RNG stream, including challenges and response randomness, exercised
// through the strict raw receiver and immutable canonical-decoding receiver.
fn run(seed: u64, t: usize, checked: bool) -> (Vec<Vec<u8>>, Vec<Vec<u8>>) {
    let mut r = StdRng::seed_from_u64(seed);
    let mut frames = vec![];
    let mut counts = vec![];
    let (pp, i) = s::setup(t, &mut r).unwrap();
    let pb = w::encode_parameters(&pp);
    frames.push(pb.clone());
    let v = if checked {
        s::install_cache(w::decode_parameters_checked(&pb).unwrap()).unwrap()
    } else {
        s::register(pp).unwrap()
    };
    let u = s::user_keygen(&mut r);
    let a = s::user_keygen(&mut r);
    let (q, x) = capture(
        || s::issue_begin(&v, &u, business(t), &mut r).unwrap(),
        &mut counts,
    );
    let b = w::encode_issue_request(&q);
    frames.push(b.clone());
    let (c, y) = if checked {
        let q = w::decode_issue_request_checked(&b).unwrap();
        capture(
            || s::issue_challenge_checked(&v, q, &mut r).unwrap(),
            &mut counts,
        )
    } else {
        capture(|| s::issue_challenge(&v, q, &mut r).unwrap(), &mut counts)
    };
    frames.push(c.bytes());
    let (z, x) = capture(|| s::issue_respond(x, c).unwrap(), &mut counts);
    let zb = z.bytes();
    frames.push(zb.clone());
    let d = if checked {
        let z = p::ReceivedResponse::from_bytes(&zb).unwrap();
        capture(
            || s::issue_issuer_received(&v, &i, y, z, &mut r).unwrap(),
            &mut counts,
        )
    } else {
        capture(
            || s::issue_issuer(&v, &i, y, z, &mut r).unwrap(),
            &mut counts,
        )
    };
    let b = w::encode_issue_delivery(&d);
    frames.push(b.clone());
    let root = if checked {
        let d = w::decode_issue_delivery_checked(&b).unwrap();
        capture(
            || s::issue_finish_checked(&v, x, d, &mut r).unwrap(),
            &mut counts,
        )
    } else {
        capture(|| s::issue_finish(&v, x, d, &mut r).unwrap(), &mut counts)
    };
    frames.push(w::encode_credential(&root));
    let (q, x) = capture(
        || s::delegate_begin(&v, &a, vec![s::period_attribute()], &mut r).unwrap(),
        &mut counts,
    );
    let b = w::encode_delegate_request(&q);
    frames.push(b.clone());
    let d = if checked {
        let q = w::decode_delegate_request_checked(&b).unwrap();
        capture(
            || s::delegate_sender_checked(&v, &root, q, &mut r).unwrap(),
            &mut counts,
        )
    } else {
        capture(
            || s::delegate_sender(&v, &root, q, &mut r).unwrap(),
            &mut counts,
        )
    };
    let b = w::encode_delegate_delivery(&d);
    frames.push(b.clone());
    let child = if checked {
        let d = w::decode_delegate_delivery_checked(&b).unwrap();
        capture(
            || s::delegate_finish_checked(&v, x, d, &mut r).unwrap(),
            &mut counts,
        )
    } else {
        capture(
            || s::delegate_finish(&v, x, d, &mut r).unwrap(),
            &mut counts,
        )
    };
    frames.push(w::encode_credential(&child));
    for cred in [&root, &child] {
        for ctx in [
            vec![1; 32],
            vec![2; 32],
            b"different length context".to_vec(),
        ] {
            let d = disclosure(cred.terminal());
            let prep = capture(|| s::show_prepare(&v, cred, &mut r).unwrap(), &mut counts);
            let (m, x) = capture(
                || s::show_begin_online(&v, prep, d.clone(), ctx.clone()).unwrap(),
                &mut counts,
            );
            let b = w::encode_show_first(&m);
            frames.push(b.clone());
            let (ch, y) = if checked {
                let m = w::decode_show_first_checked(&b).unwrap();
                capture(
                    || s::show_challenge_checked(&v, m, &d, &ctx, &mut r).unwrap(),
                    &mut counts,
                )
            } else {
                capture(
                    || s::show_challenge(&v, m, &d, &ctx, &mut r).unwrap(),
                    &mut counts,
                )
            };
            frames.push(ch.bytes());
            let z = capture(|| s::show_respond(x, ch).unwrap(), &mut counts);
            let b = z.bytes();
            frames.push(b.clone());
            let accepted = if checked {
                let z = p::ReceivedResponse::from_bytes(&b).unwrap();
                capture(|| s::show_verify_received(&v, y, z), &mut counts)
            } else {
                capture(|| s::show_verify(&v, y, z), &mut counts)
            };
            assert!(accepted);
        }
    }
    for cred in [&root, &child] {
        let b = w::encode_credential(cred);
        assert_eq!(
            w::encode_credential(&w::decode_credential(&v, &b).unwrap()),
            b
        );
    }
    (frames, counts)
}
#[test]
fn raw_and_checked_same_tape_bytes_and_all_counters() {
    for t in [4, 9, 29] {
        for seed in [19, 47, 299] {
            let a = run(seed, t, false);
            let b = run(seed, t, true);
            assert_eq!(a, b, "seed {seed} t {t}");
            assert_eq!(a.0.len(), 27);
            assert_eq!(a.1.len(), 38);
        }
    }
}
#[test]
fn parameter_decoding_seals_actual_points_and_registration_equations() {
    let mut r = StdRng::seed_from_u64(0x007100);
    let (pp, _) = s::setup(9, &mut r).unwrap();
    let bytes = w::encode_parameters(&pp);
    start_counts();
    let a = s::register_checked(pp.clone()).unwrap();
    let ca = stop_counts();
    start_counts();
    let b = w::decode_parameters_checked(&bytes).unwrap();
    let cb = stop_counts();
    assert_eq!(
        serde_json::to_vec(&ca).unwrap(),
        serde_json::to_vec(&cb).unwrap()
    );
    let a = s::install_cache(a).unwrap();
    let b = s::install_cache(b).unwrap();
    assert_eq!(a.id(), b.id());
    assert_eq!(
        w::encode_parameters(a.parameters()),
        w::encode_parameters(b.parameters())
    );
    for field in 0..6 {
        for kind in 0..3 {
            let mut bad = pp.clone();
            let g = match field {
                0 => pp.x0,
                1 => pp.sc.srs1[1],
                _ => pp.registration.a1[0],
            };
            let g = if kind == 0 {
                alias1(g)
            } else if kind == 1 {
                torsion1()
            } else {
                G1::identity()
            };
            let h = match field {
                3 => pp.xs[0],
                4 => pp.sc.srs2[1],
                _ => pp.registration.a2[0],
            };
            let h = if kind == 0 {
                alias2(h)
            } else if kind == 1 {
                torsion2()
            } else {
                G2::identity()
            };
            match field {
                0 => bad.x0 = g,
                1 => bad.sc.srs1[1] = g,
                2 => bad.registration.a1[0] = g,
                3 => bad.xs[0] = h,
                4 => bad.sc.srs2[1] = h,
                _ => bad.registration.a2[0] = h,
            };
            assert!(
                s::register_checked(bad.clone()).is_err(),
                "field {field}, kind {kind}"
            );
            // A raw off-curve object with the same bytes encodes a legitimate point;
            // that canonical wire point is intentionally a different ingress value.
            if kind != 0 {
                assert!(w::decode_parameters_checked(&w::encode_parameters(&bad)).is_err());
            }
        }
    }
    let mut bad = pp;
    bad.registration.z[0] += S::ONE;
    assert!(w::decode_parameters_checked(&w::encode_parameters(&bad)).is_err());
}
#[test]
fn unknown_raw_show_points_are_checked_before_the_state_is_sealed() {
    let (v, _, child, mut r) = fixture();
    let d = disclosure(true);
    let ctx = vec![19; 32];
    let (m, _) = s::show_begin(&v, &child, d.clone(), ctx.clone(), &mut r).unwrap();
    for field in 0..10 {
        for kind in 0..3 {
            let mut b = m.clone();
            let g = match field {
                0 => m.sig.z,
                1 => m.sig.y,
                2 => m.sig.t,
                3..=5 => m.cs[field - 3],
                6 => m.nym,
                7 => m.witness,
                _ => m.first.commitment,
            };
            let bad = if kind == 0 {
                alias1(g)
            } else if kind == 1 {
                torsion1()
            } else {
                G1::identity()
            };
            match field {
                0 => b.sig.z = bad,
                1 => b.sig.y = bad,
                2 => b.sig.t = bad,
                3..=5 => b.cs[field - 3] = bad,
                6 => b.nym = bad,
                7 => b.witness = bad,
                8 => b.first.commitment = bad,
                _ => {
                    b.sig.yhat = if kind == 0 {
                        alias2(m.sig.yhat)
                    } else if kind == 1 {
                        torsion2()
                    } else {
                        G2::identity()
                    }
                }
            };
            let allowed = kind == 2 && matches!(field, 0 | 2 | 8);
            assert_eq!(
                s::check_show_first(b).is_ok(),
                allowed,
                "field {field}, kind {kind}"
            );
        }
    }
}
#[test]
fn issue_and_delegate_received_requests_reject_actual_points() {
    let mut r = StdRng::seed_from_u64(0x007102);
    let (pp, _) = s::setup(9, &mut r).unwrap();
    let v = s::register(pp).unwrap();
    let u = s::user_keygen(&mut r);
    let (q, _) = s::issue_begin(&v, &u, business(9), &mut r).unwrap();
    for field in 0..4 {
        for kind in 0..3 {
            let mut b = q.clone();
            let g = match field {
                0 => q.nym,
                1..=2 => q.blinded[field - 1],
                _ => q.first.commitment,
            };
            let bad = if kind == 0 {
                alias1(g)
            } else if kind == 1 {
                torsion1()
            } else {
                G1::identity()
            };
            match field {
                0 => b.nym = bad,
                1..=2 => b.blinded[field - 1] = bad,
                _ => b.first.commitment = bad,
            };
            assert_eq!(s::check_issue_request(b).is_ok(), field == 3 && kind == 2);
        }
    }
    let (v, root, _, mut r) = fixture();
    let u = s::user_keygen(&mut r);
    let (q, _) = s::delegate_begin(&v, &u, vec![s::period_attribute()], &mut r).unwrap();
    for g in [alias1(q.nym), torsion1(), G1::identity()] {
        let mut bad = q.clone();
        bad.nym = g;
        assert!(s::delegate_sender(&v, &root, bad, &mut r).is_err());
    }
}
#[test]
fn orphan_t_is_validated_before_receiver_addition_and_other_delivery_points_reject() {
    let (v, root, _, mut r) = fixture();
    let u = s::user_keygen(&mut r);
    for field in 0..7 {
        for kind in 0..2 {
            let (q, x) = s::delegate_begin(&v, &u, vec![s::period_attribute()], &mut r).unwrap();
            let mut d = s::delegate_sender(&v, &root, q, &mut r).unwrap();
            let g = match field {
                0 => d.orphan.z,
                1 => d.orphan.y,
                2 => d.orphan.t,
                _ => d.cs[(field - 3).min(2)],
            };
            let bad = if kind == 0 { alias1(g) } else { torsion1() };
            match field {
                0 => d.orphan.z = bad,
                1 => d.orphan.y = bad,
                2 => d.orphan.t = bad,
                3..=5 => d.cs[field - 3] = bad,
                _ => {
                    d.orphan.yhat = if kind == 0 {
                        alias2(d.orphan.yhat)
                    } else {
                        torsion2()
                    }
                }
            };
            assert!(
                s::delegate_finish(&v, x, d, &mut r).is_err(),
                "field {field}, kind {kind}"
            );
        }
    }
}
#[test]
fn generic_pok_keeps_strict_unknown_point_validation_and_identity_semantics() {
    let mut r = StdRng::seed_from_u64(0x007103);
    let h = p::commitment_base(b"generic");
    let secret = S::from(13);
    let target = g1_mul(G1::generator(), secret);
    for bad in [alias1(target), torsion1(), G1::identity()] {
        assert!(p::prepare_g1(h, &[bad], &[secret], &mut r).is_err());
    }
    assert!(p::prepare_g1(alias1(h), &[target], &[secret], &mut r).is_err());
    for bad in [alias1(target), torsion1()] {
        assert!(p::challenge(h, &[target], b"s", &p::First { commitment: bad }, &mut r).is_err());
    }
    assert!(p::challenge(
        h,
        &[target],
        b"s",
        &p::First {
            commitment: G1::identity()
        },
        &mut r
    )
    .is_ok());
    let (first, x) = p::start_g1(h, &[target], &[secret], b"s", &mut r).unwrap();
    let (ch, y) = p::challenge(h, &[target], b"s", &first, &mut r).unwrap();
    let mut z = p::respond(x, ch).unwrap();
    z.announcements[0] = alias1(z.announcements[0]);
    assert!(!p::verify(y, &z));
    let z = p::Response {
        announcements: vec![G1::identity()],
        opening: S::ZERO,
        responses: vec![S::ZERO],
    };
    assert!(p::ReceivedResponse::from_bytes(&z.bytes()).is_ok());
}
#[test]
// The test deliberately supplies owned cloned protocol objects to exercise their binding checks.
#[allow(clippy::cloned_ref_to_slice_refs)]
fn generic_set_commit_does_not_trust_foreign_points_or_srs() {
    let mut r = StdRng::seed_from_u64(0x007104);
    let (pp, _) = sc::setup(9, &mut r);
    let full = business(9);
    let sub = vec![full[0], full[1]];
    let rho = S::from(17);
    let c = sc::commit(&pp, &full, rho).unwrap();
    let wit = sc::subset_witness(&pp, c, &full, rho, &sub).unwrap();
    for bad in [alias1(c), torsion1(), G1::identity()] {
        assert!(!sc::open(&pp, bad, &full, rho));
        assert!(sc::aggregate(&pp, &[bad], &[sub.clone()], &[wit]).is_err());
    }
    for bad in [alias1(wit), torsion1(), G1::identity()] {
        assert!(!sc::verify_across(&pp, &[c], &[sub.clone()], bad));
        assert!(sc::aggregate(&pp, &[c], &[sub.clone()], &[bad]).is_err());
    }
    let mut bad = pp.clone();
    bad.srs1[1] = alias1(bad.srs1[1]);
    assert!(!sc::validate_params(&bad));
}
#[test]
fn checked_decoders_reject_noncanonical_torsion_and_trailing_data() {
    let (v, _, child, mut r) = fixture();
    let d = disclosure(true);
    let (m, _) = s::show_begin(&v, &child, d, vec![19; 32], &mut r).unwrap();
    let bytes = w::encode_show_first(&m);
    // Final field is the 48-byte first commitment, so this mutation leaves every
    // framing/disclosure field intact and targets only canonical point parsing.
    for point in [
        enc1(torsion1()),
        {
            let mut x = enc1(m.first.commitment);
            x[0] &= 0x7f;
            x
        },
        vec![0xff; 48],
    ] {
        let mut b = bytes.clone();
        let n = b.len();
        b[n - 48..].copy_from_slice(&point);
        assert!(w::decode_show_first_checked(&b).is_err());
    }
    let mut b = bytes.clone();
    b.push(0);
    assert!(w::decode_show_first_checked(&b).is_err());
    for n in [0, 8, 16, bytes.len() - 1] {
        assert!(w::decode_show_first_checked(&bytes[..n]).is_err());
    }
    let z = p::Response {
        announcements: vec![G1::generator()],
        opening: S::from(3),
        responses: vec![S::from(5)],
    };
    let zb = z.bytes();
    let mut b = zb.clone();
    b[8..56].copy_from_slice(&enc1(torsion1()));
    assert!(p::ReceivedResponse::from_bytes(&b).is_err());
    let mut b = zb;
    b[56..88].fill(0xff);
    assert!(p::ReceivedResponse::from_bytes(&b).is_err());
}
#[test]
fn opaque_holder_decoder_preserves_complete_opening_and_system_validation() {
    let (v, root, child, mut r) = fixture();
    for c in [&root, &child] {
        let bytes = w::encode_credential(c);
        let decoded = w::decode_credential(&v, &bytes).unwrap();
        let d = disclosure(c.terminal());
        let ctx = vec![22; 32];
        let (m, x) = s::show_begin(&v, &decoded, d.clone(), ctx.clone(), &mut r).unwrap();
        let (ch, y) = s::show_challenge(&v, m, &d, &ctx, &mut r).unwrap();
        assert!(s::show_verify(&v, y, s::show_respond(x, ch).unwrap()));
        let mut bad = bytes.clone();
        bad[9..57].copy_from_slice(&enc1(torsion1()));
        assert!(w::decode_credential(&v, &bad).is_err());
        let mut bad = bytes.clone();
        let n = bad.len();
        bad[n - 1] ^= 1;
        assert!(w::decode_credential(&v, &bad).is_err());
    }
    let (pp, _) = s::setup(9, &mut r).unwrap();
    let other = s::register(pp).unwrap();
    assert!(w::decode_credential(&other, &w::encode_credential(&root)).is_err());
}
