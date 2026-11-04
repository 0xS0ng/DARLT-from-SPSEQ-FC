use baseline_core::{arithmetic::*, cdm as c, encoding as canonical};
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};

fn fixture(n: usize, target_group: u8) -> (c::Relation, Vec<S>) {
    let w: Vec<S> = (0..n).map(|i| S::from((i + 7) as u64)).collect();
    let bases2: Vec<G2> = (0..n)
        .map(|i| g2_mul(G2::generator(), S::from((i + 2) as u64)))
        .collect();
    if target_group == 0 {
        let target = bases2
            .iter()
            .zip(&w)
            .fold(G2::identity(), |a, (g, s)| g2_add(a, g2_mul(*g, *s)));
        (c::Relation::g2(bases2, target).unwrap(), w)
    } else {
        let bases1: Vec<G1> = (0..n)
            .map(|i| g1_mul(G1::generator(), S::from((i + 2) as u64)))
            .collect();
        let a = g2_mul(G2::generator(), S::from(29));
        let target = pair(
            sum1(
                &bases1
                    .iter()
                    .zip(&w)
                    .map(|(g, s)| (*g, *s))
                    .collect::<Vec<_>>(),
            ),
            a,
        );
        if target_group == 1 {
            let bases = bases1.iter().map(|g| pair(*g, a)).collect();
            (c::Relation::gt(bases, target).unwrap(), w)
        } else {
            (c::Relation::pairing_g1(bases1, a, target).unwrap(), w)
        }
    }
}

#[test]
fn honest_four_moves_all_relations_and_canonical_messages() {
    for kind in 0..3 {
        for n in [1, 2, 7, 12] {
            for seed in 0..4 {
                let (relation, w) = fixture(n, kind);
                assert!(relation.check(&w));
                assert_eq!(c::Relation::decode(&relation.encode()).unwrap(), relation);
                let mut rng = StdRng::seed_from_u64(23000 + seed);
                let (vs, v1) = c::verifier_begin(&relation, &mut rng).unwrap();
                let v1 = c::VFirst::decode(&v1.encode()).unwrap();
                let (ps, p2) = c::prover_begin(&relation, &w, &v1, &mut rng).unwrap();
                let p2 = c::PFirst::decode(&p2.encode()).unwrap();
                let (vs, v3) = c::verifier_challenge(vs, p2.clone(), &mut rng).unwrap();
                let v3 = c::VThird::decode(&v3.encode()).unwrap();
                let p4 = c::prover_respond(ps, v3.clone()).unwrap();
                let p4 = c::PFourth::decode(&p4.encode()).unwrap();
                assert!(c::transcript_valid(&relation, &v1, &p2, &v3, &p4));
                assert!(c::verifier_finish(vs, p4));
            }
        }
    }
}

#[test]
fn malicious_verifier_response_aborts_and_consumes_prover_state() {
    for kind in 0..3 {
        for changed in 0..4 {
            let (relation, w) = fixture(3, kind);
            let mut rng = StdRng::seed_from_u64(23111 + changed);
            let (vs, v1) = c::verifier_begin(&relation, &mut rng).unwrap();
            let (ps, p2) = c::prover_begin(&relation, &w, &v1, &mut rng).unwrap();
            let (_, mut v3) = c::verifier_challenge(vs, p2, &mut rng).unwrap();
            v3.opening_responses[changed as usize] += S::ONE;
            assert!(c::prover_respond(ps, v3).is_err());
        }
    }
}

#[test]
fn opening_challenge_tamper_is_checked_by_prover_before_response() {
    let (relation, w) = fixture(3, 0);
    let mut rng = StdRng::seed_from_u64(23191);
    let (vs, v1) = c::verifier_begin(&relation, &mut rng).unwrap();
    let (ps, mut p2) = c::prover_begin(&relation, &w, &v1, &mut rng).unwrap();
    p2.opening_challenge += S::ONE;
    let (_, v3) = c::verifier_challenge(vs, p2, &mut rng).unwrap();
    assert!(c::prover_respond(ps, v3).is_err());
}

#[test]
fn changing_commitment_or_opening_first_cannot_complete_live_interaction() {
    for changed in 0..2 {
        let (relation, w) = fixture(2, 0);
        let mut rng = StdRng::seed_from_u64(23470 + changed);
        let (vs, mut v1) = c::verifier_begin(&relation, &mut rng).unwrap();
        if changed == 0 {
            if let c::Point::G2(ref mut g) = v1.commitment {
                *g += G2::generator();
            }
        } else {
            if let c::Point::G2(ref mut g) = v1.opening_first {
                *g += G2::generator();
            }
        }
        let (ps, p2) = c::prover_begin(&relation, &w, &v1, &mut rng).unwrap();
        let (_, v3) = c::verifier_challenge(vs, p2, &mut rng).unwrap();
        assert!(c::prover_respond(ps, v3).is_err());
    }
}

#[test]
fn wrong_witness_statement_challenge_and_final_responses_reject() {
    for kind in 0..3 {
        let (relation, w) = fixture(4, kind);
        let mut rng = StdRng::seed_from_u64(23901);
        let (v1, p2, v3, p4) = c::prove(&relation, &w, &mut rng).unwrap();
        let (other, _) = fixture(5, kind);
        assert!(!c::transcript_valid(&other, &v1, &p2, &v3, &p4));
        let same_n_wrong_target = match relation.target() {
            c::Point::G2(g) => c::Relation::g2(
                relation
                    .bases()
                    .iter()
                    .map(|p| match p {
                        c::Point::G2(x) => *x,
                        _ => unreachable!(),
                    })
                    .collect(),
                g + G2::generator(),
            )
            .unwrap(),
            c::Point::GT(g) => {
                let bases: Vec<_> = (0..4)
                    .map(|i| {
                        pair(
                            g1_mul(G1::generator(), S::from((i + 2) as u64)),
                            g2_mul(G2::generator(), S::from(29)),
                        )
                    })
                    .collect();
                c::Relation::gt(bases, g + pair(G1::generator(), G2::generator())).unwrap()
            }
        };
        assert!(!c::transcript_valid(
            &same_n_wrong_target,
            &v1,
            &p2,
            &v3,
            &p4
        ));
        let mut wrong_w = w.clone();
        wrong_w[0] += S::ONE;
        assert!(c::prove(&relation, &wrong_w, &mut rng).is_err());
        let mut wrong_k = v3.clone();
        wrong_k.or_challenge += S::ONE;
        assert!(!c::transcript_valid(&relation, &v1, &p2, &wrong_k, &p4));
        for which in 0..3 {
            let mut last = p4.clone();
            if which == 0 {
                last.true_challenge += S::ONE;
            }
            if which == 1 {
                last.true_responses[2] += S::ONE;
            }
            if which == 2 {
                last.opening_responses[3] += S::ONE;
            }
            assert!(!c::transcript_valid(&relation, &v1, &p2, &v3, &last));
        }
    }
}

#[test]
fn transcript_reproducibility_and_fresh_sessions() {
    let (relation, w) = fixture(3, 0);
    let mut a = StdRng::seed_from_u64(80029);
    let mut b = StdRng::seed_from_u64(80029);
    let (v1, p2, v3, p4) = c::prove(&relation, &w, &mut a).unwrap();
    let (x1, x2, x3, x4) = c::prove(&relation, &w, &mut b).unwrap();
    assert_eq!(
        (v1.clone(), p2.clone(), v3.clone(), p4.clone()),
        (x1, x2, x3, x4)
    );
    let (new1, new2, new3, new4) = c::prove(&relation, &w, &mut a).unwrap();
    assert_ne!(v1, new1);
    assert_ne!(p2, new2);
    assert_ne!(v3, new3);
    assert_ne!(p4, new4);
}

#[test]
fn malformed_and_unbounded_messages_reject() {
    let (relation, w) = fixture(2, 0);
    let mut rng = StdRng::seed_from_u64(24011);
    let (v1, p2, v3, p4) = c::prove(&relation, &w, &mut rng).unwrap();
    let message_bytes = [v1.encode(), p2.encode(), v3.encode(), p4.encode()];
    let parsers: [fn(&[u8]) -> bool; 4] = [
        |b| c::VFirst::decode(b).is_ok(),
        |b| c::PFirst::decode(b).is_ok(),
        |b| c::VThird::decode(b).is_ok(),
        |b| c::PFourth::decode(b).is_ok(),
    ];
    for (bytes, parse) in message_bytes.iter().zip(parsers) {
        assert!(parse(bytes));
        for n in 0..bytes.len() {
            assert!(!parse(&bytes[..n]));
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(!parse(&trailing));
    }
    let mut unbounded = canonical::Writer::new(b"CDM-V3-v1");
    unbounded.u32(u32::MAX);
    assert!(c::VThird::decode(&unbounded.finish()).is_err());
    let noncanonical = canonical::Writer::new(b"CDM-P2-v1");
    let mut bytes = noncanonical.finish();
    bytes.extend([255; 32]);
    bytes.push(0);
    bytes.extend(G2::generator().to_compressed());
    bytes.push(0);
    bytes.extend(G2::generator().to_compressed());
    assert!(c::PFirst::decode(&bytes).is_err());
}

#[test]
fn domain_validation_and_group_mismatch_reject() {
    assert!(c::Relation::g2(vec![], G2::generator()).is_err());
    assert!(c::Relation::g2(vec![G2::identity()], G2::generator()).is_err());
    assert!(
        c::Relation::pairing_g1(vec![G1::generator()], G2::identity(), GT::identity()).is_err()
    );
    assert!(c::Relation::gt(vec![pair(G1::generator(), G2::generator())], GT::default()).is_err());
    assert!(c::Relation::gt(vec![GT::default()], GT::identity()).is_err());
    assert!(
        c::Relation::pairing_g1(vec![G1::generator()], G2::generator(), GT::default()).is_err()
    );
    let (gt_relation, gt_witness) = fixture(2, 1);
    let mut gt_rng = StdRng::seed_from_u64(24117);
    let (_, mut gt_first) = c::verifier_begin(&gt_relation, &mut gt_rng).unwrap();
    gt_first.commitment = c::Point::GT(GT::default());
    assert!(c::prover_begin(&gt_relation, &gt_witness, &gt_first, &mut gt_rng).is_err());
    let (relation, w) = fixture(2, 0);
    let mut rng = StdRng::seed_from_u64(24119);
    let (_, mut v1) = c::verifier_begin(&relation, &mut rng).unwrap();
    v1.commitment = c::Point::GT(pair(G1::generator(), G2::generator()));
    assert!(c::prover_begin(&relation, &w, &v1, &mut rng).is_err());
    let (vs, v1) = c::verifier_begin(&relation, &mut rng).unwrap();
    let (_, mut p2) = c::prover_begin(&relation, &w, &v1, &mut rng).unwrap();
    p2.true_first = c::Point::GT(GT::identity());
    assert!(c::verifier_challenge(vs, p2, &mut rng).is_err());
}

#[test]
fn zero_target_remains_valid_and_pairing_evaluation_agrees() {
    let relation = c::Relation::g2(vec![G2::generator()], G2::identity()).unwrap();
    let mut rng = StdRng::seed_from_u64(24219);
    let (v1, p2, v3, p4) = c::prove(&relation, &[S::ZERO], &mut rng).unwrap();
    assert!(c::transcript_valid(&relation, &v1, &p2, &v3, &p4));
    let (gt, w) = fixture(5, 1);
    let (paired, _) = fixture(5, 2);
    assert_eq!(gt.evaluate(&w).unwrap(), paired.evaluate(&w).unwrap());
}

#[test]
fn pairing_backed_group_work_is_executed_and_counted() {
    let n = 4;
    let (relation, w) = fixture(n, 2);
    let mut rng = StdRng::seed_from_u64(24499);
    canonical::start_counts();
    let (vs, v1) = c::verifier_begin(&relation, &mut rng).unwrap();
    let vfirst = canonical::stop_counts();
    canonical::start_counts();
    let (ps, p2) = c::prover_begin(&relation, &w, &v1, &mut rng).unwrap();
    let pfirst = canonical::stop_counts();
    canonical::start_counts();
    let (vs, v3) = c::verifier_challenge(vs, p2, &mut rng).unwrap();
    let vthird = canonical::stop_counts();
    canonical::start_counts();
    let p4 = c::prover_respond(ps, v3).unwrap();
    let pfourth = canonical::stop_counts();
    canonical::start_counts();
    assert!(c::verifier_finish(vs, p4));
    let vfinish = canonical::stop_counts();
    assert_eq!((vfirst.e1, vfirst.et, vfirst.p), (0, 2, 2));
    assert_eq!((pfirst.e1, pfirst.et, pfirst.p), (0, 2, 2));
    assert_eq!((vthird.e1, vthird.et, vthird.p), (0, 0, 0));
    assert_eq!((pfourth.e1, pfourth.et, pfourth.p), (0, 2, 1));
    assert_eq!((vfinish.e1, vfinish.et, vfinish.p), (0, 3, 2));
    assert_eq!(vfirst.msm_sizes, vec![4, 4]);
    assert_eq!(pfirst.msm_sizes, vec![4, 4]);
    assert_eq!(pfourth.msm_sizes, vec![4]);
    assert_eq!(vfinish.msm_sizes, vec![4, 4]);
    assert_eq!(
        vfirst.hz + pfirst.hz + vthird.hz + pfourth.hz + vfinish.hz,
        0
    );
}
