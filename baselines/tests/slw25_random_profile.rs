use baseline_core::{arithmetic::*, cdm, slw25 as s};
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, CryptoRng, RngCore, SeedableRng};

struct NoCoins;
impl RngCore for NoCoins {
    fn next_u32(&mut self) -> u32 {
        panic!("coins before complete checks")
    }
    fn next_u64(&mut self) -> u64 {
        panic!("coins before complete checks")
    }
    fn fill_bytes(&mut self, _: &mut [u8]) {
        panic!("coins before complete checks")
    }
    fn try_fill_bytes(&mut self, _: &mut [u8]) -> Result<(), rand::Error> {
        panic!("coins before complete checks")
    }
}
impl CryptoRng for NoCoins {}

fn fixture() -> (
    s::PublicKey,
    s::Holder,
    s::Holder,
    s::Credential,
    s::Credential,
) {
    let mut rng = StdRng::seed_from_u64(212_250);
    let (pk, sk) = s::setup(8, &mut rng).unwrap();
    let user = s::Holder::generate(&mut rng);
    let agent = s::Holder::generate(&mut rng);
    let attrs = (100..108).map(S::from).collect::<Vec<_>>();
    let (parent, _) = s::run_issue(&pk, &sk, &user, &attrs, &mut rng).unwrap();
    let (child, _) =
        s::run_delegate(&pk, &user, &agent, &parent, &[2, 3, 4, 5, 6, 7], &mut rng).unwrap();
    (pk, user, agent, parent, child)
}

#[test]
fn complete_profiles_keep_native_live_interaction_and_exact_wire() {
    let (pk, user, agent, parent, child) = fixture();
    for (holder, cred) in [(&user, &parent), (&agent, &child)] {
        let mut a = StdRng::seed_from_u64(212_251);
        let mut b = a.clone();
        let native = s::run_show(&pk, holder, cred, &[2, 3, 4], &mut a).unwrap();
        let fixed = s::run_show_frozen(
            &pk,
            holder,
            cred,
            &[2, 3, 4],
            s::VerificationMode::Specification,
            &mut b,
        )
        .unwrap();
        assert_eq!(native.messages.as_slice(), fixed.messages());
        assert_eq!(native.bytes(), fixed.bytes());
        assert_eq!(fixed.issuer_id(), pk.issuer_id());
        assert!(fixed
            .verify(s::VerificationMode::Specification, &mut NoCoins)
            .unwrap());
        assert!(fixed
            .verify(s::VerificationMode::Randomized, &mut b)
            .unwrap());
        let mut rng = StdRng::seed_from_u64(212_252);
        let random = s::run_show_frozen(
            &pk,
            holder,
            cred,
            &[2, 3, 4],
            s::VerificationMode::Randomized,
            &mut rng,
        )
        .unwrap();
        assert!(random
            .verify(s::VerificationMode::Specification, &mut NoCoins)
            .unwrap());
        assert!(random
            .verify(s::VerificationMode::Randomized, &mut rng)
            .unwrap());
    }
}

#[test]
fn full_pairing_profile_includes_purge_and_both_cdm_final_equations() {
    let (pk, _user, agent, _parent, child) = fixture();
    for profile in [
        s::VerificationMode::Specification,
        s::VerificationMode::Randomized,
    ] {
        let mut rng = StdRng::seed_from_u64(212_253);
        let mut prepared = s::show_precompute(&pk, &agent, &child, &mut rng).unwrap();
        let (mut prepared, prefix) =
            s::show_bind_profile(&pk, &mut prepared, &[2, 3, 4], profile).unwrap();
        start_counts();
        let (vs, v1) = s::show_verifier_begin_profile(
            &pk,
            &prefix,
            &[2, 3, 4],
            &[S::from(100), S::from(101), S::from(102)],
            profile,
            &mut rng,
        )
        .unwrap();
        let begin = stop_counts();
        let (ps, p2) = s::show_holder_first(&pk, &mut prepared, &v1, &mut rng).unwrap();
        let (vs, v3) = s::show_verifier_challenge_profile(vs, &p2, &mut rng).unwrap();
        let p4 = s::show_holder_respond(ps, &v3).unwrap();
        start_counts();
        assert!(s::show_verifier_finish_profile(vs, &p4, &mut rng).unwrap());
        let finish = stop_counts();
        if profile == s::VerificationMode::Specification {
            assert_eq!((begin.p + begin.mp_terms, begin.p + begin.mp_calls), (6, 6));
            assert_eq!(
                (finish.p + finish.mp_terms, finish.p + finish.mp_calls),
                (2, 2)
            );
        } else {
            assert_eq!((begin.p + begin.mp_terms, begin.p + begin.mp_calls), (6, 4));
            assert_eq!(
                (finish.p + finish.mp_terms, finish.p + finish.mp_calls),
                (1, 1)
            );
        }
    }
}

#[test]
fn fixed_record_batch_rechecks_all_constraints_and_rejects_bad_final_messages() {
    let (pk, _user, agent, _parent, child) = fixture();
    let mut rng = StdRng::seed_from_u64(212_254);
    let fixed = (0..3)
        .map(|_| {
            s::run_show_frozen(
                &pk,
                &agent,
                &child,
                &[2, 3, 4],
                s::VerificationMode::Randomized,
                &mut rng,
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    for profile in [
        s::VerificationMode::Specification,
        s::VerificationMode::Randomized,
    ] {
        assert!(s::verify_frozen_batch(&fixed, profile, &mut rng).unwrap());
        for field in 0..3 {
            let mut last = cdm::PFourth::decode(&fixed[1].messages()[4]).unwrap();
            match field {
                0 => last.true_challenge += S::ONE,
                1 => last.true_responses[0] += S::ONE,
                _ => last.opening_responses[0] += S::ONE,
            }
            let mut bad = fixed.clone();
            bad[1] = bad[1].with_final_message(&last.encode());
            assert!(!s::verify_frozen_batch(&bad, profile, &mut rng).unwrap());
        }
    }
    let mut bad = fixed.clone();
    bad[2] = bad[2].with_final_message(&[0]);
    assert!(s::verify_frozen_batch(&bad, s::VerificationMode::Randomized, &mut NoCoins).is_err());
    assert!(!s::verify_frozen_batch(&[], s::VerificationMode::Randomized, &mut NoCoins).unwrap());
    let mut prep = s::show_precompute(&pk, &agent, &child, &mut rng).unwrap();
    let (_, prefix) =
        s::show_bind_profile(&pk, &mut prep, &[2, 3, 4], s::VerificationMode::Randomized).unwrap();
    assert!(s::show_verifier_begin_profile(
        &pk,
        &prefix,
        &[2, 3, 4],
        &[S::ONE; 3],
        s::VerificationMode::Randomized,
        &mut NoCoins
    )
    .is_err());
}

#[test]
fn original_and_partial_credential_acceptance_checks_all_native_equations() {
    let (pk, user, agent, parent, child) = fixture();
    let mut rng = StdRng::seed_from_u64(212_255);
    for (holder, cred) in [(&user, &parent), (&agent, &child)] {
        let bytes = cred.encode();
        let received = s::receive_expected_profile(
            &pk,
            holder,
            &bytes,
            cred.retained(),
            cred.attributes(),
            s::VerificationMode::Randomized,
            &mut rng,
        )
        .unwrap();
        assert_eq!(received.encode(), bytes);
        assert!(s::receive_expected_profile(
            &pk,
            holder,
            &bytes,
            cred.retained(),
            &[],
            s::VerificationMode::Randomized,
            &mut NoCoins
        )
        .is_err());
        let mut bad = bytes.clone();
        // Original and partial wire codecs both place B immediately after A.
        let b_offset = bad.len()
            - if cred.mode() == s::Mode::Original {
                288
            } else {
                96
            };
        bad[b_offset..b_offset + 96]
            .copy_from_slice(&(G2::generator() * S::from(77)).to_compressed());
        assert!(
            s::receive_profile(&pk, holder, &bad, s::VerificationMode::Randomized, &mut rng)
                .is_err()
        );
    }
}

#[test]
fn cdm_randomization_preserves_nonpairing_relations_and_preflights_lengths() {
    let mut rng = StdRng::seed_from_u64(212_256);
    for paired in [false, true] {
        let witness = [S::from(7), S::from(11)];
        let relation = if paired {
            cdm::Relation::pairing_g1(
                vec![G1::generator(), G1::generator() * S::from(3)],
                G2::generator(),
                pair(G1::generator() * S::from(40), G2::generator()),
            )
            .unwrap()
        } else {
            cdm::Relation::g2(
                vec![G2::generator(), G2::generator() * S::from(3)],
                G2::generator() * S::from(40),
            )
            .unwrap()
        };
        let (vs, v1) = cdm::verifier_begin(&relation, &mut rng).unwrap();
        let (ps, p2) = cdm::prover_begin(&relation, &witness, &v1, &mut rng).unwrap();
        let (vs, v3) = cdm::verifier_challenge(vs, p2, &mut rng).unwrap();
        let p4 = cdm::prover_respond(ps, v3).unwrap();
        if paired {
            assert!(cdm::verifier_finish_profile(
                vs,
                p4,
                s::VerificationMode::Randomized,
                &mut rng
            ));
        } else {
            assert!(cdm::verifier_finish_profile(
                vs,
                p4,
                s::VerificationMode::Randomized,
                &mut NoCoins
            ));
        }
        let (vs, v1) = cdm::verifier_begin(&relation, &mut rng).unwrap();
        let (ps, p2) = cdm::prover_begin(&relation, &witness, &v1, &mut rng).unwrap();
        let (vs, v3) = cdm::verifier_challenge(vs, p2, &mut rng).unwrap();
        let mut p4 = cdm::prover_respond(ps, v3).unwrap();
        p4.opening_responses.pop();
        assert!(!cdm::verifier_finish_profile(
            vs,
            p4,
            s::VerificationMode::Randomized,
            &mut NoCoins
        ));
    }
}

#[test]
fn installed_key_profile_checks_all_cross_group_relations_before_use() {
    let (pk, _, _, _, _) = fixture();
    let mut rng = StdRng::seed_from_u64(212_257);
    let raw = pk.raw();
    let checked =
        s::PublicKey::install_profile(raw, s::VerificationMode::Randomized, &mut rng).unwrap();
    assert_eq!(checked.encode(), pk.encode());
    assert_eq!(
        s::PublicKey::decode_install_profile(
            &pk.encode(),
            s::VerificationMode::Randomized,
            &mut rng
        )
        .unwrap()
        .encode(),
        pk.encode()
    );
    let mut bad = pk.raw();
    bad.yh[0] += G2::generator();
    assert!(s::PublicKey::install_profile(bad, s::VerificationMode::Randomized, &mut rng).is_err());
    let mut bad = pk.raw();
    bad.z[0][1] += G1::generator();
    assert!(
        s::PublicKey::install_profile(bad, s::VerificationMode::Randomized, &mut NoCoins).is_err()
    );
    let mut bad = pk.raw();
    bad.yh.pop();
    assert!(
        s::PublicKey::install_profile(bad, s::VerificationMode::Randomized, &mut NoCoins).is_err()
    );
    assert!(s::PublicKey::decode_install_profile(
        &[0],
        s::VerificationMode::Randomized,
        &mut NoCoins
    )
    .is_err());
}

#[test]
fn issuance_and_delegation_profile_retain_the_native_four_message_proofs() {
    let mut rng = StdRng::seed_from_u64(212_258);
    let (pk, sk) = s::setup(8, &mut rng).unwrap();
    let old = s::Holder::generate(&mut rng);
    let new = s::Holder::generate(&mut rng);
    let attrs = (100..108).map(S::from).collect::<Vec<_>>();
    let mut a = StdRng::seed_from_u64(212_259);
    let mut b = a.clone();
    let (ca, ta) = s::run_issue(&pk, &sk, &old, &attrs, &mut a).unwrap();
    let (cb, tb) = s::run_issue_profile(
        &pk,
        &sk,
        &old,
        &attrs,
        s::VerificationMode::Specification,
        &mut b,
    )
    .unwrap();
    assert_eq!(ca.encode(), cb.encode());
    assert_eq!(ta.messages, tb.messages);
    let (ca, ta) = s::run_delegate(&pk, &old, &new, &ca, &[2, 3, 4, 5, 6, 7], &mut a).unwrap();
    let (cb, tb) = s::run_delegate_profile(
        &pk,
        &old,
        &new,
        &cb,
        &[2, 3, 4, 5, 6, 7],
        s::VerificationMode::Specification,
        &mut b,
    )
    .unwrap();
    assert_eq!(ca.encode(), cb.encode());
    assert_eq!(ta.messages, tb.messages);
    let (parent, _) = s::run_issue_profile(
        &pk,
        &sk,
        &old,
        &attrs,
        s::VerificationMode::Randomized,
        &mut rng,
    )
    .unwrap();
    assert!(s::receive(&pk, &old, &parent.encode()).is_ok());
    let (child, _) = s::run_delegate_profile(
        &pk,
        &old,
        &new,
        &parent,
        &[2, 3, 4, 5, 6, 7],
        s::VerificationMode::Randomized,
        &mut rng,
    )
    .unwrap();
    assert!(s::receive(&pk, &new, &child.encode()).is_ok());
}

#[test]
fn independent_weights_prevent_cancelling_bad_cdm_response_pairs() {
    let mut rng = StdRng::seed_from_u64(212_260);
    let base = G1::generator();
    let second = G2::generator();
    let witness = [S::from(7)];
    let relation =
        cdm::Relation::pairing_g1(vec![base], second, pair(base * S::from(7), second)).unwrap();
    for _ in 0..6 {
        let mut sessions = Vec::new();
        for sign in [S::ONE, -S::ONE] {
            let (vs, v1) = cdm::verifier_begin(&relation, &mut rng).unwrap();
            let (ps, p2) = cdm::prover_begin(&relation, &witness, &v1, &mut rng).unwrap();
            let (vs, v3) = cdm::verifier_challenge(vs, p2, &mut rng).unwrap();
            let mut p4 = cdm::prover_respond(ps, v3).unwrap();
            p4.true_responses[0] += sign;
            sessions.push((vs, p4));
        }
        assert!(!cdm::verifier_finish_many_profile(
            sessions,
            s::VerificationMode::Randomized,
            &mut rng
        ));
    }
}
