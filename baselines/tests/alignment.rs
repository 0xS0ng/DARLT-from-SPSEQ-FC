use baseline_core::{
    arithmetic::*,
    encoding, klo26 as cpat,
    msb23::{scheme as msb, wire},
    slw25 as slw,
};
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::json;
use std::collections::BTreeSet;

fn measured<T>(
    scheme: &str,
    phase: &str,
    attributes: usize,
    action: impl FnOnce() -> T,
) -> (T, Counts) {
    encoding::start_counts();
    let result = action();
    let counts = encoding::stop_counts();
    println!(
        "CHECK:{}",
        json!({"scheme":scheme,"phase":phase,"attributes":attributes,
        "timing_enabled":false,"formal_samples":0,"counts":counts})
    );
    (result, counts)
}

fn msb_issue(t: usize, mode: usize) -> (msb::Registered, msb::Credential) {
    let mut rng = StdRng::seed_from_u64(214_230 + t as u64);
    let (pp, issuer) = msb::setup(t, &mut rng).unwrap();
    let registered = msb::register(pp).unwrap();
    let holder = msb::user_keygen(&mut rng);
    let (q, state) = msb::issue_begin(
        &registered,
        &holder,
        (101..101 + t as u64).map(S::from).collect(),
        &mut rng,
    )
    .unwrap();
    let (challenge, verifier) = msb::issue_challenge(&registered, q, &mut rng).unwrap();
    let (answer, state) = msb::issue_respond(state, challenge).unwrap();
    let response = msb::issue_issuer(&registered, &issuer, verifier, answer, &mut rng).unwrap();
    let phase = [
        "obtain_specification",
        "obtain_random_cached_GT",
        "obtain_random_pairing_key",
    ][mode];
    let (credential, count) = measured("MSB+23", phase, t + 1, || match mode {
        0 => msb::issue_finish(&registered, state, response, &mut rng),
        1 => msb::issue_finish_random(&registered, state, response, &mut rng),
        _ => msb::issue_finish_random_pairing_key(&registered, state, response, &mut rng),
    });
    if mode != 0 {
        assert_eq!(count.p + count.mp_calls, 1);
    }
    (registered, credential.unwrap())
}

#[test]
fn msb_obtain_aggregates_all_update_keys_and_known_policy_has_constant_online_group_work() {
    let mut online_shapes = vec![];
    let mut obtain_shapes = vec![];
    for t in [4, 9, 14, 19, 24, 29] {
        msb_issue(t, 0);
        msb_issue(t, 1);
        let (v, credential) = msb_issue(t, 2);
        let disclosed = msb::Disclosure {
            indices: vec![1],
            sets: vec![vec![S::from(101), S::from(102), S::from(103)]],
        };
        let mut old_rng = StdRng::seed_from_u64(214_231);
        let mut new_rng = old_rng.clone();
        let (old_prepared, _) = measured("MSB+23", "before_prepare_policy_late", t + 1, || {
            msb::show_prepare(&v, &credential, &mut old_rng).unwrap()
        });
        let (new_prepared, _) = measured("MSB+23", "after_prepare_policy_known", t + 1, || {
            msb::show_prepare_policy(&v, &credential, disclosed.clone(), &mut new_rng).unwrap()
        });
        let ((old_first, old_prover), _) =
            measured("MSB+23", "before_online_subset_and_context", t + 1, || {
                msb::show_begin_online(&v, old_prepared, disclosed.clone(), vec![42; 32]).unwrap()
            });
        let ((new_first, new_prover), counts) =
            measured("MSB+23", "after_online_context_only", t + 1, || {
                msb::show_begin_prepared(&v, new_prepared, vec![42; 32]).unwrap()
            });
        assert_eq!(
            wire::encode_show_first(&old_first),
            wire::encode_show_first(&new_first)
        );
        online_shapes.push(serde_json::to_value(counts).unwrap());
        let mut a = StdRng::seed_from_u64(214_232);
        let mut b = a.clone();
        let (challenge, old_verifier) =
            msb::show_challenge(&v, old_first, &disclosed, &[42; 32], &mut a).unwrap();
        let (new_challenge, new_verifier) =
            msb::show_challenge(&v, new_first, &disclosed, &[42; 32], &mut b).unwrap();
        let old_answer = msb::show_respond(old_prover, challenge).unwrap();
        let new_answer = msb::show_respond(new_prover, new_challenge).unwrap();
        assert_eq!(old_answer.bytes(), new_answer.bytes());
        assert!(msb::show_verify(&v, old_verifier, old_answer));
        assert!(msb::show_verify(&v, new_verifier, new_answer));
        // Input sizes and subgroup checks remain in Obtain; only physical
        // pairing terms and FE are claimed constant, not the complete cost.
        let mut rng = StdRng::seed_from_u64(214_233);
        let (pp, i) = msb::setup(t, &mut rng).unwrap();
        let installed = msb::register(pp).unwrap();
        let u = msb::user_keygen(&mut rng);
        let (q, s) = msb::issue_begin(
            &installed,
            &u,
            (101..101 + t as u64).map(S::from).collect(),
            &mut rng,
        )
        .unwrap();
        let (ch, vs) = msb::issue_challenge(&installed, q, &mut rng).unwrap();
        let (answer, s) = msb::issue_respond(s, ch).unwrap();
        let response = msb::issue_issuer(&installed, &i, vs, answer, &mut rng).unwrap();
        encoding::start_counts();
        msb::issue_finish_random_pairing_key(&installed, s, response, &mut rng).unwrap();
        let c = encoding::stop_counts();
        obtain_shapes.push((c.p + c.mp_terms, c.p + c.mp_calls));
    }
    assert!(online_shapes.windows(2).all(|w| w[0] == w[1]));
    assert!(obtain_shapes.windows(2).all(|w| w[0] == w[1]));
}

#[test]
fn cpat_accepted_wallet_tag_preparation_and_incremental_read_keep_native_bytes() {
    let mut rng = StdRng::seed_from_u64(214_260);
    let issuer = cpat::keygen(&mut rng);
    let key = cpat::validate_key(&issuer.pk).unwrap();
    for bit in [0, 1] {
        let (req, pending) = cpat::request(&key, b"public-metadata", &mut rng);
        let response = cpat::issue(&issuer, &req, b"public-metadata", bit, &mut rng).unwrap();
        let (wallet, receive) = measured("CPAT", "receive_signature_once", 0, || {
            cpat::receive(pending, &response).unwrap()
        });
        assert_eq!(receive.p + receive.mp_terms, 7);
        let mut a = StdRng::seed_from_u64(214_261);
        let mut b = a.clone();
        let (old_p, old) = measured("CPAT", "before_prepare_revalidates_wallet", 0, || {
            cpat::prepare_revalidated(&key, &wallet, &mut a).unwrap()
        });
        let (new_p, new) = measured("CPAT", "after_prepare_accepted_wallet", 0, || {
            cpat::prepare(&key, &wallet, &mut b).unwrap()
        });
        assert_eq!((old.p + old.mp_terms, new.p + new.mp_terms), (7, 0));
        let tag = vec![31; 32];
        let (old_token, _) = measured("CPAT", "before_online_tag_binding", 0, || {
            cpat::show_online(old_p, &tag).unwrap()
        });
        let (new_token, _) = measured("CPAT", "after_offline_tag_binding", 0, || {
            cpat::show_online(new_p, &tag).unwrap()
        });
        assert_eq!(old_token.encode(), new_token.encode());
        let mut c = StdRng::seed_from_u64(214_261);
        let (ready, _) = measured("CPAT", "after_prepare_complete_redemption", 0, || {
            cpat::prepare_redemption(&key, &wallet, &tag, &mut c).unwrap()
        });
        let (delivered, online) = measured("CPAT", "after_online_present_only", 0, || {
            cpat::present(ready)
        });
        assert_eq!(delivered.encode(), old_token.encode());
        assert_eq!(
            (
                online.e1,
                online.e2,
                online.et,
                online.p + online.mp_terms,
                online.h1
            ),
            (0, 0, 0, 0, 0)
        );
        let policy = cpat::Policy {
            allowed: BTreeSet::from([tag]),
        };
        let record = cpat::verify_record(&key, &policy, b"public-metadata", &delivered).unwrap();
        let (full, _) = measured("CPAT", "native_Read_includes_Verify", 0, || {
            cpat::read_bit(&issuer, &key, &policy, b"public-metadata", &delivered).unwrap()
        });
        let (incremental, read) = measured("CPAT", "Read_one_already_verified_record", 0, || {
            cpat::read_bit_validated(&issuer, &record).unwrap()
        });
        assert_eq!((full, incremental), (bit, bit));
        assert_eq!((read.e1, read.e2, read.p + read.mp_terms), (1, 0, 0));
        let mut damaged = delivered.clone();
        damaged.sig.z += G1::generator();
        assert!(cpat::verify_record(&key, &policy, b"public-metadata", &damaged).is_err());
        let other = cpat::keygen(&mut rng);
        assert!(cpat::read_bit_validated(&other, &record).is_err());
    }
}

#[test]
fn slw_offline_cdm_keeps_fresh_binding_and_live_opening_checks() {
    for business in [5, 10, 15, 20, 25, 30] {
        let mut rng = StdRng::seed_from_u64(214_250 + business as u64);
        let (pk, sk) = slw::setup(business, &mut rng).unwrap();
        let holder = slw::Holder::generate(&mut rng);
        let attrs = (100..100 + business as u64)
            .map(S::from)
            .collect::<Vec<_>>();
        let (credential, _) = slw::run_issue(&pk, &sk, &holder, &attrs, &mut rng).unwrap();
        let mut a = StdRng::seed_from_u64(214_251);
        let mut b = a.clone();
        let ((mut old_prepared, old_prefix), _) = measured(
            "SLW+25",
            "before_prepare_without_CDM_first",
            business,
            || {
                let mut p = slw::show_precompute(&pk, &holder, &credential, &mut a).unwrap();
                slw::show_bind(&pk, &mut p, &[2, 3, 4]).unwrap()
            },
        );
        let ((mut new_prepared, new_prefix), _) = measured(
            "SLW+25",
            "after_prepare_fixed_CDM_branches",
            business,
            || slw::show_prepare(&pk, &holder, &credential, &[2, 3, 4], &mut b).unwrap(),
        );
        assert_eq!(old_prefix, new_prefix);
        let mut verifier_a = StdRng::seed_from_u64(214_252);
        let mut verifier_b = verifier_a.clone();
        let (va, v1) = slw::show_verifier_begin(&pk, &old_prefix, &mut verifier_a).unwrap();
        let (vb, w1) = slw::show_verifier_begin(&pk, &new_prefix, &mut verifier_b).unwrap();
        assert_eq!(v1, w1);
        let ((pa, p2), before) = measured("SLW+25", "before_online_CDM_first", business, || {
            slw::show_holder_first(&pk, &mut old_prepared, &v1, &mut a).unwrap()
        });
        let ((pb, q2), after) = measured(
            "SLW+25",
            "after_online_fresh_commitment_only",
            business,
            || slw::show_holder_first(&pk, &mut new_prepared, &w1, &mut b).unwrap(),
        );
        assert_eq!(p2, q2);
        assert_eq!(
            (before.p + before.mp_terms, after.p + after.mp_terms),
            (2, 0)
        );
        assert_eq!(after.et, 1);
        assert!(after.msm_sizes.is_empty() && after.msm2_sizes.is_empty());
        let (va, v3) = slw::show_verifier_challenge(va, &p2, &mut verifier_a).unwrap();
        let (vb, w3) = slw::show_verifier_challenge(vb, &q2, &mut verifier_b).unwrap();
        assert_eq!(v3, w3);
        let (p4, before) = measured(
            "SLW+25",
            "before_online_verify_fresh_opening_and_respond",
            business,
            || slw::show_holder_respond(pa, &v3).unwrap(),
        );
        let (q4, after) = measured(
            "SLW+25",
            "after_online_verify_fresh_opening_and_respond",
            business,
            || slw::show_holder_respond(pb, &w3).unwrap(),
        );
        assert_eq!(p4, q4);
        assert_eq!(
            serde_json::to_value(before).unwrap(),
            serde_json::to_value(after).unwrap()
        );
        assert!(slw::show_verifier_finish(va, &p4).unwrap());
        assert!(slw::show_verifier_finish(vb, &q4).unwrap());
    }
}

#[test]
fn prepared_cdm_aborts_before_witness_response_for_invalid_fresh_opening() {
    use baseline_core::cdm;
    let mut rng = StdRng::seed_from_u64(214_253);
    let secret = S::from(9);
    let base = G2::generator();
    let relation = cdm::Relation::g2(vec![base], g2_mul(base, secret)).unwrap();
    let prepared = cdm::prover_prepare(&relation, &[secret], &mut rng).unwrap();
    let (v, v1) = cdm::verifier_begin(&relation, &mut rng).unwrap();
    let (p, p2) = cdm::prover_bind(prepared, &v1).unwrap();
    let (_, mut v3) = cdm::verifier_challenge(v, p2, &mut rng).unwrap();
    v3.opening_responses[0] += S::ONE;
    assert!(cdm::prover_respond(p, v3).is_err());
}

#[test]
fn slw_partial_credential_keeps_attribute_dependent_opening_check_online() {
    for business in [5, 10, 15, 20, 25, 30] {
        let mut rng = StdRng::seed_from_u64(214_254 + business as u64);
        let (pk, sk) = slw::setup(business, &mut rng).unwrap();
        let holder = slw::Holder::generate(&mut rng);
        let recipient = slw::Holder::generate(&mut rng);
        let attrs = (100..100 + business as u64)
            .map(S::from)
            .collect::<Vec<_>>();
        let (parent, _) = slw::run_issue(&pk, &sk, &holder, &attrs, &mut rng).unwrap();
        let (child, _) = slw::run_delegate(
            &pk,
            &holder,
            &recipient,
            &parent,
            &(2..business + 2).collect::<Vec<_>>(),
            &mut rng,
        )
        .unwrap();
        let mut a = StdRng::seed_from_u64(214_255);
        let mut b = a.clone();
        let ((mut old_prepared, old_prefix), _) = measured(
            "SLW+25",
            "before_partial_prepare_without_CDM_first",
            business,
            || {
                let mut p = slw::show_precompute(&pk, &recipient, &child, &mut a).unwrap();
                slw::show_bind(&pk, &mut p, &[2, 3, 4]).unwrap()
            },
        );
        let ((mut new_prepared, new_prefix), _) = measured(
            "SLW+25",
            "after_partial_prepare_fixed_CDM_branches",
            business,
            || slw::show_prepare(&pk, &recipient, &child, &[2, 3, 4], &mut b).unwrap(),
        );
        assert_eq!(old_prefix, new_prefix);
        let mut va_rng = StdRng::seed_from_u64(214_256);
        let mut vb_rng = va_rng.clone();
        let (va, v1) = slw::show_verifier_begin(&pk, &old_prefix, &mut va_rng).unwrap();
        let (vb, w1) = slw::show_verifier_begin(&pk, &new_prefix, &mut vb_rng).unwrap();
        let ((pa, p2), before) = measured(
            "SLW+25",
            "before_partial_online_CDM_first",
            business,
            || slw::show_holder_first(&pk, &mut old_prepared, &v1, &mut a).unwrap(),
        );
        let ((pb, q2), after) = measured(
            "SLW+25",
            "after_partial_online_fresh_commitment_only",
            business,
            || slw::show_holder_first(&pk, &mut new_prepared, &w1, &mut b).unwrap(),
        );
        assert_eq!(p2, q2);
        assert_eq!(
            (before.p + before.mp_terms, after.p + after.mp_terms),
            (2, 0)
        );
        assert_eq!(after.et, 1);
        assert!(after.msm_sizes.is_empty() && after.msm2_sizes.is_empty());
        let (va, v3) = slw::show_verifier_challenge(va, &p2, &mut va_rng).unwrap();
        let (vb, w3) = slw::show_verifier_challenge(vb, &q2, &mut vb_rng).unwrap();
        let (p4, before) = measured(
            "SLW+25",
            "before_partial_online_verify_fresh_opening_and_respond",
            business,
            || slw::show_holder_respond(pa, &v3).unwrap(),
        );
        let (q4, after) = measured(
            "SLW+25",
            "after_partial_online_verify_fresh_opening_and_respond",
            business,
            || slw::show_holder_respond(pb, &w3).unwrap(),
        );
        assert_eq!(p4, q4);
        assert_eq!(
            serde_json::to_value(&before).unwrap(),
            serde_json::to_value(&after).unwrap()
        );
        assert_eq!(after.msm_sizes, vec![business - 1]);
        assert_eq!(after.p, 1);
        assert!(slw::show_verifier_finish(va, &p4).unwrap());
        assert!(slw::show_verifier_finish(vb, &q4).unwrap());
    }
}

#[test]
fn msb_known_policy_also_retains_delegated_period_witness_and_context_binding() {
    let (v, parent) = msb_issue(9, 2);
    let mut rng = StdRng::seed_from_u64(214_234);
    let agent = msb::user_keygen(&mut rng);
    let (q, s) = msb::delegate_begin(&v, &agent, vec![msb::period_attribute()], &mut rng).unwrap();
    let delivery = msb::delegate_sender(&v, &parent, q, &mut rng).unwrap();
    let child = msb::delegate_finish(&v, s, delivery, &mut rng).unwrap();
    let d = msb::Disclosure {
        indices: vec![1, 2],
        sets: vec![
            vec![S::from(101), S::from(102)],
            vec![msb::period_attribute()],
        ],
    };
    let mut a = StdRng::seed_from_u64(214_235);
    let mut b = a.clone();
    let p = msb::show_prepare(&v, &child, &mut a).unwrap();
    let q = msb::show_prepare_policy(&v, &child, d.clone(), &mut b).unwrap();
    let ((old, _), _) = measured(
        "MSB+23",
        "before_child_online_subset_and_context",
        10,
        || msb::show_begin_online(&v, p, d.clone(), vec![42; 32]).unwrap(),
    );
    let ((new, ps), after) = measured("MSB+23", "after_child_online_context_only", 10, || {
        msb::show_begin_prepared(&v, q, vec![42; 32]).unwrap()
    });
    assert_eq!(wire::encode_show_first(&old), wire::encode_show_first(&new));
    assert_eq!((after.e1, after.e2, after.p + after.mp_terms), (1, 0, 0));
    assert!(msb::show_challenge(&v, new.clone(), &d, &[43; 32], &mut rng).is_err());
    let (ch, vs) = msb::show_challenge(&v, new, &d, &[42; 32], &mut rng).unwrap();
    let answer = msb::show_respond(ps, ch).unwrap();
    assert!(msb::show_verify(&v, vs, answer));
}

#[test]
fn existing_metadata_read_endpoints_are_incremental_on_one_accepted_record() {
    use baseline_core::{bhn26 as niat, hintoken as hin, sma2rt as sma};
    let mut rng = StdRng::seed_from_u64(214_500);
    let pp = sma::setup(10, 1024);
    let issuer = sma::ikeygen(&pp, &mut rng);
    let reader = sma::vkeygen(&pp, &mut rng);
    let user = sma::ukeygen(&mut rng);
    let installed = sma::install_instance(&pp, &issuer, &reader).unwrap();
    let attrs = vec![
        S::ONE,
        S::from(21),
        S::from(22),
        S::from(23),
        S::from(24),
        S::from(25),
        S::from(7),
        S::from(8),
        S::from(9),
        S::from(10),
    ];
    let policy = sma::Policy {
        atoms: (0..3).map(|i| sma::Atom::Reveal(i, attrs[i])).collect(),
    };
    for bit in [0, 1] {
        let (wallet, _, _) =
            sma::issue(&pp, &issuer, &reader, &user, &attrs, &policy, bit, &mut rng).unwrap();
        let token =
            sma::show_installed(&installed, &wallet, 0, &[42; 32], &policy, &mut rng).unwrap();
        assert!(sma::verify_installed(
            &installed, &token, &[42; 32], &policy
        ));
        let (before, old) = measured(
            "SMA²RT",
            "before_Read_one_already_verified_record",
            10,
            || sma::recover_metadata(&reader, &token).unwrap(),
        );
        let (after, new) = measured(
            "SMA²RT",
            "after_Read_one_already_verified_record",
            10,
            || sma::recover_metadata(&reader, &token).unwrap(),
        );
        assert_eq!((before, after), (bit, bit));
        assert_eq!(
            serde_json::to_value(old).unwrap(),
            serde_json::to_value(&new).unwrap()
        );
        assert_eq!((new.e1, new.p + new.mp_terms), (bit as u64 + 1, 0));
    }
    let keys = niat::IssuerKeys::generate(&mut rng);
    let installed = keys.install().unwrap();
    let client = niat::ClientKeys::generate(&mut rng);
    for bit in [0, 1] {
        let response =
            niat::issue(&installed, &keys.secret, client.public_key(), bit, &mut rng).unwrap();
        let token = niat::obtain(&installed, &client, &response, &mut rng).unwrap();
        let verified = niat::verify_token(&installed, &token).unwrap();
        let (before, old) = measured("NIAT", "before_Read_one_already_verified_record", 0, || {
            niat::read_bit_extract(&keys.secret, &verified).unwrap()
        });
        let (after, new) = measured("NIAT", "after_Read_one_already_verified_record", 0, || {
            niat::read_bit_extract(&keys.secret, &verified).unwrap()
        });
        assert_eq!((before, after), (bit, bit));
        assert_eq!(
            serde_json::to_value(old).unwrap(),
            serde_json::to_value(&new).unwrap()
        );
        assert_eq!((new.e1, new.p + new.mp_terms), (bit as u64 + 1, 0));
        let (full, _) = measured("NIAT", "native_Read_includes_Verify", 0, || {
            niat::read_bit_total(&installed, &keys.secret, &token).unwrap()
        });
        assert_eq!(full, bit);
    }
    let (public, secret) = hin::issuer_keygen(&mut rng);
    let installed = public.install().unwrap();
    let (reader, reader_secret) = hin::reader_keygen(&mut rng);
    for bit in [0, 1] {
        let (req, pending) = hin::request(&reader, &mut rng).unwrap();
        let response = hin::issue(&secret, &reader, &req, bit, &mut rng).unwrap();
        let token = hin::receive(pending, &response, &mut rng).unwrap();
        assert!(hin::verify(
            &installed,
            &token,
            hin::VerificationMode::Specification,
            &mut rng
        ));
        let (before, old) = measured(
            "HinToken",
            "before_Read_one_already_verified_record",
            0,
            || hin::read_bit(&reader_secret, &token).unwrap(),
        );
        let (after, new) = measured(
            "HinToken",
            "after_Read_one_already_verified_record",
            0,
            || hin::read_bit(&reader_secret, &token).unwrap(),
        );
        assert_eq!((before, after), (bit, bit));
        assert_eq!(
            serde_json::to_value(old).unwrap(),
            serde_json::to_value(&new).unwrap()
        );
        assert_eq!((new.e1, new.e2, new.p + new.mp_terms), (0, 0, 0));
        assert_eq!(new.msm_sizes, vec![1]);
        let (full, _) = measured("HinToken", "native_Read_includes_Verify", 0, || {
            hin::read_total(
                &reader_secret,
                &installed,
                &token,
                hin::VerificationMode::Specification,
                &mut rng,
            )
            .unwrap()
        });
        assert_eq!(full, bit);
    }
}

#[test]
fn sma_known_policy_moves_only_fixed_attribute_factors_without_changing_transcript() {
    use baseline_core::sma2rt as sma;
    for attributes in [5, 10, 15, 20, 25, 30] {
        let mut rng = StdRng::seed_from_u64(214_510 + attributes as u64);
        let pp = sma::setup(attributes, 1024);
        let issuer = sma::ikeygen(&pp, &mut rng);
        let reader = sma::vkeygen(&pp, &mut rng);
        let user = sma::ukeygen(&mut rng);
        let installed = sma::install_instance(&pp, &issuer, &reader).unwrap();
        let attrs = (1..=attributes as u64).map(S::from).collect::<Vec<_>>();
        let policy = sma::Policy {
            atoms: (0..3).map(|i| sma::Atom::Reveal(i, attrs[i])).collect(),
        };
        let (wallet, _, _) =
            sma::issue(&pp, &issuer, &reader, &user, &attrs, &policy, 1, &mut rng).unwrap();
        let mut a = StdRng::seed_from_u64(214_511);
        let mut b = a.clone();
        let (old_prepared, old_offline) =
            measured("SMA²RT", "before_prepare_policy_late", attributes, || {
                sma::precompute_installed(&installed, &wallet, 0, &mut a).unwrap()
            });
        let (new_prepared, new_offline) =
            measured("SMA²RT", "after_prepare_policy_known", attributes, || {
                sma::precompute_policy_installed(&installed, &wallet, 0, &policy, &mut b).unwrap()
            });
        let (old_token, old) = measured(
            "SMA²RT",
            "before_online_fixed_attribute_factors_and_context",
            attributes,
            || sma::show_online_installed(&installed, old_prepared, &[42; 32], &policy).unwrap(),
        );
        let (new_token, new) = measured("SMA²RT", "after_online_context_only", attributes, || {
            sma::show_online_installed(&installed, new_prepared, &[42; 32], &policy).unwrap()
        });
        assert_eq!(old_token.bytes(), new_token.bytes());
        assert!(sma::verify_installed(
            &installed, &new_token, &[42; 32], &policy
        ));
        assert_eq!(new_offline.mul1, old_offline.mul1 + (attributes - 3) as u64);
        assert_eq!((old.mul1, new.mul1), ((attributes - 2) as u64, 1));
        assert_eq!(
            (old.e1, new.e1, old.p + old.mp_terms, new.p + new.mp_terms),
            (2, 2, 0, 0)
        );
        let changed = sma::Policy {
            atoms: vec![
                sma::Atom::Reveal(0, attrs[0]),
                sma::Atom::Reveal(3, attrs[3]),
            ],
        };
        let p =
            sma::precompute_policy_installed(&installed, &wallet, 0, &policy, &mut rng).unwrap();
        assert!(sma::show_online_installed(&installed, p, &[42; 32], &changed).is_err());
    }
}
