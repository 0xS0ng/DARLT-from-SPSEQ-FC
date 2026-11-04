use baseline_core::{arithmetic::*, bhn26 as n, klo26 as c, sma2rt as s};
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, RngCore, SeedableRng};
use std::collections::BTreeSet;

struct NoCoins;
impl RngCore for NoCoins {
    fn next_u32(&mut self) -> u32 {
        panic!("coins before complete validation")
    }
    fn next_u64(&mut self) -> u64 {
        panic!("coins before complete validation")
    }
    fn fill_bytes(&mut self, _: &mut [u8]) {
        panic!("coins before complete validation")
    }
    fn try_fill_bytes(&mut self, _: &mut [u8]) -> Result<(), rand::Error> {
        panic!("coins before complete validation")
    }
}

#[test]
fn real_backend_msms_match_unfolded_sums_and_have_honest_counts() {
    let p = G1::generator();
    let q = G2::generator();
    let terms1 = [
        (p, S::from(7)),
        (p * S::from(3), S::from(9)),
        (-p, S::from(2)),
        (p, S::ONE),
        (p, S::ZERO),
    ];
    let terms2 = terms1.map(|(g, x)| {
        (
            q * if g == p {
                S::ONE
            } else if g == -p {
                -S::ONE
            } else {
                S::from(3)
            },
            x,
        )
    });
    start_counts();
    let a = sum1(&terms1);
    let b = sum2(&terms2);
    let counts = stop_counts();
    assert_eq!(a, terms1.iter().fold(G1::identity(), |s, (g, x)| s + g * x));
    assert_eq!(b, terms2.iter().fold(G2::identity(), |s, (g, x)| s + g * x));
    assert_eq!((counts.e1, counts.e2), (0, 0));
    assert_eq!(counts.msm_sizes, vec![2]);
    assert_eq!(counts.msm2_sizes, vec![2]);
    start_counts();
    assert_eq!(sum1(&[]), G1::identity());
    assert_eq!(sum2(&[]), G2::identity());
    let empty = stop_counts();
    assert!(empty.msm_sizes.is_empty() && empty.msm2_sizes.is_empty());
}

#[test]
fn niat_native_and_two_random_profiles_keep_complete_tags_and_real_equation_counts() {
    let mut rng = StdRng::seed_from_u64(20720);
    let keys = n::IssuerKeys::generate(&mut rng);
    let installed = keys.install().unwrap();
    let client = n::ClientKeys::generate(&mut rng);
    let tokens: Vec<_> = (0..4)
        .map(|i| {
            let msg = n::issue(
                &installed,
                &keys.secret,
                client.public_key(),
                (i % 2) as u8,
                &mut rng,
            )
            .unwrap();
            n::obtain(&installed, &client, &msg, &mut rng).unwrap()
        })
        .collect();
    let tags: Vec<_> = tokens.iter().map(n::redemption_tag).collect();
    assert_eq!(tags[0].len(), 96);
    assert_eq!(tags.iter().collect::<BTreeSet<_>>().len(), 4);
    for mode in [
        n::RedemptionBatch::OriginalAllOnes,
        n::RedemptionBatch::RandomSecondEquation,
        n::RedemptionBatch::RandomFhs,
        n::RedemptionBatch::RandomFhsCachedAnchor,
    ] {
        start_counts();
        let checked = n::verify_batch_redemption(&installed, &tokens, mode, &mut rng).unwrap();
        let counts = stop_counts();
        assert_eq!(checked.len(), 4);
        assert_eq!(
            (counts.mp_terms, counts.mp_calls),
            match mode {
                n::RedemptionBatch::RandomFhs => (8, 1),
                n::RedemptionBatch::RandomFhsCachedAnchor => (7, 1),
                _ => (14, 5),
            }
        );
        for (i, t) in checked.iter().enumerate() {
            assert_eq!(n::read_bit_extract(&keys.secret, t).unwrap(), (i % 2) as u8);
        }
        let mut bad = tokens.clone();
        bad[1].signature.z += G1::generator();
        assert!(n::verify_batch_redemption(&installed, &bad, mode, &mut rng).is_err());
        let mut bad = tokens.clone();
        bad[1].signature.y2 = G2::identity();
        assert!(n::verify_batch_redemption(&installed, &bad, mode, &mut NoCoins).is_err());
        assert!(n::verify_batch_redemption(&installed, &[], mode, &mut NoCoins).is_err());
        let duplicate = vec![tokens[0].clone(), tokens[0].clone()];
        assert!(n::verify_batch_redemption(&installed, &duplicate, mode, &mut NoCoins).is_err());
    }
    // App.C.3 Eq.(2)'s published all-one check permits opposite errors.
    let mut cancel = tokens.clone();
    cancel[0].signature.y1 += G1::generator();
    cancel[1].signature.y1 -= G1::generator();
    assert!(!n::public_verify(&installed, &cancel[0]));
    assert!(!n::public_verify(&installed, &cancel[1]));
    assert!(n::verify_batch_redemption(
        &installed,
        &cancel,
        n::RedemptionBatch::OriginalAllOnes,
        &mut rng
    )
    .is_ok());
    assert!(n::verify_batch_redemption(
        &installed,
        &cancel,
        n::RedemptionBatch::RandomSecondEquation,
        &mut rng
    )
    .is_err());
    assert!(n::verify_batch_redemption(
        &installed,
        &cancel,
        n::RedemptionBatch::RandomFhs,
        &mut rng
    )
    .is_err());
}

#[test]
fn cpat_independently_issued_units_keep_each_dleq_policy_and_metadata_check() {
    let mut rng = StdRng::seed_from_u64(20730);
    let issuer = c::keygen(&mut rng);
    let key = c::validate_key(&issuer.pk).unwrap();
    let tag = b"same-service-period".to_vec();
    let policy = c::Policy {
        allowed: BTreeSet::from([tag.clone()]),
    };
    let tokens: Vec<_> = (0..4)
        .map(|i| {
            let (req, state) = c::request(&key, b"metadata", &mut rng);
            let response =
                c::issue_installed(&key, &issuer, &req, b"metadata", i % 2, &mut rng).unwrap();
            let wallet = c::receive(state, &response).unwrap();
            c::show(&key, &wallet, &tag, &mut rng).unwrap()
        })
        .collect();
    assert!(tokens
        .iter()
        .all(|t| c::verify(&key, &policy, b"metadata", t)));
    assert_eq!(
        tokens
            .iter()
            .map(|t| enc1(t.delta))
            .collect::<BTreeSet<_>>()
            .len(),
        4
    );
    start_counts();
    assert!(c::verify_random_batch(
        &key,
        &policy,
        b"metadata",
        &tokens,
        &mut rng
    ));
    let counts = stop_counts();
    assert_eq!((counts.mp_terms, counts.mp_calls), (9, 1));
    let installed_md = c::install_metadata(&key, b"metadata");
    start_counts();
    assert!(c::verify_random_batch_metadata(
        &installed_md,
        &policy,
        &tokens,
        &mut rng
    ));
    let optimized = stop_counts();
    assert_eq!((optimized.mp_terms, optimized.mp_calls), (8, 1));
    let wrong = c::install_metadata(&key, b"different");
    assert!(!c::verify_random_batch_metadata(
        &wrong, &policy, &tokens, &mut rng
    ));
    assert!(!c::verify_random_batch_metadata(
        &installed_md,
        &policy,
        &[tokens[0].clone(), tokens[0].clone()],
        &mut NoCoins
    ));
    assert!(!c::verify_random_batch(
        &key,
        &policy,
        b"different",
        &tokens,
        &mut rng
    ));
    assert!(!c::verify_random_batch(
        &key,
        &policy,
        b"metadata",
        &[tokens[0].clone(), tokens[0].clone()],
        &mut NoCoins
    ));
    assert!(c::verify_random(
        &key,
        &policy,
        b"metadata",
        &tokens[0],
        &mut rng
    ));
    let mut bad = tokens.clone();
    bad[2].proof.z += S::ONE;
    assert!(!c::verify_random_batch(
        &key,
        &policy,
        b"metadata",
        &bad,
        &mut NoCoins
    ));
    let mut bad = tokens.clone();
    bad[2].sig.z += G1::generator();
    assert!(!c::verify_random_batch(
        &key,
        &policy,
        b"metadata",
        &bad,
        &mut rng
    ));
    let mut bad = tokens.clone();
    bad[2].tag = b"outside".to_vec();
    assert!(!c::verify_random_batch(
        &key,
        &policy,
        b"metadata",
        &bad,
        &mut NoCoins
    ));
}

#[test]
fn sma_batch_preserves_native_sigma_counter_context_policy_and_signature_checks() {
    let mut rng = StdRng::seed_from_u64(20740);
    let pp = s::setup(10, 1024);
    let issuer = s::ikeygen(&pp, &mut rng);
    let metadata = s::vkeygen(&pp, &mut rng);
    let key = s::ukeygen(&mut rng);
    let installed = s::install_instance(&pp, &issuer, &metadata).unwrap();
    let attrs: Vec<_> = (0..10).map(|i| S::from(101 + i)).collect();
    let policy = s::Policy {
        atoms: vec![s::Atom::Reveal(0, attrs[0])],
    };
    let (wallet, _, _) =
        s::issue(&pp, &issuer, &metadata, &key, &attrs, &policy, 0, &mut rng).unwrap();
    let tokens: Vec<_> = (0..4)
        .map(|i| {
            s::show_installed(&installed, &wallet, i, b"same-context", &policy, &mut rng).unwrap()
        })
        .collect();
    assert!(tokens
        .iter()
        .all(|t| s::verify_installed(&installed, t, b"same-context", &policy)));
    start_counts();
    assert!(s::verify_random_batch_installed(
        &installed,
        &tokens,
        b"same-context",
        &policy,
        &mut rng
    ));
    let counts = stop_counts();
    assert_eq!((counts.mp_terms, counts.mp_calls), (9, 1));
    assert!(!s::verify_random_batch_installed(
        &installed,
        &tokens,
        b"other-context",
        &policy,
        &mut NoCoins
    ));
    assert!(!s::verify_random_batch_installed(
        &installed,
        &[tokens[0].clone(), tokens[0].clone()],
        b"same-context",
        &policy,
        &mut NoCoins
    ));
    assert!(s::verify_random_installed(
        &installed,
        &tokens[0],
        b"same-context",
        &policy,
        &mut rng
    ));
    let mut bad = tokens.clone();
    bad[1].proof.c += S::ONE;
    assert!(!s::verify_random_batch_installed(
        &installed,
        &bad,
        b"same-context",
        &policy,
        &mut NoCoins
    ));
    let mut bad = tokens.clone();
    bad[1].sig.z += G1::generator();
    assert!(!s::verify_random_batch_installed(
        &installed,
        &bad,
        b"same-context",
        &policy,
        &mut NoCoins
    ));
    let mut bad = tokens.clone();
    bad[1].bits[0] = G1::identity();
    assert!(!s::verify_random_batch_installed(
        &installed,
        &bad,
        b"same-context",
        &policy,
        &mut NoCoins
    ));
}
