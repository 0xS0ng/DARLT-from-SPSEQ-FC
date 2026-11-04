use baseline_core::{arithmetic::*, klo26 as c};
use group::Group;
use rand::{rngs::StdRng, SeedableRng};
use std::collections::BTreeSet;
fn fixture() -> (c::Issuer, c::ValidatedKey, c::Wallet, StdRng) {
    let mut r = StdRng::seed_from_u64(804);
    let i = c::keygen(&mut r);
    let k = c::validate_key(&i.pk).unwrap();
    let (q, p) = c::request(&k, b"md", &mut r);
    let d = c::issue(&i, &q, b"md", 1, &mut r).unwrap();
    let w = c::receive(p, &d).unwrap();
    (i, k, w, r)
}
#[test]
fn honest_counts_codec_and_receive_guard_cached_for_preparation() {
    let (i, k, w, mut r) = fixture();
    let tag = vec![31; 32];
    let policy = c::Policy {
        allowed: BTreeSet::from([tag.clone()]),
    };
    for _ in 0..2 {
        start_counts();
        let p = c::prepare(&k, &w, &mut r).unwrap();
        let a = stop_counts();
        assert_eq!((a.e1, a.e2, a.p + a.mp_terms), (6, 1, 0));
        start_counts();
        let t = c::show_online(p, &tag).unwrap();
        let b = stop_counts();
        assert_eq!((b.e1, b.e2, b.p + b.mp_terms, b.h1), (2, 0, 0, 1));
        start_counts();
        assert!(c::verify(&k, &policy, b"md", &t));
        let v = stop_counts();
        assert_eq!((v.e1, v.p + v.mp_terms, v.h1), (1, 7, 1));
        assert_eq!(v.msm_sizes, vec![2, 2]);
        assert_eq!(c::read_bit(&i, &k, &policy, b"md", &t), Ok(1));
        let bytes = t.encode();
        assert_eq!(c::Token::decode(&bytes).unwrap().encode(), bytes);
        for n in 0..bytes.len() {
            assert!(c::Token::decode(&bytes[..n]).is_err())
        }
    }
}
#[test]
fn shared_secret_context_policy_metadata_and_signature_mutations_reject() {
    let (_, k, w, mut r) = fixture();
    let tag = vec![31; 32];
    let policy = c::Policy {
        allowed: BTreeSet::from([tag.clone()]),
    };
    let t = c::show(&k, &w, &tag, &mut r).unwrap();
    assert!(!c::verify(&k, &policy, b"wrong", &t));
    assert!(!c::verify(
        &k,
        &c::Policy {
            allowed: BTreeSet::new()
        },
        b"md",
        &t
    ));
    for j in 0..8 {
        let mut b = t.clone();
        match j {
            0 => b.delta += G1::generator(),
            1 => b.tag[0] ^= 1,
            2 => b.pkc += G1::generator(),
            3 => b.x += G1::generator(),
            4 => b.r += G1::generator(),
            5 => b.sig.z += G1::generator(),
            6 => b.proof.c += S::from(1),
            _ => b.proof.z += S::from(1),
        }
        assert!(!c::verify(&k, &policy, b"md", &b), "mutation {j}")
    }
}
#[test]
fn issuer_user_counts_and_wrong_response_binding() {
    let mut r = StdRng::seed_from_u64(806);
    let i = c::keygen(&mut r);
    let k = c::validate_key(&i.pk).unwrap();
    start_counts();
    let (q, p) = c::request(&k, b"md", &mut r);
    let a = stop_counts();
    assert_eq!(a.e1, 2);
    start_counts();
    let d = c::issue(&i, &q, b"md", 1, &mut r).unwrap();
    let b = stop_counts();
    assert_eq!((b.e1, b.e2), (6, 1));
    assert_eq!(b.msm_sizes, vec![2, 2, 2, 2]);
    start_counts();
    let _ = c::receive(p, &d).unwrap();
    let z = stop_counts();
    assert_eq!((z.e1, z.p + z.mp_terms), (2, 7));
    assert_eq!(z.msm_sizes, vec![2, 2, 2, 2]);
    let (_, p) = c::request(&k, b"md", &mut r);
    assert!(c::receive(p, &d).is_err());
}
