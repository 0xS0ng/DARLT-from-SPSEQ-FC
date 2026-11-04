use rand::{rngs::StdRng, SeedableRng};
use rp23_native::{
    api::*,
    backend::{self as b, ScalarCompat, VerificationMode as M},
};
const MERCHANT: [u8; 16] = [7; 16];
fn info(n: u8) -> PayInfo {
    PayInfo::new(MERCHANT, [n; 16])
}
fn nonsubgroup_bytes() -> [u8; 48] {
    (1u64..256)
        .find_map(|i| {
            let mut b = [0; 48];
            b[0] = 0x80;
            b[40..].copy_from_slice(&i.to_be_bytes());
            let p =
                Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed_unchecked(&b))?;
            (!bool::from(p.is_torsion_free())).then_some(b)
        })
        .unwrap()
}

#[test]
fn compact_native_lifecycle_amounts_codecs_and_rejection() {
    let c = Compact::new(80).unwrap();
    let mut rng = StdRng::seed_from_u64(214);
    for k in [1, 16, 64] {
        let w = c.issue().unwrap();
        assert_eq!(w.next_index(), 0);
        let p = c.spend(&w, k, info(k as u8)).unwrap();
        assert_eq!(w.next_index(), k);
        assert_eq!(p.amount(), k);
        let bytes = p.encode();
        let q = CompactPayment::decode(&bytes, p.payinfo, 80).unwrap();
        assert_eq!(q.encode(), bytes);
        assert_eq!(bytes.len(), 409 + 528 * k as usize);
        for m in [M::Specification, M::Randomized] {
            assert!(c.verify(std::slice::from_ref(&q), &MERCHANT, m, &mut rng));
        }
        let ids = c
            .deposit_serials_after_verification(std::slice::from_ref(&q))
            .unwrap();
        assert_eq!(ids.len(), k as usize);
        assert_eq!(
            ids.iter().collect::<std::collections::BTreeSet<_>>().len(),
            k as usize
        );
        assert!(!c.verify(std::slice::from_ref(&q), &[8; 16], M::Randomized, &mut rng));
        let mut bad = q.clone();
        bad.native.zk_proof = bad.native.zk_proof.with_invalid_challenge();
        assert!(!c.verify(&[bad], &MERCHANT, M::Randomized, &mut rng));
        let mut bad = q.clone();
        bad.payinfo = info(255);
        assert!(!c.verify(&[bad], &MERCHANT, M::Specification, &mut rng));
        let mut bad = q.clone();
        bad.native.ss.clear();
        assert!(!c.verify(&[bad], &MERCHANT, M::Specification, &mut rng));
        assert!(CompactPayment::decode(&bytes[..bytes.len() - 1], p.payinfo, 80).is_err());
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(CompactPayment::decode(&bad, p.payinfo, 80).is_err());
        let mut bad = bytes.clone();
        bad[105..153].copy_from_slice(&nonsubgroup_bytes());
        assert!(CompactPayment::decode(&bad, p.payinfo, 80).is_err());
    }
    let w = c.issue().unwrap();
    assert!(c.spend(&w, 0, info(0)).is_err());
    assert_eq!(w.next_index(), 0);
    let p = c.spend(&w, 3, info(3)).unwrap();
    assert_ne!(p.native.rr[0], p.native.rr[1]);
}
#[test]
fn divisible_native_lifecycle_amounts_complete_deposit_and_codecs() {
    let d = Divisible::new(80).unwrap();
    assert_eq!(d.authority_triangular_points(), 80 * 81 / 2);
    let mut rng = StdRng::seed_from_u64(215);
    for k in [1, 16, 64] {
        let w = d.issue().unwrap();
        assert_eq!(w.next_index(), 1);
        let p = d.spend(&w, k, info(k as u8)).unwrap();
        assert_eq!(w.next_index(), 1 + k);
        let bytes = p.encode();
        let q = DivisiblePayment::decode(&bytes, p.payinfo, 80).unwrap();
        assert_eq!(q.encode(), bytes);
        assert_eq!(bytes.len(), 1321);
        for m in [M::Specification, M::Randomized] {
            assert!(d.verify(std::slice::from_ref(&q), &MERCHANT, m, &mut rng));
        }
        b::start_counts();
        let ids = d
            .deposit_serials_after_verification(std::slice::from_ref(&q))
            .unwrap();
        let counts = b::stop_counts();
        assert_eq!(counts.miller_terms, 2 * k as usize);
        assert_eq!(counts.final_exponentiations, k as usize);
        assert_eq!(ids.len(), k as usize);
        assert!(ids.iter().all(|s| s.len() == 288));
        assert_eq!(
            ids.iter().collect::<std::collections::BTreeSet<_>>().len(),
            k as usize
        );
        assert!(!d.verify(std::slice::from_ref(&q), &[8; 16], M::Randomized, &mut rng));
        let mut bad = q.clone();
        bad.native.zk_proof = bad.native.zk_proof.with_invalid_challenge();
        assert!(!d.verify(&[bad], &MERCHANT, M::Randomized, &mut rng));
        let mut bad = q.clone();
        bad.payinfo = info(255);
        assert!(!d.verify(&[bad], &MERCHANT, M::Specification, &mut rng));
        let mut wrong_amount = q.clone();
        wrong_amount.native.vv = if k == 1 { 2 } else { k - 1 };
        assert!(!d.verify(&[wrong_amount], &MERCHANT, M::Randomized, &mut rng));
        let mut bad = q.clone();
        bad.native.vv = 0;
        assert!(!d.verify(&[bad], &MERCHANT, M::Randomized, &mut rng));
        assert!(DivisiblePayment::decode(&bytes[..bytes.len() - 1], p.payinfo, 80).is_err());
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(DivisiblePayment::decode(&bad, p.payinfo, 80).is_err());
        let mut bad = bytes.clone();
        bad[105..153].copy_from_slice(&nonsubgroup_bytes());
        assert!(DivisiblePayment::decode(&bad, p.payinfo, 80).is_err());
    }
    let w = d.issue().unwrap();
    assert!(d.spend(&w, 0, info(0)).is_err());
    assert_eq!(w.next_index(), 1);
    // Same native wallet, two consecutive spends: exact disjoint serial expansion.
    let a = d.spend(&w, 7, info(7)).unwrap();
    let c = d.spend(&w, 9, info(9)).unwrap();
    let ids = d.deposit_serials_after_verification(&[a, c]).unwrap();
    assert_eq!(
        ids.iter().collect::<std::collections::BTreeSet<_>>().len(),
        16
    );
}
#[test]
fn canonical_native_scalar_gt_and_nonsubgroup_fixtures() {
    use b::GtCompat;
    let scalar = b::hash_scalar(
        b"rp23-cross-backend-fixture",
        b"QUUX-V01-CS02-with-expander",
    );
    assert_eq!(
        scalar
            .to_bytes()
            .iter()
            .map(|x| format!("{x:02x}"))
            .collect::<String>(),
        "376dfde2ef0005efad9ea2e214ceeb709e469a032b76f6e510f908102d035d0d"
    );
    let gt = b::pairing(
        &(b::G1Projective::generator() * b::Scalar::from(5)).to_affine(),
        &(b::G2Projective::generator() * b::Scalar::from(7)).to_affine(),
    )
    .to_compressed();
    assert_eq!(gt.iter().map(|x|format!("{x:02x}")).collect::<String>(),"c1ca814ff7083094975f2186a643146a7440e3e451905945743752b1401bc11a377d49af8939df3388152e89ad3d7f8e14b3f4389d9347fa57f8cb1036f6a43936bc5c5fd3c36230112ea895bd6c45a554327d63d2125c19a887d30b3c6f64ef173f8d588daf92c713fccb463c052c8359021710b2b03fc987305afc2438e723104abcc268c48a2e2583a02bd555916e0b40356ba88972c575266d95cc1c8fd1615cdbbec72de888d956f0a2cfffa74e90f20b78fee5c08a55863e45f606dda900e4919a80ad50e8284b62cc2c32de5a34ff7024c9417943c38623e6cca63503092558c4d7cc575d4ce8936f3d20e92f16dd215f3d476c02356ee7741f7ced89d248a7c4ad28b374337e3b50eab071aeed42fe13cc7cde247c801bc05d563943");
    let bytes = (1u64..256)
        .find_map(|i| {
            let mut bytes = [0; 48];
            bytes[0] = 0x80;
            bytes[40..].copy_from_slice(&i.to_be_bytes());
            let p = Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed_unchecked(
                &bytes,
            ))?;
            (!bool::from(p.is_torsion_free())).then_some(bytes)
        })
        .unwrap();
    assert!(Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed(&bytes)).is_none());
}
