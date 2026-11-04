use baseline_core::arithmetic::{g1_add, g2_add, G1, G2, S};
use baseline_core::bhn26::*;
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};

fn fixture(seed: u64, bit: u8) -> (IssuerKeys, InstalledIssuer, ClientKeys, IssueMessage, Token) {
    let mut rng = StdRng::seed_from_u64(seed);
    let issuer = IssuerKeys::generate(&mut rng);
    let installed = issuer.install().unwrap();
    let client = ClientKeys::generate(&mut rng);
    let message = issue(
        &installed,
        &issuer.secret,
        client.public_key(),
        bit,
        &mut rng,
    )
    .unwrap();
    let token = obtain(&installed, &client, &message, &mut rng).unwrap();
    (issuer, installed, client, message, token)
}
#[test]
fn honest_both_bits_roundtrip_and_individual_verification() {
    for seed in 0..24 {
        for bit in 0..=1 {
            let (issuer, installed, client, message, token) =
                fixture(1210100 + seed * 2 + bit as u64, bit);
            assert_eq!(
                PublicKey::decode(&issuer.public.encode()).unwrap(),
                issuer.public
            );
            let message = IssueMessage::decode(&message.encode()).unwrap();
            let token = Token::decode(&token.encode()).unwrap();
            assert!(public_verify(&installed, &token));
            let verified = verify_token(&installed, &token).unwrap();
            assert_eq!(read_bit_extract(&issuer.secret, &verified).unwrap(), bit);
            assert_eq!(
                read_bit_total(&installed, &issuer.secret, &token).unwrap(),
                bit
            );
            let mut rng = StdRng::seed_from_u64(seed + 1);
            let wire_token = client
                .prepare_obtain(&mut rng)
                .obtain_wire(&installed, &message.encode())
                .unwrap();
            assert_eq!(
                read_bit_total(&installed, &issuer.secret, &wire_token).unwrap(),
                bit
            );
        }
    }
}
#[test]
fn every_issuance_field_is_authenticated() {
    let (_, installed, client, message, _) = fixture(1210200, 1);
    for index in 0..12 {
        let mut bad = message.clone();
        match index {
            0 => bad.nonce[0] ^= 1,
            1 => bad.s = g1_add(bad.s, G1::generator()),
            2 => bad.signature.z = g1_add(bad.signature.z, G1::generator()),
            3 => bad.signature.y1 = g1_add(bad.signature.y1, G1::generator()),
            4 => bad.signature.y2 = g2_add(bad.signature.y2, G2::generator()),
            5 => bad.proof.c0 += S::ONE,
            6 => bad.proof.c1 += S::ONE,
            7 => bad.proof.au += S::ONE,
            8 => bad.proof.av += S::ONE,
            9 => bad.proof.aw += S::ONE,
            10 => bad.proof.a0 += S::ONE,
            11 => bad.proof.a1 += S::ONE,
            _ => unreachable!(),
        }
        let mut rng = StdRng::seed_from_u64(1210201 + index);
        assert!(
            client
                .prepare_obtain(&mut rng)
                .obtain(&installed, &bad)
                .is_err(),
            "issuance field {index}"
        );
    }
}
#[test]
fn every_token_field_is_authenticated() {
    let (issuer, installed, _, _, token) = fixture(1210300, 0);
    for index in 0..5 {
        let mut bad = token.clone();
        match index {
            0 => bad.t1 = g1_add(bad.t1, G1::generator()),
            1 => bad.t2 = g1_add(bad.t2, G1::generator()),
            2 => bad.signature.z = g1_add(bad.signature.z, G1::generator()),
            3 => bad.signature.y1 = g1_add(bad.signature.y1, G1::generator()),
            4 => bad.signature.y2 = g2_add(bad.signature.y2, G2::generator()),
            _ => unreachable!(),
        }
        assert!(!public_verify(&installed, &bad), "token field {index}");
        assert!(read_bit_total(&installed, &issuer.secret, &bad).is_err());
    }
}
#[test]
fn keys_client_binding_and_domains_are_enforced() {
    let (issuer, installed, client, message, token) = fixture(1210400, 0);
    let mut rng = StdRng::seed_from_u64(1210401);
    let other_issuer = IssuerKeys::generate(&mut rng);
    let other_installed = other_issuer.install().unwrap();
    let other_client = ClientKeys::generate(&mut rng);
    assert!(other_client
        .prepare_obtain(&mut rng)
        .obtain(&installed, &message)
        .is_err());
    assert!(client
        .prepare_obtain(&mut rng)
        .obtain(&other_installed, &message)
        .is_err());
    assert!(issue(
        &other_installed,
        &issuer.secret,
        client.public_key(),
        0,
        &mut rng
    )
    .is_err());
    assert!(issue(&installed, &issuer.secret, G1::identity(), 0, &mut rng).is_err());
    assert!(issue(&installed, &issuer.secret, client.public_key(), 2, &mut rng).is_err());
    let verified = verify_token(&installed, &token).unwrap();
    assert!(read_bit_extract(&other_issuer.secret, &verified).is_err());
    assert!(read_bit_total(&other_installed, &other_issuer.secret, &token).is_err());
    for i in 0..5 {
        let mut bad = issuer.public.clone();
        if i < 2 {
            bad.t[i] += G1::generator();
        } else {
            bad.y[i - 2] += G2::generator();
        }
        let changed = install(&bad).unwrap();
        assert!(client
            .prepare_obtain(&mut rng)
            .obtain(&changed, &message)
            .is_err());
        if i < 2 {
            // The final SPS token uses y[0..3]; the metadata-bit keys t[0..2]
            // authenticate issuance and extraction rather than SPS verification.
            assert!(public_verify(&changed, &token));
            let cap = verify_token(&changed, &token).unwrap();
            assert!(read_bit_extract(&issuer.secret, &cap).is_err());
        } else {
            assert!(!public_verify(&changed, &token));
        }
    }
}
fn replace_once(bytes: &mut [u8], before: &[u8], after: &[u8]) {
    assert_eq!(before.len(), after.len());
    let positions: Vec<_> = bytes
        .windows(before.len())
        .enumerate()
        .filter_map(|(i, b)| (b == before).then_some(i))
        .collect();
    assert_eq!(positions.len(), 1);
    bytes[positions[0]..positions[0] + after.len()].copy_from_slice(after);
}
fn nonsubgroup_g1() -> [u8; 48] {
    for v in 1..10000u64 {
        let mut bytes = [0u8; 48];
        bytes[0] = 0x80;
        bytes[40..].copy_from_slice(&v.to_be_bytes());
        if let Some(point) =
            Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed_unchecked(&bytes))
        {
            if !bool::from(point.is_torsion_free()) {
                return bytes;
            }
        }
    }
    panic!("no subgroup-negative fixture");
}
fn nonsubgroup_g2() -> [u8; 96] {
    for v in 1..10000u64 {
        let mut bytes = [0u8; 96];
        bytes[0] = 0x80;
        bytes[88..].copy_from_slice(&v.to_be_bytes());
        if let Some(point) =
            Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed_unchecked(&bytes))
        {
            if !bool::from(point.is_torsion_free()) {
                return bytes;
            }
        }
    }
    panic!("no subgroup-negative fixture");
}
#[test]
fn malformed_wire_and_received_domains_are_rejected() {
    let (issuer, installed, client, message, token) = fixture(1210500, 1);
    let msg_bytes = message.encode();
    let tok_bytes = token.encode();
    for bytes in [&msg_bytes, &tok_bytes] {
        for len in [0, 1, bytes.len() - 1] {
            assert!(IssueMessage::decode(&bytes[..len]).is_err());
            assert!(Token::decode(&bytes[..len]).is_err());
        }
        let mut tail = bytes.to_vec();
        tail.push(0);
        assert!(IssueMessage::decode(&tail).is_err());
        assert!(Token::decode(&tail).is_err());
    }
    assert!(IssueMessage::decode(&tok_bytes).is_err());
    assert!(Token::decode(&msg_bytes).is_err());
    assert!(PublicKey::decode(&msg_bytes).is_err());
    for replacement in [
        G1::identity().to_compressed(),
        [255u8; 48],
        nonsubgroup_g1(),
    ] {
        let mut bytes = tok_bytes.clone();
        replace_once(&mut bytes, &token.t1.to_compressed(), &replacement);
        assert!(Token::decode(&bytes).is_err());
        assert!(verify_token_wire(&installed, &bytes).is_err());
        let mut bytes = msg_bytes.clone();
        replace_once(&mut bytes, &message.s.to_compressed(), &replacement);
        assert!(IssueMessage::decode(&bytes).is_err());
        let mut rng = StdRng::seed_from_u64(1210501);
        assert!(client
            .prepare_obtain(&mut rng)
            .obtain_wire(&installed, &bytes)
            .is_err());
        let mut bytes = issuer.public.encode();
        replace_once(
            &mut bytes,
            &issuer.public.t[0].to_compressed(),
            &replacement,
        );
        assert!(PublicKey::decode(&bytes).is_err());
    }
    for replacement in [
        G2::identity().to_compressed(),
        [255u8; 96],
        nonsubgroup_g2(),
    ] {
        let mut bytes = tok_bytes.clone();
        replace_once(
            &mut bytes,
            &token.signature.y2.to_compressed(),
            &replacement,
        );
        assert!(Token::decode(&bytes).is_err());
        let mut bytes = msg_bytes.clone();
        replace_once(
            &mut bytes,
            &message.signature.y2.to_compressed(),
            &replacement,
        );
        assert!(IssueMessage::decode(&bytes).is_err());
        let mut bytes = issuer.public.encode();
        replace_once(
            &mut bytes,
            &issuer.public.y[0].to_compressed(),
            &replacement,
        );
        assert!(PublicKey::decode(&bytes).is_err());
    }
    let mut bytes = msg_bytes.clone();
    replace_once(&mut bytes, &message.proof.aw.to_bytes_be(), &[255; 32]);
    assert!(IssueMessage::decode(&bytes).is_err());
    let mut bytes = msg_bytes.clone();
    replace_once(&mut bytes, &message.nonce, &[3; NONCE_BYTES]);
    let changed = IssueMessage::decode(&bytes).unwrap();
    let mut rng = StdRng::seed_from_u64(1210502);
    assert!(client
        .prepare_obtain(&mut rng)
        .obtain(&installed, &changed)
        .is_err());
    let mut short_nonce = message.clone();
    short_nonce.nonce.pop();
    assert!(IssueMessage::decode(&short_nonce.encode()).is_err());
}
#[test]
fn object_offcurve_and_identity_mutations_are_rejected() {
    let (_, installed, client, message, token) = fixture(1210600, 0);
    let p = token.t1;
    let offcurve = G1::from_raw_unchecked(p.x(), p.y() + p.z(), p.z());
    assert!(!bool::from(offcurve.is_on_curve()));
    let mut bad = token.clone();
    bad.t1 = offcurve;
    assert!(!public_verify(&installed, &bad));
    let mut bad = message.clone();
    bad.s = offcurve;
    let mut rng = StdRng::seed_from_u64(1210601);
    assert!(client
        .prepare_obtain(&mut rng)
        .obtain(&installed, &bad)
        .is_err());
    let mut key = installed.public_key().clone();
    key.t[0] = offcurve;
    assert!(install(&key).is_err());
    let p = token.signature.y2;
    let offcurve = G2::from_raw_unchecked(p.x(), p.y() + p.z(), p.z());
    assert!(!bool::from(offcurve.is_on_curve()));
    let mut bad = token.clone();
    bad.signature.y2 = offcurve;
    assert!(!public_verify(&installed, &bad));
    let mut key = installed.public_key().clone();
    key.y[0] = offcurve;
    assert!(install(&key).is_err());
    for i in 0..4 {
        let mut bad = token.clone();
        match i {
            0 => bad.t1 = G1::identity(),
            1 => bad.t2 = G1::identity(),
            2 => bad.signature.y1 = G1::identity(),
            3 => bad.signature.y2 = G2::identity(),
            _ => unreachable!(),
        }
        assert!(!public_verify(&installed, &bad));
    }
}
#[test]
fn canonical_zero_scalars_are_not_rejected_by_codec() {
    let (_, _, _, mut message, _) = fixture(1210700, 0);
    message.proof = IssuerProof {
        c0: S::ZERO,
        c1: S::ZERO,
        au: S::ZERO,
        av: S::ZERO,
        aw: S::ZERO,
        a0: S::ZERO,
        a1: S::ZERO,
    };
    assert_eq!(IssueMessage::decode(&message.encode()).unwrap(), message);
    message.signature.z = G1::identity();
    assert_eq!(IssueMessage::decode(&message.encode()).unwrap(), message);
}
#[test]
fn random_tape_repeats_and_fresh_sessions_differ() {
    let (keys1, _, _, message1, token1) = fixture(1210800, 1);
    let (keys2, _, _, message2, token2) = fixture(1210800, 1);
    assert_eq!(keys1.public, keys2.public);
    assert_eq!(message1, message2);
    assert_eq!(token1, token2);
    let mut rng = StdRng::seed_from_u64(1210801);
    let installed = keys1.install().unwrap();
    let client = ClientKeys::generate(&mut rng);
    let first = issue(&installed, &keys1.secret, client.public_key(), 0, &mut rng).unwrap();
    let second = issue(&installed, &keys1.secret, client.public_key(), 0, &mut rng).unwrap();
    assert_ne!(first.nonce, second.nonce);
    assert_ne!(first.proof, second.proof);
    let token1 = client
        .prepare_obtain(&mut rng)
        .obtain(&installed, &first)
        .unwrap();
    let token2 = client
        .prepare_obtain(&mut rng)
        .obtain(&installed, &first)
        .unwrap();
    assert_ne!(token1.signature, token2.signature);
    assert!(public_verify(&installed, &token1));
    assert!(public_verify(&installed, &token2));
}
#[test]
fn prepared_issue_received_requests_and_cross_key_binding() {
    let (issuer, installed, client, _, token) = fixture(1210900, 1);
    let mut rng = StdRng::seed_from_u64(1210901);
    let request = encode_client_request(client.public_key());
    let issued = prepare_issue(&installed, &mut rng)
        .issue_wire(&installed, &issuer.secret, &request, 1, &mut rng)
        .unwrap();
    let obtained = client
        .prepare_obtain(&mut rng)
        .obtain_wire(&installed, &issued.encode())
        .unwrap();
    assert_eq!(
        read_bit_total(&installed, &issuer.secret, &obtained).unwrap(),
        1
    );
    let mut trailing = request.clone();
    trailing.push(0);
    assert!(prepare_issue(&installed, &mut rng)
        .issue_wire(&installed, &issuer.secret, &trailing, 1, &mut rng)
        .is_err());
    assert!(prepare_issue(&installed, &mut rng)
        .issue_wire(&installed, &issuer.secret, &token.encode(), 1, &mut rng)
        .is_err());
    for replacement in [
        G1::identity().to_compressed(),
        [255u8; 48],
        nonsubgroup_g1(),
    ] {
        let mut bad = request.clone();
        replace_once(&mut bad, &client.public_key().to_compressed(), &replacement);
        assert!(prepare_issue(&installed, &mut rng)
            .issue_wire(&installed, &issuer.secret, &bad, 1, &mut rng)
            .is_err());
    }
    let other = IssuerKeys::generate(&mut rng);
    let other_installed = other.install().unwrap();
    assert!(prepare_issue(&installed, &mut rng)
        .issue_wire(&other_installed, &other.secret, &request, 1, &mut rng)
        .is_err());
    assert!(prepare_issue(&installed, &mut rng)
        .issue_wire(&installed, &issuer.secret, &request, 2, &mut rng)
        .is_err());
}

#[test]
fn object_non_subgroup_points_are_rejected() {
    let (_, installed, client, message, token) = fixture(1211100, 0);
    let p = blstrs::G1Affine::from_compressed_unchecked(&nonsubgroup_g1()).unwrap();
    assert!(bool::from(p.is_on_curve()) && !bool::from(p.is_torsion_free()));
    let mut bad = token.clone();
    bad.t1 = G1::from(p);
    assert!(!public_verify(&installed, &bad));
    let mut bad = message.clone();
    bad.s = G1::from(p);
    let mut rng = StdRng::seed_from_u64(1211101);
    assert!(client
        .prepare_obtain(&mut rng)
        .obtain(&installed, &bad)
        .is_err());
    let p = blstrs::G2Affine::from_compressed_unchecked(&nonsubgroup_g2()).unwrap();
    assert!(bool::from(p.is_on_curve()) && !bool::from(p.is_torsion_free()));
    let mut bad = token.clone();
    bad.signature.y2 = G2::from(p);
    assert!(!public_verify(&installed, &bad));
}
