//! Independent metadata OR Chaum--Pedersen proof component.
//!
//! The relation is (P0=g^eta0 AND E=R^eta0) OR
//! (P1=g^eta1 AND E=R^eta1), as in the metadata proof.
//! This module is not an issuance protocol. The caller supplies the external
//! domain prefix, which must carry the surrounding public-parameter and issuer
//! context when this component is incorporated into a complete protocol.

use blstrs::{G1Projective as G1, Scalar as S};
use ff::Field;
use group::Group;
use rand::RngCore;
use sha2::{Digest, Sha256};

const DOMAIN: &[u8] = b"DARLT/Metadata/Component/OR-Proof";
pub const PROOF_PAYLOAD_BYTES: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetadataError {
    InvalidBit,
    ZeroSecret,
    InvalidPublicPoint,
    InconsistentWitness,
    InvalidLength,
    NoncanonicalScalar,
}

#[derive(Clone, Debug)]
pub struct MetadataStatement {
    pub keys: [G1; 2],
    pub r: G1,
    pub e: G1,
}

impl MetadataStatement {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn nondegenerate(&self) -> bool {
        self.keys.iter().all(|point| *point != G1::identity())
            && self.r != G1::identity()
            && self.e != G1::identity()
    }
}

/// Four canonical scalars: global challenge, branch-0 challenge and responses.
///
/// Branch-1 challenge is c-c0. The four first-message points are reconstructed,
/// not transmitted. This is the OR core representation without the
/// generic Proof object's version and vector-length framing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataProof {
    pub c: S,
    pub c0: S,
    pub z: [S; 2],
}

impl MetadataProof {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn to_bytes(&self) -> [u8; PROOF_PAYLOAD_BYTES] {
        let mut out = [0; PROOF_PAYLOAD_BYTES];
        for (chunk, scalar) in out
            .chunks_exact_mut(32)
            .zip([self.c, self.c0, self.z[0], self.z[1]])
        {
            chunk.copy_from_slice(&scalar.to_bytes_be());
        }
        out
    }

    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, MetadataError> {
        if bytes.len() != PROOF_PAYLOAD_BYTES {
            return Err(MetadataError::InvalidLength);
        }
        let mut values = [S::ZERO; 4];
        for (value, chunk) in values.iter_mut().zip(bytes.chunks_exact(32)) {
            let encoded: [u8; 32] = chunk.try_into().unwrap();
            *value = Option::<S>::from(S::from_bytes_be(&encoded))
                .ok_or(MetadataError::NoncanonicalScalar)?;
        }
        Ok(Self {
            c: values[0],
            c0: values[1],
            z: [values[2], values[3]],
        })
    }
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn challenge(prefix: &[u8], statement: &MetadataStatement, firsts: &[G1; 4]) -> S {
    let mut transcript = Vec::with_capacity(DOMAIN.len() + 8 + prefix.len() + 9 * 48);
    transcript.extend_from_slice(DOMAIN);
    transcript.extend_from_slice(&(prefix.len() as u64).to_be_bytes());
    transcript.extend_from_slice(prefix);
    for point in [
        G1::generator(),
        statement.keys[0],
        statement.keys[1],
        statement.r,
        statement.e,
        firsts[0],
        firsts[1],
        firsts[2],
        firsts[3],
    ] {
        transcript.extend_from_slice(&point.to_compressed());
    }
    // As in the existing scalar-hash profile, reject out-of-field and zero
    // SHA-256 values instead of reducing a truncated digest modulo the field.
    for counter in 0u64.. {
        let mut hash = Sha256::new();
        hash.update(&transcript);
        hash.update(counter.to_be_bytes());
        let digest: [u8; 32] = hash.finalize().into();
        if let Some(candidate) = Option::<S>::from(S::from_bytes_be(&digest)) {
            if candidate != S::ZERO {
                return candidate;
            }
        }
    }
    unreachable!()
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn prove(
    rng: &mut impl RngCore,
    domain_prefix: &[u8],
    statement: &MetadataStatement,
    which: usize,
    eta: S,
) -> Result<MetadataProof, MetadataError> {
    if which >= 2 {
        return Err(MetadataError::InvalidBit);
    }
    if eta == S::ZERO {
        return Err(MetadataError::ZeroSecret);
    }
    if !statement.nondegenerate() {
        return Err(MetadataError::InvalidPublicPoint);
    }
    let g = G1::generator();
    if g * eta != statement.keys[which] || statement.r * eta != statement.e {
        return Err(MetadataError::InconsistentWitness);
    }
    let simulated = 1 - which;
    let simulated_c = S::random(&mut *rng);
    let simulated_z = S::random(&mut *rng);
    let nonce = S::random(&mut *rng);
    let mut firsts = [G1::identity(); 4];
    firsts[2 * which] = g * nonce;
    firsts[2 * which + 1] = statement.r * nonce;
    firsts[2 * simulated] = crate::ops::msm1(
        &[g, statement.keys[simulated]],
        &[simulated_z, -simulated_c],
    );
    firsts[2 * simulated + 1] =
        crate::ops::msm1(&[statement.r, statement.e], &[simulated_z, -simulated_c]);
    let c = challenge(domain_prefix, statement, &firsts);
    let real_c = c - simulated_c;
    let real_z = nonce + real_c * eta;
    let mut z = [S::ZERO; 2];
    z[which] = real_z;
    z[simulated] = simulated_z;
    Ok(MetadataProof {
        c,
        c0: if which == 0 { real_c } else { simulated_c },
        z,
    })
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verify(domain_prefix: &[u8], statement: &MetadataStatement, proof: &MetadataProof) -> bool {
    if !statement.nondegenerate() {
        return false;
    }
    let g = G1::generator();
    let challenges = [proof.c0, proof.c - proof.c0];
    let mut firsts = [G1::identity(); 4];
    for (branch, branch_challenge) in challenges.into_iter().enumerate() {
        firsts[2 * branch] = crate::ops::msm1(
            &[g, statement.keys[branch]],
            &[proof.z[branch], -branch_challenge],
        );
        firsts[2 * branch + 1] = crate::ops::msm1(
            &[statement.r, statement.e],
            &[proof.z[branch], -branch_challenge],
        );
    }
    challenge(domain_prefix, statement, &firsts) == proof.c
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    fn statement(which: usize) -> (MetadataStatement, S) {
        let secrets = [S::from(17), S::from(29)];
        let g = G1::generator();
        let r = g * S::from(43);
        (
            MetadataStatement {
                keys: [g * secrets[0], g * secrets[1]],
                r,
                e: r * secrets[which],
            },
            secrets[which],
        )
    }

    #[test]
    fn both_metadata_bits_have_valid_core_encodings() {
        let mut rng = StdRng::seed_from_u64(182028);
        for which in 0..2 {
            let (statement, eta) = statement(which);
            let proof = prove(
                &mut rng,
                b"test-pp-and-issuer-prefix",
                &statement,
                which,
                eta,
            )
            .unwrap();
            assert!(verify(b"test-pp-and-issuer-prefix", &statement, &proof));
            let bytes = proof.to_bytes();
            assert_eq!(bytes.len(), 128);
            assert_eq!(MetadataProof::from_bytes(&bytes).unwrap(), proof);
        }
    }

    #[test]
    fn all_four_proof_scalar_mutations_are_rejected() {
        let mut rng = StdRng::seed_from_u64(182029);
        let (statement, eta) = statement(0);
        let proof = prove(&mut rng, b"bound-prefix", &statement, 0, eta).unwrap();
        for field in 0..4 {
            let mut changed = proof.clone();
            match field {
                0 => changed.c += S::ONE,
                1 => changed.c0 += S::ONE,
                2 => changed.z[0] += S::ONE,
                _ => changed.z[1] += S::ONE,
            }
            assert!(!verify(b"bound-prefix", &statement, &changed));
        }
    }

    #[test]
    fn public_keys_r_e_and_branch_order_are_bound() {
        let mut rng = StdRng::seed_from_u64(182030);
        let (statement, eta) = statement(1);
        let proof = prove(&mut rng, b"bound-prefix", &statement, 1, eta).unwrap();
        for field in 0..5 {
            let mut changed = statement.clone();
            match field {
                0 => changed.keys[0] += G1::generator(),
                1 => changed.keys[1] += G1::generator(),
                2 => changed.r += G1::generator(),
                3 => changed.e += G1::generator(),
                _ => changed.keys.swap(0, 1),
            }
            assert!(!verify(b"bound-prefix", &changed, &proof));
        }
    }

    #[test]
    fn external_prefix_is_bound() {
        let mut rng = StdRng::seed_from_u64(182031);
        let (statement, eta) = statement(0);
        let proof = prove(&mut rng, b"pp-A/issuer-A", &statement, 0, eta).unwrap();
        for prefix in [&b"pp-B/issuer-A"[..], &b"pp-A/issuer-B"[..], &b""[..]] {
            assert!(!verify(prefix, &statement, &proof));
        }
    }

    #[test]
    fn inconsistent_witness_or_bit_is_rejected() {
        let mut rng = StdRng::seed_from_u64(182032);
        let (statement, eta) = statement(0);
        assert_eq!(
            prove(&mut rng, b"p", &statement, 2, eta),
            Err(MetadataError::InvalidBit)
        );
        assert_eq!(
            prove(&mut rng, b"p", &statement, 0, eta + S::ONE),
            Err(MetadataError::InconsistentWitness)
        );
        assert_eq!(
            prove(&mut rng, b"p", &statement, 1, eta),
            Err(MetadataError::InconsistentWitness)
        );
        let mut wrong_e = statement.clone();
        wrong_e.e += G1::generator();
        assert_eq!(
            prove(&mut rng, b"p", &wrong_e, 0, eta),
            Err(MetadataError::InconsistentWitness)
        );
    }

    #[test]
    fn zero_secret_or_identity_statement_points_are_rejected() {
        let mut rng = StdRng::seed_from_u64(182033);
        let (statement, eta) = statement(1);
        let proof = prove(&mut rng, b"p", &statement, 1, eta).unwrap();
        assert!(!verify(
            b"p",
            &statement,
            &MetadataProof {
                c: S::ZERO,
                c0: S::ZERO,
                z: [S::ZERO; 2]
            }
        ));
        assert_eq!(
            prove(&mut rng, b"p", &statement, 1, S::ZERO),
            Err(MetadataError::ZeroSecret)
        );
        for field in 0..4 {
            let mut changed = statement.clone();
            match field {
                0 => changed.keys[0] = G1::identity(),
                1 => changed.keys[1] = G1::identity(),
                2 => changed.r = G1::identity(),
                _ => changed.e = G1::identity(),
            }
            assert_eq!(
                prove(&mut rng, b"p", &changed, 1, eta),
                Err(MetadataError::InvalidPublicPoint)
            );
            assert!(!verify(b"p", &changed, &proof));
        }
    }

    #[test]
    fn malformed_or_noncanonical_proof_encodings_are_rejected() {
        let mut rng = StdRng::seed_from_u64(182034);
        let (statement, eta) = statement(0);
        let bytes = prove(&mut rng, b"p", &statement, 0, eta)
            .unwrap()
            .to_bytes();
        assert_eq!(
            MetadataProof::from_bytes(&bytes[..127]),
            Err(MetadataError::InvalidLength)
        );
        let mut too_long = bytes.to_vec();
        too_long.push(0);
        assert_eq!(
            MetadataProof::from_bytes(&too_long),
            Err(MetadataError::InvalidLength)
        );
        let mut noncanonical = bytes;
        noncanonical[32..64].fill(255);
        assert_eq!(
            MetadataProof::from_bytes(&noncanonical),
            Err(MetadataError::NoncanonicalScalar)
        );
    }
}
