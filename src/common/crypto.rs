//! Framed encodings, nonzero scalars, hash functions and point validation.
use crate::polynomial::S;
use blstrs::{G1Projective as G1, G2Projective as G2};
use ff::Field;
use group::{Curve, Group};
use rand::RngCore;
use sha2::{Digest, Sha256};

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend((bytes.len() as u64).to_be_bytes());
    out.extend(bytes);
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn scalars(out: &mut Vec<u8>, values: &[S]) {
    let _span = crate::darlt::instrumentation::span("encoding");
    out.extend((values.len() as u64).to_be_bytes());
    for x in values {
        out.extend(x.to_bytes_be());
    }
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn points1(out: &mut Vec<u8>, values: &[G1]) {
    let _span = crate::darlt::instrumentation::span("encoding");
    out.extend((values.len() as u64).to_be_bytes());
    for x in values {
        out.extend(x.to_compressed());
    }
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn points2(out: &mut Vec<u8>, values: &[G2]) {
    let _span = crate::darlt::instrumentation::span("encoding");
    out.extend((values.len() as u64).to_be_bytes());
    for x in values {
        out.extend(x.to_compressed());
    }
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn nonzero(rng: &mut impl RngCore) -> S {
    loop {
        let x = S::random(&mut *rng);
        if x != S::ZERO {
            return x;
        }
    }
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn hash_scalar(label: &[u8], payload: &[u8]) -> S {
    let _span = crate::darlt::instrumentation::span("fiat_shamir");
    for counter in 0u64.. {
        let mut h = Sha256::new();
        h.update(b"DARLT/hash/scalar/frame");
        h.update((label.len() as u64).to_be_bytes());
        h.update(label);
        h.update((payload.len() as u64).to_be_bytes());
        h.update(payload);
        h.update(counter.to_be_bytes());
        if let Some(x) = Option::<S>::from(S::from_bytes_be(&h.finalize().into())) {
            if x != S::ZERO {
                return x;
            }
        }
    }
    unreachable!()
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn hash_point(label: &[u8], payload: &[u8]) -> G1 {
    let _span = crate::darlt::instrumentation::span("hash_to_group");
    let mut msg = Vec::new();
    frame(&mut msg, label);
    frame(&mut msg, payload);
    G1::hash_to_curve(&msg, b"DARLT/G1/BLS12381G1_XMD:SHA-256_SSWU_RO_", &[])
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn valid1(p: G1, nonidentity: bool) -> bool {
    crate::subgroup_audit::g1(&p, "common::crypto::valid1");
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    let a = p.to_affine();
    bool::from(a.is_on_curve() & a.is_torsion_free()) && (!nonidentity || p != G1::identity())
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn valid2(p: G2, nonidentity: bool) -> bool {
    crate::subgroup_audit::g2(&p, "common::crypto::valid2");
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    let a = p.to_affine();
    bool::from(a.is_on_curve() & a.is_torsion_free()) && (!nonidentity || p != G2::identity())
}
