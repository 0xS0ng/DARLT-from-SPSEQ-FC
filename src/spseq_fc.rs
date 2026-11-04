//! SPSEQ-FC signatures, derivation keys and recipient proofs.
//!
//! The mask-refreshing delegation and functional-opening operations are
//! implemented by the DARLT specialization in `darlt::protocol` and
//! `darlt::caulk`. Encodings use canonical compressed points and big-endian scalars.

use crate::polynomial::S;
use blstrs::{G1Projective as G1, G2Prepared, G2Projective as G2, Gt};
use ff::Field;
use group::{Curve, Group};
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

pub type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
pub struct Params {
    pub u: G1,
    pub h0: G1,
    pub attrs: Vec<G1>,
    pub pools: Vec<G1>,
}
impl Params {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn new(u: G1, h0: G1, attrs: Vec<G1>, pools: Vec<G1>) -> Result<Self> {
        let value = Self {
            u,
            h0,
            attrs,
            pools,
        };
        if !value.valid() {
            return Err("invalid SPSEQ-FC public bases".into());
        }
        Ok(value)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn valid(&self) -> bool {
        !self.attrs.is_empty()
            && !self.pools.is_empty()
            && std::iter::once(&self.u)
                .chain(std::iter::once(&self.h0))
                .chain(self.attrs.iter())
                .chain(self.pools.iter())
                .all(|point| valid1(*point, true))
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend(self.u.to_compressed());
        out.extend(self.h0.to_compressed());
        g1s(&mut out, &self.attrs);
        g1s(&mut out, &self.pools);
        out
    }
}
#[derive(Clone, Debug)]
pub struct KeyPair {
    pub sk: Vec<S>,
    pub vk: Vec<G2>,
}
#[derive(Clone, Debug)]
pub struct Sig {
    pub z: G1,
    pub y: G1,
    pub yhat: G2,
}
impl Sig {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(192);
        out.extend(self.z.to_compressed());
        out.extend(self.y.to_compressed());
        out.extend(self.yhat.to_compressed());
        out
    }
}
#[derive(Clone, Debug)]
pub struct Dk {
    pub k0: G1,
    pub ka: G1,
    pub attrs: Vec<G1>,
    pub pools: Vec<G1>,
}
impl Dk {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend(self.k0.to_compressed());
        out.extend(self.ka.to_compressed());
        g1s(&mut out, &self.attrs);
        g1s(&mut out, &self.pools);
        out
    }
}
#[derive(Clone, Debug)]
pub struct Schnorr {
    pub a: G1,
    pub z: S,
}
#[derive(Clone, Debug)]
pub struct Request {
    pub sid: Vec<u8>,
    pub pka: G1,
    pub proof: Schnorr,
}
impl Request {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = request_fields(self);
        out.extend(self.proof.a.to_compressed());
        out.extend(self.proof.z.to_bytes_be());
        out
    }
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn random_nonzero(rng: &mut impl RngCore) -> S {
    loop {
        let value = S::random(&mut *rng);
        if value != S::ZERO {
            return value;
        }
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid1(point: G1, nonidentity: bool) -> bool {
    let affine = point.to_affine();
    crate::subgroup_audit::g1(&point, "darlt/spseq_fc/valid1");
    bool::from(affine.is_on_curve() & affine.is_torsion_free())
        && (!nonidentity || point != G1::identity())
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid2(point: G2, nonidentity: bool) -> bool {
    let affine = point.to_affine();
    crate::subgroup_audit::g2(&point, "darlt/spseq_fc/valid2");
    bool::from(affine.is_on_curve() & affine.is_torsion_free())
        && (!nonidentity || point != G2::identity())
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_vk(vk: &[G2]) -> bool {
    vk.len() == 9 && vk.iter().all(|point| valid2(*point, true))
}
/// Validate the immutable public instance once before using crate-local hot
/// operations. A ProtocolContext retains the checked parameters and key.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn validate_instance(pp: &Params, vk: &[G2]) -> bool {
    pp.valid() && valid_vk(vk)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_sig(sig: &Sig) -> bool {
    valid1(sig.z, false) && valid1(sig.y, true) && valid2(sig.yhat, true)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_message(parent: &[G1], child_allowed: bool) -> bool {
    (parent.len() == 8 || (child_allowed && parent.len() == 9))
        && parent.iter().all(|point| valid1(*point, true))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn multi_pair(terms: &[(G1, G2)]) -> Gt {
    let first: Vec<_> = terms.iter().map(|(a, _)| a.to_affine()).collect();
    let second: Vec<_> = terms
        .iter()
        .map(|(_, b)| G2Prepared::from(b.to_affine()))
        .collect();
    let refs: Vec<_> = first.iter().zip(&second).collect();
    crate::ops::final_exponentiation(&crate::ops::multi_miller_loop(&refs, terms.len()))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn frame(out: &mut Vec<u8>, input: &[u8]) {
    out.extend((input.len() as u64).to_be_bytes());
    out.extend(input);
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn g1s(out: &mut Vec<u8>, input: &[G1]) {
    out.extend((input.len() as u64).to_be_bytes());
    for point in input {
        out.extend(point.to_compressed());
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn scalar_hash(label: &[u8], transcript: &[u8]) -> S {
    for counter in 0u64.. {
        let mut hash = Sha256::new();
        hash.update((label.len() as u64).to_be_bytes());
        hash.update(label);
        hash.update((transcript.len() as u64).to_be_bytes());
        hash.update(transcript);
        hash.update(counter.to_be_bytes());
        let bytes: [u8; 32] = hash.finalize().into();
        if let Some(value) = Option::<S>::from(S::from_bytes_be(&bytes)) {
            if value != S::ZERO {
                return value;
            }
        }
    }
    unreachable!()
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn request_fields(request: &Request) -> Vec<u8> {
    let mut out = Vec::new();
    frame(&mut out, &request.sid);
    out.extend(request.pka.to_compressed());
    out
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn grant_valid(pp: &Params, gamma: &[usize], delta: &[bool]) -> bool {
    delta.len() == pp.attrs.len()
        && gamma.iter().all(|pool| *pool < pp.pools.len())
        && gamma.iter().copied().collect::<BTreeSet<_>>().len() == gamma.len()
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn keygen(rng: &mut impl RngCore) -> KeyPair {
    let sk: Vec<_> = (0..9).map(|_| random_nonzero(&mut *rng)).collect();
    let vk = sk.iter().map(|secret| G2::generator() * secret).collect();
    KeyPair { sk, vk }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn sign(pp: &Params, sk: &[S], parent: &[G1], rng: &mut impl RngCore) -> Result<(Sig, Dk)> {
    if !pp.valid()
        || !valid_message(parent, false)
        || parent[0] != pp.u
        || sk.len() != 9
        || sk.contains(&S::ZERO)
    {
        return Err("invalid SPSEQ-FC signing input".into());
    }
    let y = random_nonzero(rng);
    let reciprocal = Option::<S>::from(y.invert()).expect("nonzero y");
    let weighted = parent
        .iter()
        .zip(sk)
        .fold(G1::identity(), |sum, (point, key)| sum + point * key);
    let signature = Sig {
        z: weighted * y,
        y: G1::generator() * reciprocal,
        yhat: G2::generator() * reciprocal,
    };
    let power = y * sk[8];
    let key = Dk {
        k0: pp.h0 * power,
        ka: G1::generator() * power,
        attrs: pp.attrs.iter().map(|base| base * power).collect(),
        pools: pp.pools.iter().map(|base| base * power).collect(),
    };
    Ok((signature, key))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verify(pp: &Params, vk: &[G2], message: &[G1], signature: &Sig) -> bool {
    if !pp.valid() || !valid_vk(vk) || !valid_message(message, true) || !valid_sig(signature) {
        return false;
    }
    let mut terms = vec![(signature.z, signature.yhat)];
    terms.extend(message.iter().zip(vk).map(|(point, key)| (-*point, *key)));
    multi_pair(&terms) == Gt::identity()
        && multi_pair(&[
            (signature.y, G2::generator()),
            (-G1::generator(), signature.yhat),
        ]) == Gt::identity()
}
/// The two separate signature pairing-product equations.
/// Each equation is evaluated independently by the native verifier.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn signature_equations(
    pp: &Params,
    vk: &[G2],
    message: &[G1],
    signature: &Sig,
) -> Option<Vec<crate::pairing_batch::Equation>> {
    if !validate_instance(pp, vk) {
        return None;
    }
    signature_equations_installed(vk, message, signature)
}
/// Same residuals after immutable instance installation. Every new message and
/// signature still undergoes its full dimension, curve, subgroup and required
/// nonidentity checks. This entry point is not exposed outside the crate.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn signature_equations_installed(
    vk: &[G2],
    message: &[G1],
    signature: &Sig,
) -> Option<Vec<crate::pairing_batch::Equation>> {
    if vk.len() != 9 || !valid_message(message, true) || !valid_sig(signature) {
        return None;
    }
    Some(signature_equations_core(vk, message, signature))
}
/// Token points have already undergone strict received decoding. The sealed
/// capability is issued only by that immutable token wrapper.
pub(crate) fn signature_equations_received(
    vk: &[G2],
    message: &[G1],
    signature: &Sig,
    _: &crate::darlt::spend::ReceivedInputs,
) -> Option<Vec<crate::pairing_batch::Equation>> {
    if vk.len() != 9
        || !(message.len() == 8 || message.len() == 9)
        || message.iter().any(|point| *point == G1::identity())
        || signature.y == G1::identity()
        || signature.yhat == G2::identity()
    {
        return None;
    }
    Some(signature_equations_core(vk, message, signature))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn signature_equations_core(
    vk: &[G2],
    message: &[G1],
    signature: &Sig,
) -> Vec<crate::pairing_batch::Equation> {
    let mut main = vec![(signature.z, signature.yhat)];
    main.extend(message.iter().zip(vk).map(|(m, x)| (-*m, *x)));
    vec![
        main,
        vec![
            (signature.y, G2::generator()),
            (-G1::generator(), signature.yhat),
        ],
    ]
}
/// Verify the native conjunction without combining its two equations.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verify_signature_native(pp: &Params, vk: &[G2], message: &[G1], signature: &Sig) -> bool {
    let Some(equations) = signature_equations(pp, vk, message, signature) else {
        return false;
    };
    crate::pairing_batch::verify_each(&equations).is_ok_and(|r| r.accepted)
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn dk_pairs(pp: &Params, key: &Dk) -> Option<Vec<(G1, G1)>> {
    if key.attrs.len() != pp.attrs.len() || key.pools.len() != pp.pools.len() {
        return None;
    }
    let mut pairs = vec![(key.k0, pp.h0), (key.ka, G1::generator())];
    pairs.extend(key.attrs.iter().copied().zip(pp.attrs.iter().copied()));
    pairs.extend(key.pools.iter().copied().zip(pp.pools.iter().copied()));
    pairs
        .iter()
        .all(|(point, _)| valid1(*point, true))
        .then_some(pairs)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verify_dk(pp: &Params, vk: &[G2], signature: &Sig, key: &Dk) -> bool {
    if !pp.valid() || !valid_vk(vk) || !valid_sig(signature) {
        return false;
    }
    let Some(pairs) = dk_pairs(pp, key) else {
        return false;
    };
    pairs.into_iter().all(|(point, base)| {
        multi_pair(&[(point, signature.yhat), (-base, vk[8])]) == Gt::identity()
    })
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn chg_rep(
    pp: &Params,
    vk: &[G2],
    message: &[G1],
    signature: &Sig,
    mu: S,
    rng: &mut impl RngCore,
) -> Result<(Vec<G1>, Sig)> {
    if !validate_instance(pp, vk) {
        return Err("invalid SPSEQ-FC representative input".into());
    }
    chg_rep_installed(message, signature, mu, rng)
}
/// ChgRep for an immutable checked instance. This retains the original
/// per-message/signature checks, nonzero scale and RNG call sequence.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn chg_rep_installed(
    message: &[G1],
    signature: &Sig,
    mu: S,
    rng: &mut impl RngCore,
) -> Result<(Vec<G1>, Sig)> {
    if !valid_message(message, true) || !valid_sig(signature) || mu == S::ZERO {
        return Err("invalid SPSEQ-FC representative input".into());
    }
    let psi = random_nonzero(rng);
    let reciprocal = Option::<S>::from(psi.invert()).expect("nonzero psi");
    Ok((
        message.iter().map(|point| point * mu).collect(),
        Sig {
            z: signature.z * (mu * psi),
            y: signature.y * reciprocal,
            yhat: signature.yhat * reciprocal,
        },
    ))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn authorization(pp: &Params, pka: G1, r: S, gamma: &[usize], delta: &[bool]) -> Result<G1> {
    if !pp.valid() || !valid1(pka, true) || !grant_valid(pp, gamma, delta) {
        return Err("invalid SPSEQ-FC authorization".into());
    }
    let scope = gamma.iter().map(|pool| pp.pools[*pool]).sum::<G1>();
    if scope == G1::identity() {
        return Err("identity SPSEQ-FC scope".into());
    }
    let mut c = pp.h0 * r + pka + scope;
    for (base, bit) in pp.attrs.iter().zip(delta) {
        if *bit {
            c += base;
        }
    }
    Ok(c)
}
/// DARLT recipient proof challenge for an immutable installed instance.
/// The recipient does not know any parent message when making this request.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn installed_pk_challenge(
    parameter_digest: &[u8; 32],
    issuer_public: &[u8],
    request: &Request,
) -> S {
    let mut out = parameter_digest.to_vec();
    frame(&mut out, issuer_public);
    frame(&mut out, &request.sid);
    out.extend(request.pka.to_compressed());
    out.extend(request.proof.a.to_compressed());
    scalar_hash(b"SPSEQ-FC/PK/instance", &out)
}
/// Verify the parent-independent DARLT proof after static installation. The
/// digest and issuer encoding must come from the enclosing checked context.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn verify_request_installed(
    parameter_digest: &[u8; 32],
    issuer_public: &[u8],
    req: &Request,
) -> bool {
    if issuer_public.is_empty()
        || req.sid.is_empty()
        || !valid1(req.pka, true)
        || !valid1(req.proof.a, false)
    {
        return false;
    }
    crate::ops::msm1(
        &[G1::generator(), req.pka],
        &[
            req.proof.z,
            -installed_pk_challenge(parameter_digest, issuer_public, req),
        ],
    ) == req.proof.a
}
/// Same native Schnorr relation for an immutable strictly decoded request.
/// Installed keys and locally derived bases are not newly received points.
pub(crate) fn verify_request_received(
    parameter_digest: &[u8; 32],
    issuer_public: &[u8],
    req: &Request,
    checked: &crate::darlt::spend::ReceivedInputs,
) -> bool {
    if !checked.matches_parameters(parameter_digest)
        || issuer_public.is_empty()
        || req.sid.is_empty()
        || req.pka == G1::identity()
    {
        return false;
    }
    crate::ops::msm1(
        &[G1::generator(), req.pka],
        &[
            req.proof.z,
            -installed_pk_challenge(parameter_digest, issuer_public, req),
        ],
    ) == req.proof.a
}
/// Create a DARLT proof using only the installed public instance, session and
/// recipient secret. No parent coordinates or full parameter bytes are input.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn request_installed(
    parameter_digest: &[u8; 32],
    issuer_public: &[u8],
    sid: &[u8],
    agent_sk: S,
    rng: &mut impl RngCore,
) -> Result<Request> {
    if issuer_public.is_empty() || agent_sk == S::ZERO || sid.is_empty() {
        return Err("invalid recipient request".into());
    }
    let nonce = S::random(&mut *rng);
    let mut req = Request {
        sid: sid.to_vec(),
        pka: G1::generator() * agent_sk,
        proof: Schnorr {
            a: G1::generator() * nonce,
            z: S::ZERO,
        },
    };
    req.proof.z = nonce + installed_pk_challenge(parameter_digest, issuer_public, &req) * agent_sk;
    Ok(req)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    fn fixture() -> (StdRng, Params, KeyPair, Vec<G1>, Sig, Dk) {
        let mut rng = StdRng::seed_from_u64(0x0001_8251);
        let make = |tag: &[u8]| {
            G1::hash_to_curve(
                tag,
                b"SPSEQ-FC/testing/BLS12381G1_XMD:SHA-256_SSWU_RO_",
                &[],
            )
        };
        let pp = Params::new(
            make(b"u"),
            make(b"h0"),
            (0..6)
                .map(|i| make(format!("attr{i}").as_bytes()))
                .collect(),
            (0..4)
                .map(|i| make(format!("pool{i}").as_bytes()))
                .collect(),
        )
        .unwrap();
        let keys = keygen(&mut rng);
        let mut parent = vec![pp.u];
        parent.extend((1..8).map(|_| G1::generator() * random_nonzero(&mut rng)));
        let (sig, dk) = sign(&pp, &keys.sk, &parent, &mut rng).unwrap();
        (rng, pp, keys, parent, sig, dk)
    }

    fn signed_child(parent: &[G1], keys: &KeyPair, rng: &mut impl RngCore) -> (Vec<G1>, Sig) {
        let mut message = parent.to_vec();
        message.push(G1::generator() * random_nonzero(rng));
        let y = random_nonzero(rng);
        let inverse = Option::<S>::from(y.invert()).unwrap();
        let z = message
            .iter()
            .zip(&keys.sk)
            .map(|(m, x)| *m * *x)
            .sum::<G1>()
            * inverse;
        (
            message,
            Sig {
                z,
                y: G1::generator() * y,
                yhat: G2::generator() * y,
            },
        )
    }

    #[test]
    fn every_derivation_key_part_is_checked() {
        let (_, pp, keys, _, sig, dk) = fixture();
        for component in 0..2 + dk.attrs.len() + dk.pools.len() {
            let mut bad = dk.clone();
            let point = if component == 0 {
                &mut bad.k0
            } else if component == 1 {
                &mut bad.ka
            } else if component < 2 + bad.attrs.len() {
                &mut bad.attrs[component - 2]
            } else {
                &mut bad.pools[component - 2 - dk.attrs.len()]
            };
            *point += G1::generator();
            assert!(!verify_dk(&pp, &keys.vk, &sig, &bad));
        }
    }

    #[test]
    fn malformed_dimensions_and_zero_scale_fail() {
        let (mut rng, pp, keys, parent, sig, _) = fixture();
        assert!(!verify(&pp, &keys.vk[..8], &parent, &sig));
        assert!(!verify(&pp, &keys.vk, &parent[..7], &sig));
        assert!(chg_rep(&pp, &keys.vk, &parent, &sig, S::ZERO, &mut rng).is_err());
    }
    #[test]
    fn native_signature_checks_preserve_parent_and_child_equations() {
        let (mut rng, pp, keys, parent, sig, _) = fixture();
        assert!(verify_signature_native(&pp, &keys.vk, &parent, &sig));
        let input = signature_equations(&pp, &keys.vk, &parent, &sig).unwrap();
        let result = crate::pairing_batch::verify_each(&input).unwrap();
        assert_eq!(result.equations, 2);
        assert_eq!(result.executed_miller_terms, 11);
        assert_eq!(result.final_exponentiations, 2);
        let (message, child) = signed_child(&parent, &keys, &mut rng);
        assert!(verify_signature_native(&pp, &keys.vk, &message, &child));
        let input = signature_equations(&pp, &keys.vk, &message, &child).unwrap();
        let result = crate::pairing_batch::verify_each(&input).unwrap();
        assert_eq!(result.equations, 2);
        assert_eq!(result.executed_miller_terms, 12);
        assert_eq!(result.final_exponentiations, 2);
        let mut changed = child;
        changed.z += G1::generator();
        assert!(!verify_signature_native(&pp, &keys.vk, &message, &changed));
    }

    #[test]
    fn native_signature_rejects_cancelling_distinct_equations() {
        let (_, pp, keys, parent, mut signature, _) = fixture();
        signature.z -= G1::generator();
        signature.y *= S::from(2);
        let equations = signature_equations(&pp, &keys.vk, &parent, &signature).unwrap();
        assert!(equations.iter().all(|eq| multi_pair(eq) != Gt::identity()));
        let product: Vec<_> = equations.iter().flatten().copied().collect();
        assert_eq!(multi_pair(&product), Gt::identity());
        assert!(!verify_signature_native(&pp, &keys.vk, &parent, &signature));
        assert!(!verify(&pp, &keys.vk, &parent, &signature));
    }

    #[test]
    fn identity_parent_or_child_message_is_rejected() {
        let (mut rng, pp, keys, parent, sig, _) = fixture();
        for j in 0..8 {
            let mut changed = parent.clone();
            changed[j] = G1::identity();
            assert!(sign(&pp, &keys.sk, &changed, &mut rng).is_err());
            assert!(!verify(&pp, &keys.vk, &changed, &sig));
            assert!(signature_equations(&pp, &keys.vk, &changed, &sig).is_none());
        }
        let mut child = parent;
        child.push(G1::identity());
        assert!(!verify(&pp, &keys.vk, &child, &sig));
        assert!(chg_rep(&pp, &keys.vk, &child, &sig, S::ONE, &mut rng).is_err());
    }

    #[test]
    fn installed_signature_and_chg_rep_match_raw_bytes_and_rng() {
        let (mut rng, pp, keys, parent, sig, _) = fixture();
        assert!(validate_instance(&pp, &keys.vk));
        let (child, child_signature) = signed_child(&parent, &keys, &mut rng);
        for (message, signature) in [(&parent, &sig), (&child, &child_signature)] {
            assert_eq!(
                signature_equations(&pp, &keys.vk, message, signature),
                signature_equations_installed(&keys.vk, message, signature)
            );
            for mu in [S::ONE, S::from(7), S::from(197_025)] {
                let mut raw_rng = StdRng::seed_from_u64(197_200);
                let mut installed_rng = raw_rng.clone();
                let raw = chg_rep(&pp, &keys.vk, message, signature, mu, &mut raw_rng).unwrap();
                let installed =
                    chg_rep_installed(message, signature, mu, &mut installed_rng).unwrap();
                assert_eq!(raw.0, installed.0);
                assert_eq!(raw.1.encode(), installed.1.encode());
                assert_eq!(raw_rng.next_u64(), installed_rng.next_u64());
                assert!(verify(&pp, &keys.vk, &installed.0, &installed.1));
            }
        }
    }

    #[test]
    fn installed_operations_reject_malformed_messages_and_signatures() {
        let (mut rng, pp, keys, parent, signature, _) = fixture();
        let mut malformed = vec![vec![], parent[..7].to_vec()];
        let mut too_long = parent.clone();
        too_long.extend([G1::generator(); 2]);
        malformed.push(too_long);
        for j in 0..parent.len() {
            let mut message = parent.clone();
            message[j] = G1::identity();
            malformed.push(message);
        }
        let one = G1::generator().z();
        #[allow(clippy::eq_op)]
        let zero = one - one;
        let torsion = G1::from_raw_unchecked(zero, one + one, one);
        let off_curve = G1::from_raw_unchecked(zero, one, one);
        for point in [torsion, off_curve] {
            let mut message = parent.clone();
            message[1] = point;
            malformed.push(message);
        }
        for message in malformed {
            assert!(signature_equations_installed(&keys.vk, &message, &signature).is_none());
            assert!(signature_equations(&pp, &keys.vk, &message, &signature).is_none());
            assert!(chg_rep_installed(&message, &signature, S::ONE, &mut rng).is_err());
            assert!(chg_rep(&pp, &keys.vk, &message, &signature, S::ONE, &mut rng).is_err());
        }
        let mut malformed_signatures = Vec::new();
        for j in 0..4 {
            let mut bad = signature.clone();
            match j {
                0 => bad.y = G1::identity(),
                1 => bad.yhat = G2::identity(),
                2 => bad.y = torsion,
                _ => bad.z = off_curve,
            }
            malformed_signatures.push(bad);
        }
        for bad in malformed_signatures {
            assert!(signature_equations_installed(&keys.vk, &parent, &bad).is_none());
            assert!(chg_rep_installed(&parent, &bad, S::ONE, &mut rng).is_err());
        }
        assert!(chg_rep_installed(&parent, &signature, S::ZERO, &mut rng).is_err());
        assert!(signature_equations_installed(&keys.vk[..8], &parent, &signature).is_none());
        // Algebraic corruption is retained as a residual, rather than being
        // mislabeled a shape error; native equation checks reject it.
        let mut corrupted = signature;
        corrupted.z += G1::generator();
        let equations = signature_equations_installed(&keys.vk, &parent, &corrupted).unwrap();
        assert!(
            !crate::pairing_batch::verify_each(&equations)
                .unwrap()
                .accepted
        );
        let mut bad_pp = pp.clone();
        bad_pp.u = G1::identity();
        assert!(!validate_instance(&bad_pp, &keys.vk));
        assert!(!validate_instance(&pp, &keys.vk[..8]));
        let mut bad_vk = keys.vk;
        bad_vk[0] = G2::identity();
        assert!(!validate_instance(&pp, &bad_vk));
    }
    #[test]
    fn installed_recipient_proof_binds_digest_issuer_session_key_and_first_message() {
        let digest = [0x21; 32];
        let issuer_public = b"accepted issuer public key";
        let mut rng = StdRng::seed_from_u64(207_001);
        let request = request_installed(
            &digest,
            issuer_public,
            b"before any parent is received",
            S::from(41),
            &mut rng,
        )
        .unwrap();
        assert!(verify_request_installed(&digest, issuer_public, &request));
        let mut other_digest = digest;
        other_digest[7] ^= 1;
        assert!(!verify_request_installed(
            &other_digest,
            issuer_public,
            &request
        ));
        assert!(!verify_request_installed(
            &digest,
            b"other issuer",
            &request
        ));
        for field in 0..4 {
            let mut changed = request.clone();
            match field {
                0 => changed.sid.push(1),
                1 => changed.pka += G1::generator(),
                2 => changed.proof.a += G1::generator(),
                _ => changed.proof.z += S::ONE,
            }
            assert!(!verify_request_installed(&digest, issuer_public, &changed));
        }
    }

    #[test]
    fn installed_recipient_proof_rejects_bad_dynamic_inputs() {
        let digest = [0x21; 32];
        let issuer_public = b"accepted issuer public key";
        let mut rng = StdRng::seed_from_u64(207_002);
        for (issuer, sid, secret) in [
            (&b""[..], &b"sid"[..], S::ONE),
            (&issuer_public[..], &b""[..], S::ONE),
            (&issuer_public[..], &b"sid"[..], S::ZERO),
        ] {
            assert!(request_installed(&digest, issuer, sid, secret, &mut rng).is_err());
        }
        let request = request_installed(&digest, issuer_public, b"sid", S::ONE, &mut rng).unwrap();
        assert!(!verify_request_installed(&digest, b"", &request));
        let mut empty_session = request.clone();
        empty_session.sid.clear();
        assert!(!verify_request_installed(
            &digest,
            issuer_public,
            &empty_session
        ));
        let mut identity_key = request.clone();
        identity_key.pka = G1::identity();
        assert!(!verify_request_installed(
            &digest,
            issuer_public,
            &identity_key
        ));
        let one = G1::generator().z();
        #[allow(clippy::eq_op)]
        let zero = one - one;
        let torsion = G1::from_raw_unchecked(zero, one + one, one);
        let off_curve = G1::from_raw_unchecked(zero, one, one);
        for point in [torsion, off_curve] {
            for field in 0..2 {
                let mut changed = request.clone();
                if field == 0 {
                    changed.pka = point;
                } else {
                    changed.proof.a = point;
                }
                assert!(!verify_request_installed(&digest, issuer_public, &changed));
            }
        }
    }
}
