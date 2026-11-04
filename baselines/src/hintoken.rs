//! HinToken, author artifact DOI 10.5281/zenodo.18681789, on BLS12-381.
//! Native issuance OR proof, normalized ciphertext and SPS-EQ signature.
//! Verify and designated-reader Read are separate; randomness is verifier-owned.
use crate::{
    arithmetic::*,
    batch::{self, FhsStatement},
    canonical,
};
use ff::Field;
use group::Group;
use rand::RngCore;
use sha2::{Digest, Sha256, Sha512};
use std::collections::{BTreeMap, BTreeSet};

pub type Result<T> = std::result::Result<T, &'static str>;
#[derive(Clone, Debug)]
pub struct Signature {
    pub z: G1,
    pub y: G1,
    pub yh: G2,
}
#[derive(Clone, Debug)]
pub struct ReaderPublic {
    pub point: G1,
}
pub struct ReaderSecret(S);
pub struct IssuerSecret([S; 4]);
#[derive(Clone, Debug)]
pub struct IssuerPublic {
    pub points: [G2; 4],
}
#[derive(Clone)]
pub struct InstalledIssuer {
    public: IssuerPublic,
    anchor: GT,
    id: [u8; 32],
}
#[derive(Clone, Debug)]
pub struct Request {
    pub g_prime: G1,
    pub h: G1,
}
pub struct Pending {
    reader: ReaderPublic,
    request: Request,
    z: S,
}
#[derive(Clone, Debug)]
pub struct BitProof {
    pub gamma: S,
    pub c0: S,
    pub z0: S,
    pub c1: S,
    pub z1: S,
}
#[derive(Clone, Debug)]
pub struct Response {
    pub u: G1,
    pub v: G1,
    pub proof: BitProof,
    pub signature: Signature,
}
/// Native TokenLite omits the public first coordinate g1. Its normalized
/// ciphertext is the stable signed message; signature rerandomization does not
/// create a new message identifier.
#[derive(Clone, Debug)]
pub struct Token {
    pub h: G1,
    pub u: G1,
    pub v: G1,
    pub signature: Signature,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerificationMode {
    Specification,
    Randomized,
    RandomizedCachedAnchor,
}

impl IssuerPublic {
    pub fn encode(&self) -> Vec<u8> {
        self.points.iter().flat_map(|p| p.to_compressed()).collect()
    }
    pub fn install(&self) -> Result<InstalledIssuer> {
        if self.points.iter().any(|&p| !valid2(p, true)) {
            return Err("invalid HinToken issuer key");
        }
        Ok(InstalledIssuer {
            public: self.clone(),
            anchor: pair(G1::generator(), self.points[0]),
            id: Sha256::digest(self.encode()).into(),
        })
    }
}
impl InstalledIssuer {
    pub fn id(&self) -> [u8; 32] {
        self.id
    }
    pub fn public(&self) -> &IssuerPublic {
        &self.public
    }
}
impl ReaderPublic {
    pub fn encode(&self) -> [u8; 48] {
        self.point.to_compressed()
    }
}
pub fn issuer_keygen(rng: &mut impl RngCore) -> (IssuerPublic, IssuerSecret) {
    let x = std::array::from_fn(|_| random_nonzero(rng));
    (
        IssuerPublic {
            points: x.map(|s| g2_mul(G2::generator(), s)),
        },
        IssuerSecret(x),
    )
}
pub fn reader_keygen(rng: &mut impl RngCore) -> (ReaderPublic, ReaderSecret) {
    let x = random_nonzero(rng);
    (
        ReaderPublic {
            point: g1_mul(G1::generator(), x),
        },
        ReaderSecret(x),
    )
}
pub fn request(reader: &ReaderPublic, rng: &mut impl RngCore) -> Result<(Request, Pending)> {
    if !valid1(reader.point, true) {
        return Err("invalid HinToken reader key");
    }
    let z = random_nonzero(rng);
    let r = Request {
        g_prime: g1_mul(G1::generator(), inv(z)),
        h: g1_mul(G1::generator(), random_nonzero(rng)),
    };
    Ok((
        r.clone(),
        Pending {
            reader: reader.clone(),
            request: r,
            z,
        },
    ))
}
/// The author's ark-bls12-381 0.5 serializer uses standard compressed BLS
/// point bytes, matching blstrs. Its Fr transcript bytes remain little-endian.
/// This is checked against a fixed transcript executed in the author crate.
fn author_g1(point: G1) -> [u8; 48] {
    point.to_compressed()
}
fn challenge(reader: &ReaderPublic, h: G1, u: G1, v: G1, gamma: S, a: [G1; 4]) -> S {
    let mut hash = Sha512::new();
    hash.update(b"hintoken.readbit.fs_chal.v1");
    for p in [
        G1::generator(),
        reader.point,
        h,
        u,
        v,
        a[0],
        a[1],
        a[2],
        a[3],
    ] {
        let b = author_g1(p);
        hash.update((b.len() as u32).to_be_bytes());
        hash.update(b);
    }
    let b = gamma.to_bytes_le();
    hash.update((b.len() as u32).to_be_bytes());
    hash.update(b);
    // Exact from_be_bytes_mod_order on the 512-bit author digest.
    hash.finalize()
        .iter()
        .fold(S::ZERO, |acc, &b| acc * S::from(256) + S::from(b as u64))
}
fn prove_bit(
    reader: &ReaderPublic,
    h: G1,
    u: G1,
    v: G1,
    r: S,
    bit: u8,
    rng: &mut impl RngCore,
) -> BitProof {
    let gamma = random_scalar(rng);
    let alpha = random_scalar(rng);
    let fake_c = random_scalar(rng);
    let nonce = random_scalar(rng);
    let u1 = sum1(&[(G1::generator(), gamma), (u, -S::ONE)]);
    let v1 = sum1(&[(reader.point, gamma), (h, S::ONE), (v, -S::ONE)]);
    let fake_bases = if bit == 0 { (u1, v1) } else { (u, v) };
    let fake = [
        sum1(&[(G1::generator(), alpha), (fake_bases.0, -fake_c)]),
        sum1(&[(reader.point, alpha), (fake_bases.1, -fake_c)]),
    ];
    let real = [g1_mul(G1::generator(), nonce), g1_mul(reader.point, nonce)];
    let a = if bit == 0 {
        [real[0], real[1], fake[0], fake[1]]
    } else {
        [fake[0], fake[1], real[0], real[1]]
    };
    let real_c = challenge(reader, h, u, v, gamma, a) - fake_c;
    let real_z = nonce + real_c * if bit == 0 { r } else { gamma - r };
    if bit == 0 {
        BitProof {
            gamma,
            c0: real_c,
            z0: real_z,
            c1: fake_c,
            z1: alpha,
        }
    } else {
        BitProof {
            gamma,
            c0: fake_c,
            z0: alpha,
            c1: real_c,
            z1: real_z,
        }
    }
}
fn verify_bit(reader: &ReaderPublic, h: G1, u: G1, v: G1, proof: &BitProof) -> bool {
    let u1 = sum1(&[(G1::generator(), proof.gamma), (u, -S::ONE)]);
    let v1 = sum1(&[(reader.point, proof.gamma), (h, S::ONE), (v, -S::ONE)]);
    let a = [
        sum1(&[(G1::generator(), proof.z0), (u, -proof.c0)]),
        sum1(&[(reader.point, proof.z0), (v, -proof.c0)]),
        sum1(&[(G1::generator(), proof.z1), (u1, -proof.c1)]),
        sum1(&[(reader.point, proof.z1), (v1, -proof.c1)]),
    ];
    challenge(reader, h, u, v, proof.gamma, a) == proof.c0 + proof.c1
}
fn signature_shape(sig: &Signature) -> bool {
    valid1(sig.z, false) && valid1(sig.y, true) && valid2(sig.yh, true)
}
fn token_identity_shape(token: &Token) -> bool {
    token.h != G1::identity()
        && token.signature.y != G1::identity()
        && token.signature.yh != G2::identity()
}
fn token_shape(token: &Token) -> bool {
    valid1(token.h, true)
        && valid1(token.u, false)
        && valid1(token.v, false)
        && signature_shape(&token.signature)
}
fn sign(sk: &IssuerSecret, message: &[G1; 4], rng: &mut impl RngCore) -> Signature {
    let r = random_nonzero(rng);
    let product = sum1(
        &message
            .iter()
            .zip(sk.0)
            .map(|(&p, s)| (p, s))
            .collect::<Vec<_>>(),
    );
    Signature {
        z: g1_mul(product, r),
        y: g1_mul(G1::generator(), inv(r)),
        yh: g2_mul(G2::generator(), inv(r)),
    }
}
pub fn issue(
    sk: &IssuerSecret,
    reader: &ReaderPublic,
    req: &Request,
    bit: u8,
    rng: &mut impl RngCore,
) -> Result<Response> {
    issue_body(sk, reader, req, bit, rng, false)
}
pub struct ReceivedRequest(Request);
impl ReceivedRequest {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        Request::decode(bytes).map(Self)
    }
}
pub fn issue_received(
    sk: &IssuerSecret,
    reader: &ReaderPublic,
    req: ReceivedRequest,
    bit: u8,
    rng: &mut impl RngCore,
) -> Result<Response> {
    issue_body(sk, reader, &req.0, bit, rng, true)
}
fn issue_body(
    sk: &IssuerSecret,
    reader: &ReaderPublic,
    req: &Request,
    bit: u8,
    rng: &mut impl RngCore,
    decoded: bool,
) -> Result<Response> {
    if bit > 1
        || !valid1(reader.point, true)
        || (!decoded && (!valid1(req.g_prime, true) || !valid1(req.h, true)))
    {
        return Err("invalid HinToken issuance input");
    }
    let r = random_scalar(rng);
    let u = g1_mul(G1::generator(), r);
    let v = sum1(&[(reader.point, r), (req.h, S::from(bit as u64))]);
    let proof = prove_bit(reader, req.h, u, v, r, bit, rng);
    let signature = sign(sk, &[req.g_prime, req.h, u, v], rng);
    Ok(Response {
        u,
        v,
        proof,
        signature,
    })
}
/// Author User1: validate plaintext-legitimacy proof, then change
/// representation. The returned token is independently verified by Verify.
/// A malformed issuer signature is not silently made valid by this operation.
pub fn receive(pending: Pending, response: &Response, rng: &mut impl RngCore) -> Result<Token> {
    receive_body(pending, response, rng, false)
}
pub struct ReceivedResponse(Response);
impl ReceivedResponse {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        Response::decode(bytes).map(Self)
    }
}
pub fn receive_received(
    pending: Pending,
    response: ReceivedResponse,
    rng: &mut impl RngCore,
) -> Result<Token> {
    receive_body(pending, &response.0, rng, true)
}
fn receive_body(
    pending: Pending,
    response: &Response,
    rng: &mut impl RngCore,
    decoded: bool,
) -> Result<Token> {
    if response.signature.y == G1::identity()
        || response.signature.yh == G2::identity()
        || (!decoded
            && (!valid1(response.u, false)
                || !valid1(response.v, false)
                || !signature_shape(&response.signature)))
        || !verify_bit(
            &pending.reader,
            pending.request.h,
            response.u,
            response.v,
            &response.proof,
        )
    {
        return Err("HinToken issuer response rejected");
    }
    let psi = random_nonzero(rng);
    Ok(Token {
        h: g1_mul(pending.request.h, pending.z),
        u: g1_mul(response.u, pending.z),
        v: g1_mul(response.v, pending.z),
        signature: Signature {
            z: g1_mul(response.signature.z, psi * pending.z),
            y: g1_mul(response.signature.y, inv(psi)),
            yh: g2_mul(response.signature.yh, inv(psi)),
        },
    })
}
/// Sealed exact-shape canonical received token; fields remain immutable.
#[derive(Clone)]
pub struct CheckedToken {
    token: Token,
}
impl CheckedToken {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        Ok(Self {
            token: Token::decode(bytes)?,
        })
    }
    pub fn as_token(&self) -> &Token {
        &self.token
    }
}
fn statement(token: &Token) -> FhsStatement {
    FhsStatement {
        message: vec![G1::generator(), token.h, token.u, token.v],
        z: token.signature.z,
        y: token.signature.y,
        yh: token.signature.yh,
    }
}
pub fn verify(
    issuer: &InstalledIssuer,
    token: &Token,
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    verify_inner(issuer, token, mode, false, rng)
}
fn verify_inner(
    issuer: &InstalledIssuer,
    token: &Token,
    mode: VerificationMode,
    decoded: bool,
    rng: &mut impl RngCore,
) -> bool {
    if !token_identity_shape(token) || (!decoded && !token_shape(token)) {
        return false;
    }
    if mode != VerificationMode::Specification {
        return verify_batch_inner(issuer, std::slice::from_ref(token), mode, decoded, rng);
    }
    let mut terms = vec![(-token.signature.z, token.signature.yh)];
    terms.extend(
        [G1::generator(), token.h, token.u, token.v]
            .iter()
            .zip(issuer.public.points)
            .map(|(&g, h)| (g, h)),
    );
    if multi_pair(&terms) != GT::identity() {
        return false;
    }
    multi_pair(&[
        (token.signature.y, G2::generator()),
        (-G1::generator(), token.signature.yh),
    ]) == GT::identity()
}
pub fn verify_batch(
    issuer: &InstalledIssuer,
    tokens: &[Token],
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    verify_batch_inner(issuer, tokens, mode, false, rng)
}
pub fn verify_batch_checked(
    issuer: &InstalledIssuer,
    tokens: &[CheckedToken],
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    let frozen = tokens.iter().map(|t| t.token.clone()).collect::<Vec<_>>();
    verify_batch_inner(issuer, &frozen, mode, true, rng)
}
fn verify_batch_inner(
    issuer: &InstalledIssuer,
    tokens: &[Token],
    mode: VerificationMode,
    decoded: bool,
    rng: &mut impl RngCore,
) -> bool {
    if tokens.is_empty()
        || tokens
            .iter()
            .any(|t| !token_identity_shape(t) || (!decoded && !token_shape(t)))
    {
        return false;
    }
    let mut identifiers = BTreeSet::new();
    if tokens.iter().any(|t| !identifiers.insert(t.message_id())) {
        return false;
    }
    if mode == VerificationMode::Specification {
        return tokens
            .iter()
            .all(|t| verify_inner(issuer, t, mode, decoded, rng));
    }
    let fixed: Vec<_> = tokens.iter().map(statement).collect();
    if decoded && mode == VerificationMode::RandomizedCachedAnchor {
        batch::fhs_random_with_anchor_checked(&issuer.public.points, &fixed, issuer.anchor, rng)
    } else if decoded {
        batch::fhs_random_checked(&issuer.public.points, &fixed, rng)
    } else if mode == VerificationMode::RandomizedCachedAnchor {
        batch::fhs_random_with_anchor(&issuer.public.points, &fixed, issuer.anchor, rng)
    } else {
        batch::fhs_random(&issuer.public.points, &fixed, rng)
    }
}
/// Each independently installed issuer owns a separate aggregation group.
/// Tokens are immutable and the outer slice fixes every issuer binding first.
pub fn verify_grouped(
    groups: &[(&InstalledIssuer, Vec<Token>)],
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    if groups.is_empty() {
        return false;
    }
    let mut all = BTreeSet::new();
    let mut joined: BTreeMap<[u8; 32], (&InstalledIssuer, Vec<Token>)> = BTreeMap::new();
    for (issuer, tokens) in groups {
        if tokens.is_empty()
            || tokens
                .iter()
                .any(|t| !token_shape(t) || !all.insert((issuer.id(), t.message_id())))
        {
            return false;
        }
        joined
            .entry(issuer.id())
            .or_insert((*issuer, vec![]))
            .1
            .extend(tokens.iter().cloned());
    }
    joined
        .values()
        .all(|(issuer, tokens)| verify_batch(issuer, tokens, mode, rng))
}
pub struct VerifiedToken {
    token: Token,
}
pub fn verify_batch_records_checked(
    issuer: &InstalledIssuer,
    tokens: &[CheckedToken],
    mode: VerificationMode,
    weights: &mut impl RngCore,
) -> Option<Vec<VerifiedToken>> {
    verify_batch_checked(issuer, tokens, mode, weights).then(|| {
        tokens
            .iter()
            .map(|t| VerifiedToken {
                token: t.token.clone(),
            })
            .collect()
    })
}
pub fn read_bit_validated(secret: &ReaderSecret, record: &VerifiedToken) -> Option<u8> {
    read_bit_body(secret, &record.token)
}
/// One scalar multiplication per token; no signature verification is hidden in
/// this extraction-only endpoint. Callers can explicitly choose read_total.
pub fn read_bit(secret: &ReaderSecret, token: &Token) -> Option<u8> {
    if !valid1(token.h, true) || !valid1(token.u, false) || !valid1(token.v, false) {
        return None;
    }
    read_bit_body(secret, token)
}
fn read_bit_body(secret: &ReaderSecret, token: &Token) -> Option<u8> {
    let decrypted = sum1(&[(token.v, S::ONE), (token.u, -secret.0)]);
    if decrypted == G1::identity() {
        Some(0)
    } else if decrypted == token.h {
        Some(1)
    } else {
        None
    }
}
pub fn read_total(
    secret: &ReaderSecret,
    issuer: &InstalledIssuer,
    token: &Token,
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> Option<u8> {
    verify(issuer, token, mode, rng)
        .then(|| read_bit(secret, token))
        .flatten()
}
pub fn read_total_checked(
    secret: &ReaderSecret,
    issuer: &InstalledIssuer,
    token: &CheckedToken,
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> Option<u8> {
    verify_inner(issuer, &token.token, mode, true, rng)
        .then(|| read_bit_body(secret, &token.token))
        .flatten()
}
impl Request {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != 96 {
            return Err("incorrect HinToken request length");
        }
        let g_prime =
            canonical::decode_g1(&bytes[..48]).map_err(|_| "invalid HinToken request point")?;
        let h = canonical::decode_g1(&bytes[48..]).map_err(|_| "invalid HinToken request point")?;
        if g_prime == G1::identity() || h == G1::identity() {
            return Err("invalid HinToken request domain");
        }
        Ok(Self { g_prime, h })
    }
    pub fn encode(&self) -> Vec<u8> {
        [self.g_prime, self.h]
            .iter()
            .flat_map(|p| p.to_compressed())
            .collect()
    }
}
impl Response {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != 448 {
            return Err("incorrect HinToken response length");
        }
        let g1 = |range: std::ops::Range<usize>| {
            canonical::decode_g1(&bytes[range]).map_err(|_| "invalid HinToken response point")
        };
        let x: Vec<S> = bytes[96..256]
            .chunks_exact(32)
            .map(|b| canonical::decode_scalar(b).map_err(|_| "invalid HinToken proof scalar"))
            .collect::<Result<_>>()?;
        let response = Self {
            u: g1(0..48)?,
            v: g1(48..96)?,
            proof: BitProof {
                gamma: x[0],
                c0: x[1],
                z0: x[2],
                c1: x[3],
                z1: x[4],
            },
            signature: Signature {
                z: g1(256..304)?,
                y: g1(304..352)?,
                yh: canonical::decode_g2(&bytes[352..448])
                    .map_err(|_| "invalid HinToken response G2")?,
            },
        };
        if response.signature.y == G1::identity()
            || response.signature.yh == G2::identity()
            || response.encode() != bytes
        {
            return Err("invalid HinToken response domain");
        }
        Ok(response)
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut b = Vec::new();
        for p in [self.u, self.v] {
            b.extend(p.to_compressed())
        }
        for s in [
            self.proof.gamma,
            self.proof.c0,
            self.proof.z0,
            self.proof.c1,
            self.proof.z1,
        ] {
            b.extend(s.to_bytes_be())
        }
        b.extend(self.signature.z.to_compressed());
        b.extend(self.signature.y.to_compressed());
        b.extend(self.signature.yh.to_compressed());
        b
    }
}
impl Token {
    pub const WIRE_BYTES: usize = 5 * 48 + 96;
    pub fn encode(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(Self::WIRE_BYTES);
        for p in [self.h, self.u, self.v, self.signature.z, self.signature.y] {
            b.extend(p.to_compressed())
        }
        b.extend(self.signature.yh.to_compressed());
        b
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != Self::WIRE_BYTES {
            return Err("incorrect HinToken token length");
        }
        let p: std::result::Result<Vec<_>, _> = bytes[..240]
            .chunks_exact(48)
            .map(canonical::decode_g1)
            .collect();
        let p = p.map_err(|_| "invalid HinToken G1 encoding/subgroup")?;
        let yh = canonical::decode_g2(&bytes[240..])
            .map_err(|_| "invalid HinToken G2 encoding/subgroup")?;
        let token = Self {
            h: p[0],
            u: p[1],
            v: p[2],
            signature: Signature {
                z: p[3],
                y: p[4],
                yh,
            },
        };
        if !token_identity_shape(&token) || token.encode() != bytes {
            return Err("invalid HinToken token domain");
        }
        Ok(token)
    }
    pub fn message_id(&self) -> Vec<u8> {
        [self.h, self.u, self.v]
            .iter()
            .flat_map(|p| p.to_compressed())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    struct NoCoins;
    impl RngCore for NoCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("coins before input rejection")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("coins before input rejection")
        }
        fn fill_bytes(&mut self, _: &mut [u8]) {
            panic!("coins before input rejection")
        }
        fn try_fill_bytes(&mut self, _: &mut [u8]) -> std::result::Result<(), rand::Error> {
            panic!("coins before input rejection")
        }
    }
    fn mint(
        pk: &IssuerPublic,
        sk: &IssuerSecret,
        reader: &ReaderPublic,
        bit: u8,
        rng: &mut StdRng,
    ) -> Token {
        let (req, pending) = request(reader, rng).unwrap();
        let response = issue(sk, reader, &req, bit, rng).unwrap();
        assert_eq!(req.encode().len(), 96);
        assert_eq!(response.encode().len(), 448);
        assert_eq!(
            Request::decode(&req.encode()).unwrap().encode(),
            req.encode()
        );
        let response = Response::decode(&response.encode()).unwrap();
        let token = receive(pending, &response, rng).unwrap();
        assert!(verify(
            &pk.install().unwrap(),
            &token,
            VerificationMode::Specification,
            rng
        ));
        token
    }
    #[test]
    fn author_arkworks_fixed_transcript_matches_blstrs() {
        let g = G1::generator();
        let c = challenge(
            &ReaderPublic {
                point: g1_mul(g, S::from(7)),
            },
            g1_mul(g, S::from(11)),
            g1_mul(g, S::from(17)),
            g1_mul(g, S::from(19)),
            S::from(13),
            [23, 29, 31, 37].map(|n| g1_mul(g, S::from(n))),
        );
        let hex: String = c.to_bytes_le().iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "a963278a5b104f60f02cd13b7f2044333bd9691ab078c608d106ff94328e4235"
        );
        for (bit,hex) in [(0u64,"88c522e40e4d57abd3386ff6cb2c5496d767606488f3c9f9494cd363741d4e67bcf9474ec612f8409fc6122f5153de16be4fa5d18b5da7cfe40576c2633817475e5e74e5ce73ad46f3e8f81d645bf8c8be5d82b2e1ad0303da75298bc70b300a1fdee53364149a7f6741a842733240f43d0eb52b74850f966714d4a3e62655577ec074aa4ff3bb0e5113c23ff7afd33a4d2c1601abd32f6ff2c691e40e1eb55f"),(1u64,"63a1e81b0f33b16fb1a3c7e497804689b050585e773db475e27628c4c711203b46f99b3802fc63ddf69c0449929c1a734858df2dd7016c93694d6a73adc6e400b661ee83e8e0a40b0498181123ec7249c3fd544ea270dc251a41f9b2a9b822062fa7f1c425d9315a6b166219d894b35d7bfba4d579fdedc6b8411b02eef9fd0a4dc911192360b8ff1fbfef1a51b5b9c89bd91ca248680529b39a397002c26c58")] {
            let bytes:Vec<_>=hex.as_bytes().chunks_exact(2).map(|s|u8::from_str_radix(std::str::from_utf8(s).unwrap(),16).unwrap()).collect();
            let x:Vec<_>=bytes.chunks_exact(32).map(|b|Option::<S>::from(S::from_bytes_le(b.try_into().unwrap())).unwrap()).collect();
            let mut proof=BitProof{gamma:x[0],c0:x[1],z0:x[2],c1:x[3],z1:x[4]};
            let reader=ReaderPublic{point:g1_mul(g,S::from(7))};
            assert!(verify_bit(&reader,g1_mul(g,S::from(11)),g1_mul(g,S::from(17)),g1_mul(g,S::from(119+11*bit)),&proof));
            proof.z0+=S::ONE;
            assert!(!verify_bit(&reader,g1_mul(g,S::from(11)),g1_mul(g,S::from(17)),g1_mul(g,S::from(119+11*bit)),&proof));
        }
    }
    #[test]
    fn native_issue_verify_read_both_bits_and_canonical_codec() {
        let mut rng = StdRng::seed_from_u64(212301);
        let (pk, sk) = issuer_keygen(&mut rng);
        let ip = pk.install().unwrap();
        let (rp, rs) = reader_keygen(&mut rng);
        for bit in [0, 1] {
            let token = mint(&pk, &sk, &rp, bit, &mut rng);
            assert_eq!(token.encode().len(), 336);
            for mode in [
                VerificationMode::Specification,
                VerificationMode::Randomized,
                VerificationMode::RandomizedCachedAnchor,
            ] {
                start_counts();
                assert!(verify(&ip, &token, mode, &mut rng));
                let counts = stop_counts();
                if mode == VerificationMode::Specification {
                    assert_eq!(counts.p + counts.mp_terms, 7);
                    assert_eq!(counts.p + counts.mp_calls, 2);
                }

                assert_eq!(read_total(&rs, &ip, &token, mode, &mut rng), Some(bit));
            }
            assert_eq!(read_bit(&rs, &token), Some(bit));
            let wire = token.encode();
            assert_eq!(Token::decode(&wire).unwrap().encode(), wire);
            let mut extra = wire.clone();
            extra.push(0);
            assert!(Token::decode(&extra).is_err());
            let mut bad = wire;
            bad[..48].fill(0xff);
            assert!(Token::decode(&bad).is_err());
        }
    }
    #[test]
    fn malformed_issuance_bad_signature_and_wrong_reader_rejected() {
        let mut rng = StdRng::seed_from_u64(212302);
        let (pk, sk) = issuer_keygen(&mut rng);
        let ip = pk.install().unwrap();
        let (rp, rs) = reader_keygen(&mut rng);
        let (_, wrong) = reader_keygen(&mut rng);
        let (req, p) = request(&rp, &mut rng).unwrap();
        let mut response = issue(&sk, &rp, &req, 0, &mut rng).unwrap();
        response.proof.z0 += S::ONE;
        assert!(receive(p, &response, &mut rng).is_err());
        assert!(issue(&sk, &rp, &req, 2, &mut rng).is_err());
        let mut token = mint(&pk, &sk, &rp, 1, &mut rng);
        assert_eq!(read_bit(&wrong, &token), None);
        assert_eq!(read_bit(&rs, &token), Some(1));
        token.signature.z += G1::generator();
        assert!(!verify(&ip, &token, VerificationMode::Randomized, &mut rng));
        assert_eq!(
            read_total(&rs, &ip, &token, VerificationMode::Specification, &mut rng),
            None
        );
        let bad = IssuerPublic {
            points: [G2::identity(); 4],
        };
        assert!(bad.install().is_err());
    }
    #[test]
    fn random_batch_all_sizes_keeps_full_message_identifiers_and_checks_before_coins() {
        let mut rng = StdRng::seed_from_u64(212303);
        let (pk, sk) = issuer_keygen(&mut rng);
        let ip = pk.install().unwrap();
        let (rp, _) = reader_keygen(&mut rng);
        let tokens: Vec<_> = (0..128)
            .map(|i| mint(&pk, &sk, &rp, (i % 2) as u8, &mut rng))
            .collect();
        for k in [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 96, 128] {
            for mode in [
                VerificationMode::Randomized,
                VerificationMode::RandomizedCachedAnchor,
            ] {
                start_counts();
                assert!(verify_batch(&ip, &tokens[..k], mode, &mut rng));
                let c = stop_counts();
                assert_eq!(
                    c.p + c.mp_terms,
                    k as u64
                        + if mode == VerificationMode::Randomized {
                            5
                        } else {
                            4
                        }
                );
                assert_eq!(c.p + c.mp_calls, 1);
            }
        }
        assert_eq!(tokens[0].message_id().len(), 144);
        assert!(!verify_batch(
            &ip,
            &[],
            VerificationMode::Randomized,
            &mut NoCoins
        ));
        assert!(!verify_batch(
            &ip,
            &[tokens[0].clone(), tokens[0].clone()],
            VerificationMode::Randomized,
            &mut NoCoins
        ));
        let mut bad = tokens[..2].to_vec();
        bad[1].signature.y = G1::identity();
        assert!(!verify_batch(
            &ip,
            &bad,
            VerificationMode::Randomized,
            &mut NoCoins
        ));
        let non_subgroup = (1u64..256)
            .find_map(|i| {
                let mut bytes = [0u8; 48];
                bytes[0] = 0x80;
                bytes[40..].copy_from_slice(&i.to_be_bytes());
                let p = Option::<blstrs::G1Affine>::from(
                    blstrs::G1Affine::from_compressed_unchecked(&bytes),
                )?;
                (!bool::from(p.is_torsion_free())).then_some(G1::from(p))
            })
            .expect("non-subgroup point fixture");
        let mut invalid = tokens[0].clone();
        invalid.u = non_subgroup;
        assert!(!verify_batch(
            &ip,
            &[invalid.clone()],
            VerificationMode::Randomized,
            &mut NoCoins
        ));
        assert!(Token::decode(&invalid.encode()).is_err());
        let mut altered = tokens[0].clone();
        let psi = S::from(9);
        altered.signature.z = g1_mul(altered.signature.z, psi);
        altered.signature.y = g1_mul(altered.signature.y, inv(psi));
        altered.signature.yh = g2_mul(altered.signature.yh, inv(psi));
        assert!(verify(
            &ip,
            &altered,
            VerificationMode::Specification,
            &mut rng
        ));
        assert_eq!(altered.message_id(), tokens[0].message_id());
        assert!(!verify_batch(
            &ip,
            &[tokens[0].clone(), altered],
            VerificationMode::Randomized,
            &mut NoCoins
        ));
        let mut bad = tokens[..2].to_vec();
        bad[1].u += G1::generator();
        assert!(!verify_batch(
            &ip,
            &bad,
            VerificationMode::Randomized,
            &mut rng
        ));
    }
    #[test]
    fn issuer_grouping_and_reader_extraction_are_separate() {
        let mut rng = StdRng::seed_from_u64(212304);
        let (pk1, sk1) = issuer_keygen(&mut rng);
        let (pk2, sk2) = issuer_keygen(&mut rng);
        let i1 = pk1.install().unwrap();
        let i2 = pk2.install().unwrap();
        let (rp, rs) = reader_keygen(&mut rng);
        let t1 = mint(&pk1, &sk1, &rp, 0, &mut rng);
        let t2 = mint(&pk2, &sk2, &rp, 1, &mut rng);
        assert!(verify_grouped(
            &[(&i1, vec![t1.clone()]), (&i2, vec![t2.clone()])],
            VerificationMode::Randomized,
            &mut rng
        ));
        assert!(!verify_grouped(
            &[(&i1, vec![t1, t2.clone()])],
            VerificationMode::Randomized,
            &mut rng
        ));
        start_counts();
        assert_eq!(read_bit(&rs, &t2), Some(1));
        let c = stop_counts();
        assert_eq!(c.p + c.mp_terms, 0);
        assert_eq!(c.et, 0);
    }
}
