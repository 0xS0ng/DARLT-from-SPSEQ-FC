//! BHN+26 with a private metadata bit and a three-coordinate SPS-EQ signature.
//! Issuance authenticates the client public key and the nonce-derived pair.
//! Token verification is individual, and the issuer uses its extraction key
//! only after public verification has established an authenticated token.
use crate::arithmetic::*;
use crate::encoding::{hash_fr, Error, Reader, Writer};
use ff::Field;
use group::Group;
use rand::{CryptoRng, RngCore};

pub type Result<T> = crate::encoding::Result<T>;
fn error(s: &str) -> Error {
    Error(s.to_owned())
}
pub const NONCE_BYTES: usize = 32;
const H_GROUP: &[u8] = b"\x4e\x49\x41\x54\x2d\x42\x41\x53\x45\x2d\x33\x44\x2f\x4e\x4f\x4e\x43\x45";
const H_PROOF: &[u8] =
    b"\x4e\x49\x41\x54\x2d\x42\x41\x53\x45\x2d\x33\x44\x2f\x49\x53\x53\x55\x45\x52\x2d\x4f\x52";
const PK_TAG: &[u8] = b"\x4e\x49\x41\x54\x2d\x42\x41\x53\x45\x2d\x33\x44\x2f\x50\x4b\x2f\x76\x31";
const ISSUE_TAG: &[u8] =
    b"\x4e\x49\x41\x54\x2d\x42\x41\x53\x45\x2d\x33\x44\x2f\x49\x53\x53\x55\x45\x2f\x76\x31";
const REQUEST_TAG: &[u8] =
    b"\x4e\x49\x41\x54\x2d\x42\x41\x53\x45\x2d\x33\x44\x2f\x52\x45\x51\x55\x45\x53\x54\x2f\x76\x31";
const TOKEN_TAG: &[u8] =
    b"\x4e\x49\x41\x54\x2d\x42\x41\x53\x45\x2d\x33\x44\x2f\x54\x4f\x4b\x45\x4e\x2f\x76\x31";

#[derive(Clone, Debug, PartialEq)]
pub struct PublicKey {
    pub t: [G1; 2],
    pub y: [G2; 3],
}
/// An immutable public key installed after curve, subgroup and domain checks.
#[derive(Clone)]
pub struct InstalledIssuer {
    key: PublicKey,
    binding: Vec<u8>,
    token_anchor: GT,
}
pub struct IssuerSecret {
    x: [S; 2],
    y: [S; 3],
    binding: Vec<u8>,
}
pub struct IssuerKeys {
    pub public: PublicKey,
    pub secret: IssuerSecret,
}
pub struct ClientKeys {
    alpha: S,
    public: G1,
}
/// A one-use client capability containing fresh SPS representative randomness.
/// Precomputation uses only the client key and protocol-independent randomness.
/// ```compile_fail
/// use baseline_core::bhn26::PreparedObtain;
/// fn cannot_reuse(prepared: PreparedObtain) {
///     drop(prepared);
///     drop(prepared);
/// }
/// ```
pub struct PreparedObtain {
    alpha_inverse: S,
    client_public: G1,
    psi_over_alpha: S,
    psi_inverse: S,
}
/// Independent, one-use issuer randomness for a single issuance. Generator
/// commitments are prepared without client input or the metadata-bit choice.
/// ```compile_fail
/// use baseline_core::bhn26::PreparedIssue;
/// fn cannot_reuse(prepared: PreparedIssue) {
///     drop(prepared);
///     drop(prepared);
/// }
/// ```
pub struct PreparedIssue {
    issuer_binding: Vec<u8>,
    v: S,
    y1: G1,
    y2: G2,
    z: S,
    g_z: G1,
    zu: [S; 3],
    g_zu: [G2; 3],
    simulated_challenge: S,
    simulated_response: S,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Signature {
    pub z: G1,
    pub y1: G1,
    pub y2: G2,
}
/// The compact Fiat-Shamir response contains both branch challenges and all
/// three signing-key responses; its scalar domain is the complete field Fr.
#[derive(Clone, Debug, PartialEq)]
pub struct IssuerProof {
    pub c0: S,
    pub c1: S,
    pub au: S,
    pub av: S,
    pub aw: S,
    pub a0: S,
    pub a1: S,
}
#[derive(Clone, Debug, PartialEq)]
pub struct IssueMessage {
    pub nonce: Vec<u8>,
    pub s: G1,
    pub signature: Signature,
    pub proof: IssuerProof,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub t1: G1,
    pub t2: G1,
    pub signature: Signature,
}
/// Public verification produces this private-field extraction capability.
pub struct VerifiedToken {
    t1: G1,
    t2: G1,
    issuer_binding: Vec<u8>,
}

impl IssuerKeys {
    /// Key generation follows the issuer-known-secret-key model. Registration
    /// of adversarially selected issuer keys is outside this interface.
    pub fn generate(rng: &mut (impl RngCore + CryptoRng)) -> Self {
        let x = std::array::from_fn(|_| random_nonzero(rng));
        let y = std::array::from_fn(|_| random_nonzero(rng));
        let public = PublicKey {
            t: x.map(|s| g1_mul(G1::generator(), s)),
            y: y.map(|s| g2_mul(G2::generator(), s)),
        };
        let binding = public.encode();
        Self {
            public,
            secret: IssuerSecret { x, y, binding },
        }
    }
    pub fn install(&self) -> Result<InstalledIssuer> {
        install(&self.public)
    }
}
impl ClientKeys {
    pub fn generate(rng: &mut (impl RngCore + CryptoRng)) -> Self {
        let alpha = random_nonzero(rng);
        Self {
            alpha,
            public: g1_mul(G1::generator(), alpha),
        }
    }
    pub fn public_key(&self) -> G1 {
        self.public
    }
    pub fn prepare_obtain(&self, rng: &mut (impl RngCore + CryptoRng)) -> PreparedObtain {
        let alpha_inverse = inv(self.alpha);
        let psi = random_nonzero(rng);
        PreparedObtain {
            alpha_inverse,
            client_public: self.public,
            psi_over_alpha: psi * alpha_inverse,
            psi_inverse: inv(psi),
        }
    }
}
impl InstalledIssuer {
    pub fn public_key(&self) -> &PublicKey {
        &self.key
    }
    pub fn encode(&self) -> Vec<u8> {
        self.binding.clone()
    }
    /// Encoding of the recomputable public pairing cache, separate from pk.
    pub fn cache_encoding(&self) -> Vec<u8> {
        enct(self.token_anchor)
    }
}
pub fn install_wire(bytes: &[u8]) -> Result<InstalledIssuer> {
    let key = PublicKey::decode(bytes)?;
    Ok(InstalledIssuer {
        binding: key.encode(),
        token_anchor: pair(G1::generator(), key.y[0]),
        key,
    })
}
/// Validate and cache the native public instance before repeated operations.
pub fn install(key: &PublicKey) -> Result<InstalledIssuer> {
    if !key.t.iter().all(|&g| valid1(g, true)) || !key.y.iter().all(|&g| valid2(g, true)) {
        return Err(error("invalid issuer public key"));
    }
    Ok(InstalledIssuer {
        key: key.clone(),
        binding: key.encode(),
        token_anchor: pair(G1::generator(), key.y[0]),
    })
}

fn put_signature(w: &mut Writer, sig: &Signature) {
    w.g1(sig.z);
    w.g1(sig.y1);
    w.g2(sig.y2);
}
fn get_signature(r: &mut Reader<'_>) -> Result<Signature> {
    Ok(Signature {
        z: r.g1(false)?,
        y1: r.g1(true)?,
        y2: r.g2(true)?,
    })
}
impl PublicKey {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(PK_TAG);
        for g in self.t {
            w.g1(g);
        }
        for g in self.y {
            w.g2(g);
        }
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, PK_TAG)?;
        let key = Self {
            t: [r.g1(true)?, r.g1(true)?],
            y: [r.g2(true)?, r.g2(true)?, r.g2(true)?],
        };
        r.finish()?;
        Ok(key)
    }
}
impl IssueMessage {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(ISSUE_TAG);
        w.bytes(&self.nonce);
        w.g1(self.s);
        put_signature(&mut w, &self.signature);
        for s in [
            self.proof.c0,
            self.proof.c1,
            self.proof.au,
            self.proof.av,
            self.proof.aw,
            self.proof.a0,
            self.proof.a1,
        ] {
            w.fr(s);
        }
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, ISSUE_TAG)?;
        let nonce = r.bytes()?;
        if nonce.len() != NONCE_BYTES {
            return Err(error("invalid nonce length"));
        }
        let s = r.g1(true)?;
        let signature = get_signature(&mut r)?;
        let proof = IssuerProof {
            c0: r.fr()?,
            c1: r.fr()?,
            au: r.fr()?,
            av: r.fr()?,
            aw: r.fr()?,
            a0: r.fr()?,
            a1: r.fr()?,
        };
        r.finish()?;
        Ok(Self {
            nonce,
            s,
            signature,
            proof,
        })
    }
}
/// Sealed provenance for a strictly decoded native bearer token.
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
impl Token {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(TOKEN_TAG);
        w.g1(self.t1);
        w.g1(self.t2);
        put_signature(&mut w, &self.signature);
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, TOKEN_TAG)?;
        let t1 = r.g1(true)?;
        let t2 = r.g1(true)?;
        let signature = get_signature(&mut r)?;
        r.finish()?;
        Ok(Self { t1, t2, signature })
    }
}

fn valid_signature(sig: &Signature) -> bool {
    valid1(sig.z, false) && valid1(sig.y1, true) && valid2(sig.y2, true)
}
fn verify_signature(installed: &InstalledIssuer, messages: [G1; 3], sig: &Signature) -> bool {
    let key = &installed.key;
    multi_pair(&[
        (messages[0], key.y[0]),
        (messages[1], key.y[1]),
        (messages[2], key.y[2]),
        (-sig.z, sig.y2),
    ]) == GT::identity()
        && multi_pair(&[(sig.y1, G2::generator()), (-G1::generator(), sig.y2)]) == GT::identity()
}
/// Transcript order is (g1,g2,pkC,S,T0,T1,U,V,W,S0,S1,T0',T1',U',V',W').
fn challenge(installed: &InstalledIssuer, client_public: G1, s: G1, c1: [G1; 4], c2: [G2; 3]) -> S {
    let mut transcript = Vec::new();
    frame(&mut transcript, &enc1(G1::generator()));
    frame(&mut transcript, &enc2(G2::generator()));
    frame(&mut transcript, &enc1(client_public));
    frame(&mut transcript, &enc1(s));
    for g in installed.key.t {
        frame(&mut transcript, &enc1(g));
    }
    for g in installed.key.y {
        frame(&mut transcript, &enc2(g));
    }
    for g in c1 {
        frame(&mut transcript, &enc1(g));
    }
    for g in c2 {
        frame(&mut transcript, &enc2(g));
    }
    hash_fr(H_PROOF, &transcript)
}
fn prove(
    installed: &InstalledIssuer,
    secret: &IssuerSecret,
    client_public: G1,
    r: G1,
    s: G1,
    bit: u8,
    prepared: &PreparedIssue,
) -> IssuerProof {
    let branch = bit as usize;
    let other = 1 - branch;
    let z = prepared.z;
    let zu = prepared.zu;
    let simulated_challenge = prepared.simulated_challenge;
    let simulated_response = prepared.simulated_response;
    let mut cs = [S::ZERO; 2];
    let mut a = [S::ZERO; 2];
    cs[other] = simulated_challenge;
    a[other] = simulated_response;
    let mut cp_r = [G1::identity(); 2];
    let mut cp_t = [G1::identity(); 2];
    cp_r[branch] = g1_mul(r, z);
    cp_t[branch] = prepared.g_z;
    // S = R^x_b and T_other = g1^x_other were derived from issuer keys.
    cp_r[other] = g1_mul(r, a[other] - cs[other] * secret.x[branch]);
    cp_t[other] = g1_mul(G1::generator(), a[other] - cs[other] * secret.x[other]);
    let cy = prepared.g_zu;
    let c = challenge(
        installed,
        client_public,
        s,
        [cp_r[0], cp_r[1], cp_t[0], cp_t[1]],
        cy,
    );
    cs[branch] = c - cs[other];
    a[branch] = z + cs[branch] * secret.x[branch];
    IssuerProof {
        c0: cs[0],
        c1: cs[1],
        au: zu[0] + c * secret.y[0],
        av: zu[1] + c * secret.y[1],
        aw: zu[2] + c * secret.y[2],
        a0: a[0],
        a1: a[1],
    }
}
fn verify_proof(
    installed: &InstalledIssuer,
    client_public: G1,
    r: G1,
    s: G1,
    proof: &IssuerProof,
) -> bool {
    let c = proof.c0 + proof.c1;
    let cp = [
        sum1(&[(r, proof.a0), (s, -proof.c0)]),
        sum1(&[(r, proof.a1), (s, -proof.c1)]),
        sum1(&[(G1::generator(), proof.a0), (installed.key.t[0], -proof.c0)]),
        sum1(&[(G1::generator(), proof.a1), (installed.key.t[1], -proof.c1)]),
    ];
    let responses = [proof.au, proof.av, proof.aw];
    let cy =
        std::array::from_fn(|i| sum2(&[(G2::generator(), responses[i]), (installed.key.y[i], -c)]));
    challenge(installed, client_public, s, cp, cy) == c
}

pub fn encode_client_request(client_public: G1) -> Vec<u8> {
    let mut w = Writer::new(REQUEST_TAG);
    w.g1(client_public);
    w.finish()
}
/// Prepare native issuer signing material before the client request arrives.
pub fn prepare_issue(
    installed: &InstalledIssuer,
    rng: &mut (impl RngCore + CryptoRng),
) -> PreparedIssue {
    let v = random_nonzero(rng);
    let v_inverse = inv(v);
    let z = random_nonzero(rng);
    let zu = std::array::from_fn(|_| random_nonzero(rng));
    let simulated_challenge = random_nonzero(rng);
    let simulated_response = random_nonzero(rng);
    PreparedIssue {
        issuer_binding: installed.binding.clone(),
        v,
        y1: g1_mul(G1::generator(), v_inverse),
        y2: g2_mul(G2::generator(), v_inverse),
        z,
        g_z: g1_mul(G1::generator(), z),
        zu,
        g_zu: zu.map(|s| g2_mul(G2::generator(), s)),
        simulated_challenge,
        simulated_response,
    }
}
impl PreparedIssue {
    pub fn issue(
        self,
        installed: &InstalledIssuer,
        secret: &IssuerSecret,
        client_public: G1,
        bit: u8,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> Result<IssueMessage> {
        self.issue_received(installed, secret, client_public, bit, rng, false)
    }
    pub fn issue_wire(
        self,
        installed: &InstalledIssuer,
        secret: &IssuerSecret,
        request: &[u8],
        bit: u8,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> Result<IssueMessage> {
        let mut r = Reader::new(request, REQUEST_TAG)?;
        let client_public = r.g1(true)?;
        r.finish()?;
        self.issue_received(installed, secret, client_public, bit, rng, true)
    }
    fn issue_received(
        self,
        installed: &InstalledIssuer,
        secret: &IssuerSecret,
        client_public: G1,
        bit: u8,
        rng: &mut (impl RngCore + CryptoRng),
        decoded: bool,
    ) -> Result<IssueMessage> {
        if self.issuer_binding != installed.binding
            || secret.binding != installed.binding
            || bit > 1
            || (!decoded && !valid1(client_public, true))
        {
            return Err(error("invalid issuance input"));
        }
        let mut nonce = vec![0; NONCE_BYTES];
        rng.fill_bytes(&mut nonce);
        let r = hash_g1(H_GROUP, &nonce);
        if r == G1::identity() {
            return Err(error("nonce hash outside message domain"));
        }
        let s = g1_mul(r, secret.x[bit as usize]);
        // S = R^x_b; combine the locally known R/S exponents before
        // executing the two message-dependent scalar multiplications.
        let z = sum1(&[
            (client_public, self.v * secret.y[0]),
            (
                r,
                self.v * (secret.y[1] + secret.x[bit as usize] * secret.y[2]),
            ),
        ]);
        let signature = Signature {
            z,
            y1: self.y1,
            y2: self.y2,
        };
        let proof = prove(installed, secret, client_public, r, s, bit, &self);
        Ok(IssueMessage {
            nonce,
            s,
            signature,
            proof,
        })
    }
}
/// Execute the native issuer response or complete issuance interface.
pub fn issue(
    installed: &InstalledIssuer,
    secret: &IssuerSecret,
    client_public: G1,
    bit: u8,
    rng: &mut (impl RngCore + CryptoRng),
) -> Result<IssueMessage> {
    prepare_issue(installed, rng).issue(installed, secret, client_public, bit, rng)
}
impl PreparedObtain {
    /// The state is moved into this method, so a successful or rejected receive
    /// cannot reuse its precomputed client inverse.
    pub fn obtain(self, installed: &InstalledIssuer, message: &IssueMessage) -> Result<Token> {
        self.obtain_received(installed, message, false)
    }
    fn obtain_received(
        self,
        installed: &InstalledIssuer,
        message: &IssueMessage,
        decoded: bool,
    ) -> Result<Token> {
        self.obtain_received_with_signature(installed, message, decoded, |messages, sig| {
            verify_signature(installed, messages, sig)
        })
    }
    fn obtain_received_with_signature(
        self,
        installed: &InstalledIssuer,
        message: &IssueMessage,
        decoded: bool,
        check: impl FnOnce([G1; 3], &Signature) -> bool,
    ) -> Result<Token> {
        if message.nonce.len() != NONCE_BYTES
            || (!decoded && (!valid1(message.s, true) || !valid_signature(&message.signature)))
        {
            return Err(error("invalid issuance message"));
        }
        let r = hash_g1(H_GROUP, &message.nonce);
        if r == G1::identity()
            || !verify_proof(installed, self.client_public, r, message.s, &message.proof)
            || !check([self.client_public, r, message.s], &message.signature)
        {
            return Err(error("invalid issuance authentication"));
        }
        Ok(Token {
            t1: g1_mul(r, self.alpha_inverse),
            t2: g1_mul(message.s, self.alpha_inverse),
            signature: Signature {
                z: g1_mul(message.signature.z, self.psi_over_alpha),
                y1: g1_mul(message.signature.y1, self.psi_inverse),
                y2: g2_mul(message.signature.y2, self.psi_inverse),
            },
        })
    }
    pub fn obtain_wire_set(
        self,
        installed: &InstalledIssuer,
        bytes: &[u8],
        weights: &mut impl RngCore,
    ) -> Result<Token> {
        let message = IssueMessage::decode(bytes)?;
        self.obtain_received_with_signature(installed, &message, true, |messages, sig| {
            crate::batch::fhs_random_checked(
                &installed.key.y,
                &[crate::batch::FhsStatement {
                    message: messages.to_vec(),
                    z: sig.z,
                    y: sig.y1,
                    yh: sig.y2,
                }],
                weights,
            )
        })
    }
    pub fn obtain_wire(self, installed: &InstalledIssuer, bytes: &[u8]) -> Result<Token> {
        let message = IssueMessage::decode(bytes)?;
        self.obtain_received(installed, &message, true)
    }
}
/// Validate and rerandomize the issuer message to obtain the native bearer token.
pub fn obtain(
    installed: &InstalledIssuer,
    client: &ClientKeys,
    message: &IssueMessage,
    rng: &mut (impl RngCore + CryptoRng),
) -> Result<Token> {
    client.prepare_obtain(rng).obtain(installed, message)
}
/// Verify a native token and return an immutable validity capability for secret extraction.
pub fn verify_token(installed: &InstalledIssuer, token: &Token) -> Result<VerifiedToken> {
    verify_token_received(installed, token, false)
}
pub fn verify_token_checked(
    installed: &InstalledIssuer,
    token: &CheckedToken,
) -> Result<VerifiedToken> {
    verify_token_received(installed, &token.token, true)
}
fn verify_token_received(
    installed: &InstalledIssuer,
    token: &Token,
    decoded: bool,
) -> Result<VerifiedToken> {
    if !decoded
        && (!valid1(token.t1, true)
            || !valid1(token.t2, true)
            || !valid_signature(&token.signature))
    {
        return Err(error("invalid token domain"));
    }
    let sig = &token.signature;
    if multi_pair(&[
        (token.t1, installed.key.y[1]),
        (token.t2, installed.key.y[2]),
        (-sig.z, sig.y2),
    ]) != -installed.token_anchor
        || multi_pair(&[(sig.y1, G2::generator()), (-G1::generator(), sig.y2)]) != GT::identity()
    {
        return Err(error("invalid token"));
    }
    Ok(VerifiedToken {
        t1: token.t1,
        t2: token.t2,
        issuer_binding: installed.binding.clone(),
    })
}
pub fn verify_token_wire(installed: &InstalledIssuer, bytes: &[u8]) -> Result<VerifiedToken> {
    verify_token_received(installed, &Token::decode(bytes)?, true)
}
/// Single-token public verification with independent verifier weights.
pub fn verify_token_random(
    installed: &InstalledIssuer,
    token: &Token,
    rng: &mut impl RngCore,
) -> Result<VerifiedToken> {
    verify_token_random_inner(installed, token, false, false, rng)
}
fn verify_token_random_inner(
    installed: &InstalledIssuer,
    token: &Token,
    cached_anchor: bool,
    decoded: bool,
    rng: &mut impl RngCore,
) -> Result<VerifiedToken> {
    if !decoded
        && (!valid1(token.t1, true)
            || !valid1(token.t2, true)
            || !valid_signature(&token.signature))
    {
        return Err(error("invalid token domain"));
    }
    let statement = crate::batch::FhsStatement {
        message: vec![G1::generator(), token.t1, token.t2],
        z: token.signature.z,
        y: token.signature.y1,
        yh: token.signature.y2,
    };
    let valid = if decoded && cached_anchor {
        crate::batch::fhs_random_with_anchor_checked(
            &installed.key.y,
            &[statement],
            installed.token_anchor,
            rng,
        )
    } else if decoded {
        crate::batch::fhs_random_checked(&installed.key.y, &[statement], rng)
    } else if cached_anchor {
        crate::batch::fhs_random_with_anchor(
            &installed.key.y,
            &[statement],
            installed.token_anchor,
            rng,
        )
    } else {
        crate::batch::fhs_random(&installed.key.y, &[statement], rng)
    };
    if !valid {
        return Err(error("invalid random signature"));
    }
    Ok(VerifiedToken {
        t1: token.t1,
        t2: token.t2,
        issuer_binding: installed.binding.clone(),
    })
}
/// Native Appendix C.3 redemption keeps the first signature equation per
/// token. Its second equation is aggregated either exactly as published or with
/// independent verifier weights. The strongest common engineering profile also
/// randomly combines both classes of FHS equations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RedemptionBatch {
    OriginalAllOnes,
    RandomSecondEquation,
    RandomFhs,
    RandomFhsCachedAnchor,
}
pub fn verify_batch_redemption(
    installed: &InstalledIssuer,
    tokens: &[Token],
    mode: RedemptionBatch,
    rng: &mut impl RngCore,
) -> Result<Vec<VerifiedToken>> {
    verify_redemption_frozen(installed, tokens.to_vec(), mode, false, rng)
}
pub fn verify_batch_redemption_checked(
    installed: &InstalledIssuer,
    tokens: &[CheckedToken],
    mode: RedemptionBatch,
    rng: &mut impl RngCore,
) -> Result<Vec<VerifiedToken>> {
    verify_redemption_frozen(
        installed,
        tokens.iter().map(|t| t.token.clone()).collect(),
        mode,
        true,
        rng,
    )
}
fn verify_redemption_frozen(
    installed: &InstalledIssuer,
    frozen: Vec<Token>,
    mode: RedemptionBatch,
    decoded: bool,
    rng: &mut impl RngCore,
) -> Result<Vec<VerifiedToken>> {
    if frozen.is_empty() {
        return Err(error("empty redemption batch"));
    }
    // Follow the native single-token interface at k=1.
    if frozen.len() == 1 && mode != RedemptionBatch::RandomSecondEquation {
        return Ok(vec![if matches!(
            mode,
            RedemptionBatch::RandomFhs | RedemptionBatch::RandomFhsCachedAnchor
        ) {
            verify_token_random_inner(
                installed,
                &frozen[0],
                mode == RedemptionBatch::RandomFhsCachedAnchor,
                decoded,
                rng,
            )?
        } else {
            verify_token_received(installed, &frozen[0], decoded)?
        }]);
    }
    if !decoded
        && frozen
            .iter()
            .any(|t| !valid1(t.t1, true) || !valid1(t.t2, true) || !valid_signature(&t.signature))
    {
        return Err(error("invalid batch token domain"));
    }
    let mut tags = std::collections::BTreeSet::new();
    if frozen.iter().any(|t| !tags.insert(redemption_tag(t))) {
        return Err(error("duplicate batch tag"));
    }
    let _bytes: Vec<_> = frozen.iter().map(Token::encode).collect();
    if matches!(
        mode,
        RedemptionBatch::RandomFhs | RedemptionBatch::RandomFhsCachedAnchor
    ) {
        let statements: Vec<_> = frozen
            .iter()
            .map(|t| crate::batch::FhsStatement {
                message: vec![G1::generator(), t.t1, t.t2],
                z: t.signature.z,
                y: t.signature.y1,
                yh: t.signature.y2,
            })
            .collect();
        let valid = if decoded && mode == RedemptionBatch::RandomFhsCachedAnchor {
            crate::batch::fhs_random_with_anchor_checked(
                &installed.key.y,
                &statements,
                installed.token_anchor,
                rng,
            )
        } else if decoded {
            crate::batch::fhs_random_checked(&installed.key.y, &statements, rng)
        } else if mode == RedemptionBatch::RandomFhsCachedAnchor {
            crate::batch::fhs_random_with_anchor(
                &installed.key.y,
                &statements,
                installed.token_anchor,
                rng,
            )
        } else {
            crate::batch::fhs_random(&installed.key.y, &statements, rng)
        };
        if !valid {
            return Err(error("invalid random signature batch"));
        }
    } else {
        // App.C.3 p.19 explicitly retains these 3n individual Miller inputs,
        // since the client provides no token-generation Sigma proof.
        for t in &frozen {
            if multi_pair(&[
                (t.t1, installed.key.y[1]),
                (t.t2, installed.key.y[2]),
                (-t.signature.z, t.signature.y2),
            ]) != -installed.token_anchor
            {
                return Err(error("invalid individual first equation"));
            }
        }
        let weights: Vec<_> = frozen
            .iter()
            .map(|_| {
                if mode == RedemptionBatch::OriginalAllOnes {
                    S::ONE
                } else {
                    random_batch_weight128(rng)
                }
            })
            .collect();
        let y1 = sum1(
            &frozen
                .iter()
                .zip(&weights)
                .map(|(t, &a)| (t.signature.y1, a))
                .collect::<Vec<_>>(),
        );
        let y2 = sum2(
            &frozen
                .iter()
                .zip(&weights)
                .map(|(t, &a)| (t.signature.y2, a))
                .collect::<Vec<_>>(),
        );
        if multi_pair(&[(y1, G2::generator()), (-G1::generator(), y2)]) != GT::identity() {
            return Err(error("invalid second equation batch"));
        }
    }
    Ok(frozen
        .iter()
        .map(|t| VerifiedToken {
            t1: t.t1,
            t2: t.t2,
            issuer_binding: installed.binding.clone(),
        })
        .collect())
}
/// Verify the native bearer token without a secret metadata key.
pub fn public_verify(installed: &InstalledIssuer, token: &Token) -> bool {
    verify_token(installed, token).is_ok()
}
/// Extract private metadata from a verified token without repeating PublicVerify.
pub fn read_bit_extract(secret: &IssuerSecret, token: &VerifiedToken) -> Result<u8> {
    if secret.binding != token.issuer_binding {
        return Err(error("wrong extraction key"));
    }
    for bit in 0..2 {
        if g1_mul(token.t1, secret.x[bit]) == token.t2 {
            return Ok(bit as u8);
        }
    }
    Err(error("metadata bit unavailable"))
}
/// Run native public verification followed by private metadata extraction.
pub fn read_bit_total(
    installed: &InstalledIssuer,
    secret: &IssuerSecret,
    token: &Token,
) -> Result<u8> {
    let verified = verify_token(installed, token)?;
    read_bit_extract(secret, &verified)
}

pub fn read_bit_total_checked(
    installed: &InstalledIssuer,
    secret: &IssuerSecret,
    token: &CheckedToken,
) -> Result<u8> {
    read_bit_extract(secret, &verify_token_checked(installed, token)?)
}
/// Complete Read under the fixed C3-grouped SET verifier.
pub fn read_bit_total_set_checked(
    installed: &InstalledIssuer,
    secret: &IssuerSecret,
    token: &CheckedToken,
    weights: &mut impl RngCore,
) -> Result<u8> {
    let records = verify_batch_redemption_checked(
        installed,
        std::slice::from_ref(token),
        RedemptionBatch::RandomSecondEquation,
        weights,
    )?;
    read_bit_extract(secret, &records[0])
}
/// Redemption uses the stable two-point token tag, excluding randomized SPS
/// signature components. It is a bearer-token identifier, not a user identity.
pub fn redemption_tag(token: &Token) -> [u8; 96] {
    let mut tag = [0; 96];
    tag[..48].copy_from_slice(&token.t1.to_compressed());
    tag[48..].copy_from_slice(&token.t2.to_compressed());
    tag
}
/// Decode and perform the native complete verification-plus-extraction operation.
pub fn read_bit_total_wire(
    installed: &InstalledIssuer,
    secret: &IssuerSecret,
    bytes: &[u8],
) -> Result<u8> {
    let verified = verify_token_wire(installed, bytes)?;
    read_bit_extract(secret, &verified)
}

#[cfg(test)]
mod algebra_contract {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn issued_points_and_proof_equal_unfolded_source_formulas() {
        for seed in 0..12 {
            for bit in 0..=1 {
                let mut rng = StdRng::seed_from_u64(1211200 + seed * 2 + bit as u64);
                let issuer = IssuerKeys::generate(&mut rng);
                let installed = issuer.install().unwrap();
                let client = ClientKeys::generate(&mut rng);
                let p = prepare_issue(&installed, &mut rng);
                let (v, z, zu, csim, asim) =
                    (p.v, p.z, p.zu, p.simulated_challenge, p.simulated_response);
                let msg = p
                    .issue(
                        &installed,
                        &issuer.secret,
                        client.public_key(),
                        bit,
                        &mut rng,
                    )
                    .unwrap();
                let r = hash_g1(H_GROUP, &msg.nonce);
                let x = issuer.secret.x;
                let y = issuer.secret.y;
                let expected_z = (client.public_key() * y[0] + r * y[1] + msg.s * y[2]) * v;
                assert_eq!(msg.signature.z, expected_z);
                assert_eq!(msg.signature.y1, G1::generator() * inv(v));
                assert_eq!(msg.signature.y2, G2::generator() * inv(v));
                let b = bit as usize;
                let other = 1 - b;
                let mut cr = [G1::identity(); 2];
                let mut ct = [G1::identity(); 2];
                cr[b] = r * z;
                ct[b] = G1::generator() * z;
                cr[other] = r * asim - msg.s * csim;
                ct[other] = G1::generator() * asim - installed.key.t[other] * csim;
                let cy = zu.map(|s| G2::generator() * s);
                let c = challenge(
                    &installed,
                    client.public_key(),
                    msg.s,
                    [cr[0], cr[1], ct[0], ct[1]],
                    cy,
                );
                let mut cs = [S::ZERO; 2];
                let mut a = [S::ZERO; 2];
                cs[other] = csim;
                a[other] = asim;
                cs[b] = c - csim;
                a[b] = z + cs[b] * x[b];
                let expected = IssuerProof {
                    c0: cs[0],
                    c1: cs[1],
                    au: zu[0] + c * y[0],
                    av: zu[1] + c * y[1],
                    aw: zu[2] + c * y[2],
                    a0: a[0],
                    a1: a[1],
                };
                assert_eq!(msg.proof, expected);
            }
        }
    }
}
