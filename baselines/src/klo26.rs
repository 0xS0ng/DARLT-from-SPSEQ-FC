//! KLO26 Construction 1 (EQS, public metadata + private bit), AsiaCCS 2026 p.669.
//! Profile 2: known-coordinate issuer fusion and fresh full ChgRep guard.
//! All original FHS, DLEQ and two-branch/two-relation OR checks remain.
//! Context/policy-independent preparation is consumed once.
use crate::arithmetic::*;
use ff::Field;
use group::Group;
use rand::RngCore;
use std::collections::BTreeSet;

pub type Result<T> = std::result::Result<T, &'static str>;
#[derive(Clone, Debug)]
pub struct Sig {
    pub z: G1,
    pub y: G1,
    pub yh: G2,
}
#[derive(Clone, Debug)]
pub struct DlProof {
    pub c: S,
    pub z: S,
}
#[derive(Clone, Debug)]
pub struct OrProof {
    pub c: [S; 2],
    pub z: [S; 2],
}
#[derive(Clone, Debug)]
pub struct KeyProof {
    pub c: S,
    pub z: [S; 4],
}
#[derive(Clone, Debug)]
pub struct PublicKey {
    pub vk: [G2; 4],
    pub bit: [G1; 2],
    pub proof: KeyProof,
}
#[derive(Clone)]
pub struct Issuer {
    sk: [S; 4],
    bit_sk: [S; 2],
    pub pk: PublicKey,
}
/// Constructible only by validating the issuer's proof once per public key (Fig6 step7).
/// Owned public key and fixed native FS domain prefixes.
/// ```compile_fail
/// use baseline_core::klo26::ValidatedKey;
/// let forged = ValidatedKey {};
/// ```
#[derive(Clone)]
pub struct ValidatedKey {
    pk: PublicKey,
    request_hash: CachedScalarHashPrefix,
    or_hash: CachedScalarHashPrefix,
    redeem_hash: CachedScalarHashPrefix,
}
impl ValidatedKey {
    pub fn matches_public_key(&self, pk: &PublicKey) -> bool {
        self.pk.vk == pk.vk
            && self.pk.bit == pk.bit
            && self.pk.proof.c == pk.proof.c
            && self.pk.proof.z == pk.proof.z
    }
    pub fn public_key(&self) -> &PublicKey {
        &self.pk
    }
}
#[derive(Clone, Debug)]
pub struct Request {
    pub pkc: G1,
    pub proof: DlProof,
}
pub struct Pending {
    skc: S,
    md: Vec<u8>,
    pk: ValidatedKey,
}
#[derive(Clone, Debug)]
pub struct Response {
    pub r: G1,
    pub pkc: G1,
    pub x: G1,
    pub sig: Sig,
    pub proof: OrProof,
}
#[derive(Clone)]
pub struct Wallet {
    msg: [G1; 4],
    skc: S,
    sig: Sig,
    metadata: Vec<u8>,
    key: ValidatedKey,
    signature_validated: bool,
}
#[derive(Clone, Debug)]
pub struct Token {
    pub delta: G1,
    pub tag: Vec<u8>,
    pub r: G1,
    pub pkc: G1,
    pub x: G1,
    pub sig: Sig,
    pub proof: DlProof,
}
/// Immutable evidence of bounded, canonical subgroup decoding. It proves group
/// membership only; every signature, DLEQ, policy and nonzero rule is rechecked.
/// ```compile_fail
/// use baseline_core::klo26::{CheckedToken, Token};
/// fn forge(token:Token) { let _ = CheckedToken { token }; }
/// ```
/// ```compile_fail
/// use baseline_core::klo26::CheckedToken;
/// fn mutate(t:&CheckedToken) { t.as_token().tag.clear(); }
/// ```
#[derive(Clone)]
pub struct CheckedToken {
    token: Token,
}
impl CheckedToken {
    pub fn decode_received(bytes: &[u8]) -> Result<Self> {
        Ok(Self {
            token: Token::decode_received(bytes)?,
        })
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        Ok(Self {
            token: Token::decode(bytes)?,
        })
    }
    pub fn as_token(&self) -> &Token {
        &self.token
    }
}
/// Tags are public, fixed-size service slots. Membership/duplicate checks are local operations.
#[derive(Clone, Debug)]
pub struct Policy {
    pub allowed: BTreeSet<Vec<u8>>,
}

fn fs_cached(tag: &[u8], points: &[G1], cached: Option<&CachedScalarHashPrefix>, skip: usize) -> S {
    let mut b = Vec::new();
    for p in points.iter().skip(if cached.is_some() { skip } else { 0 }) {
        b.extend(enc1(*p));
    }
    cached.map_or_else(|| hash_scalar(tag, &b), |h| h.finish(&b))
}
fn key_fs(vk: &[G2; 4], a: &[G2; 4]) -> S {
    let mut b = enc2(G2::generator());
    for i in 0..4 {
        b.extend(enc2(vk[i]));
        b.extend(enc2(a[i]));
    }
    hash_scalar(b"\x43\x50\x41\x54\x32\x2f\x65\x71\x73\x2d\x6b\x65\x79", &b)
}

fn dleq_cached(
    tag: &[u8],
    x: S,
    base: &[G1],
    target: &[G1],
    rng: &mut impl RngCore,
    cached: Option<&CachedScalarHashPrefix>,
    skip: usize,
) -> DlProof {
    let r = random_scalar(rng);
    let a: Vec<_> = base.iter().map(|g| g1_mul(*g, r)).collect();
    let mut p = vec![];
    for i in 0..base.len() {
        p.extend([base[i], target[i], a[i]]);
    }
    let c = fs_cached(tag, &p, cached, skip);
    DlProof { c, z: r - c * x }
}

// Private, call-local path. Callers establish membership of every raw point
// before entering; generator/hash points and their scalar products are local.
// Shape and the original nonzero-base rule still apply on every invocation.
fn verify_dleq_checked(
    tag: &[u8],
    proof: &DlProof,
    base: &[G1],
    target: &[G1],
    cached: Option<&CachedScalarHashPrefix>,
    skip: usize,
) -> bool {
    if base.len() != target.len() || base.is_empty() || base.iter().any(|g| *g == G1::identity()) {
        return false;
    }
    let mut p = vec![];
    for i in 0..base.len() {
        let a = sum1(&[(target[i], proof.c), (base[i], proof.z)]);
        p.extend([base[i], target[i], a]);
    }
    fs_cached(tag, &p, cached, skip) == proof.c
}

fn or_fs_cached(
    pk: &PublicKey,
    r: G1,
    x: G1,
    a: &[[G1; 2]; 2],
    cached: Option<&CachedScalarHashPrefix>,
) -> S {
    fs_cached(
        b"\x43\x50\x41\x54\x32\x2f\x65\x71\x2d\x6f\x72",
        &[
            G1::generator(),
            r,
            pk.bit[0],
            x,
            a[0][0],
            a[0][1],
            pk.bit[1],
            x,
            a[1][0],
            a[1][1],
        ],
        cached,
        1,
    )
}

fn prove_bit_cached(
    pk: &PublicKey,
    r: G1,
    x: G1,
    v: S,
    bit: usize,
    rng: &mut impl RngCore,
    cached: Option<&CachedScalarHashPrefix>,
) -> OrProof {
    let f = 1 - bit;
    let rand = random_scalar(rng);
    let mut c = [S::ZERO; 2];
    let mut z = [S::ZERO; 2];
    let mut a = [[G1::identity(); 2]; 2];
    c[f] = random_scalar(rng);
    z[f] = random_scalar(rng);
    a[bit] = [g1_mul(G1::generator(), rand), g1_mul(pk.bit[bit], rand)];
    a[f] = [
        sum1(&[(r, c[f]), (G1::generator(), z[f])]),
        sum1(&[(x, c[f]), (pk.bit[f], z[f])]),
    ];
    c[bit] = or_fs_cached(pk, r, x, &a, cached) - c[f];
    z[bit] = rand - c[bit] * v;
    OrProof { c, z }
}

fn verify_bit_cached(
    pk: &PublicKey,
    r: G1,
    x: G1,
    p: &OrProof,
    cached: Option<&CachedScalarHashPrefix>,
) -> bool {
    let a = std::array::from_fn(|i| {
        [
            sum1(&[(r, p.c[i]), (G1::generator(), p.z[i])]),
            sum1(&[(x, p.c[i]), (pk.bit[i], p.z[i])]),
        ]
    });
    or_fs_cached(pk, r, x, &a, cached) == p.c[0] + p.c[1]
}

fn signature_members(s: &Sig) -> bool {
    valid1(s.y, true) && valid1(s.z, false) && valid2(s.yh, true)
}
// The only callers are the fully checked receive/verify entry points and the
// immutable, private Wallet created by receive. This is not a public trust flag.
fn verify_signature_checked(pk: &PublicKey, m: &[G1; 4], s: &Sig) -> bool {
    if m[0] == G1::identity() || s.y == G1::identity() || s.yh == G2::identity() {
        return false;
    }
    let mut t: Vec<_> = (0..4).map(|i| (m[i], pk.vk[i])).collect();
    t.push((-s.z, s.yh));
    multi_pair(&t) == GT::identity()
        && multi_pair(&[(s.y, G2::generator()), (-G1::generator(), s.yh)]) == GT::identity()
}
/// Generate the native issuer secret and public key.
pub fn keygen(rng: &mut impl RngCore) -> Issuer {
    let sk = std::array::from_fn(|_| random_nonzero(rng));
    let vk = std::array::from_fn(|i| g2_mul(G2::generator(), sk[i]));
    let rr: [S; 4] = std::array::from_fn(|_| random_scalar(rng));
    let a = std::array::from_fn(|i| g2_mul(G2::generator(), rr[i]));
    let c = key_fs(&vk, &a);
    let proof = KeyProof {
        c,
        z: std::array::from_fn(|i| rr[i] - c * sk[i]),
    };
    let bit_sk = std::array::from_fn(|_| random_scalar(rng));
    let bit = std::array::from_fn(|i| g1_mul(G1::generator(), bit_sk[i]));
    Issuer {
        sk,
        bit_sk,
        pk: PublicKey { vk, bit, proof },
    }
}
/// Validate and cache the complete native public key.
pub fn validate_key(pk: &PublicKey) -> Result<ValidatedKey> {
    if pk.vk.iter().any(|p| !valid2(*p, true)) || pk.bit.iter().any(|p| !valid1(*p, false)) {
        return Err("invalid issuer key");
    }
    let a =
        std::array::from_fn(|i| sum2(&[(pk.vk[i], pk.proof.c), (G2::generator(), pk.proof.z[i])]));
    if key_fs(&pk.vk, &a) != pk.proof.c {
        return Err("issuer key PoK");
    }
    Ok(ValidatedKey {
        pk: pk.clone(),
        request_hash: CachedScalarHashPrefix::new(
            b"\x43\x50\x41\x54\x32\x2f\x72\x65\x71",
            &enc1(G1::generator()),
            &[96],
        ),
        or_hash: CachedScalarHashPrefix::new(
            b"\x43\x50\x41\x54\x32\x2f\x65\x71\x2d\x6f\x72",
            &enc1(G1::generator()),
            &[432],
        ),
        redeem_hash: CachedScalarHashPrefix::new(
            b"\x43\x50\x41\x54\x32\x2f\x72\x65\x64\x65\x65\x6d",
            &[],
            &[288],
        ),
    })
}
/// Create the holder request for native credential or token acquisition.
pub fn request(pk: &ValidatedKey, metadata: &[u8], rng: &mut impl RngCore) -> (Request, Pending) {
    let skc = random_scalar(rng);
    let pkc = g1_mul(G1::generator(), skc);
    let proof = dleq_cached(
        b"\x43\x50\x41\x54\x32\x2f\x72\x65\x71",
        skc,
        &[G1::generator()],
        &[pkc],
        rng,
        Some(&pk.request_hash),
        1,
    );
    (
        Request { pkc, proof },
        Pending {
            skc,
            md: metadata.to_vec(),
            pk: pk.clone(),
        },
    )
}
/// Execute the native issuer response or complete issuance interface.
pub fn issue(
    issuer: &Issuer,
    req: &Request,
    metadata: &[u8],
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<Response> {
    issue_internal(issuer, req, metadata, bit, rng, None, false)
}
pub fn issue_installed(
    key: &ValidatedKey,
    issuer: &Issuer,
    req: &Request,
    metadata: &[u8],
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<Response> {
    if !key.matches_public_key(&issuer.pk) {
        return Err("installed issuer mismatch");
    }
    issue_internal(issuer, req, metadata, bit, rng, Some(key), false)
}
/// Checked request provenance, immutable outside this module.
pub struct ReceivedRequest(Request);
impl ReceivedRequest {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = crate::canonical::Reader::new(bytes, crate::canonical::DecodeLimits::default())
            .map_err(|_| "request framing")?;
        let pkc = r.g1().map_err(|_| "request point")?;
        let proof = DlProof {
            c: r.scalar().map_err(|_| "request c")?,
            z: r.scalar().map_err(|_| "request z")?,
        };
        r.finish().map_err(|_| "request trailing bytes")?;
        Ok(Self(Request { pkc, proof }))
    }
}
pub fn issue_received_installed(
    key: &ValidatedKey,
    issuer: &Issuer,
    request: ReceivedRequest,
    metadata: &[u8],
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<Response> {
    if !key.matches_public_key(&issuer.pk) {
        return Err("installed issuer mismatch");
    }
    issue_internal(issuer, &request.0, metadata, bit, rng, Some(key), true)
}
fn issue_internal(
    issuer: &Issuer,
    req: &Request,
    metadata: &[u8],
    bit: usize,
    rng: &mut impl RngCore,
    key: Option<&ValidatedKey>,
    decoded_request: bool,
) -> Result<Response> {
    // Issuer.pk is publicly mutable. Only the installed branch carries an
    // exact, privately owned validation binding. Authenticate raw public
    // bases before deriving X and either OR branch; bit points may be zero.
    if key.is_none()
        && (issuer.pk.bit.iter().any(|&g| !valid1(g, false))
            || issuer.pk.vk.iter().any(|&g| !valid2(g, true)))
    {
        return Err("issuer public group");
    }
    // Request is public and mutable: authenticate its received point now.
    // The fixed generator has known prime-order membership.
    if bit > 1
        || (!decoded_request && !valid1(req.pkc, false))
        || !verify_dleq_checked(
            b"\x43\x50\x41\x54\x32\x2f\x72\x65\x71",
            &req.proof,
            &[G1::generator()],
            &[req.pkc],
            key.map(|k| &k.request_hash),
            1,
        )
    {
        return Err("request");
    }
    let v = random_nonzero(rng);
    let r = g1_mul(G1::generator(), v);
    let pkc = g1_mul(req.pkc, v);
    let x = g1_mul(issuer.pk.bit[bit], v);
    let proof = prove_bit_cached(&issuer.pk, r, x, v, bit, rng, key.map(|k| &k.or_hash));
    let m = hash_scalar(
        b"\x43\x50\x41\x54\x32\x2f\x48\x31\x2f\x6d\x65\x74\x61\x64\x61\x74\x61",
        metadata,
    );
    let y = random_nonzero(rng);
    let iy = inv(y);
    // X=bit_sk*r and metadata coordinate=m*r are known to this issuer.
    // Neither the untransmitted m*r nor an outer signature power is formed.
    let sig = Sig {
        z: sum1(&[
            (
                r,
                y * (issuer.sk[0] + m * issuer.sk[2] + issuer.bit_sk[bit] * issuer.sk[3]),
            ),
            (pkc, y * issuer.sk[1]),
        ]),
        y: g1_mul(G1::generator(), iy),
        yh: g2_mul(G2::generator(), iy),
    };
    Ok(Response {
        r,
        pkc,
        x,
        sig,
        proof,
    })
}
/// Validate the native issuer response or delivery and obtain holder material.
pub struct ReceivedResponse(Response);
impl ReceivedResponse {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = crate::canonical::Reader::new(bytes, crate::canonical::DecodeLimits::default())
            .map_err(|_| "response encoding")?;
        let response = Response {
            r: r.g1().map_err(|_| "response R")?,
            pkc: r.g1().map_err(|_| "response PK")?,
            x: r.g1().map_err(|_| "response X")?,
            sig: Sig {
                z: r.g1().map_err(|_| "response Z")?,
                y: r.g1().map_err(|_| "response Y")?,
                yh: r.g2().map_err(|_| "response Yhat")?,
            },
            proof: OrProof {
                c: [
                    r.scalar().map_err(|_| "response scalar")?,
                    r.scalar().map_err(|_| "response scalar")?,
                ],
                z: [
                    r.scalar().map_err(|_| "response scalar")?,
                    r.scalar().map_err(|_| "response scalar")?,
                ],
            },
        };
        r.finish().map_err(|_| "response trailing bytes")?;
        if response.r == G1::identity()
            || response.sig.y == G1::identity()
            || response.sig.yh == G2::identity()
        {
            return Err("response identity");
        }
        Ok(Self(response))
    }
}
fn response_domain(res: &Response) -> bool {
    valid1(res.r, true)
        && valid1(res.pkc, false)
        && valid1(res.x, false)
        && signature_members(&res.sig)
}
pub fn receive(pending: Pending, res: &Response) -> Result<Wallet> {
    receive_with_signature(pending, res, response_domain, |key, msg, sig| {
        verify_signature_checked(key, msg, sig)
    })
}
fn receive_with_signature(
    pending: Pending,
    res: &Response,
    domain: impl FnOnce(&Response) -> bool,
    check: impl FnOnce(&PublicKey, &[G1; 4], &Sig) -> bool,
) -> Result<Wallet> {
    if !domain(res) {
        return Err("response group");
    }
    let m = hash_scalar(
        b"\x43\x50\x41\x54\x32\x2f\x48\x31\x2f\x6d\x65\x74\x61\x64\x61\x74\x61",
        &pending.md,
    );
    let msg = [res.r, res.pkc, g1_mul(res.r, m), res.x];
    // msg[2] is a scalar product of the checked R; other coordinates and the
    // signature were checked once above. Both original relation checks remain.
    if res.pkc != g1_mul(res.r, pending.skc)
        || !verify_bit_cached(
            &pending.pk.pk,
            res.r,
            res.x,
            &res.proof,
            Some(&pending.pk.or_hash),
        )
        || !check(&pending.pk.pk, &msg, &res.sig)
    {
        return Err("response verification");
    }
    Ok(Wallet {
        msg,
        skc: pending.skc,
        sig: res.sig.clone(),
        metadata: pending.md,
        key: pending.pk,
        signature_validated: true,
    })
}
/// Native receive with all SPS signature pairing equations jointly weighted.
pub fn receive_set(pending: Pending, res: &Response, weights: &mut impl RngCore) -> Result<Wallet> {
    receive_with_signature(pending, res, response_domain, |key, msg, sig| {
        crate::batch::fhs_random_checked(
            &key.vk,
            &[crate::batch::FhsStatement {
                message: msg.to_vec(),
                z: sig.z,
                y: sig.y,
                yh: sig.yh,
            }],
            weights,
        )
    })
}
pub fn receive_received_set(
    pending: Pending,
    response: ReceivedResponse,
    weights: &mut impl RngCore,
) -> Result<Wallet> {
    receive_with_signature(
        pending,
        &response.0,
        |r| r.r != G1::identity() && r.sig.y != G1::identity() && r.sig.yh != G2::identity(),
        |key, msg, sig| {
            crate::batch::fhs_random_checked(
                &key.vk,
                &[crate::batch::FhsStatement {
                    message: msg.to_vec(),
                    z: sig.z,
                    y: sig.y,
                    yh: sig.yh,
                }],
                weights,
            )
        },
    )
}
/// Private one-use preparation from an immutable accepted wallet.
/// ```compile_fail
/// use baseline_core::klo26::*;
/// fn reuse(p:Prepared) { let _=show_online(p,b"first"); let _=show_online(p,b"second"); }
/// ```
pub struct Prepared {
    r: G1,
    pkc: G1,
    x: G1,
    sig: Sig,
    skc: S,
    nonce: S,
    redeem_hash: ScalarHashPrefix,
}
/// Prepare fresh one-use context-independent native token material.
pub fn prepare(pk: &ValidatedKey, wallet: &Wallet, rng: &mut impl RngCore) -> Result<Prepared> {
    prepare_body(pk, wallet, rng, false)
}
/// Reference/late-import boundary: charge wallet validation at preparation.
/// Ordinary wallets returned by receive use the cached acceptance in prepare.
pub fn prepare_revalidated(
    pk: &ValidatedKey,
    wallet: &Wallet,
    rng: &mut impl RngCore,
) -> Result<Prepared> {
    prepare_body(pk, wallet, rng, true)
}
fn prepare_body(
    pk: &ValidatedKey,
    wallet: &Wallet,
    rng: &mut impl RngCore,
    revalidate: bool,
) -> Result<Prepared> {
    if pk.pk.vk != wallet.key.pk.vk || pk.pk.bit != wallet.key.pk.bit {
        return Err("complete ChgRep input guard");
    }
    if !wallet.signature_validated
        && (wallet.msg.iter().any(|g| !valid1(*g, false))
            || wallet.msg[0] == G1::identity()
            || !signature_members(&wallet.sig)
            || wallet.skc == S::ZERO
            || wallet.msg[1] != g1_mul(wallet.msg[0], wallet.skc)
            || wallet.msg[2]
                != g1_mul(
                    wallet.msg[0],
                    hash_scalar(b"CPAT2/H1/metadata", &wallet.metadata),
                ))
    {
        return Err("complete ChgRep input guard");
    }
    if (revalidate || !wallet.signature_validated)
        && !verify_signature_checked(&pk.pk, &wallet.msg, &wallet.sig)
    {
        return Err("complete ChgRep input guard");
    }
    let mu = random_nonzero(rng);
    let psi = random_nonzero(rng);
    let ip = inv(psi);
    let r = g1_mul(wallet.msg[0], mu);
    let pkc = g1_mul(wallet.msg[1], mu);
    let x = g1_mul(wallet.msg[3], mu);
    let sig = Sig {
        z: g1_mul(wallet.sig.z, mu * psi),
        y: g1_mul(wallet.sig.y, ip),
        yh: g2_mul(wallet.sig.yh, ip),
    };
    let nonce = random_scalar(rng);
    let first = g1_mul(r, nonce);
    // The original redemption transcript starts with these three prepared
    // points, before any tag-dependent point. Absorb their exact canonical
    // bytes here; the one-use state owns the hash continuation privately.
    let mut prefix = enc1(r);
    prefix.extend(enc1(pkc));
    prefix.extend(enc1(first));
    let redeem_hash = ScalarHashPrefix::new(
        b"\x43\x50\x41\x54\x32\x2f\x72\x65\x64\x65\x65\x6d",
        288,
        &prefix,
    );
    Ok(Prepared {
        r,
        pkc,
        x,
        sig,
        skc: wallet.skc,
        nonce,
        redeem_hash,
    })
}
/// Consume native token preparation while binding its online statement.
pub fn show_online(p: Prepared, tag: &[u8]) -> Result<Token> {
    if tag.is_empty() || tag.len() > 1024 * 1024 {
        return Err("tag length");
    }
    let h = hash_g1(b"\x43\x50\x41\x54\x32\x2f\x48\x32\x2f\x74\x61\x67", tag);
    let delta = g1_mul(h, p.skc);
    let second = g1_mul(h, p.nonce);
    let mut suffix = enc1(h);
    suffix.extend(enc1(delta));
    suffix.extend(enc1(second));
    let c = p.redeem_hash.finish(&suffix);
    let proof = DlProof {
        c,
        z: p.nonce - c * p.skc,
    };
    Ok(Token {
        delta,
        tag: tag.to_vec(),
        r: p.r,
        pkc: p.pkc,
        x: p.x,
        sig: p.sig,
        proof,
    })
}
/// One-use native redemption completed before the request: the service tag is
/// already known and CPAT has no separate application context in its transcript.
pub struct PreparedRedemption(Token);
pub fn prepare_redemption(
    pk: &ValidatedKey,
    wallet: &Wallet,
    tag: &[u8],
    rng: &mut impl RngCore,
) -> Result<PreparedRedemption> {
    Ok(PreparedRedemption(show_online(
        prepare(pk, wallet, rng)?,
        tag,
    )?))
}
/// Deliver the already prepared native token; no new group operation is needed.
pub fn present(p: PreparedRedemption) -> Token {
    p.0
}
/// Run native token preparation and online generation.
pub fn show(
    pk: &ValidatedKey,
    wallet: &Wallet,
    tag: &[u8],
    rng: &mut impl RngCore,
) -> Result<Token> {
    show_online(prepare(pk, wallet, rng)?, tag)
}
/// Verify the native complete signature or token equations against the declared statement.
pub fn verify(pk: &ValidatedKey, policy: &Policy, metadata: &[u8], token: &Token) -> bool {
    verify_internal(pk, policy, metadata, token, false)
}
/// Verify a canonically checked token using the installed native public instance.
pub fn verify_checked(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &CheckedToken,
) -> bool {
    verify_internal(pk, policy, metadata, &token.token, true)
}
fn verify_internal(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &Token,
    decoded: bool,
) -> bool {
    verify_relations_internal(pk, policy, metadata, token, decoded, true)
}
fn verify_relations_internal(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &Token,
    decoded: bool,
    check_signature: bool,
) -> bool {
    // Token is public and mutable. Validate every received point once before
    // using it in either signature or DLEQ reconstruction. The alternate path
    // is reachable only through a privately owned immutable checked decode.
    if !policy.allowed.contains(&token.tag)
        || token.r == G1::identity()
        || token.sig.y == G1::identity()
        || token.sig.yh == G2::identity()
        || (!decoded
            && (!valid1(token.delta, false)
                || !valid1(token.r, true)
                || !valid1(token.pkc, false)
                || !valid1(token.x, false)
                || !signature_members(&token.sig)))
    {
        return false;
    }
    let m = hash_scalar(
        b"\x43\x50\x41\x54\x32\x2f\x48\x31\x2f\x6d\x65\x74\x61\x64\x61\x74\x61",
        metadata,
    );
    let msg = [token.r, token.pkc, g1_mul(token.r, m), token.x];
    if check_signature && !verify_signature_checked(&pk.pk, &msg, &token.sig) {
        return false;
    }
    let h = hash_g1(
        b"\x43\x50\x41\x54\x32\x2f\x48\x32\x2f\x74\x61\x67",
        &token.tag,
    );
    verify_dleq_checked(
        b"\x43\x50\x41\x54\x32\x2f\x72\x65\x64\x65\x65\x6d",
        &token.proof,
        &[token.r, h],
        &[token.pkc, token.delta],
        Some(&pk.redeem_hash),
        0,
    )
}
/// Installed same-metadata public signature key. The native metadata coordinate
/// is a public multiple of R, so its G2 key can be combined once at installation.
#[derive(Clone)]
pub struct InstalledMetadata {
    key: ValidatedKey,
    metadata: Vec<u8>,
    combined: [G2; 3],
}
pub fn install_metadata(key: &ValidatedKey, metadata: &[u8]) -> InstalledMetadata {
    let m = hash_scalar(b"CPAT2/H1/metadata", metadata);
    InstalledMetadata {
        key: key.clone(),
        metadata: metadata.to_vec(),
        combined: [
            sum2(&[(key.pk.vk[0], S::ONE), (key.pk.vk[2], m)]),
            key.pk.vk[1],
            key.pk.vk[3],
        ],
    }
}
/// Same-metadata batch with the installed three-coordinate equivalent key.
/// Every individual DLEQ, policy, group and duplicate check is preserved.
pub fn verify_random_batch_metadata(
    installed: &InstalledMetadata,
    policy: &Policy,
    tokens: &[Token],
    rng: &mut impl RngCore,
) -> bool {
    verify_metadata_frozen(installed, policy, tokens.to_vec(), false, rng)
}
pub fn verify_random_batch_metadata_checked(
    installed: &InstalledMetadata,
    policy: &Policy,
    tokens: &[CheckedToken],
    rng: &mut impl RngCore,
) -> bool {
    verify_metadata_frozen(
        installed,
        policy,
        tokens.iter().map(|t| t.token.clone()).collect(),
        true,
        rng,
    )
}
fn verify_metadata_frozen(
    installed: &InstalledMetadata,
    policy: &Policy,
    frozen: Vec<Token>,
    decoded: bool,
    rng: &mut impl RngCore,
) -> bool {
    if frozen.is_empty() {
        return false;
    }
    if frozen.iter().any(|t| {
        !verify_relations_internal(
            &installed.key,
            policy,
            &installed.metadata,
            t,
            decoded,
            false,
        )
    }) {
        return false;
    }
    let mut tags = BTreeSet::new();
    if frozen
        .iter()
        .any(|t| !tags.insert((t.tag.clone(), enc1(t.delta))))
    {
        return false;
    }
    let statements: Vec<_> = frozen
        .iter()
        .map(|t| crate::batch::FhsStatement {
            message: vec![t.r, t.pkc, t.x],
            z: t.sig.z,
            y: t.sig.y,
            yh: t.sig.yh,
        })
        .collect();
    if decoded {
        crate::batch::fhs_random_same_metadata_checked(&installed.combined, &statements, rng)
    } else {
        crate::batch::fhs_random_same_metadata(&installed.combined, &statements, rng)
    }
}
/// Single-token Verify using the same standard verifier-random pairing profile.
pub fn verify_random(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &Token,
    rng: &mut impl RngCore,
) -> bool {
    verify_random_many_inner(pk, policy, metadata, std::slice::from_ref(token), rng)
}
/// Verify k genuinely independent native CPAT tokens. Every policy and DLEQ
/// check remains individual; only the two FHS pairing equations are combined.
/// Tokens obtained by rerandomizing one credential are not independent units.
pub fn verify_random_batch(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    tokens: &[Token],
    rng: &mut impl RngCore,
) -> bool {
    if tokens.len() == 1 {
        return verify_random(pk, policy, metadata, &tokens[0], rng);
    }
    verify_random_many_inner(pk, policy, metadata, tokens, rng)
}
pub fn verify_random_batch_checked(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    tokens: &[CheckedToken],
    rng: &mut impl RngCore,
) -> bool {
    verify_random_frozen(
        pk,
        policy,
        metadata,
        tokens.iter().map(|t| t.token.clone()).collect(),
        true,
        rng,
    )
}
fn verify_random_many_inner(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    tokens: &[Token],
    rng: &mut impl RngCore,
) -> bool {
    verify_random_frozen(pk, policy, metadata, tokens.to_vec(), false, rng)
}
fn verify_random_frozen(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    frozen: Vec<Token>,
    decoded: bool,
    rng: &mut impl RngCore,
) -> bool {
    if frozen.is_empty() {
        return false;
    }
    if frozen
        .iter()
        .any(|t| !verify_relations_internal(pk, policy, metadata, t, decoded, false))
    {
        return false;
    }
    let mut tags = BTreeSet::new();
    if frozen
        .iter()
        .any(|t| !tags.insert((t.tag.clone(), enc1(t.delta))))
    {
        return false;
    }
    let m = hash_scalar(b"CPAT2/H1/metadata", metadata);
    let statements: Vec<_> = frozen
        .iter()
        .map(|t| crate::batch::FhsStatement {
            message: vec![t.r, t.pkc, g1_mul(t.r, m), t.x],
            z: t.sig.z,
            y: t.sig.y,
            yh: t.sig.yh,
        })
        .collect();
    if decoded {
        crate::batch::fhs_random_checked(&pk.pk.vk, &statements, rng)
    } else {
        crate::batch::fhs_random(&pk.pk.vk, &statements, rng)
    }
}
/// Native ReadBit includes token verification before checking the private metadata relation.
pub fn read_bit(
    issuer: &Issuer,
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &Token,
) -> Result<usize> {
    if issuer.pk.vk != pk.pk.vk || issuer.pk.bit != pk.pk.bit {
        return Err("metadata key mismatch");
    }
    if !verify(pk, policy, metadata, token) {
        return Err("invalid token");
    }
    Ok(usize::from(token.x == g1_mul(token.r, issuer.bit_sk[1])))
}
/// Native complete Read from a sealed strictly received token.
pub fn read_bit_checked(
    issuer: &Issuer,
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &CheckedToken,
) -> Result<usize> {
    if issuer.pk.vk != pk.pk.vk || issuer.pk.bit != pk.pk.bit {
        return Err("metadata key mismatch");
    }
    if !verify_checked(pk, policy, metadata, token) {
        return Err("invalid token");
    }
    Ok(usize::from(
        token.token.x == g1_mul(token.token.r, issuer.bit_sk[1]),
    ))
}
/// Complete Read under the fixed metadata-cached SET verifier.
pub fn read_bit_set_checked(
    issuer: &Issuer,
    installed: &InstalledMetadata,
    policy: &Policy,
    token: &CheckedToken,
    weights: &mut impl RngCore,
) -> Result<usize> {
    if !installed.key.matches_public_key(&issuer.pk) {
        return Err("metadata key mismatch");
    }
    if !verify_random_batch_metadata_checked(
        installed,
        policy,
        std::slice::from_ref(token),
        weights,
    ) {
        return Err("invalid token");
    }
    Ok(usize::from(
        token.token.x == g1_mul(token.token.r, issuer.bit_sk[1]),
    ))
}
/// Immutable evidence that the complete native token has been accepted for the
/// installed issuer, declared metadata and service policy.
pub struct VerifiedToken {
    token: Token,
    key: ValidatedKey,
}
pub fn verify_record(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &Token,
) -> Result<VerifiedToken> {
    if !verify(pk, policy, metadata, token) {
        return Err("invalid token");
    }
    Ok(VerifiedToken {
        token: token.clone(),
        key: pk.clone(),
    })
}
pub fn verify_record_checked(
    pk: &ValidatedKey,
    policy: &Policy,
    metadata: &[u8],
    token: &CheckedToken,
) -> Result<VerifiedToken> {
    if !verify_checked(pk, policy, metadata, token) {
        return Err("invalid token");
    }
    Ok(VerifiedToken {
        token: token.token.clone(),
        key: pk.clone(),
    })
}
pub fn verify_random_batch_metadata_records_checked(
    installed: &InstalledMetadata,
    policy: &Policy,
    tokens: &[CheckedToken],
    weights: &mut impl RngCore,
) -> Result<Vec<VerifiedToken>> {
    if !verify_random_batch_metadata_checked(installed, policy, tokens, weights) {
        return Err("invalid token batch");
    }
    Ok(tokens
        .iter()
        .map(|t| VerifiedToken {
            token: t.token.clone(),
            key: installed.key.clone(),
        })
        .collect())
}
/// Incremental reading of one already verified immutable record.
pub fn read_bit_validated(issuer: &Issuer, record: &VerifiedToken) -> Result<usize> {
    if issuer.pk.vk != record.key.pk.vk || issuer.pk.bit != record.key.pk.bit {
        return Err("metadata key mismatch");
    }
    Ok(usize::from(
        record.token.x == g1_mul(record.token.r, issuer.bit_sk[1]),
    ))
}
impl Token {
    /// Canonical/subgroup and native field-domain checks only; no DLEQ/FHS check.
    pub fn decode_received(bytes: &[u8]) -> Result<Self> {
        let token = Self::decode(bytes)?;
        if token.r == G1::identity()
            || token.sig.y == G1::identity()
            || token.sig.yh == G2::identity()
        {
            return Err("CPAT received-token identity domain");
        }
        Ok(token)
    }

    /// δ, τ, R*, pkc*, X*, signature(2G1+G2), DLEQ(c,z). Tag length is explicit.
    pub fn payload_bytes(&self) -> usize {
        8 * 48 + 64 + self.tag.len()
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut b = b"\x45\x56\x41\x2d\x43\x50\x41\x54\x2d\x32".to_vec();
        frame(&mut b, &self.tag);
        for p in [self.delta, self.r, self.pkc, self.x, self.sig.z, self.sig.y] {
            b.extend(enc1(p));
        }
        b.extend(enc2(self.sig.yh));
        b.extend(encs(self.proof.c));
        b.extend(encs(self.proof.z));
        b
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        const HEADER: &[u8] = b"\x45\x56\x41\x2d\x43\x50\x41\x54\x2d\x32";
        if b.len() < HEADER.len() + 8 || &b[..HEADER.len()] != HEADER {
            return Err("header");
        }
        let mut p = HEADER.len();
        let len = usize::try_from(u64::from_be_bytes(b[p..p + 8].try_into().unwrap()))
            .map_err(|_| "length overflow")?;
        p += 8;
        if len > 1024 * 1024 || b.len() != p + len + 448 {
            return Err("length");
        }
        let tag = b[p..p + len].to_vec();
        p += len;
        let mut gs = vec![];
        for _ in 0..6 {
            gs.push(
                crate::canonical::decode_g1(&b[p..p + 48]).map_err(|_| "canonical G1/subgroup")?,
            );
            p += 48;
        }
        let yh = crate::canonical::decode_g2(&b[p..p + 96]).map_err(|_| "canonical G2/subgroup")?;
        p += 96;
        let c = Option::<S>::from(S::from_bytes_be(b[p..p + 32].try_into().unwrap()))
            .ok_or("scalar")?;
        p += 32;
        let z = Option::<S>::from(S::from_bytes_be(b[p..p + 32].try_into().unwrap()))
            .ok_or("scalar")?;
        Ok(Self {
            delta: gs[0],
            tag,
            r: gs[1],
            pkc: gs[2],
            x: gs[3],
            sig: Sig {
                z: gs[4],
                y: gs[5],
                yh,
            },
            proof: DlProof { c, z },
        })
    }
}
impl Request {
    pub fn payload_bytes(&self) -> usize {
        48 + 64
    }
}
impl Response {
    pub fn payload_bytes(&self) -> usize {
        3 * 48 + 192 + 128
    }
}
impl Wallet {
    /// Import native wallet components without claiming signature acceptance.
    /// Preparation validates the full message, holder secret and signature.
    pub fn import_unverified(
        key: &ValidatedKey,
        msg: [G1; 4],
        skc: S,
        sig: Sig,
        metadata: Vec<u8>,
    ) -> Self {
        Self {
            msg,
            skc,
            sig,
            metadata,
            key: key.clone(),
            signature_validated: false,
        }
    }
    pub fn payload_bytes(&self) -> usize {
        4 * 48 + 32 + 192 + self.metadata.len()
    }
}

// Native negative-test helper; not part of ordinary protocol execution.
// Native negative-test helper; not part of ordinary protocol execution.
// Native negative-test helper; not part of ordinary protocol execution.
// Native negative-test helper; not part of ordinary protocol execution.
#[cfg(test)]
fn verify_dleq_cached(
    tag: &[u8],
    proof: &DlProof,
    base: &[G1],
    target: &[G1],
    cached: Option<&CachedScalarHashPrefix>,
    skip: usize,
) -> bool {
    if base.len() != target.len()
        || base.is_empty()
        || base.iter().any(|g| !valid1(*g, true))
        || target.iter().any(|g| !valid1(*g, false))
    {
        return false;
    }
    verify_dleq_checked(tag, proof, base, target, cached, skip)
}

#[cfg(test)]
fn verify_dleq(tag: &[u8], proof: &DlProof, base: &[G1], target: &[G1]) -> bool {
    verify_dleq_cached(tag, proof, base, target, None, 0)
}

#[cfg(test)]
fn dleq(tag: &[u8], x: S, base: &[G1], target: &[G1], rng: &mut impl RngCore) -> DlProof {
    dleq_cached(tag, x, base, target, rng, None, 0)
}

#[cfg(test)]
// Retain the exact shared native guard or state layout; current checked paths may not call every fallback.
#[allow(dead_code)]
fn fs(tag: &[u8], points: &[G1]) -> S {
    fs_cached(tag, points, None, 0)
}

#[cfg(test)]
mod credential_integrity_tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn full_guard_rejects_replaced_signature_or_public_key() {
        let mut rng = StdRng::seed_from_u64(404);
        let iss = keygen(&mut rng);
        let pk = validate_key(&iss.pk).unwrap();
        let (req, p) = request(&pk, b"metadata", &mut rng);
        let res = issue(&iss, &req, b"metadata", 1, &mut rng).unwrap();
        let w = receive(p, &res).unwrap();
        let mut bad_sig = w.sig.clone();
        bad_sig.z += G1::generator();
        let imported = Wallet::import_unverified(&pk, w.msg, w.skc, bad_sig, w.metadata.clone());
        assert!(prepare(&pk, &imported, &mut rng).is_err());
        let imported = Wallet::import_unverified(
            &pk,
            w.msg,
            w.skc + S::ONE,
            w.sig.clone(),
            w.metadata.clone(),
        );
        assert!(prepare(&pk, &imported, &mut rng).is_err());
        let other = keygen(&mut rng);
        let op = validate_key(&other.pk).unwrap();
        assert!(prepare(&op, &w, &mut rng).is_err());
        start_counts();
        let _ = prepare(&pk, &w, &mut rng).unwrap();
        let c = stop_counts();
        assert_eq!((c.e1, c.e2, c.p + c.mp_terms), (6, 1, 0));
        let imported =
            Wallet::import_unverified(&pk, w.msg, w.skc, w.sig.clone(), w.metadata.clone());
        start_counts();
        prepare(&pk, &imported, &mut rng).unwrap();
        let c = stop_counts();
        assert_eq!((c.e1, c.e2, c.p + c.mp_terms), (8, 1, 7));
    }
    #[test]
    fn fused_issuer_signature_has_same_equation_and_value() {
        let mut rng = StdRng::seed_from_u64(405);
        let iss = keygen(&mut rng);
        let r = g1_mul(G1::generator(), S::from(11));
        let pkc = g1_mul(G1::generator(), S::from(17));
        let m = S::from(23);
        let y = S::from(29);
        let msg = [r, pkc, g1_mul(r, m), g1_mul(r, iss.bit_sk[1])];
        let ordinary = sum1(&(0..4).map(|i| (msg[i], iss.sk[i] * y)).collect::<Vec<_>>());
        let fused = sum1(&[
            (
                r,
                y * (iss.sk[0] + m * iss.sk[2] + iss.bit_sk[1] * iss.sk[3]),
            ),
            (pkc, y * iss.sk[1]),
        ]);
        assert_eq!(ordinary, fused);
    }
    #[test]
    fn two_dleq_relations_cannot_use_different_secrets() {
        let mut rng = StdRng::seed_from_u64(408);
        let b = [G1::generator(), hash_g1(b"cpat2-test", b"second")];
        let t = [g1_mul(b[0], S::from(13)), g1_mul(b[1], S::from(17))];
        let proof = dleq(b"test", S::from(13), &b, &t, &mut rng);
        assert!(!verify_dleq(b"test", &proof, &b, &t));
    }
}
