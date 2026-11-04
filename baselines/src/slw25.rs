//! Flat no-revocation credentials over BLS12-381 with interactive CDM proofs.
//! Coordinates 0 and 1 authenticate the holder secret and eid; business indices
//! start at 2. Each prepared object is consumed by exactly one interaction.
use crate::arithmetic::*;
use crate::cdm as mv;
use crate::encoding::{Error, Reader, Result, Writer};
pub use crate::pairing_verify::Mode as VerificationMode;
use crate::pairing_verify::{self, Equation};
use ff::Field;
use group::Group;
use rand::{CryptoRng, RngCore};
use std::sync::Arc;

pub const MAX_BUSINESS: usize = 128;
/// The evaluated profile is the source's flat configuration without revocation.
pub const REVOCATION_ENABLED: bool = false;
fn fail<T>(s: &str) -> Result<T> {
    Err(Error(s.into()))
}
fn need(b: bool, s: &str) -> Result<()> {
    if b {
        Ok(())
    } else {
        fail(s)
    }
}
fn add1(xs: impl IntoIterator<Item = G1>) -> G1 {
    xs.into_iter().fold(G1::identity(), g1_add)
}
fn add2(xs: impl IntoIterator<Item = G2>) -> G2 {
    xs.into_iter().fold(G2::identity(), g2_add)
}
fn valid_business(indices: &[usize], k: usize) -> bool {
    indices.iter().all(|&i| i >= 2 && i < k + 2) && indices.windows(2).all(|w| w[0] < w[1])
}
fn all_business(k: usize) -> Vec<usize> {
    (2..k + 2).collect()
}
fn coordinates(keep: &[usize]) -> Vec<usize> {
    [vec![0, 1], keep.to_vec()].concat()
}

#[derive(Clone)]
pub struct PublicKeyData {
    pub x: G1,
    pub y: Vec<G1>,
    pub yh: Vec<G2>,
    pub z: Vec<Vec<G1>>,
}
/// An immutable installed public key; setup produces it locally or install
/// validates canonical received group points and all cross-group relations.
#[derive(Clone)]
pub struct PublicKey(Arc<PublicKeyData>, [u8; 32]);
pub struct IssuerSecret {
    x: S,
    y: Vec<S>,
}
#[derive(Clone)]
pub struct Holder {
    usk: S,
    eid: S,
    upk: G2,
}
impl Holder {
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        Self::from_secrets(random_nonzero(rng), random_scalar(rng)).expect("nonzero secret")
    }
    pub fn from_secrets(usk: S, eid: S) -> Result<Self> {
        need(usk != S::ZERO, "holder secret domain")?;
        Ok(Self {
            usk,
            eid,
            upk: g2_mul(G2::generator(), usk),
        })
    }
    pub fn public_key(&self) -> G2 {
        self.upk
    }
    pub fn eid(&self) -> S {
        self.eid
    }
}
impl PublicKey {
    pub fn business(&self) -> usize {
        self.0.y.len() - 2
    }
    pub fn raw(&self) -> PublicKeyData {
        (*self.0).clone()
    }
    /// Application namespace for an installed native issuer. This does not
    /// add a field to any native protocol message.
    pub fn issuer_id(&self) -> [u8; 32] {
        self.1
    }
    fn installed(raw: PublicKeyData) -> Self {
        let mut key = Self(Arc::new(raw), [0; 32]);
        key.1 = digest(&key.encode()).try_into().expect("SHA-256 length");
        key
    }
    pub fn install(raw: PublicKeyData) -> Result<Self> {
        Self::install_checked(raw, false)
    }
    /// Validate all cross-group parameter relations with a single randomized
    /// pairing product after dimensions, domains, symmetry and diagonals pass.
    pub fn install_profile(
        raw: PublicKeyData,
        profile: VerificationMode,
        rng: &mut impl RngCore,
    ) -> Result<Self> {
        if profile == VerificationMode::Specification {
            return Self::install(raw);
        }
        let n = raw.y.len();
        need(
            (3..=MAX_BUSINESS + 2).contains(&n)
                && raw.yh.len() == n
                && raw.z.len() == n
                && raw.z.iter().all(|r| r.len() == n),
            "public key dimensions",
        )?;
        need(
            valid1(raw.x, true)
                && raw.y.iter().all(|p| valid1(*p, true))
                && raw.yh.iter().all(|p| valid2(*p, true)),
            "public key domain",
        )?;
        let mut equations = Vec::new();
        for i in 0..n {
            need(
                raw.z[i][i] == G1::identity() && valid1(raw.z[i][i], false),
                "diagonal convention",
            )?;
            equations.push(Equation {
                terms: vec![(raw.y[i], G2::generator()), (-G1::generator(), raw.yh[i])],
                target: GT::identity(),
            });
            for j in i + 1..n {
                need(
                    valid1(raw.z[i][j], true)
                        && valid1(raw.z[j][i], true)
                        && raw.z[i][j] == raw.z[j][i],
                    "public key cross domain/symmetry",
                )?;
                equations.push(Equation {
                    terms: vec![(raw.z[i][j], G2::generator()), (-raw.y[i], raw.yh[j])],
                    target: GT::identity(),
                });
            }
        }
        need(
            pairing_verify::verify(&equations, profile, rng),
            "public key group relations",
        )?;
        Ok(Self::installed(raw))
    }
    #[allow(clippy::manual_range_contains)]
    fn install_checked(raw: PublicKeyData, decoded: bool) -> Result<Self> {
        let n = raw.y.len();
        need(
            n >= 3
                && n <= MAX_BUSINESS + 2
                && raw.yh.len() == n
                && raw.z.len() == n
                && raw.z.iter().all(|r| r.len() == n),
            "public key dimensions",
        )?;
        if !decoded {
            need(
                valid1(raw.x, true)
                    && raw.y.iter().all(|&p| valid1(p, true))
                    && raw.yh.iter().all(|&p| valid2(p, true)),
                "public key domain",
            )?;
        }
        for i in 0..n {
            need(
                pair(raw.y[i], G2::generator()) == pair(G1::generator(), raw.yh[i]),
                "public key group relation",
            )?;
            need(raw.z[i][i] == G1::identity(), "diagonal convention")?;
            for j in i + 1..n {
                if !decoded {
                    need(
                        valid1(raw.z[i][j], true) && valid1(raw.z[j][i], true),
                        "public key cross point domain",
                    )?;
                }
                need(
                    raw.z[i][j] == raw.z[j][i]
                        && pair(raw.z[i][j], G2::generator()) == pair(raw.y[i], raw.yh[j]),
                    "public key cross relation",
                )?;
            }
        }
        Ok(Self::installed(raw))
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(b"\x53\x4c\x57\x32\x34\x2d\x50\x4b\x2d\x76\x31");
        w.u32(self.business() as u32);
        w.g1(self.0.x);
        for i in 0..self.0.y.len() {
            w.g1(self.0.y[i]);
            w.g2(self.0.yh[i]);
        }
        for i in 0..self.0.y.len() {
            for j in 0..self.0.y.len() {
                if i != j {
                    w.g1(self.0.z[i][j]);
                }
            }
        }
        w.finish()
    }
    pub fn decode_install(bytes: &[u8]) -> Result<Self> {
        Self::install_checked(Self::decode_raw(bytes)?, true)
    }
    pub fn decode_install_profile(
        bytes: &[u8],
        profile: VerificationMode,
        rng: &mut impl RngCore,
    ) -> Result<Self> {
        if profile == VerificationMode::Specification {
            return Self::decode_install(bytes);
        }
        Self::install_profile(Self::decode_raw(bytes)?, profile, rng)
    }
    fn decode_raw(bytes: &[u8]) -> Result<PublicKeyData> {
        let mut r = Reader::new(bytes, b"\x53\x4c\x57\x32\x34\x2d\x50\x4b\x2d\x76\x31")?;
        let k = r.u32()? as usize;
        need((1..=MAX_BUSINESS).contains(&k), "business dimension")?;
        let n = k + 2;
        let x = r.g1(true)?;
        let mut y = vec![];
        let mut yh = vec![];
        for _ in 0..n {
            y.push(r.g1(true)?);
            yh.push(r.g2(true)?);
        }
        let mut z = vec![vec![G1::identity(); n]; n];
        for (i, row) in z.iter_mut().enumerate() {
            for (j, p) in row.iter_mut().enumerate() {
                if i != j {
                    *p = r.g1(true)?;
                }
            }
        }
        r.finish()?;
        Ok(PublicKeyData { x, y, yh, z })
    }
}
/// Create in-memory public parameters for this native scheme.
pub fn setup<R: RngCore + CryptoRng>(k: usize, rng: &mut R) -> Result<(PublicKey, IssuerSecret)> {
    need((1..=MAX_BUSINESS).contains(&k), "business dimension")?;
    let x = random_nonzero(rng);
    let y: Vec<_> = (0..k + 2).map(|_| random_nonzero(rng)).collect();
    let n = y.len();
    let mut z = vec![vec![G1::identity(); n]; n];
    for i in 0..n {
        for j in i + 1..n {
            let p = g1_mul(G1::generator(), y[i] * y[j]);
            z[i][j] = p;
            z[j][i] = p;
        }
    }
    let raw = PublicKeyData {
        x: g1_mul(G1::generator(), x),
        y: y.iter().map(|&v| g1_mul(G1::generator(), v)).collect(),
        yh: y.iter().map(|&v| g2_mul(G2::generator(), v)).collect(),
        z,
    };
    Ok((PublicKey::installed(raw), IssuerSecret { x, y }))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Original,
    Partial,
}
#[derive(Clone, Copy)]
struct Signature {
    p: G1,
    q: G1,
    a: G2,
    b: G2,
}
/// Only receive creates an accepted credential. Reusable credentials are
/// distinct from the one-use preparation and proof states.
#[derive(Clone)]
pub struct Credential {
    mode: Mode,
    keep: Vec<usize>,
    attrs: Vec<S>,
    sig: Signature,
    uk: Option<[G2; 2]>,
}
impl Credential {
    pub fn mode(&self) -> Mode {
        self.mode
    }
    pub fn retained(&self) -> &[usize] {
        &self.keep
    }
    pub fn attributes(&self) -> &[S] {
        &self.attrs
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(
            b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31",
        );
        w.u8(if self.mode == Mode::Original { 0 } else { 1 });
        w.indices(&self.keep);
        for &m in &self.attrs {
            w.fr(m);
        }
        if self.mode == Mode::Partial {
            w.g1(self.sig.p);
            w.g1(self.sig.q);
        }
        w.g2(self.sig.a);
        w.g2(self.sig.b);
        if let Some(uk) = self.uk {
            w.g2(uk[0]);
            w.g2(uk[1]);
        }
        w.finish()
    }
    fn decode(pk: &PublicKey, bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(
            bytes,
            b"\x53\x4c\x57\x32\x34\x2d\x63\x72\x65\x64\x65\x6e\x74\x69\x61\x6c\x2d\x76\x31",
        )?;
        let mode = match r.u8()? {
            0 => Mode::Original,
            1 => Mode::Partial,
            _ => return fail("credential mode"),
        };
        let keep = r.indices(pk.business() + 2)?;
        need(valid_business(&keep, pk.business()), "business indices")?;
        if mode == Mode::Original {
            need(
                keep == all_business(pk.business()),
                "original credential indices",
            )?;
        }
        let attrs = (0..keep.len())
            .map(|_| r.fr())
            .collect::<Result<Vec<_>>>()?;
        let (p, q) = if mode == Mode::Partial {
            (r.g1(false)?, r.g1(false)?)
        } else {
            (G1::identity(), G1::identity())
        };
        let a = r.g2(true)?;
        let b = r.g2(false)?;
        let uk = if mode == Mode::Original {
            Some([r.g2(true)?, r.g2(true)?])
        } else {
            None
        };
        r.finish()?;
        Ok(Self {
            mode,
            keep,
            attrs,
            sig: Signature { p, q, a, b },
            uk,
        })
    }
}
fn message_target(pk: &PublicKey, h: &Holder, c: &Credential) -> G1 {
    let own = sum1(&[(pk.0.y[0], h.usk), (pk.0.y[1], h.eid)]);
    let terms: Vec<_> = c
        .keep
        .iter()
        .zip(&c.attrs)
        .map(|(&i, &v)| (pk.0.y[i], v))
        .collect();
    g1_add(g1_add(g1_add(pk.0.x, c.sig.p), own), sum1(&terms))
}
fn credential_valid(pk: &PublicKey, h: &Holder, c: &Credential) -> bool {
    if c.keep.len() != c.attrs.len()
        || !valid_business(&c.keep, pk.business())
        || c.sig.a == G2::identity()
    {
        return false;
    }
    if pair(message_target(pk, h, c), c.sig.a) != pair(G1::generator(), c.sig.b) {
        return false;
    }
    match c.mode {
        Mode::Original => {
            c.keep == all_business(pk.business())
                && c.sig.p == G1::identity()
                && c.sig.q == G1::identity()
                && c.uk.is_some_and(|uk| {
                    (0..2).all(|i| pair(G1::generator(), uk[i]) == pair(pk.0.y[i], c.sig.a))
                })
        }
        Mode::Partial => {
            c.uk.is_none()
                && pair(
                    c.sig.p,
                    add2(coordinates(&c.keep).iter().map(|&i| pk.0.yh[i])),
                ) == pair(c.sig.q, G2::generator())
        }
    }
}

fn credential_equations(pk: &PublicKey, h: &Holder, c: &Credential) -> Result<Vec<Equation>> {
    need(
        c.keep.len() == c.attrs.len()
            && valid_business(&c.keep, pk.business())
            && c.sig.a != G2::identity(),
        "credential dimensions/domain",
    )?;
    let mut equations = vec![Equation {
        terms: vec![
            (message_target(pk, h, c), c.sig.a),
            (-G1::generator(), c.sig.b),
        ],
        target: GT::identity(),
    }];
    match c.mode {
        Mode::Original => {
            need(
                c.keep == all_business(pk.business())
                    && c.sig.p == G1::identity()
                    && c.sig.q == G1::identity(),
                "original credential coordinates",
            )?;
            let uk = c.uk.ok_or_else(|| Error("original update key".into()))?;
            need(uk.iter().all(|p| *p != G2::identity()), "update key domain")?;
            for (i, point) in uk.into_iter().enumerate() {
                equations.push(Equation {
                    terms: vec![(G1::generator(), point), (-pk.0.y[i], c.sig.a)],
                    target: GT::identity(),
                });
            }
        }
        Mode::Partial => {
            need(c.uk.is_none(), "partial update key")?;
            equations.push(Equation {
                terms: vec![
                    (
                        c.sig.p,
                        add2(coordinates(&c.keep).iter().map(|&i| pk.0.yh[i])),
                    ),
                    (-c.sig.q, G2::generator()),
                ],
                target: GT::identity(),
            });
        }
    }
    Ok(equations)
}

/// Accept the same native credential with all signature/update/purge
/// equations fixed before independent verifier weights are sampled.
pub fn receive_profile(
    pk: &PublicKey,
    h: &Holder,
    bytes: &[u8],
    profile: VerificationMode,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    if profile == VerificationMode::Specification {
        return receive(pk, h, bytes);
    }
    let c = Credential::decode(pk, bytes)?;
    need(
        pairing_verify::verify_checked(&credential_equations(pk, h, &c)?, profile, rng),
        "credential verification",
    )?;
    Ok(c)
}

pub fn receive_expected_profile(
    pk: &PublicKey,
    h: &Holder,
    bytes: &[u8],
    keep: &[usize],
    attrs: &[S],
    profile: VerificationMode,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    // The application disclosure/attribute contract precedes random coins.
    let c = Credential::decode(pk, bytes)?;
    need(
        c.keep == keep && c.attrs == attrs,
        "credential attribute contract",
    )?;
    if profile == VerificationMode::Specification {
        need(credential_valid(pk, h, &c), "credential verification")?;
    } else {
        need(
            pairing_verify::verify_checked(&credential_equations(pk, h, &c)?, profile, rng),
            "credential verification",
        )?;
    }
    Ok(c)
}
/// Validate the native issuer response or delivery and obtain holder material.
pub fn receive(pk: &PublicKey, h: &Holder, bytes: &[u8]) -> Result<Credential> {
    let c = Credential::decode(pk, bytes)?;
    need(credential_valid(pk, h, &c), "credential verification")?;
    Ok(c)
}
pub fn receive_expected(
    pk: &PublicKey,
    h: &Holder,
    bytes: &[u8],
    keep: &[usize],
    attrs: &[S],
) -> Result<Credential> {
    let c = receive(pk, h, bytes)?;
    need(
        c.keep == keep && c.attrs == attrs,
        "credential attribute contract",
    )?;
    Ok(c)
}

#[derive(Clone)]
pub struct IssueRequest {
    upk: G2,
    eid: S,
    attrs: Vec<S>,
}
impl IssueRequest {
    pub fn new(pk: &PublicKey, h: &Holder, attrs: &[S]) -> Result<Self> {
        need(attrs.len() == pk.business(), "issue attributes")?;
        Ok(Self {
            upk: h.upk,
            eid: h.eid,
            attrs: attrs.to_vec(),
        })
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(b"\x53\x4c\x57\x32\x34\x2d\x69\x73\x73\x75\x65\x2d\x72\x65\x71\x75\x65\x73\x74\x2d\x76\x31");
        w.g2(self.upk);
        w.fr(self.eid);
        w.u32(self.attrs.len() as u32);
        for &v in &self.attrs {
            w.fr(v);
        }
        w.finish()
    }
    fn decode(pk: &PublicKey, bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, b"\x53\x4c\x57\x32\x34\x2d\x69\x73\x73\x75\x65\x2d\x72\x65\x71\x75\x65\x73\x74\x2d\x76\x31")?;
        let upk = r.g2(true)?;
        let eid = r.fr()?;
        need(r.u32()? as usize == pk.business(), "issue dimension")?;
        let attrs = (0..pk.business())
            .map(|_| r.fr())
            .collect::<Result<Vec<_>>>()?;
        r.finish()?;
        Ok(Self { upk, eid, attrs })
    }
    fn relation(&self) -> Result<mv::Relation> {
        mv::Relation::g2_trusted(vec![G2::generator()], self.upk)
    }
}
pub struct IssueIssuerAwaitFirst {
    req: IssueRequest,
    proof: mv::VerifierAwaitFirst,
}
pub struct IssueIssuerAwaitFourth {
    req: IssueRequest,
    proof: mv::VerifierAwaitFourth,
}
pub struct IssueHolderAwaitThird(mv::ProverAwaitThird);
/// Create the holder request for native credential acquisition.
pub fn issue_request(pk: &PublicKey, h: &Holder, attrs: &[S]) -> Result<Vec<u8>> {
    Ok(IssueRequest::new(pk, h, attrs)?.encode())
}
pub struct IssuePrepared(Option<(mv::Relation, S)>);
/// Retain the sender's validated local request instead of decoding it again.
pub fn issue_prepare(pk: &PublicKey, h: &Holder, attrs: &[S]) -> Result<(IssuePrepared, Vec<u8>)> {
    let req = IssueRequest::new(pk, h, attrs)?;
    let relation = req.relation()?;
    Ok((IssuePrepared(Some((relation, h.usk))), req.encode()))
}
pub fn holder_issue_first_prepared<R: RngCore + CryptoRng>(
    prepared: &mut IssuePrepared,
    v1: &[u8],
    rng: &mut R,
) -> Result<(IssueHolderAwaitThird, Vec<u8>)> {
    let (relation, witness) = prepared
        .0
        .take()
        .ok_or_else(|| Error("issue prepared already consumed".into()))?;
    let (proof, msg) =
        mv::prover_begin_decoded(&relation, &[witness], &mv::VFirst::decode(v1)?, rng)?;
    Ok((IssueHolderAwaitThird(proof), msg.encode()))
}
/// Begin the live issuer proof exchange on the native request.
pub fn issuer_begin<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    request: &[u8],
    rng: &mut R,
) -> Result<(IssueIssuerAwaitFirst, Vec<u8>)> {
    let req = IssueRequest::decode(pk, request)?;
    let (proof, msg) = mv::verifier_begin(&req.relation()?, rng)?;
    Ok((IssueIssuerAwaitFirst { req, proof }, msg.encode()))
}
pub fn holder_issue_first<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    request: &[u8],
    v1: &[u8],
    rng: &mut R,
) -> Result<(IssueHolderAwaitThird, Vec<u8>)> {
    let req = IssueRequest::decode(pk, request)?;
    need(req.upk == h.upk && req.eid == h.eid, "holder request")?;
    let first = mv::VFirst::decode(v1)?;
    let (state, msg) = mv::prover_begin_decoded(&req.relation()?, &[h.usk], &first, rng)?;
    Ok((IssueHolderAwaitThird(state), msg.encode()))
}
pub fn issuer_issue_challenge<R: RngCore + CryptoRng>(
    state: IssueIssuerAwaitFirst,
    p2: &[u8],
    rng: &mut R,
) -> Result<(IssueIssuerAwaitFourth, Vec<u8>)> {
    let (proof, msg) = mv::verifier_challenge_decoded(state.proof, mv::PFirst::decode(p2)?, rng)?;
    Ok((
        IssueIssuerAwaitFourth {
            req: state.req,
            proof,
        },
        msg.encode(),
    ))
}
pub fn holder_issue_respond(state: IssueHolderAwaitThird, v3: &[u8]) -> Result<Vec<u8>> {
    Ok(mv::prover_respond(state.0, mv::VThird::decode(v3)?)?.encode())
}
/// Finish the native issuer proof and produce the credential response.
pub fn issuer_issue_finish<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    sk: &IssuerSecret,
    state: IssueIssuerAwaitFourth,
    p4: &[u8],
    rng: &mut R,
) -> Result<Vec<u8>> {
    need(
        mv::verifier_finish(state.proof, mv::PFourth::decode(p4)?),
        "issuance knowledge proof",
    )?;
    need(
        sk.y.len() == pk.business() + 2 && state.req.attrs.len() == pk.business(),
        "issuer dimensions",
    )?;
    let r = random_nonzero(rng);
    let a = g2_mul(G2::generator(), r);
    let d = sk.x
        + sk.y[1] * state.req.eid
        + sk.y[2..]
            .iter()
            .zip(&state.req.attrs)
            .map(|(&y, &m)| y * m)
            .sum::<S>();
    let b = sum2(&[(state.req.upk, r * sk.y[0]), (a, d)]);
    let c = Credential {
        mode: Mode::Original,
        keep: all_business(pk.business()),
        attrs: state.req.attrs,
        sig: Signature {
            p: G1::identity(),
            q: G1::identity(),
            a,
            b,
        },
        uk: Some([g2_mul(a, sk.y[0]), g2_mul(a, sk.y[1])]),
    };
    Ok(c.encode())
}

struct DelegateData {
    keys: [G2; 2],
    keep: Vec<usize>,
    attrs: Vec<S>,
    sig: Signature,
    cm_scale: S,
}
pub struct DelegationPrepared(Option<DelegateData>);
pub struct DelegateAwaitFirst {
    data: DelegateData,
    proof: mv::VerifierAwaitFirst,
}
pub struct DelegateAwaitFourth {
    data: DelegateData,
    proof: mv::VerifierAwaitFourth,
}
pub struct ReceiverCommitment {
    relation: mv::Relation,
    witness: [S; 2],
}
pub struct ReceiverAwaitThird(mv::ProverAwaitThird);
fn purge_parts(pk: &PublicKey, c: &Credential, keep: &[usize], t: S) -> (G1, G1) {
    let dropped: Vec<_> = c
        .keep
        .iter()
        .zip(&c.attrs)
        .filter(|(i, _)| !keep.contains(i))
        .map(|(&i, &v)| (i, v))
        .collect();
    let mut pterms: Vec<_> = dropped.iter().map(|&(i, v)| (pk.0.y[i], v)).collect();
    pterms.push((G1::generator(), t));
    let p = sum1(&pterms);
    let coords = coordinates(keep);
    let aggregate_y = add1(coords.iter().map(|&i| pk.0.y[i]));
    let mut terms: Vec<_> = dropped
        .iter()
        .map(|&(j, v)| (add1(coords.iter().map(|&i| pk.0.z[i][j])), v))
        .collect();
    terms.push((aggregate_y, t));
    let q = sum1(&terms);
    (p, q)
}
struct DelegateBase {
    data: DelegateData,
    source: Credential,
    t: S,
}
pub struct DelegationPrecomputed(Option<DelegateBase>);
/// Policy-independent work: fresh key switching and signature masks.
/// Prepare fresh one-use native delegation material before receiver binding.
pub fn delegate_precompute<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    c: &Credential,
    rng: &mut R,
) -> Result<DelegationPrecomputed> {
    need(
        c.mode == Mode::Original && c.keep == all_business(pk.business()) && c.uk.is_some(),
        "flat delegation requires original credential",
    )?;
    let [k, u, s, t] = [
        random_nonzero(rng),
        random_nonzero(rng),
        random_nonzero(rng),
        random_nonzero(rng),
    ];
    let uk = c.uk.unwrap();
    let keys = uk.map(|p| g2_mul(p, k));
    let a = g2_mul(c.sig.a, k * u * s);
    let b = sum2(&[
        (c.sig.b, k * u * s),
        (keys[0], -h.usk * u * s),
        (keys[1], -h.eid * u * s),
        (a, t),
    ]);
    let data = DelegateData {
        keys,
        keep: vec![],
        attrs: vec![],
        sig: Signature {
            p: G1::identity(),
            q: G1::identity(),
            a,
            b,
        },
        cm_scale: u * s,
    };
    Ok(DelegationPrecomputed(Some(DelegateBase {
        data,
        source: c.clone(),
        t,
    })))
}
/// Bind the retained subset after precomputation; this work is online.
/// Bind native prepared delegation to the requested retained attributes.
pub fn delegate_bind(
    pk: &PublicKey,
    precomputed: &mut DelegationPrecomputed,
    keep: &[usize],
) -> Result<(DelegationPrepared, Vec<u8>)> {
    let base = precomputed
        .0
        .take()
        .ok_or_else(|| Error("delegation precomputation already consumed".into()))?;
    need(valid_business(keep, pk.business()), "delegation indices")?;
    let (p, q) = purge_parts(pk, &base.source, keep, base.t);
    let mut data = base.data;
    data.sig.p = p;
    data.sig.q = q;
    data.keep = keep.to_vec();
    data.attrs = keep.iter().map(|&i| base.source.attrs[i - 2]).collect();
    let mut w = Writer::new(b"\x53\x4c\x57\x32\x34\x2d\x64\x65\x6c\x65\x67\x61\x74\x65\x2d\x70\x72\x65\x66\x69\x78\x2d\x76\x31");
    w.g2(data.keys[0]);
    w.g2(data.keys[1]);
    w.indices(keep);
    Ok((DelegationPrepared(Some(data)), w.finish()))
}
pub fn delegate_prepare<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    c: &Credential,
    keep: &[usize],
    rng: &mut R,
) -> Result<(DelegationPrepared, Vec<u8>)> {
    let mut offline = delegate_precompute(pk, h, c, rng)?;
    delegate_bind(pk, &mut offline, keep)
}
fn read_delegate_prefix(pk: &PublicKey, bytes: &[u8]) -> Result<([G2; 2], Vec<usize>)> {
    let mut r = Reader::new(bytes, b"\x53\x4c\x57\x32\x34\x2d\x64\x65\x6c\x65\x67\x61\x74\x65\x2d\x70\x72\x65\x66\x69\x78\x2d\x76\x31")?;
    let keys = [r.g2(true)?, r.g2(true)?];
    let keep = r.indices(pk.business() + 2)?;
    need(valid_business(&keep, pk.business()), "delegation indices")?;
    r.finish()?;
    Ok((keys, keep))
}
/// Construct the native receiver commitment for the live delegation exchange.
pub fn receiver_cm(
    pk: &PublicKey,
    h: &Holder,
    prefix: &[u8],
) -> Result<(ReceiverCommitment, Vec<u8>)> {
    let (keys, _) = read_delegate_prefix(pk, prefix)?;
    let cm = sum2(&[(keys[0], h.usk), (keys[1], h.eid)]);
    let relation = mv::Relation::g2_trusted(keys.to_vec(), cm)?;
    let mut w = Writer::new(
        b"\x53\x4c\x57\x32\x34\x2d\x72\x65\x63\x65\x69\x76\x65\x72\x2d\x63\x6d\x2d\x76\x31",
    );
    w.g2(cm);
    Ok((
        ReceiverCommitment {
            relation,
            witness: [h.usk, h.eid],
        },
        w.finish(),
    ))
}
pub fn delegator_begin<R: RngCore + CryptoRng>(
    prepared: &mut DelegationPrepared,
    cm_bytes: &[u8],
    rng: &mut R,
) -> Result<(DelegateAwaitFirst, Vec<u8>)> {
    let data = prepared
        .0
        .take()
        .ok_or_else(|| Error("delegation prepared already consumed".into()))?;
    let mut r = Reader::new(
        cm_bytes,
        b"\x53\x4c\x57\x32\x34\x2d\x72\x65\x63\x65\x69\x76\x65\x72\x2d\x63\x6d\x2d\x76\x31",
    )?;
    let cm = r.g2(false)?;
    r.finish()?;
    let relation = mv::Relation::g2_trusted(data.keys.to_vec(), cm)?;
    let (proof, msg) = mv::verifier_begin(&relation, rng)?;
    // The public statement includes cm, so carry it into the final signature.
    let mut data = data;
    data.sig.b = g2_add(data.sig.b, g2_mul(cm, data.cm_scale));
    Ok((DelegateAwaitFirst { data, proof }, msg.encode()))
}
pub fn receiver_first<R: RngCore + CryptoRng>(
    cm: ReceiverCommitment,
    v1: &[u8],
    rng: &mut R,
) -> Result<(ReceiverAwaitThird, Vec<u8>)> {
    let (proof, msg) =
        mv::prover_begin_decoded(&cm.relation, &cm.witness, &mv::VFirst::decode(v1)?, rng)?;
    Ok((ReceiverAwaitThird(proof), msg.encode()))
}
pub fn delegator_challenge<R: RngCore + CryptoRng>(
    state: DelegateAwaitFirst,
    p2: &[u8],
    rng: &mut R,
) -> Result<(DelegateAwaitFourth, Vec<u8>)> {
    let (proof, msg) = mv::verifier_challenge_decoded(state.proof, mv::PFirst::decode(p2)?, rng)?;
    Ok((
        DelegateAwaitFourth {
            data: state.data,
            proof,
        },
        msg.encode(),
    ))
}
pub fn receiver_respond(state: ReceiverAwaitThird, v3: &[u8]) -> Result<Vec<u8>> {
    Ok(mv::prover_respond(state.0, mv::VThird::decode(v3)?)?.encode())
}
/// Finish the native delegator proof and create the partial credential.
pub fn delegator_finish(state: DelegateAwaitFourth, p4: &[u8]) -> Result<Vec<u8>> {
    need(
        mv::verifier_finish(state.proof, mv::PFourth::decode(p4)?),
        "delegation knowledge proof",
    )?;
    let c = Credential {
        mode: Mode::Partial,
        keep: state.data.keep,
        attrs: state.data.attrs,
        sig: state.data.sig,
        uk: None,
    };
    Ok(c.encode())
}

#[derive(Clone)]
struct ShowPrefix {
    keep: Vec<usize>,
    disclosed: Vec<usize>,
    values: Vec<S>,
    sig: Signature,
}
impl ShowPrefix {
    #[cfg(test)]
    fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(
            b"\x53\x4c\x57\x32\x34\x2d\x73\x68\x6f\x77\x2d\x70\x72\x65\x66\x69\x78\x2d\x76\x31",
        );
        w.indices(&self.keep);
        w.indices(&self.disclosed);
        for &v in &self.values {
            w.fr(v);
        }
        w.g1(self.sig.p);
        w.g1(self.sig.q);
        w.g2(self.sig.a);
        w.g2(self.sig.b);
        w.finish()
    }
    fn encode_precomputed(&self, encoding: &ShowSignatureEncoding) -> Vec<u8> {
        let mut w = Writer::new(
            b"\x53\x4c\x57\x32\x34\x2d\x73\x68\x6f\x77\x2d\x70\x72\x65\x66\x69\x78\x2d\x76\x31",
        );
        w.indices(&self.keep);
        w.indices(&self.disclosed);
        for &v in &self.values {
            w.fr(v);
        }
        // Preserve the original canonical order. Original-mode P/Q depend on the
        // selected disclosure and remain online; partial-mode P/Q are fresh
        // policy-independent points from the consumed preparation.
        let mut bytes = w.finish();
        if let Some([p, q]) = &encoding.partial_pq {
            bytes.extend_from_slice(p);
            bytes.extend_from_slice(q);
        } else {
            bytes.extend_from_slice(&self.sig.p.to_compressed());
            bytes.extend_from_slice(&self.sig.q.to_compressed());
        }
        bytes.extend_from_slice(&encoding.a);
        bytes.extend_from_slice(&encoding.b);
        bytes
    }
    fn decode(pk: &PublicKey, bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(
            bytes,
            b"\x53\x4c\x57\x32\x34\x2d\x73\x68\x6f\x77\x2d\x70\x72\x65\x66\x69\x78\x2d\x76\x31",
        )?;
        let keep = r.indices(pk.business() + 2)?;
        let disclosed = r.indices(pk.business() + 2)?;
        need(
            valid_business(&keep, pk.business())
                && valid_business(&disclosed, pk.business())
                && disclosed.iter().all(|i| keep.contains(i)),
            "show indices",
        )?;
        let values = (0..disclosed.len())
            .map(|_| r.fr())
            .collect::<Result<Vec<_>>>()?;
        let p = r.g1(false)?;
        let q = r.g1(false)?;
        let a = r.g2(true)?;
        let b = r.g2(true)?;
        r.finish()?;
        Ok(Self {
            keep,
            disclosed,
            values,
            sig: Signature { p, q, a, b },
        })
    }
    fn hidden(&self) -> Vec<usize> {
        coordinates(&self.keep)
            .into_iter()
            .filter(|i| !self.disclosed.contains(i))
            .collect()
    }
    fn relation(&self, pk: &PublicKey) -> Result<mv::Relation> {
        self.relation_profile(pk, VerificationMode::Specification)
    }
    fn relation_profile(&self, pk: &PublicKey, profile: VerificationMode) -> Result<mv::Relation> {
        let target_public = g1_add(
            g1_add(pk.0.x, self.sig.p),
            sum1(
                &self
                    .disclosed
                    .iter()
                    .zip(&self.values)
                    .map(|(&i, &m)| (pk.0.y[i], m))
                    .collect::<Vec<_>>(),
            ),
        );
        let target = if profile == VerificationMode::Specification {
            gt_add(
                pair(G1::generator(), self.sig.b),
                -pair(target_public, self.sig.a),
            )
        } else {
            // This computes one required GT value. It is an exact two-term
            // product, not a randomized merger of distinct proof outputs.
            multi_pair(&[(G1::generator(), self.sig.b), (-target_public, self.sig.a)])
        };
        let bases = self.hidden().iter().map(|&i| pk.0.y[i]).collect();
        mv::Relation::pairing_g1_trusted(bases, self.sig.a, target)
    }
    fn purge_valid(&self, pk: &PublicKey) -> bool {
        pair(
            self.sig.p,
            add2(coordinates(&self.keep).iter().map(|&i| pk.0.yh[i])),
        ) == pair(self.sig.q, G2::generator())
    }
    fn purge_equation(&self, pk: &PublicKey) -> Equation {
        Equation {
            terms: vec![
                (
                    self.sig.p,
                    add2(coordinates(&self.keep).iter().map(|&i| pk.0.yh[i])),
                ),
                (-self.sig.q, G2::generator()),
            ],
            target: GT::identity(),
        }
    }
}
struct ShowData {
    relation: mv::Relation,
    witness: Vec<S>,
    cdm_prepared: Option<mv::PreparedProver>,
}
pub struct ShowPrepared(Option<ShowData>);
pub struct ShowHolderAwaitThird(mv::ProverAwaitThird);
pub struct ShowVerifierAwaitFirst(mv::VerifierAwaitFirst);
pub struct ShowVerifierAwaitFourth(mv::VerifierAwaitFourth);
pub struct ShowVerifierProfileAwaitFirst {
    proof: mv::VerifierAwaitFirst,
    profile: VerificationMode,
}
pub struct ShowVerifierProfileAwaitFourth {
    proof: mv::VerifierAwaitFourth,
    profile: VerificationMode,
}
struct ShowBase {
    origin: Mode,
    source: Credential,
    holder: Holder,
    sig: Signature,
    encoding: ShowSignatureEncoding,
    t: Option<S>,
}
/// Encodings of locally derived randomized points, held only by the private
/// one-use state. No received-point decoding or verifier check uses this cache.
struct ShowSignatureEncoding {
    partial_pq: Option<[[u8; 48]; 2]>,
    a: [u8; 96],
    b: [u8; 96],
}
impl ShowSignatureEncoding {
    fn precompute(sig: &Signature, mode: Mode) -> Self {
        Self {
            partial_pq: (mode == Mode::Partial)
                .then(|| [sig.p.to_compressed(), sig.q.to_compressed()]),
            a: sig.a.to_compressed(),
            b: sig.b.to_compressed(),
        }
    }
}
pub struct ShowPrecomputed(Option<ShowBase>);
/// Randomize the credential before a disclosure policy is selected. Source
/// full-field masks are retained; an identity signature follows the abort path.
/// Prepare fresh one-use native presentation material before the live verifier exchange.
pub fn show_precompute<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    c: &Credential,
    rng: &mut R,
) -> Result<ShowPrecomputed> {
    let (sig, t) = if c.mode == Mode::Original {
        let s = random_scalar(rng);
        let t = random_scalar(rng);
        let a = g2_mul(c.sig.a, s);
        let b = sum2(&[(c.sig.b, s), (a, t)]);
        (
            Signature {
                p: G1::identity(),
                q: G1::identity(),
                a,
                b,
            },
            Some(t),
        )
    } else {
        let alpha = random_scalar(rng);
        let beta = random_scalar(rng);
        let a = g2_mul(c.sig.a, alpha);
        let p = g1_add(c.sig.p, g1_mul(G1::generator(), beta));
        let q = g1_add(
            c.sig.q,
            g1_mul(add1(coordinates(&c.keep).iter().map(|&i| pk.0.y[i])), beta),
        );
        let b = sum2(&[(c.sig.b, alpha), (a, beta)]);
        (Signature { p, q, a, b }, None)
    };
    need(
        sig.a != G2::identity() && sig.b != G2::identity(),
        "source show abort at signature domain",
    )?;
    let encoding = ShowSignatureEncoding::precompute(&sig, c.mode);
    Ok(ShowPrecomputed(Some(ShowBase {
        origin: c.mode,
        source: c.clone(),
        holder: h.clone(),
        sig,
        encoding,
        t,
    })))
}
/// Bind native prepared presentation material to the chosen disclosure.
pub fn show_bind(
    pk: &PublicKey,
    precomputed: &mut ShowPrecomputed,
    disclosed: &[usize],
) -> Result<(ShowPrepared, Vec<u8>)> {
    show_bind_profile(pk, precomputed, disclosed, VerificationMode::Specification)
}

/// Use the same native disclosure binding with an exact multi-pairing target
/// computation for the engineering profile.
pub fn show_bind_profile(
    pk: &PublicKey,
    precomputed: &mut ShowPrecomputed,
    disclosed: &[usize],
    profile: VerificationMode,
) -> Result<(ShowPrepared, Vec<u8>)> {
    let mut base = precomputed
        .0
        .take()
        .ok_or_else(|| Error("show precomputation already consumed".into()))?;
    need(
        valid_business(disclosed, pk.business())
            && disclosed.iter().all(|i| base.source.keep.contains(i)),
        "disclosure indices",
    )?;
    let keep = if base.origin == Mode::Original {
        let (p, q) = purge_parts(pk, &base.source, disclosed, base.t.unwrap());
        base.sig.p = p;
        base.sig.q = q;
        disclosed.to_vec()
    } else {
        base.source.keep.clone()
    };
    let values = disclosed
        .iter()
        .map(|i| base.source.attrs[base.source.keep.iter().position(|j| j == i).unwrap()])
        .collect();
    let prefix = ShowPrefix {
        keep,
        disclosed: disclosed.to_vec(),
        values,
        sig: base.sig,
    };
    let witness = prefix
        .hidden()
        .iter()
        .map(|&i| match i {
            0 => base.holder.usk,
            1 => base.holder.eid,
            _ => base.source.attrs[base.source.keep.iter().position(|&j| j == i).unwrap()],
        })
        .collect();
    let relation = prefix.relation_profile(pk, profile)?;
    let bytes = prefix.encode_precomputed(&base.encoding);
    Ok((
        ShowPrepared(Some(ShowData {
            relation,
            witness,
            cdm_prepared: None,
        })),
        bytes,
    ))
}
/// Precompute the fixed CDM branches after the disclosure relation is known.
/// Fresh verifier-commitment binding and verifier-opening checks remain online.
pub fn show_precompute_first<R: RngCore + CryptoRng>(
    prepared: &mut ShowPrepared,
    rng: &mut R,
) -> Result<()> {
    let data = prepared
        .0
        .as_mut()
        .ok_or_else(|| Error("show prepared already consumed".into()))?;
    need(data.cdm_prepared.is_none(), "CDM first already prepared")?;
    data.cdm_prepared = Some(mv::prover_prepare(&data.relation, &data.witness, rng)?);
    Ok(())
}
/// Prepare the native presentation when disclosure is known before the request.
pub fn show_prepare<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    c: &Credential,
    disclosed: &[usize],
    rng: &mut R,
) -> Result<(ShowPrepared, Vec<u8>)> {
    show_prepare_profile(pk, h, c, disclosed, VerificationMode::Specification, rng)
}
pub fn show_prepare_profile<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    c: &Credential,
    disclosed: &[usize],
    profile: VerificationMode,
    rng: &mut R,
) -> Result<(ShowPrepared, Vec<u8>)> {
    let mut offline = show_precompute(pk, h, c, rng)?;
    let (mut prepared, prefix) = show_bind_profile(pk, &mut offline, disclosed, profile)?;
    show_precompute_first(&mut prepared, rng)?;
    Ok((prepared, prefix))
}
pub fn show_verifier_begin<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    prefix_bytes: &[u8],
    rng: &mut R,
) -> Result<(ShowVerifierAwaitFirst, Vec<u8>)> {
    let prefix = ShowPrefix::decode(pk, prefix_bytes)?;
    need(prefix.purge_valid(pk), "purge signature equation")?;
    let (proof, msg) = mv::verifier_begin(&prefix.relation(pk)?, rng)?;
    Ok((ShowVerifierAwaitFirst(proof), msg.encode()))
}
/// Begin verification with caller-supplied expected native disclosure values.
pub fn show_verifier_begin_expected<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    prefix_bytes: &[u8],
    expected_disclosed: &[usize],
    expected_values: &[S],
    rng: &mut R,
) -> Result<(ShowVerifierAwaitFirst, Vec<u8>)> {
    let prefix = ShowPrefix::decode(pk, prefix_bytes)?;
    need(
        prefix.disclosed == expected_disclosed && prefix.values == expected_values,
        "disclosure contract",
    )?;
    need(prefix.purge_valid(pk), "purge signature equation")?;
    let (proof, msg) = mv::verifier_begin(&prefix.relation(pk)?, rng)?;
    Ok((ShowVerifierAwaitFirst(proof), msg.encode()))
}
pub fn show_holder_first<R: RngCore + CryptoRng>(
    _pk: &PublicKey,
    prepared: &mut ShowPrepared,
    v1: &[u8],
    rng: &mut R,
) -> Result<(ShowHolderAwaitThird, Vec<u8>)> {
    let data = prepared
        .0
        .take()
        .ok_or_else(|| Error("show prepared already consumed".into()))?;
    let first = mv::VFirst::decode(v1)?;
    let (proof, msg) = if let Some(p) = data.cdm_prepared {
        mv::prover_bind_decoded(p, &first)?
    } else {
        // Reference/late-policy path retaining the original preparation split.
        mv::prover_begin_decoded(&data.relation, &data.witness, &first, rng)?
    };
    Ok((ShowHolderAwaitThird(proof), msg.encode()))
}
pub fn show_verifier_challenge<R: RngCore + CryptoRng>(
    state: ShowVerifierAwaitFirst,
    p2: &[u8],
    rng: &mut R,
) -> Result<(ShowVerifierAwaitFourth, Vec<u8>)> {
    let (proof, msg) = mv::verifier_challenge_decoded(state.0, mv::PFirst::decode(p2)?, rng)?;
    Ok((ShowVerifierAwaitFourth(proof), msg.encode()))
}
pub fn show_holder_respond(state: ShowHolderAwaitThird, v3: &[u8]) -> Result<Vec<u8>> {
    Ok(mv::prover_respond(state.0, mv::VThird::decode(v3)?)?.encode())
}
/// Verify the complete native live presentation transcript.
pub fn show_verifier_finish(state: ShowVerifierAwaitFourth, p4: &[u8]) -> Result<bool> {
    Ok(mv::verifier_finish(state.0, mv::PFourth::decode(p4)?))
}

/// Sealed input-only parsing results. Their creation performs canonical group,
/// subgroup, native identity and exact disclosure/dimension checks, no algebra.
pub struct ReceivedShowPrefix(ShowPrefix);
pub struct ReceivedShowFirst(mv::PFirst);
pub struct ReceivedShowFinal(mv::PFourth);

impl ReceivedShowPrefix {
    pub fn received_field_counts(&self) -> (usize, usize, usize, usize) {
        (2, 2, 0, self.0.values.len())
    }
}
impl ReceivedShowFirst {
    pub fn received_field_counts(&self) -> (usize, usize, usize, usize) {
        let points = [self.0.true_first, self.0.opening_or_first];
        let g2 = points
            .iter()
            .filter(|p| matches!(p, mv::Point::G2(_)))
            .count();
        (0, g2, 2 - g2, 1)
    }
}
impl ReceivedShowFinal {
    pub fn received_field_counts(&self) -> (usize, usize, usize, usize) {
        (
            0,
            0,
            0,
            1 + self.0.true_responses.len() + self.0.opening_responses.len(),
        )
    }
}
pub fn decode_show_prefix_received(
    pk: &PublicKey,
    bytes: &[u8],
    disclosed: &[usize],
    values: &[S],
) -> Result<ReceivedShowPrefix> {
    let prefix = ShowPrefix::decode(pk, bytes)?;
    need(
        prefix.disclosed == disclosed && prefix.values == values,
        "disclosure contract",
    )?;
    Ok(ReceivedShowPrefix(prefix))
}
pub fn decode_show_first_received(
    state: &ShowVerifierProfileAwaitFirst,
    bytes: &[u8],
) -> Result<ReceivedShowFirst> {
    Ok(ReceivedShowFirst(mv::decode_prover_first(
        &state.proof,
        bytes,
    )?))
}
pub fn decode_show_final_received(
    state: &ShowVerifierProfileAwaitFourth,
    bytes: &[u8],
) -> Result<ReceivedShowFinal> {
    Ok(ReceivedShowFinal(mv::decode_prover_fourth(
        &state.proof,
        bytes,
    )?))
}
/// Start the same native interaction with a phase-aware verification profile.
/// Purge acceptance remains before the first verifier message; it is not
/// deferred until a later proof stage to manufacture one total FE.
pub fn show_verifier_begin_profile<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    prefix_bytes: &[u8],
    expected_disclosed: &[usize],
    expected_values: &[S],
    profile: VerificationMode,
    rng: &mut R,
) -> Result<(ShowVerifierProfileAwaitFirst, Vec<u8>)> {
    let received =
        decode_show_prefix_received(pk, prefix_bytes, expected_disclosed, expected_values)?;
    show_verifier_begin_received_profile(pk, received, profile, rng)
}
pub fn show_verifier_begin_received_profile<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    received: ReceivedShowPrefix,
    profile: VerificationMode,
    rng: &mut R,
) -> Result<(ShowVerifierProfileAwaitFirst, Vec<u8>)> {
    let prefix = received.0;
    let purge_ok = if profile == VerificationMode::Specification {
        prefix.purge_valid(pk)
    } else {
        pairing_verify::verify_checked(&[prefix.purge_equation(pk)], profile, rng)
    };
    need(purge_ok, "purge signature equation")?;
    let (proof, msg) = mv::verifier_begin(&prefix.relation_profile(pk, profile)?, rng)?;
    Ok((
        ShowVerifierProfileAwaitFirst { proof, profile },
        msg.encode(),
    ))
}

/// The same live verifier stage with independent random tapes for aggregation
/// weights and the native opening/challenge messages. Both tapes have the same
/// native distributions; the received statement is fixed before either draw.
/// No prover state is copied or replayed by this continuation.
pub fn show_verifier_begin_received_profile_rngs<R: RngCore + CryptoRng, W: RngCore + CryptoRng>(
    pk: &PublicKey,
    received: ReceivedShowPrefix,
    profile: VerificationMode,
    weights: &mut W,
    live: &mut R,
) -> Result<(ShowVerifierProfileAwaitFirst, Vec<u8>)> {
    let prefix = received.0;
    let purge_ok = if profile == VerificationMode::Specification {
        prefix.purge_valid(pk)
    } else {
        pairing_verify::verify_checked(&[prefix.purge_equation(pk)], profile, weights)
    };
    need(purge_ok, "purge signature equation")?;
    let (proof, msg) = mv::verifier_begin(&prefix.relation_profile(pk, profile)?, live)?;
    Ok((
        ShowVerifierProfileAwaitFirst { proof, profile },
        msg.encode(),
    ))
}

/// One received round: verify all purge PPEs in one SET, then produce the
/// independent native live commitments. Per-proof relation target computation
/// remains individual; it is not an additional verification equation.
pub fn show_verifier_begin_many_received_profile_rngs<
    R: RngCore + CryptoRng,
    W: RngCore + CryptoRng,
>(
    pk: &PublicKey,
    prefixes: Vec<ReceivedShowPrefix>,
    profile: VerificationMode,
    weights: &mut W,
    live: &mut R,
) -> Result<Vec<(ShowVerifierProfileAwaitFirst, Vec<u8>)>> {
    need(!prefixes.is_empty(), "empty native presentation round")?;
    let valid = if profile == VerificationMode::Specification {
        prefixes.iter().all(|p| p.0.purge_valid(pk))
    } else {
        let equations = prefixes
            .iter()
            .map(|p| p.0.purge_equation(pk))
            .collect::<Vec<_>>();
        pairing_verify::verify_checked(&equations, profile, weights)
    };
    need(valid, "purge signature equations")?;
    prefixes
        .into_iter()
        .map(|p| {
            let (proof, msg) = mv::verifier_begin(&p.0.relation_profile(pk, profile)?, live)?;
            Ok((
                ShowVerifierProfileAwaitFirst { proof, profile },
                msg.encode(),
            ))
        })
        .collect()
}

pub fn show_verifier_challenge_profile<R: RngCore + CryptoRng>(
    state: ShowVerifierProfileAwaitFirst,
    p2: &[u8],
    rng: &mut R,
) -> Result<(ShowVerifierProfileAwaitFourth, Vec<u8>)> {
    let received = decode_show_first_received(&state, p2)?;
    show_verifier_challenge_received_profile(state, received, rng)
}
pub fn show_verifier_challenge_received_profile<R: RngCore + CryptoRng>(
    state: ShowVerifierProfileAwaitFirst,
    received: ReceivedShowFirst,
    rng: &mut R,
) -> Result<(ShowVerifierProfileAwaitFourth, Vec<u8>)> {
    let (proof, msg) = mv::verifier_challenge_decoded(state.proof, received.0, rng)?;
    Ok((
        ShowVerifierProfileAwaitFourth {
            proof,
            profile: state.profile,
        },
        msg.encode(),
    ))
}

pub fn show_verifier_finish_profile(
    state: ShowVerifierProfileAwaitFourth,
    p4: &[u8],
    rng: &mut impl RngCore,
) -> Result<bool> {
    Ok(mv::verifier_finish_profile(
        state.proof,
        mv::PFourth::decode(p4)?,
        state.profile,
        rng,
    ))
}

/// Final checks of completed native interactions. Every response is strictly
/// decoded before the first aggregation weight is drawn.
pub fn show_verifier_finish_many_profile(
    sessions: Vec<(ShowVerifierProfileAwaitFourth, Vec<u8>)>,
    profile: VerificationMode,
    rng: &mut impl RngCore,
) -> Result<bool> {
    if sessions.iter().any(|(state, _)| state.profile != profile) {
        return fail("mixed verification profiles");
    }
    let sessions = sessions
        .into_iter()
        .map(|(state, bytes)| {
            let decoded = decode_show_final_received(&state, &bytes)?;
            Ok((state, decoded))
        })
        .collect::<Result<Vec<_>>>()?;
    show_verifier_finish_many_received_profile(sessions, profile, rng)
}
pub fn show_verifier_finish_many_received_profile(
    sessions: Vec<(ShowVerifierProfileAwaitFourth, ReceivedShowFinal)>,
    profile: VerificationMode,
    rng: &mut impl RngCore,
) -> Result<bool> {
    if sessions.iter().any(|(state, _)| state.profile != profile) {
        return fail("mixed verification profiles");
    }
    Ok(mv::verifier_finish_many_checked(
        sessions
            .into_iter()
            .map(|(state, message)| (state.proof, message.0))
            .collect(),
        profile,
        rng,
    ))
}

/// Completed live-session material with a sealed verifier challenge. It has no
/// prover nonce or verifier opening secret. These fixed-record checks support
/// batch fallback; live verifier generation costs remain separate stages.
#[derive(Clone)]
pub struct FrozenShow {
    key: PublicKey,
    issuer_id: [u8; 32],
    prefix: ShowPrefix,
    verifier: mv::FrozenVerifier,
    messages: [Vec<u8>; 5],
}
impl FrozenShow {
    pub fn issuer_id(&self) -> [u8; 32] {
        self.issuer_id
    }
    pub fn messages(&self) -> &[Vec<u8>; 5] {
        &self.messages
    }
    pub fn bytes(&self) -> usize {
        self.messages.iter().map(Vec::len).sum()
    }
    /// Framed transcript binding for application state/cache keys. This is
    /// not an extra protocol message and is not included in bytes().
    pub fn application_binding_bytes(&self) -> Vec<u8> {
        let mut w = Writer::new(b"SLW-frozen-live-session-v1");
        w.bytes(&self.issuer_id);
        for message in &self.messages {
            w.bytes(message);
        }
        w.finish()
    }
    /// Model receiving a replacement final message for the same original
    /// verifier session; all earlier statements/challenges stay immutable.
    pub fn with_final_message(&self, bytes: &[u8]) -> Self {
        let mut out = self.clone();
        out.messages[4] = bytes.to_vec();
        out
    }
    pub fn verify(&self, profile: VerificationMode, rng: &mut impl RngCore) -> Result<bool> {
        verify_frozen_batch(std::slice::from_ref(self), profile, rng)
    }
}

/// Recheck all purge and CDM final equations for fixed completed sessions.
/// This is not a replacement for timing the three live verifier phases.
pub fn verify_frozen_batch(
    sessions: &[FrozenShow],
    profile: VerificationMode,
    rng: &mut impl RngCore,
) -> Result<bool> {
    if sessions.is_empty() {
        return Ok(false);
    }
    let lasts = sessions
        .iter()
        .map(|s| mv::PFourth::decode(&s.messages[4]))
        .collect::<Result<Vec<_>>>()?;
    if profile == VerificationMode::Specification {
        return Ok(sessions.iter().zip(lasts).all(|(s, last)| {
            s.prefix.purge_valid(&s.key) && s.verifier.verify(last, profile, rng)
        }));
    }
    let mut equations = Vec::new();
    for (session, last) in sessions.iter().zip(lasts) {
        equations.push(session.prefix.purge_equation(&session.key));
        let Some(proof) = session.verifier.equations(&last) else {
            return Ok(false);
        };
        equations.extend(proof);
    }
    Ok(pairing_verify::verify_checked(&equations, profile, rng))
}

/// Execute all native messages and retain the completed verifier statement.
/// The proof's generation and the honest holder's opening check are identical
/// to the four-message source interaction.
pub fn run_show_frozen<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    c: &Credential,
    disclosed: &[usize],
    profile: VerificationMode,
    rng: &mut R,
) -> Result<FrozenShow> {
    let values = disclosed
        .iter()
        .map(|i| {
            c.keep
                .iter()
                .position(|j| j == i)
                .map(|j| c.attrs[j])
                .ok_or_else(|| Error("disclosure indices".into()))
        })
        .collect::<Result<Vec<_>>>()?;
    let (mut prep, prefix_bytes) = show_prepare_profile(pk, h, c, disclosed, profile, rng)?;
    let prefix = ShowPrefix::decode(pk, &prefix_bytes)?;
    let (vs, v1) =
        show_verifier_begin_profile(pk, &prefix_bytes, disclosed, &values, profile, rng)?;
    let (ps, p2) = show_holder_first(pk, &mut prep, &v1, rng)?;
    let (vs, v3) = show_verifier_challenge_profile(vs, &p2, rng)?;
    let p4 = show_holder_respond(ps, &v3)?;
    let verifier = mv::FrozenVerifier::from_live(vs.proof);
    need(
        verifier.verify(mv::PFourth::decode(&p4)?, profile, rng),
        "show proof",
    )?;
    Ok(FrozenShow {
        key: pk.clone(),
        issuer_id: pk.issuer_id(),
        prefix,
        verifier,
        messages: [prefix_bytes, v1, p2, v3, p4],
    })
}

#[derive(Clone, Debug)]
pub struct Interaction {
    pub messages: Vec<Vec<u8>>,
    pub senders: Vec<&'static str>,
}
impl Interaction {
    pub fn bytes(&self) -> usize {
        self.messages.iter().map(Vec::len).sum()
    }
    pub fn message_sizes(&self) -> Vec<usize> {
        self.messages.iter().map(Vec::len).collect()
    }
}
/// Run every party and message of the native issuance exchange.
pub fn run_issue<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    sk: &IssuerSecret,
    h: &Holder,
    attrs: &[S],
    rng: &mut R,
) -> Result<(Credential, Interaction)> {
    let (mut prepared, req) = issue_prepare(pk, h, attrs)?;
    let (vs, v1) = issuer_begin(pk, &req, rng)?;
    let (ps, p2) = holder_issue_first_prepared(&mut prepared, &v1, rng)?;
    let (vs, v3) = issuer_issue_challenge(vs, &p2, rng)?;
    let p4 = holder_issue_respond(ps, &v3)?;
    let cred = issuer_issue_finish(pk, sk, vs, &p4, rng)?;
    let received = receive_expected(pk, h, &cred, &all_business(pk.business()), attrs)?;
    Ok((
        received,
        Interaction {
            messages: vec![req, v1, p2, v3, p4, cred],
            senders: vec!["holder", "issuer", "holder", "issuer", "holder", "issuer"],
        },
    ))
}
/// Full issuance with the native G2 CDM exchange and the selected acceptance
/// profile. The interactive proof has no pairing residual to merge here.
pub fn run_issue_profile<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    sk: &IssuerSecret,
    h: &Holder,
    attrs: &[S],
    profile: VerificationMode,
    rng: &mut R,
) -> Result<(Credential, Interaction)> {
    let (mut prepared, req) = issue_prepare(pk, h, attrs)?;
    let (vs, v1) = issuer_begin(pk, &req, rng)?;
    let (ps, p2) = holder_issue_first_prepared(&mut prepared, &v1, rng)?;
    let (vs, v3) = issuer_issue_challenge(vs, &p2, rng)?;
    let p4 = holder_issue_respond(ps, &v3)?;
    let cred = issuer_issue_finish(pk, sk, vs, &p4, rng)?;
    let received = receive_expected_profile(
        pk,
        h,
        &cred,
        &all_business(pk.business()),
        attrs,
        profile,
        rng,
    )?;
    Ok((
        received,
        Interaction {
            messages: vec![req, v1, p2, v3, p4, cred],
            senders: vec!["holder", "issuer", "holder", "issuer", "holder", "issuer"],
        },
    ))
}
/// Run every party and message of the native partial-credential delegation.
pub fn run_delegate<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    old: &Holder,
    new: &Holder,
    c: &Credential,
    keep: &[usize],
    rng: &mut R,
) -> Result<(Credential, Interaction)> {
    let (mut prep, prefix) = delegate_prepare(pk, old, c, keep, rng)?;
    let (cmstate, cm) = receiver_cm(pk, new, &prefix)?;
    let (vs, v1) = delegator_begin(&mut prep, &cm, rng)?;
    let (ps, p2) = receiver_first(cmstate, &v1, rng)?;
    let (vs, v3) = delegator_challenge(vs, &p2, rng)?;
    let p4 = receiver_respond(ps, &v3)?;
    let cred = delegator_finish(vs, &p4)?;
    let attrs: Vec<_> = keep
        .iter()
        .map(|i| c.attrs[c.keep.iter().position(|j| j == i).unwrap()])
        .collect();
    let received = receive_expected(pk, new, &cred, keep, &attrs)?;
    Ok((
        received,
        Interaction {
            messages: vec![prefix, cm, v1, p2, v3, p4, cred],
            senders: vec![
                "delegator",
                "receiver",
                "delegator",
                "receiver",
                "delegator",
                "receiver",
                "delegator",
            ],
        },
    ))
}
/// Full native delegation; all G2 CDM checks stay exact and the receiver's
/// signature plus purge checks use the selected aggregation profile.
pub fn run_delegate_profile<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    old: &Holder,
    new: &Holder,
    c: &Credential,
    keep: &[usize],
    profile: VerificationMode,
    rng: &mut R,
) -> Result<(Credential, Interaction)> {
    let (mut prep, prefix) = delegate_prepare(pk, old, c, keep, rng)?;
    let (cmstate, cm) = receiver_cm(pk, new, &prefix)?;
    let (vs, v1) = delegator_begin(&mut prep, &cm, rng)?;
    let (ps, p2) = receiver_first(cmstate, &v1, rng)?;
    let (vs, v3) = delegator_challenge(vs, &p2, rng)?;
    let p4 = receiver_respond(ps, &v3)?;
    let cred = delegator_finish(vs, &p4)?;
    let attrs = keep
        .iter()
        .map(|i| c.attrs[c.keep.iter().position(|j| j == i).unwrap()])
        .collect::<Vec<_>>();
    let received = receive_expected_profile(pk, new, &cred, keep, &attrs, profile, rng)?;
    Ok((
        received,
        Interaction {
            messages: vec![prefix, cm, v1, p2, v3, p4, cred],
            senders: vec![
                "delegator",
                "receiver",
                "delegator",
                "receiver",
                "delegator",
                "receiver",
                "delegator",
            ],
        },
    ))
}
/// Run every party and message of the native interactive presentation exchange.
pub fn run_show<R: RngCore + CryptoRng>(
    pk: &PublicKey,
    h: &Holder,
    c: &Credential,
    disclosed: &[usize],
    rng: &mut R,
) -> Result<Interaction> {
    let (mut prep, prefix) = show_prepare(pk, h, c, disclosed, rng)?;
    let (vs, v1) = show_verifier_begin(pk, &prefix, rng)?;
    let (ps, p2) = show_holder_first(pk, &mut prep, &v1, rng)?;
    let (vs, v3) = show_verifier_challenge(vs, &p2, rng)?;
    let p4 = show_holder_respond(ps, &v3)?;
    need(show_verifier_finish(vs, &p4)?, "show proof")?;
    Ok(Interaction {
        messages: vec![prefix, v1, p2, v3, p4],
        senders: vec!["holder", "verifier", "holder", "verifier", "holder"],
    })
}

#[cfg(test)]
mod domain_contract {
    use super::*;
    #[test]
    fn cached_show_prefix_keeps_policy_dependent_original_points_online() {
        let sig = Signature {
            p: G1::generator() * S::from(3),
            q: G1::generator() * S::from(5),
            a: G2::generator() * S::from(7),
            b: G2::generator() * S::from(11),
        };
        for mode in [Mode::Original, Mode::Partial] {
            let encoding = ShowSignatureEncoding::precompute(&sig, mode);
            let mut prefix = ShowPrefix {
                keep: vec![2, 3, 4],
                disclosed: vec![2, 3],
                values: vec![S::from(100), S::from(101)],
                sig,
            };
            if mode == Mode::Original {
                assert!(encoding.partial_pq.is_none());
                // The disclosure bind replaces original P/Q after the cache
                // was formed, and those new points must be encoded online.
                prefix.sig.p += G1::generator();
                prefix.sig.q += G1::generator() * S::from(2);
            } else {
                assert!(encoding.partial_pq.is_some());
            }
            assert_eq!(prefix.encode(), prefix.encode_precomputed(&encoding));
        }
    }

    #[test]
    // Retain the original owned test witness or transcript fixture.
    #[allow(clippy::useless_vec)]
    fn legal_identity_b_is_accepted_only_with_valid_signature_equations() {
        let ys = vec![S::from(3), S::from(5), S::from(7)];
        let x = S::from(11);
        let raw = PublicKeyData {
            x: G1::generator() * x,
            y: ys.iter().map(|&y| G1::generator() * y).collect(),
            yh: ys.iter().map(|&y| G2::generator() * y).collect(),
            z: ys
                .iter()
                .enumerate()
                .map(|(i, &v)| {
                    ys.iter()
                        .enumerate()
                        .map(|(j, &u)| {
                            if i == j {
                                G1::identity()
                            } else {
                                G1::generator() * (v * u)
                            }
                        })
                        .collect()
                })
                .collect(),
        };
        let pk = PublicKey::install(raw).unwrap();
        let h = Holder::from_secrets(S::from(13), S::ZERO).unwrap();
        let m = -(x + ys[0] * h.usk) * inv(ys[2]);
        let a = G2::generator();
        let c = Credential {
            mode: Mode::Original,
            keep: vec![2],
            attrs: vec![m],
            sig: Signature {
                p: G1::identity(),
                q: G1::identity(),
                a,
                b: G2::identity(),
            },
            uk: Some([a * ys[0], a * ys[1]]),
        };
        assert!(receive(&pk, &h, &c.encode()).is_ok());
        let wrong = Holder::from_secrets(S::from(14), S::ZERO).unwrap();
        assert!(receive(&pk, &wrong, &c.encode()).is_err());
    }
}
