//! Mir et al., PoPETs 2023, Fig. 2 and Appendix B.
//! The single terminal delegation uses the authors' explicit ChangeRel(mu).
//! A root keeps mu privately; a terminal credential has no update key.
use super::{pok, set_commit as sc, wire};
use crate::arithmetic::*;
use crate::pairing_verify::{self, Equation, Mode as VerificationMode};
use ff::Field;
use group::Group;
use rand::RngCore;

pub const PROFILE: &str = "\x53\x50\x53\x45\x51\x2d\x55\x43\x2d\x70\x72\x6f\x66\x69\x6c\x65\x2d\x32\x2d\x72\x6f\x6f\x74\x39\x2d\x70\x65\x72\x69\x6f\x64\x31\x2d\x74\x65\x72\x6d\x69\x6e\x61\x6c";
pub type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
pub struct Signature {
    pub z: G1,
    pub y: G1,
    pub yhat: G2,
    pub t: G1,
}
#[derive(Clone, Debug)]
pub struct RegistrationProof {
    pub a1: Vec<G1>,
    pub a2: Vec<G2>,
    pub z: Vec<S>,
}
#[derive(Clone, Debug)]
pub struct PublicParameters {
    pub sc: sc::Params,
    pub x0: G1,
    /// x0, x1, and the three commitment-position keys x2,x3,x4.
    pub xs: Vec<G2>,
    pub registration: RegistrationProof,
}
pub struct Issuer {
    alpha: S,
    x: [S; 5],
    system_id: Vec<u8>,
}
/// Public objects are privately owned; only immutable borrows are exported.
/// ```compile_fail
/// use baseline_core::msb23::scheme::Registered;
/// let forged = Registered {};
/// ```
/// ```compile_fail
/// use baseline_core::msb23::scheme::Registered;
/// fn mutate(h: &Registered) { h.parameters().xs.clear(); }
/// ```
#[derive(Clone)]
pub struct Registered {
    pub(crate) pp: PublicParameters,
    pub(crate) id: Vec<u8>,
    // Retain the exact shared native guard or state layout; current checked paths may not call every fallback.
    #[allow(dead_code)]
    pub(crate) h: G1,
    dummy_value: G1,
    uk_fixed: Vec<GT>,
    proof_base: std::sync::Arc<pok::InstalledBase>,
}
impl Registered {
    pub fn parameters(&self) -> &PublicParameters {
        &self.pp
    }
    pub fn id(&self) -> &[u8] {
        &self.id
    }
    /// Checks an externally replaced object without mutating this capability.
    pub fn matches_parameters(&self, pp: &PublicParameters) -> bool {
        // Actual field/point equality is required: unchecked in-memory
        // off-curve points can alias a checked point's compressed encoding.
        pp.sc.max_cardinality == self.pp.sc.max_cardinality
            && pp.sc.srs1 == self.pp.sc.srs1
            && pp.sc.srs2 == self.pp.sc.srs2
            && pp.x0 == self.pp.x0
            && pp.xs == self.pp.xs
            && pp.registration.a1 == self.pp.registration.a1
            && pp.registration.a2 == self.pp.registration.a2
            && pp.registration.z == self.pp.registration.z
    }
}

fn registration_challenge(pp: &PublicParameters, a1: &[G1], a2: &[G2]) -> S {
    let mut b = wire::parameters_statement(pp);
    for a in a1 {
        b.extend(enc1(*a));
    }
    for a in a2 {
        b.extend(enc2(*a));
    }
    hash_scalar(b"\x53\x50\x53\x45\x51\x5f\x55\x43\x5f\x52\x45\x47\x49\x53\x54\x52\x41\x54\x49\x4f\x4e\x5f\x56\x32", &b)
}

/// Parameter/key creation; setup is measured separately, never hidden in Issue.
#[allow(clippy::manual_range_contains)]
/// Create in-memory public parameters for this native scheme.
pub fn setup(t: usize, rng: &mut impl RngCore) -> Result<(PublicParameters, Issuer)> {
    if t < 3 || t > 4096 {
        return Err("supported cardinality is 3..=4096".into());
    }
    let (sc, alpha) = sc::setup(t, rng);
    let x = std::array::from_fn(|_| random_nonzero(rng));
    let xs = x.iter().map(|v| g2_mul(G2::generator(), *v)).collect();
    let mut pp = PublicParameters {
        sc,
        x0: g1_mul(G1::generator(), x[0]),
        xs,
        registration: RegistrationProof {
            a1: vec![],
            a2: vec![],
            z: vec![],
        },
    };
    let w: Vec<S> = (0..6).map(|_| random_nonzero(rng)).collect();
    let a1 = vec![g1_mul(G1::generator(), w[0]), g1_mul(G1::generator(), w[5])];
    let a2 = w
        .iter()
        .map(|v| g2_mul(G2::generator(), *v))
        .collect::<Vec<_>>();
    let c = registration_challenge(&pp, &a1, &a2);
    let z = w
        .iter()
        .enumerate()
        .map(|(i, v)| *v + c * if i < 5 { x[i] } else { alpha })
        .collect();
    pp.registration = RegistrationProof { a1, a2, z };
    let system_id = digest(&wire::encode_parameters(&pp));
    Ok((
        pp,
        Issuer {
            alpha,
            x,
            system_id,
        },
    ))
}

/// Offline registration verifies each secret-key relation and every SRS power.
pub struct CheckedParameters {
    pp: PublicParameters,
    id: Vec<u8>,
    h: G1,
}

/// Validate received public parameters before native registration.
pub fn register_checked(pp: PublicParameters) -> Result<CheckedParameters> {
    register_body(pp, false)
}
pub(crate) fn register_decoded(pp: PublicParameters) -> Result<CheckedParameters> {
    register_body(pp, true)
}
fn register_body(pp: PublicParameters, decoded: bool) -> Result<CheckedParameters> {
    if !(3..=4096).contains(&pp.sc.max_cardinality)
        || pp.xs.len() != 5
        || (if decoded {
            pp.x0 == G1::identity()
        } else {
            !valid1(pp.x0, true)
        })
        || pp.xs.iter().any(|v| {
            if decoded {
                *v == G2::identity()
            } else {
                !valid2(*v, true)
            }
        })
        || !(if decoded {
            sc::validate_params_decoded(&pp.sc)
        } else {
            sc::validate_params(&pp.sc)
        })
    {
        return Err("invalid public parameters".into());
    }
    let p = &pp.registration;
    if p.a1.len() != 2
        || p.a2.len() != 6
        || p.z.len() != 6
        || p.a1.iter().any(|v| {
            if decoded {
                *v == G1::identity()
            } else {
                !valid1(*v, true)
            }
        })
        || p.a2.iter().any(|v| {
            if decoded {
                *v == G2::identity()
            } else {
                !valid2(*v, true)
            }
        })
    {
        return Err("malformed registration proof".into());
    }
    let c = registration_challenge(&pp, &p.a1, &p.a2);
    for i in 0..6 {
        let target = if i < 5 { pp.xs[i] } else { pp.sc.srs2[1] };
        if g2_mul(G2::generator(), p.z[i]) != g2_add(p.a2[i], g2_mul(target, c)) {
            return Err("registration G2 knowledge proof rejected".into());
        }
    }
    for (j, i, target) in [(0, 0, pp.x0), (1, 5, pp.sc.srs1[1])] {
        if g1_mul(G1::generator(), p.z[i]) != g1_add(p.a1[j], g1_mul(target, c)) {
            return Err("registration shared-witness G1 proof rejected".into());
        }
    }
    let id = digest(&wire::encode_parameters(&pp));
    let h = pok::commitment_base(&id);
    Ok(CheckedParameters { pp, id, h })
}

/// Local cache installation after all registration checks. Never trusts a
/// transmitted GT cache. Count this once separately, not as free hot-path work.
pub fn install_cache(c: CheckedParameters) -> Result<Registered> {
    let dummy_value =
        sc::evaluate_g1(&c.pp.sc, &sc::polynomial_coefficients(&[dummy_attribute()]))?;
    if dummy_value == G1::identity() {
        return Err("degenerate fixed dummy".into());
    }
    let uk_fixed = c.pp.sc.srs1.iter().map(|&a| pair(a, c.pp.xs[4])).collect();
    let mut schemas = vec![];
    for (domain, body_len, n) in [
        (
            b"root issuance rho knowledge".as_slice(),
            249 + 32 * c.pp.sc.max_cardinality,
            2,
        ),
        (b"show nym knowledge".as_slice(), 673, 1),
        (b"show nym knowledge".as_slice(), 609, 1),
    ] {
        let mut prefix = vec![];
        frame(&mut prefix, PROFILE.as_bytes());
        frame(&mut prefix, &c.id);
        frame(&mut prefix, domain);
        schemas.push((domain.to_vec(), prefix, body_len, n));
    }
    let proof_base = std::sync::Arc::new(pok::InstalledBase::install_derived(c.h, schemas)?);
    Ok(Registered {
        pp: c.pp,
        id: c.id,
        h: c.h,
        dummy_value,
        uk_fixed,
        proof_base,
    })
}
/// Register the native public instance and its proof bases.
pub fn register(pp: PublicParameters) -> Result<Registered> {
    install_cache(register_checked(pp)?)
}
pub fn period_attribute() -> S {
    S::from(7u64)
}

pub struct UserKey {
    secret: S,
    public: G1,
}
impl UserKey {
    pub fn public(&self) -> G1 {
        self.public
    }
}
/// UKeyGen: generate a native holder or recipient key pair.
pub fn user_keygen(rng: &mut impl RngCore) -> UserKey {
    let secret = random_nonzero(rng);
    UserKey {
        secret,
        public: g1_mul(G1::generator(), secret),
    }
}
fn nym(key: &UserKey, rng: &mut impl RngCore) -> (G1, S) {
    let psi = random_nonzero(rng);
    loop {
        let chi = random_nonzero(rng);
        let s = (key.secret + chi) * psi;
        if s != S::ZERO {
            return (g1_mul(G1::generator(), s), s);
        }
    }
}
pub fn dummy_attribute() -> S {
    hash_scalar(
        b"\x53\x50\x53\x45\x51\x5f\x55\x43\x5f\x46\x49\x58\x45\x44\x5f\x44\x55\x4d\x4d\x59\x5f\x56\x32",
        b"public fixed root dummy; never disclosed",
    )
}

fn signature_points(cs: &[G1], sig: &Signature, decoded: bool) -> bool {
    (2..=3).contains(&cs.len())
        && cs.iter().all(|c| {
            if decoded {
                *c != G1::identity()
            } else {
                valid1(*c, true)
            }
        })
        && (if decoded {
            sig.y != G1::identity() && sig.yhat != G2::identity()
        } else {
            valid1(sig.z, false)
                && valid1(sig.y, true)
                && valid2(sig.yhat, true)
                && valid1(sig.t, false)
        })
}
pub fn verify_signature(v: &Registered, nym: G1, cs: &[G1], sig: &Signature) -> bool {
    valid1(nym, true) && signature_points(cs, sig, false) && verify_signature_body(v, nym, cs, sig)
}
fn verify_signature_body(v: &Registered, nym: G1, cs: &[G1], sig: &Signature) -> bool {
    if multi_pair(&[(sig.y, G2::generator()), (-G1::generator(), sig.yhat)]) != GT::identity() {
        return false;
    }
    if multi_pair(&[
        (sig.t, G2::generator()),
        (-sig.y, v.pp.xs[1]),
        (-nym, v.pp.xs[0]),
    ]) != GT::identity()
    {
        return false;
    }
    let mut terms = vec![(sig.z, sig.yhat)];
    for (i, c) in cs.iter().enumerate() {
        terms.push((-*c, v.pp.xs[i + 2]));
    }
    multi_pair(&terms) == GT::identity()
}

fn signature_equations(v: &Registered, nym: G1, cs: &[G1], sig: &Signature) -> Vec<Equation> {
    let mut signed = vec![(sig.z, sig.yhat)];
    signed.extend(cs.iter().enumerate().map(|(i, c)| (-*c, v.pp.xs[i + 2])));
    vec![
        Equation {
            terms: vec![(sig.y, G2::generator()), (-G1::generator(), sig.yhat)],
            target: GT::identity(),
        },
        Equation {
            terms: vec![
                (sig.t, G2::generator()),
                (-sig.y, v.pp.xs[1]),
                (-nym, v.pp.xs[0]),
            ],
            target: GT::identity(),
        },
        Equation {
            terms: signed,
            target: GT::identity(),
        },
    ]
}

/// The native signature's three equations, checked with fresh full-field
/// verifier weights only after the complete received signature is checked.
pub fn verify_signature_random(
    v: &Registered,
    nym: G1,
    cs: &[G1],
    sig: &Signature,
    rng: &mut impl RngCore,
) -> bool {
    valid1(nym, true)
        && signature_points(cs, sig, false)
        && pairing_verify::verify(
            &signature_equations(v, nym, cs, sig),
            VerificationMode::Randomized,
            rng,
        )
}
// Retain the exact shared native guard or state layout; current checked paths may not call every fallback.
#[cfg(test)]
pub(crate) fn openings_valid(v: &Registered, cs: &[G1], sets: &[Vec<S>], os: &[S]) -> bool {
    cs.len() == sets.len()
        && cs.len() == os.len()
        && cs.iter().zip(sets).zip(os).all(|((c, s), o)| {
            if s == &vec![dummy_attribute()] {
                *o != S::ZERO && valid1(*c, true) && g1_mul(v.dummy_value, *o) == *c
            } else {
                sc::open(&v.pp.sc, *c, s, *o)
            }
        })
}
fn openings_checked(v: &Registered, cs: &[G1], sets: &[Vec<S>], os: &[S]) -> bool {
    cs.len() == sets.len()
        && cs.len() == os.len()
        && cs.iter().zip(sets).zip(os).all(|((c, s), o)| {
            if s == &vec![dummy_attribute()] {
                *o != S::ZERO && *c != G1::identity() && g1_mul(v.dummy_value, *o) == *c
            } else {
                sc::open_checked(v, *c, s, *o)
            }
        })
}
pub(crate) fn decoded_credential_valid(
    v: &Registered,
    nym: G1,
    cs: &[G1],
    sig: &Signature,
    sets: &[Vec<S>],
    os: &[S],
) -> bool {
    nym != G1::identity()
        && signature_points(cs, sig, true)
        && verify_signature_body(v, nym, cs, sig)
        && openings_checked(v, cs, sets, os)
}
/// Only the fresh, pre-randomization UK is subject to the printed UKVerify.
pub fn verify_fresh_update_key(v: &Registered, key: &[G1], sig: &Signature) -> bool {
    valid2(sig.yhat, true) && fresh_key_body(v, key, sig, false)
}
fn fresh_key_body(v: &Registered, key: &[G1], sig: &Signature, decoded: bool) -> bool {
    key.len() == v.pp.sc.srs1.len()
        && key.iter().enumerate().all(|(i, u)| {
            (if decoded {
                *u != G1::identity()
            } else {
                valid1(*u, true)
            }) && pair(*u, sig.yhat) == v.uk_fixed[i]
        })
}

fn fresh_key_equations(
    v: &Registered,
    key: &[G1],
    sig: &Signature,
    decoded: bool,
    cached_targets: bool,
) -> Result<Vec<Equation>> {
    if key.len() != v.pp.sc.srs1.len()
        || key.iter().any(|u| {
            if decoded {
                *u == G1::identity()
            } else {
                !valid1(*u, true)
            }
        })
    {
        return Err("invalid fresh update key".into());
    }
    Ok(key
        .iter()
        .enumerate()
        .map(|(i, u)| Equation {
            terms: if cached_targets {
                vec![(*u, sig.yhat)]
            } else {
                vec![(*u, sig.yhat), (-v.pp.sc.srs1[i], v.pp.xs[4])]
            },
            target: if cached_targets {
                v.uk_fixed[i]
            } else {
                GT::identity()
            },
        })
        .collect())
}

pub(crate) struct RootUpdate {
    pub(crate) key: Vec<G1>,
    pub(crate) private_mu: S,
}
/// Validated local holder state. Secrets/scale are never part of public messages.
pub struct Credential {
    pub(crate) system_id: Vec<u8>,
    pub(crate) sig: Signature,
    pub(crate) cs: Vec<G1>,
    pub(crate) sets: Vec<Vec<S>>,
    pub(crate) openings: Vec<S>,
    pub(crate) nym: G1,
    pub(crate) aux: S,
    pub(crate) update: Option<RootUpdate>,
}
impl Credential {
    pub fn terminal(&self) -> bool {
        self.update.is_none()
    }
    pub fn commitment_count(&self) -> usize {
        self.cs.len()
    }
    /// Signature plus holder-only attributes/openings/aux and optional UK+mu.
    pub fn storage_payload_bytes(&self) -> usize {
        3 * 48
            + 96
            + self.cs.len() * 48
            + self.sets.iter().map(|s| s.len() * 32).sum::<usize>()
            + self.openings.len() * 32
            + 48
            + 32
            + self.update.as_ref().map_or(0, |u| u.key.len() * 48 + 32)
    }
}

// The parameter list follows the native multi-party protocol interface; do not regroup its arguments.
#[allow(clippy::too_many_arguments)]
fn randomize(
    v: &Registered,
    sig: &Signature,
    cs: &[G1],
    os: &[S],
    _nym: G1,
    aux: S,
    update: Option<&RootUpdate>,
    rng: &mut impl RngCore,
) -> (Signature, Vec<G1>, Vec<S>, G1, S, Option<RootUpdate>) {
    let mu = random_nonzero(rng);
    let psi = random_nonzero(rng);
    let chi = loop {
        let c = random_nonzero(rng);
        if aux + c != S::ZERO {
            break c;
        }
    };
    let scale = mu * inv(psi);
    let sig = Signature {
        z: g1_mul(sig.z, scale),
        y: g1_mul(sig.y, psi),
        yhat: g2_mul(sig.yhat, psi),
        t: g1_mul(g1_add(sig.t, g1_mul(v.pp.x0, chi)), psi),
    };
    let cs = cs.iter().map(|c| g1_mul(*c, mu)).collect();
    let os = os.iter().map(|o| *o * mu).collect();
    let newnym = g1_mul(G1::generator(), (aux + chi) * psi);
    let newaux = (aux + chi) * psi;
    let update = update.map(|u| RootUpdate {
        key: u.key.iter().map(|a| g1_mul(*a, scale)).collect(),
        private_mu: u.private_mu * mu,
    });
    (sig, cs, os, newnym, newaux, update)
}
fn binding(v: &Registered, domain: &[u8], body: &[u8]) -> Vec<u8> {
    if let Some(b) = v.proof_base.binding(domain, body) {
        return b;
    }
    let mut b = Vec::new();
    frame(&mut b, PROFILE.as_bytes());
    frame(&mut b, v.id());
    frame(&mut b, domain);
    frame(&mut b, body);
    b
}

#[derive(Clone, Debug)]
pub struct IssueRequest {
    pub session: [u8; 32],
    pub nym: G1,
    pub blinded: Vec<G1>,
    pub sets: Vec<Vec<S>>,
    pub first: pok::First,
}
pub struct IssueUserState {
    system_id: Vec<u8>,
    req: IssueRequest,
    aux: S,
    rhos: Vec<S>,
    proof: pok::ProverState,
}
pub struct IssueAwait {
    system_id: Vec<u8>,
    req: IssueRequest,
    aux: S,
    rhos: Vec<S>,
}
pub struct IssueVerifierState {
    system_id: Vec<u8>,
    req: IssueRequest,
    proof: pok::VerifierState,
}
#[derive(Clone, Debug)]
pub struct IssueDelivery {
    pub request_id: Vec<u8>,
    pub sig: Signature,
    pub cs: Vec<G1>,
    pub update_key: Vec<G1>,
}

/// Begin native credential acquisition and its holder proof.
pub fn issue_begin(
    v: &Registered,
    key: &UserKey,
    business: Vec<S>,
    rng: &mut impl RngCore,
) -> Result<(IssueRequest, IssueUserState)> {
    if !sc::validate_set(&v.pp.sc, &business)
        || business.len() != v.pp.sc.max_cardinality
        || business.contains(&period_attribute())
        || business.contains(&dummy_attribute())
    {
        return Err("invalid root business set".into());
    }
    let sets = vec![vec![dummy_attribute()], business];
    let (nym, aux) = nym(key, rng);
    let rhos: Vec<_> = (0..2).map(|_| random_nonzero(rng)).collect();
    let blinded = rhos
        .iter()
        .map(|r| g1_mul(G1::generator(), *r))
        .collect::<Vec<_>>();
    let mut session = [0; 32];
    rng.fill_bytes(&mut session);
    let mut req = IssueRequest {
        session,
        nym,
        blinded,
        sets,
        first: pok::First {
            commitment: G1::identity(),
        },
    };
    let b = binding(
        v,
        b"root issuance rho knowledge",
        &wire::issue_statement(&req),
    );
    let (first, proof) = pok::start_local(&v.proof_base, &req.blinded, &rhos, &b, rng)?;
    req.first = first;
    Ok((
        req.clone(),
        IssueUserState {
            system_id: v.id.clone(),
            req,
            aux,
            rhos,
            proof,
        },
    ))
}
/// Received point fields validated once; owned and immutable after ingress.
pub struct CheckedIssueRequest(IssueRequest);
impl CheckedIssueRequest {
    pub fn message(&self) -> &IssueRequest {
        &self.0
    }
}
pub fn check_issue_request(req: IssueRequest) -> Result<CheckedIssueRequest> {
    checked_issue(req, false)
}
pub(crate) fn decoded_issue_request(req: IssueRequest) -> Result<CheckedIssueRequest> {
    checked_issue(req, true)
}
fn checked_issue(req: IssueRequest, decoded: bool) -> Result<CheckedIssueRequest> {
    if if decoded {
        req.nym == G1::identity() || req.blinded.iter().any(|p| *p == G1::identity())
    } else {
        !valid1(req.nym, true)
            || req.blinded.iter().any(|p| !valid1(*p, true))
            || !valid1(req.first.commitment, false)
    } {
        return Err("invalid received issue points".into());
    }
    Ok(CheckedIssueRequest(req))
}
pub fn issue_challenge(
    v: &Registered,
    req: IssueRequest,
    rng: &mut impl RngCore,
) -> Result<(pok::Challenge, IssueVerifierState)> {
    issue_challenge_checked(v, check_issue_request(req)?, rng)
}
pub fn issue_challenge_checked(
    v: &Registered,
    checked: CheckedIssueRequest,
    rng: &mut impl RngCore,
) -> Result<(pok::Challenge, IssueVerifierState)> {
    let req = checked.0;
    if req.blinded.len() != 2
        || req.sets.len() != 2
        || req.sets[0] != vec![dummy_attribute()]
        || req.sets[1].len() != v.pp.sc.max_cardinality
        || req.sets[1].contains(&period_attribute())
        || req.sets[1].contains(&dummy_attribute())
        || req.sets.iter().any(|s| !sc::validate_set(&v.pp.sc, s))
    {
        return Err("malformed root issue request".into());
    }
    let b = binding(
        v,
        b"root issuance rho knowledge",
        &wire::issue_statement(&req),
    );
    let (c, proof) = pok::challenge_checked(&v.proof_base, &req.blinded, &b, &req.first, rng)?;
    Ok((
        c,
        IssueVerifierState {
            system_id: v.id.clone(),
            req,
            proof,
        },
    ))
}
/// Consume holder proof state to respond to the original native challenge.
pub fn issue_respond(
    state: IssueUserState,
    c: pok::Challenge,
) -> Result<(pok::Response, IssueAwait)> {
    let r = pok::respond(state.proof, c)?;
    Ok((
        r,
        IssueAwait {
            system_id: state.system_id,
            req: state.req,
            aux: state.aux,
            rhos: state.rhos,
        },
    ))
}
/// Verify the holder proof and create the native credential delivery.
pub fn issue_issuer(
    v: &Registered,
    issuer: &Issuer,
    state: IssueVerifierState,
    response: pok::Response,
    rng: &mut impl RngCore,
) -> Result<IssueDelivery> {
    if state.system_id != v.id || issuer.system_id != v.id || !pok::verify(state.proof, &response) {
        return Err("root rho proof or system binding rejected".into());
    }
    issue_issuer_body(v, issuer, state.req, rng)
}
pub fn issue_issuer_received(
    v: &Registered,
    issuer: &Issuer,
    state: IssueVerifierState,
    response: pok::ReceivedResponse,
    rng: &mut impl RngCore,
) -> Result<IssueDelivery> {
    if state.system_id != v.id
        || issuer.system_id != v.id
        || !pok::verify_received(state.proof, response)
    {
        return Err("root rho proof or system binding rejected".into());
    }
    issue_issuer_body(v, issuer, state.req, rng)
}
fn issue_issuer_body(
    v: &Registered,
    issuer: &Issuer,
    req: IssueRequest,
    rng: &mut impl RngCore,
) -> Result<IssueDelivery> {
    let mut cs = Vec::new();
    for (s, b) in req.sets.iter().zip(&req.blinded) {
        cs.push(sc::commit_blind_checked(v, s, issuer.alpha, *b)?)
    }
    let y = random_nonzero(rng);
    let yinv = inv(y);
    let z = sum1(&[(cs[0], issuer.x[2] * yinv), (cs[1], issuer.x[3] * yinv)]);
    let yg = g1_mul(G1::generator(), y);
    let sig = Signature {
        z,
        y: yg,
        yhat: g2_mul(G2::generator(), y),
        t: sum1(&[(yg, issuer.x[1]), (req.nym, issuer.x[0])]),
    };
    let update_key =
        v.pp.sc
            .srs1
            .iter()
            .map(|p| g1_mul(*p, issuer.x[4] * yinv))
            .collect();
    Ok(IssueDelivery {
        request_id: digest(&wire::encode_issue_request(&req)),
        sig,
        cs,
        update_key,
    })
}
pub struct CheckedIssueDelivery(IssueDelivery);
impl CheckedIssueDelivery {
    pub fn message(&self) -> &IssueDelivery {
        &self.0
    }
}
pub(crate) fn decoded_issue_delivery(m: IssueDelivery) -> CheckedIssueDelivery {
    CheckedIssueDelivery(m)
}
/// Accept the native issuer delivery and obtain the checked credential.
pub fn issue_finish(
    v: &Registered,
    state: IssueAwait,
    delivery: IssueDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    issue_finish_body(
        v,
        state,
        delivery,
        rng,
        false,
        VerificationMode::Specification,
        true,
        None,
    )
}
pub fn issue_finish_checked(
    v: &Registered,
    state: IssueAwait,
    delivery: CheckedIssueDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    issue_finish_body(
        v,
        state,
        delivery.0,
        rng,
        true,
        VerificationMode::Specification,
        true,
        None,
    )
}
/// Native issuance acceptance, aggregating every signature and fresh-update
/// key pairing equation. Attribute openings remain fully checked.
pub fn issue_finish_random(
    v: &Registered,
    state: IssueAwait,
    delivery: IssueDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    issue_finish_body(
        v,
        state,
        delivery,
        rng,
        false,
        VerificationMode::Randomized,
        true,
        None,
    )
}
pub fn issue_finish_checked_random(
    v: &Registered,
    state: IssueAwait,
    delivery: CheckedIssueDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    issue_finish_body(
        v,
        state,
        delivery.0,
        rng,
        true,
        VerificationMode::Randomized,
        true,
        None,
    )
}
/// Algebraically equivalent issuance candidate: retain update-key relations
/// as pairing products rather than cached GT targets. Backend merging uses
/// one additional G2 base and avoids one GT power per update-key element.
/// Prepare verification against a registered key.
pub fn issue_finish_random_pairing_key(
    v: &Registered,
    state: IssueAwait,
    delivery: IssueDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    issue_finish_body(
        v,
        state,
        delivery,
        rng,
        false,
        VerificationMode::Randomized,
        false,
        None,
    )
}
pub fn issue_finish_checked_random_pairing_key(
    v: &Registered,
    state: IssueAwait,
    delivery: CheckedIssueDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    issue_finish_body(
        v,
        state,
        delivery.0,
        rng,
        true,
        VerificationMode::Randomized,
        false,
        None,
    )
}
/// Separate verifier coefficients from the native credential-rerandomization tape.
pub fn issue_finish_checked_random_pairing_key_rngs(
    v: &Registered,
    state: IssueAwait,
    delivery: CheckedIssueDelivery,
    weights: &mut impl RngCore,
    native: &mut impl RngCore,
) -> Result<Credential> {
    issue_finish_body(
        v,
        state,
        delivery.0,
        native,
        true,
        VerificationMode::Randomized,
        false,
        Some(weights),
    )
}
#[allow(clippy::too_many_arguments)]
fn issue_finish_body(
    v: &Registered,
    state: IssueAwait,
    delivery: IssueDelivery,
    rng: &mut impl RngCore,
    decoded: bool,
    mode: VerificationMode,
    cached_targets: bool,
    mut external_weights: Option<&mut dyn RngCore>,
) -> Result<Credential> {
    if state.system_id != v.id
        || delivery.request_id != digest(&wire::encode_issue_request(&state.req))
        || !signature_points(&delivery.cs, &delivery.sig, decoded)
    {
        return Err("root receive verification failed".into());
    }
    let accepted = if mode == VerificationMode::Specification {
        verify_signature_body(v, state.req.nym, &delivery.cs, &delivery.sig)
            && openings_checked(v, &delivery.cs, &state.req.sets, &state.rhos)
            && fresh_key_body(v, &delivery.update_key, &delivery.sig, decoded)
    } else {
        if !openings_checked(v, &delivery.cs, &state.req.sets, &state.rhos) {
            return Err("root openings rejected".into());
        }
        let mut eq = signature_equations(v, state.req.nym, &delivery.cs, &delivery.sig);
        eq.extend(fresh_key_equations(
            v,
            &delivery.update_key,
            &delivery.sig,
            decoded,
            cached_targets,
        )?);
        match external_weights.as_mut() {
            Some(weights) => {
                if decoded {
                    pairing_verify::verify_checked(&eq, mode, weights)
                } else {
                    pairing_verify::verify(&eq, mode, weights)
                }
            }
            None => {
                if decoded {
                    pairing_verify::verify_checked(&eq, mode, rng)
                } else {
                    pairing_verify::verify(&eq, mode, rng)
                }
            }
        }
    };
    if !accepted {
        return Err("root receive verification failed".into());
    }
    let fresh = RootUpdate {
        key: delivery.update_key,
        private_mu: S::ONE,
    };
    let (sig, cs, openings, nym, aux, update) = randomize(
        v,
        &delivery.sig,
        &delivery.cs,
        &state.rhos,
        state.req.nym,
        state.aux,
        Some(&fresh),
        rng,
    );
    Ok(Credential {
        system_id: v.id.clone(),
        sig,
        cs,
        sets: state.req.sets,
        openings,
        nym,
        aux,
        update,
    })
}

#[derive(Clone, Debug)]
pub struct DelegateRequest {
    pub session: [u8; 32],
    pub nym: G1,
    pub added: Vec<S>,
}
pub struct DelegateAwait {
    system_id: Vec<u8>,
    req: DelegateRequest,
    aux: S,
}
#[derive(Clone, Debug)]
pub struct DelegateDelivery {
    pub request_id: Vec<u8>,
    pub orphan: Signature,
    pub cs: Vec<G1>,
    pub sets: Vec<Vec<S>>,
    pub openings: Vec<S>,
}
/// This profile follows Fig.2's terminal request, without the extra author-code
/// recipient nym PoK. Root rho knowledge and Show nym knowledge remain complete.
/// Begin the native recipient request for delegation.
pub fn delegate_begin(
    v: &Registered,
    key: &UserKey,
    added: Vec<S>,
    rng: &mut impl RngCore,
) -> Result<(DelegateRequest, DelegateAwait)> {
    if added != vec![period_attribute()] {
        return Err("profile requires fixed period singleton".into());
    }
    let (nym, aux) = nym(key, rng);
    let mut session = [0; 32];
    rng.fill_bytes(&mut session);
    let req = DelegateRequest {
        session,
        nym,
        added,
    };
    Ok((
        req.clone(),
        DelegateAwait {
            system_id: v.id.clone(),
            req,
            aux,
        },
    ))
}
pub struct CheckedDelegateRequest(DelegateRequest);
impl CheckedDelegateRequest {
    pub fn message(&self) -> &DelegateRequest {
        &self.0
    }
}
pub(crate) fn decoded_delegate_request(m: DelegateRequest) -> Result<CheckedDelegateRequest> {
    if m.nym == G1::identity() {
        return Err("zero receiver nym".into());
    }
    Ok(CheckedDelegateRequest(m))
}
/// Create the native holder delegation delivery.
pub fn delegate_sender(
    v: &Registered,
    root: &Credential,
    req: DelegateRequest,
    rng: &mut impl RngCore,
) -> Result<DelegateDelivery> {
    delegate_sender_body(v, root, req, rng, false)
}
pub fn delegate_sender_checked(
    v: &Registered,
    root: &Credential,
    req: CheckedDelegateRequest,
    rng: &mut impl RngCore,
) -> Result<DelegateDelivery> {
    delegate_sender_body(v, root, req.0, rng, true)
}
fn delegate_sender_body(
    v: &Registered,
    root: &Credential,
    req: DelegateRequest,
    rng: &mut impl RngCore,
    decoded: bool,
) -> Result<DelegateDelivery> {
    if root.system_id != v.id {
        return Err("credential installed system mismatch".into());
    }
    let u = root
        .update
        .as_ref()
        .ok_or("terminal credential cannot delegate")?;
    if root.cs.len() != 2
        || (if decoded {
            req.nym == G1::identity()
        } else {
            !valid1(req.nym, true)
        })
        || req.added != vec![period_attribute()]
    {
        return Err("delegate request or root state rejected".into());
    }
    let rho = random_nonzero(rng);
    let fresh = sc::commit_local(v, &req.added, rho * u.private_mu)?;
    let coeff = sc::polynomial_coefficients(&req.added);
    if coeff.len() > u.key.len() {
        return Err("update key shorter than polynomial".into());
    }
    let delta = g1_mul(
        sum1(
            &u.key
                .iter()
                .copied()
                .zip(coeff.iter().copied())
                .collect::<Vec<_>>(),
        ),
        rho,
    );
    let orphan = Signature {
        z: g1_add(root.sig.z, delta),
        y: root.sig.y,
        yhat: root.sig.yhat,
        t: g1_add(root.sig.t, -g1_mul(v.pp.x0, root.aux)),
    };
    let mut cs = root.cs.clone();
    cs.push(fresh);
    let mut sets = root.sets.clone();
    sets.push(req.added.clone());
    let mut openings = root.openings.clone();
    openings.push(rho * u.private_mu);
    Ok(DelegateDelivery {
        request_id: digest(&wire::encode_delegate_request(&req)),
        orphan,
        cs,
        sets,
        openings,
    })
}
pub struct CheckedDelegateDelivery(DelegateDelivery);
impl CheckedDelegateDelivery {
    pub fn message(&self) -> &DelegateDelivery {
        &self.0
    }
}
pub(crate) fn decoded_delegate_delivery(m: DelegateDelivery) -> CheckedDelegateDelivery {
    CheckedDelegateDelivery(m)
}
/// Accept and validate the native delegated credential.
pub fn delegate_finish(
    v: &Registered,
    state: DelegateAwait,
    delivery: DelegateDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    delegate_finish_body(
        v,
        state,
        delivery,
        rng,
        false,
        VerificationMode::Specification,
        None,
    )
}
pub fn delegate_finish_checked(
    v: &Registered,
    state: DelegateAwait,
    delivery: CheckedDelegateDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    delegate_finish_body(
        v,
        state,
        delivery.0,
        rng,
        true,
        VerificationMode::Specification,
        None,
    )
}
/// Complete the unchanged terminal delivery with all native signature
/// equations in one verifier-random pairing check.
pub fn delegate_finish_random(
    v: &Registered,
    state: DelegateAwait,
    delivery: DelegateDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    delegate_finish_body(
        v,
        state,
        delivery,
        rng,
        false,
        VerificationMode::Randomized,
        None,
    )
}
pub fn delegate_finish_checked_random(
    v: &Registered,
    state: DelegateAwait,
    delivery: CheckedDelegateDelivery,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    delegate_finish_body(
        v,
        state,
        delivery.0,
        rng,
        true,
        VerificationMode::Randomized,
        None,
    )
}
/// Separate verifier coefficients from the native credential-rerandomization tape.
pub fn delegate_finish_checked_random_rngs(
    v: &Registered,
    state: DelegateAwait,
    delivery: CheckedDelegateDelivery,
    weights: &mut impl RngCore,
    native: &mut impl RngCore,
) -> Result<Credential> {
    delegate_finish_body(
        v,
        state,
        delivery.0,
        native,
        true,
        VerificationMode::Randomized,
        Some(weights),
    )
}
fn delegate_finish_body(
    v: &Registered,
    state: DelegateAwait,
    delivery: DelegateDelivery,
    rng: &mut impl RngCore,
    decoded: bool,
    mode: VerificationMode,
    mut external_weights: Option<&mut dyn RngCore>,
) -> Result<Credential> {
    if state.system_id != v.id
        || delivery.request_id != digest(&wire::encode_delegate_request(&state.req))
        || delivery.cs.len() != 3
        || delivery.sets.len() != 3
        || delivery.sets[0] != vec![dummy_attribute()]
        || delivery.sets[2] != state.req.added
    {
        return Err("delegate package binding failed".into());
    }
    if !signature_points(&delivery.cs, &delivery.orphan, decoded) {
        return Err("invalid received orphan points".into());
    }
    let mut sig = delivery.orphan;
    sig.t = g1_add(sig.t, g1_mul(v.pp.x0, state.aux));
    let accepted = if mode == VerificationMode::Specification {
        verify_signature_body(v, state.req.nym, &delivery.cs, &sig)
            && openings_checked(v, &delivery.cs, &delivery.sets, &delivery.openings)
    } else {
        openings_checked(v, &delivery.cs, &delivery.sets, &delivery.openings) && {
            let eq = signature_equations(v, state.req.nym, &delivery.cs, &sig);
            match external_weights.as_mut() {
                Some(weights) => {
                    if decoded {
                        pairing_verify::verify_checked(&eq, mode, weights)
                    } else {
                        pairing_verify::verify(&eq, mode, weights)
                    }
                }
                None => {
                    if decoded {
                        pairing_verify::verify_checked(&eq, mode, rng)
                    } else {
                        pairing_verify::verify(&eq, mode, rng)
                    }
                }
            }
        }
    };
    if !accepted {
        return Err("delegate receiver verification failed".into());
    }
    let (sig, cs, openings, nym, aux, update) = randomize(
        v,
        &sig,
        &delivery.cs,
        &delivery.openings,
        state.req.nym,
        state.aux,
        None,
        rng,
    );
    Ok(Credential {
        system_id: v.id.clone(),
        sig,
        cs,
        sets: delivery.sets,
        openings,
        nym,
        aux,
        update,
    })
}

#[derive(Clone, Debug, PartialEq)]
pub struct Disclosure {
    pub indices: Vec<usize>,
    pub sets: Vec<Vec<S>>,
}
impl Disclosure {
    pub fn count(&self) -> usize {
        self.sets.iter().map(Vec::len).sum()
    }
}
#[derive(Clone, Debug)]
pub struct ShowFirst {
    pub context: Vec<u8>,
    pub disclosed: Disclosure,
    pub sig: Signature,
    pub cs: Vec<G1>,
    pub nym: G1,
    pub witness: G1,
    pub first: pok::First,
}
pub struct ShowProverState {
    proof: pok::ProverState,
}
pub struct ShowVerifierState {
    system_id: Vec<u8>,
    message: ShowFirst,
    proof: pok::VerifierState,
}
fn disclosure_shape(v: &Registered, d: &Disclosure, cs_len: usize) -> bool {
    let shape = if cs_len == 3 {
        d.indices == vec![1, 2]
            && d.sets.len() == 2
            && d.sets[0].len() == 2
            && d.sets[1] == vec![period_attribute()]
    } else if cs_len == 2 {
        d.indices == vec![1] && d.sets.len() == 1 && d.sets[0].len() == 3
    } else {
        false
    };
    shape && d.sets.iter().all(|s| sc::validate_set(&v.pp.sc, s))
}
/// Secret, non-Clone and non-serializable per-show state. No future root subset
/// or context is accepted by preparation; the fixed period is schema semantics.
/// ```compile_fail
/// use baseline_core::msb23::scheme::*;
/// fn reused(v:&Registered,p:PreparedShow,d:Disclosure) {
///  let _=show_begin_online(v,p,d.clone(),vec![1]);
///  let _=show_begin_online(v,p,d,vec![2]);
/// }
/// ```
pub struct PreparedShow {
    system_id: Vec<u8>,
    sig: Signature,
    cs: Vec<G1>,
    nym: G1,
    open: Vec<sc::OpenedSet>,
    period_witness: Option<G1>,
    proof: pok::Prepared,
    encoded: wire::PreparedShowEncoding,
}
/// Prepare fresh one-use native presentation material.
pub fn show_prepare(
    v: &Registered,
    cred: &Credential,
    rng: &mut impl RngCore,
) -> Result<PreparedShow> {
    if cred.system_id != v.id
        || !(2..=3).contains(&cred.cs.len())
        || cred.sets.len() != cred.cs.len()
        || cred.openings.len() != cred.cs.len()
        || cred.sets[0] != vec![dummy_attribute()]
        || cred.sets[1].len() != v.pp.sc.max_cardinality
        || (cred.cs.len() == 3 && cred.sets[2] != vec![period_attribute()])
    {
        return Err("credential profile shape".into());
    }
    let (sig, cs, os, nym, aux, _) = randomize(
        v,
        &cred.sig,
        &cred.cs,
        &cred.openings,
        cred.nym,
        cred.aux,
        None,
        rng,
    );
    // The two possible business sets are fully opened BEFORE policy selection.
    let mut open = vec![];
    for i in 1..cs.len() {
        open.push(sc::prepare_open_local(v, cs[i], &cred.sets[i], os[i])?);
    }
    let period_witness = if cs.len() == 3 {
        Some(sc::subset_local(v, &open[1], &[period_attribute()])?)
    } else {
        None
    };
    let proof = pok::prepare_local(&v.proof_base, &[nym], &[aux], rng)?;
    let encoded = wire::PreparedShowEncoding::new(&sig, &cs, nym);
    Ok(PreparedShow {
        system_id: v.id.clone(),
        sig,
        cs,
        nym,
        open,
        period_witness,
        proof,
        encoded,
    })
}
/// One-use native material after the public disclosure has been fixed, but
/// before the application context arrives. Subset and aggregation work is done.
pub struct PreparedPolicyShow {
    prepared: PreparedShow,
    disclosed: Disclosure,
    witness: G1,
}
pub fn show_prepare_policy(
    v: &Registered,
    cred: &Credential,
    disclosed: Disclosure,
    rng: &mut impl RngCore,
) -> Result<PreparedPolicyShow> {
    show_bind_policy(v, show_prepare(v, cred, rng)?, disclosed)
}
/// Finish all disclosure-dependent native work while the policy is known.
pub fn show_bind_policy(
    v: &Registered,
    p: PreparedShow,
    disclosed: Disclosure,
) -> Result<PreparedPolicyShow> {
    if p.system_id != v.id || !disclosure_shape(v, &disclosed, p.cs.len()) {
        return Err("invalid disclosure/preparation binding".into());
    }
    let root_w = sc::subset_local(v, &p.open[0], &disclosed.sets[0])?;
    let mut witnesses = vec![root_w];
    if let Some(w) = p.period_witness {
        witnesses.push(w);
    }
    let selected: Vec<_> = disclosed.indices.iter().map(|&i| p.cs[i]).collect();
    let encoded_selected = p.encoded.selected_commitments(&disclosed.indices);
    let witness =
        sc::aggregate_local_encoded(v, &selected, &disclosed.sets, &witnesses, &encoded_selected)?;
    Ok(PreparedPolicyShow {
        prepared: p,
        disclosed,
        witness,
    })
}
/// Context-only native binding: the one fresh Damgard commitment remains online.
pub fn show_begin_prepared(
    v: &Registered,
    prepared: PreparedPolicyShow,
    context: Vec<u8>,
) -> Result<(ShowFirst, ShowProverState)> {
    let PreparedPolicyShow {
        prepared: p,
        disclosed,
        witness,
    } = prepared;
    if p.system_id != v.id || context.is_empty() || context.len() > 4096 {
        return Err("invalid context/preparation binding".into());
    }
    let mut m = ShowFirst {
        context,
        disclosed,
        sig: p.sig,
        cs: p.cs,
        nym: p.nym,
        witness,
        first: pok::First {
            commitment: G1::identity(),
        },
    };
    let b = binding(
        v,
        b"show nym knowledge",
        &wire::show_statement_prepared(&m, &p.encoded),
    );
    let (first, proof) = pok::bind_prepared(p.proof, &b)?;
    m.first = first;
    Ok((m, ShowProverState { proof }))
}
/// Late-policy reference boundary, retaining the original native operations.
pub fn show_begin_online(
    v: &Registered,
    p: PreparedShow,
    disclosed: Disclosure,
    context: Vec<u8>,
) -> Result<(ShowFirst, ShowProverState)> {
    if context.is_empty() || context.len() > 4096 {
        return Err("invalid context/preparation binding".into());
    }
    show_begin_prepared(v, show_bind_policy(v, p, disclosed)?, context)
}
pub fn show_begin(
    v: &Registered,
    cred: &Credential,
    disclosed: Disclosure,
    context: Vec<u8>,
    rng: &mut impl RngCore,
) -> Result<(ShowFirst, ShowProverState)> {
    show_begin_online(v, show_prepare(v, cred, rng)?, disclosed, context)
}
/// A full received first message with privately owned validation provenance.
pub struct CheckedShowFirst(ShowFirst);
impl CheckedShowFirst {
    pub fn message(&self) -> &ShowFirst {
        &self.0
    }
}
pub fn check_show_first(m: ShowFirst) -> Result<CheckedShowFirst> {
    checked_show(m, false)
}
pub(crate) fn decoded_show_first(m: ShowFirst) -> Result<CheckedShowFirst> {
    checked_show(m, true)
}
fn checked_show(m: ShowFirst, decoded: bool) -> Result<CheckedShowFirst> {
    if !signature_points(&m.cs, &m.sig, decoded)
        || (if decoded {
            m.nym == G1::identity() || m.witness == G1::identity()
        } else {
            !valid1(m.nym, true) || !valid1(m.witness, true) || !valid1(m.first.commitment, false)
        })
    {
        return Err("invalid received show points".into());
    }
    Ok(CheckedShowFirst(m))
}
/// Create the live verifier challenge bound to the native first message.
pub fn show_challenge(
    v: &Registered,
    m: ShowFirst,
    expected: &Disclosure,
    expected_context: &[u8],
    rng: &mut impl RngCore,
) -> Result<(pok::Challenge, ShowVerifierState)> {
    show_challenge_checked(v, check_show_first(m)?, expected, expected_context, rng)
}

/// Input-only received statement checks, without transcript hashing or PoK algebra.
pub fn decode_show_first_received(
    v: &Registered,
    bytes: &[u8],
    expected: &Disclosure,
    context: &[u8],
) -> Result<CheckedShowFirst> {
    let checked = wire::decode_show_first_checked(bytes)?;
    let m = checked.message();
    if m.context != context
        || m.context.is_empty()
        || m.context.len() > 4096
        || &m.disclosed != expected
        || !disclosure_shape(v, &m.disclosed, m.cs.len())
        || !(2..=3).contains(&m.cs.len())
    {
        return Err("show statement binding/shape failed".into());
    }
    Ok(checked)
}
pub fn decode_show_response_received(
    state: &ShowVerifierState,
    bytes: &[u8],
) -> Result<pok::ReceivedResponse> {
    pok::decode_response_for_state(&state.proof, bytes).map_err(str::to_owned)
}
pub fn show_challenge_checked(
    v: &Registered,
    checked: CheckedShowFirst,
    expected: &Disclosure,
    expected_context: &[u8],
    rng: &mut impl RngCore,
) -> Result<(pok::Challenge, ShowVerifierState)> {
    let m = checked.0;
    if m.context != expected_context
        || m.context.is_empty()
        || m.context.len() > 4096
        || &m.disclosed != expected
        || !disclosure_shape(v, &m.disclosed, m.cs.len())
        || !(2..=3).contains(&m.cs.len())
    {
        return Err("show statement binding/shape failed".into());
    }
    let b = binding(v, b"show nym knowledge", &wire::show_statement(&m));
    let (c, proof) = pok::challenge_checked(&v.proof_base, &[m.nym], &b, &m.first, rng)?;
    Ok((
        c,
        ShowVerifierState {
            system_id: v.id.clone(),
            message: m,
            proof,
        },
    ))
}
/// Consume the original holder presentation state and answer its saved challenge.
pub fn show_respond(s: ShowProverState, c: pok::Challenge) -> Result<pok::Response> {
    Ok(pok::respond(s.proof, c)?)
}
/// Verify the native response against the original saved verifier state.
pub fn show_verify(v: &Registered, s: ShowVerifierState, r: pok::Response) -> bool {
    if s.system_id != v.id || !pok::verify(s.proof, &r) {
        return false;
    }
    show_verify_body(v, s.message)
}
pub fn show_verify_received(
    v: &Registered,
    s: ShowVerifierState,
    r: pok::ReceivedResponse,
) -> bool {
    if s.system_id != v.id || !pok::verify_received(s.proof, r) {
        return false;
    }
    show_verify_body(v, s.message)
}
fn show_verify_body(v: &Registered, m: ShowFirst) -> bool {
    let selected = m
        .disclosed
        .indices
        .iter()
        .map(|i| m.cs[*i])
        .collect::<Vec<_>>();
    verify_signature_body(v, m.nym, &m.cs, &m.sig)
        && sc::verify_across_checked(v, &selected, &m.disclosed.sets, m.witness)
}

/// Immutable completed interactive presentation. This is produced only by
/// consuming a live verifier session and its one fixed response; it does not
/// expose a way to choose or replay a new challenge. Freezing is input
/// validation, not proof acceptance: call a verification function before state
/// registration or treating the presentation as authenticated.
pub struct FrozenShow {
    system_id: Vec<u8>,
    message: ShowFirst,
    proof: pok::FrozenProof,
}
impl FrozenShow {
    /// Sum of the three actual native interactive message encodings.
    pub fn wire_bytes(&self) -> usize {
        wire::encode_show_first(&self.message).len() + self.proof.wire_bytes()
    }
    pub fn wire_messages(&self) -> [Vec<u8>; 3] {
        let [challenge, response] = self.proof.wire_messages();
        [wire::encode_show_first(&self.message), challenge, response]
    }
    /// Framed canonical transcript for exact-request identity/cache binding.
    /// These three extra frames are accounting metadata, not transmitted
    /// protocol bytes and are not included by `wire_bytes()`.
    pub fn replay_binding(&self) -> Vec<u8> {
        let mut out = vec![];
        for message in self.wire_messages() {
            frame(&mut out, &message);
        }
        out
    }
    /// Model a replacement final message for this already completed session.
    /// The original public challenge, first message and issuer stay fixed.
    /// No live prover state or new challenge is produced.
    pub fn with_response_bytes(&self, bytes: &[u8]) -> Result<Self> {
        let response = pok::Response::from_bytes(bytes)?;
        let proof = self
            .proof
            .with_response(response)
            .ok_or("invalid replacement response")?;
        Ok(Self {
            system_id: self.system_id.clone(),
            message: self.message.clone(),
            proof,
        })
    }
}

/// The validation/freezing work belongs to the verifier's received-message
/// stage. It is not free holder preparation in a measurement harness.
pub fn freeze_show(
    v: &Registered,
    state: ShowVerifierState,
    response: pok::Response,
) -> Result<FrozenShow> {
    if state.system_id != v.id {
        return Err("show installed system mismatch".into());
    }
    let proof = pok::FrozenProof::new(state.proof, response)
        .ok_or("invalid received show proof shape/point")?;
    Ok(FrozenShow {
        system_id: state.system_id,
        message: state.message,
        proof,
    })
}
pub fn freeze_show_received(
    v: &Registered,
    state: ShowVerifierState,
    response: pok::ReceivedResponse,
) -> Result<FrozenShow> {
    if state.system_id != v.id {
        return Err("show installed system mismatch".into());
    }
    let proof = pok::FrozenProof::from_received(state.proof, response)
        .ok_or("invalid received show proof shape")?;
    Ok(FrozenShow {
        system_id: state.system_id,
        message: state.message,
        proof,
    })
}

fn show_equations(v: &Registered, m: &ShowFirst) -> Result<Vec<Equation>> {
    let selected = m
        .disclosed
        .indices
        .iter()
        .map(|i| m.cs[*i])
        .collect::<Vec<_>>();
    let mut equations = signature_equations(v, m.nym, &m.cs, &m.sig);
    equations.push(sc::across_equation_checked(
        v,
        &selected,
        &m.disclosed.sets,
        m.witness,
    )?);
    Ok(equations)
}

/// Every native interactive PoK is rechecked, and every signature and
/// across-set pairing equation is retained. Random weights are consumed only
/// after all immutable inputs and non-pairing proofs in the batch are checked.
pub fn verify_frozen_shows(
    v: &Registered,
    records: &[FrozenShow],
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    if records.is_empty() {
        return false;
    }
    let mut equations = vec![];
    for r in records {
        if r.system_id != v.id || !r.proof.verify() {
            return false;
        }
        let native = match show_equations(v, &r.message) {
            Ok(e) => e,
            Err(_) => return false,
        };
        equations.extend(native);
    }
    pairing_verify::verify_checked(&equations, mode, rng)
}

pub fn verify_frozen_show(
    v: &Registered,
    record: &FrozenShow,
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    verify_frozen_shows(v, std::slice::from_ref(record), mode, rng)
}

/// Complete one native interactive presentation with the common randomized
/// engineering verifier; no Fiat--Shamir conversion replaces the interaction.
pub fn show_verify_random(
    v: &Registered,
    state: ShowVerifierState,
    response: pok::Response,
    rng: &mut impl RngCore,
) -> bool {
    match freeze_show(v, state, response) {
        Ok(record) => verify_frozen_show(v, &record, VerificationMode::Randomized, rng),
        Err(_) => false,
    }
}

#[cfg(test)]
mod randomized_verifier_tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    struct NoCoins;
    impl RngCore for NoCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("coins before all fixed input checks")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("coins before all fixed input checks")
        }
        fn fill_bytes(&mut self, _: &mut [u8]) {
            panic!("coins before all fixed input checks")
        }
        fn try_fill_bytes(&mut self, _: &mut [u8]) -> std::result::Result<(), rand::Error> {
            panic!("coins before all fixed input checks")
        }
    }
    fn fixture() -> (Registered, Credential, Credential, StdRng) {
        let mut rng = StdRng::seed_from_u64(212230);
        let (pp, issuer) = setup(9, &mut rng).unwrap();
        let v = register(pp).unwrap();
        let user = user_keygen(&mut rng);
        let agent = user_keygen(&mut rng);
        let (q, state) =
            issue_begin(&v, &user, (101..110).map(S::from).collect(), &mut rng).unwrap();
        let (c, vs) = issue_challenge(&v, q, &mut rng).unwrap();
        let (response, state) = issue_respond(state, c).unwrap();
        let delivery = issue_issuer(&v, &issuer, vs, response, &mut rng).unwrap();
        let root = issue_finish_random(&v, state, delivery, &mut rng).unwrap();
        let (q, state) = delegate_begin(&v, &agent, vec![period_attribute()], &mut rng).unwrap();
        let delivery = delegate_sender(&v, &root, q, &mut rng).unwrap();
        let child = delegate_finish_random(&v, state, delivery, &mut rng).unwrap();
        (v, root, child, rng)
    }
    fn disclosure(child: bool) -> Disclosure {
        if child {
            Disclosure {
                indices: vec![1, 2],
                sets: vec![vec![S::from(101), S::from(102)], vec![period_attribute()]],
            }
        } else {
            Disclosure {
                indices: vec![1],
                sets: vec![vec![S::from(101), S::from(102), S::from(103)]],
            }
        }
    }
    /// Bind a real native interactive PoK to the selected first message,
    /// including intentionally false pairing statements from a holder who
    /// still knows its nym. This isolates each checked pairing relation.
    fn record(v: &Registered, c: &Credential, bad: usize, rng: &mut StdRng) -> FrozenShow {
        let p = show_prepare(v, c, rng).unwrap();
        let disclosed = disclosure(c.cs.len() == 3);
        let mut witnesses = vec![sc::subset_local(v, &p.open[0], &disclosed.sets[0]).unwrap()];
        if let Some(w) = p.period_witness {
            witnesses.push(w);
        }
        let selected = disclosed
            .indices
            .iter()
            .map(|i| p.cs[*i])
            .collect::<Vec<_>>();
        let witness = sc::aggregate(&v.pp.sc, &selected, &disclosed.sets, &witnesses).unwrap();
        let mut m = ShowFirst {
            context: b"native-random-context".to_vec(),
            disclosed: disclosed.clone(),
            sig: p.sig,
            cs: p.cs,
            nym: p.nym,
            witness,
            first: pok::First {
                commitment: G1::identity(),
            },
        };
        match bad {
            1 => m.sig.y += G1::generator(),
            2 => m.sig.t += G1::generator(),
            3 => m.sig.z += G1::generator(),
            4 => m.witness += G1::generator(),
            _ => (),
        }
        let b = binding(v, b"show nym knowledge", &wire::show_statement(&m));
        let (first, proof) = pok::bind_prepared(p.proof, &b).unwrap();
        m.first = first;
        let first_bytes = wire::encode_show_first(&m);
        let (challenge, vs) =
            show_challenge(v, m, &disclosed, b"native-random-context", rng).unwrap();
        let cb = challenge.bytes();
        let mut response = pok::respond(proof, challenge).unwrap();
        if bad == 5 {
            response.responses[0] += S::ONE;
        }
        let rb = response.bytes();
        let frozen = freeze_show(v, vs, response).unwrap();
        assert_eq!(frozen.wire_messages(), [first_bytes, cb, rb]);
        assert_eq!(
            frozen.wire_bytes(),
            frozen.wire_messages().iter().map(Vec::len).sum::<usize>()
        );
        frozen
    }
    #[test]
    fn full_native_interaction_and_all_pairing_constraints_are_kept() {
        let (v, root, child, mut rng) = fixture();
        for credential in [&root, &child] {
            let r = record(&v, credential, 0, &mut rng);
            start_counts();
            assert!(verify_frozen_show(
                &v,
                &r,
                VerificationMode::Specification,
                &mut NoCoins
            ));
            let spec = stop_counts();
            assert_eq!(spec.p + spec.mp_calls, 4);
            start_counts();
            assert!(verify_frozen_show(
                &v,
                &r,
                VerificationMode::Randomized,
                &mut rng
            ));
            let random = stop_counts();
            assert_eq!(random.p + random.mp_calls, 1);
            for bad in 1..=4 {
                let r = record(&v, credential, bad, &mut rng);
                assert!(!verify_frozen_show(
                    &v,
                    &r,
                    VerificationMode::Specification,
                    &mut NoCoins
                ));
                for _ in 0..3 {
                    assert!(!verify_frozen_show(
                        &v,
                        &r,
                        VerificationMode::Randomized,
                        &mut rng
                    ));
                }
            }
        }
    }
    #[test]
    fn all_interactive_responses_are_checked_before_any_batch_coins() {
        let (v, root, child, mut rng) = fixture();
        let good = record(&v, &root, 0, &mut rng);
        let bad = record(&v, &child, 5, &mut rng);
        assert!(!verify_frozen_shows(
            &v,
            &[good, bad],
            VerificationMode::Randomized,
            &mut NoCoins
        ));
        assert!(!verify_frozen_shows(
            &v,
            &[],
            VerificationMode::Randomized,
            &mut NoCoins
        ));
        let records = (0..3)
            .map(|_| record(&v, &child, 0, &mut rng))
            .collect::<Vec<_>>();
        assert!(verify_frozen_shows(
            &v,
            &records,
            VerificationMode::Randomized,
            &mut rng
        ));
        assert!(verify_frozen_shows(
            &v,
            &records,
            VerificationMode::Specification,
            &mut NoCoins
        ));
        let mut response = pok::Response::from_bytes(&records[1].wire_messages()[2]).unwrap();
        response.responses[0] += S::ONE;
        let replaced = records[1].with_response_bytes(&response.bytes()).unwrap();
        assert_eq!(
            replaced.wire_messages()[..2],
            records[1].wire_messages()[..2]
        );
        assert!(!verify_frozen_show(
            &v,
            &replaced,
            VerificationMode::Randomized,
            &mut NoCoins
        ));
    }
    #[test]
    fn issuance_signature_and_every_update_key_equation_share_one_random_check() {
        let mut rng = StdRng::seed_from_u64(212231);
        let (pp, issuer) = setup(9, &mut rng).unwrap();
        let v = register(pp).unwrap();
        let user = user_keygen(&mut rng);
        for (cached, bad) in [true, false]
            .into_iter()
            .flat_map(|cached| [0, 1, 2].map(|bad| (cached, bad)))
        {
            let (q, state) =
                issue_begin(&v, &user, (101..110).map(S::from).collect(), &mut rng).unwrap();
            let (c, vs) = issue_challenge(&v, q, &mut rng).unwrap();
            let (response, state) = issue_respond(state, c).unwrap();
            let mut d = issue_issuer(&v, &issuer, vs, response, &mut rng).unwrap();
            if bad == 1 {
                d.sig.z += G1::generator();
            }
            if bad == 2 {
                d.update_key[7] += G1::generator();
            }
            start_counts();
            let result = if cached {
                issue_finish_random(&v, state, d, &mut rng)
            } else {
                issue_finish_random_pairing_key(&v, state, d, &mut rng)
            };
            let counts = stop_counts();
            assert_eq!(result.is_ok(), bad == 0);
            assert_eq!(counts.p + counts.mp_calls, 1);
            assert_eq!(counts.et, if cached { 10 } else { 0 });
        }
    }
    #[test]
    fn randomized_profile_accepts_complete_strictly_decoded_interactions() {
        let mut rng = StdRng::seed_from_u64(212232);
        let (pp, issuer) = setup(9, &mut rng).unwrap();
        let v = register(pp).unwrap();
        let user = user_keygen(&mut rng);
        let agent = user_keygen(&mut rng);
        let (q, state) =
            issue_begin(&v, &user, (101..110).map(S::from).collect(), &mut rng).unwrap();
        let q = wire::decode_issue_request_checked(&wire::encode_issue_request(&q)).unwrap();
        let (c, vs) = issue_challenge_checked(&v, q, &mut rng).unwrap();
        let (response, state) = issue_respond(state, c).unwrap();
        let response = pok::ReceivedResponse::from_bytes(&response.bytes()).unwrap();
        let delivery = issue_issuer_received(&v, &issuer, vs, response, &mut rng).unwrap();
        let delivery =
            wire::decode_issue_delivery_checked(&wire::encode_issue_delivery(&delivery)).unwrap();
        let root = issue_finish_checked_random(&v, state, delivery, &mut rng).unwrap();
        let (q, state) = delegate_begin(&v, &agent, vec![period_attribute()], &mut rng).unwrap();
        let q = wire::decode_delegate_request_checked(&wire::encode_delegate_request(&q)).unwrap();
        let delivery = delegate_sender_checked(&v, &root, q, &mut rng).unwrap();
        let delivery =
            wire::decode_delegate_delivery_checked(&wire::encode_delegate_delivery(&delivery))
                .unwrap();
        let child = delegate_finish_checked_random(&v, state, delivery, &mut rng).unwrap();
        let d = disclosure(true);
        let (m, ps) =
            show_begin(&v, &child, d.clone(), b"received-native".to_vec(), &mut rng).unwrap();
        let first = wire::encode_show_first(&m);
        let m = wire::decode_show_first_checked(&first).unwrap();
        let (c, vs) = show_challenge_checked(&v, m, &d, b"received-native", &mut rng).unwrap();
        let response = show_respond(ps, c).unwrap();
        let response = pok::ReceivedResponse::from_bytes(&response.bytes()).unwrap();
        let record = freeze_show_received(&v, vs, response).unwrap();
        assert!(verify_frozen_show(
            &v,
            &record,
            VerificationMode::Specification,
            &mut NoCoins
        ));
        assert!(verify_frozen_show(
            &v,
            &record,
            VerificationMode::Randomized,
            &mut rng
        ));
        assert_eq!(record.wire_messages()[0], first);
    }
}

#[cfg(test)]
mod preparation_guard_tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn whole_opening_is_checked_before_any_subset_is_chosen() {
        let mut r = StdRng::seed_from_u64(997);
        let (pp, iss) = setup(9, &mut r).unwrap();
        let v = register(pp).unwrap();
        let u = user_keygen(&mut r);
        let (q, x) = issue_begin(&v, &u, (101..110).map(S::from).collect(), &mut r).unwrap();
        let (c, y) = issue_challenge(&v, q, &mut r).unwrap();
        let (z, x) = issue_respond(x, c).unwrap();
        let d = issue_issuer(&v, &iss, y, z, &mut r).unwrap();
        let mut root = issue_finish(&v, x, d, &mut r).unwrap();
        root.openings[1] += S::ONE;
        assert!(show_prepare(&v, &root, &mut r).is_err());
    }
}

#[cfg(test)]
mod installed_system_binding_tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    // A second authentic issuer for the EXACT same SRS isolates issuer binding
    // from opening checks; different SRS alone would mask a missing guard.
    fn second_issuer_same_srs(
        pp: &PublicParameters,
        first: &Issuer,
        rng: &mut StdRng,
    ) -> (PublicParameters, Issuer) {
        let x: [S; 5] = std::array::from_fn(|_| random_nonzero(rng));
        let mut out = PublicParameters {
            sc: pp.sc.clone(),
            x0: g1_mul(G1::generator(), x[0]),
            xs: x.iter().map(|&v| g2_mul(G2::generator(), v)).collect(),
            registration: RegistrationProof {
                a1: vec![],
                a2: vec![],
                z: vec![],
            },
        };
        let w: Vec<S> = (0..6).map(|_| random_nonzero(&mut *rng)).collect();
        let a1 = vec![g1_mul(G1::generator(), w[0]), g1_mul(G1::generator(), w[5])];
        let a2 = w
            .iter()
            .map(|&v| g2_mul(G2::generator(), v))
            .collect::<Vec<_>>();
        let c = registration_challenge(&out, &a1, &a2);
        let z = w
            .iter()
            .enumerate()
            .map(|(j, &v)| v + c * if j < 5 { x[j] } else { first.alpha })
            .collect();
        out.registration = RegistrationProof { a1, a2, z };
        let system_id = digest(&wire::encode_parameters(&out));
        (
            out,
            Issuer {
                alpha: first.alpha,
                x,
                system_id,
            },
        )
    }
    #[test]
    fn same_srs_different_valid_issuer_cannot_use_holder_or_preparation() {
        let mut r = StdRng::seed_from_u64(8206);
        let (pp, i) = setup(9, &mut r).unwrap();
        let (other_pp, _) = second_issuer_same_srs(&pp, &i, &mut r);
        assert_eq!(pp.sc.srs1, other_pp.sc.srs1);
        assert_eq!(pp.sc.srs2, other_pp.sc.srs2);
        assert_ne!(pp.xs, other_pp.xs);
        let v = register(pp).unwrap();
        let other = register(other_pp).unwrap();
        let u = user_keygen(&mut r);
        let a = user_keygen(&mut r);
        let (q, x) = issue_begin(&v, &u, (101..110).map(S::from).collect(), &mut r).unwrap();
        let (c, y) = issue_challenge(&v, q, &mut r).unwrap();
        let (z, x) = issue_respond(x, c).unwrap();
        let d = issue_issuer(&v, &i, y, z, &mut r).unwrap();
        let root = issue_finish(&v, x, d, &mut r).unwrap();
        // Opening checks under this same-SRS other issuer would pass, so the
        // negative exercise specifically requires the private source binding.
        assert!(openings_valid(&other, &root.cs, &root.sets, &root.openings));
        assert!(show_prepare(&other, &root, &mut r).is_err());
        let (q, x) = delegate_begin(&v, &a, vec![period_attribute()], &mut r).unwrap();
        assert!(delegate_sender(&other, &root, q.clone(), &mut r).is_err());
        let d = delegate_sender(&v, &root, q, &mut r).unwrap();
        let child = delegate_finish(&v, x, d, &mut r).unwrap();
        assert!(openings_valid(
            &other,
            &child.cs,
            &child.sets,
            &child.openings
        ));
        assert!(show_prepare(&other, &child, &mut r).is_err());
        let p = show_prepare(&v, &child, &mut r).unwrap();
        let disc = Disclosure {
            indices: vec![1, 2],
            sets: vec![vec![S::from(101), S::from(102)], vec![period_attribute()]],
        };
        assert!(show_begin_online(&other, p, disc, vec![19; 32]).is_err());
        for cred in [&root, &child] {
            let b = wire::encode_credential(cred);
            assert!(wire::decode_credential(&other, &b).is_err());
            let restored = wire::decode_credential(&v, &b).unwrap();
            assert_eq!(wire::encode_credential(&restored), b);
            assert!(show_prepare(&other, &restored, &mut r).is_err());
        }
    }
}
