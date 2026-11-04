//! Interactive Damgard-compiled Schnorr proofs for a vector of G1 logarithms.
//!
//! Announcements A_i = w_i G are committed via a hash-to-scalar Pedersen
//! commitment K = H_Fr(statement, A_1,...,A_n) G + r H. Opening sends only
//! (A_i, r), NEVER w_i. Bare K=A+rH is not binding to arbitrary group messages.
//! The challenge comes from a private, consumed verifier session, not the proof.
//! Public H must be transparently derived (commitment_base) or independently
//! generated with its discrete logarithm unknown to every protocol participant.
use crate::arithmetic::*;
use blstrs::G1Affine;
use ff::Field;
use group::Group;
use rand::RngCore;
use std::sync::Arc;
pub type Result<T> = std::result::Result<T, &'static str>;
pub const MAX_RELATIONS: usize = 4096;
pub const MAX_BINDING_BYTES: usize = 1024 * 1024;
#[derive(Clone, Debug)]
pub struct First {
    pub commitment: G1,
}
#[derive(Clone, Debug)]
pub struct Challenge {
    pub c: S,
}
#[derive(Clone, Debug)]
pub struct Response {
    pub announcements: Vec<G1>,
    pub opening: S,
    pub responses: Vec<S>,
}
/// Non-Clone secret state, consumed even when its challenge is rejected.
pub struct ProverState {
    nonces: Vec<S>,
    secrets: Vec<S>,
    announcements: Vec<G1>,
    opening: S,
}
/// Non-Clone verifier-owned state. All fields are private and immutable.
pub struct VerifierState {
    h: G1,
    targets: Vec<G1>,
    binding: Vec<u8>,
    commitment: G1,
    c: S,
    installed: Option<Arc<InstalledBase>>,
}

pub fn commitment_base(domain: &[u8]) -> G1 {
    // Domain must be agreed system configuration, not a prover-supplied choice.
    let mut input = b"\x53\x50\x53\x45\x51\x2d\x55\x43\x2d\x70\x72\x6f\x66\x69\x6c\x65\x2d\x32\x2d\x72\x6f\x6f\x74\x39\x2d\x70\x65\x72\x69\x6f\x64\x31\x2d\x74\x65\x72\x6d\x69\x6e\x61\x6c\x2f\x44\x61\x6d\x67\x61\x72\x64\x2d\x43\x52\x53\x2f\x76\x32".to_vec();
    frame(&mut input, domain);
    hash_g1(b"SPSEQUC_DAMGARD_H", &input)
}
/// A registered, private immutable CRS capability. Dynamic targets and proof
/// elements remain subgroup-checked on every received session.
#[derive(Clone)]
pub(crate) struct InstalledBase {
    h: G1,
    bindings: Vec<(Vec<u8>, Vec<u8>)>,
    hashes: Vec<(usize, usize, Vec<u8>, ScalarHashPrefix)>,
}
// Retain the exact shared native guard or state layout; current checked paths may not call every fallback.
#[allow(dead_code)]
impl InstalledBase {
    pub(crate) fn install(h: G1, schemas: Vec<(Vec<u8>, Vec<u8>, usize, usize)>) -> Result<Self> {
        if !valid1(h, true) || h == G1::generator() || h == -G1::generator() {
            return Err("invalid registered Damgard CRS");
        }
        Self::install_body(h, schemas)
    }
    /// Registered protocol passes its hash-to-curve result; generic installation
    /// still performs full checks on caller-supplied CRS points.
    pub(crate) fn install_derived(
        h: G1,
        schemas: Vec<(Vec<u8>, Vec<u8>, usize, usize)>,
    ) -> Result<Self> {
        if h == G1::identity() || h == G1::generator() || h == -G1::generator() {
            return Err("invalid derived Damgard CRS");
        }
        Self::install_body(h, schemas)
    }
    fn install_body(h: G1, schemas: Vec<(Vec<u8>, Vec<u8>, usize, usize)>) -> Result<Self> {
        let mut bindings = vec![];
        let mut hashes = vec![];
        for (domain, binding_prefix, body_len, n) in schemas {
            let binding_len = binding_prefix.len() + 8 + body_len;
            let mut prefix = b"\x53\x50\x53\x45\x51\x2d\x55\x43\x2f\x44\x61\x6d\x67\x61\x72\x64\x2d\x67\x72\x6f\x75\x70\x2d\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2f\x76\x32".to_vec();
            prefix.extend(enc1(G1::generator()));
            prefix.extend(enc1(h));
            prefix.extend((binding_len as u64).to_be_bytes());
            prefix.extend(&binding_prefix);
            let input_len = prefix.len() + 8 + body_len + 16 + 96 * n;
            let state = ScalarHashPrefix::new(b"SPSEQUC_DAMGARD_MESSAGE", input_len, &prefix);
            hashes.push((binding_len, n, binding_prefix.clone(), state));
            if !bindings.iter().any(|(d, _)| d == &domain) {
                bindings.push((domain, binding_prefix));
            }
        }
        Ok(Self {
            h,
            bindings,
            hashes,
        })
    }
    pub(crate) fn binding(&self, domain: &[u8], body: &[u8]) -> Option<Vec<u8>> {
        self.bindings
            .iter()
            .find(|(d, _)| d == domain)
            .map(|(_, p)| {
                let mut b = p.clone();
                frame(&mut b, body);
                b
            })
    }
}

fn valid_inputs_cached(
    h: G1,
    targets: &[G1],
    binding: &[u8],
    installed: Option<&Arc<InstalledBase>>,
) -> bool {
    !targets.is_empty()
        && targets.len() <= MAX_RELATIONS
        && binding.len() <= MAX_BINDING_BYTES
        && installed.map_or_else(
            || valid1(h, true) && h != G1::generator() && h != -G1::generator(),
            |i| i.h == h,
        )
        && targets.iter().all(|&y| valid1(y, true))
}

fn message_cached(
    h: G1,
    targets: &[G1],
    binding: &[u8],
    announcements: &[G1],
    installed: Option<&Arc<InstalledBase>>,
) -> S {
    if let Some(i) = installed {
        if targets.len() == announcements.len() {
            if let Some((_, _, prefix, state)) = i.hashes.iter().find(|(len, n, p, _)| {
                *len == binding.len() && *n == targets.len() && binding.starts_with(p)
            }) {
                let mut suffix = binding[prefix.len()..].to_vec();
                suffix.extend((targets.len() as u64).to_be_bytes());
                for &y in targets {
                    suffix.extend(enc1(y));
                }
                suffix.extend((announcements.len() as u64).to_be_bytes());
                for &a in announcements {
                    suffix.extend(enc1(a));
                }
                return state.finish(&suffix);
            }
        }
    }
    let mut b = b"\x53\x50\x53\x45\x51\x2d\x55\x43\x2f\x44\x61\x6d\x67\x61\x72\x64\x2d\x67\x72\x6f\x75\x70\x2d\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2f\x76\x32".to_vec();
    b.extend(enc1(G1::generator()));
    b.extend(enc1(h));
    frame(&mut b, binding);
    b.extend((targets.len() as u64).to_be_bytes());
    for &y in targets {
        b.extend(enc1(y));
    }
    b.extend((announcements.len() as u64).to_be_bytes());
    for &a in announcements {
        b.extend(enc1(a));
    }
    hash_scalar(b"SPSEQUC_DAMGARD_MESSAGE", &b)
}
/// `binding` must include phase/session ID, system/key ID, and the exact public
/// application statement (credential, policy/disclosures and context as used).
/// This function assumes the caller knows the matching witnesses. A wrong
/// witness produces a response that the verifier rejects; we do not repeat all
/// y_i=G*x_i computations already performed by the calling protocol.
/// Secret one-use precomputation; its public statement is bound only later.
/// ```compile_fail
/// use baseline_core::msb23::pok::{Prepared,bind_prepared};
/// fn reuse(p:Prepared) { let _=bind_prepared(p,b"first"); let _=bind_prepared(p,b"second"); }
/// ```
/// ```compile_fail
/// use baseline_core::msb23::pok::Prepared;
/// fn copy(p:&Prepared) -> Prepared { p.clone() }
/// ```
pub struct Prepared {
    targets: Vec<G1>,
    state: ProverState,
    blind: G1,
    installed: Option<Arc<InstalledBase>>,
    encoded: PreparedMessageEncoding,
}
struct PreparedMessageEncoding {
    base: Vec<u8>,
    targets: Vec<u8>,
    announcements: Vec<u8>,
}
impl PreparedMessageEncoding {
    fn new(h: G1, targets: &[G1], announcements: &[G1]) -> Self {
        let mut base = b"\x53\x50\x53\x45\x51\x2d\x55\x43\x2f\x44\x61\x6d\x67\x61\x72\x64\x2d\x67\x72\x6f\x75\x70\x2d\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2f\x76\x32".to_vec();
        base.extend(enc1(G1::generator()));
        base.extend(enc1(h));
        let mut target_bytes = (targets.len() as u64).to_be_bytes().to_vec();
        for &y in targets {
            target_bytes.extend(enc1(y));
        }
        let mut announcement_bytes = (announcements.len() as u64).to_be_bytes().to_vec();
        for &a in announcements {
            announcement_bytes.extend(enc1(a));
        }
        Self {
            base,
            targets: target_bytes,
            announcements: announcement_bytes,
        }
    }
}
fn prepared_message(p: &Prepared, binding: &[u8]) -> S {
    if let Some(i) = p.installed.as_ref() {
        if let Some((_, _, prefix, state)) = i.hashes.iter().find(|(len, n, prefix, _)| {
            *len == binding.len() && *n == p.targets.len() && binding.starts_with(prefix)
        }) {
            let mut suffix = binding[prefix.len()..].to_vec();
            suffix.extend(&p.encoded.targets);
            suffix.extend(&p.encoded.announcements);
            return state.finish(&suffix);
        }
    }
    let mut b = p.encoded.base.clone();
    frame(&mut b, binding);
    b.extend(&p.encoded.targets);
    b.extend(&p.encoded.announcements);
    hash_scalar(b"SPSEQUC_DAMGARD_MESSAGE", &b)
}
pub fn prepare_g1(
    h: G1,
    targets: &[G1],
    secrets: &[S],
    rng: &mut impl RngCore,
) -> Result<Prepared> {
    prepare_g1_cached(h, targets, secrets, rng, None)
}

/// Only the owning installed protocol may use this entry: every target is a
/// generator multiple computed from its private witness in that same flow.
/// The public prepare_g1 API still validates arbitrary caller-supplied points.
pub(crate) fn prepare_local(
    i: &Arc<InstalledBase>,
    targets: &[G1],
    secrets: &[S],
    rng: &mut impl RngCore,
) -> Result<Prepared> {
    if targets.is_empty()
        || targets.len() > MAX_RELATIONS
        || targets.len() != secrets.len()
        || targets.iter().any(|y| *y == G1::identity())
    {
        return Err("invalid local Damgard statement");
    }
    prepare_body(i.h, targets, secrets, rng, Some(i))
}
fn prepare_g1_cached(
    h: G1,
    targets: &[G1],
    secrets: &[S],
    rng: &mut impl RngCore,
    installed: Option<&Arc<InstalledBase>>,
) -> Result<Prepared> {
    if !valid_inputs_cached(h, targets, &[], installed) || targets.len() != secrets.len() {
        return Err("invalid prepared Damgard statement");
    }
    prepare_body(h, targets, secrets, rng, installed)
}
fn prepare_body(
    h: G1,
    targets: &[G1],
    secrets: &[S],
    rng: &mut impl RngCore,
    installed: Option<&Arc<InstalledBase>>,
) -> Result<Prepared> {
    let nonces: Vec<_> = (0..targets.len())
        .map(|_| random_scalar(&mut *rng))
        .collect();
    let announcements: Vec<_> = nonces.iter().map(|&w| g1_mul(G1::generator(), w)).collect();
    let opening = random_scalar(rng);
    let blind = g1_mul(h, opening);
    let encoded = PreparedMessageEncoding::new(h, targets, &announcements);
    Ok(Prepared {
        targets: targets.to_vec(),
        state: ProverState {
            nonces,
            secrets: secrets.to_vec(),
            announcements,
            opening,
        },
        blind,
        installed: installed.cloned(),
        encoded,
    })
}
pub fn bind_prepared(p: Prepared, binding: &[u8]) -> Result<(First, ProverState)> {
    // Prepared has private immutable fields and was validated at construction.
    if binding.len() > MAX_BINDING_BYTES {
        return Err("invalid final Damgard binding");
    }
    let m = prepared_message(&p, binding);
    let commitment = g1_add(g1_mul(G1::generator(), m), p.blind);
    Ok((First { commitment }, p.state))
}
pub fn start_g1(
    h: G1,
    targets: &[G1],
    secrets: &[S],
    binding: &[u8],
    rng: &mut impl RngCore,
) -> Result<(First, ProverState)> {
    bind_prepared(prepare_g1(h, targets, secrets, rng)?, binding)
}

pub(crate) fn start_local(
    i: &Arc<InstalledBase>,
    targets: &[G1],
    secrets: &[S],
    binding: &[u8],
    rng: &mut impl RngCore,
) -> Result<(First, ProverState)> {
    bind_prepared(prepare_local(i, targets, secrets, rng)?, binding)
}
/// Called only by the verifier after receiving First. A returned Challenge is
/// public; the saved c in VerifierState is authoritative for acceptance.
pub fn challenge(
    h: G1,
    targets: &[G1],
    binding: &[u8],
    first: &First,
    rng: &mut impl RngCore,
) -> Result<(Challenge, VerifierState)> {
    challenge_cached(h, targets, binding, first, rng, None)
}

/// Crate-private continuation of an immutable checked protocol message. The
/// owning protocol validated all targets and First exactly once at ingress.
pub(crate) fn challenge_checked(
    i: &Arc<InstalledBase>,
    targets: &[G1],
    binding: &[u8],
    first: &First,
    rng: &mut impl RngCore,
) -> Result<(Challenge, VerifierState)> {
    if targets.is_empty()
        || targets.len() > MAX_RELATIONS
        || binding.len() > MAX_BINDING_BYTES
        || targets.iter().any(|y| *y == G1::identity())
    {
        return Err("invalid checked Damgard shape");
    }
    Ok(challenge_body(i.h, targets, binding, first, rng, Some(i)))
}
fn challenge_cached(
    h: G1,
    targets: &[G1],
    binding: &[u8],
    first: &First,
    rng: &mut impl RngCore,
    installed: Option<&Arc<InstalledBase>>,
) -> Result<(Challenge, VerifierState)> {
    if !valid_inputs_cached(h, targets, binding, installed) || !valid1(first.commitment, false) {
        return Err("invalid Damgard first message");
    }
    Ok(challenge_body(h, targets, binding, first, rng, installed))
}
fn challenge_body(
    h: G1,
    targets: &[G1],
    binding: &[u8],
    first: &First,
    rng: &mut impl RngCore,
    installed: Option<&Arc<InstalledBase>>,
) -> (Challenge, VerifierState) {
    let c = random_nonzero(rng);
    (
        Challenge { c },
        VerifierState {
            h,
            targets: targets.to_vec(),
            binding: binding.to_vec(),
            commitment: first.commitment,
            c,
            installed: installed.cloned(),
        },
    )
}
pub fn respond(state: ProverState, c: Challenge) -> Result<Response> {
    if c.c == S::ZERO {
        return Err("zero challenge outside this profile");
    }
    let responses = state
        .nonces
        .iter()
        .zip(&state.secrets)
        .map(|(&w, &x)| w + c.c * x)
        .collect();
    Ok(Response {
        announcements: state.announcements,
        opening: state.opening,
        responses,
    })
}
pub fn verify(state: VerifierState, response: &Response) -> bool {
    let n = state.targets.len();
    if response.announcements.len() != n
        || response.responses.len() != n
        || response.announcements.iter().any(|&a| !valid1(a, false))
    {
        return false;
    }
    verify_body(&state, response)
}
/// Decoded, owned proof response; no mutable accessor or public constructor.
pub struct ReceivedResponse(Response);
impl ReceivedResponse {
    pub fn from_bytes(b: &[u8]) -> Result<Self> {
        Ok(Self(Response::from_bytes(b)?))
    }
    pub fn bytes(&self) -> Vec<u8> {
        self.0.bytes()
    }
    pub fn received_field_counts(&self) -> (usize, usize) {
        (self.0.announcements.len(), 1 + self.0.responses.len())
    }
}
pub(crate) fn decode_response_for_state(
    state: &VerifierState,
    bytes: &[u8],
) -> Result<ReceivedResponse> {
    let response = ReceivedResponse::from_bytes(bytes)?;
    if response.0.announcements.len() != state.targets.len()
        || response.0.responses.len() != state.targets.len()
    {
        return Err("received proof response dimension");
    }
    Ok(response)
}
pub fn verify_received(state: VerifierState, response: ReceivedResponse) -> bool {
    let n = state.targets.len();
    if response.0.announcements.len() != n || response.0.responses.len() != n {
        return false;
    }
    verify_body(&state, &response.0)
}
/// A completed, immutable transcript. Creating this consumes the live
/// verifier state; it cannot produce a second challenge or change a response.
/// The same public transcript can subsequently be rechecked for batch failure
/// localization without rewinding the interactive prover.
pub(crate) struct FrozenProof {
    state: VerifierState,
    response: Response,
}
impl FrozenProof {
    pub(crate) fn new(state: VerifierState, response: Response) -> Option<Self> {
        let n = state.targets.len();
        if response.announcements.len() != n
            || response.responses.len() != n
            || response.announcements.iter().any(|&a| !valid1(a, false))
        {
            return None;
        }
        Some(Self { state, response })
    }
    pub(crate) fn verify(&self) -> bool {
        verify_body(&self.state, &self.response)
    }
    pub(crate) fn wire_bytes(&self) -> usize {
        self.wire_messages().iter().map(Vec::len).sum()
    }
    pub(crate) fn wire_messages(&self) -> [Vec<u8>; 2] {
        [Challenge { c: self.state.c }.bytes(), self.response.bytes()]
    }
    pub(crate) fn from_received(state: VerifierState, response: ReceivedResponse) -> Option<Self> {
        let n = state.targets.len();
        if response.0.announcements.len() != n || response.0.responses.len() != n {
            return None;
        }
        Some(Self {
            state,
            response: response.0,
        })
    }
    pub(crate) fn with_response(&self, response: Response) -> Option<Self> {
        let state = VerifierState {
            h: self.state.h,
            targets: self.state.targets.clone(),
            binding: self.state.binding.clone(),
            commitment: self.state.commitment,
            c: self.state.c,
            installed: self.state.installed.clone(),
        };
        Self::new(state, response)
    }
}
fn verify_body(state: &VerifierState, response: &Response) -> bool {
    let m = message_cached(
        state.h,
        &state.targets,
        &state.binding,
        &response.announcements,
        state.installed.as_ref(),
    );
    if g1_add(
        g1_mul(G1::generator(), m),
        g1_mul(state.h, response.opening),
    ) != state.commitment
    {
        return false;
    }
    // Check every relation separately; an aggregate sum would only prove the
    // logarithm of the sum of keys, permitting cancellation of unknown keys.
    state
        .targets
        .iter()
        .zip(&response.announcements)
        .zip(&response.responses)
        .all(|((&y, &a), &z)| g1_mul(G1::generator(), z) == g1_add(a, g1_mul(y, state.c)))
}
fn read_g1(b: &[u8]) -> Result<G1> {
    let a: [u8; 48] = b.try_into().map_err(|_| "wrong G1 length")?;
    crate::subgroup_audit::decode("G1", &a, "msb23::pok::read_g1");
    let p = Option::<G1Affine>::from(G1Affine::from_compressed(&a))
        .ok_or("invalid G1 encoding/subgroup")?;
    if p.to_compressed() != a {
        return Err("noncanonical G1");
    }
    Ok(G1::from(p))
}
fn read_scalar(b: &[u8]) -> Result<S> {
    let a: [u8; 32] = b.try_into().map_err(|_| "wrong scalar length")?;
    Option::<S>::from(S::from_bytes_be(&a)).ok_or("noncanonical scalar")
}
impl First {
    pub fn bytes(&self) -> Vec<u8> {
        enc1(self.commitment)
    }
    pub fn from_bytes(b: &[u8]) -> Result<Self> {
        Ok(Self {
            commitment: read_g1(b)?,
        })
    }
}
impl Challenge {
    pub fn bytes(&self) -> Vec<u8> {
        encs(self.c)
    }
    pub fn from_bytes(b: &[u8]) -> Result<Self> {
        let c = read_scalar(b)?;
        if c == S::ZERO {
            return Err("zero challenge");
        }
        Ok(Self { c })
    }
}
impl Response {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = vec![];
        b.extend((self.announcements.len() as u64).to_be_bytes());
        for &a in &self.announcements {
            b.extend(enc1(a));
        }
        b.extend(encs(self.opening));
        b.extend((self.responses.len() as u64).to_be_bytes());
        for &z in &self.responses {
            b.extend(encs(z));
        }
        b
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        struct Reader<'a> {
            b: &'a [u8],
            p: usize,
        }
        impl<'a> Reader<'a> {
            fn take(&mut self, n: usize) -> Result<&'a [u8]> {
                let e = self.p.checked_add(n).ok_or("length overflow")?;
                if e > self.b.len() {
                    return Err("truncated proof");
                }
                let x = &self.b[self.p..e];
                self.p = e;
                Ok(x)
            }
            fn count(&mut self) -> Result<usize> {
                let n = u64::from_be_bytes(self.take(8)?.try_into().unwrap());
                if n == 0 || n > MAX_RELATIONS as u64 {
                    return Err("proof count limit");
                }
                Ok(n as usize)
            }
        }
        if bytes.len() > 48 + MAX_RELATIONS * 80 {
            return Err("proof byte limit");
        }
        let mut r = Reader { b: bytes, p: 0 };
        let n = r.count()?;
        // Reject impossible allocation before parsing curve points.
        if bytes.len() != 48 + n * 80 {
            return Err("wrong canonical proof length");
        }
        let mut announcements = Vec::with_capacity(n);
        for _ in 0..n {
            announcements.push(read_g1(r.take(48)?)?);
        }
        let opening = read_scalar(r.take(32)?)?;
        if r.count()? != n {
            return Err("proof relation count mismatch");
        }
        let mut responses = Vec::with_capacity(n);
        for _ in 0..n {
            responses.push(read_scalar(r.take(32)?)?);
        }
        if r.p != bytes.len() {
            return Err("trailing proof bytes");
        }
        Ok(Self {
            announcements,
            opening,
            responses,
        })
    }
}
