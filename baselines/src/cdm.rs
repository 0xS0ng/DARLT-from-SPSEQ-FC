//! Four-message interactive compiler for prime-order group homomorphism proofs.
//! The public relation is fixed before the verifier's first message.
use crate::arithmetic::{
    g2_add, g2_mul, gt_add, gt_mul, pair, random_scalar, sum1, sum2, valid1, valid2, G1, G2, GT, S,
};
use crate::encoding::{Error, Reader, Result, Writer};
use crate::pairing_verify::{self, Equation, Mode as VerificationMode};
use group::Group;
use rand::{CryptoRng, RngCore};

pub const MAX_WITNESSES: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
// State variants keep the native owned protocol material without changing allocation or timing boundaries.
#[allow(clippy::large_enum_variant)]
pub enum Point {
    G2(G2),
    GT(GT),
}
impl Point {
    fn identity(self) -> Self {
        match self {
            Self::G2(_) => Self::G2(G2::identity()),
            Self::GT(_) => Self::GT(GT::identity()),
        }
    }
    fn kind(self) -> u8 {
        match self {
            Self::G2(_) => 0,
            Self::GT(_) => 1,
        }
    }
    fn valid(self) -> bool {
        match self {
            Self::G2(g) => valid2(g, false),
            // blstrs's default value is Fp12 zero, outside the group. Its
            // public group constructors otherwise produce subgroup elements.
            Self::GT(g) => g != GT::default(),
        }
    }
    fn domain_valid(self) -> bool {
        match self {
            Self::G2(_) => true,
            Self::GT(g) => g != GT::default(),
        }
    }
    fn add(self, other: Self) -> Result<Self> {
        match (self, other) {
            (Self::G2(a), Self::G2(b)) => Ok(Self::G2(g2_add(a, b))),
            (Self::GT(a), Self::GT(b)) => Ok(Self::GT(gt_add(a, b))),
            _ => Err(Error("group mismatch".into())),
        }
    }
    fn mul(self, scalar: S) -> Self {
        match self {
            Self::G2(g) => Self::G2(g2_mul(g, scalar)),
            Self::GT(g) => Self::GT(gt_mul(g, scalar)),
        }
    }
    fn write(self, w: &mut Writer) {
        w.u8(self.kind());
        match self {
            Self::G2(g) => w.g2(g),
            Self::GT(g) => w.gt(g),
        }
    }
    fn read(r: &mut Reader<'_>) -> Result<Self> {
        match r.u8()? {
            0 => Ok(Self::G2(r.g2(false)?)),
            1 => Ok(Self::GT(r.gt(false)?)),
            _ => Err(Error("point group tag".into())),
        }
    }
}

/// The homomorphism maps a vector of scalars to one prime-order group element.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Relation {
    bases: Vec<Point>,
    target: Point,
    paired_bases: Option<(Vec<G1>, G2)>,
}
impl Relation {
    pub fn g2(bases: Vec<G2>, target: G2) -> Result<Self> {
        Self::new(
            bases.into_iter().map(Point::G2).collect(),
            Point::G2(target),
        )
    }
    pub fn gt(bases: Vec<GT>, target: GT) -> Result<Self> {
        Self::new(
            bases.into_iter().map(Point::GT).collect(),
            Point::GT(target),
        )
    }
    /// The caller supplies only installed, locally generated or immediately
    /// decoded subgroup elements. Semantic relation checks still run.
    pub(crate) fn g2_trusted(bases: Vec<G2>, target: G2) -> Result<Self> {
        Self::new_inner(
            bases.into_iter().map(Point::G2).collect(),
            Point::G2(target),
            true,
        )
    }
    /// Evaluate a GT homomorphism with one pairing after a G1 multi-scalar sum.
    pub fn pairing_g1(bases: Vec<G1>, second: G2, target: GT) -> Result<Self> {
        Self::pairing_g1_inner(bases, second, target, false)
    }
    /// The G1 bases belong to an installed key, the G2 operand has already
    /// passed its source domain and subgroup checks, and GT is locally derived.
    pub(crate) fn pairing_g1_trusted(bases: Vec<G1>, second: G2, target: GT) -> Result<Self> {
        Self::pairing_g1_inner(bases, second, target, true)
    }
    fn pairing_g1_inner(bases: Vec<G1>, second: G2, target: GT, trusted: bool) -> Result<Self> {
        if bases.is_empty()
            || bases.len() > MAX_WITNESSES
            || second == G2::identity()
            || target == GT::default()
            || (!trusted && (!valid2(second, true) || bases.iter().any(|g| !valid1(*g, false))))
            || bases.iter().all(|g| *g == G1::identity())
        {
            return Err(Error("pairing homomorphism relation".into()));
        }
        Ok(Self {
            bases: vec![],
            target: Point::GT(target),
            paired_bases: Some((bases, second)),
        })
    }
    fn new(bases: Vec<Point>, target: Point) -> Result<Self> {
        Self::new_inner(bases, target, false)
    }
    fn new_inner(bases: Vec<Point>, target: Point, trusted: bool) -> Result<Self> {
        if bases.is_empty()
            || bases.len() > MAX_WITNESSES
            || !target.domain_valid()
            || (!trusted && !target.valid())
            || bases
                .iter()
                .any(|b| b.kind() != target.kind() || !b.domain_valid() || (!trusted && !b.valid()))
            || bases.iter().all(|b| *b == b.identity())
        {
            return Err(Error("homomorphism relation".into()));
        }
        Ok(Self {
            bases,
            target,
            paired_bases: None,
        })
    }
    pub fn dimension(&self) -> usize {
        self.paired_bases
            .as_ref()
            .map(|(b, _)| b.len())
            .unwrap_or(self.bases.len())
    }
    pub fn target(&self) -> Point {
        self.target
    }
    pub fn bases(&self) -> &[Point] {
        &self.bases
    }
    pub fn evaluate(&self, witness: &[S]) -> Result<Point> {
        if witness.len() != self.dimension() {
            return Err(Error("witness dimension".into()));
        }
        if let Some((bases, second)) = &self.paired_bases {
            let terms: Vec<(G1, S)> = bases.iter().zip(witness).map(|(g, s)| (*g, *s)).collect();
            return Ok(Point::GT(pair(sum1(&terms), *second)));
        }
        if matches!(self.target, Point::G2(_)) {
            let terms: Vec<_> = self
                .bases
                .iter()
                .zip(witness)
                .map(|(b, s)| {
                    let Point::G2(g) = *b else {
                        unreachable!("validated homogeneous relation")
                    };
                    (g, *s)
                })
                .collect();
            Ok(Point::G2(sum2(&terms)))
        } else {
            self.bases
                .iter()
                .zip(witness)
                .try_fold(self.target.identity(), |sum, (b, s)| sum.add(b.mul(*s)))
        }
    }
    pub fn check(&self, witness: &[S]) -> bool {
        self.evaluate(witness)
            .map(|x| x == self.target)
            .unwrap_or(false)
    }
    fn opening_evaluate(&self, opening: &[S]) -> Result<Point> {
        if opening.len() != self.dimension() + 1 {
            return Err(Error("opening dimension".into()));
        }
        self.evaluate(&opening[..self.dimension()])?
            .add(self.target.mul(-opening[self.dimension()]))
    }
    fn same_group(&self, p: Point) -> bool {
        p.kind() == self.target.kind() && p.valid()
    }
    fn same_group_received(&self, p: Point, decoded: bool) -> bool {
        p.kind() == self.target.kind() && p.domain_valid() && (decoded || p.valid())
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(b"CDM-relation-v1");
        self.target.write(&mut w);
        w.u8(if self.paired_bases.is_some() { 1 } else { 0 });
        w.u32(self.dimension() as u32);
        if let Some((bases, second)) = &self.paired_bases {
            w.g2(*second);
            for b in bases {
                w.g1(*b);
            }
        } else {
            for b in &self.bases {
                b.write(&mut w);
            }
        }
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, b"CDM-relation-v1")?;
        let target = Point::read(&mut r)?;
        let representation = r.u8()?;
        let n = read_count(&mut r, MAX_WITNESSES)?;
        if representation == 1 {
            let second = r.g2(true)?;
            let bases = (0..n).map(|_| r.g1(false)).collect::<Result<Vec<_>>>()?;
            r.finish()?;
            return match target {
                Point::GT(g) => Self::pairing_g1(bases, second, g),
                _ => Err(Error("pairing target group".into())),
            };
        }
        if representation != 0 {
            return Err(Error("homomorphism representation".into()));
        }
        let bases = (0..n)
            .map(|_| Point::read(&mut r))
            .collect::<Result<Vec<_>>>()?;
        r.finish()?;
        Self::new(bases, target)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VFirst {
    pub commitment: Point,
    pub opening_first: Point,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PFirst {
    pub opening_challenge: S,
    pub true_first: Point,
    pub opening_or_first: Point,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VThird {
    pub opening_responses: Vec<S>,
    pub or_challenge: S,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PFourth {
    pub true_challenge: S,
    pub true_responses: Vec<S>,
    pub opening_responses: Vec<S>,
}

fn write_scalars(w: &mut Writer, x: &[S]) {
    w.u32(x.len() as u32);
    for v in x {
        w.fr(*v);
    }
}
fn read_count(r: &mut Reader<'_>, max: usize) -> Result<usize> {
    let n = r.u32()? as usize;
    if n == 0 || n > max {
        Err(Error("vector count".into()))
    } else {
        Ok(n)
    }
}
fn read_scalars(r: &mut Reader<'_>, max: usize) -> Result<Vec<S>> {
    let n = read_count(r, max)?;
    (0..n).map(|_| r.fr()).collect()
}
impl VFirst {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(b"CDM-V1-v1");
        self.commitment.write(&mut w);
        self.opening_first.write(&mut w);
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, b"CDM-V1-v1")?;
        let commitment = Point::read(&mut r)?;
        let opening_first = Point::read(&mut r)?;
        r.finish()?;
        Ok(Self {
            commitment,
            opening_first,
        })
    }
}
impl PFirst {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(b"CDM-P2-v1");
        w.fr(self.opening_challenge);
        self.true_first.write(&mut w);
        self.opening_or_first.write(&mut w);
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, b"CDM-P2-v1")?;
        let opening_challenge = r.fr()?;
        let true_first = Point::read(&mut r)?;
        let opening_or_first = Point::read(&mut r)?;
        r.finish()?;
        Ok(Self {
            opening_challenge,
            true_first,
            opening_or_first,
        })
    }
}
impl VThird {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(b"CDM-V3-v1");
        write_scalars(&mut w, &self.opening_responses);
        w.fr(self.or_challenge);
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, b"CDM-V3-v1")?;
        let opening_responses = read_scalars(&mut r, MAX_WITNESSES + 1)?;
        let or_challenge = r.fr()?;
        r.finish()?;
        Ok(Self {
            opening_responses,
            or_challenge,
        })
    }
}
impl PFourth {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new(b"CDM-P4-v1");
        w.fr(self.true_challenge);
        write_scalars(&mut w, &self.true_responses);
        write_scalars(&mut w, &self.opening_responses);
        w.finish()
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = Reader::new(bytes, b"CDM-P4-v1")?;
        let true_challenge = r.fr()?;
        let true_responses = read_scalars(&mut r, MAX_WITNESSES)?;
        let opening_responses = read_scalars(&mut r, MAX_WITNESSES + 1)?;
        r.finish()?;
        Ok(Self {
            true_challenge,
            true_responses,
            opening_responses,
        })
    }
}

/// These states are consumed at the next move; they cannot be cloned or reused.
pub struct VerifierAwaitFirst {
    relation: Relation,
    first: VFirst,
    opening: Vec<S>,
    opening_nonce: Vec<S>,
}
pub struct VerifierAwaitFourth {
    relation: Relation,
    first: VFirst,
    prover_first: PFirst,
    challenge: S,
}
pub struct ProverAwaitThird {
    relation: Relation,
    first: VFirst,
    opening_challenge: S,
    witness: Vec<S>,
    true_nonce: Vec<S>,
    simulated_challenge: S,
    simulated_responses: Vec<S>,
}
/// One-use prover work that depends only on the already fixed relation and
/// witness. The simulated branch is not bound to a fresh verifier commitment.
pub struct PreparedProver {
    relation: Relation,
    opening_challenge: S,
    witness: Vec<S>,
    true_nonce: Vec<S>,
    simulated_challenge: S,
    simulated_responses: Vec<S>,
    true_first: Point,
    simulated_opening_base: Point,
}

fn scalars<R: RngCore + CryptoRng>(n: usize, rng: &mut R) -> Vec<S> {
    (0..n).map(|_| random_scalar(rng)).collect()
}

/// Move 1: the verifier commits a challenge and starts proving an opening.
pub fn verifier_begin<R: RngCore + CryptoRng>(
    relation: &Relation,
    rng: &mut R,
) -> Result<(VerifierAwaitFirst, VFirst)> {
    let opening = scalars(relation.dimension() + 1, rng);
    let opening_nonce = scalars(relation.dimension() + 1, rng);
    let first = VFirst {
        commitment: relation.opening_evaluate(&opening)?,
        opening_first: relation.opening_evaluate(&opening_nonce)?,
    };
    Ok((
        VerifierAwaitFirst {
            relation: relation.clone(),
            first: first.clone(),
            opening,
            opening_nonce,
        },
        first,
    ))
}

/// Move 2 contains only fresh commitments and a simulated opening branch.
pub fn prover_begin<R: RngCore + CryptoRng>(
    relation: &Relation,
    witness: &[S],
    first: &VFirst,
    rng: &mut R,
) -> Result<(ProverAwaitThird, PFirst)> {
    prover_begin_inner(relation, witness, first, rng, false)
}
/// Called immediately after VFirst::decode within one protocol execution.
pub(crate) fn prover_begin_decoded<R: RngCore + CryptoRng>(
    relation: &Relation,
    witness: &[S],
    first: &VFirst,
    rng: &mut R,
) -> Result<(ProverAwaitThird, PFirst)> {
    prover_begin_inner(relation, witness, first, rng, true)
}
fn prover_begin_inner<R: RngCore + CryptoRng>(
    relation: &Relation,
    witness: &[S],
    first: &VFirst,
    rng: &mut R,
    decoded: bool,
) -> Result<(ProverAwaitThird, PFirst)> {
    if !relation.same_group_received(first.commitment, decoded)
        || !relation.same_group_received(first.opening_first, decoded)
    {
        return Err(Error("verifier first message".into()));
    }
    // The received points were checked above, before sampling prover coins.
    prover_bind_inner(prover_prepare(relation, witness, rng)?, first, true)
}
/// Evaluate the true branch and fixed simulated-branch homomorphism before
/// receiving VFirst. The resulting object is consumed by one native session.
pub fn prover_prepare<R: RngCore + CryptoRng>(
    relation: &Relation,
    witness: &[S],
    rng: &mut R,
) -> Result<PreparedProver> {
    if witness.len() != relation.dimension() {
        return Err(Error("relation witness dimension".into()));
    }
    let opening_challenge = random_scalar(rng);
    let true_nonce = scalars(relation.dimension(), rng);
    let simulated_challenge = random_scalar(rng);
    let simulated_responses = scalars(relation.dimension() + 1, rng);
    let true_first = relation.evaluate(&true_nonce)?;
    let simulated_opening_base = relation.opening_evaluate(&simulated_responses)?;
    Ok(PreparedProver {
        relation: relation.clone(),
        opening_challenge,
        witness: witness.to_vec(),
        true_nonce,
        simulated_challenge,
        simulated_responses,
        true_first,
        simulated_opening_base,
    })
}
/// Complete only the term depending on the verifier's fresh commitment.
pub fn prover_bind(prepared: PreparedProver, first: &VFirst) -> Result<(ProverAwaitThird, PFirst)> {
    prover_bind_inner(prepared, first, false)
}
/// Called immediately after VFirst::decode within the same native exchange.
pub(crate) fn prover_bind_decoded(
    prepared: PreparedProver,
    first: &VFirst,
) -> Result<(ProverAwaitThird, PFirst)> {
    prover_bind_inner(prepared, first, true)
}
fn prover_bind_inner(
    prepared: PreparedProver,
    first: &VFirst,
    decoded: bool,
) -> Result<(ProverAwaitThird, PFirst)> {
    if !prepared
        .relation
        .same_group_received(first.commitment, decoded)
        || !prepared
            .relation
            .same_group_received(first.opening_first, decoded)
    {
        return Err(Error("verifier first message".into()));
    }
    let pfirst = PFirst {
        opening_challenge: prepared.opening_challenge,
        true_first: prepared.true_first,
        opening_or_first: prepared
            .simulated_opening_base
            .add(first.commitment.mul(-prepared.simulated_challenge))?,
    };
    let state = ProverAwaitThird {
        relation: prepared.relation,
        first: first.clone(),
        opening_challenge: prepared.opening_challenge,
        witness: prepared.witness,
        true_nonce: prepared.true_nonce,
        simulated_challenge: prepared.simulated_challenge,
        simulated_responses: prepared.simulated_responses,
    };
    Ok((state, pfirst))
}

/// Move 3 completes the verifier's opening proof and challenges the OR proof.
pub fn verifier_challenge<R: RngCore + CryptoRng>(
    state: VerifierAwaitFirst,
    first: PFirst,
    rng: &mut R,
) -> Result<(VerifierAwaitFourth, VThird)> {
    verifier_challenge_inner(state, first, rng, false)
}
/// Called immediately after PFirst::decode within one protocol execution.
pub(crate) fn verifier_challenge_decoded<R: RngCore + CryptoRng>(
    state: VerifierAwaitFirst,
    first: PFirst,
    rng: &mut R,
) -> Result<(VerifierAwaitFourth, VThird)> {
    verifier_challenge_inner(state, first, rng, true)
}
fn verifier_challenge_inner<R: RngCore + CryptoRng>(
    state: VerifierAwaitFirst,
    first: PFirst,
    rng: &mut R,
    decoded: bool,
) -> Result<(VerifierAwaitFourth, VThird)> {
    if !state
        .relation
        .same_group_received(first.true_first, decoded)
        || !state
            .relation
            .same_group_received(first.opening_or_first, decoded)
    {
        return Err(Error("prover first message".into()));
    }
    let responses = {
        state
            .opening_nonce
            .iter()
            .zip(&state.opening)
            .map(|(r, w)| *r + first.opening_challenge * w)
            .collect()
    };
    let challenge = random_scalar(rng);
    let third = VThird {
        opening_responses: responses,
        or_challenge: challenge,
    };
    Ok((
        VerifierAwaitFourth {
            relation: state.relation,
            first: state.first,
            prover_first: first,
            challenge,
        },
        third,
    ))
}

/// Input-only shape checks after strict decoding; no proof-verification equations.
pub(crate) fn decode_prover_first(state: &VerifierAwaitFirst, bytes: &[u8]) -> Result<PFirst> {
    let first = PFirst::decode(bytes)?;
    if !state.relation.same_group_received(first.true_first, true)
        || !state
            .relation
            .same_group_received(first.opening_or_first, true)
    {
        return Err(Error("prover first message group kind".into()));
    }
    Ok(first)
}
pub(crate) fn decode_prover_fourth(state: &VerifierAwaitFourth, bytes: &[u8]) -> Result<PFourth> {
    let last = PFourth::decode(bytes)?;
    let n = state.relation.dimension();
    if last.true_responses.len() != n || last.opening_responses.len() != n + 1 {
        return Err(Error("prover final response dimension".into()));
    }
    Ok(last)
}
/// An invalid verifier proof aborts before a witness-dependent response exists.
pub fn prover_respond(state: ProverAwaitThird, third: VThird) -> Result<PFourth> {
    let left = state.relation.opening_evaluate(&third.opening_responses)?;
    let right = state
        .first
        .opening_first
        .add(state.first.commitment.mul(state.opening_challenge))?;
    if left != right {
        return Err(Error("verifier opening proof".into()));
    }
    let (true_challenge, true_responses) = {
        let true_challenge = third.or_challenge - state.simulated_challenge;
        let true_responses = state
            .true_nonce
            .iter()
            .zip(&state.witness)
            .map(|(r, w)| *r + true_challenge * w)
            .collect();
        (true_challenge, true_responses)
    };
    Ok(PFourth {
        true_challenge,
        true_responses,
        opening_responses: state.simulated_responses,
    })
}

pub fn verifier_finish(state: VerifierAwaitFourth, last: PFourth) -> bool {
    let simulated_challenge = state.challenge - last.true_challenge;
    let true_left = match state.relation.evaluate(&last.true_responses) {
        Ok(v) => v,
        Err(_) => return false,
    };
    let true_right = match state
        .prover_first
        .true_first
        .add(state.relation.target.mul(last.true_challenge))
    {
        Ok(v) => v,
        Err(_) => return false,
    };
    let sim_left = match state.relation.opening_evaluate(&last.opening_responses) {
        Ok(v) => v,
        Err(_) => return false,
    };
    let sim_right = match state
        .prover_first
        .opening_or_first
        .add(state.first.commitment.mul(simulated_challenge))
    {
        Ok(v) => v,
        Err(_) => return false,
    };
    true_left == true_right && sim_left == sim_right
}

/// Check all paired-homomorphism residuals only after complete live verifier
/// states and final responses have been fixed. The four native messages and
/// the verifier's private challenge remain unchanged. Non-pairing G2 and
/// generic GT relations retain their exact native checks.
pub fn verifier_finish_profile(
    state: VerifierAwaitFourth,
    last: PFourth,
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    verifier_finish_many_profile(vec![(state, last)], mode, rng)
}

/// Combine eligible final checks across completed independent interactions.
/// Earlier verifier-opening checks remain at their native causal stage.
pub fn verifier_finish_many_profile(
    sessions: Vec<(VerifierAwaitFourth, PFourth)>,
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    verifier_finish_many_inner(sessions, mode, false, rng)
}
/// Private continuation: every group field comes from sealed received messages
/// or the installed local relation; no untrusted typed input reaches this call.
pub(crate) fn verifier_finish_many_checked(
    sessions: Vec<(VerifierAwaitFourth, PFourth)>,
    mode: VerificationMode,
    rng: &mut impl RngCore,
) -> bool {
    verifier_finish_many_inner(sessions, mode, true, rng)
}
fn verifier_finish_many_inner(
    sessions: Vec<(VerifierAwaitFourth, PFourth)>,
    mode: VerificationMode,
    checked: bool,
    rng: &mut impl RngCore,
) -> bool {
    if sessions.is_empty() {
        return false;
    }
    if mode == VerificationMode::Specification {
        return sessions
            .into_iter()
            .all(|(state, last)| verifier_finish(state, last));
    }
    let mut equations = Vec::new();
    for (state, last) in sessions {
        let Some(next) = finish_equations(&state, &last) else {
            return false;
        };
        equations.extend(next);
    }
    equations.is_empty()
        || if checked {
            pairing_verify::verify_checked(&equations, mode, rng)
        } else {
            pairing_verify::verify(&equations, mode, rng)
        }
}

fn copied_public_state(state: &VerifierAwaitFourth) -> VerifierAwaitFourth {
    VerifierAwaitFourth {
        relation: state.relation.clone(),
        first: state.first.clone(),
        prover_first: state.prover_first.clone(),
        challenge: state.challenge,
    }
}

fn finish_equations(state: &VerifierAwaitFourth, last: &PFourth) -> Option<Vec<Equation>> {
    let n = state.relation.dimension();
    if last.true_responses.len() != n || last.opening_responses.len() != n + 1 {
        return None;
    }
    let Some((bases, second)) = state.relation.paired_bases.as_ref() else {
        return verifier_finish(copied_public_state(state), last.clone()).then(Vec::new);
    };
    let Point::GT(target) = state.relation.target else {
        return None;
    };
    let Point::GT(true_first) = state.prover_first.true_first else {
        return None;
    };
    let Point::GT(opening_first) = state.prover_first.opening_or_first else {
        return None;
    };
    let Point::GT(commitment) = state.first.commitment else {
        return None;
    };
    let true_sum = sum1(
        &bases
            .iter()
            .zip(&last.true_responses)
            .map(|(g, s)| (*g, *s))
            .collect::<Vec<_>>(),
    );
    let opening_sum = sum1(
        &bases
            .iter()
            .zip(&last.opening_responses[..n])
            .map(|(g, s)| (*g, *s))
            .collect::<Vec<_>>(),
    );
    Some(vec![
        Equation {
            terms: vec![(true_sum, *second)],
            target: gt_add(true_first, gt_mul(target, last.true_challenge)),
        },
        Equation {
            terms: vec![(opening_sum, *second)],
            target: gt_add(
                gt_add(
                    opening_first,
                    gt_mul(commitment, state.challenge - last.true_challenge),
                ),
                gt_mul(target, last.opening_responses[n]),
            ),
        },
    ])
}

/// Immutable public verification material from an actual completed live
/// session. It contains no prover nonce or verifier opening secret. Rechecking
/// a fixed response is distinct from reusing an interactive prover state.
pub struct FrozenVerifier {
    state: VerifierAwaitFourth,
}
impl Clone for FrozenVerifier {
    fn clone(&self) -> Self {
        Self {
            state: copied_public_state(&self.state),
        }
    }
}
impl FrozenVerifier {
    pub(crate) fn from_live(state: VerifierAwaitFourth) -> Self {
        Self { state }
    }
    pub fn verify(&self, last: PFourth, mode: VerificationMode, rng: &mut impl RngCore) -> bool {
        verifier_finish_profile(copied_public_state(&self.state), last, mode, rng)
    }
    pub(crate) fn equations(&self, last: &PFourth) -> Option<Vec<Equation>> {
        finish_equations(&self.state, last)
    }
}

/// A complete interaction; all four messages can be encoded independently.
pub fn prove<R: RngCore + CryptoRng>(
    relation: &Relation,
    witness: &[S],
    rng: &mut R,
) -> Result<(VFirst, PFirst, VThird, PFourth)> {
    let (vs, v1) = verifier_begin(relation, rng)?;
    let (ps, p2) = prover_begin(relation, witness, &v1, rng)?;
    let (vs, v3) = verifier_challenge(vs, p2.clone(), rng)?;
    let p4 = prover_respond(ps, v3.clone())?;
    if !verifier_finish(vs, p4.clone()) {
        return Err(Error("proof verification".into()));
    }
    Ok((v1, p2, v3, p4))
}

/// Checks the equations of a complete transcript for the fixed public relation.
/// Live acceptance uses the consumed verifier state, rather than this function.
pub fn transcript_valid(
    relation: &Relation,
    v1: &VFirst,
    p2: &PFirst,
    v3: &VThird,
    p4: &PFourth,
) -> bool {
    if !relation.same_group(v1.commitment)
        || !relation.same_group(v1.opening_first)
        || !relation.same_group(p2.true_first)
        || !relation.same_group(p2.opening_or_first)
    {
        return false;
    }
    let l = match relation.opening_evaluate(&v3.opening_responses) {
        Ok(v) => v,
        Err(_) => return false,
    };
    let r = match v1
        .opening_first
        .add(v1.commitment.mul(p2.opening_challenge))
    {
        Ok(v) => v,
        Err(_) => return false,
    };
    if l != r {
        return false;
    }
    verifier_finish(
        VerifierAwaitFourth {
            relation: relation.clone(),
            first: v1.clone(),
            prover_first: p2.clone(),
            challenge: v3.or_challenge,
        },
        p4.clone(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::g1_mul;
    use rand::{rngs::StdRng, SeedableRng};

    fn complete(relation: &Relation, witness: &[S], decoded: bool) -> Vec<Vec<u8>> {
        let mut rng = StdRng::seed_from_u64(121020911);
        let (vs, v1) = verifier_begin(relation, &mut rng).unwrap();
        let received_v1 = VFirst::decode(&v1.encode()).unwrap();
        let (ps, p2) = if decoded {
            prover_begin_decoded(relation, witness, &received_v1, &mut rng).unwrap()
        } else {
            prover_begin(relation, witness, &received_v1, &mut rng).unwrap()
        };
        let received_p2 = PFirst::decode(&p2.encode()).unwrap();
        let (vs, v3) = if decoded {
            verifier_challenge_decoded(vs, received_p2, &mut rng).unwrap()
        } else {
            verifier_challenge(vs, received_p2, &mut rng).unwrap()
        };
        let p4 = prover_respond(ps, VThird::decode(&v3.encode()).unwrap()).unwrap();
        assert!(verifier_finish(vs, PFourth::decode(&p4.encode()).unwrap()));
        vec![v1.encode(), p2.encode(), v3.encode(), p4.encode()]
    }

    #[test]
    fn trusted_received_entries_preserve_all_four_bytes() {
        let w = [S::from(7), S::from(11), S::from(13)];
        let bases2: Vec<_> = [2, 3, 5]
            .iter()
            .map(|&x| g2_mul(G2::generator(), S::from(x)))
            .collect();
        let target2 = bases2
            .iter()
            .zip(w)
            .fold(G2::identity(), |s, (g, v)| g2_add(s, g2_mul(*g, v)));
        let checked2 = Relation::g2(bases2.clone(), target2).unwrap();
        let trusted2 = Relation::g2_trusted(bases2, target2).unwrap();
        assert_eq!(checked2, trusted2);
        assert_eq!(
            complete(&checked2, &w, false),
            complete(&trusted2, &w, true)
        );

        let bases1: Vec<_> = [2, 3, 5]
            .iter()
            .map(|&x| g1_mul(G1::generator(), S::from(x)))
            .collect();
        let second = g2_mul(G2::generator(), S::from(19));
        let target = pair(
            sum1(
                &bases1
                    .iter()
                    .zip(w)
                    .map(|(g, v)| (*g, v))
                    .collect::<Vec<_>>(),
            ),
            second,
        );
        let checked = Relation::pairing_g1(bases1.clone(), second, target).unwrap();
        let trusted = Relation::pairing_g1_trusted(bases1, second, target).unwrap();
        assert_eq!(checked, trusted);
        assert_eq!(complete(&checked, &w, false), complete(&trusted, &w, true));

        assert!(Relation::g2_trusted(vec![], target2).is_err());
        assert!(Relation::g2_trusted(vec![G2::identity()], target2).is_err());
        assert!(
            Relation::pairing_g1_trusted(vec![G1::generator()], G2::identity(), target).is_err()
        );
        assert!(
            Relation::pairing_g1_trusted(vec![G1::generator()], second, GT::default()).is_err()
        );
    }

    #[test]
    fn public_typed_entries_keep_offcurve_and_subgroup_checks() {
        let p = G2::generator();
        let offcurve = G2::from_raw_unchecked(p.x(), p.y() + p.z(), p.z());
        assert!(!bool::from(offcurve.is_on_curve()));
        let subgroup_bad = (1u64..10000)
            .find_map(|x| {
                let mut b = [0u8; 96];
                b[0] = 0x80;
                b[88..].copy_from_slice(&x.to_be_bytes());
                Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed_unchecked(&b))
                    .filter(|g| !bool::from(g.is_torsion_free()))
                    .map(G2::from)
            })
            .unwrap();
        for bad in [offcurve, subgroup_bad] {
            assert!(Relation::g2(vec![bad], p).is_err());
            assert!(Relation::g2(vec![p], bad).is_err());
            let relation = Relation::g2(vec![p], g2_mul(p, S::from(7))).unwrap();
            let mut rng = StdRng::seed_from_u64(121020913);
            let (vs, mut v1) = verifier_begin(&relation, &mut rng).unwrap();
            v1.commitment = Point::G2(bad);
            assert!(prover_begin(&relation, &[S::from(7)], &v1, &mut rng).is_err());
            let (_, v1) = verifier_begin(&relation, &mut rng).unwrap();
            let (_, mut p2) = prover_begin(&relation, &[S::from(7)], &v1, &mut rng).unwrap();
            p2.true_first = Point::G2(bad);
            assert!(verifier_challenge(vs, p2, &mut rng).is_err());
        }
    }
}
