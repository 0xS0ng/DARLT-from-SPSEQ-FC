//! DARLT one-child tokens, offline double Caulk and vector shared witnesses.
use super::recovery;
use super::{
    caulk,
    protocol::{self, Holder, IssuerPublic, PublicParameters},
    sigma::{self, Eq1, Statement},
    verification::{self, Mode},
};
use crate::{common::crypto, polynomial::S, spseq_fc};
use blstrs::G1Projective as G1;
use ff::Field;
use group::Group;
use rand::RngCore;
use sha2::Digest;
use std::{borrow::Cow, collections::BTreeSet};
pub type Result<T> = std::result::Result<T, String>;
#[derive(Clone, Debug)]
pub enum Atom {
    Reveal(usize, S),
    Equal(usize, S),
    Linear(Vec<(usize, S)>, S),
    Range(usize, u64, u64),
}
#[derive(Clone, Debug)]
pub struct Policy {
    pub period: u64,
    pub atoms: Vec<Atom>,
}
impl Policy {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = self.period.to_be_bytes().to_vec();
        b.extend((self.atoms.len() as u64).to_be_bytes());
        for a in &self.atoms {
            match a {
                Atom::Reveal(i, v) | Atom::Equal(i, v) => {
                    b.push(if matches!(a, Atom::Reveal(..)) { 0 } else { 1 });
                    b.extend((*i as u64).to_be_bytes());
                    b.extend(v.to_bytes_be());
                }
                Atom::Linear(ts, v) => {
                    b.push(2);
                    b.extend((ts.len() as u64).to_be_bytes());
                    for (i, c) in ts {
                        b.extend((*i as u64).to_be_bytes());
                        b.extend(c.to_bytes_be());
                    }
                    b.extend(v.to_bytes_be());
                }
                Atom::Range(i, l, h) => {
                    b.push(3);
                    for x in [*i as u64, *l, *h] {
                        b.extend(x.to_be_bytes());
                    }
                }
            }
        }
        b
    }
}

#[derive(Clone, Debug)]
pub struct Authentication {
    pub message: Vec<G1>,
    pub signature: spseq_fc::Sig,
}
impl Authentication {
    pub fn message(&self) -> &[G1] {
        &self.message
    }
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = vec![];
        for p in &self.message {
            b.extend(p.to_compressed());
        }
        b.extend(self.signature.encode());
        b
    }
}
#[derive(Clone, Debug)]
pub struct Unit {
    pub sn: G1,
    pub aid: G1,
    pub tu: G1,
    pub ta: G1,
}
#[derive(Clone, Debug)]
pub struct Token {
    pub auth: Authentication,
    pub scope: G1,
    pub offset_table: G1,
    pub commitments: [G1; 3],
    pub seed_query: G1,
    pub units: Vec<Unit>,
    pub lookups: Vec<caulk::Proof>,
    pub range_commitments: Vec<G1>,
    pub proof: sigma::Proof,
    pub policy: Policy,
    pub context: Vec<u8>,
}
/// Immutable received token. Only the complete strict wire parser can issue
/// this provenance; callers cannot mutate its checked group elements.
#[derive(Clone, Debug)]
pub struct ReceivedToken {
    token: Token,
    inputs: ReceivedInputs,
}
/// Capability for internal algorithms whose inputs are checked received
/// points, installed public material, or arithmetic derived from those points.
/// Its fields remain private. Receipt provenance can additionally be issued
/// only from the protocol module's private strict-decoder seal.
#[derive(Clone, Debug)]
pub(crate) struct ReceivedInputs {
    parameter_id: [u8; 32],
}
impl ReceivedInputs {
    pub(super) fn from_receipt(seal: &super::protocol::CheckedReceipt) -> Self {
        Self {
            parameter_id: seal.parameter_id(),
        }
    }
    pub(crate) fn matches_parameters(&self, id: &[u8; 32]) -> bool {
        self.parameter_id == *id
    }
}
impl ReceivedToken {
    #[cfg(test)]
    pub(crate) fn native_equations_match(&self, pp: &PublicParameters, ip: &IssuerPublic) -> bool {
        let raw = checked_equations(pp, ip, &self.token);
        let received = checked_equations_impl(pp, ip, &self.token, Some(&self.inputs));
        raw.is_ok() && raw == received
    }
    pub fn token(&self) -> &Token {
        &self.token
    }
    pub fn wire_encode(&self) -> Vec<u8> {
        self.token.wire_encode()
    }
    pub fn serials(&self) -> Vec<[u8; 48]> {
        self.token.serials()
    }
    pub fn wire_decode(pp: &PublicParameters, bytes: &[u8]) -> Result<Self> {
        Ok(Self {
            token: Token::wire_decode(pp, bytes)?,
            inputs: ReceivedInputs {
                parameter_id: pp.id,
            },
        })
    }
}
impl Token {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn serials(&self) -> Vec<[u8; 48]> {
        self.units.iter().map(|u| u.sn.to_compressed()).collect()
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn wire_encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = vec![21];
        crypto::frame(&mut b, &self.auth.encode());
        for g in [self.scope, self.offset_table] {
            b.extend(g.to_compressed());
        }
        for g in self.commitments {
            b.extend(g.to_compressed());
        }
        b.extend(self.seed_query.to_compressed());
        b.extend((self.units.len() as u64).to_be_bytes());
        for u in &self.units {
            for g in [u.sn, u.aid, u.tu, u.ta] {
                b.extend(g.to_compressed());
            }
        }
        for p in &self.lookups {
            b.extend(p.to_bytes());
        }
        crypto::points1(&mut b, &self.range_commitments);
        crypto::frame(&mut b, &self.proof.encode());
        crypto::frame(&mut b, &self.policy.encode());
        crypto::frame(&mut b, &self.context);
        b
    }
}
#[derive(Clone, Debug)]
struct UnitSecret {
    x1: S,
    x2: S,
    x3: S,
    eta: S,
}
#[derive(Clone, Debug)]
struct UnitHashes {
    h1: G1,
    h3: G1,
    c: S,
}
#[derive(Clone, Debug)]
struct Auxiliary {
    mu: S,
    vector_rhos: [S; 3],
    q: S,
    link_rho: S,
    chi: S,
    range_values: Vec<S>,
    range_blinds: Vec<S>,
    units: Vec<UnitSecret>,
    hashes: Vec<UnitHashes>,
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn hash_payload(pp: &PublicParameters, ip: &IssuerPublic, parts: &[&[u8]]) -> Vec<u8> {
    let mut b = protocol::prefix(pp, ip);
    for p in parts {
        crypto::frame(&mut b, p);
    }
    b
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn hscalar(pp: &PublicParameters, ip: &IssuerPublic, label: &[u8], parts: &[&[u8]]) -> S {
    crypto::hash_scalar(label, &hash_payload(pp, ip, parts))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn hpoint(pp: &PublicParameters, ip: &IssuerPublic, label: &[u8], parts: &[&[u8]]) -> G1 {
    crypto::hash_point(label, &hash_payload(pp, ip, parts))
}
/// Exactly the H_col prefix: no context, policy, T_a, or lookup proof.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn outer0(pp: &PublicParameters, ip: &IssuerPublic, t: &Token) -> Vec<u8> {
    let _span = crate::darlt::instrumentation::span("fiat_shamir_transcript");
    let mut b = protocol::prefix(pp, ip);
    b.extend(b"FC/Spend/H_col/merge");
    b.extend((t.units.len() as u64).to_be_bytes());
    crypto::frame(&mut b, &t.auth.encode());
    for g in [t.scope, t.offset_table] {
        b.extend(g.to_compressed());
    }
    for g in t.commitments {
        b.extend(g.to_compressed());
    }
    for u in &t.units {
        for g in [u.sn, u.aid, u.tu] {
            b.extend(g.to_compressed());
        }
    }
    b
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn lookup_prefix(tr0: &[u8], lambda: S, role: usize) -> Vec<u8> {
    let mut b = tr0.to_vec();
    b.extend(b"Caulk/lookup/role-bound");
    b.extend(lambda.to_bytes_be());
    b.extend((role as u64).to_be_bytes());
    b
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn alpha_prefix(tr0: &[u8], lambda: S, t: &Token) -> Vec<u8> {
    let _span = crate::darlt::instrumentation::span("fiat_shamir_transcript");
    let mut b = tr0.to_vec();
    b.extend(lambda.to_bytes_be());
    b.extend(t.seed_query.to_compressed());
    for p in &t.lookups {
        b.extend(p.to_bytes());
    }
    crypto::frame(&mut b, &t.context);
    crypto::frame(&mut b, &t.policy.encode());
    for u in &t.units {
        b.extend(u.ta.to_compressed());
    }
    b
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn caulk_view(pp: &PublicParameters) -> caulk::CaulkView<'_> {
    caulk::CaulkView {
        domain: &pp.srs.domain,
        n: pp.srs.n,
        degree: pp.srs.degree,
        g1: &pp.srs.g1,
        g2: &pp.srs.g2,
    }
}
#[derive(Clone, Debug)]
struct Layout {
    known: Vec<Option<S>>,
    referenced: Vec<bool>,
    private: bool,
    ranges: Vec<(usize, u64, u64)>,
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn layout(pp: &PublicParameters, p: &Policy) -> Result<Layout> {
    let count = pp.k_del + pp.k_prv;
    let mut out = Layout {
        known: vec![None; count],
        referenced: vec![false; count],
        private: false,
        ranges: vec![],
    };
    let mut period = false;
    for a in &p.atoms {
        match a {
            Atom::Reveal(i, v) | Atom::Equal(i, v) => {
                if *i >= count {
                    return Err("attribute index".into());
                }
                if out.known[*i].is_some_and(|x| x != *v) {
                    return Err("conflicting policy constants".into());
                }
                out.known[*i] = Some(*v);
                out.referenced[*i] = true;
                if matches!(a, Atom::Equal(0, _)) && *v == S::from(p.period) {
                    period = true;
                }
            }
            Atom::Linear(ts, _) => {
                for (i, c) in ts {
                    if *i >= count {
                        return Err("linear policy index".into());
                    }
                    if *c != S::ZERO {
                        out.referenced[*i] = true;
                    }
                }
            }
            Atom::Range(i, lo, hi) => {
                if *i >= count || lo > hi || *hi == u64::MAX {
                    return Err("range policy input".into());
                }
                out.referenced[*i] = true;
                if lo == hi {
                    let v = S::from(*lo);
                    if out.known[*i].is_some_and(|x| x != v) {
                        return Err("range/equality conflict".into());
                    }
                    out.known[*i] = Some(v);
                } else {
                    out.ranges.push((*i, *lo, *hi));
                }
            }
        }
    }
    if !period {
        return Err("missing period equality".into());
    }
    out.private = out.referenced[pp.k_del..].iter().any(|x| *x);
    Ok(out)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn scalar_u64(v: S) -> Result<u64> {
    let b = v.to_bytes_be();
    if b[..24].iter().any(|x| *x != 0) {
        return Err("range value outside u64".into());
    }
    Ok(u64::from_be_bytes(b[24..].try_into().unwrap()))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn bits_needed(lo: u64, hi: u64) -> usize {
    (64 - (hi - lo).leading_zeros()) as usize
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn weights(prefix: &[u8], k: usize) -> [Vec<S>; 4] {
    let _span = crate::darlt::instrumentation::span("fiat_shamir");
    std::array::from_fn(|equation| {
        (0..k)
            .map(|i| {
                let mut b = prefix.to_vec();
                b.extend((equation as u64).to_be_bytes());
                b.extend((i as u64).to_be_bytes());
                crypto::hash_scalar(b"H_unit/four-independent-vectors", &b)
            })
            .collect()
    })
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn sigma_external(alpha_prefix: &[u8], alpha: &[Vec<S>; 4]) -> Vec<u8> {
    let _span = crate::darlt::instrumentation::span("fiat_shamir_transcript");
    let mut b = alpha_prefix.to_vec();
    for row in alpha {
        crypto::scalars(&mut b, row);
    }
    b
}
struct Builder {
    statement: Statement,
    witness: Vec<S>,
}
impl Builder {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn new() -> Self {
        Self {
            statement: Statement::new(0),
            witness: vec![],
        }
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn variable(&mut self, v: S) -> usize {
        let i = self.witness.len();
        self.witness.push(v);
        self.statement.vars = self.witness.len();
        i
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn row(&mut self, target: G1, terms: Vec<(usize, G1, S)>) {
        self.statement.g1.push(Eq1 { target, terms });
    }
}
/// The first real query receives all padded-domain Lagrange bases. Power-of-two
/// queries borrow their installed bases without changing the formal-grid path.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn merged_query_bases(bases: &[G1], k: usize) -> Result<Cow<'_, [G1]>> {
    if k == 0 || bases.len() != k.next_power_of_two() {
        return Err("padded query base dimensions".into());
    }
    if bases.len() == k {
        return Ok(Cow::Borrowed(bases));
    }
    let mut merged = bases[..k].to_vec();
    merged[0] += bases[k..].iter().copied().sum::<G1>();
    Ok(Cow::Owned(merged))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn joint_statement(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
    lambda: S,
    alpha: &[Vec<S>; 4],
    holder: Option<&Holder>,
    aux: Option<&Auxiliary>,
) -> Result<(Statement, Vec<S>)> {
    joint_statement_impl(pp, ip, t, lambda, alpha, holder, aux, None)
}
#[allow(clippy::too_many_arguments)]
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn joint_statement_impl(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
    lambda: S,
    alpha: &[Vec<S>; 4],
    holder: Option<&Holder>,
    aux: Option<&Auxiliary>,
    received: Option<&ReceivedInputs>,
) -> Result<(Statement, Vec<S>)> {
    let l = layout(pp, &t.policy)?;
    let m = t.auth.message();
    let k = t.units.len();
    if k == 0 || k > pp.k_max || alpha.iter().any(|a| a.len() != k) || m.len() != 9 {
        return Err("record dimensions".into());
    }
    let present = holder.is_some();
    if present != aux.is_some() {
        return Err("missing prover auxiliary values".into());
    }
    let mut b = Builder::new();
    let mu = b.variable(aux.map_or(S::ZERO, |a| a.mu));
    let beta = b.variable(aux.map_or(S::ZERO, |a| {
        Option::<S>::from(a.mu.invert()).unwrap_or(S::ZERO)
    }));
    let ska = b.variable(holder.map_or(S::ZERO, |h| h.ska));
    let r = b.variable(holder.map_or(S::ZERO, |h| h.r));
    let rdel = b.variable(holder.map_or(S::ZERO, |h| h.rdel));
    b.row(m[0], vec![(mu, pp.fc.u, S::ONE)]);
    b.row(pp.fc.u, vec![(beta, m[0], S::ONE)]);
    let mut attributes = vec![S::ZERO; pp.k_del + pp.k_prv];
    if let Some(h) = holder {
        if h.mdel.len() != pp.k_del || h.delta.len() != pp.k_del {
            return Err("holder attribute shape".into());
        }
        attributes[..pp.k_del].copy_from_slice(&h.mdel);
        if l.private {
            let owner = h
                .owner
                .as_ref()
                .ok_or("agent cannot use private attributes")?;
            if owner.mprv.len() != pp.k_prv {
                return Err("owner attribute shape".into());
            }
            attributes[pp.k_del..].copy_from_slice(&owner.mprv);
        }
        for (i, value) in l.known.iter().enumerate() {
            if let Some(value) = value {
                if (i < pp.k_del || l.private) && attributes[i] != *value {
                    return Err("false known attribute".into());
                }
            }
        }
    }
    let mut attr_ids = vec![None; attributes.len()];
    for i in 0..attributes.len() {
        if (i < pp.k_del || l.private) && l.known[i].is_none() {
            attr_ids[i] = Some(b.variable(attributes[i]));
        }
    }
    let mut del_points = vec![];
    let mut del_values = vec![];
    let mut del_terms = vec![(beta, m[6], S::ONE), (rdel, pp.hdel, -S::ONE)];
    for (j, base) in pp.adel.iter().enumerate() {
        if let Some(v) = l.known[j] {
            del_points.push(*base);
            del_values.push(v);
        } else {
            del_terms.push((attr_ids[j].unwrap(), *base, -S::ONE));
        }
    }
    b.row(crate::ops::msm1(&del_points, &del_values), del_terms);
    let mut delta_ids = vec![None; pp.k_del];
    let mut known_grant_group = G1::identity();
    let mut known_aid_group = G1::identity();
    for (j, delta_id) in delta_ids.iter_mut().enumerate() {
        if l.referenced[j] {
            if holder.is_some_and(|h| !h.delta[j]) {
                return Err("policy refers to an ungranted attribute".into());
            }
            known_grant_group += pp.fc.attrs[j];
            known_aid_group += pp.grant_bases[j];
        } else {
            *delta_id = Some(b.variable(holder.map_or(S::ZERO, |h| S::from(h.delta[j] as u64))));
        }
    }
    let mut authorization_terms = vec![
        (beta, -t.scope, S::ONE),
        (r, -pp.fc.h0, S::ONE),
        (ska, -G1::generator(), S::ONE),
    ];
    authorization_terms.push((beta, m[8], S::ONE));
    for (j, id) in delta_ids.iter().enumerate() {
        if let Some(id) = id {
            authorization_terms.push((*id, -pp.fc.attrs[j], S::ONE));
        }
    }
    b.row(known_grant_group, authorization_terms);
    // Original conditional R_own: private attributes require the wallet owner.
    if l.private {
        let rprv = b.variable(
            holder
                .and_then(|h| h.owner.as_ref())
                .map_or(S::ZERO, |o| o.rprv),
        );
        let mut known_points = vec![];
        let mut known_values = vec![];
        let mut terms = vec![(beta, m[7], S::ONE), (rprv, -pp.hprv, S::ONE)];
        for (j, base) in pp.bprv.iter().enumerate() {
            let index = pp.k_del + j;
            if let Some(v) = l.known[index] {
                known_points.push(*base);
                known_values.push(v);
            } else {
                terms.push((attr_ids[index].unwrap(), -*base, S::ONE));
            }
        }
        b.row(crate::ops::msm1(&known_points, &known_values), terms);
        b.row(
            G1::identity(),
            vec![(beta, m[3], S::ONE), (ska, -G1::generator(), S::ONE)],
        );
    }
    // R_Pi: policy predicates share the commitment-opening responses.
    for atom in &t.policy.atoms {
        if let Atom::Linear(ts, target) = atom {
            let mut constant = -*target;
            let mut terms = vec![];
            for (i, c) in ts {
                if *c == S::ZERO {
                    continue;
                }
                if let Some(v) = l.known[*i] {
                    constant += *c * v;
                } else {
                    terms.push((
                        attr_ids[*i].ok_or("missing private linear attribute")?,
                        G1::generator(),
                        *c,
                    ));
                }
            }
            if present && ts.iter().map(|(i, c)| attributes[*i] * c).sum::<S>() != *target {
                return Err("false linear policy".into());
            }
            if terms.is_empty() {
                if constant != S::ZERO {
                    return Err("false constant linear policy".into());
                }
            } else {
                b.row(G1::generator() * -constant, terms);
            }
        }
    }
    let expected_ranges: usize = l
        .ranges
        .iter()
        .map(|(_, lo, hi)| 2 * bits_needed(*lo, *hi))
        .sum();
    if t.range_commitments.len() != expected_ranges {
        return Err("range commitment shape".into());
    }
    let mut range_index = 0;
    for (idx, lo, hi) in &l.ranges {
        if present {
            let value = scalar_u64(attributes[*idx])?;
            if value < *lo || value > *hi {
                return Err("false range policy".into());
            }
        }
        for side in 0..2 {
            let mut range_points = vec![];
            let mut range_powers = vec![];
            let mut terms = vec![];
            let mut power = S::ONE;
            for _ in 0..bits_needed(*lo, *hi) {
                let bit = aux.map_or(S::ZERO, |a| a.range_values[range_index]);
                let blind = aux.map_or(S::ZERO, |a| a.range_blinds[range_index]);
                let var = b.variable(bit);
                let blind_var = b.variable(blind);
                let commitment = t.range_commitments[range_index];
                b.statement.bits.push(sigma::BitRelation {
                    var,
                    blind_var,
                    g: G1::generator(),
                    h: pp.h,
                    commitment,
                });
                range_points.push(commitment);
                range_powers.push(power);
                terms.push((blind_var, pp.h, power));
                power = power + power;
                range_index += 1;
            }
            let sign = if side == 0 { S::ONE } else { -S::ONE };
            let offset = if side == 0 {
                S::from(*lo)
            } else {
                -S::from(*hi)
            };
            range_points.push(G1::generator());
            range_powers.push(offset);
            let mut target = crate::ops::msm1(&range_points, &range_powers);
            if let Some(value) = l.known[*idx] {
                target -= G1::generator() * (sign * value);
            } else {
                terms.push((attr_ids[*idx].unwrap(), G1::generator(), sign));
            }
            b.row(target, terms);
        }
    }
    let mut unit_ids = Vec::new();
    for index in 0..k {
        let secret = aux.map(|a| &a.units[index]);
        unit_ids.push([
            b.variable(secret.map_or(S::ZERO, |u| u.x1)),
            b.variable(secret.map_or(S::ZERO, |u| u.x2)),
            b.variable(secret.map_or(S::ZERO, |u| u.x3)),
            b.variable(secret.map_or(S::ZERO, |u| u.eta)),
        ]);
    }
    let (bases, vanishing) = pp.query_basis(k.next_power_of_two())?;
    let merged = merged_query_bases(&bases, k)?;
    for (d, commitment) in t.commitments.iter().enumerate() {
        let blind = b.variable(aux.map_or(S::ZERO, |a| a.vector_rhos[d]));
        let mut terms = vec![(blind, vanishing, S::ONE)];
        for t in 0..k {
            terms.push((unit_ids[t][d], merged[t], S::ONE));
        }
        b.row(*commitment, terms);
    }
    let q = b.variable(aux.map_or(S::ZERO, |a| a.q));
    let mut terms = vec![(beta, t.commitments[1], S::ONE), (q, vanishing, -S::ONE)];
    for t in 0..k {
        terms.push((unit_ids[t][3], merged[t], -S::ONE));
    }
    b.row(G1::identity(), terms);
    let rho = b.variable(aux.map_or(S::ZERO, |a| a.link_rho));
    b.row(
        crate::ops::msm1(
            &[
                t.seed_query,
                t.commitments[0],
                t.commitments[1],
                t.commitments[2],
            ],
            &[S::ONE, -S::ONE, -lambda, S::ONE + lambda],
        ),
        vec![(mu, pp.ghat, lambda.square()), (rho, vanishing, S::ONE)],
    );
    let chi = b.variable(aux.map_or(S::ZERO, |a| a.chi));
    b.row(
        pp.srs.offset,
        vec![
            (beta, t.offset_table, S::ONE),
            (chi, pp.srs.vanishing, -S::ONE),
        ],
    );
    let mut serial_terms = vec![];
    let mut tu_terms = vec![];
    let mut aid_terms = vec![];
    let mut aid_points = vec![];
    let mut aid_powers = vec![];
    let mut ta_points = vec![];
    let mut ta_powers = vec![];
    let mut serial_weight = S::ZERO;
    let mut tu_weight = S::ZERO;
    let mut aid_weight = S::ZERO;
    let mut ta_terms = vec![];
    let mut h1_terms = vec![];
    let v = hscalar(pp, ip, b"Hstar/context", &[&t.context]);
    for (index, u) in t.units.iter().enumerate() {
        let sn = u.sn.to_compressed();
        let aid = u.aid.to_compressed();
        let (c, h1, h3) = if let Some(aux) = aux {
            let h = &aux.hashes[index];
            (h.c, h.h1, h.h3)
        } else {
            (
                hscalar(pp, ip, b"Hstar/authorization", &[&sn, &aid]),
                hpoint(pp, ip, b"H1", &[&sn]),
                hpoint(pp, ip, b"H3", &[&sn, &aid]),
            )
        };
        serial_terms.push((unit_ids[index][0], u.sn, alpha[0][index]));
        serial_weight += alpha[0][index];
        tu_terms.push((unit_ids[index][1], u.tu, alpha[1][index]));
        tu_terms.push((unit_ids[index][3], -m[3], alpha[1][index]));
        tu_weight += alpha[1][index] * c;
        aid_points.push(u.aid);
        aid_powers.push(alpha[2][index]);
        aid_weight += alpha[2][index];
        h1_terms.push((r, h1, alpha[2][index]));
        ta_points.push(u.ta);
        ta_powers.push(alpha[3][index]);
        ta_terms.push((ska, G1::generator(), alpha[3][index]));
        ta_terms.push((ska, h3, v * alpha[3][index]));
    }
    serial_terms.push((mu, -G1::generator(), serial_weight));
    tu_terms.push((mu, -G1::generator(), tu_weight));
    b.row(G1::identity(), serial_terms);
    b.row(G1::identity(), tu_terms);
    aid_points.push(known_aid_group);
    aid_powers.push(-aid_weight);
    let aid_target = crate::ops::msm1(&aid_points, &aid_powers);
    let ta_target = crate::ops::msm1(&ta_points, &ta_powers);
    aid_terms.extend([
        (ska, G1::generator(), aid_weight),
        (beta, t.scope, aid_weight),
    ]);
    for (j, id) in delta_ids.iter().enumerate() {
        if let Some(id) = id {
            aid_terms.push((*id, pp.grant_bases[j], aid_weight));
        }
    }
    aid_terms.extend(h1_terms);
    b.row(aid_target, aid_terms);
    b.row(ta_target, ta_terms);
    if !received.map_or_else(
        || b.statement.shape(),
        |checked| b.statement.shape_received(checked),
    ) {
        return Err("malformed joint statement".into());
    }
    Ok((b.statement, b.witness))
}
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn remaining(&self) -> usize {
        self.bytes.len() - self.at
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn take(&mut self, count: usize) -> Result<&'a [u8]> {
        let end = self.at.checked_add(count).ok_or("record length overflow")?;
        if end > self.bytes.len() {
            return Err("truncated record".into());
        }
        let out = &self.bytes[self.at..end];
        self.at = end;
        Ok(out)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(self.take(8)?.try_into().unwrap()))
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn count(&mut self, max: usize) -> Result<usize> {
        let n = usize::try_from(self.u64()?).map_err(|_| "record count overflow")?;
        if n > max {
            return Err("record count outside expected bounds".into());
        }
        Ok(n)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn frame(&mut self) -> Result<&'a [u8]> {
        let count = self.count(self.remaining().saturating_sub(8))?;
        self.take(count)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn g1(&mut self) -> Result<G1> {
        let _span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
        let raw: [u8; 48] = self.take(48)?.try_into().unwrap();
        crate::subgroup_audit::decode("G1", &raw, "darlt/token/G1");
        Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed(&raw))
            .map(G1::from)
            .ok_or("invalid G1 encoding".into())
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn g2(&mut self) -> Result<blstrs::G2Projective> {
        let _span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
        let raw: [u8; 96] = self.take(96)?.try_into().unwrap();
        crate::subgroup_audit::decode("G2", &raw, "darlt/token/G2");
        Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed(&raw))
            .map(blstrs::G2Projective::from)
            .ok_or("invalid G2 encoding".into())
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn scalar(&mut self) -> Result<S> {
        let raw: [u8; 32] = self.take(32)?.try_into().unwrap();
        Option::<S>::from(S::from_bytes_be(&raw)).ok_or("noncanonical scalar encoding".into())
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn points1(&mut self) -> Result<Vec<G1>> {
        let count = self.count(self.remaining() / 48)?;
        (0..count).map(|_| self.g1()).collect()
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn sig(&mut self) -> Result<spseq_fc::Sig> {
        Ok(spseq_fc::Sig {
            z: self.g1()?,
            y: self.g1()?,
            yhat: self.g2()?,
        })
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn finish(&self) -> Result<()> {
        if self.remaining() == 0 {
            Ok(())
        } else {
            Err("trailing bytes".into())
        }
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn decode_policy(bytes: &[u8], attributes: usize) -> Result<Policy> {
    let _span = crate::darlt::instrumentation::span("strict_decoding");
    let mut r = Reader::new(bytes);
    let period = r.u64()?;
    let count = r.count(r.remaining() / 17)?;
    let mut atoms = Vec::with_capacity(count);
    for _ in 0..count {
        let tag = r.take(1)?[0];
        let index = if tag == 0 || tag == 1 || tag == 3 {
            Some(r.count(attributes.saturating_sub(1))?)
        } else {
            None
        };
        let atom = match tag {
            0 => Atom::Reveal(index.unwrap(), r.scalar()?),
            1 => Atom::Equal(index.unwrap(), r.scalar()?),
            2 => {
                let length = r.count(r.remaining().saturating_sub(32) / 40)?;
                let mut terms = Vec::with_capacity(length);
                for _ in 0..length {
                    terms.push((r.count(attributes.saturating_sub(1))?, r.scalar()?));
                }
                Atom::Linear(terms, r.scalar()?)
            }
            3 => Atom::Range(index.unwrap(), r.u64()?, r.u64()?),
            _ => return Err("unknown policy atom".into()),
        };
        atoms.push(atom);
    }
    r.finish()?;
    Ok(Policy { period, atoms })
}

pub struct PreparedSpend<'a> {
    holder: &'a Holder,
    token: Token,
    aux: Auxiliary,
    sigma: sigma::Prepared,
    statement: Statement,
    witness: Vec<S>,
    known_aid_group: G1,
    query_shape: QueryShape,
    column_transcript: Vec<u8>,
    column_challenge: S,
}
impl PreparedSpend<'_> {
    pub fn serials(&self) -> Vec<[u8; 48]> {
        self.token.serials()
    }
    /// Local workload evidence only; these counts are not token fields.
    pub fn query_shape(&self) -> &QueryShape {
        &self.query_shape
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryShape {
    pub units: usize,
    pub distinct_pools: usize,
    pub distinct_offsets: usize,
    pub first_pool_offset: usize,
}

/// Pool-by-pool selection for the measured workload. The caller supplies actual
/// previously spent positions; this does not reserve or change protocol state.
/// Arbitrary legal position sets remain accepted by the protocol interfaces.
pub fn select_sequential_units(
    pp: &PublicParameters,
    holder: &Holder,
    already_spent: &BTreeSet<usize>,
    k: usize,
) -> Result<Vec<usize>> {
    if k == 0 || holder.pp_id != pp.id {
        return Err("invalid sequential workload request".into());
    }
    let positions: Vec<_> = (0..pp.n)
        .filter(|p| holder.gamma.contains(&(p / pp.s)) && !already_spent.contains(p))
        .take(k)
        .collect();
    if positions.len() != k {
        return Err("insufficient unused units in sequential workload".into());
    }
    Ok(positions)
}

pub fn query_shape(pp: &PublicParameters, positions: &[usize]) -> Result<QueryShape> {
    if positions.is_empty()
        || positions.iter().any(|p| *p >= pp.n)
        || positions.iter().copied().collect::<BTreeSet<_>>().len() != positions.len()
    {
        return Err("invalid query-shape positions".into());
    }
    Ok(QueryShape {
        units: positions.len(),
        distinct_pools: positions
            .iter()
            .map(|p| p / pp.s)
            .collect::<BTreeSet<_>>()
            .len(),
        distinct_offsets: positions
            .iter()
            .map(|p| p % pp.s)
            .collect::<BTreeSet<_>>()
            .len(),
        first_pool_offset: positions[0] % pp.s,
    })
}
/// Consumed once by finish_spend. Both Caulk proofs and all context-independent
/// nonce-base powers are computed here, before a verifier context is supplied.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn prepare_spend<'a>(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    holder: &'a mut Holder,
    positions: &[usize],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> Result<PreparedSpend<'a>> {
    if !spseq_fc::validate_instance(&pp.fc, &ip.vk) {
        return Err("invalid SPSEQ-FC instance".into());
    }
    prepare_spend_impl(pp, ip, holder, positions, policy, rng)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn prepare_spend_installed<'a>(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    holder: &'a mut Holder,
    positions: &[usize],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> Result<PreparedSpend<'a>> {
    prepare_spend_impl(pp, ip, holder, positions, policy, rng)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn prepare_spend_impl<'a>(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    holder: &'a mut Holder,
    positions: &[usize],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> Result<PreparedSpend<'a>> {
    let k = positions.len();
    if holder.pp_id != pp.id
        || holder.issuer_id != <[u8; 32]>::from(sha2::Sha256::digest(ip.encode()))
        || holder.parent.len() != 8
        || holder.mdel.len() != pp.k_del
        || holder.delta.len() != pp.k_del
        || holder
            .owner
            .as_ref()
            .is_some_and(|o| o.mprv.len() != pp.k_prv)
    {
        return Err("malformed child holder".into());
    }
    if k == 0
        || k > pp.k_max
        || positions.iter().any(|p| *p >= pp.n)
        || positions.iter().copied().collect::<BTreeSet<_>>().len() != k
    {
        return Err("invalid one-child block positions".into());
    }
    let l = layout(pp, policy)?;
    for p in positions {
        holder.pool(*p / pp.s)?;
    }
    for p in positions {
        holder.scope_opening(pp, *p / pp.s)?;
    }
    let mu = crypto::nonzero(rng);
    let beta = mu.invert().unwrap();
    let chi = S::random(&mut *rng);
    let (message, signature) =
        spseq_fc::chg_rep_installed(&holder.message(), &holder.signature, mu, rng)?;
    let vector_rhos = [
        S::random(&mut *rng),
        S::random(&mut *rng),
        S::random(&mut *rng),
    ];
    let mut token = Token {
        auth: Authentication { message, signature },
        scope: holder.scope * mu,
        offset_table: crate::ops::msm1(&[pp.srs.offset, pp.srs.vanishing], &[mu, mu * chi]),
        commitments: [G1::identity(); 3],
        seed_query: G1::identity(),
        units: vec![],
        lookups: vec![],
        range_commitments: vec![],
        proof: sigma::Proof {
            c: S::ZERO,
            z: vec![],
            bits: vec![],
        },
        policy: policy.clone(),
        context: vec![],
    };
    let mut aux = Auxiliary {
        mu,
        vector_rhos,
        q: vector_rhos[1] * beta,
        link_rho: S::random(&mut *rng),
        chi,
        range_values: vec![],
        range_blinds: vec![],
        units: vec![],
        hashes: vec![],
    };
    let grant_group = pp
        .grant_bases
        .iter()
        .zip(&holder.delta)
        .filter(|(_, b)| **b)
        .map(|(g, _)| *g)
        .sum::<G1>();
    for p in positions {
        let pool = holder.pool(*p / pp.s)?;
        let i = *p % pp.s;
        let zeta = pool.seeds[0] + S::from(i as u64);
        let eta = pool.seeds[1] + S::from(i as u64);
        let sn = G1::generator() * Option::<S>::from(zeta.invert()).ok_or("zero zeta")?;
        let h1 = hpoint(pp, ip, b"H1", &[&sn.to_compressed()]);
        let aid = crate::ops::msm1(&[G1::generator(), h1], &[holder.ska, holder.r])
            + grant_group
            + holder.scope;
        let c = hscalar(
            pp,
            ip,
            b"Hstar/authorization",
            &[&sn.to_compressed(), &aid.to_compressed()],
        );
        let tu = holder.parent[3]
            + G1::generator() * (c * Option::<S>::from(eta.invert()).ok_or("zero eta")?);
        token.units.push(Unit {
            sn,
            aid,
            tu,
            ta: G1::identity(),
        });
        aux.hashes.push(UnitHashes {
            h1,
            h3: hpoint(pp, ip, b"H3", &[&sn.to_compressed(), &aid.to_compressed()]),
            c,
        });
        aux.units.push(UnitSecret {
            x1: mu * zeta,
            x2: mu * eta,
            x3: mu * S::from(i as u64),
            eta,
        });
    }
    let (bases, vanishing) = pp.query_basis(k.next_power_of_two())?;
    let merged = merged_query_bases(&bases, k)?;
    for (d, rho) in vector_rhos.iter().enumerate() {
        let values: Vec<_> = aux
            .units
            .iter()
            .map(|u| match d {
                0 => u.x1,
                1 => u.x2,
                _ => u.x3,
            })
            .collect();
        let mut vector_bases = merged.to_vec();
        vector_bases.push(vanishing);
        let mut values = values;
        values.push(*rho);
        token.commitments[d] = crate::ops::msm1(&vector_bases, &values);
    }
    let tr0 = outer0(pp, ip, &token);
    let lambda = crypto::hash_scalar(b"H_col/merge", &tr0);
    token.seed_query = crate::ops::msm1(
        &[
            token.commitments[0],
            token.commitments[1],
            token.commitments[2],
            pp.ghat,
            vanishing,
        ],
        &[
            S::ONE,
            lambda,
            -(S::ONE + lambda),
            lambda.square() * mu,
            aux.link_rho,
        ],
    );
    for role in 0..2 {
        let (table, cm, positions, values, blind, openings) = if role == 0 {
            let values = aux
                .units
                .iter()
                .map(|u| u.x1 + lambda * u.x2 + lambda.square() * mu - (S::ONE + lambda) * u.x3)
                .collect();
            let openings = positions
                .iter()
                .map(|p| {
                    let b = *p / pp.s;
                    let pool = holder.pool(b)?;
                    Ok(crate::ops::msm2(
                        &[
                            pool.openings[0],
                            pool.openings[1],
                            holder.scope_openings[&b],
                        ],
                        &[mu, mu * lambda, mu * lambda.square()],
                    ))
                })
                .collect::<Result<Vec<_>>>()?;
            (
                seed_table(&token, lambda),
                token.seed_query,
                positions.iter().map(|p| *p / pp.s).collect::<Vec<_>>(),
                values,
                vector_rhos[0] + lambda * vector_rhos[1] - (S::ONE + lambda) * vector_rhos[2]
                    + aux.link_rho,
                openings,
            )
        } else {
            let openings = positions
                .iter()
                .map(|p| {
                    let i = *p % pp.s;
                    crate::ops::msm2(&[pp.srs.o_hat[i], pp.srs.k_hat[i]], &[mu, mu * chi])
                })
                .collect();
            (
                token.offset_table,
                token.commitments[2],
                positions.iter().map(|p| *p % pp.s).collect(),
                aux.units.iter().map(|u| u.x3).collect(),
                vector_rhos[2],
                openings,
            )
        };
        let statement = caulk::Statement {
            table_commitment: table,
            query_commitment: cm,
            query_size: k.next_power_of_two(),
            actual_query_count: k,
        };
        let witness = caulk::Witness {
            positions,
            values,
            query_blinder: blind,
            table_openings_g2: openings,
        };
        token.lookups.push(caulk::prove(
            caulk_view(pp),
            &statement,
            &witness,
            &lookup_prefix(&tr0, lambda, role),
            rng,
        )?);
    }
    let mut attrs = holder.mdel.clone();
    if l.private {
        attrs.extend(
            &holder
                .owner
                .as_ref()
                .ok_or("agent cannot use private attribute")?
                .mprv,
        );
    } else {
        attrs.extend(vec![S::ZERO; pp.k_prv]);
    }
    for (idx, lo, hi) in &l.ranges {
        let value = scalar_u64(attrs[*idx])?;
        if value < *lo || value > *hi {
            return Err("false range policy".into());
        }
        for diff in [value - lo, hi - value] {
            for bit in 0..bits_needed(*lo, *hi) {
                let value = S::from((diff >> bit) & 1);
                let blind = S::random(&mut *rng);
                token
                    .range_commitments
                    .push(crate::ops::msm1(&[G1::generator(), pp.h], &[value, blind]));
                aux.range_values.push(value);
                aux.range_blinds.push(blind);
            }
        }
    }
    // Prepared caches stable variable/base pairs; template targets are not
    // protocol messages, so no dummy context or dummy T_a exponentiation is needed.
    let ones = std::array::from_fn(|_| vec![S::ONE; k]);
    let (st, witness) = joint_statement(pp, ip, &token, lambda, &ones, Some(holder), Some(&aux))?;
    // Only the last four rows depend on H_unit/context. Cache all other rows
    // collapsing the statement or its shared attribute responses.
    let aid_row = st.g1.len() - 2;
    let aid_prefix = st.g1[aid_row].terms.len() - k;
    let mut groups: Vec<_> = (0..st.g1.len() - 4)
        .map(|row| (row, (0..st.g1[row].terms.len()).collect()))
        .collect();
    groups.push((aid_row, (0..aid_prefix).collect()));
    let sigma = sigma::Prepared::new_grouped(&st, &witness, &groups, rng)?;
    let known_aid_group = pp
        .grant_bases
        .iter()
        .zip(&l.referenced)
        .filter_map(|(base, referenced)| referenced.then_some(*base))
        .sum();
    Ok(PreparedSpend {
        holder,
        token,
        aux,
        sigma,
        statement: st,
        witness,
        known_aid_group,
        query_shape: query_shape(pp, positions)?,
        column_transcript: tr0,
        column_challenge: lambda,
    })
}

/// Update exactly the original four unit rows. Fixed attributes, policy rows,
/// bases and witnesses were constructed before context and are retained.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn online_unit_rows(
    statement: &mut Statement,
    token: &Token,
    hashes: &[UnitHashes],
    alpha: &[Vec<S>; 4],
    context_scalar: S,
    known_aid_group: G1,
) -> Result<()> {
    let k = token.units.len();
    if statement.g1.len() < 4 || hashes.len() != k || alpha.iter().any(|row| row.len() != k) {
        return Err("online unit-row dimensions".into());
    }
    let at = statement.g1.len() - 4;
    let rows = &mut statement.g1[at..];
    if rows[0].terms.len() != k + 1
        || rows[1].terms.len() != 2 * k + 1
        || rows[2].terms.len() < k + 2
        || rows[3].terms.len() != 2 * k
    {
        return Err("prepared unit-row layout changed".into());
    }
    let field_span = crate::darlt::instrumentation::span("field_arithmetic");
    for (i, ((serial, tu), ta)) in alpha[0].iter().zip(&alpha[1]).zip(&alpha[3]).enumerate() {
        rows[0].terms[i].2 = *serial;
        rows[1].terms[2 * i].2 = *tu;
        rows[1].terms[2 * i + 1].2 = *tu;
        rows[3].terms[2 * i].2 = *ta;
        rows[3].terms[2 * i + 1].2 = context_scalar * ta;
    }
    rows[0].terms[k].2 = alpha[0].iter().copied().sum();
    rows[1].terms[2 * k].2 = alpha[1]
        .iter()
        .zip(hashes)
        .map(|(coefficient, hash)| *coefficient * hash.c)
        .sum();
    let aid_weight: S = alpha[2].iter().copied().sum();
    let aid_prefix = rows[2].terms.len() - k;
    for term in &mut rows[2].terms[..aid_prefix] {
        term.2 = aid_weight;
    }
    for (term, coefficient) in rows[2].terms[aid_prefix..].iter_mut().zip(&alpha[2]) {
        term.2 = *coefficient;
    }
    drop(field_span);
    let mut aid_points: Vec<_> = token.units.iter().map(|u| u.aid).collect();
    aid_points.push(known_aid_group);
    let mut aid_scalars = alpha[2].clone();
    aid_scalars.push(-aid_weight);
    rows[2].target = crate::ops::msm1(&aid_points, &aid_scalars);
    rows[3].target = crate::ops::msm1(
        &token.units.iter().map(|u| u.ta).collect::<Vec<_>>(),
        &alpha[3],
    );
    Ok(())
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn finish_spend(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    prepared: PreparedSpend<'_>,
    context: &[u8],
    _rng: &mut impl RngCore,
) -> Result<Token> {
    if context.is_empty() {
        return Err("empty verifier context".into());
    }
    let PreparedSpend {
        holder,
        mut token,
        aux,
        sigma,
        mut statement,
        witness,
        known_aid_group,
        query_shape: _,
        column_transcript: tr0,
        column_challenge: lambda,
    } = prepared;
    token.context = context.to_vec();
    let v = hscalar(pp, ip, b"Hstar/context", &[context]);
    for (u, hashes) in token.units.iter_mut().zip(&aux.hashes) {
        u.ta = crate::ops::msm1(&[G1::generator(), hashes.h3], &[holder.ska, holder.ska * v]);
    }
    let ap = alpha_prefix(&tr0, lambda, &token);
    let alpha = weights(&ap, token.units.len());
    online_unit_rows(
        &mut statement,
        &token,
        &aux.hashes,
        &alpha,
        v,
        known_aid_group,
    )?;
    token.proof = sigma.finish(
        &statement,
        b"DARLT/Spend/ZK",
        &sigma_external(&ap, &alpha),
        &witness,
    )?;
    Ok(token)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn record_shape(pp: &PublicParameters, t: &Token) -> bool {
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    record_format(pp, t)
        && t.auth.message.iter().all(|p| crypto::valid1(*p, true))
        && [t.scope, t.offset_table, t.seed_query]
            .iter()
            .chain(t.commitments.iter())
            .chain(t.range_commitments.iter())
            .all(|p| crypto::valid1(*p, false))
        && t.units.iter().all(|u| {
            [u.sn, u.aid, u.tu, u.ta]
                .iter()
                .all(|p| crypto::valid1(*p, true))
        })
}
fn record_format(pp: &PublicParameters, t: &Token) -> bool {
    t.auth.message.len() == 9
        && !t.units.is_empty()
        && t.units.len() <= pp.k_max
        && t.lookups.len() == 2
        && !t.context.is_empty()
        && t.auth.message.iter().all(|p| *p != G1::identity())
        && t.auth.signature.y != G1::identity()
        && t.auth.signature.yhat != blstrs::G2Projective::identity()
        && t.units.iter().all(|u| {
            [u.sn, u.aid, u.tu, u.ta]
                .iter()
                .all(|p| *p != G1::identity())
        })
        && t.serials().iter().copied().collect::<BTreeSet<_>>().len() == t.units.len()
}
/// All non-pairing checks remain per token even in the randomized profile.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn valid(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    spseq_fc::validate_instance(&pp.fc, &ip.vk) && valid_impl(pp, ip, t, mode, rng)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn valid_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    valid_impl(pp, ip, t, mode, rng)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_impl(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    (|| -> Result<bool> {
        let equations = checked_equations(pp, ip, t)?;
        Ok(verification::check(&equations, mode, rng)?.accepted)
    })()
    .unwrap_or(false)
}

/// Check genuinely independent token proofs before a shared pairing check.
/// No token-local Fiat--Shamir, policy or shape check is removed. Verifier
/// randomness is sampled only after every immutable input has been checked.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn valid_many(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    tokens: &[Token],
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    spseq_fc::validate_instance(&pp.fc, &ip.vk) && valid_many_installed(pp, ip, tokens, mode, rng)
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn valid_many_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    tokens: &[Token],
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    (|| -> Result<bool> {
        if tokens.is_empty() {
            return Ok(false);
        }
        let mut serials = BTreeSet::new();
        let mut equations = vec![];
        for token in tokens {
            equations.extend(checked_equations(pp, ip, token)?);
            if token.serials().into_iter().any(|sn| !serials.insert(sn)) {
                return Ok(false);
            }
        }
        Ok(verification::check(&equations, mode, rng)?.accepted)
    })()
    .unwrap_or(false)
}

/// Return fixed pairing equations only after all per-token non-pairing
/// checks pass. Both individual and across-token validation use this path.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn checked_equations(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
) -> Result<Vec<crate::pairing_batch::Equation>> {
    checked_equations_impl(pp, ip, t, None)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn checked_equations_impl(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
    received: Option<&ReceivedInputs>,
) -> Result<Vec<crate::pairing_batch::Equation>> {
    if !received.map_or_else(|| record_shape(pp, t), |_| record_format(pp, t)) {
        return Err("token shape".into());
    }
    let tr0 = outer0(pp, ip, t);
    let lambda = crypto::hash_scalar(b"H_col/merge", &tr0);
    let ap = alpha_prefix(&tr0, lambda, t);
    let alpha = weights(&ap, t.units.len());
    let (st, _) = joint_statement_impl(pp, ip, t, lambda, &alpha, None, None, received)?;
    let external = sigma_external(&ap, &alpha);
    if !received.map_or_else(
        || st.verify(b"DARLT/Spend/ZK", &external, &t.proof),
        |checked| st.verify_received(b"DARLT/Spend/ZK", &external, &t.proof, checked),
    ) {
        return Err("token Sigma proof".into());
    }
    let mut equations = received
        .map_or_else(
            || spseq_fc::signature_equations_installed(&ip.vk, &t.auth.message, &t.auth.signature),
            |checked| {
                spseq_fc::signature_equations_received(
                    &ip.vk,
                    &t.auth.message,
                    &t.auth.signature,
                    checked,
                )
            },
        )
        .ok_or("signature shape")?;
    for role in 0..2 {
        let statement = caulk::Statement {
            table_commitment: if role == 0 {
                seed_table(t, lambda)
            } else {
                t.offset_table
            },
            query_commitment: if role == 0 {
                t.seed_query
            } else {
                t.commitments[2]
            },
            query_size: t.units.len().next_power_of_two(),
            actual_query_count: t.units.len(),
        };
        let prefix = lookup_prefix(&tr0, lambda, role);
        equations.extend(match received {
            Some(checked) => caulk::verification_equations_received(
                caulk_view(pp),
                &statement,
                &t.lookups[role],
                &prefix,
                checked,
            )?,
            None => caulk::verification_equations(
                caulk_view(pp),
                &statement,
                &t.lookups[role],
                &prefix,
            )?,
        });
    }
    Ok(equations)
}
/// Installed-context path for an immutable token created by strict decoding.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn valid_received_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    token: &ReceivedToken,
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    let _native = super::instrumentation::span("verification.native");
    (|| -> Result<bool> {
        if token.inputs.parameter_id != pp.id {
            return Err("received token parameter binding".into());
        }
        let equations = checked_equations_impl(pp, ip, &token.token, Some(&token.inputs))?;
        Ok(verification::check_received(&equations, mode, rng, &token.inputs)?.accepted)
    })()
    .unwrap_or(false)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn valid_many_received_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    tokens: &[ReceivedToken],
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    let _native = super::instrumentation::span("verification.native");
    (|| -> Result<bool> {
        let first = tokens.first().ok_or("empty received batch")?;
        let mut serials = BTreeSet::new();
        let mut equations = vec![];
        for token in tokens {
            if token.inputs.parameter_id != pp.id {
                return Err("received token parameter binding".into());
            }
            equations.extend(checked_equations_impl(
                pp,
                ip,
                &token.token,
                Some(&token.inputs),
            )?);
            if token.serials().into_iter().any(|sn| !serials.insert(sn)) {
                return Ok(false);
            }
        }
        Ok(verification::check_received(&equations, mode, rng, &first.inputs)?.accepted)
    })()
    .unwrap_or(false)
}
/// Judge receives two complete evidence records in one verification step.
/// A repeated serial across those records is intentional evidence, whereas
/// every token's own syntax, Sigma proof and serial uniqueness remain checked.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn valid_evidence_received_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    a: &ReceivedToken,
    b: &ReceivedToken,
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    let _native = super::instrumentation::span("verification.native");
    (|| -> Result<bool> {
        let mut equations = vec![];
        for token in [a, b] {
            if token.inputs.parameter_id != pp.id {
                return Err("received evidence parameter binding".into());
            }
            equations.extend(checked_equations_impl(
                pp,
                ip,
                &token.token,
                Some(&token.inputs),
            )?);
        }
        Ok(verification::check_received(&equations, mode, rng, &a.inputs)?.accepted)
    })()
    .unwrap_or(false)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn valid_evidence_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    a: &Token,
    b: &Token,
    mode: Mode,
    rng: &mut impl RngCore,
) -> bool {
    (|| -> Result<bool> {
        let mut equations = checked_equations(pp, ip, a)?;
        equations.extend(checked_equations(pp, ip, b)?);
        Ok(verification::check(&equations, mode, rng)?.accepted)
    })()
    .unwrap_or(false)
}
impl Token {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn wire_decode(pp: &PublicParameters, bytes: &[u8]) -> Result<Self> {
        let _span = crate::darlt::instrumentation::span("strict_decoding");
        let mut r = Reader::new(bytes);
        if r.take(1)?[0] != 21 {
            return Err("token version".into());
        }
        let mut a = Reader::new(r.frame()?);
        let auth = Authentication {
            message: (0..9).map(|_| a.g1()).collect::<Result<Vec<_>>>()?,
            signature: a.sig()?,
        };
        a.finish()?;
        // Match the native SPSEQ signature format. Z may be the identity;
        // the two representation generators Y and Yhat must not be.
        if auth.signature.y == G1::identity()
            || auth.signature.yhat == blstrs::G2Projective::identity()
        {
            return Err("identity signature representation generator".into());
        }
        let scope = r.g1()?;
        let offset_table = r.g1()?;
        let commitments = [r.g1()?, r.g1()?, r.g1()?];
        let seed_query = r.g1()?;
        let k = r.count(pp.k_max)?;
        if k == 0 {
            return Err("empty token".into());
        }
        let units = (0..k)
            .map(|_| {
                Ok(Unit {
                    sn: r.g1()?,
                    aid: r.g1()?,
                    tu: r.g1()?,
                    ta: r.g1()?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let lookups = (0..2)
            .map(|_| caulk::Proof::from_bytes(r.take(caulk::PROOF_BYTES)?))
            .collect::<Result<Vec<_>>>()?;
        let range_commitments = r.points1()?;
        let proof_bytes = r.frame()?;
        let policy = decode_policy(r.frame()?, pp.k_del + pp.k_prv)?;
        let context = r.frame()?.to_vec();
        r.finish()?;
        let mut token = Self {
            auth,
            scope,
            offset_table,
            commitments,
            seed_query,
            units,
            lookups,
            range_commitments,
            proof: sigma::Proof {
                c: S::ZERO,
                z: vec![],
                bits: vec![],
            },
            policy,
            context,
        };
        let l = layout(pp, &token.policy)?;
        let range_bits = l
            .ranges
            .iter()
            .map(|(_, lo, hi)| 2 * bits_needed(*lo, *hi))
            .sum::<usize>();
        let vars = 11
            + l.known[..pp.k_del].iter().filter(|v| v.is_none()).count()
            + l.referenced[..pp.k_del].iter().filter(|v| !**v).count()
            + if l.private {
                1 + l.known[pp.k_del..].iter().filter(|v| v.is_none()).count()
            } else {
                0
            }
            + 2 * range_bits
            + 4 * k;
        token.proof = sigma::Proof::decode(proof_bytes, vars, range_bits)?;
        if !record_format(pp, &token)
            || token.range_commitments.len() != range_bits
            || token.wire_encode() != bytes
        {
            return Err("noncanonical token shape".into());
        }
        Ok(token)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Responsibility {
    DoubleUse,
    DoubleAlloc,
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn identify_validated(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    a: &Token,
    ai: usize,
    b: &Token,
    bi: usize,
) -> Option<(Responsibility, G1)> {
    let x = a.units.get(ai)?;
    let y = b.units.get(bi)?;
    if x.sn != y.sn || (x.aid == y.aid && a.context == b.context) {
        return None;
    }
    if x.aid == y.aid {
        let v1 = hscalar(pp, ip, b"Hstar/context", &[&a.context]);
        let v2 = hscalar(pp, ip, b"Hstar/context", &[&b.context]);
        recovery::raw_du_recover(x.ta, y.ta, v1, v2)
            .ok()
            .map(|p| (Responsibility::DoubleUse, p))
    } else {
        let sn = x.sn.to_compressed();
        let c1 = hscalar(
            pp,
            ip,
            b"Hstar/authorization",
            &[&sn, &x.aid.to_compressed()],
        );
        let c2 = hscalar(
            pp,
            ip,
            b"Hstar/authorization",
            &[&sn, &y.aid.to_compressed()],
        );
        recovery::raw_da_recover(x.tu, y.tu, c1, c2)
            .ok()
            .map(|p| (Responsibility::DoubleAlloc, p))
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
#[allow(clippy::too_many_arguments)]
pub fn judge(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    a: &Token,
    ai: usize,
    b: &Token,
    bi: usize,
    mode: Mode,
    rng: &mut impl RngCore,
) -> Option<(Responsibility, G1)> {
    if !spseq_fc::validate_instance(&pp.fc, &ip.vk)
        || !valid_evidence_installed(pp, ip, a, b, mode, rng)
    {
        return None;
    }
    identify_validated(pp, ip, a, ai, b, bi)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn read_bit(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    t: &Token,
    secrets: &[S; 2],
    mode: Mode,
    rng: &mut impl RngCore,
) -> Option<usize> {
    if !valid(pp, ip, t, mode, rng) || secrets.map(|x| G1::generator() * x) != ip.metadata_keys {
        return None;
    }
    let r = t.auth.message[4];
    let e = t.auth.message[5];
    let bits: Vec<_> = (0..2).filter(|b| r * secrets[*b] == e).collect();
    (bits.len() == 1).then(|| bits[0])
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn seed_table(t: &Token, lambda: S) -> G1 {
    crate::ops::msm1(
        &[t.auth.message[1], t.auth.message[2], t.scope],
        &[S::ONE, lambda, lambda.square()],
    )
}
