//! Shared-witness Schnorr representations and Pedersen bit OR proofs.
//!
//! Shared-witness transcripts and proof encoding.
//! G1/G2 representation sums execute actual backend MSMs. One-use Prepared
//! stores context-independent nonce powers; online coefficients may vary.

use crate::polynomial::S;
use blstrs::{Compress, G1Projective as G1, G2Projective as G2, Gt};
use ff::Field;
use group::{Curve, Group};
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub struct Eq1 {
    pub target: G1,
    pub terms: Vec<(usize, G1, S)>,
}
#[derive(Clone, Debug)]
pub struct Eq2 {
    pub target: G2,
    pub terms: Vec<(usize, G2, S)>,
}
#[derive(Clone, Debug)]
pub struct EqT {
    pub target: Gt,
    pub terms: Vec<(usize, Gt, S)>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitRelation {
    pub var: usize,
    pub blind_var: usize,
    pub g: G1,
    pub h: G1,
    pub commitment: G1,
}
#[derive(Clone, Debug)]
pub struct Statement {
    pub vars: usize,
    pub g1: Vec<Eq1>,
    pub g2: Vec<Eq2>,
    pub gt: Vec<EqT>,
    pub bits: Vec<BitRelation>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub c: S,
    pub z: Vec<S>,
    /// Per bit: [c_0, z_0, z_1], with c_1 = global c - c_0.
    pub bits: Vec<[S; 3]>,
}

impl Proof {
    /// Compact native payload; vector dimensions are fixed by the statement.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut out = Vec::with_capacity(32 * (1 + self.z.len() + 3 * self.bits.len()));
        out.extend(self.c.to_bytes_be());
        for response in &self.z {
            out.extend(response.to_bytes_be());
        }
        for responses in &self.bits {
            for response in responses {
                out.extend(response.to_bytes_be());
            }
        }
        out
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn decode(bytes: &[u8], vars: usize, bits: usize) -> Result<Self, String> {
        let _span = crate::darlt::instrumentation::span("strict_decoding");
        let scalars = bits
            .checked_mul(3)
            .and_then(|n| n.checked_add(vars))
            .and_then(|n| n.checked_add(1))
            .ok_or("proof dimension overflow")?;
        let length = scalars.checked_mul(32).ok_or("proof length overflow")?;
        if bytes.len() != length {
            return Err("incorrect proof byte length".into());
        }
        let values: Result<Vec<S>, String> = bytes
            .chunks_exact(32)
            .map(|chunk| {
                let value: [u8; 32] = chunk.try_into().expect("fixed scalar chunk");
                Option::<S>::from(S::from_bytes_be(&value))
                    .ok_or_else(|| "noncanonical scalar".to_owned())
            })
            .collect();
        let values = values?;
        Ok(Self {
            c: values[0],
            z: values[1..1 + vars].to_vec(),
            bits: values[1 + vars..]
                .chunks_exact(3)
                .map(|chunk| [chunk[0], chunk[1], chunk[2]])
                .collect(),
        })
    }
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid1(point: G1) -> bool {
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    let affine = point.to_affine();
    crate::subgroup_audit::g1(&point, "darlt/sigma/valid1");
    bool::from(affine.is_on_curve() & affine.is_torsion_free())
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid2(point: G2) -> bool {
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    let affine = point.to_affine();
    crate::subgroup_audit::g2(&point, "darlt/sigma/valid2");
    bool::from(affine.is_on_curve() & affine.is_torsion_free())
}
/// Integer-order check. Converting the group order into Fr would give zero and
/// would not test membership. Additions here are Fp12 multiplications.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_gt(point: Gt) -> bool {
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    if point == Gt::default() {
        return false;
    }
    if point == Gt::identity() {
        return true;
    }
    crate::subgroup_audit::gt(&point, "darlt/sigma/valid_gt");
    const ORDER: [u8; 32] = [
        0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8,
        0x05, 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00,
        0x00, 0x01,
    ];
    let mut accumulator = Gt::identity();
    for byte in ORDER {
        for bit in (0..8).rev() {
            accumulator = accumulator + accumulator;
            if byte & (1 << bit) != 0 {
                accumulator += point;
            }
        }
    }
    accumulator == Gt::identity()
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn gt_bytes(point: Gt) -> Vec<u8> {
    if point == Gt::identity() {
        return vec![255; 288];
    }
    let mut out = Vec::with_capacity(288);
    point
        .write_compressed(&mut out)
        .expect("validated GT compression");
    out
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend((bytes.len() as u64).to_be_bytes());
    out.extend(bytes);
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn scalar_hash(domain: &[u8], bytes: &[u8]) -> S {
    let _span = crate::darlt::instrumentation::span("fiat_shamir_hash");
    for counter in 0u64.. {
        let mut hash = Sha256::new();
        hash.update(b"DARLT/Proof/Sigma/Shared");
        hash.update((domain.len() as u64).to_be_bytes());
        hash.update(domain);
        hash.update((bytes.len() as u64).to_be_bytes());
        hash.update(bytes);
        hash.update(counter.to_be_bytes());
        let digest: [u8; 32] = hash.finalize().into();
        if let Some(value) = Option::<S>::from(S::from_bytes_be(&digest)) {
            return value;
        }
    }
    unreachable!()
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn eval1(terms: &[(usize, G1, S)], witness: &[S]) -> G1 {
    let points: Vec<_> = terms.iter().map(|(_, base, _)| *base).collect();
    let scalars = scalar_coefficients(terms, witness);
    crate::ops::msm1(&points, &scalars)
}

fn scalar_coefficients<T>(terms: &[(usize, T, S)], witness: &[S]) -> Vec<S> {
    let _span = crate::darlt::instrumentation::span("field_arithmetic");
    terms
        .iter()
        .map(|(index, _, coefficient)| witness[*index] * coefficient)
        .collect()
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn eval2(terms: &[(usize, G2, S)], witness: &[S]) -> G2 {
    let points: Vec<_> = terms.iter().map(|(_, base, _)| *base).collect();
    let scalars = scalar_coefficients(terms, witness);
    crate::ops::msm2(&points, &scalars)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn evalt(terms: &[(usize, Gt, S)], witness: &[S]) -> Gt {
    terms
        .iter()
        .fold(Gt::identity(), |sum, (index, base, coefficient)| {
            sum + base * (witness[*index] * coefficient)
        })
}
struct BitState {
    real: usize,
    nonce: S,
    fake_c: S,
    fake_z: S,
    opening: S,
}

struct CachedPowers {
    nonce: G1,
    witness: G1,
}

struct CachedGroup {
    positions: Vec<usize>,
    pivot: Option<(usize, S)>,
    nonce: G1,
    witness: G1,
}

struct CachedRow {
    terms: Vec<(usize, G1, S)>,
    groups: Vec<CachedGroup>,
}

impl CachedGroup {
    /// A group is reusable when all of its coefficients changed by one factor.
    /// Otherwise the original individual cached powers remain available.
    fn factor(&self, template: &[(usize, G1, S)], actual: &[(usize, G1, S)]) -> Option<S> {
        let factor = self
            .pivot
            .map_or(S::ZERO, |(i, inverse)| actual[i].2 * inverse);
        self.positions
            .iter()
            .all(|&i| actual[i].2 == template[i].2 * factor)
            .then_some(factor)
    }
}

/// Context-independent first-message work, consumed by one online proof.
/// The witness is retained privately to bind this capability to its creation.
/// Template targets and coefficients may change online; variable/base pairs
/// and all bit relations must already be fixed before preparation.
///
/// ```compile_fail,E0382
/// use darlt_spseq_fc::darlt::sigma::{Prepared, Statement};
/// use blstrs::Scalar;
/// fn reuse(p: Prepared, actual: &Statement, w: &[Scalar]) {
///     let _ = p.finish(actual, b"domain", b"context", w);
///     let _ = p.finish(actual, b"domain", b"other-context", w);
/// }
/// ```
pub struct Prepared {
    vars: usize,
    witness: Vec<S>,
    nonces: Vec<S>,
    powers: BTreeMap<(usize, [u8; 48]), CachedPowers>,
    rows: Vec<CachedRow>,
    bit_relations: Vec<BitRelation>,
    bit_firsts: Vec<[G1; 3]>,
    bit_states: Vec<BitState>,
}

impl Prepared {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn new(
        template: &Statement,
        witness: &[S],
        rng: &mut impl RngCore,
    ) -> Result<Self, String> {
        Self::new_grouped(template, witness, &[], rng)
    }

    /// Cache weighted sums of fixed terms before context arrives. Each entry
    /// names one row and a disjoint group of term positions in that row.
    /// Unlisted terms remain individual cached powers. This does not change the
    /// statement, first-message value, transcript, or proof representation.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn new_grouped(
        template: &Statement,
        witness: &[S],
        groups: &[(usize, Vec<usize>)],
        rng: &mut impl RngCore,
    ) -> Result<Self, String> {
        if !template.g2.is_empty() || !template.gt.is_empty() {
            return Err("prepared Sigma supports G1 representations only".into());
        }
        if witness.len() != template.vars || !template.shape() {
            return Err("malformed prepared Sigma template".into());
        }
        for bit in &template.bits {
            if (witness[bit.var] != S::ZERO && witness[bit.var] != S::ONE)
                || crate::ops::msm1(&[bit.g, bit.h], &[witness[bit.var], witness[bit.blind_var]])
                    != bit.commitment
            {
                return Err("false prepared bit opening".into());
            }
        }
        let nonces: Vec<_> = (0..template.vars).map(|_| S::random(&mut *rng)).collect();
        let mut powers = BTreeMap::new();
        for row in &template.g1 {
            for (index, base, _) in &row.terms {
                powers
                    .entry((*index, base.to_compressed()))
                    .or_insert_with(|| CachedPowers {
                        nonce: *base * nonces[*index],
                        witness: *base * witness[*index],
                    });
            }
        }
        let mut requested = BTreeMap::<usize, Vec<Vec<usize>>>::new();
        for (row, positions) in groups {
            let terms = &template
                .g1
                .get(*row)
                .ok_or("prepared group row out of bounds")?
                .terms;
            if positions.is_empty() || positions.iter().any(|&i| i >= terms.len()) {
                return Err("invalid prepared group positions".into());
            }
            requested.entry(*row).or_default().push(positions.clone());
        }
        let mut rows = Vec::with_capacity(template.g1.len());
        for (index, row) in template.g1.iter().enumerate() {
            let partitions = if let Some(mut partitions) = requested.remove(&index) {
                let mut covered = vec![false; row.terms.len()];
                for group in &partitions {
                    for &i in group {
                        if std::mem::replace(&mut covered[i], true) {
                            return Err("overlapping prepared term groups".into());
                        }
                    }
                }
                partitions.extend(
                    covered
                        .iter()
                        .enumerate()
                        .filter_map(|(i, present)| (!present).then_some(vec![i])),
                );
                partitions
            } else {
                (0..row.terms.len()).map(|i| vec![i]).collect()
            };
            let groups = partitions
                .into_iter()
                .map(|positions| {
                    if positions.len() == 1 {
                        let (variable, base, _) = row.terms[positions[0]];
                        let cached = &powers[&(variable, base.to_compressed())];
                        return CachedGroup {
                            positions,
                            pivot: None,
                            nonce: cached.nonce,
                            witness: cached.witness,
                        };
                    }
                    let mut nonce_points = Vec::with_capacity(positions.len());
                    let mut witness_points = Vec::with_capacity(positions.len());
                    let mut coefficients = Vec::with_capacity(positions.len());
                    for &i in &positions {
                        let (variable, base, coefficient) = row.terms[i];
                        let cached = &powers[&(variable, base.to_compressed())];
                        nonce_points.push(cached.nonce);
                        witness_points.push(cached.witness);
                        coefficients.push(coefficient);
                    }
                    CachedGroup {
                        pivot: positions.iter().copied().find_map(|i| {
                            (row.terms[i].2 != S::ZERO)
                                .then(|| (i, row.terms[i].2.invert().unwrap()))
                        }),
                        positions,
                        nonce: crate::ops::msm1(&nonce_points, &coefficients),
                        witness: crate::ops::msm1(&witness_points, &coefficients),
                    }
                })
                .collect();
            rows.push(CachedRow {
                terms: row.terms.clone(),
                groups,
            });
        }
        let mut bit_firsts = Vec::with_capacity(template.bits.len());
        let mut bit_states = Vec::with_capacity(template.bits.len());
        for bit in &template.bits {
            let real = usize::from(witness[bit.var] == S::ONE);
            let fake = 1 - real;
            let nonce = S::random(&mut *rng);
            let fake_c = S::random(&mut *rng);
            let fake_z = S::random(&mut *rng);
            let targets = [bit.commitment, bit.commitment - bit.g];
            let mut firsts = [G1::identity(); 2];
            firsts[real] = bit.h * nonce;
            firsts[fake] = crate::ops::msm1(&[bit.h, targets[fake]], &[fake_z, -fake_c]);
            bit_firsts.push([
                crate::ops::msm1(&[bit.g, bit.h], &[nonces[bit.var], nonces[bit.blind_var]]),
                firsts[0],
                firsts[1],
            ]);
            bit_states.push(BitState {
                real,
                nonce,
                fake_c,
                fake_z,
                opening: witness[bit.blind_var],
            });
        }
        Ok(Self {
            vars: template.vars,
            witness: witness.to_vec(),
            nonces,
            powers,
            rows,
            bit_relations: template.bits.clone(),
            bit_firsts,
            bit_states,
        })
    }

    /// No online fallback creates a nonce power for a previously unseen base.
    /// Actual satisfaction is checked with the witness powers cached offline.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn finish(
        self,
        actual: &Statement,
        domain: &[u8],
        external: &[u8],
        witness: &[S],
    ) -> Result<Proof, String> {
        if actual.vars != self.vars
            || witness != self.witness
            || actual.bits != self.bit_relations
            || !actual.g2.is_empty()
            || !actual.gt.is_empty()
        {
            return Err("prepared Sigma witness or statement shape changed".into());
        }
        let fixed_layout = actual.g1.len() == self.rows.len()
            && actual.g1.iter().zip(&self.rows).all(|(row, cached)| {
                row.terms.len() == cached.terms.len()
                    && row
                        .terms
                        .iter()
                        .zip(&cached.terms)
                        .all(|((i, base, _), (j, fixed, _))| i == j && base == fixed)
            });
        // Matching bases and indices were validated at preparation. Only row
        // targets vary here; do not repeat subgroup checks on every fixed
        // attribute base. A changed layout uses the complete original check.
        if if fixed_layout {
            actual.g1.iter().any(|row| !valid1(row.target))
        } else {
            !actual.shape()
        } {
            return Err("prepared Sigma statement rejected".into());
        }
        let mut firsts = Vec::with_capacity(actual.g1.len());
        for (row_index, row) in actual.g1.iter().enumerate() {
            let mut nonce_points = Vec::with_capacity(row.terms.len());
            let mut witness_points = Vec::with_capacity(row.terms.len());
            let mut scalars = Vec::with_capacity(row.terms.len());
            let individual = |i: usize| -> Result<(&CachedPowers, S), String> {
                let (index, base, coefficient) = &row.terms[i];
                let cached = self
                    .powers
                    .get(&(*index, base.to_compressed()))
                    .ok_or("online Sigma introduced an unprepared variable/base pair")?;
                Ok((cached, *coefficient))
            };
            if fixed_layout {
                let cached_row = &self.rows[row_index];
                for group in &cached_row.groups {
                    if group.positions.len() == 1 {
                        nonce_points.push(group.nonce);
                        witness_points.push(group.witness);
                        scalars.push(row.terms[group.positions[0]].2);
                    } else if let Some(factor) = group.factor(&cached_row.terms, &row.terms) {
                        nonce_points.push(group.nonce);
                        witness_points.push(group.witness);
                        scalars.push(factor);
                    } else {
                        for &i in &group.positions {
                            let (cached, coefficient) = individual(i)?;
                            nonce_points.push(cached.nonce);
                            witness_points.push(cached.witness);
                            scalars.push(coefficient);
                        }
                    }
                }
            } else {
                for i in 0..row.terms.len() {
                    let (cached, coefficient) = individual(i)?;
                    nonce_points.push(cached.nonce);
                    witness_points.push(cached.witness);
                    scalars.push(coefficient);
                }
            }
            let evaluate = |points: &[G1]| {
                if points.len() == 1 && scalars[0] == S::ONE {
                    points[0]
                } else {
                    crate::ops::msm1(points, &scalars)
                }
            };
            if evaluate(&witness_points) != row.target {
                return Err("false online Sigma representation".into());
            }
            firsts.push(evaluate(&nonce_points));
        }
        let c = actual.challenge(domain, external, &firsts, &[], &[], &self.bit_firsts);
        let response_span = crate::darlt::instrumentation::span("sigma_response");
        let field_span = crate::darlt::instrumentation::span("field_arithmetic");
        let z = self
            .nonces
            .iter()
            .zip(&self.witness)
            .map(|(nonce, secret)| *nonce + c * secret)
            .collect();
        let bits = self
            .bit_states
            .into_iter()
            .map(|state| {
                let real_c = c - state.fake_c;
                let real_z = state.nonce + real_c * state.opening;
                if state.real == 0 {
                    [real_c, real_z, state.fake_z]
                } else {
                    [state.fake_c, state.fake_z, real_z]
                }
            })
            .collect();
        drop(field_span);
        drop(response_span);
        Ok(Proof { c, z, bits })
    }
}

impl Statement {
    /// The joint statement is built privately from strictly decoded token
    /// points and installed public material. Arithmetic preserves membership;
    /// all structural and native nonidentity conditions still apply.
    pub(super) fn shape_received(&self, _: &super::spend::ReceivedInputs) -> bool {
        !(self.g1.is_empty() && self.g2.is_empty() && self.gt.is_empty() && self.bits.is_empty())
            && self.g1.iter().all(|row| {
                !row.terms.is_empty() && row.terms.iter().all(|(index, _, _)| *index < self.vars)
            })
            && self.g2.iter().all(|row| {
                !row.terms.is_empty() && row.terms.iter().all(|(index, _, _)| *index < self.vars)
            })
            && self.gt.iter().all(|row| {
                !row.terms.is_empty()
                    && row.target != Gt::default()
                    && row
                        .terms
                        .iter()
                        .all(|(index, point, _)| *index < self.vars && *point != Gt::default())
            })
            && self.bits.iter().all(|bit| {
                bit.var < self.vars
                    && bit.blind_var < self.vars
                    && bit.g != G1::identity()
                    && bit.h != G1::identity()
            })
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn new(vars: usize) -> Self {
        Self {
            vars,
            g1: vec![],
            g2: vec![],
            gt: vec![],
            bits: vec![],
        }
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn shape(&self) -> bool {
        if self.g1.is_empty() && self.g2.is_empty() && self.gt.is_empty() && self.bits.is_empty() {
            return false;
        }
        if self.g1.iter().any(|row| {
            row.terms.is_empty()
                || !valid1(row.target)
                || row
                    .terms
                    .iter()
                    .any(|(index, base, _)| *index >= self.vars || !valid1(*base))
        }) {
            return false;
        }
        if self.g2.iter().any(|row| {
            row.terms.is_empty()
                || !valid2(row.target)
                || row
                    .terms
                    .iter()
                    .any(|(index, base, _)| *index >= self.vars || !valid2(*base))
        }) {
            return false;
        }
        let mut checked_gt = Vec::new();
        for row in &self.gt {
            if row.terms.is_empty() || row.terms.iter().any(|(index, _, _)| *index >= self.vars) {
                return false;
            }
            for point in
                std::iter::once(row.target).chain(row.terms.iter().map(|(_, base, _)| *base))
            {
                if !checked_gt.contains(&point) {
                    if !valid_gt(point) {
                        return false;
                    }
                    checked_gt.push(point);
                }
            }
        }
        self.bits.iter().all(|bit| {
            bit.var < self.vars
                && bit.blind_var < self.vars
                && bit.g != G1::identity()
                && bit.h != G1::identity()
                && valid1(bit.g)
                && valid1(bit.h)
                && valid1(bit.commitment)
        })
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut out = Vec::new();
        out.extend((self.vars as u64).to_be_bytes());
        out.extend((self.g1.len() as u64).to_be_bytes());
        for row in &self.g1 {
            out.extend(row.target.to_compressed());
            out.extend((row.terms.len() as u64).to_be_bytes());
            for (index, base, coefficient) in &row.terms {
                out.extend((*index as u64).to_be_bytes());
                out.extend(base.to_compressed());
                out.extend(coefficient.to_bytes_be());
            }
        }
        out.extend((self.g2.len() as u64).to_be_bytes());
        for row in &self.g2 {
            out.extend(row.target.to_compressed());
            out.extend((row.terms.len() as u64).to_be_bytes());
            for (index, base, coefficient) in &row.terms {
                out.extend((*index as u64).to_be_bytes());
                out.extend(base.to_compressed());
                out.extend(coefficient.to_bytes_be());
            }
        }
        out.extend((self.gt.len() as u64).to_be_bytes());
        for row in &self.gt {
            out.extend(gt_bytes(row.target));
            out.extend((row.terms.len() as u64).to_be_bytes());
            for (index, base, coefficient) in &row.terms {
                out.extend((*index as u64).to_be_bytes());
                out.extend(gt_bytes(*base));
                out.extend(coefficient.to_bytes_be());
            }
        }
        out.extend((self.bits.len() as u64).to_be_bytes());
        for bit in &self.bits {
            out.extend((bit.var as u64).to_be_bytes());
            out.extend((bit.blind_var as u64).to_be_bytes());
            out.extend(bit.g.to_compressed());
            out.extend(bit.h.to_compressed());
            out.extend(bit.commitment.to_compressed());
        }
        out
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn satisfied(&self, witness: &[S]) -> bool {
        self.shape()
            && witness.len() == self.vars
            && self
                .g1
                .iter()
                .all(|row| eval1(&row.terms, witness) == row.target)
            && self
                .g2
                .iter()
                .all(|row| eval2(&row.terms, witness) == row.target)
            && self
                .gt
                .iter()
                .all(|row| evalt(&row.terms, witness) == row.target)
            && self.bits.iter().all(|bit| {
                (witness[bit.var] == S::ZERO || witness[bit.var] == S::ONE)
                    && crate::ops::msm1(
                        &[bit.g, bit.h],
                        &[witness[bit.var], witness[bit.blind_var]],
                    ) == bit.commitment
            })
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn challenge(
        &self,
        domain: &[u8],
        external: &[u8],
        first1: &[G1],
        first2: &[G2],
        firstt: &[Gt],
        bitfirsts: &[[G1; 3]],
    ) -> S {
        let _span = crate::darlt::instrumentation::span("fiat_shamir");
        let mut out = Vec::new();
        frame(&mut out, external);
        frame(&mut out, &self.encode());
        out.extend((first1.len() as u64).to_be_bytes());
        for point in first1 {
            out.extend(point.to_compressed());
        }
        out.extend((first2.len() as u64).to_be_bytes());
        for point in first2 {
            out.extend(point.to_compressed());
        }
        out.extend((firstt.len() as u64).to_be_bytes());
        for point in firstt {
            out.extend(gt_bytes(*point));
        }
        out.extend((bitfirsts.len() as u64).to_be_bytes());
        for firsts in bitfirsts {
            for point in firsts {
                out.extend(point.to_compressed());
            }
        }
        scalar_hash(domain, &out)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn prove(
        &self,
        domain: &[u8],
        external: &[u8],
        witness: &[S],
        rng: &mut impl RngCore,
    ) -> Result<Proof, String> {
        if !self.satisfied(witness) {
            return Err("false or malformed shared-witness statement".into());
        }
        let nonces: Vec<_> = (0..self.vars).map(|_| S::random(&mut *rng)).collect();
        let first1: Vec<_> = self
            .g1
            .iter()
            .map(|row| eval1(&row.terms, &nonces))
            .collect();
        let first2: Vec<_> = self
            .g2
            .iter()
            .map(|row| eval2(&row.terms, &nonces))
            .collect();
        let firstt: Vec<_> = self
            .gt
            .iter()
            .map(|row| evalt(&row.terms, &nonces))
            .collect();
        let mut states = Vec::with_capacity(self.bits.len());
        let mut bitfirsts = Vec::with_capacity(self.bits.len());
        for bit in &self.bits {
            let real = usize::from(witness[bit.var] == S::ONE);
            let fake = 1 - real;
            let nonce = S::random(&mut *rng);
            let fake_c = S::random(&mut *rng);
            let fake_z = S::random(&mut *rng);
            let targets = [bit.commitment, bit.commitment - bit.g];
            let mut firsts = [G1::identity(); 2];
            firsts[real] = bit.h * nonce;
            firsts[fake] = crate::ops::msm1(&[bit.h, targets[fake]], &[fake_z, -fake_c]);
            bitfirsts.push([
                crate::ops::msm1(&[bit.g, bit.h], &[nonces[bit.var], nonces[bit.blind_var]]),
                firsts[0],
                firsts[1],
            ]);
            states.push(BitState {
                real,
                nonce,
                fake_c,
                fake_z,
                opening: witness[bit.blind_var],
            });
        }
        let c = self.challenge(domain, external, &first1, &first2, &firstt, &bitfirsts);
        let response_span = crate::darlt::instrumentation::span("sigma_response");
        let field_span = crate::darlt::instrumentation::span("field_arithmetic");
        let z = nonces
            .iter()
            .zip(witness)
            .map(|(nonce, secret)| *nonce + c * secret)
            .collect();
        let bits = states
            .into_iter()
            .map(|state| {
                let real_c = c - state.fake_c;
                let real_z = state.nonce + real_c * state.opening;
                if state.real == 0 {
                    [real_c, real_z, state.fake_z]
                } else {
                    [state.fake_c, state.fake_z, real_z]
                }
            })
            .collect();
        drop(field_span);
        drop(response_span);
        Ok(Proof { c, z, bits })
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn verify(&self, domain: &[u8], external: &[u8], proof: &Proof) -> bool {
        if proof.z.len() != self.vars || proof.bits.len() != self.bits.len() || !self.shape() {
            return false;
        }
        self.verify_core(domain, external, proof)
    }
    pub(super) fn verify_received(
        &self,
        domain: &[u8],
        external: &[u8],
        proof: &Proof,
        received: &super::spend::ReceivedInputs,
    ) -> bool {
        if proof.z.len() != self.vars
            || proof.bits.len() != self.bits.len()
            || !self.shape_received(received)
        {
            return false;
        }
        self.verify_core(domain, external, proof)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn verify_core(&self, domain: &[u8], external: &[u8], proof: &Proof) -> bool {
        let first1: Vec<_> = self
            .g1
            .iter()
            .map(|row| {
                let mut points: Vec<_> = row.terms.iter().map(|(_, base, _)| *base).collect();
                let mut scalars = scalar_coefficients(&row.terms, &proof.z);
                points.push(row.target);
                scalars.push(-proof.c);
                crate::ops::msm1(&points, &scalars)
            })
            .collect();
        let first2: Vec<_> = self
            .g2
            .iter()
            .map(|row| {
                let mut points: Vec<_> = row.terms.iter().map(|(_, base, _)| *base).collect();
                let mut scalars = scalar_coefficients(&row.terms, &proof.z);
                points.push(row.target);
                scalars.push(-proof.c);
                crate::ops::msm2(&points, &scalars)
            })
            .collect();
        let firstt: Vec<_> = self
            .gt
            .iter()
            .map(|row| evalt(&row.terms, &proof.z) - row.target * proof.c)
            .collect();
        let bitfirsts: Vec<_> = self
            .bits
            .iter()
            .zip(&proof.bits)
            .map(|(bit, response)| {
                let c0 = response[0];
                let c1 = proof.c - c0;
                [
                    crate::ops::msm1(
                        &[bit.g, bit.h, bit.commitment],
                        &[proof.z[bit.var], proof.z[bit.blind_var], -proof.c],
                    ),
                    crate::ops::msm1(&[bit.h, bit.commitment], &[response[1], -c0]),
                    crate::ops::msm1(&[bit.h, bit.commitment - bit.g], &[response[2], -c1]),
                ]
            })
            .collect();
        self.challenge(domain, external, &first1, &first2, &firstt, &bitfirsts) == proof.c
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blstrs::{pairing, G2Projective as G2};
    use rand::{rngs::StdRng, SeedableRng};
    fn statement(bit_value: S) -> (Statement, Vec<S>) {
        let g = G1::generator();
        let h = G1::hash_to_curve(
            b"sigma-h",
            b"DARLT/Sigma/testing/BLS12381G1_XMD:SHA-256_SSWU_RO_",
            &[],
        );
        let gt = pairing(&g.to_affine(), &G2::generator().to_affine());
        let witness = vec![S::from(7), bit_value, S::from(19)];
        let mut statement = Statement::new(3);
        statement.g1.push(Eq1 {
            target: g * witness[0] + h * (S::from(3) * witness[1]),
            terms: vec![(0, g, S::ONE), (1, h, S::from(3))],
        });
        statement.g2.push(Eq2 {
            target: G2::generator() * (S::from(11) * witness[0]),
            terms: vec![(0, G2::generator(), S::from(11))],
        });
        statement.gt.push(EqT {
            target: gt * (S::from(5) * witness[0]),
            terms: vec![(0, gt, S::from(5))],
        });
        statement.bits.push(BitRelation {
            var: 1,
            blind_var: 2,
            g,
            h,
            commitment: g * bit_value + h * witness[2],
        });
        (statement, witness)
    }
    #[test]
    fn shared_g1_gt_and_both_bit_branches_round_trip() {
        let mut rng = StdRng::seed_from_u64(0x0001_8261);
        for bit in [S::ZERO, S::ONE] {
            let (statement, witness) = statement(bit);
            assert!(statement.shape());
            assert!(statement.satisfied(&witness));
            let proof = statement
                .prove(b"sigma-test", b"all-protocol-context", &witness, &mut rng)
                .unwrap();
            assert!(statement.verify(b"sigma-test", b"all-protocol-context", &proof));
            let bytes = proof.encode();
            assert_eq!(bytes.len(), 32 * (1 + 3 + 3));
            let parsed = Proof::decode(&bytes, 3, 1).unwrap();
            assert_eq!(parsed, proof);
            assert!(statement.verify(b"sigma-test", b"all-protocol-context", &parsed));
        }
    }
    #[test]
    fn every_response_and_external_transcript_are_bound() {
        let mut rng = StdRng::seed_from_u64(0x0001_8262);
        let (statement, witness) = statement(S::ONE);
        let proof = statement
            .prove(b"domain", b"context", &witness, &mut rng)
            .unwrap();
        assert!(!statement.verify(b"other-domain", b"context", &proof));
        assert!(!statement.verify(b"domain", b"other-context", &proof));
        let mut bad = proof.clone();
        bad.c += S::ONE;
        assert!(!statement.verify(b"domain", b"context", &bad));
        for index in 0..proof.z.len() {
            let mut bad = proof.clone();
            bad.z[index] += S::ONE;
            assert!(!statement.verify(b"domain", b"context", &bad));
        }
        for index in 0..3 {
            let mut bad = proof.clone();
            bad.bits[0][index] += S::ONE;
            assert!(!statement.verify(b"domain", b"context", &bad));
        }
        let mut bad = proof.clone();
        bad.z.pop();
        assert!(!statement.verify(b"domain", b"context", &bad));
        let mut bad = proof;
        bad.bits.clear();
        assert!(!statement.verify(b"domain", b"context", &bad));
    }
    #[test]
    fn raw_bases_coefficients_indexes_targets_and_bit_fields_are_bound() {
        let mut rng = StdRng::seed_from_u64(0x0001_8263);
        let (statement, witness) = statement(S::ONE);
        let proof = statement
            .prove(b"domain", b"external", &witness, &mut rng)
            .unwrap();
        for index in 0..9 {
            let mut changed = statement.clone();
            match index {
                0 => changed.g1[0].terms[0].1 += G1::generator(),
                1 => changed.g1[0].terms[0].2 += S::ONE,
                2 => changed.g1[0].terms[0].0 = 1,
                3 => changed.g1[0].target += G1::generator(),
                4 => changed.gt[0].terms[0].2 += S::ONE,
                5 => {
                    let base = changed.gt[0].terms[0].1;
                    changed.gt[0].target += base;
                }
                6 => changed.bits[0].commitment += G1::generator(),
                7 => changed.bits[0].g += G1::generator(),
                _ => changed.bits[0].blind_var = 0,
            }
            assert!(!changed.verify(b"domain", b"external", &proof));
        }
    }
    #[test]
    fn algebraically_equivalent_raw_representations_are_still_fs_bound() {
        let mut rng = StdRng::seed_from_u64(0x0001_8267);
        let (statement, witness) = statement(S::ONE);
        let proof = statement
            .prove(b"domain", b"external", &witness, &mut rng)
            .unwrap();
        let two = S::from(2);
        let half = Option::<S>::from(two.invert()).unwrap();
        let mut equivalent = statement.clone();
        equivalent.g1[0].terms[0].1 *= two;
        equivalent.g1[0].terms[0].2 *= half;
        assert!(equivalent.satisfied(&witness));
        assert!(!equivalent.verify(b"domain", b"external", &proof));
        let mut equivalent = statement.clone();
        equivalent.gt[0].terms[0].1 *= two;
        equivalent.gt[0].terms[0].2 *= half;
        assert!(equivalent.satisfied(&witness));
        assert!(!equivalent.verify(b"domain", b"external", &proof));
    }
    #[test]
    fn false_bit_and_false_linear_witnesses_are_rejected_before_proving() {
        let mut rng = StdRng::seed_from_u64(0x0001_8264);
        let (statement, witness) = statement(S::from(2));
        assert!(!statement.satisfied(&witness));
        assert!(statement.prove(b"d", b"e", &witness, &mut rng).is_err());
        let (statement, mut witness) = self::statement(S::ONE);
        witness[0] += S::ONE;
        assert!(statement.prove(b"d", b"e", &witness, &mut rng).is_err());
        let (statement, mut witness) = self::statement(S::ONE);
        witness[2] += S::ONE;
        assert!(statement.prove(b"d", b"e", &witness, &mut rng).is_err());
    }
    #[test]
    fn malformed_statement_and_scalar_encodings_are_rejected() {
        let mut rng = StdRng::seed_from_u64(0x0001_8265);
        let (mut statement, witness) = statement(S::ZERO);
        let proof = statement.prove(b"d", b"e", &witness, &mut rng).unwrap();
        assert!(Proof::decode(&proof.encode()[..31], 3, 1).is_err());
        let mut bytes = proof.encode();
        bytes[..32].fill(255);
        assert!(Proof::decode(&bytes, 3, 1).is_err());
        assert!(Proof::decode(&[], usize::MAX, usize::MAX).is_err());
        statement.g1[0].terms[0].0 = statement.vars;
        assert!(!statement.shape());
        assert!(!statement.verify(b"d", b"e", &proof));
        let (mut statement, _) = self::statement(S::ZERO);
        statement.gt[0].target = Gt::default();
        assert!(!statement.shape());
    }
    #[test]
    fn identity_gt_rows_and_zero_openings_are_safe() {
        assert_ne!(Gt::default(), Gt::identity());
        let gt = pairing(&G1::generator().to_affine(), &G2::generator().to_affine());
        assert!(valid_gt(gt));
        assert!(valid_gt(Gt::identity()));
        assert!(!valid_gt(Gt::default()));
        let mut st = Statement::new(1);
        st.gt.push(EqT {
            target: Gt::identity(),
            terms: vec![(0, gt, S::ONE)],
        });
        let mut rng = StdRng::seed_from_u64(0x0001_8266);
        let proof = st.prove(b"zero-gt", b"", &[S::ZERO], &mut rng).unwrap();
        assert!(st.verify(b"zero-gt", b"", &proof));
        assert_eq!(gt_bytes(Gt::identity()), vec![255; 288]);
    }
    #[test]
    fn g2_rows_have_shared_responses_and_complete_statement_binding() {
        let mut rng = StdRng::seed_from_u64(182305);
        let (st, w) = statement(S::ONE);
        let proof = st.prove(b"g2-shared", b"outer", &w, &mut rng).unwrap();
        assert!(st.verify(b"g2-shared", b"outer", &proof));
        for i in 0..4 {
            let mut altered = st.clone();
            match i {
                0 => altered.g2[0].target += G2::generator(),
                1 => altered.g2[0].terms[0].0 = 1,
                2 => altered.g2[0].terms[0].1 += G2::generator(),
                _ => altered.g2[0].terms[0].2 += S::ONE,
            }
            assert!(!altered.verify(b"g2-shared", b"outer", &proof));
        }
        let mut equivalent = st.clone();
        equivalent.g2[0].terms[0].1 *= S::from(2);
        equivalent.g2[0].terms[0].2 *= S::from(2).invert().unwrap();
        assert!(equivalent.satisfied(&w));
        assert!(!equivalent.verify(b"g2-shared", b"outer", &proof));
        let mut only = Statement::new(1);
        only.g2.push(Eq2 {
            target: G2::identity(),
            terms: vec![(0, G2::generator(), S::ONE)],
        });
        let p = only.prove(b"only-g2", b"", &[S::ZERO], &mut rng).unwrap();
        assert!(only.verify(b"only-g2", b"", &p));
        assert!(!only.satisfied(&[S::ONE]));
    }
}

#[cfg(test)]
mod prepared_tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    fn fixture() -> (Statement, Statement, Vec<S>) {
        let g = G1::generator();
        let h = G1::hash_to_curve(
            b"Sigma/prepare/h-point",
            b"DARLT/Sigma/testing/BLS12381G1_XMD:SHA-256_SSWU_RO_",
            &[],
        );
        let witness = vec![S::from(7), S::ONE, S::from(19)];
        let mut template = Statement::new(witness.len());
        template.g1.push(Eq1 {
            target: G1::identity(),
            terms: vec![(0, g, S::ZERO), (1, h, S::ZERO)],
        });
        template.bits.push(BitRelation {
            var: 1,
            blind_var: 2,
            g,
            h,
            commitment: crate::ops::msm1(&[g, h], &[witness[1], witness[2]]),
        });
        let mut actual = template.clone();
        actual.g1[0].terms[0].2 = S::from(29);
        actual.g1[0].terms[1].2 = S::from(43);
        actual.g1[0].target = eval1(&actual.g1[0].terms, &witness);
        (template, actual, witness)
    }

    #[test]
    fn grouped_fixed_terms_preserve_full_statement_and_proof_bytes() {
        let g = G1::generator();
        let witness: Vec<_> = (2..7).map(S::from).collect();
        let mut template = Statement::new(witness.len());
        template.g1.push(Eq1 {
            target: G1::identity(),
            terms: (0..5)
                .map(|i| (i, g * S::from((i + 1) as u64), S::ONE))
                .collect(),
        });
        let mut actual = template.clone();
        for (term, coefficient) in actual.g1[0].terms.iter_mut().zip([17, 17, 17, 23, 31]) {
            term.2 = S::from(coefficient);
        }
        actual.g1[0].target = eval1(&actual.g1[0].terms, &witness);
        let mut plain_rng = StdRng::seed_from_u64(214_004_111);
        let mut grouped_rng = plain_rng.clone();
        let plain = Prepared::new(&template, &witness, &mut plain_rng).unwrap();
        let grouped =
            Prepared::new_grouped(&template, &witness, &[(0, vec![0, 1, 2])], &mut grouped_rng)
                .unwrap();
        let a = plain.finish(&actual, b"same", b"ctx", &witness).unwrap();
        let b = grouped.finish(&actual, b"same", b"ctx", &witness).unwrap();
        assert_eq!(a.encode(), b.encode());
        assert!(actual.verify(b"same", b"ctx", &b));
        for groups in [
            vec![(0, vec![0, 0])],
            vec![(0, vec![0, 1]), (0, vec![1, 2])],
            vec![(1, vec![0])],
            vec![(0, vec![5])],
            vec![(0, vec![])],
        ] {
            assert!(Prepared::new_grouped(&template, &witness, &groups, &mut grouped_rng).is_err());
        }
        let mut false_actual = actual.clone();
        false_actual.g1[0].target += g;
        assert!(Prepared::new_grouped(
            &template,
            &witness,
            &[(0, vec![0, 1, 2])],
            &mut grouped_rng
        )
        .unwrap()
        .finish(&false_actual, b"same", b"ctx", &witness)
        .is_err());
    }

    #[test]
    fn zero_template_coefficients_can_become_nonzero_online() {
        let (template, actual, witness) = fixture();
        let mut rng = StdRng::seed_from_u64(0x2151);
        let p = Prepared::new(&template, &witness, &mut rng)
            .unwrap()
            .finish(&actual, b"sigma-proof", b"ctx-arrives-later", &witness)
            .unwrap();
        assert!(actual.verify(b"sigma-proof", b"ctx-arrives-later", &p));
        assert!(!actual.verify(b"sigma-proof", b"other-context", &p));
        let parsed = Proof::decode(&p.encode(), actual.vars, actual.bits.len()).unwrap();
        assert_eq!(p, parsed);
    }

    #[test]
    fn online_witness_shape_bases_and_bit_fields_cannot_change() {
        let (template, actual, witness) = fixture();
        let mut rng = StdRng::seed_from_u64(0x2152);
        let mut other_witness = witness.clone();
        other_witness[0] += S::ONE;
        assert!(Prepared::new(&template, &witness, &mut rng)
            .unwrap()
            .finish(&actual, b"domain", b"ctx", &other_witness)
            .is_err());
        for mutation in 0..7 {
            let mut changed = actual.clone();
            match mutation {
                0 => changed.g1[0].terms[0].1 += G1::generator(),
                1 => changed.g1[0].terms[0].0 = 2,
                2 => changed.vars += 1,
                3 => changed.bits[0].commitment += G1::generator(),
                4 => changed.bits[0].h += G1::generator(),
                5 => changed.bits[0].blind_var = 0,
                _ => changed.g1[0].target += G1::generator(),
            }
            assert!(Prepared::new(&template, &witness, &mut rng)
                .unwrap()
                .finish(&changed, b"domain", b"ctx", &witness)
                .is_err());
        }
    }

    #[test]
    fn prepared_rejects_non_g1_rows_and_false_bit_openings() {
        let (template, actual, witness) = fixture();
        let mut rng = StdRng::seed_from_u64(0x2153);
        let mut non_g1 = template.clone();
        non_g1.g2.push(Eq2 {
            target: G2::generator() * witness[0],
            terms: vec![(0, G2::generator(), S::ONE)],
        });
        assert!(Prepared::new(&non_g1, &witness, &mut rng).is_err());
        assert!(Prepared::new(&template, &witness[..2], &mut rng).is_err());
        let mut false_bit = witness.clone();
        false_bit[1] = S::from(2);
        assert!(Prepared::new(&template, &false_bit, &mut rng).is_err());
        let p = Prepared::new(&template, &witness, &mut rng).unwrap();
        assert!(p.finish(&non_g1, b"d", b"e", &witness).is_err());
        assert!(actual.satisfied(&witness));
    }

    #[cfg(feature = "op-counts")]
    #[test]
    fn online_prepared_work_and_verification_execute_real_msms() {
        let (template, actual, witness) = fixture();
        let mut rng = StdRng::seed_from_u64(0x2156);
        let prepared = Prepared::new(&template, &witness, &mut rng).unwrap();
        crate::ops::reset();
        let proof = prepared.finish(&actual, b"d", b"e", &witness).unwrap();
        let counts = crate::ops::stop();
        assert_eq!(counts.g1_exponentiations, 0);
        assert_eq!(counts.msm_g1_sizes, [2, 2]);
        crate::ops::reset();
        assert!(actual.verify(b"d", b"e", &proof));
        let counts = crate::ops::stop();
        assert_eq!(counts.g1_exponentiations, 0);
        assert_eq!(counts.msm_g1_sizes, [3, 3, 2, 2]);
    }
}
