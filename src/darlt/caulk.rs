//! Direct blstrs implementation of Caulk (CCS 2022), Figs.4--5.
//! Uses selected G2 opening advice and public powers only; never the trapdoor.
//! Ordinary (X-a) and partial (X^n-a) openings are batched separately.
use crate::{
    pairing_batch::{BatchResult, Equation},
    poly_ops as p,
    polynomial::{evaluate, Domain, S},
};
use blstrs::{G1Affine, G1Projective as G1, G2Affine, G2Projective as G2};
use ff::Field;
use group::Group;
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
pub const PROOF_BYTES: usize = 14 * 48 + 96 + 4 * 32;
pub const VERIFICATION_MILLER_TERMS: usize = 12;
pub const VERIFICATION_FINAL_EXPONENTIATIONS: usize = 6;
#[derive(Clone, Copy)]
pub struct CaulkView<'a> {
    pub domain: &'a Domain,
    pub n: usize,
    /// Full SRS degree; a verifier retains only G1 powers 0, 1 and 2.
    pub degree: usize,
    pub g1: &'a [G1],
    pub g2: &'a BTreeMap<usize, G2>,
}
impl CaulkView<'_> {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn commit(&self, poly: &[S]) -> Result<G1, String> {
        if poly.is_empty() || poly.len() > self.g1.len() {
            return Err("Caulk polynomial exceeds SRS degree".into());
        }
        Ok(crate::ops::msm1(&self.g1[..poly.len()], poly))
    }
    fn power(&self, j: usize) -> Result<G2, String> {
        self.g2
            .get(&j)
            .copied()
            .ok_or_else(|| format!("missing Caulk sparse G2 power {j}"))
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn shifted(&self, poly: &[S], shift: usize) -> Result<G1, String> {
        let end = shift.checked_add(poly.len()).ok_or("degree overflow")?;
        if end > self.g1.len() {
            return Err("Caulk shifted quotient exceeds SRS degree".into());
        }
        Ok(crate::ops::msm1(&self.g1[shift..end], poly))
    }
}
#[derive(Clone, Debug)]
pub struct Statement {
    pub table_commitment: G1,
    pub query_commitment: G1,
    /// K is the padded domain size, k is the actual query count.
    pub query_size: usize,
    pub actual_query_count: usize,
}
#[derive(Clone, Debug)]
pub struct Witness {
    /// Each vector has actual length k; padding copies position/value zero.
    pub positions: Vec<usize>,
    pub values: Vec<S>,
    pub query_blinder: S,
    pub table_openings_g2: Vec<G2>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub c_i: G1,
    pub z_i: G1,
    pub u: G1,
    pub h_2: G1,
    pub u_bar: G1,
    pub h_2_multi: G1,
    pub h_1: G1,
    pub u_bar_a: G1,
    pub h_2_a: G1,
    pub q_ord: G1,
    pub q_v: G1,
    pub q_part: G1,
    pub q_3: G1,
    pub q_b: G1,
    pub h_1_main: G2,
    pub v_1: S,
    pub v_2: S,
    pub v_2_prime: S,
    pub v_3_prime: S,
}
impl Proof {
    fn points(&self) -> [G1; 14] {
        [
            self.c_i,
            self.z_i,
            self.u,
            self.h_2,
            self.u_bar,
            self.h_2_multi,
            self.h_1,
            self.u_bar_a,
            self.h_2_a,
            self.q_ord,
            self.q_v,
            self.q_part,
            self.q_3,
            self.q_b,
        ]
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn to_bytes(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut out = Vec::with_capacity(PROOF_BYTES);
        for point in self.points() {
            out.extend(G1Affine::from(point).to_compressed());
        }
        out.extend(G2Affine::from(self.h_1_main).to_compressed());
        for scalar in [self.v_1, self.v_2, self.v_2_prime, self.v_3_prime] {
            out.extend(scalar.to_bytes_le());
        }
        out
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let _span = crate::darlt::instrumentation::span("strict_decoding");
        if bytes.len() != PROOF_BYTES {
            return Err("incorrect Caulk proof length".into());
        }
        let mut points = Vec::with_capacity(14);
        let mut at = 0;
        for _ in 0..14 {
            let _point_span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
            let raw: [u8; 48] = bytes[at..at + 48].try_into().unwrap();
            crate::subgroup_audit::decode("G1", &raw, "darlt/caulk/G1");
            at += 48;
            points.push(G1::from(
                Option::<G1Affine>::from(G1Affine::from_compressed(&raw))
                    .ok_or("invalid Caulk G1 encoding/subgroup")?,
            ));
        }
        let raw: [u8; 96] = bytes[at..at + 96].try_into().unwrap();
        crate::subgroup_audit::decode("G2", &raw, "darlt/caulk/G2");
        at += 96;
        let point_span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
        let h_1_main = G2::from(
            Option::<G2Affine>::from(G2Affine::from_compressed(&raw))
                .ok_or("invalid Caulk G2 encoding/subgroup")?,
        );
        drop(point_span);
        let mut scalars = Vec::with_capacity(4);
        for _ in 0..4 {
            let raw: [u8; 32] = bytes[at..at + 32].try_into().unwrap();
            at += 32;
            scalars.push(
                Option::<S>::from(S::from_bytes_le(&raw)).ok_or("noncanonical Caulk scalar")?,
            );
        }
        // The native verifier already requires a nonzero subset-polynomial
        // commitment. Other proof points can encode zero quotient polynomials.
        if points[1] == G1::identity() {
            return Err("zero Caulk subset-polynomial commitment".into());
        }
        Ok(Self {
            c_i: points[0],
            z_i: points[1],
            u: points[2],
            h_2: points[3],
            u_bar: points[4],
            h_2_multi: points[5],
            h_1: points[6],
            u_bar_a: points[7],
            h_2_a: points[8],
            q_ord: points[9],
            q_v: points[10],
            q_part: points[11],
            q_3: points[12],
            q_b: points[13],
            h_1_main,
            v_1: scalars[0],
            v_2: scalars[1],
            v_2_prime: scalars[2],
            v_3_prime: scalars[3],
        })
    }
}
#[derive(Clone)]
struct Transcript(Sha256);
impl Transcript {
    fn append(&mut self, label: &[u8], bytes: &[u8]) {
        let _span = crate::darlt::instrumentation::span("fiat_shamir_transcript");
        self.0.update((label.len() as u64).to_le_bytes());
        self.0.update(label);
        self.0.update((bytes.len() as u64).to_le_bytes());
        self.0.update(bytes);
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn g1(&mut self, l: &[u8], p: G1) {
        self.append(l, &G1Affine::from(p).to_compressed());
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn g2(&mut self, l: &[u8], p: G2) {
        self.append(l, &G2Affine::from(p).to_compressed());
    }
    fn scalar(&mut self, l: &[u8], s: S) {
        self.append(l, &s.to_bytes_le());
    }
    fn challenge(&mut self, label: &[u8], excluded: &[S]) -> S {
        let _span = crate::darlt::instrumentation::span("fiat_shamir");
        for counter in 0u64.. {
            let mut h = self.0.clone();
            h.update(b"Caulk/field-challenge");
            h.update((label.len() as u64).to_le_bytes());
            h.update(label);
            h.update(counter.to_le_bytes());
            let raw: [u8; 32] = h.finalize().into();
            if let Some(s) = Option::<S>::from(S::from_bytes_le(&raw)) {
                if !excluded.contains(&s) {
                    self.scalar(label, s);
                    return s;
                }
            }
        }
        unreachable!()
    }
    fn new(v: CaulkView<'_>, st: &Statement, prefix: &[u8]) -> Result<Self, String> {
        let _span = crate::darlt::instrumentation::span("fiat_shamir_transcript");
        if prefix.is_empty() {
            return Err("Caulk requires issuer/pp/role outer prefix".into());
        }
        let mut t = Self(Sha256::new());
        t.append(b"version", b"DARLT/Caulk/lookup-proof/v1");
        t.append(b"outer-statement-prefix", prefix);
        for (l, x) in [
            (b"W".as_slice(), v.domain.size),
            (b"n".as_slice(), v.n),
            (b"D".as_slice(), v.degree),
            (b"K".as_slice(), st.query_size),
            (b"k".as_slice(), st.actual_query_count),
        ] {
            t.append(l, &(x as u64).to_le_bytes());
        }
        t.g1(b"g1-base", v.g1[0]);
        t.g1(b"g1-tau", v.g1[1]);
        for j in powers(v) {
            t.append(b"G2-exponent", &(j as u64).to_le_bytes());
            t.g2(b"G2-power", v.power(j)?);
        }
        t.g1(b"table", st.table_commitment);
        t.g1(b"query", st.query_commitment);
        Ok(t)
    }
    fn first(&mut self, p: &Proof) -> S {
        self.g1(b"C_I", p.c_i);
        self.g1(b"z_I", p.z_i);
        self.g1(b"u", p.u);
        self.g2(b"H_1-main", p.h_1_main);
        self.g1(b"U_bar", p.u_bar);
        self.g1(b"h_2-multi", p.h_2_multi);
        self.challenge(b"xi", &[])
    }
    fn second(&mut self, p: &Proof) -> S {
        self.g1(b"H_2", p.h_2);
        self.challenge(b"a", &[])
    }
    fn third(&mut self, p: &Proof, sigma: S) -> S {
        self.g1(b"U_bar-a", p.u_bar_a);
        self.g1(b"h_2-a", p.h_2_a);
        self.g1(b"h_1", p.h_1);
        self.challenge(b"b", &[S::ZERO, S::ONE, sigma.invert().unwrap()])
    }
    fn weights(&mut self, p: &Proof) -> (S, S) {
        self.scalar(b"v_1", p.v_1);
        self.scalar(b"v_2", p.v_2);
        self.scalar(b"v_2-prime", p.v_2_prime);
        self.scalar(b"v_3-prime", p.v_3_prime);
        (
            self.challenge(b"d-ord", &[S::ZERO]),
            self.challenge(b"d-part", &[S::ZERO]),
        )
    }
}
fn powers(v: CaulkView<'_>) -> [usize; 7] {
    [0, 1, 2, 3, v.n, v.degree - v.n + 2, v.degree - v.n + 4]
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_g1(p: G1) -> bool {
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    let a = G1Affine::from(p);
    crate::subgroup_audit::g1(&p, "darlt/caulk/valid_g1");
    bool::from(a.is_on_curve() & a.is_torsion_free())
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_g2(p: G2) -> bool {
    let _span = crate::darlt::instrumentation::span("subgroup_check");
    let a = G2Affine::from(p);
    crate::subgroup_audit::g2(&p, "darlt/caulk/valid_g2");
    bool::from(a.is_on_curve() & a.is_torsion_free())
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn validate(v: CaulkView<'_>, st: &Statement) -> Result<S, String> {
    let sigma = validate_structure(v, st)?;
    for j in powers(v) {
        if !valid_g2(v.power(j)?) {
            return Err("invalid Caulk sparse G2 point".into());
        }
    }
    if !valid_g1(st.table_commitment)
        || !valid_g1(st.query_commitment)
        || !valid_g1(v.g1[0])
        || !valid_g1(v.g1[1])
    {
        return Err("invalid Caulk commitment/SRS generator".into());
    }
    Ok(sigma)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn validate_structure(v: CaulkView<'_>, st: &Statement) -> Result<S, String> {
    let k = st.actual_query_count;
    let padded = k
        .checked_next_power_of_two()
        .ok_or("Caulk query overflow")?;
    if k == 0
        || st.query_size != padded
        || v.n <= 6
        || !v.domain.size.is_power_of_two()
        || v.domain.size.checked_ilog2() != Some(v.n as u32)
        || v.degree.checked_add(1).is_none()
        || v.degree < v.domain.size
        || v.degree <= v.n + 2
        || v.g1.len() < 3
        || v.g1.len() > v.degree + 1
    {
        return Err("invalid Caulk table/query/SRS dimensions".into());
    }
    for j in powers(v) {
        v.power(j)?;
    }
    if v.g1[0] == G1::identity() || v.power(0)? == G2::identity() {
        return Err("invalid Caulk commitment/SRS generator".into());
    }
    super::params::nth_root(v.n)
}
/// Fourier Lagrange formula supports the non-binary n=11 domain.
fn unity_basis(n: usize, sigma: S) -> Result<Vec<p::Poly>, String> {
    let inv = Option::<S>::from(S::from(n as u64).invert()).ok_or("zero unity domain")?;
    let mut root = S::ONE;
    let mut basis = Vec::with_capacity(n);
    for _ in 0..n {
        let mut power = S::ONE;
        let mut q = Vec::with_capacity(n);
        for _ in 0..n {
            q.push(inv * power);
            power *= root;
        }
        basis.push(q);
        root *= sigma.invert().unwrap();
    }
    Ok(basis)
}
pub fn query_polynomial(values: &[S], blinder: S) -> Result<p::Poly, String> {
    if values.is_empty() {
        return Err("empty Caulk query".into());
    }
    let k = values
        .len()
        .checked_next_power_of_two()
        .ok_or("Caulk query overflow")?;
    let mut vals = values.to_vec();
    vals.resize(k, values[0]);
    let mut q = Domain::new(k)?.ifft(&vals)?;
    q[0] -= blinder;
    q.push(blinder);
    Ok(p::normalize(q))
}
fn exact(poly: &[S], divisor: &[S], context: &str) -> Result<p::Poly, String> {
    let (q, r) = p::div_rem(poly, divisor)?;
    if !p::is_zero(&r) {
        return Err(format!("Caulk nonzero remainder in {context}"));
    }
    Ok(q)
}
/// Bivariate polynomial: Y coefficient slots, each a polynomial in X.
type Bivariate = Vec<p::Poly>;
fn bivariate(polys: &[p::Poly], weights: &[p::Poly], n: usize) -> Bivariate {
    let mut out = vec![vec![S::ZERO]; n];
    for (q, weight) in polys.iter().zip(weights) {
        for (j, c) in weight.iter().enumerate() {
            out[j] = p::add(&out[j], &p::scale(q, *c));
        }
    }
    out
}
fn flatten(b: &Bivariate) -> p::Poly {
    let n = b.len();
    let len = b.iter().map(Vec::len).max().unwrap_or(1) * n;
    let mut out = vec![S::ZERO; len];
    for (j, q) in b.iter().enumerate() {
        for (i, c) in q.iter().enumerate() {
            out[i * n + j] += c;
        }
    }
    p::normalize(out)
}
fn partial(b: &Bivariate, a: S) -> p::Poly {
    p::normalize(b.iter().map(|q| evaluate(q, a)).collect())
}
fn partial_q(b: &Bivariate, a: S) -> p::Poly {
    flatten(&b.iter().map(|q| p::linear_quotient(q, a).1).collect())
}
fn blank() -> Proof {
    let g = G1::identity();
    Proof {
        c_i: g,
        z_i: g,
        u: g,
        h_2: g,
        u_bar: g,
        h_2_multi: g,
        h_1: g,
        u_bar_a: g,
        h_2_a: g,
        q_ord: g,
        q_v: g,
        q_part: g,
        q_3: g,
        q_b: g,
        h_1_main: G2::identity(),
        v_1: S::ZERO,
        v_2: S::ZERO,
        v_2_prime: S::ZERO,
        v_3_prime: S::ZERO,
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn prove(
    v: CaulkView<'_>,
    st: &Statement,
    w: &Witness,
    prefix: &[u8],
    rng: &mut impl RngCore,
) -> Result<Proof, String> {
    let sigma = validate(v, st)?;
    if v.g1.len() != v.degree + 1 {
        return Err("Caulk prover requires the complete G1 reference string".into());
    }
    let k = st.actual_query_count;
    if w.positions.len() != k || w.values.len() != k || w.table_openings_g2.len() != k {
        return Err("Caulk witness length differs from actual k".into());
    }
    let mut selected = BTreeMap::new();
    for j in 0..k {
        let pos = w.positions[j];
        let value = w.values[j];
        let opening = w.table_openings_g2[j];
        if pos >= v.domain.size || !valid_g2(opening) {
            return Err("invalid selected position/opening".into());
        }
        if let Some(&(old_value, old_opening)) = selected.get(&pos) {
            if old_value != value || old_opening != opening {
                return Err("inconsistent repeated Caulk position".into());
            }
        } else {
            selected.insert(pos, (value, opening));
        }
    }
    let phi = query_polynomial(&w.values, w.query_blinder)?;
    if v.commit(&phi)? != st.query_commitment {
        return Err("Caulk query opening mismatch".into());
    }
    let roots: Vec<S> = selected.keys().map(|i| v.domain.elements[*i]).collect();
    let values: Vec<S> = selected.values().map(|(x, _)| *x).collect();
    let a_i = p::product_roots(&roots)?;
    let c_i_0 = p::interpolate(&roots, &values)?;
    let mut weights = Vec::with_capacity(roots.len());
    for root in &roots {
        let (_, q) = p::linear_quotient(&a_i, *root);
        weights
            .push(Option::<S>::from(evaluate(&q, *root).invert()).ok_or("duplicate subset roots")?);
    }
    let advice: Vec<G2> = selected.values().map(|(_, q)| *q).collect();
    let q = crate::ops::msm2(&advice, &weights);
    let r_1 = loop {
        let r = S::random(&mut *rng);
        if r != S::ZERO {
            break r;
        }
    };
    let r_c: Vec<S> = (0..3).map(|_| S::random(&mut *rng)).collect();
    let r_u: Vec<S> = (0..3).map(|_| S::random(&mut *rng)).collect();
    let z_i = p::scale(&a_i, r_1);
    let c_i = p::add(&c_i_0, &p::mul(&z_i, &r_c)?);
    let small_g2: Vec<G2> = (0..3).map(|j| v.power(j)).collect::<Result<_, _>>()?;
    let h_1_main = q * r_1.invert().unwrap() - crate::ops::msm2(&small_g2, &r_c);
    let mut query_roots: Vec<S> = w.positions.iter().map(|i| v.domain.elements[*i]).collect();
    query_roots.resize(st.query_size, query_roots[0]);
    let kd = Domain::new(st.query_size)?;
    let z_k = p::vanishing(st.query_size);
    let u = p::add(&kd.ifft(&query_roots)?, &p::mul(&r_u, &z_k)?);
    let mut chain = vec![u.clone()];
    let mut vals = query_roots;
    // u_n=1 is fixed. Blinding is added only to intermediate chain items.
    for _ in 1..v.n {
        for x in &mut vals {
            *x = x.square();
        }
        chain.push(p::add(
            &kd.ifft(&vals)?,
            &p::scale(&z_k, S::random(&mut *rng)),
        ));
    }
    chain.push(vec![S::ONE]);
    let rho = unity_basis(v.n, sigma)?;
    let mut h_s = Vec::with_capacity(v.n);
    for j in 0..v.n {
        h_s.push(exact(
            &p::sub(&p::mul(&chain[j], &chain[j])?, &chain[j + 1]),
            &z_k,
            "square chain",
        )?);
    }
    let u_bar = bivariate(&chain[1..v.n], &rho[1..], v.n);
    let h_multi = bivariate(&h_s, &rho, v.n);
    let mut proof = blank();
    proof.c_i = v.commit(&c_i)?;
    proof.z_i = v.commit(&z_i)?;
    proof.u = v.commit(&u)?;
    proof.h_1_main = h_1_main;
    proof.u_bar = v.commit(&flatten(&u_bar))?;
    proof.h_2_multi = v.commit(&flatten(&h_multi))?;
    let mut transcript = Transcript::new(v, st, prefix)?;
    let xi = transcript.first(&proof);
    let p_1 = p::add(&z_i, &p::scale(&c_i, xi));
    let h_2 = exact(
        &p::sub(&p::compose(&p_1, &u)?, &p::scale(&phi, xi)),
        &z_k,
        "lookup composition",
    )?;
    proof.h_2 = v.commit(&h_2)?;
    let a = transcript.second(&proof);
    proof.v_1 = evaluate(&u, a);
    proof.v_2 = evaluate(&p_1, proof.v_1);
    let u_bar_a = partial(&u_bar, a);
    let h_2_a = partial(&h_multi, a);
    let u_a = p::add(&p::scale(&rho[0], proof.v_1), &u_bar_a);
    let mut squares = vec![S::ZERO];
    for (q, r) in chain[..v.n].iter().zip(&rho) {
        squares = p::add(&squares, &p::scale(r, evaluate(q, a).square()));
    }
    let h_1 = exact(
        &p::sub(&p::mul(&u_a, &u_a)?, &squares),
        &p::vanishing(v.n),
        "Y square chain",
    )?;
    proof.u_bar_a = v.commit(&u_bar_a)?;
    proof.h_2_a = v.commit(&h_2_a)?;
    proof.h_1 = v.commit(&h_1)?;
    let b = transcript.third(&proof, sigma);
    proof.v_2_prime = evaluate(&u_bar_a, b);
    proof.v_3_prime = evaluate(&u_bar_a, sigma * b);
    let (d_ord, d_part) = transcript.weights(&proof);
    let zka = evaluate(&z_k, a);
    let p_2 = p::sub(
        &p::sub(&[proof.v_2], &p::scale(&phi, xi)),
        &p::scale(&h_2, zka),
    );
    let (v1, q_u) = p::linear_quotient(&u, a);
    let (zero, q_p2) = p::linear_quotient(&p_2, a);
    if v1 != proof.v_1 || zero != S::ZERO {
        return Err("ordinary opening remainder".into());
    }
    proof.q_ord = v.commit(&p::add(&q_u, &p::scale(&q_p2, d_ord)))?;
    let (v2, q_v) = p::linear_quotient(&p_1, proof.v_1);
    if v2 != proof.v_2 {
        return Err("P1 opening mismatch".into());
    }
    proof.q_v = v.commit(&q_v)?;
    proof.q_part = v.commit(&p::add(
        &partial_q(&u_bar, a),
        &p::scale(&partial_q(&h_multi, a), d_part),
    ))?;
    let ell = p::interpolate(
        &[S::ONE, b, sigma * b],
        &[S::ZERO, proof.v_2_prime, proof.v_3_prime],
    )?;
    let z3 = p::product_roots(&[S::ONE, b, sigma * b])?;
    let q3 = exact(&p::sub(&u_bar_a, &ell), &z3, "three-point degree check")?;
    let d = v.degree;
    proof.q_3 = v.shifted(&q3, d - v.n + 4)?;
    let uu = proof.v_1 * evaluate(&rho[0], b) + proof.v_2_prime;
    let constant = uu.square() - proof.v_3_prime - evaluate(&rho[v.n - 1], b);
    let py = p::sub(
        &p::sub(
            &[constant],
            &p::scale(&h_1, b.pow_vartime([v.n as u64]) - S::ONE),
        ),
        &p::scale(&h_2_a, zka),
    );
    let (zero, qb) = p::linear_quotient(&py, b);
    if zero != S::ZERO {
        return Err("final unity relation does not vanish".into());
    }
    proof.q_b = v.shifted(&qb, d - v.n + 2)?;
    Ok(proof)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verification_equations(
    v: CaulkView<'_>,
    st: &Statement,
    proof: &Proof,
    prefix: &[u8],
) -> Result<Vec<Equation>, String> {
    let sigma = validate(v, st)?;
    if !proof.points().into_iter().all(valid_g1)
        || !valid_g2(proof.h_1_main)
        || proof.z_i == G1::identity()
    {
        return Err("invalid Caulk proof point/zero subset polynomial".into());
    }
    verification_equations_core(v, st, proof, prefix, sigma)
}
pub(super) fn verification_equations_received(
    v: CaulkView<'_>,
    st: &Statement,
    proof: &Proof,
    prefix: &[u8],
    _: &super::spend::ReceivedInputs,
) -> Result<Vec<Equation>, String> {
    let sigma = validate_structure(v, st)?;
    if proof.z_i == G1::identity() {
        return Err("invalid Caulk proof point/zero subset polynomial".into());
    }
    verification_equations_core(v, st, proof, prefix, sigma)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn verification_equations_core(
    v: CaulkView<'_>,
    st: &Statement,
    proof: &Proof,
    prefix: &[u8],
    sigma: S,
) -> Result<Vec<Equation>, String> {
    let mut t = Transcript::new(v, st, prefix)?;
    let xi = t.first(proof);
    let a = t.second(proof);
    let b = t.third(proof, sigma);
    let (d_ord, d_part) = t.weights(proof);
    let g1 = v.g1[0];
    let g2 = v.power(0)?;
    let zka = a.pow_vartime([st.query_size as u64]) - S::ONE;
    let p1 = crate::ops::msm1(&[proof.z_i, proof.c_i], &[S::ONE, xi]);
    let p2 = crate::ops::msm1(
        &[g1, st.query_commitment, proof.h_2],
        &[proof.v_2, -xi, -zka],
    );
    let ordinary = crate::ops::msm1(&[proof.u, g1, p2], &[S::ONE, -proof.v_1, d_ord]);
    let part = crate::ops::msm1(
        &[proof.u_bar, proof.u_bar_a, proof.h_2_multi, proof.h_2_a],
        &[S::ONE, -S::ONE, d_part, -d_part],
    );
    // Only rho_1 and rho_n are needed. The rejected b values make both
    // denominators nonzero; this avoids constructing an O(n^2) basis.
    let z_n_b = b.pow_vartime([v.n as u64]) - S::ONE;
    let inverse_n = S::from(v.n as u64).invert().unwrap();
    let last_root = sigma.invert().unwrap();
    let rho_first = z_n_b * inverse_n * (b - S::ONE).invert().unwrap();
    let rho_last = last_root * z_n_b * inverse_n * (b - last_root).invert().unwrap();
    let uu = proof.v_1 * rho_first + proof.v_2_prime;
    let constant = uu.square() - proof.v_3_prime - rho_last;
    let pp = crate::ops::msm1(&[g1, proof.h_1, proof.h_2_a], &[constant, -z_n_b, -zka]);
    let ell = p::interpolate(
        &[S::ONE, b, sigma * b],
        &[S::ZERO, proof.v_2_prime, proof.v_3_prime],
    )?;
    let z3 = p::product_roots(&[S::ONE, b, sigma * b])?;
    let small: Vec<G2> = (0..4).map(|j| v.power(j)).collect::<Result<_, _>>()?;
    let z3_cm = crate::ops::msm2(&small, &z3);
    let d = v.degree;
    let ga = crate::ops::msm2(&[v.power(1)?, g2], &[S::ONE, -a]);
    let gv = crate::ops::msm2(&[v.power(1)?, g2], &[S::ONE, -proof.v_1]);
    let gn = crate::ops::msm2(&[v.power(v.n)?, g2], &[S::ONE, -a]);
    let gb = crate::ops::msm2(&[v.power(1)?, g2], &[S::ONE, -b]);
    Ok(vec![
        vec![
            (st.table_commitment - proof.c_i, g2),
            (-proof.z_i, proof.h_1_main),
        ],
        vec![(ordinary, g2), (-proof.q_ord, ga)],
        vec![(p1 - g1 * proof.v_2, g2), (-proof.q_v, gv)],
        vec![(part, g2), (-proof.q_part, gn)],
        vec![
            (proof.u_bar_a - v.commit(&ell)?, v.power(d - v.n + 4)?),
            (-proof.q_3, z3_cm),
        ],
        vec![(pp, v.power(d - v.n + 2)?), (-proof.q_b, gb)],
    ])
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verify_each(
    v: CaulkView<'_>,
    st: &Statement,
    proof: &Proof,
    prefix: &[u8],
) -> Result<BatchResult, String> {
    crate::pairing_batch::verify_each(&verification_equations(v, st, proof, prefix)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::darlt::params::ReferenceString;
    use rand::{rngs::StdRng, SeedableRng};

    const PREFIX: &[u8] = b"tests|pp-digest-A|issuer-A|seed-role|outer-fixed-statement";
    fn view(pp: &ReferenceString) -> CaulkView<'_> {
        CaulkView {
            domain: &pp.domain,
            n: pp.n,
            degree: pp.degree,
            g1: &pp.g1,
            g2: &pp.g2,
        }
    }
    fn fixture(pp: &ReferenceString, positions: &[usize]) -> (Statement, Witness) {
        let seeds: Vec<S> = (0..pp.w).map(|i| S::from((i * 13) as u64)).collect();
        let rho = S::from(17);
        let mut table_values = seeds.clone();
        table_values.resize(pp.domain.size, S::ZERO);
        let mut coefficients = pp.domain.ifft(&table_values).unwrap();
        coefficients[0] -= rho;
        coefficients.push(rho);
        let v = view(pp);
        let values: Vec<S> = positions.iter().map(|i| seeds[*i]).collect();
        let query_blinder = S::from(31);
        let statement = Statement {
            table_commitment: v.commit(&coefficients).unwrap(),
            query_commitment: v
                .commit(&query_polynomial(&values, query_blinder).unwrap())
                .unwrap(),
            query_size: positions.len().next_power_of_two(),
            actual_query_count: positions.len(),
        };
        let witness = Witness {
            positions: positions.to_vec(),
            values,
            query_blinder,
            table_openings_g2: positions
                .iter()
                .map(|i| pp.parent_opening(*i, &seeds, rho).unwrap())
                .collect(),
        };
        (statement, witness)
    }
    fn accepted(pp: &ReferenceString, statement: &Statement, proof: &Proof, prefix: &[u8]) -> bool {
        verify_each(view(pp), statement, proof, prefix)
            .map(|r| r.accepted)
            .unwrap_or(false)
    }
    #[test]
    fn valid_lookup_padding_repetition_zero_value_and_native_counts() {
        let mut rng = StdRng::seed_from_u64(202_021_400);
        let pp = ReferenceString::new(4, 4, 8, G1::generator(), &mut rng).unwrap();
        assert_eq!(pp.n, 8);
        for positions in [
            vec![0],
            vec![3, 0, 3],
            vec![0, 1, 1, 2, 3, 0, 2],
            vec![0, 1, 2, 3, 0, 1, 2, 3],
        ] {
            let (statement, witness) = fixture(&pp, &positions);
            let proof = prove(view(&pp), &statement, &witness, PREFIX, &mut rng).unwrap();
            let result = verify_each(view(&pp), &statement, &proof, PREFIX).unwrap();
            assert!(result.accepted);
            assert_eq!(result.equations, 6);
            assert_eq!(result.executed_miller_terms, 12);
            assert_eq!(result.final_exponentiations, 6);
            assert_eq!(proof.to_bytes().len(), 896);
            assert_eq!(Proof::from_bytes(&proof.to_bytes()).unwrap(), proof);
            let equation_sizes: Vec<_> =
                verification_equations(view(&pp), &statement, &proof, PREFIX)
                    .unwrap()
                    .iter()
                    .map(Vec::len)
                    .collect();
            assert_eq!(equation_sizes, vec![2; 6]);
        }
    }
    #[test]
    fn every_proof_group_and_scalar_field_is_bound() {
        let mut rng = StdRng::seed_from_u64(202_021_401);
        let pp = ReferenceString::new(4, 4, 8, G1::generator(), &mut rng).unwrap();
        let (statement, witness) = fixture(&pp, &[0, 1, 2, 3, 1, 1, 0]);
        let proof = prove(view(&pp), &statement, &witness, PREFIX, &mut rng).unwrap();
        let bytes = proof.to_bytes();
        for (j, point) in proof.points().iter().enumerate() {
            let mut changed = bytes.clone();
            changed[j * 48..(j + 1) * 48]
                .copy_from_slice(&G1Affine::from(*point + G1::generator()).to_compressed());
            let altered = Proof::from_bytes(&changed).unwrap();
            assert!(!accepted(&pp, &statement, &altered, PREFIX), "G1 field {j}");
        }
        let mut altered = proof.clone();
        altered.h_1_main += G2::generator();
        assert!(!accepted(&pp, &statement, &altered, PREFIX), "G2 field");
        for j in 0..4 {
            let mut altered = proof.clone();
            let fields = [
                &mut altered.v_1,
                &mut altered.v_2,
                &mut altered.v_2_prime,
                &mut altered.v_3_prime,
            ];
            *fields.into_iter().nth(j).unwrap() += S::ONE;
            assert!(
                !accepted(&pp, &statement, &altered, PREFIX),
                "scalar field {j}"
            );
        }
        let mut altered = proof.clone();
        altered.z_i = G1::identity();
        assert!(!accepted(&pp, &statement, &altered, PREFIX));
    }
    #[test]
    fn issuer_role_statement_and_private_input_mismatches_fail() {
        let mut rng = StdRng::seed_from_u64(202_021_402);
        let pp = ReferenceString::new(4, 4, 8, G1::generator(), &mut rng).unwrap();
        let (statement, witness) = fixture(&pp, &[0, 2, 2]);
        let proof = prove(view(&pp), &statement, &witness, PREFIX, &mut rng).unwrap();
        for prefix in [
            b"tests|pp-digest-A|issuer-B|seed-role|outer-fixed-statement".as_slice(),
            b"tests|pp-digest-A|issuer-A|offset-role|outer-fixed-statement".as_slice(),
            b"tests|pp-digest-B|issuer-A|seed-role|outer-fixed-statement".as_slice(),
            b"".as_slice(),
        ] {
            assert!(!accepted(&pp, &statement, &proof, prefix));
        }
        let mut changed = statement.clone();
        changed.table_commitment += G1::generator();
        assert!(!accepted(&pp, &changed, &proof, PREFIX));
        changed = statement.clone();
        changed.query_commitment += G1::generator();
        assert!(!accepted(&pp, &changed, &proof, PREFIX));
        changed = statement.clone();
        changed.actual_query_count = 4;
        assert!(!accepted(&pp, &changed, &proof, PREFIX));
        let mut bad = witness.clone();
        bad.positions[0] = pp.domain.size;
        assert!(prove(view(&pp), &statement, &bad, PREFIX, &mut rng).is_err());
        bad = witness.clone();
        bad.values[0] += S::ONE;
        assert!(prove(view(&pp), &statement, &bad, PREFIX, &mut rng).is_err());
        bad = witness.clone();
        bad.values[2] += S::ONE;
        assert!(prove(view(&pp), &statement, &bad, PREFIX, &mut rng).is_err());
        // Wrong but well-formed quotient advice must not yield an accepted proof.
        bad = witness.clone();
        bad.table_openings_g2[0] += G2::generator();
        let altered = prove(view(&pp), &statement, &bad, PREFIX, &mut rng).unwrap();
        assert!(!accepted(&pp, &statement, &altered, PREFIX));
    }
    #[test]
    fn canonical_codec_rejects_wrong_lengths_points_and_scalars() {
        let mut rng = StdRng::seed_from_u64(202_021_403);
        let pp = ReferenceString::new(4, 4, 4, G1::generator(), &mut rng).unwrap();
        let (statement, witness) = fixture(&pp, &[1]);
        let proof = prove(view(&pp), &statement, &witness, PREFIX, &mut rng).unwrap();
        let bytes = proof.to_bytes();
        assert!(Proof::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        let mut long = bytes.clone();
        long.push(0);
        assert!(Proof::from_bytes(&long).is_err());
        for j in 0..14 {
            let mut bad = bytes.clone();
            bad[j * 48..(j + 1) * 48].fill(0xff);
            assert!(Proof::from_bytes(&bad).is_err());
        }
        let mut bad = bytes.clone();
        bad[14 * 48..14 * 48 + 96].fill(0xff);
        assert!(Proof::from_bytes(&bad).is_err());
        for j in 0..4 {
            let mut bad = bytes.clone();
            bad[14 * 48 + 96 + j * 32..14 * 48 + 96 + (j + 1) * 32].fill(0xff);
            assert!(Proof::from_bytes(&bad).is_err());
        }
    }
    #[test]
    fn partial_divisor_and_n11_unity_basis_are_not_binary_domain_shortcuts() {
        let sigma = super::super::params::nth_root(11).unwrap();
        let rho = unity_basis(11, sigma).unwrap();
        let mut x = S::ONE;
        for row in 0..11 {
            for (j, poly) in rho.iter().enumerate() {
                assert_eq!(evaluate(poly, x), if row == j { S::ONE } else { S::ZERO });
            }
            x *= sigma;
        }
        let coefficients: Bivariate = (0..11)
            .map(|j| {
                (0..4)
                    .map(|i| S::from((3 * j + 7 * i + 1) as u64))
                    .collect()
            })
            .collect();
        let a = S::from(19);
        let mut divisor = vec![S::ZERO; 12];
        divisor[0] = -a;
        divisor[11] = S::ONE;
        let numerator = p::sub(&flatten(&coefficients), &partial(&coefficients, a));
        assert_eq!(
            exact(&numerator, &divisor, "partial identity").unwrap(),
            partial_q(&coefficients, a)
        );
        assert!(exact(&numerator, &[-a, S::ONE], "wrong ordinary divisor").is_err());
    }
    #[test]
    fn n11_full_proof_uses_only_the_sparse_public_reference_string() {
        let mut rng = StdRng::seed_from_u64(202_021_404);
        let pp = ReferenceString::new(512, 16, 4, G1::generator(), &mut rng).unwrap();
        assert_eq!(pp.n, 11);
        assert_eq!(pp.g2.len(), 7);
        let (statement, witness) = fixture(&pp, &[0, 256, 511]);
        let proof = prove(view(&pp), &statement, &witness, PREFIX, &mut rng).unwrap();
        assert!(accepted(&pp, &statement, &proof, PREFIX));
    }
    #[cfg(feature = "op-counts")]
    #[test]
    fn backend_operation_counter_agrees_with_six_equations() {
        let mut rng = StdRng::seed_from_u64(202_021_405);
        let pp = ReferenceString::new(4, 4, 8, G1::generator(), &mut rng).unwrap();
        let (statement, witness) = fixture(&pp, &[0, 1, 2, 3, 1, 1, 0]);
        let proof = prove(view(&pp), &statement, &witness, PREFIX, &mut rng).unwrap();
        crate::ops::reset();
        let result = verify_each(view(&pp), &statement, &proof, PREFIX).unwrap();
        let counts = crate::ops::stop();
        assert!(result.accepted);
        assert_eq!(counts.miller_loop_terms, 12);
        assert_eq!(counts.miller_loop_calls, 6);
        assert_eq!(counts.final_exponentiations, 6);
    }
    #[test]
    fn default_sixty_four_distinct_queries_fit_exact_unrounded_degree() {
        let mut rng = StdRng::seed_from_u64(202_021_406);
        let pp = ReferenceString::new(64, 16, 64, G1::generator(), &mut rng).unwrap();
        assert_eq!(pp.degree, 4292);
        let positions: Vec<usize> = (0..64).collect();
        let (statement, witness) = fixture(&pp, &positions);
        let proof = prove(view(&pp), &statement, &witness, PREFIX, &mut rng).unwrap();
        assert!(accepted(&pp, &statement, &proof, PREFIX));
    }
}
