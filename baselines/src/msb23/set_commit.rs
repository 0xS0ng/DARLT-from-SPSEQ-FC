//! MSB23 Appendix B polynomial set commitments and across-set aggregation.
//!
//! The profile uses canonical, nonempty sets of distinct field elements. Public
//! parameters contain powers 0..=t, so t is a cardinality/degree bound, not a
//! number of SRS entries. Call `validate_params` once when installing parameters;
//! hot-path functions check shape and their own inputs, not the whole SRS again.
//! Aggregation binds the index and the ordered commitment/disclosed-set list.
//! ordered (commitment, disclosed set) list, as required by the printed paper.

use crate::arithmetic::*;
use ff::Field;
use group::Group;
use rand::RngCore;

pub type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
pub struct Params {
    pub srs1: Vec<G1>,
    pub srs2: Vec<G2>,
    pub max_cardinality: usize,
}

pub fn setup(t: usize, rng: &mut impl RngCore) -> (Params, S) {
    assert!(t > 0 && t < usize::MAX, "positive finite degree bound");
    // Zero alpha makes all positive SRS powers identities. This explicit
    // implementation profile samples from Fr* and rejects degenerate sets.
    let alpha = random_nonzero(rng);
    let mut power = S::ONE;
    let mut srs1 = Vec::with_capacity(t + 1);
    let mut srs2 = Vec::with_capacity(t + 1);
    for _ in 0..=t {
        srs1.push(g1_mul(G1::generator(), power));
        srs2.push(g2_mul(G2::generator(), power));
        power *= alpha;
    }
    (
        Params {
            srs1,
            srs2,
            max_cardinality: t,
        },
        alpha,
    )
}

fn valid_shape(p: &Params) -> bool {
    p.max_cardinality > 0
        && p.max_cardinality.checked_add(1) == Some(p.srs1.len())
        && p.srs1.len() == p.srs2.len()
}

/// Full, deterministic SRS validation. No aggregate equation susceptible to
/// cancellation is substituted for the individual power relations.
pub fn validate_params(p: &Params) -> bool {
    if !valid_shape(p)
        || p.srs1[0] != G1::generator()
        || p.srs2[0] != G2::generator()
        || p.srs1.iter().any(|&x| !valid1(x, true))
        || p.srs2.iter().any(|&x| !valid2(x, true))
    {
        return false;
    }
    validate_power_relations(p)
}
/// Canonical decoder checked every actual SRS point before owning this value.
/// Only the installed protocol's sealed registration continuation uses this.
pub(crate) fn validate_params_decoded(p: &Params) -> bool {
    if !valid_shape(p)
        || p.srs1[0] != G1::generator()
        || p.srs2[0] != G2::generator()
        || p.srs1.iter().any(|p| *p == G1::identity())
        || p.srs2.iter().any(|p| *p == G2::identity())
    {
        return false;
    }
    validate_power_relations(p)
}
fn validate_power_relations(p: &Params) -> bool {
    for i in 1..p.srs1.len() {
        if multi_pair(&[(p.srs1[i], G2::generator()), (-G1::generator(), p.srs2[i])])
            != GT::identity()
            || multi_pair(&[(p.srs1[i], G2::generator()), (-p.srs1[i - 1], p.srs2[1])])
                != GT::identity()
        {
            return false;
        }
    }
    true
}

/// Canonical order is lexicographic order of 32-byte big-endian Fr encodings.
/// This predicate rejects duplicates rather than silently changing a set.
pub fn validate_set(p: &Params, set: &[S]) -> bool {
    valid_shape(p)
        && !set.is_empty()
        && set.len() <= p.max_cardinality
        && set
            .windows(2)
            .all(|w| w[0].to_bytes_be() < w[1].to_bytes_be())
}

/// Coefficients in ascending degree order of product(X - a), including the
/// constant polynomial one for the empty difference set.
pub fn polynomial_coefficients(roots: &[S]) -> Vec<S> {
    let mut out = vec![S::ONE];
    for &root in roots {
        let mut next = vec![S::ZERO; out.len() + 1];
        for (i, &v) in out.iter().enumerate() {
            next[i] -= root * v;
            next[i + 1] += v;
        }
        out = next;
    }
    out
}

pub fn evaluate_g1(p: &Params, coefficients: &[S]) -> Result<G1> {
    if !valid_shape(p) || coefficients.is_empty() || coefficients.len() > p.srs1.len() {
        return Err("G1 polynomial exceeds installed SRS degree".into());
    }
    Ok(sum1(
        &p.srs1
            .iter()
            .copied()
            .zip(coefficients.iter().copied())
            .collect::<Vec<_>>(),
    ))
}

pub fn evaluate_g2(p: &Params, coefficients: &[S]) -> Result<G2> {
    if !valid_shape(p) || coefficients.is_empty() || coefficients.len() > p.srs2.len() {
        return Err("G2 polynomial exceeds installed SRS degree".into());
    }
    Ok(sum2(
        &p.srs2
            .iter()
            .copied()
            .zip(coefficients.iter().copied())
            .collect::<Vec<_>>(),
    ))
}

pub fn commit(p: &Params, set: &[S], rho: S) -> Result<G1> {
    if !validate_set(p, set) || rho == S::ZERO {
        return Err("nonempty canonical set and nonzero opening required".into());
    }
    let c = g1_mul(evaluate_g1(p, &polynomial_coefficients(set))?, rho);
    if !valid1(c, true) {
        return Err("degenerate set commitment".into());
    }
    Ok(c)
}

/// Fig. 2 blind root commitment: the issuer knows alpha, but receives only
/// P^rho. The alpha/SRS relationship is established at setup/registration.
pub fn commit_blind(p: &Params, set: &[S], alpha: S, prho: G1) -> Result<G1> {
    if !validate_set(p, set) || alpha == S::ZERO || !valid1(prho, true) {
        return Err("invalid blind commitment input".into());
    }
    let value = set.iter().fold(S::ONE, |v, &a| v * (alpha - a));
    let c = g1_mul(prho, value);
    if !valid1(c, true) {
        return Err("degenerate blind commitment".into());
    }
    Ok(c)
}

#[allow(clippy::unnecessary_map_or)]
pub fn open(p: &Params, commitment: G1, set: &[S], rho: S) -> bool {
    valid1(commitment, true) && commit(p, set, rho).map_or(false, |c| c == commitment)
}

fn difference(set: &[S], subset: &[S]) -> Option<Vec<S>> {
    // Inputs are already canonical; a merge checks every member, unlike the
    // author Python membership helper which overwrites its previous result.
    let mut j = 0;
    let mut out = Vec::with_capacity(set.len());
    for &a in set {
        if j < subset.len() && a == subset[j] {
            j += 1;
        } else {
            out.push(a);
        }
    }
    (j == subset.len()).then_some(out)
}

/// Includes the full opening check required by Appendix B OpenSubset. The
/// printed line omits a negation before Open; successful Open is required here.
pub fn subset_witness(p: &Params, commitment: G1, set: &[S], rho: S, subset: &[S]) -> Result<G1> {
    if !validate_set(p, subset) || !open(p, commitment, set, rho) {
        return Err("invalid set opening or disclosed subset".into());
    }
    let diff = difference(set, subset).ok_or("disclosed set is not a subset")?;
    let w = g1_mul(evaluate_g1(p, &polynomial_coefficients(&diff))?, rho);
    if !valid1(w, true) {
        return Err("degenerate subset witness".into());
    }
    Ok(w)
}

/// Private capability produced only by a successful full opening check.
pub(crate) struct OpenedSet {
    set: Vec<S>,
    rho: S,
}

pub fn verify_subset(p: &Params, commitment: G1, subset: &[S], witness: G1) -> bool {
    if !validate_set(p, subset) || !valid1(commitment, true) || !valid1(witness, true) {
        return false;
    }
    let q = match evaluate_g2(p, &polynomial_coefficients(subset)) {
        Ok(q) if valid2(q, true) => q,
        _ => return false,
    };
    multi_pair(&[(witness, q), (-commitment, G2::generator())]) == GT::identity()
}

fn aggregate_inputs(p: &Params, cs: &[G1], ds: &[Vec<S>]) -> Result<Vec<S>> {
    if cs.is_empty()
        || cs.len() != ds.len()
        || cs.iter().any(|&c| !valid1(c, true))
        || ds.iter().any(|d| !validate_set(p, d))
    {
        return Err("invalid across-set input shape or disclosure".into());
    }
    let mut union: Vec<S> = ds.iter().flatten().copied().collect();
    union.sort_by_key(|s| s.to_bytes_be());
    union.dedup();
    if union.len() > p.max_cardinality {
        return Err("disclosure union exceeds installed SRS degree".into());
    }
    Ok(union)
}

/// Exact experimental encoding of H(j, {(C_i,T_i)}): fixed domain, one-based
/// index, list length, then each compressed C and length-prefixed canonical set.
/// Every weight binds the complete ordered statement, not just its own C_j.
pub fn aggregation_weights(p: &Params, cs: &[G1], ds: &[Vec<S>]) -> Result<Vec<S>> {
    aggregate_inputs(p, cs, ds)?;
    Ok(weights_body(cs, ds))
}
fn weights_body(cs: &[G1], ds: &[Vec<S>]) -> Vec<S> {
    let encoded: Vec<_> = cs.iter().map(|&c| enc1(c)).collect();
    weights_encoded(&encoded.iter().map(Vec::as_slice).collect::<Vec<_>>(), ds)
}
fn weights_encoded(cs: &[&[u8]], ds: &[Vec<S>]) -> Vec<S> {
    let mut common = Vec::new();
    common.extend((cs.len() as u64).to_be_bytes());
    for (&c, d) in cs.iter().zip(ds) {
        common.extend(c);
        common.extend((d.len() as u64).to_be_bytes());
        for &x in d {
            common.extend(encs(x));
        }
    }
    (1..=cs.len())
        .map(|index| {
            let mut input = Vec::with_capacity(8 + common.len());
            input.extend((index as u64).to_be_bytes());
            input.extend(&common);
            hash_scalar(b"\x53\x50\x53\x45\x51\x5f\x55\x43\x5f\x43\x53\x43\x41\x5f\x41\x43\x52\x4f\x53\x53\x5f\x56\x32", &input)
        })
        .collect()
}

// These continuations require the privately owned Registered SRS. Callers are
// the installed protocol, after ingress validation or from opaque holder state.
// Public generic APIs retain their original dynamic-input/result checks.
// Mutable generic Params still requires validate_params at installation.
use super::scheme::Registered;
pub(crate) fn commit_local(v: &Registered, set: &[S], rho: S) -> Result<G1> {
    let p = &v.pp.sc;
    if !validate_set(p, set) || rho == S::ZERO {
        return Err("invalid local commitment input".into());
    }
    let c = g1_mul(evaluate_g1(p, &polynomial_coefficients(set))?, rho);
    if c == G1::identity() {
        return Err("degenerate set commitment".into());
    }
    Ok(c)
}
pub(crate) fn commit_blind_checked(v: &Registered, set: &[S], alpha: S, prho: G1) -> Result<G1> {
    if !validate_set(&v.pp.sc, set) || alpha == S::ZERO || prho == G1::identity() {
        return Err("invalid checked blind input".into());
    }
    let value = set.iter().fold(S::ONE, |x, &a| x * (alpha - a));
    let c = g1_mul(prho, value);
    if c == G1::identity() {
        return Err("degenerate blind commitment".into());
    }
    Ok(c)
}
#[allow(clippy::unnecessary_map_or)]
pub(crate) fn open_checked(v: &Registered, c: G1, set: &[S], rho: S) -> bool {
    c != G1::identity() && commit_local(v, set, rho).map_or(false, |expected| expected == c)
}
pub(crate) fn prepare_open_local(v: &Registered, c: G1, set: &[S], rho: S) -> Result<OpenedSet> {
    if !open_checked(v, c, set, rho) {
        return Err("full opening check rejected".into());
    }
    Ok(OpenedSet {
        set: set.to_vec(),
        rho,
    })
}
pub(crate) fn subset_local(v: &Registered, o: &OpenedSet, subset: &[S]) -> Result<G1> {
    if !validate_set(&v.pp.sc, subset) {
        return Err("invalid disclosed subset".into());
    }
    let diff = difference(&o.set, subset).ok_or("disclosure not in checked full set")?;
    let w = g1_mul(
        evaluate_g1(&v.pp.sc, &polynomial_coefficients(&diff))?,
        o.rho,
    );
    if w == G1::identity() {
        return Err("degenerate subset witness".into());
    }
    Ok(w)
}
fn local_inputs(v: &Registered, cs: &[G1], ds: &[Vec<S>]) -> Result<Vec<S>> {
    if cs.is_empty()
        || cs.len() != ds.len()
        || cs.iter().any(|c| *c == G1::identity())
        || ds.iter().any(|d| !validate_set(&v.pp.sc, d))
    {
        return Err("invalid checked across-set shape".into());
    }
    let mut union: Vec<S> = ds.iter().flatten().copied().collect();
    union.sort_by_key(|x| x.to_bytes_be());
    union.dedup();
    if union.len() > v.pp.sc.max_cardinality {
        return Err("disclosure union exceeds SRS".into());
    }
    Ok(union)
}

/// Holder-only continuation with canonical commitment bytes produced by that
/// same private preparation. No received-message or verifier path uses it.
pub(crate) fn aggregate_local_encoded(
    v: &Registered,
    cs: &[G1],
    ds: &[Vec<S>],
    ws: &[G1],
    encoded: &[&[u8]],
) -> Result<G1> {
    if ws.len() != cs.len() || ws.iter().any(|w| *w == G1::identity()) {
        return Err("invalid local witnesses".into());
    }
    local_inputs(v, cs, ds)?;
    if encoded.len() != cs.len() || encoded.iter().any(|b| b.len() != 48) {
        return Err("invalid private encoding shape".into());
    }
    let weights = weights_encoded(encoded, ds);
    let pi = sum1(&ws.iter().copied().zip(weights).collect::<Vec<_>>());
    if pi == G1::identity() {
        return Err("degenerate aggregate witness".into());
    }
    Ok(pi)
}
pub(crate) fn verify_across_checked(v: &Registered, cs: &[G1], ds: &[Vec<S>], pi: G1) -> bool {
    let equation = match across_equation_checked(v, cs, ds, pi) {
        Ok(e) => e,
        Err(_) => return false,
    };
    multi_pair(&equation.terms) == equation.target
}

/// Complete native across-set relation, exposed as a fixed pairing equation
/// so an engineering verifier can batch it together with all signature checks.
pub(crate) fn across_equation_checked(
    v: &Registered,
    cs: &[G1],
    ds: &[Vec<S>],
    pi: G1,
) -> Result<crate::pairing_verify::Equation> {
    if pi == G1::identity() {
        return Err("degenerate aggregate witness".into());
    }
    let union = local_inputs(v, cs, ds)?;
    let weights = weights_body(cs, ds);
    let mut terms = Vec::with_capacity(cs.len() + 1);
    for ((&c, d), weight) in cs.iter().zip(ds).zip(weights) {
        let diff = match difference(&union, d) {
            Some(x) => x,
            None => return Err("invalid across-set difference".into()),
        };
        let q = match evaluate_g2(&v.pp.sc, &polynomial_coefficients(&diff)) {
            Ok(q) if q != G2::identity() => q,
            _ => return Err("degenerate across-set quotient".into()),
        };
        terms.push((c, g2_mul(q, weight)));
    }
    let qunion = match evaluate_g2(&v.pp.sc, &polynomial_coefficients(&union)) {
        Ok(q) if q != G2::identity() => q,
        _ => return Err("degenerate across-set union".into()),
    };
    terms.push((-pi, qunion));
    Ok(crate::pairing_verify::Equation {
        terms,
        target: GT::identity(),
    })
}

pub fn aggregate(p: &Params, cs: &[G1], ds: &[Vec<S>], witnesses: &[G1]) -> Result<G1> {
    if witnesses.len() != cs.len() || witnesses.iter().any(|&w| !valid1(w, true)) {
        return Err("invalid across-set witness vector".into());
    }
    let weights = aggregation_weights(p, cs, ds)?;
    let pi = sum1(&witnesses.iter().copied().zip(weights).collect::<Vec<_>>());
    if !valid1(pi, true) {
        return Err("degenerate aggregate witness".into());
    }
    Ok(pi)
}

pub fn verify_across(p: &Params, cs: &[G1], ds: &[Vec<S>], pi: G1) -> bool {
    if !valid1(pi, true) {
        return false;
    }
    let union = match aggregate_inputs(p, cs, ds) {
        Ok(s) => s,
        Err(_) => return false,
    };
    let weights = match aggregation_weights(p, cs, ds) {
        Ok(w) => w,
        Err(_) => return false,
    };
    let mut terms = Vec::with_capacity(cs.len() + 1);
    for ((&c, d), weight) in cs.iter().zip(ds).zip(weights) {
        let diff = match difference(&union, d) {
            Some(d) => d,
            None => return false,
        };
        let q = match evaluate_g2(p, &polynomial_coefficients(&diff)) {
            Ok(q) if valid2(q, true) => q,
            _ => return false,
        };
        terms.push((c, g2_mul(q, weight)));
    }
    let qunion = match evaluate_g2(p, &polynomial_coefficients(&union)) {
        Ok(q) if valid2(q, true) => q,
        _ => return false,
    };
    terms.push((-pi, qunion));
    multi_pair(&terms) == GT::identity()
}
