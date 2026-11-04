//! Dense scalar polynomial arithmetic for the native lookup backend.
//!
//! Coefficients are ascending. FFT multiplication, Newton division and a
//! remainder tree keep composition quasi-linear in its O(k^2) output length.
use crate::polynomial::{evaluate, Domain, S};
use ff::Field;

pub type Poly = Vec<S>;

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn normalize(mut a: Poly) -> Poly {
    while a.len() > 1 && a.last() == Some(&S::ZERO) {
        a.pop();
    }
    if a.is_empty() {
        a.push(S::ZERO);
    }
    a
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn is_zero(a: &[S]) -> bool {
    a.iter().all(|x| *x == S::ZERO)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn add(a: &[S], b: &[S]) -> Poly {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let mut out = vec![S::ZERO; a.len().max(b.len())];
    for (i, v) in a.iter().enumerate() {
        out[i] += v;
    }
    for (i, v) in b.iter().enumerate() {
        out[i] += v;
    }
    normalize(out)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn sub(a: &[S], b: &[S]) -> Poly {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let mut out = vec![S::ZERO; a.len().max(b.len())];
    for (i, v) in a.iter().enumerate() {
        out[i] += v;
    }
    for (i, v) in b.iter().enumerate() {
        out[i] -= v;
    }
    normalize(out)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn scale(a: &[S], c: S) -> Poly {
    let _span = crate::darlt::instrumentation::span("polynomial");
    normalize(a.iter().map(|v| *v * c).collect())
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn mul(a: &[S], b: &[S]) -> Result<Poly, String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    if a.is_empty() || b.is_empty() || is_zero(a) || is_zero(b) {
        return Ok(vec![S::ZERO]);
    }
    let count = a.len() + b.len() - 1;
    if a.len().min(b.len()) <= 16 {
        let _field_span = crate::darlt::instrumentation::span("field_arithmetic");
        let mut out = vec![S::ZERO; count];
        for (i, x) in a.iter().enumerate() {
            for (j, y) in b.iter().enumerate() {
                out[i + j] += *x * y;
            }
        }
        return Ok(normalize(out));
    }
    let n = count.next_power_of_two();
    let domain = Domain::new(n)?;
    let mut left = vec![S::ZERO; n];
    left[..a.len()].copy_from_slice(a);
    let mut right = vec![S::ZERO; n];
    right[..b.len()].copy_from_slice(b);
    let mut spectrum = domain.fft(&left)?;
    let other = domain.fft(&right)?;
    let field_span = crate::darlt::instrumentation::span("field_arithmetic");
    for (x, y) in spectrum.iter_mut().zip(other) {
        *x *= y;
    }
    drop(field_span);
    let mut result = domain.ifft(&spectrum)?;
    result.truncate(count);
    Ok(normalize(result))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn inverse_series(a: &[S], count: usize) -> Result<Poly, String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    if count == 0 {
        return Ok(vec![]);
    }
    let a0 = *a.first().ok_or("empty inverse series")?;
    let mut inverse =
        vec![Option::<S>::from(a0.invert()).ok_or("zero constant in inverse series")?];
    while inverse.len() < count {
        let target = (inverse.len() * 2).min(count);
        let prefix = &a[..a.len().min(target)];
        let product = mul(prefix, &inverse)?;
        let mut correction = vec![S::ZERO; target];
        correction[0] = S::from(2);
        for (i, x) in product.iter().take(target).enumerate() {
            correction[i] -= x;
        }
        inverse = mul(&inverse, &correction)?;
        inverse.resize(target, S::ZERO);
        inverse.truncate(target);
    }
    Ok(inverse)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn div_rem(a: &[S], b: &[S]) -> Result<(Poly, Poly), String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let a = normalize(a.to_vec());
    let b = normalize(b.to_vec());
    if is_zero(&b) {
        return Err("division by zero polynomial".into());
    }
    if a.len() < b.len() {
        return Ok((vec![S::ZERO], a));
    }
    let qlen = a.len() - b.len() + 1;
    if qlen.min(b.len()) <= 16 {
        let _field_span = crate::darlt::instrumentation::span("field_arithmetic");
        let mut remainder = a;
        let mut q = vec![S::ZERO; qlen];
        let top_inverse =
            Option::<S>::from(b.last().unwrap().invert()).ok_or("zero leading divisor")?;
        for index in (0..qlen).rev() {
            let v = remainder[index + b.len() - 1] * top_inverse;
            q[index] = v;
            for j in 0..b.len() {
                remainder[index + j] -= v * b[j];
            }
        }
        remainder.truncate(b.len().saturating_sub(1));
        return Ok((normalize(q), normalize(remainder)));
    }
    let reversed_a: Poly = a.iter().rev().take(qlen).copied().collect();
    let reversed_b: Poly = b.iter().rev().take(qlen).copied().collect();
    let inverse = inverse_series(&reversed_b, qlen)?;
    let mut reverse_q = mul(&reversed_a, &inverse)?;
    reverse_q.resize(qlen, S::ZERO);
    reverse_q.truncate(qlen);
    reverse_q.reverse();
    let q = normalize(reverse_q);
    let mut remainder = sub(&a, &mul(&b, &q)?);
    if remainder.iter().skip(b.len() - 1).any(|x| *x != S::ZERO) {
        return Err("fast polynomial division residual degree".into());
    }
    remainder.truncate(b.len() - 1);
    Ok((q, normalize(remainder)))
}
/// Divide by X^m-1 in linear work in the numerator's coefficient count.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn divide_vanishing(a: &[S], m: usize) -> Result<(Poly, Poly), String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    if m == 0 {
        return Err("zero vanishing domain".into());
    }
    if a.len() <= m {
        return Ok((vec![S::ZERO], normalize(a.to_vec())));
    }
    let mut remainder = a.to_vec();
    let mut q = vec![S::ZERO; a.len() - m];
    for index in (m..a.len()).rev() {
        let value = remainder[index];
        q[index - m] = value;
        remainder[index] = S::ZERO;
        remainder[index - m] += value;
    }
    remainder.truncate(m);
    Ok((normalize(q), normalize(remainder)))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn vanishing(m: usize) -> Poly {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let mut out = vec![S::ZERO; m + 1];
    out[0] = -S::ONE;
    out[m] = S::ONE;
    out
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn linear_quotient(a: &[S], point: S) -> (S, Poly) {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let _field_span = crate::darlt::instrumentation::span("field_arithmetic");
    if a.len() <= 1 {
        return (a.first().copied().unwrap_or(S::ZERO), vec![S::ZERO]);
    }
    let mut quotient = vec![S::ZERO; a.len() - 1];
    quotient[a.len() - 2] = a[a.len() - 1];
    for index in (0..a.len() - 2).rev() {
        quotient[index] = a[index + 1] + point * quotient[index + 1];
    }
    let value = a[0] + point * quotient[0];
    (value, normalize(quotient))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn interpolate(points: &[S], values: &[S]) -> Result<Poly, String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    if points.len() != values.len() || points.is_empty() {
        return Err("invalid interpolation lengths".into());
    }
    let z = product_roots(points)?;
    let mut result = vec![S::ZERO; points.len()];
    for (point, value) in points.iter().zip(values) {
        let (zero, q) = linear_quotient(&z, *point);
        if zero != S::ZERO {
            return Err("interpolation root mismatch".into());
        }
        let denom = evaluate(&q, *point);
        let inv = Option::<S>::from(denom.invert()).ok_or("duplicate interpolation point")?;
        for (out, c) in result.iter_mut().zip(q) {
            *out += c * value * inv;
        }
    }
    Ok(normalize(result))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn product_roots(points: &[S]) -> Result<Poly, String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let mut p = vec![S::ONE];
    for point in points {
        p = mul(&p, &[-*point, S::ONE])?;
    }
    Ok(p)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn evaluate_many(a: &[S], points: &[S]) -> Result<Vec<S>, String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    if points.is_empty() {
        return Ok(vec![]);
    }
    if !points.len().is_power_of_two() {
        return Err("remainder tree needs a binary point count".into());
    }
    let mut levels = vec![points.iter().map(|p| vec![-*p, S::ONE]).collect::<Vec<_>>()];
    while levels.last().unwrap().len() > 1 {
        let mut next = vec![];
        for pair in levels.last().unwrap().chunks_exact(2) {
            next.push(mul(&pair[0], &pair[1])?);
        }
        levels.push(next);
    }
    let mut residues = vec![div_rem(a, &levels.last().unwrap()[0])?.1];
    for level in (0..levels.len() - 1).rev() {
        let mut next = Vec::with_capacity(residues.len() * 2);
        for (i, residue) in residues.iter().enumerate() {
            next.push(div_rem(residue, &levels[level][2 * i])?.1);
            next.push(div_rem(residue, &levels[level][2 * i + 1])?.1);
        }
        residues = next;
    }
    Ok(residues.into_iter().map(|r| r[0]).collect())
}
/// Compose by FFT evaluation, fast remainder-tree evaluation, and interpolation.
/// Work is quasi-linear in the output degree, not cubic Horner composition.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn compose(outer: &[S], inner: &[S]) -> Result<Poly, String> {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let outer = normalize(outer.to_vec());
    let inner = normalize(inner.to_vec());
    if outer.len() == 1 {
        return Ok(outer);
    }
    if inner.len() == 1 {
        return Ok(vec![evaluate(&outer, inner[0])]);
    }
    let degree = (outer.len() - 1)
        .checked_mul(inner.len() - 1)
        .ok_or("composition degree overflow")?;
    let n = (degree + 1).next_power_of_two();
    let domain = Domain::new(n)?;
    let mut padded = inner;
    padded.resize(n, S::ZERO);
    let arguments = domain.fft(&padded)?;
    let evaluations = evaluate_many(&outer, &arguments)?;
    let mut coefficients = domain.ifft(&evaluations)?;
    coefficients.truncate(degree + 1);
    Ok(normalize(coefficients))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn products_division_and_composition_agree_with_independent_values() {
        let mut rng = StdRng::seed_from_u64(182_555);
        for (da, db) in [(3, 4), (32, 33), (70, 68)] {
            let a: Vec<_> = (0..=da).map(|_| S::random(&mut rng)).collect();
            let b: Vec<_> = (0..=db).map(|_| S::random(&mut rng)).collect();
            let product = mul(&a, &b).unwrap();
            let (q, r) = div_rem(&product, &b).unwrap();
            assert_eq!(q, a);
            assert!(is_zero(&r));
            let composition = compose(&a, &b).unwrap();
            for x in [S::ZERO, S::ONE, S::from(7), S::from(29)] {
                assert_eq!(evaluate(&composition, x), evaluate(&a, evaluate(&b, x)));
                assert_eq!(evaluate(&product, x), evaluate(&a, x) * evaluate(&b, x));
            }
        }
    }
    #[test]
    fn repeat_arguments_zero_polynomials_and_vanishing_division() {
        let p = vec![S::from(2), S::from(3), S::from(5)];
        let points = vec![S::ONE; 32];
        assert_eq!(evaluate_many(&p, &points).unwrap(), vec![S::from(10); 32]);
        assert_eq!(
            compose(&p, &[S::from(7)]).unwrap(),
            vec![evaluate(&p, S::from(7))]
        );
        assert_eq!(compose(&[S::ZERO], &p).unwrap(), vec![S::ZERO]);
        let a = mul(&p, &vanishing(4)).unwrap();
        let (q, r) = divide_vanishing(&a, 4).unwrap();
        assert_eq!(q, p);
        assert!(is_zero(&r));
    }
}
