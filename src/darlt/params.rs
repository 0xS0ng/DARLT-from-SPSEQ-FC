//! Reference string and on-demand pool openings.
//!
//! The trapdoor is confined to generation. Only the seven prescribed G2
//! monomial powers and the O(w+s) public quotient bases are retained.
use crate::polynomial::{Domain, S};
use blstrs::{G1Affine, G1Projective as G1, G2Projective as G2};
use ff::{Field, PrimeField};
use group::Group;
use rand::RngCore;
use std::collections::{BTreeMap, BTreeSet};

// Little-endian limbs of the BLS12-381 scalar modulus minus one.
const MODULUS_MINUS_ONE: [u64; 4] = [
    0xffff_ffff_0000_0000,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
];

fn divide_modulus_minus_one(divisor: usize) -> Result<[u64; 4], String> {
    let divisor = u64::try_from(divisor).map_err(|_| "root order exceeds u64")?;
    if divisor == 0 {
        return Err("zero root order".into());
    }
    let mut quotient = [0; 4];
    let mut remainder = 0u128;
    for index in (0..4).rev() {
        let limb = (remainder << 64) | u128::from(MODULUS_MINUS_ONE[index]);
        quotient[index] = (limb / u128::from(divisor)) as u64;
        remainder = limb % u128::from(divisor);
    }
    if remainder != 0 {
        return Err("root order does not divide p-1".into());
    }
    Ok(quotient)
}

/// Primitive root of any order dividing p-1, separate from FFT domains W/K.
pub fn nth_root(order: usize) -> Result<S, String> {
    let exponent = divide_modulus_minus_one(order)?;
    Ok(S::MULTIPLICATIVE_GENERATOR.pow_vartime(exponent))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dimensions {
    pub w: usize,
    pub s: usize,
    pub k_max: usize,
    pub k_padded: usize,
    pub n: usize,
    pub table_size: usize,
    pub degree: usize,
}

impl Dimensions {
    /// Exact Construction §I bound; D is not rounded to a power of two.
    pub fn new(w: usize, s: usize, k_max: usize) -> Result<Self, String> {
        if w == 0 || s == 0 || k_max == 0 {
            return Err("pool count, pool capacity and block size must be positive".into());
        }
        w.checked_mul(s).ok_or("unit capacity overflow")?;
        let k_padded = k_max
            .checked_next_power_of_two()
            .ok_or("query domain overflow")?;
        if k_padded.trailing_zeros() > S::S {
            return Err("query domain does not divide p-1".into());
        }
        let required = w.max(s);
        let (n, table_size) = (7..=S::S as usize)
            .find_map(|n| {
                let table_size = 1usize.checked_shl(n as u32)?;
                (table_size >= required && divide_modulus_minus_one(n).is_ok())
                    .then_some((n, table_size))
            })
            .ok_or("no permitted table domain".to_owned())?;
        let r = k_max.min(required);
        let composed = r
            .checked_add(2)
            .and_then(|x| k_padded.checked_add(2).and_then(|k| x.checked_mul(k)))
            .and_then(|x| x.checked_sub(k_padded))
            .ok_or("composed-polynomial degree overflow")?;
        let unity = k_padded
            .checked_add(5)
            .and_then(|x| n.checked_mul(x))
            .and_then(|x| x.checked_sub(1))
            .ok_or("multi-unity degree overflow")?;
        let degree = table_size.max(composed).max(unity);
        degree
            .checked_add(1)
            .ok_or("reference string length overflow")?;
        Ok(Self {
            w,
            s,
            k_max,
            k_padded,
            n,
            table_size,
            degree,
        })
    }
}

#[derive(Clone, Debug)]
pub struct ReferenceString {
    pub domain: Domain,
    pub degree: usize,
    pub n: usize,
    pub w: usize,
    pub s: usize,
    pub k_max: usize,
    pub k_padded: usize,
    pub g1: Vec<G1>,
    pub g2: BTreeMap<usize, G2>,
    /// Only the first max(w,s) table Lagrange bases are published.
    pub lagrange: Vec<G1>,
    pub vanishing: G1,
    pub k_hat: Vec<G2>,
    pub d_hat: Vec<G2>,
    pub o_hat: Vec<G2>,
    pub offset: G1,
}

impl ReferenceString {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn new(
        w: usize,
        s: usize,
        k_max: usize,
        base: G1,
        rng: &mut impl RngCore,
    ) -> Result<Self, String> {
        let dimensions = Dimensions::new(w, s, k_max)?;
        let affine = G1Affine::from(base);
        if base == G1::identity() || !bool::from(affine.is_on_curve() & affine.is_torsion_free()) {
            return Err("invalid reference-string base".into());
        }
        let tau = loop {
            let candidate = S::random(&mut *rng);
            if candidate != S::ZERO
                && candidate.pow_vartime([dimensions.table_size as u64]) != S::ONE
                && candidate.pow_vartime([dimensions.k_padded as u64]) != S::ONE
            {
                break candidate;
            }
        };
        Self::generate(dimensions, base, tau)
    }

    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn generate(dim: Dimensions, base: G1, tau: S) -> Result<Self, String> {
        let domain = Domain::new(dim.table_size)?;
        let mut g1 = Vec::new();
        g1.try_reserve_exact(dim.degree + 1)
            .map_err(|_| "G1 reference-string allocation failed")?;
        let mut power = S::ONE;
        for _ in 0..=dim.degree {
            g1.push(base * power);
            power *= tau;
        }
        let sparse_indices = [
            0,
            1,
            2,
            3,
            dim.n,
            dim.degree - dim.n + 2,
            dim.degree - dim.n + 4,
        ];
        let g2 = sparse_indices
            .into_iter()
            .map(|index| (index, G2::generator() * tau.pow_vartime([index as u64])))
            .collect();
        let z = tau.pow_vartime([domain.size as u64]) - S::ONE;
        let w_inverse = Option::<S>::from(S::from(domain.size as u64).invert())
            .ok_or("invalid table domain size")?;
        let mut l_values = Vec::with_capacity(dim.w.max(dim.s));
        let mut k_hat = Vec::with_capacity(dim.w.max(dim.s));
        for &point in &domain.elements[..dim.w.max(dim.s)] {
            let inverse = Option::<S>::from((tau - point).invert())
                .ok_or("setup trapdoor is in the table domain")?;
            let k_value = z * inverse;
            l_values.push(point * w_inverse * k_value);
            k_hat.push(G2::generator() * k_value);
        }
        let lagrange: Vec<_> = l_values.iter().map(|value| base * value).collect();
        let offset_values: Vec<_> = (0..dim.s).map(|index| S::from(index as u64)).collect();
        let offset = crate::ops::msm1(&lagrange[..dim.s], &offset_values);
        let offset_value = l_values[..dim.s]
            .iter()
            .zip(&offset_values)
            .fold(S::ZERO, |sum, (l, i)| sum + *l * i);
        let d_hat = (0..dim.w)
            .map(|index| {
                G2::generator()
                    * ((l_values[index] - S::ONE)
                        * (tau - domain.elements[index]).invert().unwrap())
            })
            .collect();
        let o_hat = (0..dim.s)
            .map(|index| {
                G2::generator()
                    * ((offset_value - S::from(index as u64))
                        * (tau - domain.elements[index]).invert().unwrap())
            })
            .collect();
        Ok(Self {
            domain,
            degree: dim.degree,
            n: dim.n,
            w: dim.w,
            s: dim.s,
            k_max: dim.k_max,
            k_padded: dim.k_padded,
            vanishing: base * z,
            g1,
            g2,
            lagrange,
            k_hat,
            d_hat,
            o_hat,
            offset,
        })
    }

    pub fn g2_power(&self, index: usize) -> Result<G2, String> {
        self.g2
            .get(&index)
            .copied()
            .ok_or_else(|| format!("G2 power {index} is outside the sparse reference string"))
    }

    pub fn commit(&self, coefficients: &[S]) -> Result<G1, String> {
        if coefficients.is_empty() || coefficients.len() > self.g1.len() {
            return Err("polynomial is outside the G1 reference-string degree bound".into());
        }
        Ok(crate::ops::msm1(
            &self.g1[..coefficients.len()],
            coefficients,
        ))
    }

    /// K query-domain Lagrange bases and the commitment to X^K-1.
    /// The group IFFT uses public monomial powers and never needs tau.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn query_basis(&self, k: usize) -> Result<(Vec<G1>, G1), String> {
        if k == 0 || !k.is_power_of_two() || k > self.k_padded {
            return Err("query domain is outside the installed block limit".into());
        }
        let domain = Domain::new(k)?;
        let mut bases = self.g1[..k].to_vec();
        let mut j = 0;
        for i in 1..k {
            let mut bit = k >> 1;
            while j & bit != 0 {
                j ^= bit;
                bit >>= 1;
            }
            j ^= bit;
            if i < j {
                bases.swap(i, j);
            }
        }
        let inverse_root = domain.omega.invert().unwrap();
        let mut width = 2;
        while width <= k {
            let step = inverse_root.pow_vartime([(k / width) as u64]);
            for block in bases.chunks_exact_mut(width) {
                let mut twiddle = S::ONE;
                for index in 0..width / 2 {
                    let even = block[index];
                    let odd = block[index + width / 2] * twiddle;
                    block[index] = even + odd;
                    block[index + width / 2] = even - odd;
                    twiddle *= step;
                }
            }
            if width == k {
                break;
            }
            width *= 2;
        }
        let inverse_size = S::from(k as u64).invert().unwrap();
        for base in &mut bases {
            *base *= inverse_size;
        }
        Ok((bases, self.g1[k] - self.g1[0]))
    }

    /// (F(X)-z_b)/(X-nu^b), using one (w+1)-point G2 MSM.
    pub fn parent_opening(&self, b: usize, seeds: &[S], rho: S) -> Result<G2, String> {
        if b >= self.w || seeds.len() != self.w {
            return Err("invalid pool or seed-vector length".into());
        }
        let mut points = Vec::with_capacity(self.w + 1);
        let mut coefficients = Vec::with_capacity(self.w + 1);
        points.push(self.d_hat[b]);
        coefficients.push(seeds[b]);
        let root = self.domain.elements[b];
        let w_inverse = S::from(self.domain.size as u64).invert().unwrap();
        for (index, seed) in seeds.iter().enumerate() {
            if index != b {
                let point = self.domain.elements[index];
                let c = point * w_inverse * (point - root).invert().unwrap();
                points.push(self.k_hat[index] - self.k_hat[b]);
                coefficients.push(*seed * c);
            }
        }
        points.push(self.k_hat[b]);
        coefficients.push(rho);
        Ok(crate::ops::msm2(&points, &coefficients))
    }

    /// (P_Gamma(X)-1)/(X-nu^b), using one |Gamma|-point G2 MSM.
    pub fn scope_opening(&self, b: usize, gamma: &[usize]) -> Result<G2, String> {
        if b >= self.w || gamma.is_empty() {
            return Err("invalid scope-opening position".into());
        }
        let set: BTreeSet<_> = gamma.iter().copied().collect();
        if set.len() != gamma.len() || !set.contains(&b) || set.iter().any(|&i| i >= self.w) {
            return Err("scope must contain the position and distinct valid pools".into());
        }
        let mut points = Vec::with_capacity(gamma.len());
        let mut coefficients = Vec::with_capacity(gamma.len());
        points.push(self.d_hat[b]);
        coefficients.push(S::ONE);
        let root = self.domain.elements[b];
        let w_inverse = S::from(self.domain.size as u64).invert().unwrap();
        for &index in gamma {
            if index != b {
                let point = self.domain.elements[index];
                points.push(self.k_hat[index] - self.k_hat[b]);
                coefficients.push(point * w_inverse * (point - root).invert().unwrap());
            }
        }
        Ok(crate::ops::msm2(&points, &coefficients))
    }

    pub fn g2_object_count(&self) -> usize {
        self.g2.len() + self.k_hat.len() + self.d_hat.len() + self.o_hat.len()
    }

    /// Public reference-string points only, in canonical compressed form.
    pub fn point_bytes(&self) -> usize {
        (self.g1.len() + self.lagrange.len() + 2) * 48 + self.g2_object_count() * 96
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::evaluate;
    use blstrs::G2Affine;
    use rand::{rngs::StdRng, SeedableRng};

    fn small() -> ReferenceString {
        ReferenceString::new(4, 3, 8, G1::generator(), &mut StdRng::seed_from_u64(0x2100)).unwrap()
    }
    fn check_opening(srs: &ReferenceString, commitment: G1, point: S, value: S, opening: G2) {
        let left = crate::ops::pairing(
            &G1Affine::from(commitment - srs.g1[0] * value),
            &G2Affine::from(srs.g2[&0]),
        );
        let right = crate::ops::pairing(
            &G1Affine::from(srs.g1[1] - srs.g1[0] * point),
            &G2Affine::from(opening),
        );
        assert_eq!(left, right);
    }
    #[test]
    fn exact_domain_and_degree_parameters() {
        let d = Dimensions::new(64, 16, 64).unwrap();
        assert_eq!(
            (d.n, d.table_size, d.k_padded, d.degree),
            (8, 256, 64, 4292)
        );
        let d = Dimensions::new(257, 16, 64).unwrap();
        assert_eq!((d.n, d.table_size, d.degree), (11, 2048, 4292));
        let d = Dimensions::new(4, 3, 7).unwrap();
        assert_eq!((d.k_max, d.k_padded), (7, 8));
        for (w, s, k) in [(0, 16, 64), (4, 0, 64), (4, 16, 0), (usize::MAX, 2, 64)] {
            assert!(Dimensions::new(w, s, k).is_err());
        }
        assert!(Dimensions::new(1, 1, usize::MAX).is_err());
    }
    #[test]
    fn non_power_of_two_roots_have_exact_order() {
        for order in [1, 2, 3, 8, 11, 16, 19, 32] {
            let root = nth_root(order).unwrap();
            assert_eq!(root.pow_vartime([order as u64]), S::ONE);
            for proper in 1..order {
                assert_ne!(root.pow_vartime([proper as u64]), S::ONE);
            }
        }
        assert!(nth_root(0).is_err());
        assert!(nth_root(7).is_err());
        assert_eq!(
            nth_root(8).unwrap(),
            Domain::new(256).unwrap().omega.pow_vartime([32])
        );
    }
    #[test]
    fn default_reference_string_publishes_only_prescribed_g2_objects() {
        let srs = ReferenceString::new(
            64,
            16,
            64,
            G1::generator(),
            &mut StdRng::seed_from_u64(0x2115),
        )
        .unwrap();
        assert_eq!(srs.g1.len(), 4293);
        assert_eq!(
            srs.g2.keys().copied().collect::<Vec<_>>(),
            vec![0, 1, 2, 3, 8, 4286, 4288]
        );
        assert_eq!(
            (srs.k_hat.len(), srs.d_hat.len(), srs.o_hat.len()),
            (64, 64, 16)
        );
        assert_eq!(srs.g2_object_count(), 151);
        assert!(srs.g2_power(4).is_err());
        assert_ne!(srs.vanishing, G1::identity());
        assert_ne!(srs.g1[64] - srs.g1[0], G1::identity());
    }
    #[test]
    fn parent_openings_agree_with_actual_committed_table() {
        let srs = small();
        let seeds = [S::from(17), S::from(29), S::from(43), S::from(61)];
        let rho = S::from(37);
        let mut values = vec![S::ZERO; srs.domain.size];
        values[..seeds.len()].copy_from_slice(&seeds);
        let mut poly = srs.domain.ifft(&values).unwrap();
        poly[0] -= rho;
        poly.push(rho);
        let commitment = srs.commit(&poly).unwrap();
        for (b, seed) in seeds.iter().enumerate() {
            assert_eq!(evaluate(&poly, srs.domain.elements[b]), *seed);
            check_opening(
                &srs,
                commitment,
                srs.domain.elements[b],
                *seed,
                srs.parent_opening(b, &seeds, rho).unwrap(),
            );
        }
        assert!(srs.parent_opening(4, &seeds, rho).is_err());
        assert!(srs.parent_opening(0, &seeds[..3], rho).is_err());
    }
    #[test]
    fn scope_and_public_offset_openings_match_their_polynomials() {
        let srs = small();
        let gamma = [0, 2, 3];
        let commitment = crate::ops::msm1(
            &gamma.iter().map(|&b| srs.lagrange[b]).collect::<Vec<_>>(),
            &vec![S::ONE; gamma.len()],
        );
        for &b in &gamma {
            check_opening(
                &srs,
                commitment,
                srs.domain.elements[b],
                S::ONE,
                srs.scope_opening(b, &gamma).unwrap(),
            );
        }
        for i in 0..srs.s {
            check_opening(
                &srs,
                srs.offset,
                srs.domain.elements[i],
                S::from(i as u64),
                srs.o_hat[i],
            );
        }
        assert!(srs.scope_opening(1, &gamma).is_err());
        assert!(srs.scope_opening(0, &[0, 0]).is_err());
        assert!(srs.scope_opening(0, &[0, 4]).is_err());
        assert!(srs.scope_opening(0, &[]).is_err());
    }
    #[test]
    fn query_lagrange_basis_matches_independent_scalar_interpolation() {
        let srs = small();
        for k in [1, 2, 4, 8] {
            let domain = Domain::new(k).unwrap();
            let (bases, z) = srs.query_basis(k).unwrap();
            assert_eq!(z, srs.g1[k] - srs.g1[0]);
            for i in 0..k {
                let mut values = vec![S::ZERO; k];
                values[i] = S::ONE;
                assert_eq!(
                    bases[i],
                    srs.commit(&domain.ifft(&values).unwrap()).unwrap()
                );
            }
        }
        assert!(srs.query_basis(0).is_err());
        assert!(srs.query_basis(3).is_err());
        assert!(srs.query_basis(16).is_err());
        assert!(srs.commit(&[]).is_err());
        assert!(srs.commit(&vec![S::ZERO; srs.degree + 2]).is_err());
    }
    #[cfg(feature = "op-counts")]
    #[test]
    fn demand_openings_execute_one_msm_with_the_declared_size() {
        let srs = small();
        let seeds = vec![S::from(2); srs.w];
        crate::ops::reset();
        srs.parent_opening(1, &seeds, S::from(5)).unwrap();
        let counts = crate::ops::stop();
        assert_eq!(counts.msm_g2_sizes, [srs.w + 1]);
        assert_eq!(counts.miller_loop_terms, 0);
        crate::ops::reset();
        srs.scope_opening(1, &[0, 1, 3]).unwrap();
        let counts = crate::ops::stop();
        assert_eq!(counts.msm_g2_sizes, [3]);
    }
}
