//! Scalar evaluation domains and FFT interpolation.

use ff::{Field, PrimeField};

pub type S = blstrs::Scalar;

/// Ordered domain H_n = {omega^j : 0 <= j < n} in the BLS12-381 scalar field.
#[derive(Clone, Debug)]
pub struct Domain {
    pub size: usize,
    pub omega: S,
    pub elements: Vec<S>,
}

impl Domain {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn new(size: usize) -> Result<Self, String> {
        let _span = crate::darlt::instrumentation::span("polynomial");
        if size == 0 || !size.is_power_of_two() || size.trailing_zeros() > S::S {
            return Err("domain size must be a power of two between 1 and 2^32".into());
        }
        let mut omega = S::ROOT_OF_UNITY;
        for _ in size.trailing_zeros()..S::S {
            omega = omega.square();
        }
        let mut elements = Vec::new();
        elements
            .try_reserve_exact(size)
            .map_err(|_| "domain allocation failed".to_owned())?;
        let mut point = S::ONE;
        for _ in 0..size {
            elements.push(point);
            point *= omega;
        }
        Ok(Self {
            size,
            omega,
            elements,
        })
    }

    /// Evaluate a coefficient vector of exactly n scalars at the ordered domain.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn fft(&self, coefficients: &[S]) -> Result<Vec<S>, String> {
        let _span = crate::darlt::instrumentation::span("polynomial");
        self.transform(coefficients, false)
    }

    /// Interpolate n evaluations as a coefficient vector of length n.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn ifft(&self, evaluations: &[S]) -> Result<Vec<S>, String> {
        let _span = crate::darlt::instrumentation::span("polynomial");
        self.transform(evaluations, true)
    }

    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn transform(&self, input: &[S], inverse: bool) -> Result<Vec<S>, String> {
        let _span = crate::darlt::instrumentation::span("polynomial");
        let _field_span = crate::darlt::instrumentation::span("field_arithmetic");
        if input.len() != self.size {
            return Err("FFT input length differs from domain size".into());
        }
        let mut values = input.to_vec();
        let mut j = 0;
        for i in 1..self.size {
            let mut bit = self.size >> 1;
            while j & bit != 0 {
                j ^= bit;
                bit >>= 1;
            }
            j ^= bit;
            if i < j {
                values.swap(i, j);
            }
        }
        let root = if inverse {
            Option::<S>::from(self.omega.invert()).ok_or("invalid FFT root")?
        } else {
            self.omega
        };
        let mut width = 2;
        while width <= self.size {
            let step = root.pow_vartime([(self.size / width) as u64]);
            for block in values.chunks_exact_mut(width) {
                let mut power = S::ONE;
                for index in 0..width / 2 {
                    let even = block[index];
                    let odd = block[index + width / 2] * power;
                    block[index] = even + odd;
                    block[index + width / 2] = even - odd;
                    power *= step;
                }
            }
            if width == self.size {
                break;
            }
            width *= 2;
        }
        if inverse {
            let reciprocal = Option::<S>::from(S::from(self.size as u64).invert())
                .ok_or("domain size is zero in scalar field")?;
            for value in &mut values {
                *value *= reciprocal;
            }
        }
        Ok(values)
    }
}

/// Horner evaluation, with coefficients ordered from constant to highest degree.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn evaluate(coefficients: &[S], point: S) -> S {
    let _span = crate::darlt::instrumentation::span("polynomial");
    let _field_span = crate::darlt::instrumentation::span("field_arithmetic");
    coefficients
        .iter()
        .rev()
        .fold(S::ZERO, |value, coefficient| value * point + coefficient)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn roots_have_declared_order() {
        for size in [1, 2, 4, 16, 64, 1024] {
            let domain = Domain::new(size).unwrap();
            assert_eq!(domain.elements[0], S::ONE);
            assert_eq!(domain.omega.pow_vartime([size as u64]), S::ONE);
            if size > 1 {
                assert_ne!(domain.omega.pow_vartime([(size / 2) as u64]), S::ONE);
            }
            for index in 0..size {
                assert_eq!(
                    domain.elements[index],
                    domain.omega.pow_vartime([index as u64])
                );
            }
        }
    }

    #[test]
    fn fft_agrees_with_independent_horner_and_round_trip() {
        let mut rng = StdRng::seed_from_u64(0x0001_8201);
        for size in [1, 2, 4, 16, 64, 1024] {
            let domain = Domain::new(size).unwrap();
            let coefficients: Vec<_> = (0..size).map(|_| S::random(&mut rng)).collect();
            let values = domain.fft(&coefficients).unwrap();
            for (&point, &value) in domain.elements.iter().zip(&values) {
                assert_eq!(value, evaluate(&coefficients, point));
            }
            assert_eq!(domain.ifft(&values).unwrap(), coefficients);
        }
    }

    #[test]
    fn domain_and_vector_boundaries_are_checked() {
        assert!(Domain::new(0).is_err());
        assert!(Domain::new(3).is_err());
        if usize::BITS > 32 {
            assert!(Domain::new(1usize << 33).is_err());
        }
        let domain = Domain::new(4).unwrap();
        assert!(domain.fft(&[S::ZERO; 3]).is_err());
        assert!(domain.ifft(&[S::ZERO; 5]).is_err());
        assert_eq!(evaluate(&[], S::from(9)), S::ZERO);
    }
}
