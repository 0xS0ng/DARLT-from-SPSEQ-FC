//! Same-curve primitive fixtures for the later authorized backend calibration.
//! No timings are produced by fixture construction or the correctness tests.
use crate::{blstrs_bridge as bridge, Result};
use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine};
use ark_ff::{PrimeField, UniformRand};
use ark_std::rand::{rngs::StdRng, CryptoRng, RngCore, SeedableRng};
use darlt_spseq_fc::sampling::{Invocation, NativeOperation};
use std::hint::black_box;

pub const MSM_SIZES: [usize; 10] = [1, 2, 4, 8, 16, 32, 64, 128, 256, 1024];
#[derive(Clone, Copy, Debug)]
pub enum Operation {
    Pairing,
    G1Msm(usize),
    G2Msm(usize),
}
/// Candidates are ordered Arkworks0.3, blstrs0.7.1. Points/scalars are the same
/// mathematical fixture; input generation and checked conversion are outside
/// the primitive callback. Each backend uses its ordinary protocol MSM API.
pub struct Fixture {
    operation: Operation,
    ark_g1: Vec<G1Affine>,
    ark_g2: Vec<G2Affine>,
    ark_scalars: Vec<<Fr as PrimeField>::BigInt>,
    common_g1: Vec<blstrs::G1Projective>,
    common_g2: Vec<blstrs::G2Projective>,
    common_scalars: Vec<blstrs::Scalar>,
    common_pair: Option<(blstrs::G1Affine, blstrs::G2Affine)>,
    ark_pair: Option<(G1Affine, G2Affine)>,
    basis_digest: [u8; 32],
    last_input: Option<[u8; 32]>,
}
impl Fixture {
    pub fn new(operation: Operation, rng: &mut (impl RngCore + CryptoRng)) -> Result<Self> {
        let count = match operation {
            Operation::Pairing => 1,
            Operation::G1Msm(n) | Operation::G2Msm(n) => n,
        };
        if !MSM_SIZES.contains(&count) {
            return Err("calibration MSM size outside plan".into());
        }
        let mut out = Self {
            operation,
            ark_g1: vec![],
            ark_g2: vec![],
            ark_scalars: vec![],
            common_g1: vec![],
            common_g2: vec![],
            common_scalars: vec![],
            common_pair: None,
            ark_pair: None,
            basis_digest: [0; 32],
            last_input: None,
        };
        for _ in 0..count {
            let s = Fr::rand(rng);
            let a = G1Affine::prime_subgroup_generator().mul(Fr::rand(rng).into_repr());
            let b = G2Affine::prime_subgroup_generator().mul(Fr::rand(rng).into_repr());
            use ark_ec::ProjectiveCurve;
            let (a, b) = (a.into_affine(), b.into_affine());
            out.ark_g1.push(a);
            out.ark_g2.push(b);
            out.ark_scalars.push(s.into_repr());
            out.common_g1.push(bridge::g1(a)?);
            out.common_g2.push(bridge::g2(b)?);
            out.common_scalars.push(bridge::scalar(s)?);
        }
        out.common_pair = Some((out.common_g1[0].into(), out.common_g2[0].into()));
        out.ark_pair = Some((out.ark_g1[0], out.ark_g2[0]));
        let mut h = blake3::Hasher::new();
        for p in &out.common_g1 {
            h.update(&p.to_compressed());
        }
        for p in &out.common_g2 {
            h.update(&p.to_compressed());
        }
        out.basis_digest = *h.finalize().as_bytes();
        Ok(out)
    }
    /// New mathematical inputs for one sampler slot; both backends consume
    /// these exact inputs, and no native operation result is cached.
    pub fn refresh_inputs(&mut self, rng: &mut (impl RngCore + CryptoRng)) -> Result<()> {
        match self.operation {
            Operation::Pairing => {
                use ark_ec::ProjectiveCurve;
                let a = self.ark_g1[0].mul(Fr::rand(rng).into_repr()).into_affine();
                let b = self.ark_g2[0].mul(Fr::rand(rng).into_repr()).into_affine();
                self.ark_pair = Some((a, b));
                self.common_pair = Some((bridge::g1(a)?.into(), bridge::g2(b)?.into()));
            }
            _ => {
                self.ark_scalars.clear();
                self.common_scalars.clear();
                for _ in 0..self.ark_g1.len() {
                    let s = Fr::rand(rng);
                    self.ark_scalars.push(s.into_repr());
                    self.common_scalars.push(bridge::scalar(s)?);
                }
            }
        }
        Ok(())
    }
    pub fn input_digest(&self) -> String {
        let mut h = blake3::Hasher::new();
        h.update(&self.basis_digest);
        if matches!(self.operation, Operation::Pairing) {
            let (a, b) = self.common_pair.as_ref().unwrap();
            h.update(&a.to_compressed());
            h.update(&b.to_compressed());
        } else {
            for s in &self.common_scalars {
                h.update(&s.to_bytes_le());
            }
        }
        h.finalize().to_hex().to_string()
    }
    pub fn check_msm_equivalence(&self) -> Result<()> {
        use ark_ec::ProjectiveCurve;
        let a = VariableBaseMSM::multi_scalar_mul(&self.ark_g1, &self.ark_scalars);
        if bridge::g1(a.into_affine())?
            != blstrs::G1Projective::multi_exp(&self.common_g1, &self.common_scalars)
        {
            return Err("calibration G1 MSM fixture mismatch".into());
        }
        let b = VariableBaseMSM::multi_scalar_mul(&self.ark_g2, &self.ark_scalars);
        if bridge::g2(b.into_affine())?
            != blstrs::G2Projective::multi_exp(&self.common_g2, &self.common_scalars)
        {
            return Err("calibration G2 MSM fixture mismatch".into());
        }
        Ok(())
    }
}
impl NativeOperation for Fixture {
    fn prepare(&mut self, i: &Invocation) -> Result<()> {
        if i.candidate > 1 {
            return Err("calibration has exactly two native backends".into());
        }
        let mut h = blake3::Hasher::new();
        h.update(&self.basis_digest);
        h.update(&(i.attempt as u64).to_le_bytes());
        h.update(&(i.index as u64).to_le_bytes());
        h.update(&(i.round as u64).to_le_bytes());
        h.update(&[if i.phase == darlt_spseq_fc::sampling::Phase::Warmup {
            0
        } else {
            1
        }]);
        let key = *h.finalize().as_bytes();
        if self.last_input != Some(key) {
            self.refresh_inputs(&mut StdRng::from_seed(key))?;
            self.last_input = Some(key);
        }
        Ok(())
    }
    fn execute(&mut self, i: &Invocation) -> Result<()> {
        match (self.operation, i.candidate) {
            (Operation::Pairing, 0) => {
                let (a, b) = self.ark_pair.expect("prepared native pairing input");
                black_box(Bls12_381::pairing(a, b));
            }
            (Operation::Pairing, 1) => {
                let (a, b) = self
                    .common_pair
                    .as_ref()
                    .expect("prepared affine pairing fixture");
                black_box(blstrs::pairing(a, b));
            }
            (Operation::G1Msm(_), 0) => {
                let _ = black_box(VariableBaseMSM::multi_scalar_mul(
                    &self.ark_g1,
                    &self.ark_scalars,
                ));
            }
            (Operation::G1Msm(_), 1) => {
                black_box(blstrs::G1Projective::multi_exp(
                    &self.common_g1,
                    &self.common_scalars,
                ));
            }
            (Operation::G2Msm(_), 0) => {
                let _ = black_box(VariableBaseMSM::multi_scalar_mul(
                    &self.ark_g2,
                    &self.ark_scalars,
                ));
            }
            (Operation::G2Msm(_), 1) => {
                black_box(blstrs::G2Projective::multi_exp(
                    &self.common_g2,
                    &self.common_scalars,
                ));
            }
            _ => return Err("unknown calibration backend".into()),
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn same_native_msm_fixture_checks_without_timing() {
        let mut rng = StdRng::seed_from_u64(214_240_003);
        for n in [1, 16, 64] {
            Fixture::new(Operation::G1Msm(n), &mut rng)
                .unwrap()
                .check_msm_equivalence()
                .unwrap();
        }
    }
}
