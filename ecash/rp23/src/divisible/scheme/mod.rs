use crate::backend::{GtCompat, IntoMsm, NativeMsm, ScalarCompat};
use ff::Field;
use std::cell::Cell;
use std::convert::TryInto;
use std::ops::Neg;
use std::ops::*;

use crate::backend::{pairing, G1Projective, G2Prepared, G2Projective, Scalar};
use group::{Curve, GroupEncoding};

use crate::divisible::constants::L;
use crate::divisible::error::{DivisibleEcashError, Result};
use crate::divisible::proofs::proof_spend::{SpendInstance, SpendProof, SpendWitness};
use crate::divisible::scheme::keygen::{SecretKeyUser, VerificationKeyAuth};
use crate::divisible::scheme::setup::{GroupParameters, Parameters};
use crate::divisible::utils::{
    check_bilinear_pairing, hash_to_scalar, try_deserialize_g1_projective, Signature, SignerIndex,
};
use crate::divisible::Attribute;

pub mod aggregation;
pub mod keygen;
pub mod setup;
pub mod structure_preserving_signature;
pub mod withdrawal;

pub fn compute_kappa(
    params: &GroupParameters,
    verification_key: &VerificationKeyAuth,
    attributes: &[Attribute],
    blinding_factor: Scalar,
) -> G2Projective {
    params.gen2() * blinding_factor
        + verification_key.alpha
        + attributes
            .iter()
            .zip(verification_key.beta_g2.iter())
            .map(|(priv_attr, beta_i)| (*beta_i, *priv_attr))
            .collect::<Vec<_>>()
            .msm()
}

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub struct Phi(pub(crate) G1Projective, pub(crate) G1Projective);

impl Phi {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(48 + 48);
        bytes.extend_from_slice(self.0.to_bytes().as_ref());
        bytes.extend_from_slice(self.1.to_bytes().as_ref());
        bytes
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < 48 * 2 || (bytes.len()) % 48 != 0 {
            return Err(DivisibleEcashError::DeserializationInvalidLength {
                actual: bytes.len(),
                modulus_target: bytes.len(),
                target: 48 * 2,
                modulus: 48,
                object: "phi".to_string(),
            });
        }

        let elem_0_bytes = bytes[0..48].try_into().unwrap();
        let elem_0 = try_deserialize_g1_projective(
            elem_0_bytes,
            DivisibleEcashError::Deserialization(
                "Failed to deserialize element 0 of Phi".to_string(),
            ),
        )?;

        let elem_1_bytes = bytes[48..96].try_into().unwrap();
        let elem_1 = try_deserialize_g1_projective(
            elem_1_bytes,
            DivisibleEcashError::Deserialization(
                "Failed to deserialize element 1 of Phi".to_string(),
            ),
        )?;

        Ok(Phi(elem_0, elem_1))
    }
}

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub struct VarPhi(pub(crate) G1Projective, pub(crate) G1Projective);

impl VarPhi {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(48 + 48);
        bytes.extend_from_slice(self.0.to_bytes().as_ref());
        bytes.extend_from_slice(self.1.to_bytes().as_ref());
        bytes
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < 48 * 2 || (bytes.len()) % 48 != 0 {
            return Err(DivisibleEcashError::DeserializationInvalidLength {
                actual: bytes.len(),
                modulus_target: bytes.len(),
                target: 48 * 2,
                modulus: 48,
                object: "varphi".to_string(),
            });
        }

        let elem_0_bytes = bytes[0..48].try_into().unwrap();
        let elem_0 = try_deserialize_g1_projective(
            elem_0_bytes,
            DivisibleEcashError::Deserialization(
                "Failed to deserialize element 0 of VarPhi".to_string(),
            ),
        )?;

        let elem_1_bytes = bytes[48..96].try_into().unwrap();
        let elem_1 = try_deserialize_g1_projective(
            elem_1_bytes,
            DivisibleEcashError::Deserialization(
                "Failed to deserialize element 1 of VarPhi".to_string(),
            ),
        )?;

        Ok(VarPhi(elem_0, elem_1))
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct PayInfo {
    pub info: [u8; 32],
}

#[derive(Debug, Clone)]
pub struct Payment {
    pub kappa: G2Projective,
    pub sig: Signature,
    pub phi: Phi,
    pub varphi: VarPhi,
    pub varsig_prime1: G1Projective,
    pub varsig_prime2: G1Projective,
    pub theta_prime1: G1Projective,
    pub theta_prime2: G1Projective,
    pub rr_prime: G1Projective,
    pub ss_prime: G1Projective,
    pub tt_prime: G2Projective,
    pub rr: Scalar,
    pub zk_proof: SpendProof,
    pub vv: u64,
}

impl Payment {
    pub fn get_kappa(&self) -> G2Projective {
        self.kappa
    }
    pub fn get_sig(&self) -> Signature {
        self.sig
    }
    pub fn get_phi(&self) -> Phi {
        self.phi
    }
    pub fn get_varphi(&self) -> VarPhi {
        self.varphi
    }
    pub fn get_varsig_prime1(&self) -> G1Projective {
        self.varsig_prime1
    }
    pub fn get_varsig_prime2(&self) -> G1Projective {
        self.varsig_prime2
    }
    pub fn get_theta_prime1(&self) -> G1Projective {
        self.theta_prime1
    }
    pub fn get_theta_prime2(&self) -> G1Projective {
        self.theta_prime2
    }
    pub fn get_rr_prime(&self) -> G1Projective {
        self.rr_prime
    }
    pub fn get_ss_prime(&self) -> G1Projective {
        self.ss_prime
    }
    pub fn get_tt_prime(&self) -> G2Projective {
        self.tt_prime
    }
    pub fn get_rr(&self) -> Scalar {
        self.rr
    }
    pub fn get_zk_proof(&self) -> SpendProof {
        self.zk_proof.clone()
    }
    pub fn get_vv(&self) -> u64 {
        self.vv
    }
}

pub struct PartialWallet {
    sig: Signature,
    v: Scalar,
    idx: Option<SignerIndex>,
}

impl PartialWallet {
    pub fn signature(&self) -> &Signature {
        &self.sig
    }
    pub fn v(&self) -> Scalar {
        self.v
    }
    pub fn index(&self) -> Option<SignerIndex> {
        self.idx
    }
}

pub struct Wallet {
    sig: Signature,
    v: Scalar,
    pub l: Cell<u64>,
}

impl Wallet {
    /// Independent local experiment branch; the native wallet counter is copied,
    /// never shared with another sample or used as an online allocator.
    pub(crate) fn fixture_branch(&self) -> Self {
        Self {
            sig: self.sig.clone(),
            v: self.v,
            l: Cell::new(self.l.get()),
        }
    }

    pub fn signature(&self) -> &Signature {
        &self.sig
    }

    pub fn v(&self) -> Scalar {
        self.v
    }

    pub fn l(&self) -> u64 {
        self.l.get()
    }

    pub fn spend(
        &self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        sk_user: &SecretKeyUser,
        pay_info: &PayInfo,
        vv: u64,
        bench_flag: bool,
    ) -> Result<(Payment, &Self)> {
        if vv == 0
            || self.l() == 0
            || self
                .l()
                .checked_add(vv - 1)
                .is_none_or(|end| end > params.capacity)
        {
            return Err(DivisibleEcashError::Spend(
                "The counter l is higher than max L".to_string(),
            ));
        }

        let grp = params.get_grp();
        let params_u = params.get_params_u();
        let params_a = params.get_params_a();
        // randomize signature in the wallet
        let (signature_prime, sign_blinding_factor) = self.signature().randomise(grp);
        // construct kappa i.e., blinded attributes for show
        let attributes = vec![sk_user.sk, self.v()];
        // compute kappa
        let kappa = compute_kappa(&grp, &verification_key, &attributes, sign_blinding_factor);

        let r1 = grp.random_scalar();
        let r2 = grp.random_scalar();
        let phi = Phi(
            grp.gen1() * r1,
            crate::msm1!(
                (params_u.get_ith_sigma(self.l() as usize), self.v),
                (params_u.get_ith_eta(vv as usize), r1)
            ),
        );

        // compute hash of the payment info
        let rr = hash_to_scalar(pay_info.info);
        let varphi = VarPhi(
            grp.gen1() * r2,
            crate::msm1!(
                (grp.gen1(), rr * sk_user.sk),
                (params_u.get_ith_theta(self.l() as usize), self.v),
                (params_u.get_ith_eta(vv as usize), r2)
            ),
        );

        // random value used to compute blinded bases
        let r_varsig1 = grp.random_scalar();
        let r_theta1 = grp.random_scalar();
        let r_varsig2 = grp.random_scalar();
        let r_theta2 = grp.random_scalar();
        let r_rr = grp.random_scalar();
        let r_ss = grp.random_scalar();
        let r_tt = grp.random_scalar();

        // compute blinded bases
        let psi_g1 = params_u.get_psi_g1();
        let psi_g2 = params_u.get_psi_g2();
        let varsig_prime1 = params_u.get_ith_sigma(self.l() as usize) + (psi_g1 * r_varsig1);
        let theta_prime1 = params_u.get_ith_theta(self.l() as usize) + (psi_g1 * r_theta1);
        let varsig_prime2 =
            params_u.get_ith_sigma(self.l() as usize + vv as usize - 1) + (psi_g1 * r_varsig2);
        let theta_prime2 =
            params_u.get_ith_theta(self.l() as usize + vv as usize - 1) + (psi_g1 * r_theta2);

        let tau_l_vv = params_u.get_ith_sps_sign(self.l() as usize + vv as usize - 1);
        let rr_prime = tau_l_vv.rr + (psi_g1 * r_rr);
        let ss_prime = tau_l_vv.ss + (psi_g1 * r_ss);
        let tt_prime = tau_l_vv.tt + (psi_g2 * r_tt);

        let rho1 = self.v.neg() * r_varsig1;
        let rho2 = self.v.neg() * r_theta1;
        let rho3 = r_rr * r_tt;

        let bases = params.install_pairing_bases(vv);
        let pg_psi0_delta = bases.pg_psi0_delta;
        let pg_psi0_gen2 = bases.pg_psi0_gen2;
        let pg_psi0_yy = bases.pg_psi0_yy;
        let pg_psi0_ww1 = bases.pg_psi0_ww1;
        let pg_psi0_ww2 = bases.pg_psi0_ww2;
        let pg_psi0_psi1 = bases.pg_psi0_psi1;
        let pg_rr_psi1 = pairing(&rr_prime.to_affine(), &psi_g2.to_affine());
        let pg_psi0_tt = pairing(&psi_g1.to_affine(), &tt_prime.to_affine());
        let pg_eq1 = crate::backend::pairing_product(&[
            (
                varsig_prime1.to_affine(),
                params_a.get_ith_delta((vv - 1) as usize).to_affine(),
            ),
            (-varsig_prime2.to_affine(), *grp.gen2()),
        ]);
        let pg_eq2 = crate::backend::pairing_product(&[
            (
                theta_prime1.to_affine(),
                params_a.get_ith_delta((vv - 1) as usize).to_affine(),
            ),
            (-theta_prime2.to_affine(), *grp.gen2()),
        ]);
        let pg_eq3 = crate::backend::pairing_product(&[
            (
                rr_prime.to_affine(),
                params_u.get_sps_pk().get_yy().to_affine(),
            ),
            (ss_prime.to_affine(), *grp.gen2()),
            (
                varsig_prime2.to_affine(),
                params_u.get_sps_pk().get_ith_ww(0).to_affine(),
            ),
            (
                theta_prime2.to_affine(),
                params_u.get_sps_pk().get_ith_ww(1).to_affine(),
            ),
        ]) - bases.pg_gen1_zz;
        let pg_eq4 = pairing(&rr_prime.to_affine(), &tt_prime.to_affine()) - bases.pg_gen1_gen2;

        let instance = SpendInstance {
            kappa,
            phi,
            varphi,
            rr,
            rr_prime,
            ss_prime,
            tt_prime,
            varsig_prime1,
            theta_prime1,
            pg_eq1,
            pg_eq2,
            pg_eq3,
            pg_eq4,
            psi_g1: *psi_g1,
            psi_g2: *psi_g2,
            pg_psi0_delta,
            pg_psi0_gen2,
            pg_psi0_yy,
            pg_psi0_ww1,
            pg_psi0_ww2,
            pg_rr_psi1,
            pg_psi0_tt,
            pg_psi0_psi1,
        };

        let witness = SpendWitness {
            sk_u: sk_user.clone(),
            v: self.v,
            r: sign_blinding_factor,
            r1,
            r2,
            r_varsig1,
            r_theta1,
            r_varsig2,
            r_theta2,
            r_rr,
            r_ss,
            r_tt,
            rho1,
            rho2,
            rho3,
        };

        // compute the zk proof
        let zk_proof = SpendProof::construct(params, &instance, &witness, &verification_key, vv);

        // output pay and updated wallet
        let pay = Payment {
            kappa,
            sig: signature_prime,
            phi,
            varphi,
            varsig_prime1,
            varsig_prime2,
            theta_prime1,
            theta_prime2,
            rr_prime,
            ss_prime,
            tt_prime,
            rr,
            zk_proof,
            vv,
        };

        // The number of samples collected by the benchmark process is way higher than the
        // MAX_WALLET_VALUE we ever consider. Thus, we would execute the spending too many times
        // and the initial condition at the top of this function will crush. Thus, we need a
        // benchmark flag to signal that we don't want to increase the spending couter but only
        // care about the function performance.
        if !bench_flag {
            let current_l = self.l();
            self.l.set(current_l + vv);
        }
        Ok((pay, self))
    }
}

impl Payment {
    pub fn spend_verify(
        &self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        pay_info: &PayInfo,
    ) -> Result<bool> {
        if bool::from(self.sig.0.is_identity()) {
            return Err(DivisibleEcashError::Spend(
                "The element h of the signature equals the identity".to_string(),
            ));
        }
        let grp = params.get_grp();
        let params_a = params.get_params_a();
        let params_u = params.get_params_u();

        if !check_bilinear_pairing(
            &self.sig.0.to_affine(),
            &G2Prepared::from(self.kappa.to_affine()),
            &self.sig.1.to_affine(),
            grp.prepared_miller_g2(),
        ) {
            return Err(DivisibleEcashError::Spend(
                "The bilinear check for kappa failed".to_string(),
            ));
        }

        if bool::from(self.sig.0.is_identity()) {
            return Err(DivisibleEcashError::Spend(
                "The element h of the signature on l equals the identity".to_string(),
            ));
        }

        // verify integrity of R
        if !(self.rr == hash_to_scalar(pay_info.info)) {
            return Err(DivisibleEcashError::Spend(
                "Integrity of R does not hold".to_string(),
            ));
        }

        // The public api::verify entry checks the expected merchant in native payinfo.

        let psi_g1 = params_u.get_psi_g1();
        let psi_g2 = params_u.get_psi_g2();
        let bases = params.install_pairing_bases(self.vv);
        let pg_psi0_delta = bases.pg_psi0_delta;
        let pg_psi0_gen2 = bases.pg_psi0_gen2;
        let pg_psi0_yy = bases.pg_psi0_yy;
        let pg_psi0_ww1 = bases.pg_psi0_ww1;
        let pg_psi0_ww2 = bases.pg_psi0_ww2;
        let pg_psi0_psi1 = bases.pg_psi0_psi1;
        let pg_rr_psi1 = pairing(&self.rr_prime.to_affine(), &psi_g2.to_affine());
        let pg_psi0_tt = pairing(&psi_g1.to_affine(), &self.tt_prime.to_affine());
        let pg_eq1 = crate::backend::pairing_product(&[
            (
                self.varsig_prime1.to_affine(),
                params_a.get_ith_delta((self.vv - 1) as usize).to_affine(),
            ),
            (-self.varsig_prime2.to_affine(), *grp.gen2()),
        ]);
        let pg_eq2 = crate::backend::pairing_product(&[
            (
                self.theta_prime1.to_affine(),
                params_a.get_ith_delta((self.vv - 1) as usize).to_affine(),
            ),
            (-self.theta_prime2.to_affine(), *grp.gen2()),
        ]);
        let pg_eq3 = crate::backend::pairing_product(&[
            (
                self.rr_prime.to_affine(),
                params_u.get_sps_pk().get_yy().to_affine(),
            ),
            (self.ss_prime.to_affine(), *grp.gen2()),
            (
                self.varsig_prime2.to_affine(),
                params_u.get_sps_pk().get_ith_ww(0).to_affine(),
            ),
            (
                self.theta_prime2.to_affine(),
                params_u.get_sps_pk().get_ith_ww(1).to_affine(),
            ),
        ]) - bases.pg_gen1_zz;
        let pg_eq4 =
            pairing(&self.rr_prime.to_affine(), &self.tt_prime.to_affine()) - bases.pg_gen1_gen2;

        let instance = SpendInstance {
            kappa: self.kappa,
            phi: self.phi,
            varphi: self.varphi,
            rr: self.rr,
            rr_prime: self.rr_prime,
            ss_prime: self.ss_prime,
            tt_prime: self.tt_prime,
            varsig_prime1: self.varsig_prime1,
            theta_prime1: self.theta_prime1,
            pg_eq1,
            pg_eq2,
            pg_eq3,
            pg_eq4,
            psi_g1: *psi_g1,
            psi_g2: *psi_g2,
            pg_psi0_delta,
            pg_psi0_gen2,
            pg_psi0_yy,
            pg_psi0_ww1,
            pg_psi0_ww2,
            pg_rr_psi1,
            pg_psi0_tt,
            pg_psi0_psi1,
        };

        Ok(self
            .zk_proof
            .verify(&params, &instance, &verification_key, self.vv))
    }
}

/// Native R-free spend statement, witnesses and Sigma preparation. Counter commit is owned by the API wallet guard.
pub struct PreparedSpend {
    start_index: u64,
    amount: u64,
    signature: Signature,
    instance: SpendInstance,
    witness: SpendWitness,
    proof: crate::divisible::proofs::proof_spend::PreparedProof,
    varsig_prime2: G1Projective,
    theta_prime2: G1Projective,
}
impl Wallet {
    pub fn prepare_spend(
        &self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        sk_user: &SecretKeyUser,
        vv: u64,
    ) -> Result<PreparedSpend> {
        if vv == 0
            || self.l() == 0
            || self
                .l()
                .checked_add(vv - 1)
                .is_none_or(|end| end > params.capacity)
        {
            return Err(DivisibleEcashError::Spend(
                "The counter l is higher than max L".to_string(),
            ));
        }

        let grp = params.get_grp();
        let params_u = params.get_params_u();
        let params_a = params.get_params_a();
        // randomize signature in the wallet
        let (signature_prime, sign_blinding_factor) = self.signature().randomise(grp);
        // construct kappa i.e., blinded attributes for show
        let attributes = vec![sk_user.sk, self.v()];
        // compute kappa
        let kappa = compute_kappa(&grp, &verification_key, &attributes, sign_blinding_factor);

        let r1 = grp.random_scalar();
        let r2 = grp.random_scalar();
        let phi = Phi(
            grp.gen1() * r1,
            crate::msm1!(
                (params_u.get_ith_sigma(self.l() as usize), self.v),
                (params_u.get_ith_eta(vv as usize), r1)
            ),
        );

        // compute hash of the payment info
        let rr = Scalar::ZERO;
        let varphi = VarPhi(
            grp.gen1() * r2,
            crate::msm1!(
                (params_u.get_ith_theta(self.l() as usize), self.v),
                (params_u.get_ith_eta(vv as usize), r2)
            ),
        );

        // random value used to compute blinded bases
        let r_varsig1 = grp.random_scalar();
        let r_theta1 = grp.random_scalar();
        let r_varsig2 = grp.random_scalar();
        let r_theta2 = grp.random_scalar();
        let r_rr = grp.random_scalar();
        let r_ss = grp.random_scalar();
        let r_tt = grp.random_scalar();

        // compute blinded bases
        let psi_g1 = params_u.get_psi_g1();
        let psi_g2 = params_u.get_psi_g2();
        let varsig_prime1 = params_u.get_ith_sigma(self.l() as usize) + (psi_g1 * r_varsig1);
        let theta_prime1 = params_u.get_ith_theta(self.l() as usize) + (psi_g1 * r_theta1);
        let varsig_prime2 =
            params_u.get_ith_sigma(self.l() as usize + vv as usize - 1) + (psi_g1 * r_varsig2);
        let theta_prime2 =
            params_u.get_ith_theta(self.l() as usize + vv as usize - 1) + (psi_g1 * r_theta2);

        let tau_l_vv = params_u.get_ith_sps_sign(self.l() as usize + vv as usize - 1);
        let rr_prime = tau_l_vv.rr + (psi_g1 * r_rr);
        let ss_prime = tau_l_vv.ss + (psi_g1 * r_ss);
        let tt_prime = tau_l_vv.tt + (psi_g2 * r_tt);

        let rho1 = self.v.neg() * r_varsig1;
        let rho2 = self.v.neg() * r_theta1;
        let rho3 = r_rr * r_tt;

        let bases = params.install_pairing_bases(vv);
        let pg_psi0_delta = bases.pg_psi0_delta;
        let pg_psi0_gen2 = bases.pg_psi0_gen2;
        let pg_psi0_yy = bases.pg_psi0_yy;
        let pg_psi0_ww1 = bases.pg_psi0_ww1;
        let pg_psi0_ww2 = bases.pg_psi0_ww2;
        let pg_psi0_psi1 = bases.pg_psi0_psi1;
        let pg_rr_psi1 = pairing(&rr_prime.to_affine(), &psi_g2.to_affine());
        let pg_psi0_tt = pairing(&psi_g1.to_affine(), &tt_prime.to_affine());
        let pg_eq1 = crate::backend::pairing_product(&[
            (
                varsig_prime1.to_affine(),
                params_a.get_ith_delta((vv - 1) as usize).to_affine(),
            ),
            (-varsig_prime2.to_affine(), *grp.gen2()),
        ]);
        let pg_eq2 = crate::backend::pairing_product(&[
            (
                theta_prime1.to_affine(),
                params_a.get_ith_delta((vv - 1) as usize).to_affine(),
            ),
            (-theta_prime2.to_affine(), *grp.gen2()),
        ]);
        let pg_eq3 = crate::backend::pairing_product(&[
            (
                rr_prime.to_affine(),
                params_u.get_sps_pk().get_yy().to_affine(),
            ),
            (ss_prime.to_affine(), *grp.gen2()),
            (
                varsig_prime2.to_affine(),
                params_u.get_sps_pk().get_ith_ww(0).to_affine(),
            ),
            (
                theta_prime2.to_affine(),
                params_u.get_sps_pk().get_ith_ww(1).to_affine(),
            ),
        ]) - bases.pg_gen1_zz;
        let pg_eq4 = pairing(&rr_prime.to_affine(), &tt_prime.to_affine()) - bases.pg_gen1_gen2;

        let instance = SpendInstance {
            kappa,
            phi,
            varphi,
            rr,
            rr_prime,
            ss_prime,
            tt_prime,
            varsig_prime1,
            theta_prime1,
            pg_eq1,
            pg_eq2,
            pg_eq3,
            pg_eq4,
            psi_g1: *psi_g1,
            psi_g2: *psi_g2,
            pg_psi0_delta,
            pg_psi0_gen2,
            pg_psi0_yy,
            pg_psi0_ww1,
            pg_psi0_ww2,
            pg_rr_psi1,
            pg_psi0_tt,
            pg_psi0_psi1,
        };

        let witness = SpendWitness {
            sk_u: sk_user.clone(),
            v: self.v,
            r: sign_blinding_factor,
            r1,
            r2,
            r_varsig1,
            r_theta1,
            r_varsig2,
            r_theta2,
            r_rr,
            r_ss,
            r_tt,
            rho1,
            rho2,
            rho3,
        };

        let proof = crate::divisible::proofs::proof_spend::PreparedProof::prepare(
            params,
            &instance,
            &witness,
            verification_key,
            vv,
        );
        Ok(PreparedSpend {
            start_index: self.l(),
            amount: vv,
            signature: signature_prime,
            instance,
            witness,
            proof,
            varsig_prime2,
            theta_prime2,
        })
    }
}
impl PreparedSpend {
    pub fn start_index(&self) -> u64 {
        self.start_index
    }
    pub fn amount(&self) -> u64 {
        self.amount
    }
    pub fn finish(
        self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        pay_info: &PayInfo,
    ) -> Result<Payment> {
        let Self {
            mut instance,
            witness,
            proof,
            signature,
            varsig_prime2,
            theta_prime2,
            amount: vv,
            ..
        } = self;
        instance.rr = hash_to_scalar(pay_info.info);
        instance.varphi.1 += params.get_grp().gen1() * (instance.rr * witness.sk_u.sk);
        let zk_proof = proof.finish(params, &instance, &witness, verification_key, vv);
        Ok(Payment {
            kappa: instance.kappa,
            sig: signature,
            phi: instance.phi,
            varphi: instance.varphi,
            varsig_prime1: instance.varsig_prime1,
            varsig_prime2,
            theta_prime1: instance.theta_prime1,
            theta_prime2,
            rr_prime: instance.rr_prime,
            ss_prime: instance.ss_prime,
            tt_prime: instance.tt_prime,
            rr: instance.rr,
            zk_proof,
            vv,
        })
    }
}
