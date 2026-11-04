use crate::backend::{GtCompat, IntoMsm, NativeMsm, ScalarCompat};
use ff::Field;
use std::ops::Neg;
use std::ops::*;

use crate::backend::{G1Projective, G2Projective, Gt, Scalar};
use group::GroupEncoding;

use crate::divisible::proofs::{compute_challenge, produce_response, ChallengeDigest};
use crate::divisible::scheme::keygen::{SecretKeyUser, VerificationKeyAuth};
use crate::divisible::scheme::setup::Parameters;
use crate::divisible::scheme::{Phi, VarPhi};

pub struct SpendInstance {
    pub kappa: G2Projective,
    pub phi: Phi,
    pub varphi: VarPhi,
    pub rr: Scalar,
    pub rr_prime: G1Projective,
    pub ss_prime: G1Projective,
    pub tt_prime: G2Projective,
    pub varsig_prime1: G1Projective,
    pub theta_prime1: G1Projective,
    pub pg_eq1: Gt,
    pub pg_eq2: Gt,
    pub pg_eq3: Gt,
    pub pg_eq4: Gt,
    pub psi_g1: G1Projective,
    pub psi_g2: G2Projective,
    pub pg_psi0_delta: Gt,
    pub pg_psi0_gen2: Gt,
    pub pg_psi0_yy: Gt,
    pub pg_psi0_ww1: Gt,
    pub pg_psi0_ww2: Gt,
    pub pg_rr_psi1: Gt,
    pub pg_psi0_tt: Gt,
    pub pg_psi0_psi1: Gt,
}

impl SpendInstance {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(96 + 96 + 3 * 96 + 5 * 48 + 12 * 288);
        bytes.extend_from_slice(self.kappa.to_bytes().as_ref());
        bytes.extend_from_slice(self.phi.to_bytes().as_ref());
        bytes.extend_from_slice(self.varphi.to_bytes().as_ref());
        bytes.extend_from_slice(self.rr.to_bytes().as_ref());
        bytes.extend_from_slice(self.rr_prime.to_bytes().as_ref());
        bytes.extend_from_slice(self.ss_prime.to_bytes().as_ref());
        bytes.extend_from_slice(self.tt_prime.to_bytes().as_ref());
        bytes.extend_from_slice(self.varsig_prime1.to_bytes().as_ref());
        bytes.extend_from_slice(self.theta_prime1.to_bytes().as_ref());
        bytes.extend_from_slice(self.pg_eq1.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_eq2.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_eq3.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_eq4.to_compressed().as_ref());
        bytes.extend_from_slice(self.psi_g1.to_bytes().as_ref());
        bytes.extend_from_slice(self.psi_g2.to_bytes().as_ref());
        bytes.extend_from_slice(self.pg_psi0_delta.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_psi0_gen2.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_psi0_yy.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_psi0_ww1.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_psi0_ww2.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_rr_psi1.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_psi0_tt.to_compressed().as_ref());
        bytes.extend_from_slice(self.pg_psi0_psi1.to_compressed().as_ref());

        bytes
    }
}

pub struct SpendWitness {
    pub sk_u: SecretKeyUser,
    pub v: Scalar,
    pub r: Scalar,
    pub r1: Scalar,
    pub r2: Scalar,
    pub r_varsig1: Scalar,
    pub r_theta1: Scalar,
    pub r_varsig2: Scalar,
    pub r_theta2: Scalar,
    pub r_rr: Scalar,
    pub r_ss: Scalar,
    pub r_tt: Scalar,
    pub rho1: Scalar,
    pub rho2: Scalar,
    pub rho3: Scalar,
}

#[derive(Debug, Clone)]
pub struct SpendProof {
    challenge: Scalar,
    response_r: Scalar,
    response_r_sk_u: Scalar,
    response_r_v: Scalar,
    response_r_r: Scalar,
    response_r_r1: Scalar,
    response_r_r2: Scalar,
    response_r_varsig1: Scalar,
    response_r_theta1: Scalar,
    response_r_varsig2: Scalar,
    response_r_theta2: Scalar,
    response_r_rr: Scalar,
    response_r_ss: Scalar,
    response_r_tt: Scalar,
    response_r_rho1: Scalar,
    response_r_rho2: Scalar,
    response_r_rho3: Scalar,
}

impl SpendProof {
    pub fn construct(
        params: &Parameters,
        instance: &SpendInstance,
        witness: &SpendWitness,
        verification_key: &VerificationKeyAuth,
        vv: u64,
    ) -> Self {
        let grp = params.get_grp();
        let params_u = params.get_params_u();
        // let params_a = params.get_params_a();

        // generate random values to replace each witness
        let r_attributes = grp.n_random_scalars(2);
        let r_sk_u = r_attributes[0];
        let r_v = r_attributes[1];
        let r_r = grp.random_scalar();
        let r_r1 = grp.random_scalar();
        let r_r2 = grp.random_scalar();
        let r_r_varsig1 = grp.random_scalar();
        let r_r_theta1 = grp.random_scalar();
        let r_r_varsig2 = grp.random_scalar();
        let r_r_theta2 = grp.random_scalar();
        let r_r_rr = grp.random_scalar();
        let r_r_ss = grp.random_scalar();
        let r_r_tt = grp.random_scalar();
        let r_rho1 = grp.random_scalar();
        let r_rho2 = grp.random_scalar();
        let r_rho3 = grp.random_scalar();

        let g1 = grp.gen1();

        // compute zkp commitment for each instance
        let zkcm_kappa = grp.gen2() * r_r
            + verification_key.alpha
            + r_attributes
                .iter()
                .zip(verification_key.beta_g2.iter())
                .map(|(attr, beta_i)| (*beta_i, *attr))
                .collect::<Vec<_>>()
                .msm();

        let zkcm_phi0 = g1 * r_r1;
        let zkcm_phi1 = crate::msm1!(
            (instance.varsig_prime1, r_v),
            (instance.psi_g1, r_rho1),
            (params_u.get_ith_eta(vv as usize), r_r1)
        );
        let zkcm_varphi0 = g1 * r_r2;
        let zkcm_varphi1 = crate::msm1!(
            (g1, instance.rr * r_sk_u),
            (instance.theta_prime1, r_v),
            (instance.psi_g1, r_rho2),
            (params_u.get_ith_eta(vv as usize), r_r2)
        );
        let zkcm_pg_eq1 =
            instance.pg_psi0_delta * r_r_varsig1 + instance.pg_psi0_gen2 * r_r_varsig2.neg();
        let zkcm_pg_eq2 =
            instance.pg_psi0_delta * r_r_theta1 + instance.pg_psi0_gen2 * r_r_theta2.neg();
        let zkcm_pg_eq3 = instance.pg_psi0_yy * r_r_rr
            + instance.pg_psi0_gen2 * r_r_ss
            + instance.pg_psi0_ww1 * r_r_varsig2
            + instance.pg_psi0_ww2 * r_r_theta2;
        let zkcm_pg_eq4 = instance.pg_rr_psi1 * r_r_tt
            + instance.pg_psi0_tt * r_r_rr
            + instance.pg_psi0_psi1 * r_rho3.neg();

        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            std::iter::once(g1.to_bytes().as_ref())
                .chain(std::iter::once(instance.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_kappa.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_phi0.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_phi1.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_varphi0.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_varphi1.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq1.to_compressed().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq2.to_compressed().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq3.to_compressed().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq4.to_compressed().as_ref())),
        );

        // compute response for each witness
        let response_r = produce_response(&r_r, &challenge, &witness.r);
        let response_r_sk_u = produce_response(&r_sk_u, &challenge, &witness.sk_u.sk);
        let response_r_v = produce_response(&r_v, &challenge, &witness.v);
        let response_r_r = produce_response(&r_r, &challenge, &witness.r);
        let response_r_r1 = produce_response(&r_r1, &challenge, &witness.r1);
        let response_r_r2 = produce_response(&r_r2, &challenge, &witness.r2);
        let response_r_varsig1 = produce_response(&r_r_varsig1, &challenge, &witness.r_varsig1);
        let response_r_theta1 = produce_response(&r_r_theta1, &challenge, &witness.r_theta1);
        let response_r_varsig2 = produce_response(&r_r_varsig2, &challenge, &witness.r_varsig2);
        let response_r_theta2 = produce_response(&r_r_theta2, &challenge, &witness.r_theta2);
        let response_r_rr = produce_response(&r_r_rr, &challenge, &witness.r_rr);
        let response_r_ss = produce_response(&r_r_ss, &challenge, &witness.r_ss);
        let response_r_tt = produce_response(&r_r_tt, &challenge, &witness.r_tt);
        let response_r_rho1 = produce_response(&r_rho1, &challenge, &witness.rho1);
        let response_r_rho2 = produce_response(&r_rho2, &challenge, &witness.rho2);
        let response_r_rho3 = produce_response(&r_rho3, &challenge, &witness.rho3);

        SpendProof {
            challenge,
            response_r,
            response_r_sk_u,
            response_r_v,
            response_r_r,
            response_r_r1,
            response_r_r2,
            response_r_varsig1,
            response_r_theta1,
            response_r_varsig2,
            response_r_theta2,
            response_r_rr,
            response_r_ss,
            response_r_tt,
            response_r_rho1,
            response_r_rho2,
            response_r_rho3,
        }
    }

    pub fn verify(
        &self,
        params: &Parameters,
        instance: &SpendInstance,
        verification_key: &VerificationKeyAuth,
        vv: u64,
    ) -> bool {
        let grp = params.get_grp();
        let params_u = params.get_params_u();
        // let params_a = params.get_params_a();
        let g1 = grp.gen1();

        // re-compute each zkp commitment
        let zkcm_kappa = instance.kappa * self.challenge
            + grp.gen2() * self.response_r
            + verification_key.alpha * (Scalar::one() - self.challenge)
            + [self.response_r_sk_u, self.response_r_v]
                .iter()
                .zip(verification_key.beta_g2.iter())
                .map(|(attr, beta_i)| (*beta_i, *attr))
                .collect::<Vec<_>>()
                .msm();

        let zkcm_phi0 = crate::msm1!((g1, self.response_r_r1), (instance.phi.0, self.challenge));
        let zkcm_phi1 = crate::msm1!(
            (instance.varsig_prime1, self.response_r_v),
            (instance.psi_g1, self.response_r_rho1),
            (params_u.get_ith_eta(vv as usize), self.response_r_r1),
            (instance.phi.1, self.challenge)
        );
        let zkcm_varphi0 = crate::msm1!(
            (g1, self.response_r_r2),
            (instance.varphi.0, self.challenge)
        );
        let zkcm_varphi1 = crate::msm1!(
            (g1, instance.rr * self.response_r_sk_u),
            (instance.theta_prime1, self.response_r_v),
            (instance.psi_g1, self.response_r_rho2),
            (params_u.get_ith_eta(vv as usize), self.response_r_r2),
            (instance.varphi.1, self.challenge)
        );
        let zkcm_pg_eq1 = instance.pg_psi0_delta * self.response_r_varsig1
            + instance.pg_psi0_gen2 * self.response_r_varsig2.neg()
            + instance.pg_eq1 * self.challenge;
        let zkcm_pg_eq2 = instance.pg_psi0_delta * self.response_r_theta1
            + instance.pg_psi0_gen2 * self.response_r_theta2.neg()
            + instance.pg_eq2 * self.challenge;

        let zkcm_pg_eq3 = instance.pg_psi0_yy * self.response_r_rr
            + instance.pg_psi0_gen2 * self.response_r_ss
            + instance.pg_psi0_ww1 * self.response_r_varsig2
            + instance.pg_psi0_ww2 * self.response_r_theta2
            + instance.pg_eq3 * self.challenge;

        let zkcm_pg_eq4 = instance.pg_rr_psi1 * self.response_r_tt
            + instance.pg_psi0_tt * self.response_r_rr
            + instance.pg_psi0_psi1 * self.response_r_rho3.neg()
            + instance.pg_eq4 * self.challenge;

        // re-compute the challenge
        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            std::iter::once(g1.to_bytes().as_ref())
                .chain(std::iter::once(instance.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_kappa.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_phi0.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_phi1.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_varphi0.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_varphi1.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq1.to_compressed().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq2.to_compressed().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq3.to_compressed().as_ref()))
                .chain(std::iter::once(zkcm_pg_eq4.to_compressed().as_ref())),
        );

        challenge == self.challenge
    }
}

impl SpendProof {
    pub(crate) fn encode(&self, out: &mut Vec<u8>) {
        out.extend(self.challenge.to_bytes());
        out.extend(self.response_r.to_bytes());
        out.extend(self.response_r_sk_u.to_bytes());
        out.extend(self.response_r_v.to_bytes());
        out.extend(self.response_r_r1.to_bytes());
        out.extend(self.response_r_r2.to_bytes());
        out.extend(self.response_r_varsig1.to_bytes());
        out.extend(self.response_r_theta1.to_bytes());
        out.extend(self.response_r_varsig2.to_bytes());
        out.extend(self.response_r_theta2.to_bytes());
        out.extend(self.response_r_rr.to_bytes());
        out.extend(self.response_r_ss.to_bytes());
        out.extend(self.response_r_tt.to_bytes());
        out.extend(self.response_r_rho1.to_bytes());
        out.extend(self.response_r_rho2.to_bytes());
        out.extend(self.response_r_rho3.to_bytes());
    }
    pub(crate) fn decode(
        r: &mut crate::backend::Reader,
        _k: usize,
    ) -> std::result::Result<Self, String> {
        let challenge = r.scalar()?;
        let response_r = r.scalar()?;
        Ok(Self {
            challenge,
            response_r,
            response_r_sk_u: r.scalar()?,
            response_r_v: r.scalar()?,
            response_r_r: response_r,
            response_r_r1: r.scalar()?,
            response_r_r2: r.scalar()?,
            response_r_varsig1: r.scalar()?,
            response_r_theta1: r.scalar()?,
            response_r_varsig2: r.scalar()?,
            response_r_theta2: r.scalar()?,
            response_r_rr: r.scalar()?,
            response_r_ss: r.scalar()?,
            response_r_tt: r.scalar()?,
            response_r_rho1: r.scalar()?,
            response_r_rho2: r.scalar()?,
            response_r_rho3: r.scalar()?,
        })
    }
    pub(crate) fn valid_shape(&self, k: usize) -> bool {
        let _ = k;
        true
    }
    pub fn with_invalid_challenge(&self) -> Self {
        let mut p = self.clone();
        p.challenge += Scalar::ONE;
        p
    }
}

/// Context-free native Sigma first messages and one-use response randomness.
pub(crate) struct PreparedProof {
    r_attributes: Vec<Scalar>,
    r_r: Scalar,
    r_r1: Scalar,
    r_r2: Scalar,
    r_r_varsig1: Scalar,
    r_r_theta1: Scalar,
    r_r_varsig2: Scalar,
    r_r_theta2: Scalar,
    r_r_rr: Scalar,
    r_r_ss: Scalar,
    r_r_tt: Scalar,
    r_rho1: Scalar,
    r_rho2: Scalar,
    r_rho3: Scalar,
    prefix: Vec<u8>,
    suffix: Vec<u8>,
    zkcm_kappa: [u8; 96],
    zkcm_phi0: [u8; 48],
    zkcm_phi1: [u8; 48],
    zkcm_varphi0: [u8; 48],
    zkcm_varphi1_without_r: G1Projective,
    gt_messages: [[u8; 288]; 4],
}
impl PreparedProof {
    pub(crate) fn prepare(
        params: &Parameters,
        instance: &SpendInstance,
        _witness: &SpendWitness,
        verification_key: &VerificationKeyAuth,
        vv: u64,
    ) -> Self {
        let grp = params.get_grp();
        let params_u = params.get_params_u();
        // let params_a = params.get_params_a();

        // generate random values to replace each witness
        let r_attributes = grp.n_random_scalars(2);
        let r_sk_u = r_attributes[0];
        let r_v = r_attributes[1];
        let r_r = grp.random_scalar();
        let r_r1 = grp.random_scalar();
        let r_r2 = grp.random_scalar();
        let r_r_varsig1 = grp.random_scalar();
        let r_r_theta1 = grp.random_scalar();
        let r_r_varsig2 = grp.random_scalar();
        let r_r_theta2 = grp.random_scalar();
        let r_r_rr = grp.random_scalar();
        let r_r_ss = grp.random_scalar();
        let r_r_tt = grp.random_scalar();
        let r_rho1 = grp.random_scalar();
        let r_rho2 = grp.random_scalar();
        let r_rho3 = grp.random_scalar();

        let g1 = grp.gen1();

        // compute zkp commitment for each instance
        let zkcm_kappa = grp.gen2() * r_r
            + verification_key.alpha
            + r_attributes
                .iter()
                .zip(verification_key.beta_g2.iter())
                .map(|(attr, beta_i)| (*beta_i, *attr))
                .collect::<Vec<_>>()
                .msm();

        let zkcm_phi0 = g1 * r_r1;
        let zkcm_phi1 = crate::msm1!(
            (instance.varsig_prime1, r_v),
            (instance.psi_g1, r_rho1),
            (params_u.get_ith_eta(vv as usize), r_r1)
        );
        let zkcm_varphi0 = g1 * r_r2;
        let zkcm_varphi1_without_r = crate::msm1!(
            (instance.theta_prime1, r_v),
            (instance.psi_g1, r_rho2),
            (params_u.get_ith_eta(vv as usize), r_r2)
        );
        let zkcm_pg_eq1 =
            instance.pg_psi0_delta * r_r_varsig1 + instance.pg_psi0_gen2 * r_r_varsig2.neg();
        let zkcm_pg_eq2 =
            instance.pg_psi0_delta * r_r_theta1 + instance.pg_psi0_gen2 * r_r_theta2.neg();
        let zkcm_pg_eq3 = instance.pg_psi0_yy * r_r_rr
            + instance.pg_psi0_gen2 * r_r_ss
            + instance.pg_psi0_ww1 * r_r_varsig2
            + instance.pg_psi0_ww2 * r_r_theta2;
        let zkcm_pg_eq4 = instance.pg_rr_psi1 * r_r_tt
            + instance.pg_psi0_tt * r_r_rr
            + instance.pg_psi0_psi1 * r_rho3.neg();

        let bytes = instance.to_bytes();
        let mut prefix = g1.to_bytes().to_vec();
        prefix.extend_from_slice(&bytes[..240]);
        let suffix = bytes[320..].to_vec();
        Self {
            r_attributes,
            r_r,
            r_r1,
            r_r2,
            r_r_varsig1,
            r_r_theta1,
            r_r_varsig2,
            r_r_theta2,
            r_r_rr,
            r_r_ss,
            r_r_tt,
            r_rho1,
            r_rho2,
            r_rho3,

            prefix,
            suffix,
            zkcm_kappa: zkcm_kappa.to_bytes(),
            zkcm_phi0: zkcm_phi0.to_bytes(),
            zkcm_phi1: zkcm_phi1.to_bytes(),
            zkcm_varphi0: zkcm_varphi0.to_bytes(),
            zkcm_varphi1_without_r,
            gt_messages: [
                zkcm_pg_eq1.to_compressed(),
                zkcm_pg_eq2.to_compressed(),
                zkcm_pg_eq3.to_compressed(),
                zkcm_pg_eq4.to_compressed(),
            ],
        }
    }
    pub(crate) fn finish(
        self,
        params: &Parameters,
        instance: &SpendInstance,
        witness: &SpendWitness,
        _verification_key: &VerificationKeyAuth,
        _vv: u64,
    ) -> SpendProof {
        let Self {
            r_attributes,
            r_r,
            r_r1,
            r_r2,
            r_r_varsig1,
            r_r_theta1,
            r_r_varsig2,
            r_r_theta2,
            r_r_rr,
            r_r_ss,
            r_r_tt,
            r_rho1,
            r_rho2,
            r_rho3,

            prefix,
            suffix,
            zkcm_kappa,
            zkcm_phi0,
            zkcm_phi1,
            zkcm_varphi0,
            zkcm_varphi1_without_r,
            gt_messages,
        } = self;
        let r_sk_u = r_attributes[0];
        let r_v = r_attributes[1];
        let varphi = instance.varphi.1.to_bytes();
        let rr = instance.rr.to_bytes();
        let dynamic =
            (zkcm_varphi1_without_r + params.get_grp().gen1() * (instance.rr * r_sk_u)).to_bytes();
        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            [
                prefix.as_slice(),
                varphi.as_slice(),
                rr.as_slice(),
                suffix.as_slice(),
                zkcm_kappa.as_slice(),
                zkcm_phi0.as_slice(),
                zkcm_phi1.as_slice(),
                zkcm_varphi0.as_slice(),
                dynamic.as_slice(),
                gt_messages[0].as_slice(),
                gt_messages[1].as_slice(),
                gt_messages[2].as_slice(),
                gt_messages[3].as_slice(),
            ]
            .into_iter(),
        );
        // compute response for each witness
        let response_r = produce_response(&r_r, &challenge, &witness.r);
        let response_r_sk_u = produce_response(&r_sk_u, &challenge, &witness.sk_u.sk);
        let response_r_v = produce_response(&r_v, &challenge, &witness.v);
        let response_r_r = produce_response(&r_r, &challenge, &witness.r);
        let response_r_r1 = produce_response(&r_r1, &challenge, &witness.r1);
        let response_r_r2 = produce_response(&r_r2, &challenge, &witness.r2);
        let response_r_varsig1 = produce_response(&r_r_varsig1, &challenge, &witness.r_varsig1);
        let response_r_theta1 = produce_response(&r_r_theta1, &challenge, &witness.r_theta1);
        let response_r_varsig2 = produce_response(&r_r_varsig2, &challenge, &witness.r_varsig2);
        let response_r_theta2 = produce_response(&r_r_theta2, &challenge, &witness.r_theta2);
        let response_r_rr = produce_response(&r_r_rr, &challenge, &witness.r_rr);
        let response_r_ss = produce_response(&r_r_ss, &challenge, &witness.r_ss);
        let response_r_tt = produce_response(&r_r_tt, &challenge, &witness.r_tt);
        let response_r_rho1 = produce_response(&r_rho1, &challenge, &witness.rho1);
        let response_r_rho2 = produce_response(&r_rho2, &challenge, &witness.rho2);
        let response_r_rho3 = produce_response(&r_rho3, &challenge, &witness.rho3);

        SpendProof {
            challenge,
            response_r,
            response_r_sk_u,
            response_r_v,
            response_r_r,
            response_r_r1,
            response_r_r2,
            response_r_varsig1,
            response_r_theta1,
            response_r_varsig2,
            response_r_theta2,
            response_r_rr,
            response_r_ss,
            response_r_tt,
            response_r_rho1,
            response_r_rho2,
            response_r_rho3,
        }
    }
}
