use crate::backend::{GtCompat, IntoMsm, NativeMsm, ScalarCompat};
use ff::Field;
use std::ops::*;

use crate::backend::{G1Projective, G2Projective, Scalar};
use group::{Curve, GroupEncoding};

use crate::compact::proofs::{
    compute_challenge, produce_response, produce_responses, ChallengeDigest,
};
use crate::compact::scheme::keygen::VerificationKeyAuth;
use crate::compact::scheme::setup::Parameters;

#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct SpendInstance {
    pub kappa: G2Projective,
    pub cc: G1Projective,
    pub aa: Vec<G1Projective>,
    pub ss: Vec<G1Projective>,
    pub tt: Vec<G1Projective>,
    pub kappa_k: Vec<G2Projective>,
}

impl SpendInstance {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut bytes: Vec<u8> = Default::default();
        bytes.extend_from_slice(self.kappa.to_bytes().as_ref());

        bytes.extend_from_slice(&self.aa.len().to_le_bytes());
        for a in &self.aa {
            bytes.extend_from_slice(&a.to_affine().to_compressed());
        }

        bytes.extend_from_slice(self.cc.to_bytes().as_ref());

        bytes.extend_from_slice(&self.ss.len().to_le_bytes());
        for s in &self.ss {
            bytes.extend_from_slice(&s.to_affine().to_compressed());
        }
        bytes.extend_from_slice(&self.tt.len().to_le_bytes());
        for t in &self.tt {
            bytes.extend_from_slice(&t.to_affine().to_compressed());
        }

        bytes.extend_from_slice(&self.kappa_k.len().to_le_bytes());
        for k in &self.kappa_k {
            bytes.extend_from_slice(&k.to_affine().to_compressed());
        }
        bytes
    }
}

pub struct SpendWitness {
    // includes skUser, v, t
    pub attributes: Vec<Scalar>,
    // signature randomizing element
    pub r: Scalar,
    pub o_c: Scalar,
    pub lk: Vec<Scalar>,
    pub o_a: Vec<Scalar>,
    pub mu: Vec<Scalar>,
    pub o_mu: Vec<Scalar>,
    pub r_k: Vec<Scalar>,
}

#[derive(Debug, Clone)]
pub struct SpendProof {
    challenge: Scalar,
    response_r: Scalar,
    response_r_l: Vec<Scalar>,
    response_l: Vec<Scalar>,
    response_o_a: Vec<Scalar>,
    response_o_c: Scalar,
    response_mu: Vec<Scalar>,
    response_o_mu: Vec<Scalar>,
    response_attributes: Vec<Scalar>,
}

/// One-use native first-message preparation. The original Fiat-Shamir byte
/// stream is cached around its two context-dependent T vectors.
pub struct PreparedProof {
    r_attributes: Vec<Scalar>,
    r_r: Scalar,
    r_o_c: Scalar,
    r_r_lk: Vec<Scalar>,
    r_lk: Vec<Scalar>,
    r_o_a: Vec<Scalar>,
    r_mu: Vec<Scalar>,
    r_o_mu: Vec<Scalar>,
    before_tt: Vec<u8>,
    after_tt: Vec<u8>,
    gamma11: Vec<[u8; 48]>,
}

impl PreparedProof {
    pub fn prepare(
        params: &Parameters,
        instance: &SpendInstance,
        witness: &SpendWitness,
        verification_key: &VerificationKeyAuth,
    ) -> Self {
        let grparams = params.grp();
        // Preserve the native Construct RNG sequence exactly.
        let r_attributes = grparams.n_random_scalars(witness.attributes.len());
        let r_v = r_attributes[1];
        let r_r = grparams.random_scalar();
        let r_o_c = grparams.random_scalar();
        let r_r_lk = grparams.n_random_scalars(witness.r_k.len());
        let r_lk = grparams.n_random_scalars(witness.lk.len());
        let r_o_a = grparams.n_random_scalars(witness.o_a.len());
        let r_mu = grparams.n_random_scalars(witness.mu.len());
        let r_o_mu = grparams.n_random_scalars(witness.o_mu.len());
        let g1 = *grparams.gen1();
        let gamma1 = *grparams.gamma1();
        let zkcm_kappa = grparams.gen2() * r_r
            + verification_key.alpha
            + r_attributes
                .iter()
                .zip(verification_key.beta_g2.iter())
                .map(|(attr, beta_i)| (*beta_i, *attr))
                .collect::<Vec<_>>()
                .msm();
        let zkcm_cc = crate::msm1!((g1, r_o_c), (gamma1, r_v));
        let zkcm_aa: Vec<_> = r_o_a
            .iter()
            .zip(&r_lk)
            .map(|(o, l)| crate::msm1!((g1, o), (gamma1, l)))
            .collect();
        let zkcm_ss: Vec<_> = r_mu.iter().map(|r| grparams.delta() * r).collect();
        let gamma11: Vec<_> = instance
            .aa
            .iter()
            .zip(&r_mu)
            .zip(&r_o_mu)
            .map(|((aa, mu), o)| crate::msm1!((aa + instance.cc + gamma1, mu), (g1, o)).to_bytes())
            .collect();
        let zkcm_kappa_k: Vec<_> = r_lk
            .iter()
            .zip(&r_r_lk)
            .map(|(l, r)| {
                (params.pk_rp().alpha
                    + crate::msm2!((params.pk_rp().beta, l), (grparams.gen2(), r)))
                .to_bytes()
            })
            .collect();

        // Exactly the original g1,gamma1,vk,instance byte order; the instance's
        // T-vector is inserted later between SS and kappa_k.
        let mut before_tt = vec![];
        before_tt.extend(g1.to_bytes());
        before_tt.extend(gamma1.to_bytes());
        before_tt.extend(verification_key.alpha.to_bytes());
        for point in &verification_key.beta_g2 {
            before_tt.extend(point.to_bytes());
        }
        before_tt.extend(instance.kappa.to_bytes());
        before_tt.extend(instance.aa.len().to_le_bytes());
        for point in &instance.aa {
            before_tt.extend(point.to_bytes());
        }
        before_tt.extend(instance.cc.to_bytes());
        before_tt.extend(instance.ss.len().to_le_bytes());
        for point in &instance.ss {
            before_tt.extend(point.to_bytes());
        }
        before_tt.extend(witness.mu.len().to_le_bytes());

        let mut after_tt = vec![];
        after_tt.extend(instance.kappa_k.len().to_le_bytes());
        for point in &instance.kappa_k {
            after_tt.extend(point.to_bytes());
        }
        after_tt.extend(zkcm_kappa.to_bytes());
        after_tt.extend(zkcm_cc.to_bytes());
        for point in &zkcm_aa {
            after_tt.extend(point.to_bytes());
        }
        for point in &zkcm_ss {
            after_tt.extend(point.to_bytes());
        }
        for bytes in zkcm_kappa_k {
            after_tt.extend(bytes);
        }
        Self {
            r_attributes,
            r_r,
            r_o_c,
            r_r_lk,
            r_lk,
            r_o_a,
            r_mu,
            r_o_mu,
            before_tt,
            after_tt,
            gamma11,
        }
    }

    pub fn finish(
        self,
        params: &Parameters,
        instance: &SpendInstance,
        witness: &SpendWitness,
        _verification_key: &VerificationKeyAuth,
        rr: &[Scalar],
    ) -> SpendProof {
        assert_eq!(rr.len(), self.r_mu.len());
        assert_eq!(instance.tt.len(), self.r_mu.len());
        let g1 = *params.grp().gen1();
        let zkcm_tt: Vec<_> = rr
            .iter()
            .zip(&self.r_mu)
            .map(|(r, mu)| (g1 * (self.r_attributes[0] + r * mu)).to_bytes())
            .collect();
        let tt: Vec<_> = instance.tt.iter().map(|t| t.to_bytes()).collect();
        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            std::iter::once(self.before_tt.as_slice())
                .chain(tt.iter().map(|b| b.as_slice()))
                .chain(std::iter::once(self.after_tt.as_slice()))
                .chain(zkcm_tt.iter().map(|b| b.as_slice()))
                .chain(self.gamma11.iter().map(|b| b.as_slice())),
        );
        SpendProof {
            challenge,
            response_r: produce_response(&self.r_r, &challenge, &witness.r),
            response_r_l: produce_responses(&self.r_r_lk, &challenge, &witness.r_k),
            response_l: produce_responses(&self.r_lk, &challenge, &witness.lk),
            response_o_a: produce_responses(&self.r_o_a, &challenge, &witness.o_a),
            response_o_c: produce_response(&self.r_o_c, &challenge, &witness.o_c),
            response_mu: produce_responses(&self.r_mu, &challenge, &witness.mu),
            response_o_mu: produce_responses(&self.r_o_mu, &challenge, &witness.o_mu),
            response_attributes: produce_responses(
                &self.r_attributes,
                &challenge,
                &witness.attributes.iter().collect::<Vec<_>>(),
            ),
        }
    }
}

impl SpendProof {
    pub fn construct(
        params: &Parameters,
        instance: &SpendInstance,
        witness: &SpendWitness,
        verification_key: &VerificationKeyAuth,
        rr: &[Scalar],
    ) -> Self {
        let grparams = params.grp();
        // generate random values to replace each witness
        let r_attributes = grparams.n_random_scalars(witness.attributes.len());
        let r_sk = r_attributes[0];
        let r_v = r_attributes[1];
        let r_r = grparams.random_scalar();
        let r_o_c = grparams.random_scalar();

        let r_r_lk = grparams.n_random_scalars(witness.r_k.len());
        let r_lk = grparams.n_random_scalars(witness.lk.len());
        let r_o_a = grparams.n_random_scalars(witness.o_a.len());
        let r_mu = grparams.n_random_scalars(witness.mu.len());
        let r_o_mu = grparams.n_random_scalars(witness.o_mu.len());

        let g1 = *grparams.gen1();
        let gamma1 = *grparams.gamma1();
        let beta2_bytes = verification_key
            .beta_g2
            .iter()
            .map(|beta_i| beta_i.to_bytes())
            .collect::<Vec<_>>();

        // compute zkp commitment for each instance
        let zkcm_kappa = grparams.gen2() * r_r
            + verification_key.alpha
            + r_attributes
                .iter()
                .zip(verification_key.beta_g2.iter())
                .map(|(attr, beta_i)| (*beta_i, *attr))
                .collect::<Vec<_>>()
                .msm();

        let zkcm_cc = crate::msm1!((g1, r_o_c), (gamma1, r_v));

        let zkcm_aa: Vec<G1Projective> = r_o_a
            .iter()
            .zip(r_lk.iter())
            .map(|(r_o_a_k, r_l_k)| crate::msm1!((g1, r_o_a_k), (gamma1, r_l_k)))
            .collect::<Vec<_>>();

        let zkcm_aa_bytes = zkcm_aa.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();

        let zkcm_ss = r_mu
            .iter()
            .map(|r_mu_k| grparams.delta() * r_mu_k)
            .collect::<Vec<_>>();

        let zkcm_ss_bytes = zkcm_ss.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();

        let zkcm_tt = rr
            .iter()
            .zip(r_mu.iter())
            .map(|(rr_k, r_mu_k)| g1 * (r_sk + rr_k * r_mu_k))
            .collect::<Vec<_>>();

        let zkcm_tt_bytes = zkcm_tt.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();

        let zkcm_gamma11 = instance
            .aa
            .iter()
            .zip(r_mu.iter())
            .zip(r_o_mu.iter())
            .map(|((aa_k, r_mu_k), r_o_mu_k)| {
                crate::msm1!((aa_k + instance.cc + gamma1, r_mu_k), (g1, r_o_mu_k))
            })
            .collect::<Vec<_>>();

        let zkcm_gamma11_bytes = zkcm_gamma11
            .iter()
            .map(|x| x.to_bytes())
            .collect::<Vec<_>>();

        let zkcm_kappa_k = r_lk
            .iter()
            .zip(r_r_lk.iter())
            .map(|(r_k, r_r_k)| {
                params.pk_rp().alpha
                    + crate::msm2!((params.pk_rp().beta, r_k), (grparams.gen2(), r_r_k))
            })
            .collect::<Vec<_>>();

        let zkcm_kappa_k_bytes = zkcm_kappa_k
            .iter()
            .map(|x| x.to_bytes())
            .collect::<Vec<_>>();

        // compute the challenge
        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            std::iter::once(grparams.gen1().to_bytes().as_ref())
                .chain(std::iter::once(gamma1.to_bytes().as_ref()))
                .chain(std::iter::once(verification_key.alpha.to_bytes().as_ref()))
                .chain(beta2_bytes.iter().map(|b| b.as_ref()))
                .chain(std::iter::once(instance.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_kappa.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_cc.to_bytes().as_ref()))
                .chain(zkcm_aa_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_ss_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_kappa_k_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_tt_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_gamma11_bytes.iter().map(|x| x.as_ref())),
        );

        // compute response for each witness
        let response_attributes = produce_responses(
            &r_attributes,
            &challenge,
            &witness.attributes.iter().collect::<Vec<_>>(),
        );
        let response_r = produce_response(&r_r, &challenge, &witness.r);
        let response_r_l = produce_responses(&r_r_lk, &challenge, &witness.r_k);
        let response_l = produce_responses(&r_lk, &challenge, &witness.lk);
        let response_o_a = produce_responses(&r_o_a, &challenge, &witness.o_a);
        let response_o_c = produce_response(&r_o_c, &challenge, &witness.o_c);

        let response_mu = produce_responses(&r_mu, &challenge, &witness.mu);
        let response_o_mu = produce_responses(&r_o_mu, &challenge, &witness.o_mu);

        SpendProof {
            challenge,
            response_r,
            response_r_l,
            response_l,
            response_o_a,
            response_o_c,
            response_mu,
            response_o_mu,
            response_attributes,
        }
    }
    pub fn verify(
        &self,
        params: &Parameters,
        instance: &SpendInstance,
        verification_key: &VerificationKeyAuth,
        rr: &[Scalar],
    ) -> bool {
        let grparams = params.grp();
        let g1 = *grparams.gen1();
        let gamma1 = *grparams.gamma1();
        let beta2_bytes = verification_key
            .beta_g2
            .iter()
            .map(|beta_i| beta_i.to_bytes())
            .collect::<Vec<_>>();

        // re-compute each zkp commitment
        let zkcm_kappa = instance.kappa * self.challenge
            + grparams.gen2() * self.response_r
            + verification_key.alpha * (Scalar::one() - self.challenge)
            + self
                .response_attributes
                .iter()
                .zip(verification_key.beta_g2.iter())
                .map(|(attr, beta_i)| (*beta_i, *attr))
                .collect::<Vec<_>>()
                .msm();

        let zkcm_aa = self
            .response_o_a
            .iter()
            .zip(self.response_l.iter())
            .zip(instance.aa.iter())
            .map(|((resp_o_a_k, resp_l_k), aa_k)| {
                crate::msm1!((g1, resp_o_a_k), (gamma1, resp_l_k), (aa_k, self.challenge))
            })
            .collect::<Vec<_>>();

        let zkcm_aa_bytes = zkcm_aa.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();

        let zkcm_cc = crate::msm1!(
            (g1, self.response_o_c),
            (gamma1, self.response_attributes[1]),
            (instance.cc, self.challenge)
        );

        let zkcm_ss = self
            .response_mu
            .iter()
            .zip(instance.ss.iter())
            .map(|(resp_mu_k, ss_k)| {
                crate::msm1!((grparams.delta(), resp_mu_k), (ss_k, self.challenge))
            })
            .collect::<Vec<_>>();

        let zkcm_ss_bytes = zkcm_ss.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();

        let zkcm_tt = self
            .response_mu
            .iter()
            .zip(rr.iter())
            .zip(instance.tt.iter())
            .map(|((resp_mu_k, rr_k), tt_k)| {
                crate::msm1!(
                    (g1, self.response_attributes[0] + rr_k * resp_mu_k),
                    (tt_k, self.challenge)
                )
            })
            .collect::<Vec<_>>();

        let zkcm_tt_bytes = zkcm_tt.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();

        let zkcm_gamma11 = instance
            .aa
            .iter()
            .zip(self.response_mu.iter())
            .zip(self.response_o_mu.iter())
            .map(|((aa_k, resp_mu_k), resp_o_mu_k)| {
                crate::msm1!(
                    (aa_k + instance.cc + gamma1, resp_mu_k),
                    (g1, resp_o_mu_k),
                    (gamma1, self.challenge)
                )
            })
            .collect::<Vec<_>>();

        let zkcm_gamma11_bytes = zkcm_gamma11
            .iter()
            .map(|x| x.to_bytes())
            .collect::<Vec<_>>();

        let zkcm_kappa_k = instance
            .kappa_k
            .iter()
            .zip(self.response_r_l.iter())
            .zip(self.response_l.iter())
            .map(|((kappa_k, resp_r_k), resp_r_l_k)| {
                crate::msm2!(
                    (kappa_k, self.challenge),
                    (grparams.gen2(), resp_r_k),
                    (params.pk_rp().alpha, Scalar::ONE - self.challenge),
                    (params.pk_rp().beta, resp_r_l_k)
                )
            })
            .collect::<Vec<_>>();

        let zkcm_kappa_k_bytes = zkcm_kappa_k
            .iter()
            .map(|x| x.to_bytes())
            .collect::<Vec<_>>();

        // re-compute the challenge
        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            std::iter::once(grparams.gen1().to_bytes().as_ref())
                .chain(std::iter::once(gamma1.to_bytes().as_ref()))
                .chain(std::iter::once(verification_key.alpha.to_bytes().as_ref()))
                .chain(beta2_bytes.iter().map(|b| b.as_ref()))
                .chain(std::iter::once(instance.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_kappa.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_cc.to_bytes().as_ref()))
                .chain(zkcm_aa_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_ss_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_kappa_k_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_tt_bytes.iter().map(|x| x.as_ref()))
                .chain(zkcm_gamma11_bytes.iter().map(|x| x.as_ref())),
        );

        challenge == self.challenge
    }
}

impl SpendProof {
    pub(crate) fn encode(&self, out: &mut Vec<u8>) {
        out.extend(self.challenge.to_bytes());
        out.extend(self.response_r.to_bytes());
        for s in &self.response_r_l {
            out.extend(s.to_bytes());
        }
        for s in &self.response_l {
            out.extend(s.to_bytes());
        }
        for s in &self.response_o_a {
            out.extend(s.to_bytes());
        }
        out.extend(self.response_o_c.to_bytes());
        for s in &self.response_mu {
            out.extend(s.to_bytes());
        }
        for s in &self.response_o_mu {
            out.extend(s.to_bytes());
        }
        for s in &self.response_attributes {
            out.extend(s.to_bytes());
        }
    }
    pub(crate) fn decode(
        r: &mut crate::backend::Reader,
        k: usize,
    ) -> std::result::Result<Self, String> {
        Ok(Self {
            challenge: r.scalar()?,
            response_r: r.scalar()?,
            response_r_l: (0..k)
                .map(|_| r.scalar())
                .collect::<std::result::Result<_, _>>()?,
            response_l: (0..k)
                .map(|_| r.scalar())
                .collect::<std::result::Result<_, _>>()?,
            response_o_a: (0..k)
                .map(|_| r.scalar())
                .collect::<std::result::Result<_, _>>()?,
            response_o_c: r.scalar()?,
            response_mu: (0..k)
                .map(|_| r.scalar())
                .collect::<std::result::Result<_, _>>()?,
            response_o_mu: (0..k)
                .map(|_| r.scalar())
                .collect::<std::result::Result<_, _>>()?,
            response_attributes: (0..2)
                .map(|_| r.scalar())
                .collect::<std::result::Result<_, _>>()?,
        })
    }
    pub(crate) fn valid_shape(&self, k: usize) -> bool {
        self.response_r_l.len() == k
            && self.response_l.len() == k
            && self.response_o_a.len() == k
            && self.response_mu.len() == k
            && self.response_o_mu.len() == k
            && self.response_attributes.len() == 2
    }
    pub fn with_invalid_challenge(&self) -> Self {
        let mut p = self.clone();
        p.challenge += Scalar::ONE;
        p
    }
}
