use crate::backend::{GtCompat, IntoMsm, NativeMsm, ScalarCompat};
use ff::Field;
use std::cell::Cell;
use std::ops::*;

use crate::backend::{G1Projective, G2Prepared, G2Projective, Scalar};
use group::Curve;

use crate::compact::error::{CompactEcashError, Result};
use crate::compact::proofs::proof_spend::{PreparedProof, SpendInstance, SpendProof, SpendWitness};
use crate::compact::scheme::keygen::{SecretKeyUser, VerificationKeyAuth};
use crate::compact::scheme::setup::{GroupParameters, Parameters};
use crate::compact::utils::{check_bilinear_pairing, hash_to_scalar, Signature, SignerIndex};
use crate::compact::Attribute;

pub mod aggregation;
pub mod keygen;
pub mod setup;
pub mod withdrawal;

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

/// Native Spend(V) with its context-independent work completed once. The API
/// layer holds the wallet exclusively and advances its counter after finish.
pub struct PreparedSpend {
    start_index: u64,
    amount: u64,
    signature: Signature,
    range_signatures: Vec<Signature>,
    instance: SpendInstance,
    witness: SpendWitness,
    proof: PreparedProof,
}

impl PreparedSpend {
    pub fn start_index(&self) -> u64 {
        self.start_index
    }
    pub fn amount(&self) -> u64 {
        self.amount
    }

    /// One G1 multiplication for each native T_k plus one for each proof
    /// commitment T_k. All static signature/range/commitment work is offline.
    pub fn finish(
        self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        pay_info: &PayInfo,
    ) -> Result<Payment> {
        let Self {
            amount,
            signature,
            range_signatures,
            mut instance,
            witness,
            proof,
            ..
        } = self;
        let rr: Vec<_> = (0..amount)
            .map(|k| hash_payment_index(pay_info, k))
            .collect();
        instance.tt = rr
            .iter()
            .zip(&witness.mu)
            .map(|(r, mu)| params.grp().gen1() * (witness.attributes[0] + r * mu))
            .collect();
        let zk_proof = proof.finish(params, &instance, &witness, verification_key, &rr);
        Ok(Payment {
            kappa: instance.kappa,
            sig: signature,
            ss: instance.ss,
            tt: instance.tt,
            aa: instance.aa,
            rr,
            kappa_k: instance.kappa_k,
            sig_lk: range_signatures,
            cc: instance.cc,
            zk_proof,
            vv: amount,
        })
    }
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

    fn up(&self) {
        self.l.set(self.l.get() + 1);
    }

    /// Prepares the original one-call Spend(V) without committing the counter
    /// or receiving payinfo. Nonce draws have exactly the reference ordering.
    pub fn prepare_spend(
        &self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        sk_user: &SecretKeyUser,
        spend_vv: u64,
    ) -> Result<PreparedSpend> {
        let start_index = self.l();
        if spend_vv == 0
            || start_index
                .checked_add(spend_vv)
                .is_none_or(|end| end > params.L())
        {
            return Err(CompactEcashError::Spend(
                "The counter l is higher than max L".into(),
            ));
        }
        let grparams = params.grp();
        let (signature, r) = self.signature().randomise(grparams);
        let attributes = vec![sk_user.sk, self.v()];
        let kappa = compute_kappa(grparams, verification_key, &attributes, r);
        let o_c = grparams.random_scalar();
        let cc = crate::msm1!((grparams.gen1(), o_c), (grparams.gamma1(), self.v()));
        let mut aa = vec![];
        let mut ss = vec![];
        let mut o_a = vec![];
        let mut o_mu = vec![];
        let mut mu = vec![];
        let mut lk = vec![];
        let mut r_k = vec![];
        let mut kappa_k = vec![];
        let mut range_signatures = vec![];
        for k in 0..spend_vv {
            let index = start_index + k;
            lk.push(Scalar::from(index));
            let opening = grparams.random_scalar();
            o_a.push(opening);
            aa.push(crate::msm1!(
                (grparams.gen1(), opening),
                (grparams.gamma1(), Scalar::from(index))
            ));
            ss.push(pseudorandom_f_delta_v(grparams, self.v(), index));
            let inverse = (self.v() + Scalar::from(index) + Scalar::ONE)
                .invert()
                .unwrap();
            mu.push(inverse);
            o_mu.push(-((opening + o_c) * inverse));
            let signature = params.get_sign_by_idx(index)?;
            let (signature, blinder) = signature.randomise(grparams);
            range_signatures.push(signature);
            r_k.push(blinder);
            kappa_k.push(
                grparams.gen2() * blinder
                    + params.pk_rp().alpha
                    + params.pk_rp().beta * Scalar::from(index),
            );
        }
        let instance = SpendInstance {
            kappa,
            cc,
            aa,
            ss,
            tt: vec![],
            kappa_k,
        };
        let witness = SpendWitness {
            attributes,
            r,
            o_c,
            lk,
            o_a,
            mu,
            o_mu,
            r_k,
        };
        let proof = PreparedProof::prepare(params, &instance, &witness, verification_key);
        Ok(PreparedSpend {
            start_index,
            amount: spend_vv,
            signature,
            range_signatures,
            instance,
            witness,
            proof,
        })
    }

    pub fn spend(
        &self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        sk_user: &SecretKeyUser,
        pay_info: &PayInfo,
        bench_flag: bool,
        spend_vv: u64,
    ) -> Result<(Payment, &Self)> {
        if spend_vv == 0
            || self
                .l()
                .checked_add(spend_vv)
                .is_none_or(|end| end > params.L())
        {
            return Err(CompactEcashError::Spend(
                "The counter l is higher than max L".to_string(),
            ));
        }

        let grparams = params.grp();
        // randomize signature in the wallet
        let (signature_prime, sign_blinding_factor) = self.signature().randomise(grparams);
        // construct kappa i.e., blinded attributes for show
        let attributes = vec![sk_user.sk, self.v()];
        // compute kappa
        let kappa = compute_kappa(
            &grparams,
            &verification_key,
            &attributes,
            sign_blinding_factor,
        );

        // pick random openings o_c
        let o_c = grparams.random_scalar();

        // compute commitments C
        let cc = crate::msm1!((grparams.gen1(), o_c), (grparams.gamma1(), self.v()));

        let mut aa: Vec<G1Projective> = Default::default();
        let mut ss: Vec<G1Projective> = Default::default();
        let mut tt: Vec<G1Projective> = Default::default();
        let mut rr: Vec<Scalar> = Default::default();
        let mut o_a: Vec<Scalar> = Default::default();
        let mut o_mu: Vec<Scalar> = Default::default();
        let mut mu: Vec<Scalar> = Default::default();
        let mut r_k_vec: Vec<Scalar> = Default::default();
        let mut kappa_k_vec: Vec<G2Projective> = Default::default();
        let mut sign_lk_prime_vec: Vec<Signature> = Default::default();
        let mut lk: Vec<Scalar> = Default::default();

        for k in 0..spend_vv {
            lk.push(Scalar::from(self.l() + k));

            // compute hashes R_k of the payment info
            let rr_k = hash_payment_index(pay_info, k);
            rr.push(rr_k);

            let o_a_k = grparams.random_scalar();
            o_a.push(o_a_k);
            let aa_k = crate::msm1!(
                (grparams.gen1(), o_a_k),
                (grparams.gamma1(), Scalar::from(self.l() + k))
            );
            aa.push(aa_k);

            // evaluate the pseudorandom functions
            let ss_k = pseudorandom_f_delta_v(&grparams, self.v(), self.l() + k);
            ss.push(ss_k);
            let tt_k = grparams.gen1()
                * (sk_user.sk
                    + (self.v() + Scalar::from(self.l() + k) + Scalar::ONE)
                        .invert()
                        .unwrap()
                        * rr_k);
            tt.push(tt_k);

            // compute values mu, o_mu, lambda, o_lambda
            let mu_k: Scalar = (self.v() + Scalar::from(self.l() + k) + Scalar::from(1))
                .invert()
                .unwrap();
            mu.push(mu_k);

            let o_mu_k = ((o_a_k + o_c) * mu_k).neg();
            o_mu.push(o_mu_k);

            // parse the signature associated with value l+k
            let sign_lk = params.get_sign_by_idx(self.l() + k)?;
            // randomise the signature associated with value l+k
            let (sign_lk_prime, r_k) = sign_lk.randomise(grparams);
            sign_lk_prime_vec.push(sign_lk_prime);
            r_k_vec.push(r_k);
            // compute kappa_k
            let kappa_k = grparams.gen2() * r_k
                + params.pk_rp().alpha
                + params.pk_rp().beta * Scalar::from(self.l() + k);
            kappa_k_vec.push(kappa_k);
        }

        // construct the zkp proof
        let spend_instance = SpendInstance {
            kappa,
            cc,
            aa: aa.clone(),
            ss: ss.clone(),
            tt: tt.clone(),
            kappa_k: kappa_k_vec.clone(),
        };
        let spend_witness = SpendWitness {
            attributes,
            r: sign_blinding_factor,
            o_c,
            lk,
            o_a,
            mu,
            o_mu,
            r_k: r_k_vec,
        };
        let zk_proof = SpendProof::construct(
            &params,
            &spend_instance,
            &spend_witness,
            &verification_key,
            &rr,
        );

        // output pay and updated wallet
        let pay = Payment {
            kappa,
            sig: signature_prime,
            ss: ss.clone(),
            tt: tt.clone(),
            aa: aa.clone(),
            rr: rr.clone(),
            kappa_k: kappa_k_vec.clone(),
            sig_lk: sign_lk_prime_vec,
            cc,
            zk_proof,
            vv: spend_vv,
        };

        // The number of samples collected by the benchmark process is way higher than the
        // MAX_WALLET_VALUE we ever consider. Thus, we would execute the spending too many times
        // and the initial condition at the top of this function will crush. Thus, we need a
        // benchmark flag to signal that we don't want to increase the spending couter but only
        // care about the function performance.
        if !bench_flag {
            let current_l = self.l();
            self.l.set(current_l + spend_vv);
        }

        Ok((pay, self))
    }
}

pub fn pseudorandom_f_delta_v(params: &GroupParameters, v: Scalar, l: u64) -> G1Projective {
    let pow = (v + Scalar::from(l) + Scalar::from(1)).invert().unwrap();
    params.delta() * pow
}

pub fn pseudorandom_f_g_v(params: &GroupParameters, v: Scalar, l: u64) -> G1Projective {
    let pow = (v + Scalar::from(l) + Scalar::from(1)).invert().unwrap();
    params.gen1() * pow
}

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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PayInfo {
    pub info: [u8; 32],
}

#[derive(Debug, Clone)]
pub struct Payment {
    pub kappa: G2Projective,
    pub sig: Signature,
    pub ss: Vec<G1Projective>,
    pub tt: Vec<G1Projective>,
    pub aa: Vec<G1Projective>,
    pub rr: Vec<Scalar>,
    pub kappa_k: Vec<G2Projective>,
    pub sig_lk: Vec<Signature>,
    pub cc: G1Projective,
    pub zk_proof: SpendProof,
    pub vv: u64,
}

impl Payment {
    pub fn spend_verify(
        &self,
        params: &Parameters,
        verification_key: &VerificationKeyAuth,
        pay_info: &PayInfo,
    ) -> Result<bool> {
        if bool::from(self.sig.0.is_identity()) {
            return Err(CompactEcashError::Spend(
                "The element h of the signature equals the identity".to_string(),
            ));
        }

        if !check_bilinear_pairing(
            &self.sig.0.to_affine(),
            &G2Prepared::from(self.kappa.to_affine()),
            &self.sig.1.to_affine(),
            params.grp().prepared_miller_g2(),
        ) {
            return Err(CompactEcashError::Spend(
                "The bilinear check for kappa failed".to_string(),
            ));
        }

        for k in 0..self.vv {
            if bool::from(self.sig_lk[k as usize].0.is_identity()) {
                return Err(CompactEcashError::Spend(
                    "The element h of the signature on l equals the identity".to_string(),
                ));
            }

            if !check_bilinear_pairing(
                &self.sig_lk[k as usize].0.to_affine(),
                &G2Prepared::from(self.kappa_k[k as usize].to_affine()),
                &self.sig_lk[k as usize].1.to_affine(),
                params.grp().prepared_miller_g2(),
            ) {
                return Err(CompactEcashError::Spend(
                    "The bilinear check for kappa_l failed".to_string(),
                ));
            }
            // verify integrity of R_k
            if !(self.rr[k as usize] == hash_payment_index(pay_info, k)) {
                return Err(CompactEcashError::Spend(
                    "Integrity of R_k does not hold".to_string(),
                ));
            }
        }

        // The public api::verify entry checks the expected merchant in native payinfo.

        // verify the zk proof
        let instance = SpendInstance {
            kappa: self.kappa,
            aa: self.aa.clone(),
            cc: self.cc,
            ss: self.ss.clone(),
            tt: self.tt.clone(),
            kappa_k: self.kappa_k.clone(),
        };

        if !self
            .zk_proof
            .verify(&params, &instance, &verification_key, &self.rr)
        {
            return Err(CompactEcashError::Spend(
                "ZkProof verification failed".to_string(),
            ));
        }

        Ok(true)
    }
}

/// Original Appendix F binds the per-payment unit index in R_k.
pub fn hash_payment_index(pay_info: &PayInfo, k: u64) -> Scalar {
    let mut input = pay_info.info.to_vec();
    input.extend_from_slice(&k.to_le_bytes());
    hash_to_scalar(input)
}
