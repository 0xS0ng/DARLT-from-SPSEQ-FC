use crate::backend::{GtCompat, IntoMsm, NativeMsm, ScalarCompat};
use ff::Field;
use std::ops::*;

use crate::backend::{G1Projective, Scalar};
use group::GroupEncoding;
use itertools::izip;

use crate::divisible::proofs::{
    compute_challenge, produce_response, produce_responses, ChallengeDigest,
};
use crate::divisible::scheme::keygen::PublicKeyUser;
use crate::divisible::scheme::setup::Parameters;

#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
// instance: g, gamma1, gamma2, gamma3, com, h, com1, com2, com3, pkUser
pub struct WithdrawalReqInstance {
    // Joined commitment to all attributes
    pub com: G1Projective,
    // Hash of the joined commitment com
    pub h: G1Projective,
    // Pedersen commitments to each attribute
    pub pc_coms: Vec<G1Projective>,
    // Public key of a user
    pub pk_user: PublicKeyUser,
}

impl WithdrawalReqInstance {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let pc_coms_len = self.pc_coms.len();
        let mut bytes = Vec::with_capacity(8 + (pc_coms_len + 3) as usize * 48);
        bytes.extend_from_slice(self.com.to_bytes().as_ref());
        bytes.extend_from_slice(self.h.to_bytes().as_ref());
        bytes.extend_from_slice(&pc_coms_len.to_le_bytes());
        for pc in self.pc_coms.iter() {
            bytes.extend_from_slice((pc.to_bytes()).as_ref());
        }
        bytes.extend_from_slice(self.pk_user.pk.to_bytes().as_ref());
        bytes
    }
}

// witness: m1, m2, m3, o, o1, o2, o3,
pub struct WithdrawalReqWitness {
    pub attributes: Vec<Scalar>,
    // Opening for the joined commitment com
    pub com_opening: Scalar,
    // Openings for the pedersen commitments
    pub pc_coms_openings: Vec<Scalar>,
}

pub struct WithdrawalReqProof {
    pub(crate) challenge: Scalar,
    pub(crate) response_opening: Scalar,
    pub(crate) response_openings: Vec<Scalar>,
    pub(crate) response_attributes: Vec<Scalar>,
}

impl WithdrawalReqProof {
    pub(crate) fn construct(
        params: &Parameters,
        instance: &WithdrawalReqInstance,
        witness: &WithdrawalReqWitness,
    ) -> Self {
        let grp = params.get_grp();
        let g1 = grp.gen1();
        let params_u = params.get_params_u();

        // generate random values to replace the witnesses
        let r_com_opening = grp.random_scalar();
        let r_pedcom_openings = grp.n_random_scalars(witness.pc_coms_openings.len());
        let r_attributes = grp.n_random_scalars(witness.attributes.len());

        // compute zkp commitments for each instance
        let zkcm_com = g1 * r_com_opening
            + r_attributes
                .iter()
                .zip(params_u.get_gammas().iter())
                .map(|(rm_i, gamma_i)| (*gamma_i, *rm_i))
                .collect::<Vec<_>>()
                .msm();

        let zkcm_pedcom = r_pedcom_openings
            .iter()
            .zip(r_attributes.iter())
            .map(|(o_j, m_j)| g1 * o_j + instance.h * m_j)
            .collect::<Vec<_>>();

        let zkcm_user_sk = g1 * r_attributes[0];

        // covert to bytes
        let gammas_bytes = params_u
            .get_gammas()
            .iter()
            .map(|gamma| gamma.to_bytes())
            .collect::<Vec<_>>();

        let zkcm_pedcom_bytes = zkcm_pedcom
            .iter()
            .map(|cm| cm.to_bytes())
            .collect::<Vec<_>>();

        // compute zkp challenge using g1, gammas, c, h, c1, c2, c3, zk commitments
        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            std::iter::once(g1.to_bytes().as_ref())
                .chain(gammas_bytes.iter().map(|gamma| gamma.as_ref()))
                .chain(std::iter::once(instance.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_com.to_bytes().as_ref()))
                .chain(zkcm_pedcom_bytes.iter().map(|c| c.as_ref()))
                .chain(std::iter::once(zkcm_user_sk.to_bytes().as_ref())),
        );

        // compute response
        let response_opening = produce_response(&r_com_opening, &challenge, &witness.com_opening);
        let response_openings = produce_responses(
            &r_pedcom_openings,
            &challenge,
            &witness.pc_coms_openings.iter().collect::<Vec<_>>(),
        );
        let response_attributes = produce_responses(
            &r_attributes,
            &challenge,
            &witness.attributes.iter().collect::<Vec<_>>(),
        );

        WithdrawalReqProof {
            challenge,
            response_opening,
            response_openings,
            response_attributes,
        }
    }

    pub(crate) fn verify(&self, params: &Parameters, instance: &WithdrawalReqInstance) -> bool {
        let grp = params.get_grp();
        let g1 = grp.gen1();
        let params_u = params.get_params_u();

        // recompute zk commitments for each instance
        let zkcm_com = instance.com * self.challenge
            + g1 * self.response_opening
            + self
                .response_attributes
                .iter()
                .zip(params_u.get_gammas().iter())
                .map(|(m_i, gamma_i)| (*gamma_i, *m_i))
                .collect::<Vec<_>>()
                .msm();

        let zkcm_pedcom = izip!(
            instance.pc_coms.iter(),
            self.response_openings.iter(),
            self.response_attributes.iter()
        )
        .map(|(cm_j, resp_o_j, resp_m_j)| {
            cm_j * self.challenge + g1 * resp_o_j + instance.h * resp_m_j
        })
        .collect::<Vec<_>>();

        let zk_commitment_user_sk =
            instance.pk_user.pk * self.challenge + g1 * self.response_attributes[0];

        // covert to bytes
        let gammas_bytes = params_u
            .get_gammas()
            .iter()
            .map(|gamma| gamma.to_bytes())
            .collect::<Vec<_>>();

        let zkcm_pedcom_bytes = zkcm_pedcom
            .iter()
            .map(|cm| cm.to_bytes())
            .collect::<Vec<_>>();

        // recompute zkp challenge
        let challenge = compute_challenge::<ChallengeDigest, _, _>(
            std::iter::once(g1.to_bytes().as_ref())
                .chain(gammas_bytes.iter().map(|hs| hs.as_ref()))
                .chain(std::iter::once(instance.to_bytes().as_ref()))
                .chain(std::iter::once(zkcm_com.to_bytes().as_ref()))
                .chain(zkcm_pedcom_bytes.iter().map(|c| c.as_ref()))
                .chain(std::iter::once(zk_commitment_user_sk.to_bytes().as_ref())),
        );

        challenge == self.challenge
    }
}
