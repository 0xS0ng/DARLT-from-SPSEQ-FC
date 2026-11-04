//! Correctness and operation-count checks without clocks.
use super::{
    context::ProtocolContext,
    protocol::{self, PublicParameters},
    spend::{self, Atom, Policy},
    verification::Mode,
};
use crate::{ops, polynomial::S};
use ff::Field;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::sync::Arc;
fn record<T>(
    rows: &mut Vec<Value>,
    stage: &str,
    k: usize,
    f: impl FnOnce() -> Result<T, String>,
) -> Result<T, String> {
    ops::reset();
    let out = f()?;
    let counts = ops::stop();
    rows.push(json!({"construction":"DARLT","phase":stage,"k":k,"value_type":if cfg!(feature="op-counts"){"execution_count"}else{"correctness"},"timing_enabled":false,"op_counts_enabled":cfg!(feature="op-counts"),"counts":if cfg!(feature="op-counts"){Some(counts)}else{None}}));
    Ok(out)
}
pub fn run() -> Result<Vec<Value>, String> {
    let mut rows = vec![];
    let mut rng = StdRng::seed_from_u64(202_021_026);
    let pp = Arc::new(record(&mut rows, "setup", 0, || {
        PublicParameters::setup(1024, 16, 64, 6, 4, b"unit-test", &mut rng)
    })?);
    let (ip, sk) = record(&mut rows, "issuer_keygen", 0, || {
        protocol::keygen(&pp, &mut rng)
    })?;
    let ip = Arc::new(ip);
    let context = record(&mut rows, "install_full_instance", 0, || {
        ProtocolContext::new(pp.clone(), ip.clone())
    })?;
    let attrs = [
        S::ONE,
        S::from(21),
        S::from(22),
        S::from(23),
        S::from(24),
        S::from(25),
    ];
    let private = [S::from(7), S::from(8), S::from(9), S::from(10)];
    let (q, secret) = record(&mut rows, "issue_user_request", 0, || {
        protocol::prepare_request(&pp, &ip, S::from(91), &attrs, &private, &mut rng)
    })?;
    let response = record(&mut rows, "issue_issuer", 0, || {
        protocol::issue(&pp, &ip, &sk, &q, 1, &mut rng)
    })?;
    let mut wallet = record(&mut rows, "issue_user_accept", 0, || {
        protocol::accept(&pp, &ip, &q, &secret, &response, &mut rng)
    })?;
    record(&mut rows, "parent_opening_cold_two_columns", 0, || {
        wallet.parent_opening(&pp, 63)
    })?;
    record(&mut rows, "parent_opening_hot_cache_hit", 0, || {
        wallet.parent_opening(&pp, 63)
    })?;
    let mut child = record(&mut rows, "self_allocation_cold_8_pools", 0, || {
        context.self_derive(
            &mut wallet,
            b"self-8",
            &(0..8).collect::<Vec<_>>(),
            &mut rng,
        )
    })?;
    // This pool is not allocated yet; only its parent openings are precomputed.
    wallet.parent_opening(&pp, 8)?;
    let request = record(&mut rows, "delegate_agent_request_installed", 0, || {
        context.delegation_request(b"agent-8", S::from(111), &mut rng)
    })?;
    let delivery = record(&mut rows, "delegate_user_hot_one_pool", 0, || {
        context.delegate(
            &mut wallet,
            &request,
            &[8],
            &[true, true, true, false, false, false],
            &mut rng,
        )
    })?;
    let _agent = record(&mut rows, "delegate_agent_receive_specification", 0, || {
        context.receive(&delivery, S::from(111), None, Mode::Specification, &mut rng)
    })?;
    record(&mut rows, "scope_opening_cold_one_pool", 0, || {
        child.holder.scope_opening(&pp, 0)
    })?;
    record(&mut rows, "scope_opening_hot_cache_hit", 0, || {
        child.holder.scope_opening(&pp, 0)
    })?;
    let policy = Policy {
        period: 1,
        atoms: vec![
            Atom::Equal(0, S::ONE),
            Atom::Reveal(1, S::from(21)),
            Atom::Reveal(2, S::from(22)),
        ],
    };
    let challenge = [0x42u8; 32];
    for k in [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64] {
        let pos: Vec<_> = (0..k).collect();
        let prepared = record(&mut rows, "spend_preparation_installed", k, || {
            spend::prepare_spend_installed(&pp, &ip, &mut child.holder, &pos, &policy, &mut rng)
        })?;
        let token = record(&mut rows, "spend_online", k, || {
            spend::finish_spend(&pp, &ip, prepared, &challenge, &mut rng)
        })?;
        let wire = record(
            &mut rows,
            "token_wire_encode",
            k,
            || Ok(token.wire_encode()),
        )?;
        let parsed = record(&mut rows, "token_strict_decode", k, || {
            spend::Token::wire_decode(&pp, &wire)
        })?;
        for (label, mode) in [
            ("valid_specification", Mode::Specification),
            ("valid_randomized", Mode::Randomized),
        ] {
            record(&mut rows, label, k, || {
                if context.valid(&parsed, mode, &mut rng) {
                    Ok(())
                } else {
                    Err(format!("{label} rejected k={k}"))
                }
            })?;
        }
        rows.push(json!({"construction":"DARLT","phase":"token_wire_size","k":k,"value_type":"actual_serialized_bytes","bytes":wire.len(),"policy_bytes":policy.encode().len(),"context_bytes":challenge.len(),"token_sha256":format!("{:x}",Sha256::digest(&wire)),"sigma_variables":token.proof.z.len(),"range_bits":token.proof.bits.len(),"timing_enabled":false}));
    }
    let a = spend::finish_spend(
        &pp,
        &ip,
        spend::prepare_spend_installed(&pp, &ip, &mut child.holder, &[0], &policy, &mut rng)?,
        b"judge-A",
        &mut rng,
    )?;
    let b = spend::finish_spend(
        &pp,
        &ip,
        spend::prepare_spend_installed(&pp, &ip, &mut child.holder, &[0], &policy, &mut rng)?,
        b"judge-B",
        &mut rng,
    )?;
    for (label, mode) in [
        ("identify_full_specification", Mode::Specification),
        ("identify_full_randomized", Mode::Randomized),
    ] {
        record(&mut rows, label, 1, || {
            context
                .judge(&a, 0, &b, 0, mode, &mut rng)
                .ok_or("full adjudication failed".into())
        })?;
    }
    record(&mut rows, "identify_validated", 1, || {
        spend::identify_validated(&pp, &ip, &a, 0, &b, 0)
            .ok_or("validated adjudication failed".into())
    })?;
    record(&mut rows, "recover_metadata_full_specification", 1, || {
        context
            .read_bit(&a, &sk.metadata_secrets, Mode::Specification, &mut rng)
            .ok_or("metadata recovery failed".into())
    })?;
    for role in ["user", "issuer", "agent", "verifier"] {
        rows.push(json!({"construction":"DARLT","phase":"current_full_parameter_package","role":role,"value_type":"actual_serialized_bytes","bytes":pp.encode().len(),"shared_full_instance":true,"timing_enabled":false}));
    }
    rows.push(json!({"construction":"DARLT","phase":"dimensions","value_type":"object_count","N":pp.n,"s":pp.s,"w":pp.w,"W":pp.srs.domain.size,"n":pp.srs.n,"D":pp.srs.degree,"g1_srs_points":pp.srs.g1.len(),"g2_public_points":pp.srs.g2.len()+pp.srs.k_hat.len()+pp.srs.d_hat.len()+pp.srs.o_hat.len(),"caulk_proof_bytes":super::caulk::PROOF_BYTES,"query_cache_point_bytes":pp.query_bases.values().map(|(g,_)|(g.len()+1)*48).sum::<usize>(),"timing_enabled":false}));
    Ok(rows)
}
