//! Clock-free wire accounting and independent-token ablation checks.
use super::{
    context::ProtocolContext,
    protocol::{self, PublicParameters},
    role_params::{Role, RoleParameters},
    spend::{self, Atom, Policy, Token},
    verification::Mode,
};
use crate::{ops, polynomial::S};
use ff::Field;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::sync::Arc;

pub const K_VALUES: [usize; 14] = [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 96, 128];

/// Rebuild the complete wire stream field by field, then compare its bytes
/// with the protocol codec. Counts are annotations of actual encoded fields.
pub fn token_ledger(token: &Token) -> Result<Vec<Value>, String> {
    let mut output = Vec::new();
    let mut fields = Vec::new();
    let k = token.units.len();
    let mut add = |name: &str, kind: &str, g1: usize, g2: usize, fr: usize, bytes: Vec<u8>| {
        let offset = output.len();
        output.extend_from_slice(&bytes);
        fields.push(
            json!({"construction":"DARLT","phase":"token_field","field":name,
            "kind":kind,"k":k,"offset":offset,"bytes":bytes.len(),"g1":g1,"g2":g2,"fr":fr,
            "value_type":"actual_serialized_bytes","timing_enabled":false}),
        );
    };
    add("version", "version", 0, 0, 0, vec![21]);
    add(
        "authentication.frame",
        "u64",
        0,
        0,
        0,
        (token.auth.encode().len() as u64).to_be_bytes().to_vec(),
    );
    add(
        "M_prime",
        "G1[]",
        token.auth.message.len(),
        0,
        0,
        token
            .auth
            .message
            .iter()
            .flat_map(|p| p.to_compressed())
            .collect(),
    );
    add(
        "sigma_prime",
        "2G1+G2",
        2,
        1,
        0,
        token.auth.signature.encode(),
    );
    add(
        "S_prime",
        "G1",
        1,
        0,
        0,
        token.scope.to_compressed().to_vec(),
    );
    add(
        "Theta_prime",
        "G1",
        1,
        0,
        0,
        token.offset_table.to_compressed().to_vec(),
    );
    for (i, p) in token.commitments.iter().enumerate() {
        add(
            &format!("C_{}", i + 1),
            "G1",
            1,
            0,
            0,
            p.to_compressed().to_vec(),
        );
    }
    add(
        "cm_seed",
        "G1",
        1,
        0,
        0,
        token.seed_query.to_compressed().to_vec(),
    );
    add(
        "units.length",
        "u64",
        0,
        0,
        0,
        (k as u64).to_be_bytes().to_vec(),
    );
    add(
        "units",
        "4kG1",
        4 * k,
        0,
        0,
        token
            .units
            .iter()
            .flat_map(|u| [u.sn, u.aid, u.tu, u.ta])
            .flat_map(|p| p.to_compressed())
            .collect(),
    );
    for (i, p) in token.lookups.iter().enumerate() {
        add(
            if i == 0 { "Caulk_seed" } else { "Caulk_offset" },
            "14G1+G2+4Fr",
            14,
            1,
            4,
            p.to_bytes(),
        );
    }
    add(
        "range_commitments.length",
        "u64",
        0,
        0,
        0,
        (token.range_commitments.len() as u64)
            .to_be_bytes()
            .to_vec(),
    );
    add(
        "range_commitments",
        "G1[]",
        token.range_commitments.len(),
        0,
        0,
        token
            .range_commitments
            .iter()
            .flat_map(|p| p.to_compressed())
            .collect(),
    );
    add(
        "Sigma.frame",
        "u64",
        0,
        0,
        0,
        (token.proof.encode().len() as u64).to_be_bytes().to_vec(),
    );
    add(
        "Sigma.challenge",
        "Fr",
        0,
        0,
        1,
        token.proof.c.to_bytes_be().to_vec(),
    );
    add(
        "Sigma.responses",
        "Fr[]",
        0,
        0,
        token.proof.z.len(),
        token.proof.z.iter().flat_map(|z| z.to_bytes_be()).collect(),
    );
    add(
        "Sigma.bit_responses",
        "3Fr/bit",
        0,
        0,
        3 * token.proof.bits.len(),
        token
            .proof
            .bits
            .iter()
            .flatten()
            .flat_map(|z| z.to_bytes_be())
            .collect(),
    );
    let policy = token.policy.encode();
    add(
        "policy.frame",
        "u64",
        0,
        0,
        0,
        (policy.len() as u64).to_be_bytes().to_vec(),
    );
    add("policy", "endpoint_policy", 0, 0, 0, policy);
    add(
        "context.frame",
        "u64",
        0,
        0,
        0,
        (token.context.len() as u64).to_be_bytes().to_vec(),
    );
    add("context", "bytes", 0, 0, 0, token.context.clone());
    if output != token.wire_encode() {
        return Err("field ledger does not reconstruct exact token wire stream".into());
    }
    Ok(fields)
}

fn count<T>(
    rows: &mut Vec<Value>,
    stage: &str,
    k: usize,
    g: usize,
    action: impl FnOnce() -> Result<T, String>,
) -> Result<T, String> {
    ops::reset();
    let out = action()?;
    let c = ops::stop();
    rows.push(json!({"construction":"DARLT","phase":stage,"k":k,"gamma":g,
        "value_type":if cfg!(feature="op-counts"){"execution_count"}else{"correctness"},
        "op_counts_enabled":cfg!(feature="op-counts"),"counts":if cfg!(feature="op-counts"){Some(c)}else{None},"timing_enabled":false}));
    Ok(out)
}

fn message(rows: &mut Vec<Value>, phase: &str, g: usize, sid: usize, bytes: &[u8]) {
    rows.push(
        json!({"construction":"DARLT","phase":phase,"gamma":g,"sid_bytes":sid,
        "bytes":bytes.len(),"wire_sha256":format!("{:x}",Sha256::digest(bytes)),
        "value_type":"actual_serialized_bytes","timing_enabled":false}),
    );
}

/// Uses fresh deterministic fixtures without collecting timing data.
pub fn run() -> Result<Vec<Value>, String> {
    let mut rows = vec![];
    let mut rng = StdRng::seed_from_u64(207_021_027);
    let pp = Arc::new(PublicParameters::setup(
        1024,
        16,
        64,
        6,
        4,
        b"receipt-test",
        &mut rng,
    )?);
    let (ip, secret_key) = protocol::keygen(&pp, &mut rng)?;
    let ip = Arc::new(ip);
    let context = ProtocolContext::new(pp.clone(), ip.clone())?;
    for role in [Role::User, Role::Issuer, Role::Agent, Role::Verifier] {
        let package = RoleParameters::from_setup(&pp, role)?;
        let fields = package.fields();
        rows.push(json!({"construction":"DARLT","phase":"role_parameter_package","role":role.name(),
            "bytes":package.encode().len(),"header_bytes":package.header_bytes(),"fields":fields,
            "dimensions":package.dimensions(),"value_type":"actual_serialized_bytes",
            "issuer_key_included":false,"trusted_setup_manifest_separate":true,
            "trusted_setup_manifest_bytes":package.manifest().encode().len(),
            "packet_sha256":format!("{:x}",Sha256::digest(package.encode())),"timing_enabled":false}));
    }
    message(&mut rows, "issuer_public_key_wire", 0, 0, &ip.encode());
    let (q, secret) = protocol::prepare_request(
        &pp,
        &ip,
        S::from(91),
        &[
            S::ONE,
            S::from(21),
            S::from(22),
            S::from(23),
            S::from(24),
            S::from(25),
        ],
        &[S::from(7), S::from(8), S::from(9), S::from(10)],
        &mut rng,
    )?;
    let response = protocol::issue(&pp, &ip, &secret_key, &q, 1, &mut rng)?;
    let wallet = protocol::accept(&pp, &ip, &q, &secret, &response, &mut rng)?;
    message(&mut rows, "issue_request_wire", 0, 0, &q.encode());
    message(&mut rows, "issue_response_wire", 0, 0, &response.encode());
    for g in [1, 8, 64] {
        // Independent contexts model alternative workloads on the same accepted
        // independent wallet, not overlapping allocations in one live state.
        let ctx = ProtocolContext::new(pp.clone(), ip.clone())?;
        let mut w = wallet.clone();
        let sid = [g as u8; 32];
        let request = count(&mut rows, "delegate_request", 0, g, || {
            ctx.delegation_request(&sid, S::from(111), &mut rng)
        })?;
        message(
            &mut rows,
            "delegate_request_wire",
            g,
            sid.len(),
            &request.encode(),
        );
        let gamma: Vec<_> = (0..g).collect();
        for pool in &gamma {
            w.parent_opening(&pp, *pool)?;
        }
        let delivery = count(&mut rows, "delegate_user_hot", 0, g, || {
            ctx.delegate(&mut w, &request, &gamma, &[true; 6], &mut rng)
        })?;
        message(
            &mut rows,
            "delegate_response_wire",
            g,
            sid.len(),
            &delivery.delivery.encode(),
        );
        count(
            &mut rows,
            "delegate_agent_receive_specification",
            0,
            g,
            || ctx.receive(&delivery, S::from(111), None, Mode::Specification, &mut rng),
        )?;
        count(&mut rows, "delegate_agent_receive_randomized", 0, g, || {
            ctx.receive(&delivery, S::from(111), None, Mode::Randomized, &mut rng)
        })?;
    }
    let mut wallet = wallet;
    let mut child = context.self_derive(
        &mut wallet,
        b"ablation-self",
        &(0..8).collect::<Vec<_>>(),
        &mut rng,
    )?;
    let policy = Policy {
        period: 1,
        atoms: vec![
            Atom::Equal(0, S::ONE),
            Atom::Reveal(1, S::from(21)),
            Atom::Reveal(2, S::from(22)),
        ],
    };
    let challenge = [0x42; 32];
    let mut singles = Vec::new();
    for p in 0..128 {
        let prepared =
            spend::prepare_spend_installed(&pp, &ip, &mut child.holder, &[p], &policy, &mut rng)?;
        let t = spend::finish_spend(&pp, &ip, prepared, &challenge, &mut rng)?;
        singles.push(Token::wire_decode(&pp, &t.wire_encode())?);
    }
    for k in K_VALUES {
        let mut blocks = Vec::new();
        for chunk in (0..k).collect::<Vec<_>>().chunks(pp.k_max) {
            let prepared = spend::prepare_spend_installed(
                &pp,
                &ip,
                &mut child.holder,
                chunk,
                &policy,
                &mut rng,
            )?;
            let t = spend::finish_spend(&pp, &ip, prepared, &challenge, &mut rng)?;
            if k <= 64 {
                rows.extend(token_ledger(&t)?);
            }
            blocks.push(Token::wire_decode(&pp, &t.wire_encode())?);
        }
        for (label, tokens) in [
            ("native_blocks", blocks.as_slice()),
            ("k_independent_singles", &singles[..k]),
        ] {
            for (mode_name, mode) in [
                ("specification", Mode::Specification),
                ("randomized", Mode::Randomized),
            ] {
                count(
                    &mut rows,
                    &format!("ablation_{label}_{mode_name}"),
                    k,
                    8,
                    || {
                        let accepted = if label == "native_blocks" {
                            // The construction verifies split native blocks
                            // independently; k=96/128 therefore uses two FEs in
                            // the randomized per-block profile.
                            tokens.iter().all(|t| context.valid(t, mode, &mut rng))
                        } else {
                            context.valid_many(tokens, mode, &mut rng)
                        };
                        if accepted {
                            Ok(())
                        } else {
                            Err(format!("{label} batch rejected k={k}"))
                        }
                    },
                )?;
            }
            let wires: Vec<_> = tokens.iter().map(Token::wire_encode).collect();
            rows.push(json!({"construction":"DARLT","phase":"ablation_wire","variant":label,"k":k,
                "token_count":tokens.len(),"block_units":tokens.iter().map(|t|t.units.len()).collect::<Vec<_>>(),
                "token_wire_bytes":wires.iter().map(Vec::len).collect::<Vec<_>>(),"bytes":wires.iter().map(Vec::len).sum::<usize>(),
                "wire_hashes":wires.iter().map(|w|format!("{:x}",Sha256::digest(w))).collect::<Vec<_>>(),
                "boundary":"sum_of_complete_token_wire_messages","timing_enabled":false,"value_type":"actual_serialized_bytes"}));
        }
    }
    Ok(rows)
}
