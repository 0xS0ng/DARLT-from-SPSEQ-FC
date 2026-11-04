//! Real equal-total-budget configuration callbacks for Fig.9(b), without clocks.
//! A second fresh execution checks each complete system scope against the
//! separately executed native stages. Installation and first use stay separate.
use crate::{
    darlt::{
        context::{key_id, ProtocolContext},
        protocol::{self, Holder, IssuerPublic, IssuerSecret, PublicParameters},
        role_params::{Role, RoleParameters},
        state::HolderStore,
        verification::Mode,
    },
    ops,
    polynomial::S,
    spseq_fc,
};
use baseline_core::{
    encoding::{self, Reader, Writer},
    sma2rt as sma, sma2rt_proof,
};
use blstrs::G1Projective as G1;
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{collections::BTreeSet, sync::Arc};

type Result<T> = std::result::Result<T, String>;
const AGENTS: [usize; 7] = [1, 2, 4, 8, 16, 32, 64];
fn error(e: impl std::fmt::Display) -> String {
    e.to_string()
}
fn need(value: bool, message: &str) -> Result<()> {
    if value {
        Ok(())
    } else {
        Err(message.into())
    }
}
fn enabled(scheme: &str) -> bool {
    scheme != "DARLT" || cfg!(feature = "op-counts")
}

fn capture<T>(scheme: &str, action: impl FnOnce() -> Result<T>) -> Result<(T, Value)> {
    if scheme == "DARLT" {
        ops::reset();
    } else {
        encoding::start_counts();
    }
    let output = action();
    let counts = if scheme == "DARLT" {
        let c = ops::stop();
        if enabled(scheme) {
            json!(c)
        } else {
            Value::Null
        }
    } else {
        json!(encoding::stop_counts())
    };
    output.map(|out| (out, counts))
}
fn base(scheme: &str, agents: Option<usize>, phase: &str, account: &str) -> Value {
    let mut row = json!({"task":"provisioning","phase":phase,"scheme":scheme,"agents":agents,
        "account":account,"total_quota":1024,"attributes":10,"timing_enabled":false,"formal_samples":0,
        "source":"fresh_native_configuration_execution","network_included":false,"persistent_io_included":false,
        "op_counts_enabled":enabled(scheme)});
    if let Some(a) = agents {
        row["per_agent_quota"] = json!(1024 / a);
        if scheme == "DARLT" {
            row["pools_per_agent"] = json!(64 / a);
        }
    }
    row
}
fn outside<T>(
    rows: &mut Vec<Value>,
    scheme: &str,
    a: Option<usize>,
    phase: &str,
    agent: Option<usize>,
    action: impl FnOnce() -> Result<T>,
) -> Result<T> {
    let (value, counts) = capture(scheme, action)?;
    let mut row = base(scheme, a, phase, "outside_system_configuration");
    row["agent"] = json!(agent);
    row["counts"] = counts;
    rows.push(row);
    Ok(value)
}
fn add_counts(sum: &mut Value, counts: &Value) -> Result<()> {
    if counts.is_null() {
        return Ok(());
    }
    if sum.is_null() {
        *sum = counts.clone();
        return Ok(());
    }
    let target = sum.as_object_mut().ok_or("counter sum must be an object")?;
    let incoming = counts
        .as_object()
        .ok_or("counter observation must be an object")?;
    need(target.len() == incoming.len(), "counter fields changed")?;
    for (key, value) in incoming {
        let target = target.get_mut(key).ok_or("counter field missing")?;
        if let Some(n) = value.as_u64() {
            let total = target
                .as_u64()
                .ok_or("counter type changed")?
                .checked_add(n)
                .ok_or("counter sum overflow")?;
            *target = json!(total);
        } else if let Some(values) = value.as_array() {
            target
                .as_array_mut()
                .ok_or("MSM counter type changed")?
                .extend(values.clone());
        } else {
            return Err("unsupported counter type".into());
        }
    }
    Ok(())
}
struct Stages<'a> {
    rows: &'a mut Vec<Value>,
    scheme: &'static str,
    agents: usize,
    detailed: bool,
    system: Value,
    issuer: Value,
    issuer_calls: usize,
}
impl Stages<'_> {
    fn run<T>(
        &mut self,
        phase: &str,
        agent: Option<usize>,
        issuer: bool,
        action: impl FnOnce() -> Result<T>,
    ) -> Result<T> {
        if !self.detailed {
            return action();
        }
        let (value, counts) = capture(self.scheme, action)?;
        add_counts(&mut self.system, &counts)?;
        if issuer {
            add_counts(&mut self.issuer, &counts)?;
            self.issuer_calls += 1;
        }
        let mut row = base(self.scheme, Some(self.agents), phase, "system_component");
        row["agent"] = json!(agent);
        row["counts"] = counts;
        row["included_in_issuer_account"] = json!(issuer);
        self.rows.push(row);
        Ok(value)
    }
}
struct Execution {
    wire: Vec<u8>,
    wire_bytes: usize,
    issuer_calls: usize,
    delegations: usize,
    budgets: Vec<usize>,
    pools: BTreeSet<usize>,
    holders: Vec<Holder>,
    stores: Vec<HolderStore>,
}
impl Execution {
    fn message(&mut self, bytes: Vec<u8>) {
        self.wire_bytes += bytes.len();
        self.wire.extend((bytes.len() as u64).to_be_bytes());
        self.wire.extend(bytes);
    }
    fn hash(&self) -> String {
        format!("{:x}", Sha256::digest(&self.wire))
    }
}
fn execution() -> Execution {
    Execution {
        wire: vec![],
        wire_bytes: 0,
        issuer_calls: 0,
        delegations: 0,
        budgets: vec![],
        pools: BTreeSet::new(),
        holders: vec![],
        stores: vec![],
    }
}

#[allow(clippy::too_many_arguments)]
fn darlt_flow(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    secret: &IssuerSecret,
    issuer_view: &PublicParameters,
    context: &ProtocolContext,
    agents: &[RoleParameters],
    keys: &[S],
    owner: S,
    stages: &mut Stages<'_>,
) -> Result<Execution> {
    let count = agents.len();
    let gamma_size = 64 / count;
    let mut rng = StdRng::seed_from_u64(214_900_000 + count as u64);
    let attrs = [
        S::ONE,
        S::from(21),
        S::from(22),
        S::from(23),
        S::from(24),
        S::from(25),
    ];
    let private = [S::from(7), S::from(8), S::from(9), S::from(10)];
    let mut out = execution();
    let ((request, opening), bytes) =
        stages.run("issue_user_request_and_encode", None, false, || {
            let (q, s) = protocol::prepare_request(pp, ip, owner, &attrs, &private, &mut rng)?;
            let b = q.encode();
            Ok(((q, s), b))
        })?;
    out.message(bytes);
    let (response, bytes) = stages.run("issue_issuer_response_and_encode", None, true, || {
        let p = protocol::issue(issuer_view, ip, secret, &request, 1, &mut rng)?;
        let b = p.encode();
        Ok((p, b))
    })?;
    out.issuer_calls += 1;
    out.message(bytes);
    let mut wallet = stages.run("issue_user_full_accept", None, false, || {
        protocol::accept(pp, ip, &request, &opening, &response, &mut rng)
    })?;
    need(
        wallet.parent_opening_cache_len() == 0,
        "fresh parent already has opening advice",
    )?;
    let issuer_bytes = ip.encode();
    for (i, (view, key)) in agents.iter().zip(keys).enumerate() {
        let gamma: Vec<_> = (i * gamma_size..(i + 1) * gamma_size).collect();
        need(
            gamma.iter().all(|p| out.pools.insert(*p)),
            "overlapping agent pool allocations",
        )?;
        let before = wallet.parent_opening_cache_len();
        stages.run(
            "cold_parent_openings_for_actual_agent_scope",
            Some(i),
            false,
            || {
                for &pool in &gamma {
                    wallet.parent_opening(pp, pool)?;
                }
                Ok(())
            },
        )?;
        need(
            wallet.parent_opening_cache_len() == before + gamma.len(),
            "cold opening count differs from new pool count",
        )?;
        let sid = format!("Fig9b/equal-budget/{count}/{i}");
        let (request, bytes) =
            stages.run("delegate_agent_request_and_encode", Some(i), false, || {
                let q = spseq_fc::request_installed(
                    &view.runtime_view().id,
                    &issuer_bytes,
                    sid.as_bytes(),
                    *key,
                    &mut rng,
                )?;
                let b = q.encode();
                Ok((q, b))
            })?;
        out.message(bytes);
        let (delivery, bytes) =
            stages.run("delegate_user_send_and_encode", Some(i), false, || {
                let d = context.delegate(&mut wallet, &request, &gamma, &[true; 6], &mut rng)?;
                let b = d.delivery.encode();
                Ok((d, b))
            })?;
        out.message(bytes.clone());
        out.delegations += 1;
        let (holder, store) = stages.run(
            "delegate_agent_decode_full_receive_and_register",
            Some(i),
            false,
            || {
                let pp = view.runtime_view();
                let d = protocol::Delivery::decode(pp, &bytes)?;
                let h = protocol::complete_installed(
                    pp,
                    ip,
                    &d,
                    *key,
                    None,
                    Mode::Randomized,
                    &mut rng,
                )?;
                let store = HolderStore::new();
                store
                    .register_parent(delivery.parent, key_id(h.parent[3]), pp.w, pp.s)
                    .map_err(error)?;
                store
                    .receive_child(
                        delivery.parent,
                        delivery.child,
                        key_id(ops::mul(G1::generator(), *key)),
                        h.gamma(),
                    )
                    .map_err(error)?;
                need(
                    h.gamma() == gamma,
                    "received scope does not match assigned pools",
                )?;
                Ok((h, store))
            },
        )?;
        out.budgets.push(holder.gamma().len() * pp.s);
        out.holders.push(holder);
        out.stores.push(store);
    }
    need(
        out.pools.len() == 64 && wallet.parent_opening_cache_len() == 64,
        "not all actual pools configured",
    )?;
    need(
        out.budgets.iter().sum::<usize>() == 1024,
        "DARLT total amount differs from1024",
    )?;
    need(
        out.budgets.iter().all(|v| *v == 1024 / count),
        "DARLT individual quota unequal",
    )?;
    Ok(out)
}

fn put_proof(w: &mut Writer, p: &sma2rt_proof::Proof) {
    w.fr(p.c);
    w.u64(p.z.len() as u64);
    for z in &p.z {
        w.fr(*z);
    }
    w.u64(p.orz.len() as u64);
    for z in &p.orz {
        for x in z {
            w.fr(*x);
        }
    }
}
fn get_proof(r: &mut Reader<'_>) -> Result<sma2rt_proof::Proof> {
    let c = r.fr().map_err(error)?;
    let n = r.u64().map_err(error)?;
    need(n <= 32, "public key proof too large")?;
    let z = (0..n)
        .map(|_| r.fr().map_err(error))
        .collect::<Result<_>>()?;
    let n = r.u64().map_err(error)?;
    need(n <= 4, "public key OR proof too large")?;
    let orz = (0..n)
        .map(|_| {
            Ok([
                r.fr().map_err(error)?,
                r.fr().map_err(error)?,
                r.fr().map_err(error)?,
            ])
        })
        .collect::<Result<_>>()?;
    Ok(sma2rt_proof::Proof { c, z, orz })
}
const SMA_PACKAGE: &[u8] = b"SMA2RT/equal-budget/public-install/v1";
/// Public objects only; unused secret fields in decoded containers are zero.
fn sma_public_bytes(pp: &sma::Params, issuer: &sma::Issuer, reader: &sma::MetadataKey) -> Vec<u8> {
    let mut w = Writer::new(SMA_PACKAGE);
    w.u64(pp.k as u64);
    w.u64(pp.n);
    for p in [pp.anchor, pp.u, pp.h, pp.bit_h] {
        w.g1(p);
    }
    w.u64(pp.y.len() as u64);
    for p in &pp.y {
        w.g1(*p);
    }
    for p in issuer.vk {
        w.g2(p);
    }
    w.fr(issuer.proof.c);
    w.u64(issuer.proof.z.len() as u64);
    for z in &issuer.proof.z {
        w.fr(*z);
    }
    for p in reader.pk {
        w.g1(p);
    }
    put_proof(&mut w, &reader.proof);
    w.finish()
}
fn decode_sma_public(bytes: &[u8]) -> Result<(sma::Params, sma::Issuer, sma::MetadataKey)> {
    let mut r = Reader::new(bytes, SMA_PACKAGE).map_err(error)?;
    let k = r.u64().map_err(error)?;
    let n = r.u64().map_err(error)?;
    need(k == 10, "wrong public attribute count")?;
    let anchor = r.g1(true).map_err(error)?;
    let u = r.g1(true).map_err(error)?;
    let h = r.g1(true).map_err(error)?;
    let bit_h = r.g1(true).map_err(error)?;
    let ys = r.u64().map_err(error)?;
    need(ys == k + 3, "wrong attribute bases")?;
    let y = (0..ys)
        .map(|_| r.g1(true).map_err(error))
        .collect::<Result<_>>()?;
    let vk = [
        r.g2(true).map_err(error)?,
        r.g2(true).map_err(error)?,
        r.g2(true).map_err(error)?,
        r.g2(true).map_err(error)?,
    ];
    let c = r.fr().map_err(error)?;
    let nz = r.u64().map_err(error)?;
    need(nz == 4, "wrong issuer key proof shape")?;
    let z = (0..nz)
        .map(|_| r.fr().map_err(error))
        .collect::<Result<_>>()?;
    let pk = [r.g1(true).map_err(error)?, r.g1(true).map_err(error)?];
    let proof = get_proof(&mut r)?;
    r.finish().map_err(error)?;
    Ok((
        sma::Params {
            k: k as usize,
            n,
            anchor,
            u,
            h,
            y,
            bit_h,
        },
        sma::Issuer {
            sk: [S::ZERO; 4],
            vk,
            proof: sma::G2Proof { c, z },
        },
        sma::MetadataKey {
            sk: [S::ZERO; 2],
            pk,
            proof,
        },
    ))
}
fn sma_flow(
    pp: &sma::Params,
    issuer: &sma::Issuer,
    reader: &sma::MetadataKey,
    issuer_instance: &sma::InstalledInstance,
    agents: &[sma::InstalledInstance],
    keys: &[sma::UserKey],
    stages: &mut Stages<'_>,
) -> Result<Execution> {
    let count = agents.len();
    let mut rng = StdRng::seed_from_u64(214_910_000 + count as u64);
    let attrs = vec![
        S::ONE,
        S::from(21),
        S::from(22),
        S::from(23),
        S::from(24),
        S::from(25),
        S::from(7),
        S::from(8),
        S::from(9),
        S::from(10),
    ];
    let policy = sma::Policy {
        atoms: (0..3).map(|i| sma::Atom::Reveal(i, attrs[i])).collect(),
    };
    let mut out = execution();
    for (i, (agent, key)) in agents.iter().zip(keys).enumerate() {
        let ((pending, request), bytes) =
            stages.run("issue_agent_request_and_encode", Some(i), false, || {
                let (p, q) =
                    sma::request_installed(agent, key, &attrs, &policy, &mut rng).map_err(error)?;
                let b = q.bytes();
                Ok(((p, q), b))
            })?;
        out.message(bytes);
        let (response, bytes) =
            stages.run("issue_issuer_response_and_encode", Some(i), true, || {
                let c = sma::respond_installed(
                    issuer_instance,
                    issuer,
                    reader,
                    &request,
                    &policy,
                    1,
                    &mut rng,
                )
                .map_err(error)?;
                let b = c.bytes();
                Ok((c, b))
            })?;
        out.message(bytes);
        out.issuer_calls += 1;
        let _wallet = stages.run("issue_agent_full_receive", Some(i), false, || {
            sma::receive_installed(agent, pending, &response).map_err(error)
        })?;
        need(agent.parameters().n == pp.n, "agent installed wrong quota")?;
        out.budgets.push(agent.parameters().n as usize);
    }
    need(
        out.budgets.iter().sum::<usize>() == 1024,
        "SMA total amount differs from1024",
    )?;
    need(
        out.budgets.iter().all(|v| *v == 1024 / count),
        "SMA individual quota unequal",
    )?;
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
fn finish_accounts(
    rows: &mut Vec<Value>,
    scheme: &str,
    a: usize,
    detailed: &Execution,
    whole: &Execution,
    components: Value,
    issuer: Value,
    actual: Value,
) -> Result<()> {
    need(
        detailed.hash() == whole.hash(),
        "component and whole executions differ in native messages",
    )?;
    need(
        detailed.budgets == whole.budgets,
        "component and whole budgets differ",
    )?;
    if enabled(scheme) {
        need(
            components == actual,
            "actual whole scope differs from component counts",
        )?;
    }
    let mut row = base(scheme, Some(a), "issuer_period_account", "issuer");
    row["counts"] = issuer;
    row["actual_issuer_calls"] = json!(detailed.issuer_calls);
    row["value_type"] = json!("sum_of_actual_issuer_response_callbacks");
    rows.push(row);
    let mut row = base(
        scheme,
        Some(a),
        "system_configuration_actual_whole_scope",
        "whole_system",
    );
    row["counts"] = actual;
    row["independent_component_count_sum"] = components;
    row["counts_match"] = if enabled(scheme) {
        json!(true)
    } else {
        Value::Null
    };
    row["actual_issuer_calls"] = json!(whole.issuer_calls);
    row["actual_delegation_calls"] = json!(whole.delegations);
    row["actual_agent_quotas"] = json!(whole.budgets);
    row["actual_pool_allocations"] = json!(whole.pools.len());
    if scheme == "DARLT" {
        row["actual_agent_pool_sets"] = json!(whole
            .holders
            .iter()
            .map(|h| h.gamma().to_vec())
            .collect::<Vec<_>>());
        row["all_allocated_pools_pairwise_disjoint"] = json!(true);
    }
    row["native_message_wire_bytes"] = json!(whole.wire_bytes);
    row["independent_replay_wire_sha256"] = json!(whole.hash());
    row["wire_stream_identical_to_component_execution"] = json!(true);
    row["setup_keygen_and_public_install_included"] = json!(false);
    row["first_use_scope_opening_included"] = json!(false);
    row["state_boundary"]=json!("native allocation/binding and received-child registration; no spend verification or spent store");
    rows.push(row);
    Ok(())
}

pub fn run() -> Result<Vec<Value>> {
    run_for_agent_counts(&AGENTS)
}
pub fn run_for_agent_counts(grid: &[usize]) -> Result<Vec<Value>> {
    need(
        !grid.is_empty()
            && grid.iter().all(|a| AGENTS.contains(a))
            && grid.iter().collect::<BTreeSet<_>>().len() == grid.len(),
        "invalid agent grid",
    )?;
    let mut rows = vec![];
    let mut setup_rng = StdRng::seed_from_u64(214_909_001);
    let pp = Arc::new(outside(
        &mut rows,
        "DARLT",
        None,
        "setup_default_parameters",
        None,
        || PublicParameters::setup(1024, 16, 64, 6, 4, b"plot-Fig9b", &mut setup_rng),
    )?);
    let (ip, secret) = outside(
        &mut rows,
        "DARLT",
        None,
        "issuer_and_metadata_keygen",
        None,
        || protocol::keygen(&pp, &mut setup_rng),
    )?;
    let ip = Arc::new(ip);
    let issuer_template = outside(
        &mut rows,
        "DARLT",
        None,
        "project_issuer_package",
        None,
        || RoleParameters::from_setup(&pp, Role::Issuer),
    )?;
    let agent_template = outside(
        &mut rows,
        "DARLT",
        None,
        "project_agent_package",
        None,
        || RoleParameters::from_setup(&pp, Role::Agent),
    )?;
    for &a in grid {
        let issuer_view = outside(
            &mut rows,
            "DARLT",
            Some(a),
            "issuer_role_package_decode_and_key_install",
            None,
            || {
                let p =
                    RoleParameters::decode(&issuer_template.encode(), &issuer_template.manifest())?;
                p.install_issuer(&ip)?;
                Ok(p)
            },
        )?;
        let mut agents = vec![];
        let mut keys = vec![];
        let mut key_rng = StdRng::seed_from_u64(214_920_000 + a as u64);
        for i in 0..a {
            let p = outside(
                &mut rows,
                "DARLT",
                Some(a),
                "agent_role_package_decode_and_key_install",
                Some(i),
                || {
                    let p = RoleParameters::decode(
                        &agent_template.encode(),
                        &agent_template.manifest(),
                    )?;
                    p.install_issuer(&ip)?;
                    Ok(p)
                },
            )?;
            let key = outside(&mut rows, "DARLT", Some(a), "agent_keygen", Some(i), || {
                let sk = crate::common::crypto::nonzero(&mut key_rng);
                let _pk = ops::mul(G1::generator(), sk);
                Ok(sk)
            })?;
            agents.push(p);
            keys.push(key);
        }
        let owner = outside(&mut rows, "DARLT", Some(a), "owner_keygen", None, || {
            let sk = crate::common::crypto::nonzero(&mut key_rng);
            let _pk = ops::mul(G1::generator(), sk);
            Ok(sk)
        })?;
        let context = outside(
            &mut rows,
            "DARLT",
            Some(a),
            "owner_full_context_install_for_component_run",
            None,
            || ProtocolContext::new(pp.clone(), ip.clone()),
        )?;
        let (detailed, components, issuer) = {
            let mut stages = Stages {
                rows: &mut rows,
                scheme: "DARLT",
                agents: a,
                detailed: true,
                system: Value::Null,
                issuer: Value::Null,
                issuer_calls: 0,
            };
            let out = darlt_flow(
                &pp,
                &ip,
                &secret,
                issuer_view.runtime_view(),
                &context,
                &agents,
                &keys,
                owner,
                &mut stages,
            )?;
            need(stages.issuer_calls == 1, "DARLT component issuer count")?;
            (out, stages.system, stages.issuer)
        };
        let context = outside(
            &mut rows,
            "DARLT",
            Some(a),
            "owner_full_context_install_for_whole_replay",
            None,
            || ProtocolContext::new(pp.clone(), ip.clone()),
        )?;
        let (whole, actual) = capture("DARLT", || {
            let mut unused = vec![];
            let mut silent = Stages {
                rows: &mut unused,
                scheme: "DARLT",
                agents: a,
                detailed: false,
                system: Value::Null,
                issuer: Value::Null,
                issuer_calls: 0,
            };
            darlt_flow(
                &pp,
                &ip,
                &secret,
                issuer_view.runtime_view(),
                &context,
                &agents,
                &keys,
                owner,
                &mut silent,
            )
        })?;
        finish_accounts(
            &mut rows, "DARLT", a, &detailed, &whole, components, issuer, actual,
        )?;
        for (i, mut holder) in detailed.holders.into_iter().enumerate() {
            let first = holder.gamma()[0];
            need(
                holder.scope_opening_cache_len() == 0,
                "scope opening was prepared inside configuration",
            )?;
            outside(
                &mut rows,
                "DARLT",
                Some(a),
                "first_use_one_pool_scope_opening",
                Some(i),
                || {
                    holder.scope_opening(agents[i].runtime_view(), first)?;
                    need(
                        holder.scope_opening_cache_len() == 1,
                        "first opening not cached",
                    )
                },
            )?;
        }
        let mut row = base(
            "DARLT",
            Some(a),
            "role_distribution_actual_bytes",
            "outside_system_configuration",
        );
        row["agent_role_package_bytes_each"] = json!(agent_template.encode().len());
        row["trusted_manifest_bytes_each"] = json!(agent_template.manifest().encode().len());
        row["issuer_public_and_key_proof_bytes_each"] = json!(ip.encode().len());
        row["actual_agent_install_calls"] = json!(a);
        row["first_use_scope_boundary"] =
            json!("one first-pool opening per agent; not all future scope openings");
        row["independent_whole_replay_uses_same_immutable_installed_agent_views"] = json!(true);
        rows.push(row);
    }
    for &a in grid {
        let quota = 1024 / a;
        let mut rng = StdRng::seed_from_u64(214_930_000 + a as u64);
        let pp = outside(
            &mut rows,
            "SMA²RT",
            Some(a),
            "setup_public_parameters_for_per_agent_quota",
            None,
            || Ok(sma::setup(10, quota as u64)),
        )?;
        let issuer = outside(&mut rows, "SMA²RT", Some(a), "issuer_keygen", None, || {
            Ok(sma::ikeygen(&pp, &mut rng))
        })?;
        let reader = outside(
            &mut rows,
            "SMA²RT",
            Some(a),
            "metadata_keygen",
            None,
            || Ok(sma::vkeygen(&pp, &mut rng)),
        )?;
        let issuer_instance = outside(
            &mut rows,
            "SMA²RT",
            Some(a),
            "issuer_public_instance_install",
            None,
            || sma::install_instance(&pp, &issuer, &reader).map_err(error),
        )?;
        let mut agents = vec![];
        let mut keys = vec![];
        for i in 0..a {
            let h = outside(
                &mut rows,
                "SMA²RT",
                Some(a),
                "agent_public_package_decode_and_key_install",
                Some(i),
                || {
                    let bytes = sma_public_bytes(&pp, &issuer, &reader);
                    let (p, issuer, reader) = decode_sma_public(&bytes)?;
                    need(
                        sma_public_bytes(&p, &issuer, &reader) == bytes,
                        "SMA public package not canonical",
                    )?;
                    sma::install_instance(&p, &issuer, &reader).map_err(error)
                },
            )?;
            let key = outside(
                &mut rows,
                "SMA²RT",
                Some(a),
                "agent_keygen",
                Some(i),
                || Ok(sma::ukeygen(&mut rng)),
            )?;
            agents.push(h);
            keys.push(key);
        }
        let (detailed, components, issuer_counts) = {
            let mut stages = Stages {
                rows: &mut rows,
                scheme: "SMA²RT",
                agents: a,
                detailed: true,
                system: Value::Null,
                issuer: Value::Null,
                issuer_calls: 0,
            };
            let out = sma_flow(
                &pp,
                &issuer,
                &reader,
                &issuer_instance,
                &agents,
                &keys,
                &mut stages,
            )?;
            need(stages.issuer_calls == a, "SMA component issuer count")?;
            (out, stages.system, stages.issuer)
        };
        let (whole, actual) = capture("SMA²RT", || {
            let mut unused = vec![];
            let mut silent = Stages {
                rows: &mut unused,
                scheme: "SMA²RT",
                agents: a,
                detailed: false,
                system: Value::Null,
                issuer: Value::Null,
                issuer_calls: 0,
            };
            sma_flow(
                &pp,
                &issuer,
                &reader,
                &issuer_instance,
                &agents,
                &keys,
                &mut silent,
            )
        })?;
        finish_accounts(
            &mut rows,
            "SMA²RT",
            a,
            &detailed,
            &whole,
            components,
            issuer_counts,
            actual,
        )?;
        let mut row = base(
            "SMA²RT",
            Some(a),
            "role_distribution_actual_bytes",
            "outside_system_configuration",
        );
        row["agent_public_package_bytes_each"] =
            json!(sma_public_bytes(&pp, &issuer, &reader).len());
        row["actual_agent_install_calls"] = json!(a);
        row["per_agent_native_counter_bound"] = json!(quota);
        row["independent_whole_replay_uses_same_immutable_installed_agent_views"] = json!(true);
        rows.push(row);
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn two_agents_are_equal_quota_real_configurations_with_independent_totals() -> Result<()> {
        let rows = run_for_agent_counts(&[2])?;
        let totals: Vec<_> = rows
            .iter()
            .filter(|r| r["phase"] == "system_configuration_actual_whole_scope")
            .collect();
        assert_eq!(totals.len(), 2);
        for row in totals {
            assert_eq!(row["actual_agent_quotas"], json!([512, 512]));
            assert_eq!(row["wire_stream_identical_to_component_execution"], true);
            assert_eq!(row["setup_keygen_and_public_install_included"], false);
            assert_eq!(
                row["actual_issuer_calls"],
                if row["scheme"] == "DARLT" { 1 } else { 2 }
            );
            if row["op_counts_enabled"] == true {
                assert_eq!(row["counts_match"], true);
            }
        }
        assert!(rows
            .iter()
            .all(|r| r["timing_enabled"] == false && r["formal_samples"] == 0));
        assert!(run_for_agent_counts(&[3]).is_err());
        Ok(())
    }
}
