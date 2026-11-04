//! Schedulable native DARLT DARLT role boundaries and independent scale scans.
//! Fixtures are built outside the selected boundary; strict received checks are
//! performed once before the unchanged native equations.
use crate::{
    batch_runtime::Adapter,
    common::spent::{Identifier, SpentSnapshot, SpentStore},
    darlt::{
        context::{Child, Delegation, ProtocolContext},
        instrumentation,
        protocol::{self, Holder, IssuerPublic, IssuerSecret, PublicParameters, Wallet},
        role_params::{Role, RoleParameters},
        sigma,
        spend::{self, Atom, Policy, ReceivedToken, Token},
        state::HolderStore,
        verification::Mode,
    },
    experiment::{Action, BoundaryClock, Job, Worker},
    polynomial::S,
    sampling::SampleClass,
    spseq_fc,
};
use blstrs::{G1Projective as G1, G2Projective as G2};
use ff::Field;
use group::Group;
use rand::{
    rngs::{OsRng, StdRng},
    RngCore, SeedableRng,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
    sync::Arc,
};

type Result<T> = std::result::Result<T, String>;
const KS: [usize; crate::harness::K_VALUES.len()] = crate::harness::K_VALUES;
const AGENTS: [usize; 7] = [1, 2, 4, 8, 16, 32, 64];
fn need(ok: bool, why: &str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(why.into())
    }
}
fn err(e: impl std::fmt::Display) -> String {
    e.to_string()
}
/// Verifier-only random tape, independent of the reproducible prover fixture.
/// Initialization is outside every selected timing boundary; individual
/// rejection-sampled 16-byte batch coefficients are drawn inside verification.
fn batch_rng() -> Result<StdRng> {
    let mut seed = [0u8; 32];
    OsRng.try_fill_bytes(&mut seed).map_err(err)?;
    Ok(StdRng::from_seed(seed))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Config {
    n: usize,
    s: usize,
    del: usize,
    private: usize,
    range: Option<usize>,
}
impl Default for Config {
    fn default() -> Self {
        Self {
            n: 1024,
            s: 16,
            del: 6,
            private: 4,
            range: None,
        }
    }
}
impl Config {
    fn workload(self) -> Value {
        json!({"n":self.n,"s":self.s,"w":self.n/self.s,"k_max":64,
            "attributes":self.del+self.private,"delegatable_attributes":self.del,
            "private_attributes":self.private,"range_bits":self.range})
    }
    fn attributes(self) -> (Vec<S>, Vec<S>) {
        (
            (0..self.del)
                .map(|i| {
                    if i == 0 {
                        S::ONE
                    } else {
                        S::from(20 + i as u64)
                    }
                })
                .collect(),
            (0..self.private).map(|i| S::from(7 + i as u64)).collect(),
        )
    }
    fn policy(self) -> Policy {
        let mut atoms = vec![
            Atom::Equal(0, S::ONE),
            Atom::Reveal(1, S::from(21)),
            Atom::Reveal(2, S::from(22)),
        ];
        if let Some(bits) = self.range {
            atoms.push(Atom::Range(3, 0, (1u64 << bits) - 1));
        }
        Policy { period: 1, atoms }
    }
}
struct Fixture {
    config: Config,
    pp: Arc<PublicParameters>,
    ip: Arc<IssuerPublic>,
    sk: IssuerSecret,
    context: ProtocolContext,
    wallet: Wallet,
    agent: RoleParameters,
    verifier: RoleParameters,
}
impl Fixture {
    fn new(config: Config) -> Result<Self> {
        let mut rng = StdRng::seed_from_u64(
            30_214_000 + config.n as u64 + config.s as u64 + config.del as u64,
        );
        let pp = Arc::new(PublicParameters::setup(
            config.n,
            config.s,
            64,
            config.del,
            config.private,
            b"DARLT/fixture",
            &mut rng,
        )?);
        let (ip, sk) = protocol::keygen(&pp, &mut rng)?;
        let ip = Arc::new(decode_issuer(&ip.encode())?);
        let context = ProtocolContext::new(pp.clone(), ip.clone())?;
        let agent = RoleParameters::from_setup(&pp, Role::Agent)?;
        let agent = RoleParameters::decode(&agent.encode(), &agent.manifest())?;
        agent.install_issuer(&ip)?;
        let verifier = RoleParameters::from_setup(&pp, Role::Verifier)?;
        let verifier = RoleParameters::decode(&verifier.encode(), &verifier.manifest())?;
        verifier.install_issuer(&ip)?;
        let (attrs, private) = config.attributes();
        let (q, sec) =
            protocol::prepare_request(&pp, &ip, S::from(91), &attrs, &private, &mut rng)?;
        let received_q = protocol::ReceivedIssueRequest::decode(&pp, &q.encode())?;
        let res = protocol::issue_received_installed(&pp, &ip, &sk, &received_q, 1, &mut rng)?;
        let res = protocol::ReceivedIssueResponse::decode(&pp, &res.encode())?;
        let wallet =
            protocol::accept_received_installed(&pp, &ip, &q, &sec, &res, &mut batch_rng()?)?;
        Ok(Self {
            config,
            pp,
            ip,
            sk,
            context,
            wallet,
            agent,
            verifier,
        })
    }
    fn child_from_wallet(
        &self,
        wallet: &Wallet,
        gamma: usize,
        hot: bool,
        rng: &mut StdRng,
    ) -> Result<(ProtocolContext, Child)> {
        let sender = self.context.fresh_holder_context();
        let receiver = self.context.fresh_holder_context();
        let mut wallet = wallet.clone();
        let recipient_key = S::from(111);
        let request = sender.delegation_request(b"trial-agent-child", recipient_key, rng)?;
        let request = protocol::ReceivedRecipientRequest::decode(self.pp.id, &request.encode())?;
        let delivery = sender.delegate_received(
            &mut wallet,
            &request,
            &(0..gamma).collect::<Vec<_>>(),
            &vec![true; self.pp.k_del],
            rng,
        )?;
        let parsed = protocol::ReceivedDelivery::decode(
            self.agent.runtime_view(),
            &delivery.delivery.encode(),
        )?;
        let mut verifier_rng = batch_rng()?;
        let holder = protocol::complete_received_installed(
            self.agent.runtime_view(),
            &self.ip,
            &parsed,
            recipient_key,
            None,
            Mode::Randomized,
            &mut verifier_rng,
        )?;
        let state = receiver.holder_state();
        state
            .register_parent(
                delivery.parent,
                crate::darlt::context::key_id(holder.parent[3]),
                self.pp.w,
                self.pp.s,
            )
            .map_err(err)?;
        state
            .receive_child(
                delivery.parent,
                delivery.child,
                crate::darlt::context::key_id(crate::ops::mul(G1::generator(), recipient_key)),
                holder.gamma(),
            )
            .map_err(err)?;
        let mut child = Child {
            parent: delivery.parent,
            id: delivery.child,
            holder,
        };
        if hot {
            for b in 0..gamma {
                child.holder.scope_opening(&self.pp, b)?;
            }
        }
        Ok((receiver, child))
    }
}

#[derive(Clone, Debug)]
enum Task {
    Setup,
    Keygen,
    Install(Role),
    IssueRequest,
    IssueIssuer,
    IssueAccept,
    Parent(bool),
    DelegateRequest,
    DelegateSend {
        gamma: usize,
        hot: bool,
    },
    DelegateReceive(usize),
    SelfAllocate {
        gamma: usize,
        hot: bool,
    },
    Scope(bool),
    Prepare(usize),
    Online(usize),
    Encode(usize),
    Decode(usize),
    DecodeAblation(usize),
    Verify {
        k: usize,
        mode: Mode,
        per_block: bool,
        ablation: bool,
    },
    Inclusive {
        k: usize,
        mode: Mode,
        per_block: bool,
        ablation: bool,
    },
    State(usize),
    Judge {
        mode: Mode,
        validated: bool,
        double_use: bool,
    },
    Metadata {
        full: bool,
        bit: usize,
    },
    CrossChild,
    PartialPool,
    Provision {
        agents: usize,
        issuer: bool,
    },
}
#[derive(Clone)]
struct Spec {
    job: Job,
    config: Config,
    task: Task,
    selected_span: Option<(&'static str, bool)>,
}
pub struct Factory {
    specs: Vec<Spec>,
    fixtures: BTreeMap<Config, Arc<Fixture>>,
    pipeline_assets: BTreeMap<Config, Rc<RefCell<PipelineAssets>>>,
}

/// Only long-lived accepted material is retained between requests. Session
/// nonces, prepared proofs, tokens and verification results are never cached.
struct PipelineAssets {
    wallet: Wallet,
    sequence: u64,
    retained_setup: Option<PublicParameters>,
    retained_keygen: Option<(IssuerPublic, IssuerSecret)>,
    spent_baseline: Option<SpentSnapshot>,
    accepted_children: BTreeMap<usize, Holder>,
    hot_children: BTreeMap<usize, Holder>,
    provision_installed: BTreeMap<usize, Rc<Vec<RoleParameters>>>,
}

struct SelectedClock<'a> {
    clock: &'a mut BoundaryClock,
    span: Option<(&'static str, bool)>,
}
impl SelectedClock<'_> {
    fn measure<T>(&mut self, action: impl FnOnce() -> Result<T>) -> Result<T> {
        if let Some((name, exclusive)) = self.span {
            self.clock.measure_darlt_substage(name, exclusive, action)
        } else {
            self.clock.measure(action)
        }
    }
}
type Body = Box<dyn FnOnce(&mut SelectedClock<'_>) -> Result<Value>>;
fn wrap(body: Body, span: Option<(&'static str, bool)>) -> Action {
    Box::new(move |clock| body(&mut SelectedClock { clock, span }))
}

fn spec(id: String, role: &str, stage: &str, config: Config, task: Task) -> Spec {
    let mut job = Job::new(&id, "DARLT", role, stage);
    job.workload = config.workload();
    job.boundary = json!({"network_included":false,"persistence_included":false,
        "fresh_holder_state_per_trial":true,"shared_immutable_installation":true,
        "fixture_work_included":false,"wire_encoding_included":false,
        "strict_decoding_included":false,"shared_state_included":false});
    match &task {
        Task::Setup => {
            job.cache = "not_applicable".into();
            job.class = SampleClass::SlowProtocol;
            job.boundary["shared_immutable_installation"] = json!(false);
        }
        Task::Install(_) => {
            job.cache = "cold".into();
            job.boundary["strict_decoding_included"] = json!(true);
            job.boundary["shared_immutable_installation"] = json!(false);
        }
        Task::Parent(hot) | Task::Scope(hot) => {
            job.cache = if *hot { "hot" } else { "cold" }.into()
        }
        Task::DelegateSend { gamma, hot } | Task::SelfAllocate { gamma, hot } => {
            job.workload["gamma"] = json!(gamma);
            job.cache = if *hot { "hot" } else { "cold" }.into();
            job.boundary["shared_state_included"] = json!(true);
        }
        Task::DelegateReceive(gamma) => {
            job.workload["gamma"] = json!(gamma);
            job.boundary["strict_decoding_included"] = json!(true);
            job.boundary["shared_state_included"] = json!(true);
        }
        Task::Prepare(k)
        | Task::Online(k)
        | Task::Encode(k)
        | Task::Decode(k)
        | Task::DecodeAblation(k)
        | Task::State(k) => {
            job.workload["k"] = json!(k);
        }
        Task::Verify {
            k,
            mode,
            per_block,
            ablation,
        }
        | Task::Inclusive {
            k,
            mode,
            per_block,
            ablation,
        } => {
            job.workload["k"] = json!(k);
            job.workload["darlt_blocks"] = json!(if *ablation { *k } else { k.div_ceil(64) });
            job.profile = if *mode == Mode::Specification {
                "Specification"
            } else if *per_block {
                "RandomizedPerBlock"
            } else {
                "RandomizedAcrossBlocks"
            }
            .into();
            job.workload["ablation"] = json!(ablation);
        }
        Task::Provision { agents, issuer } => {
            job.workload["agents"] = json!(agents);
            job.workload["total_quota"] = json!(1024);
            job.workload["per_agent_quota"] = json!(1024 / agents);
            job.workload["gamma"] = json!(64 / agents);
            job.workload["actual_issuer_calls"] = json!(1);
            job.workload["actual_delegation_calls"] = json!(if *issuer { 0 } else { *agents });
            job.boundary["setup_keygen_and_public_install_included"] = json!(false);
            job.boundary["first_use_scope_opening_included"] = json!(false);
            job.boundary["shared_state_included"] = json!(!issuer);
        }
        _ => {}
    }
    match task {
        Task::IssueRequest
        | Task::IssueIssuer
        | Task::DelegateRequest
        | Task::DelegateSend { .. }
        | Task::Encode(_)
        | Task::Provision { .. } => job.boundary["wire_encoding_included"] = json!(true),
        _ => {}
    }
    match task {
        Task::IssueIssuer
        | Task::IssueAccept
        | Task::DelegateSend { .. }
        | Task::Decode(_)
        | Task::DecodeAblation(_)
        | Task::Provision { issuer: false, .. } => {
            job.boundary["strict_decoding_included"] = json!(true)
        }
        _ => {}
    }
    if matches!(task, Task::State(_)) {
        job.boundary["shared_state_included"] = json!(true);
        job.boundary["state_scope"] = json!("record_checked_only");
        job.boundary["request_binding"] = json!("outside");
        job.boundary["id_extraction"] = json!("outside");
    }
    if matches!(task, Task::Verify { .. } | Task::Inclusive { .. }) {
        job.boundary["strict_decoding_included"] = json!(true);
        job.boundary["received_bytes_first"] = json!(true);
        job.boundary["all_packets_decoded_before_algorithm"] = json!(true);
    }
    if matches!(
        task,
        Task::IssueIssuer
            | Task::DelegateSend { .. }
            | Task::IssueAccept
            | Task::DelegateReceive(_)
            | Task::Verify { .. }
            | Task::Inclusive { .. }
            | Task::Decode(_)
            | Task::DecodeAblation(_)
            | Task::Judge {
                validated: false,
                ..
            }
            | Task::Metadata { full: true, .. }
    ) {
        job.boundary["strict_decoding_included"] = json!(true);
        job.boundary["received_bytes_first"] = json!(true);
        job.boundary["subgroup_checks_included"] = json!(true);
        job.boundary["native_format_checks_included"] = json!(true);
        job.boundary["subgroup_checks_per_received_element"] = json!(1);
        job.boundary["received_input_provenance"] = json!("sealed_checked_input");
    }
    if let Task::Decode(k) | Task::DecodeAblation(k) = task {
        let ablation = matches!(task, Task::DecodeAblation(_));
        job.workload["ablation"] = json!(ablation);
        job.workload["darlt_blocks"] = json!(if ablation { k } else { k.div_ceil(64) });
        job.boundary["decoder_scope"] =
            json!("canonical_group_subgroup_native_identity_and_shape_only");
        job.boundary["decode_only"] = json!(true);
        job.boundary["parent_verification_stage"] = json!("verification_crypto");
        job.boundary["signature_or_proof_equations_included"] = json!(false);
    }
    if matches!(
        task,
        Task::Judge {
            validated: false,
            ..
        } | Task::Metadata { full: true, .. }
    ) {
        job.boundary["strict_decoding_included"] = json!(true);
        job.boundary["received_bytes_first"] = json!(true);
        job.boundary["subgroup_checks_included"] = json!(true);
        job.boundary["native_format_checks_included"] = json!(true);
    }
    if matches!(task, Task::Inclusive { .. }) {
        job.boundary["shared_state_included"] = json!(true);
        job.boundary["inclusive_total"] = json!(true);
        job.boundary["wire_encoding_included"] = json!(true);
    }
    if matches!(task, Task::State(_) | Task::Inclusive { .. }) {
        job.workload["history_records"] = json!(10000);
        job.workload["history_id_bytes"] = json!(48);
        job.boundary["history_fixture_included"] = json!(false);
    }
    if let Task::Metadata { bit, .. } = task {
        job.workload["hidden_bit"] = json!(bit);
    }
    if matches!(
        task,
        Task::IssueAccept | Task::DelegateReceive(_) | Task::Metadata { full: true, .. }
    ) {
        job.profile = "Randomized".into();
    }
    if matches!(
        task,
        Task::IssueAccept
            | Task::DelegateReceive(_)
            | Task::Verify {
                mode: Mode::Randomized,
                ..
            }
            | Task::Inclusive {
                mode: Mode::Randomized,
                ..
            }
            | Task::Judge {
                mode: Mode::Randomized,
                validated: false,
                ..
            }
            | Task::Metadata { full: true, .. }
            | Task::Provision { issuer: false, .. }
    ) {
        job.boundary["pairing_batch_weight_bits"] = json!(128);
        job.boundary["pairing_batch_weight_distribution"] =
            json!("independent uniform integers in 1..2^128-1");
        job.boundary["verifier_random_tape"] =
            json!("StdRng(ChaCha12), 256-bit OsRng seed, initialization outside selected boundary");
        job.boundary["batch_weight_sampling_included"] = json!(true);
    }
    if let Task::Judge { double_use, .. } = task {
        job.workload["judge_branch"] = json!(if double_use {
            "DoubleUse"
        } else {
            "DoubleAlloc"
        });
    }
    if let Task::Judge { mode, .. } = task {
        job.profile = format!("{mode:?}");
    }
    Spec {
        job,
        config,
        task,
        selected_span: None,
    }
}
pub fn new() -> Result<Factory> {
    let mut specs = vec![];
    let d = Config::default();
    let mut add = |suffix: &str, role: &str, stage: &str, task: Task| {
        specs.push(spec(format!("darlt/{suffix}"), role, stage, d, task))
    };
    add("setup", "system", "setup", Task::Setup);
    add("keygen", "issuer", "key_generation", Task::Keygen);
    for role in [Role::User, Role::Issuer, Role::Agent, Role::Verifier] {
        add(
            &format!("install/{}", role.name()),
            role.name(),
            "install",
            Task::Install(role),
        );
    }
    add("issue/request", "user", "issue_request", Task::IssueRequest);
    add(
        "issue/issuer",
        "issuer",
        "issue_response",
        Task::IssueIssuer,
    );
    add("issue/accept", "user", "issue_accept", Task::IssueAccept);
    for hot in [false, true] {
        let cache = if hot { "hot" } else { "cold" };
        add(
            &format!("parent/{cache}"),
            "user",
            "parent_opening",
            Task::Parent(hot),
        );
        add(
            &format!("scope/{cache}"),
            "agent",
            "scope_opening",
            Task::Scope(hot),
        );
        for gamma in AGENTS {
            add(
                &format!("delegate/send/{cache}/g{gamma}"),
                "user",
                "delegate_send",
                Task::DelegateSend { gamma, hot },
            );
            add(
                &format!("self/{cache}/g{gamma}"),
                "user",
                "self_allocate",
                Task::SelfAllocate { gamma, hot },
            );
        }
    }
    add(
        "delegate/request",
        "agent",
        "delegate_request",
        Task::DelegateRequest,
    );
    for gamma in AGENTS {
        add(
            &format!("delegate/receive/g{gamma}"),
            "agent",
            "delegate_receive",
            Task::DelegateReceive(gamma),
        );
    }
    for k in KS {
        add(
            &format!("prepare/k{k}"),
            "agent",
            "preparation",
            Task::Prepare(k),
        );
        add(
            &format!("online/k{k}"),
            "agent",
            "online_generation",
            Task::Online(k),
        );
        add(
            &format!("encode/k{k}"),
            "agent",
            "encoding",
            Task::Encode(k),
        );
        add(
            &format!("decode/k{k}"),
            "verifier",
            "strict_decoding",
            Task::Decode(k),
        );
        add(
            &format!("decode/ablation/k{k}"),
            "verifier",
            "strict_decoding",
            Task::DecodeAblation(k),
        );
        add(
            &format!("state/k{k}"),
            "verifier",
            "shared_state",
            Task::State(k),
        );
        for (name, mode, per_block) in [
            ("Specification", Mode::Specification, false),
            ("RandomizedPerBlock", Mode::Randomized, true),
            ("RandomizedAcrossBlocks", Mode::Randomized, false),
        ] {
            for ablation in [false, true] {
                add(
                    &format!(
                        "verify/{name}/{}/k{k}",
                        if ablation { "ablation" } else { "native" }
                    ),
                    "verifier",
                    "verification_crypto",
                    Task::Verify {
                        k,
                        mode,
                        per_block,
                        ablation,
                    },
                );
                add(
                    &format!(
                        "inclusive/{name}/{}/k{k}",
                        if ablation { "ablation" } else { "native" }
                    ),
                    "verifier",
                    "inclusive_verification",
                    Task::Inclusive {
                        k,
                        mode,
                        per_block,
                        ablation,
                    },
                );
            }
        }
    }
    add(
        "judge/spec",
        "authority",
        "identify",
        Task::Judge {
            mode: Mode::Specification,
            validated: false,
            double_use: false,
        },
    );
    add(
        "judge/randomized",
        "authority",
        "identify",
        Task::Judge {
            mode: Mode::Randomized,
            validated: false,
            double_use: false,
        },
    );
    add(
        "judge/validated",
        "authority",
        "identify_validated",
        Task::Judge {
            mode: Mode::Specification,
            validated: true,
            double_use: false,
        },
    );
    for (label, mode, validated) in [
        ("spec", Mode::Specification, false),
        ("randomized", Mode::Randomized, false),
        ("validated", Mode::Specification, true),
    ] {
        add(
            &format!("judge/double-use/{label}"),
            "authority",
            if validated {
                "identify_validated"
            } else {
                "identify"
            },
            Task::Judge {
                mode,
                validated,
                double_use: true,
            },
        );
    }
    for bit in [0, 1] {
        add(
            &format!("metadata/validated/bit{bit}"),
            "reader",
            "metadata_read",
            Task::Metadata { full: false, bit },
        );
        add(
            &format!("metadata/full/bit{bit}"),
            "reader",
            "native_read",
            Task::Metadata { full: true, bit },
        );
    }
    add(
        "cross-child/k17",
        "user",
        "cross_child_spend",
        Task::CrossChild,
    );
    add(
        "partial-pool/k16",
        "user",
        "partially_consumed_pool_spend",
        Task::PartialPool,
    );
    for agents in AGENTS {
        for issuer in [true, false] {
            add(
                &format!(
                    "provision/{}/{agents}",
                    if issuer { "issuer" } else { "system" }
                ),
                if issuer { "issuer" } else { "system" },
                if issuer {
                    "provisioning_issuer"
                } else {
                    "provisioning_system"
                },
                Task::Provision { agents, issuer },
            );
        }
    }
    let mut scans = vec![];
    for a in [5, 10, 15, 20, 25, 30] {
        scans.push((
            format!("attributes/{a}"),
            Config {
                del: a,
                private: 0,
                ..d
            },
        ));
    }
    for bits in [8, 16, 32] {
        scans.push((
            format!("range/{bits}"),
            Config {
                range: Some(bits),
                ..d
            },
        ));
    }
    for n in [256, 1024, 4096] {
        for s in [16, 64, 256] {
            if n % s == 0 {
                scans.push((format!("scale/n{n}/s{s}"), Config { n, s, ..d }));
            }
        }
    }
    for (id, c) in scans {
        for (phase, role, stage, task) in [
            ("issue-request", "user", "issue_request", Task::IssueRequest),
            (
                "issue-issuer",
                "issuer",
                "issue_response",
                Task::IssueIssuer,
            ),
            ("issue-accept", "user", "issue_accept", Task::IssueAccept),
            (
                "delegate-cold",
                "user",
                "delegate_send",
                Task::DelegateSend {
                    gamma: 1,
                    hot: false,
                },
            ),
            (
                "delegate-hot",
                "user",
                "delegate_send",
                Task::DelegateSend {
                    gamma: 1,
                    hot: true,
                },
            ),
            ("prepare", "agent", "preparation", Task::Prepare(16)),
            ("online", "agent", "online_generation", Task::Online(16)),
            ("decode", "verifier", "strict_decoding", Task::Decode(16)),
            (
                "valid-spec",
                "verifier",
                "verification_crypto",
                Task::Verify {
                    k: 16,
                    mode: Mode::Specification,
                    per_block: false,
                    ablation: false,
                },
            ),
            (
                "valid-randomized",
                "verifier",
                "verification_crypto",
                Task::Verify {
                    k: 16,
                    mode: Mode::Randomized,
                    per_block: false,
                    ablation: false,
                },
            ),
            (
                "valid-randomized/inclusive",
                "verifier",
                "inclusive_verification",
                Task::Inclusive {
                    k: 16,
                    mode: Mode::Randomized,
                    per_block: false,
                    ablation: false,
                },
            ),
        ] {
            specs.push(spec(
                format!("darlt/scan/{id}/{phase}"),
                role,
                stage,
                c,
                task,
            ));
        }
    }
    // A decomposition is a separate real native execution, not an allocation
    // of the outer total by an operation-count formula. Each hook must run.
    let fine: [(&str, &[&'static str]); 13] = [
        (
            "darlt/issue/request",
            &[
                "encoding",
                "fiat_shamir",
                "subgroup_check",
                "sigma_response",
                "group_msm_g1",
            ],
        ),
        (
            "darlt/issue/issuer",
            &[
                "encoding",
                "strict_decoding",
                "point_decode_and_subgroup",
                "hash_to_group",
                "fiat_shamir",
                "subgroup_check",
                "group_msm_g1",
            ],
        ),
        (
            "darlt/issue/accept",
            &[
                "encoding",
                "strict_decoding",
                "point_decode_and_subgroup",
                "hash_to_group",
                "fiat_shamir",
                "subgroup_check",
                "group_msm_g1",
                "miller_loop",
                "final_exponentiation",
            ],
        ),
        (
            "darlt/delegate/send/cold/g8",
            &[
                "encoding",
                "strict_decoding",
                "point_decode_and_subgroup",
                "state_access",
                "parent_opening_cache_and_compute",
                "subgroup_check",
                "group_msm_g1",
                "group_msm_g2",
            ],
        ),
        (
            "darlt/delegate/receive/g8",
            &[
                "encoding",
                "strict_decoding",
                "point_decode_and_subgroup",
                "state_access",
                "subgroup_check",
                "group_msm_g1",
                "group_msm_g2",
                "miller_loop",
                "final_exponentiation",
            ],
        ),
        (
            "darlt/self/cold/g8",
            &[
                "encoding",
                "state_access",
                "parent_opening_cache_and_compute",
                "group_msm_g1",
                "group_msm_g2",
            ],
        ),
        (
            "darlt/scope/cold",
            &["scope_opening_cache_and_compute", "group_msm_g2"],
        ),
        (
            "darlt/prepare/k16",
            &[
                "hash_to_group",
                "fiat_shamir",
                "fiat_shamir_transcript",
                "polynomial",
                "subgroup_check",
                "encoding",
                "group_msm_g1",
                "group_msm_g2",
            ],
        ),
        (
            "darlt/online/k16",
            &[
                "sigma_response",
                "fiat_shamir",
                "fiat_shamir_transcript",
                "encoding",
                "subgroup_check",
                "group_msm_g1",
            ],
        ),
        (
            "darlt/verify/Specification/native/k16",
            &[
                "hash_to_group",
                "fiat_shamir",
                "polynomial",
                "point_decode_and_subgroup",
                "encoding",
                "group_msm_g1",
                "miller_loop",
                "final_exponentiation",
            ],
        ),
        (
            "darlt/verify/RandomizedAcrossBlocks/native/k16",
            &[
                "hash_to_group",
                "fiat_shamir",
                "polynomial",
                "point_decode_and_subgroup",
                "encoding",
                "group_msm_g1",
                "group_msm_g2",
                "miller_loop",
                "final_exponentiation",
            ],
        ),
        (
            "darlt/install/user",
            &[
                "strict_decoding",
                "point_decode_and_subgroup",
                "parameter_installation",
                "key_proof_installation",
                "subgroup_check",
            ],
        ),
        (
            "darlt/decode/k16",
            &["strict_decoding", "point_decode_and_subgroup"],
        ),
    ];
    let mut detailed = vec![];
    for (id, names) in fine {
        let field_covered = [
            "darlt/issue/request",
            "darlt/issue/issuer",
            "darlt/issue/accept",
            "darlt/prepare/k16",
            "darlt/online/k16",
            "darlt/verify/Specification/native/k16",
            "darlt/verify/RandomizedAcrossBlocks/native/k16",
            "darlt/install/user",
        ]
        .contains(&id);
        let source = specs
            .iter()
            .find(|s| s.job.id == id)
            .ok_or("missing decomposition parent")?;
        for name in names
            .iter()
            .copied()
            .chain(field_covered.then_some("field_arithmetic"))
        {
            for exclusive in [false, true] {
                let mut s = source.clone();
                s.job.id = format!(
                    "{id}/substage/{name}/{}",
                    if exclusive { "exclusive" } else { "inclusive" }
                );
                s.job.substage = name.into();
                s.job.boundary["span_duration"] =
                    json!(if exclusive { "exclusive" } else { "inclusive" });
                s.job.boundary["decomposition_of_total_job"] = json!(id);
                s.selected_span = Some((name, exclusive));
                detailed.push(s);
            }
        }
    }
    specs.extend(detailed);
    need(
        specs
            .iter()
            .map(|s| &s.job.id)
            .collect::<BTreeSet<_>>()
            .len()
            == specs.len(),
        "duplicate DARLT job",
    )?;
    Ok(Factory {
        specs,
        fixtures: BTreeMap::new(),
        pipeline_assets: BTreeMap::new(),
    })
}
impl Worker for Factory {
    fn jobs(&self) -> Vec<Job> {
        self.specs.iter().map(|s| s.job.clone()).collect()
    }
    fn prepare(&mut self, id: &str, trial: u64) -> Result<Action> {
        let spec = self
            .specs
            .iter()
            .find(|s| s.job.id == id)
            .cloned()
            .ok_or("unknown DARLT job")?;
        let seed = 30_000_000u64
            .wrapping_add(trial)
            .wrapping_add(u64::from_be_bytes(
                Sha256::digest(id.as_bytes())[..8].try_into().unwrap(),
            ));
        if matches!(spec.task, Task::Setup) {
            return Ok(wrap(
                Box::new(move |clock| {
                    let c = spec.config;
                    let mut rng = StdRng::seed_from_u64(seed);
                    let pp = clock.measure(|| {
                        PublicParameters::setup(
                            c.n,
                            c.s,
                            64,
                            c.del,
                            c.private,
                            b"fixture/setup",
                            &mut rng,
                        )
                    })?;
                    Ok(
                        json!({"actual_parameter_bytes":pp.encode().len(),"degree":pp.srs.degree,"query_cache_points":pp.query_bases.values().map(|(p,_)|p.len()+1).sum::<usize>()}),
                    )
                }),
                spec.selected_span,
            ));
        }
        if let std::collections::btree_map::Entry::Vacant(entry) = self.fixtures.entry(spec.config)
        {
            entry.insert(Arc::new(Fixture::new(spec.config)?));
        }
        let f = self.fixtures[&spec.config].clone();
        Ok(wrap(
            prepare_action(f, spec.task, seed)?,
            spec.selected_span,
        ))
    }
    fn prepare_pipeline(&mut self, ids: &[String], trial: u64) -> Result<Action> {
        need(!ids.is_empty(), "empty DARLT pipeline")?;
        let specs = ids
            .iter()
            .map(|id| {
                self.specs
                    .iter()
                    .find(|s| s.job.id == *id)
                    .cloned()
                    .ok_or_else(|| format!("unknown DARLT pipeline job {id}"))
            })
            .collect::<Result<Vec<_>>>()?;
        let config = specs[0].config;
        need(
            specs.iter().all(|s| s.config == config),
            "DARLT pipeline mixes immutable configurations",
        )?;
        need(
            specs.iter().all(|s| s.selected_span.is_none()),
            "standalone fine-span jobs are not pipeline tasks",
        )?;
        if let std::collections::btree_map::Entry::Vacant(entry) = self.fixtures.entry(config) {
            entry.insert(Arc::new(Fixture::new(config)?));
        }
        let fixture = self.fixtures[&config].clone();
        let assets = self
            .pipeline_assets
            .entry(config)
            .or_insert_with(|| {
                Rc::new(RefCell::new(PipelineAssets {
                    wallet: fixture.wallet.clone(),
                    sequence: 0,
                    retained_setup: None,
                    retained_keygen: None,
                    spent_baseline: None,
                    accepted_children: BTreeMap::new(),
                    hot_children: BTreeMap::new(),
                    provision_installed: BTreeMap::new(),
                }))
            })
            .clone();
        let sequence = {
            let mut a = assets
                .try_borrow_mut()
                .map_err(|_| "DARLT pipeline slot still active")?;
            a.sequence += 1;
            a.sequence
        };
        Ok(Box::new(move |clock| {
            run_pipeline(fixture, assets, specs, trial, sequence, clock)
        }))
    }
}

fn pipeline_capture<T>(
    clock: &mut BoundaryClock,
    ids: &[String],
    action: impl FnOnce() -> Result<T>,
) -> Result<T> {
    if let Some(first) = ids.first() {
        let out = clock.capture(first, |c| c.measure(action))?;
        for alias in &ids[1..] {
            clock.capture_alias(alias, first, "whole")?;
        }
        Ok(out)
    } else {
        action()
    }
}
fn matching_ids(specs: &[Spec], matches: impl Fn(&Task) -> bool) -> Vec<String> {
    specs
        .iter()
        .filter(|s| matches(&s.task))
        .map(|s| s.job.id.clone())
        .collect()
}
fn pipeline_seed(config: Config, trial: u64, sequence: u64) -> u64 {
    let mut hash = Sha256::new();
    hash.update(b"DARLT/pipeline/request-seed");
    hash.update(config.workload().to_string());
    hash.update(trial.to_be_bytes());
    hash.update(sequence.to_be_bytes());
    u64::from_be_bytes(hash.finalize()[..8].try_into().unwrap())
}
fn pipeline_evidence(
    f: &Fixture,
    holder: &Holder,
    context: &[u8],
    rng: &mut StdRng,
) -> Result<Token> {
    let mut holder = holder.clone();
    holder.scope_opening(&f.pp, 0)?;
    let prepared = spend::prepare_spend_installed(
        f.agent.runtime_view(),
        &f.ip,
        &mut holder,
        &[0],
        &f.config.policy(),
        rng,
    )?;
    spend::finish_spend(f.agent.runtime_view(), &f.ip, prepared, context, rng)
}

fn run_pipeline(
    f: Arc<Fixture>,
    assets: Rc<RefCell<PipelineAssets>>,
    specs: Vec<Spec>,
    trial: u64,
    sequence: u64,
    clock: &mut BoundaryClock,
) -> Result<Value> {
    let mut assets = assets
        .try_borrow_mut()
        .map_err(|_| "DARLT configuration already has a live slot")?;
    let mut rng = StdRng::seed_from_u64(pipeline_seed(f.config, trial, sequence));
    let mut verifier_rng = batch_rng()?;
    let mut wallet = assets.wallet.clone();
    let mut observations = BTreeMap::<String, Value>::new();
    let mut request_digests = vec![];
    let mut verification_schedules = BTreeMap::new();
    let mut base = b"req".to_vec();
    base.extend(sequence.to_be_bytes());
    clock.set_darlt_details(false);
    let setup = matching_ids(&specs, |t| matches!(t, Task::Setup));
    if !setup.is_empty() {
        let c = f.config;
        let pp = pipeline_capture(clock, &setup, || {
            PublicParameters::setup(c.n, c.s, 64, c.del, c.private, b"sampler/setup", &mut rng)
        })?;
        let value = json!({"actual_parameter_bytes":pp.encode().len(),"degree":pp.srs.degree,"retained_actual_output":true});
        for id in setup {
            observations.insert(id, value.clone());
        }
        assets.retained_setup = Some(pp);
    }
    let keys = matching_ids(&specs, |t| matches!(t, Task::Keygen));
    if !keys.is_empty() {
        let out = pipeline_capture(clock, &keys, || protocol::keygen(&f.pp, &mut rng))?;
        protocol::install(&f.pp, &out.0)?;
        for id in keys {
            observations.insert(
                id,
                json!({"issuer_public_bytes":out.0.encode().len(),"retained_actual_output":true}),
            );
        }
        assets.retained_keygen = Some(out);
    }
    let issue_req = matching_ids(&specs, |t| matches!(t, Task::IssueRequest));
    let issue_issuer = matching_ids(&specs, |t| matches!(t, Task::IssueIssuer));
    let issue_accept = matching_ids(&specs, |t| matches!(t, Task::IssueAccept));
    let issuance_active =
        !issue_req.is_empty() || !issue_issuer.is_empty() || !issue_accept.is_empty();
    if issuance_active {
        let (attrs, private) = f.config.attributes();
        let (q, sec, qb) = pipeline_capture(clock, &issue_req, || {
            let (q, sec) =
                protocol::prepare_request(&f.pp, &f.ip, S::from(91), &attrs, &private, &mut rng)?;
            let bytes = q.encode();
            Ok((q, sec, bytes))
        })?;
        let (response, rb) = pipeline_capture(clock, &issue_issuer, || {
            let parsed = protocol::ReceivedIssueRequest::decode(&f.pp, &qb)?;
            let response =
                protocol::issue_received_installed(&f.pp, &f.ip, &f.sk, &parsed, 1, &mut rng)?;
            let wire = response.encode();
            Ok((response, wire))
        })?;
        wallet = pipeline_capture(clock, &issue_accept, || {
            let parsed = protocol::ReceivedIssueResponse::decode(&f.pp, &rb)?;
            protocol::accept_received_installed(&f.pp, &f.ip, &q, &sec, &parsed, &mut verifier_rng)
        })?;
        request_digests.push(format!("{:x}", Sha256::digest(&qb)));
        for id in issue_req {
            observations.insert(id,json!({"request_bytes":qb.len(),"actual_request_digest":request_digests.last(),"output_consumed_by_issuer":true}));
        }
        for id in issue_issuer {
            observations.insert(id,json!({"response_bytes":rb.len(),"actual_issuer_calls":1,"output_consumed_by_acceptance":true}));
        }
        for id in issue_accept {
            observations.insert(id,json!({"accepted_parent":format!("{:x}",Sha256::digest(wallet.id())),"response_bytes":rb.len(),"output_retained_as_wallet_asset":true}));
        }
        drop(response);
        assets.wallet = wallet.clone();
        assets.accepted_children.clear();
        assets.hot_children.clear();
    }
    let mut points = BTreeSet::new();
    let mut scopes = BTreeSet::new();
    for spec in &specs {
        match spec.task {
            Task::Prepare(k) | Task::Online(k) | Task::Encode(k) | Task::State(k) => {
                points.insert((k, false));
            }
            Task::Verify { k, ablation, .. } | Task::Inclusive { k, ablation, .. } => {
                points.insert((k, ablation));
            }
            Task::DelegateSend { gamma, hot } => {
                scopes.insert((gamma, hot));
            }
            Task::DelegateReceive(gamma) => {
                scopes.insert((gamma, false));
            }
            Task::Scope(_) | Task::DelegateRequest => {
                scopes.insert((1, false));
            }
            Task::Decode(_) | Task::DecodeAblation(_) => {
                return Err("standalone DARLT decoder is not a pipeline workload".into())
            }
            _ => {}
        }
    }
    for (k, _) in &points {
        need(
            [1, 2, 4, 8, 16, 32, 64, 96, 128].contains(k),
            "noncanonical DARLT pipeline k",
        )?;
        need(*k <= f.pp.n, "pipeline quota exceeds issued credential")?;
        scopes.insert((k.div_ceil(f.pp.s), false));
    }
    let needs_state = specs
        .iter()
        .any(|s| matches!(s.task, Task::Inclusive { .. } | Task::State(_)));
    if needs_state && assets.spent_baseline.is_none() {
        let adapter = crate::adapters::ReceivedDarlt::new(&f.context);
        assets.spent_baseline = Some(
            SpentStore::with_preexisting_records(10000, adapter.namespace(), 48)
                .map_err(err)?
                .snapshot()
                .map_err(err)?,
        );
    }
    let mut holders = std::mem::take(&mut assets.accepted_children);
    let mut hot_children = std::mem::take(&mut assets.hot_children);
    let history = assets.spent_baseline.as_ref();
    let mut core_delegation_flows = 0;
    let core_token_batches = points.len();
    let request_ids = matching_ids(&specs, |t| matches!(t, Task::DelegateRequest));
    let mut recipient_request = None;
    for (gamma, hot) in scopes {
        let send = matching_ids(
            &specs,
            |t| matches!(t,Task::DelegateSend{gamma:g,hot:h} if *g==gamma&&*h==hot),
        );
        let receive_ids = if hot {
            vec![]
        } else {
            matching_ids(
                &specs,
                |t| matches!(t,Task::DelegateReceive(g) if *g==gamma),
            )
        };
        if send.is_empty()
            && receive_ids.is_empty()
            && request_ids.is_empty()
            && holders.contains_key(&gamma)
        {
            continue;
        }
        core_delegation_flows += 1;
        if recipient_request.is_none() {
            let wire = pipeline_capture(clock, &request_ids, || {
                let request = f
                    .context
                    .delegation_request(&base, S::from(111), &mut rng)?;
                Ok(request.encode())
            })?;
            for id in &request_ids {
                observations.insert(id.clone(),json!({"request_bytes":wire.len(),"actual_request_digest":format!("{:x}",Sha256::digest(&wire)),"output_reused_for_delegation":true}));
            }
            recipient_request = Some(wire);
        }
        let c = f.context.fresh_holder_context();
        let mut world = wallet.clone();
        if hot {
            for b in 0..gamma {
                world.parent_opening(&f.pp, b)?;
            }
        }
        need(
            gamma <= f.pp.w,
            "pipeline delegation scope exceeds pool count",
        )?;
        let qb = recipient_request
            .as_ref()
            .ok_or("pipeline recipient request missing")?;
        let before = world.parent_opening_cache_len();
        let (delivery, wire) = pipeline_capture(clock, &send, || {
            let request = protocol::ReceivedRecipientRequest::decode(f.pp.id, qb)?;
            let d = c.delegate_received(
                &mut world,
                &request,
                &(0..gamma).collect::<Vec<_>>(),
                &vec![true; f.pp.k_del],
                &mut rng,
            )?;
            let bytes = d.delivery.encode();
            Ok((d, bytes))
        })?;
        let holder = pipeline_capture(clock, &receive_ids, || {
            receive(&f, &delivery, &wire, S::from(111), &mut verifier_rng)
        })?;
        let digest = format!("{:x}", Sha256::digest(&wire));
        request_digests.push(digest.clone());
        for id in send {
            observations.insert(id,json!({"gamma":gamma,"cache_before":before,"cache_after":world.parent_opening_cache_len(),"delivery_bytes":wire.len(),"recipient_consumed_same_delivery":true,"delivery_digest":digest}));
        }
        for id in receive_ids {
            observations.insert(id,json!({"gamma":gamma,"delivery_bytes":wire.len(),"delivery_digest":digest,"quota":gamma*f.pp.s}));
        }
        if !hot || !holders.contains_key(&gamma) {
            holders.insert(gamma, holder);
            hot_children.remove(&gamma);
        }
    }
    for hot in [false, true] {
        let scope = matching_ids(&specs, |t| matches!(t,Task::Scope(h) if *h==hot));
        if scope.is_empty() {
            continue;
        }
        let mut holder = if hot {
            hot_children
                .get(&1)
                .or_else(|| holders.get(&1))
                .ok_or("scope child missing")?
                .clone()
        } else {
            let mut holder = holders.get(&1).ok_or("scope child missing")?.clone();
            holder.scope_openings.clear();
            holder
        };
        if hot {
            holder.scope_opening(&f.pp, 0)?;
        }
        let before = holder.scope_opening_cache_len();
        pipeline_capture(clock, &scope, || holder.scope_opening(&f.pp, 0))?;
        for id in scope {
            observations.insert(id,json!({"cache_before":before,"cache_after":holder.scope_opening_cache_len(),"consumed_current_delegated_child":true}));
        }
        hot_children.insert(1, holder);
    }
    for gamma in points
        .iter()
        .map(|(k, _)| k.div_ceil(f.pp.s))
        .collect::<BTreeSet<_>>()
    {
        if let std::collections::btree_map::Entry::Vacant(entry) = hot_children.entry(gamma) {
            let mut holder = holders
                .get(&gamma)
                .ok_or("pipeline child output missing")?
                .clone();
            for b in 0..gamma {
                holder.scope_opening(&f.pp, b)?;
            }
            entry.insert(holder);
        }
    }
    let mut reference_k1 = None;
    for (k, ablation) in points {
        let mut holder = hot_children
            .get(&k.div_ceil(f.pp.s))
            .ok_or("pipeline child output missing")?
            .clone();
        let prep = if ablation {
            vec![]
        } else {
            matching_ids(&specs, |t| matches!(t,Task::Prepare(n) if *n==k))
        };
        let online = if ablation {
            vec![]
        } else {
            matching_ids(&specs, |t| matches!(t,Task::Online(n) if *n==k))
        };
        let detailed = f.config == Config::default() && k == 16 && !ablation;
        let mut context = sequence.to_be_bytes().to_vec();
        context.extend((k as u16).to_be_bytes());
        context.push(u8::from(ablation));
        let policy = f.config.policy();
        let positions = (0..k).collect::<Vec<_>>();
        let mut tokens = vec![];
        clock.set_darlt_details(detailed);
        for chunk in positions.chunks(if ablation { 1 } else { 64 }) {
            let prepared = pipeline_capture(clock, &prep, || {
                spend::prepare_spend_installed(
                    f.agent.runtime_view(),
                    &f.ip,
                    &mut holder,
                    chunk,
                    &policy,
                    &mut rng,
                )
            })?;
            let token = pipeline_capture(clock, &online, || {
                spend::finish_spend(f.agent.runtime_view(), &f.ip, prepared, &context, &mut rng)
            })?;
            tokens.push(token);
        }
        clock.set_darlt_details(false);
        let encode = if ablation {
            vec![]
        } else {
            matching_ids(&specs, |t| matches!(t,Task::Encode(n) if *n==k))
        };
        let wire = pipeline_capture(clock, &encode, || {
            Ok(tokens.iter().map(Token::wire_encode).collect::<Vec<_>>())
        })?;
        let result = token_result(&tokens);
        if k == 1 && !ablation {
            reference_k1 = tokens.first().cloned();
        }
        request_digests.push(
            result["wire_sha256"]
                .as_str()
                .ok_or("token digest missing")?
                .to_string(),
        );
        for id in prep.iter().chain(&online).chain(&encode) {
            observations.insert(id.clone(), result.clone());
        }
        let mut verification_profiles = [
            (Mode::Specification, false),
            (Mode::Randomized, true),
            (Mode::Randomized, false),
        ].into_iter().filter_map(|(mode,per_block)| {
            let included = matching_ids(
                &specs,
                |t| matches!(t,Task::Inclusive{k:n,ablation:a,mode:m,per_block:p} if *n==k&&*a==ablation&&*m==mode&&*p==per_block),
            );
            let crypto = matching_ids(
                &specs,
                |t| matches!(t,Task::Verify{k:n,ablation:a,mode:m,per_block:p} if *n==k&&*a==ablation&&*m==mode&&*p==per_block),
            );
            (!included.is_empty()||!crypto.is_empty()).then_some((mode,per_block,included,crypto))
        }).collect::<Vec<_>>();
        let rotation = if verification_profiles.is_empty() {
            0
        } else {
            (trial % verification_profiles.len() as u64) as usize
        };
        verification_profiles.rotate_left(rotation);
        verification_schedules.insert(format!("{}/k{k}",if ablation{"ablation"}else{"native"}),json!({"active_profile_count":verification_profiles.len(),"rotation":rotation,"rule":"filter active candidates, then rotate_left(trial % active_count)","execution_order":verification_profiles.iter().map(|(mode,per_block,_,_)|format!("{mode:?}/per_block={per_block}")).collect::<Vec<_>>()}));
        for (mode, per_block, included, crypto) in verification_profiles {
            clock.set_darlt_details(detailed && mode == Mode::Randomized && !per_block);
            if !included.is_empty() {
                let adapter = if per_block {
                    crate::adapters::ReceivedDarlt::per_block(&f.context)
                } else {
                    crate::adapters::ReceivedDarlt::new(&f.context)
                };
                let store =
                    SpentStore::from_snapshot(history.ok_or("pipeline state snapshot missing")?);
                let runtime_mode = if mode == Mode::Specification {
                    crate::batch_runtime::Mode::Specification
                } else {
                    crate::batch_runtime::Mode::Randomized
                };
                let accepted = pipeline_capture(clock, &included, || {
                    let received = decode_received(f.verifier.runtime_view(), &wire)?;
                    crate::batch_runtime::verify_and_record(
                        &adapter,
                        &received,
                        b"trial-request",
                        b"ok",
                        &store,
                        runtime_mode,
                        &mut verifier_rng,
                    )
                    .map_err(err)
                })?;
                need(
                    accepted.newly_registered == k && !accepted.replayed,
                    "pipeline registration mismatch",
                )?;
                need(
                    store.counts().map_err(err)? == (10001, 10000 + k),
                    "pipeline history/state width mismatch",
                )?;
                for id in &included {
                    let mut value = result.clone();
                    value["state_before"] = json!([10000, 10000]);
                    value["state_after"] = json!([10001, 10000 + k]);
                    value["received_input_reused_across_profiles"] = json!(true);
                    observations.insert(id.clone(), value);
                }
            }
            if !crypto.is_empty() {
                let ok = pipeline_capture(clock, &crypto, || {
                    verify_received(
                        f.verifier.runtime_view(),
                        &f.ip,
                        &wire,
                        mode,
                        per_block,
                        &mut verifier_rng,
                    )
                })?;
                need(ok, "pipeline optional crypto diagnosis rejected")?;
                for id in crypto {
                    observations.insert(id, result.clone());
                }
            }
        }
        clock.set_darlt_details(false);
        for spec in specs
            .iter()
            .filter(|s| matches!(s.task,Task::State(n) if n==k) && !ablation)
        {
            let adapter = crate::adapters::Darlt::new(&f.context);
            let ids = tokens
                .iter()
                .flat_map(Token::serials)
                .map(|s| Identifier::new(adapter.namespace(), &s).map_err(err))
                .collect::<Result<Vec<_>>>()?;
            let bound = crate::batch_runtime::bound_request(&adapter, &tokens, b"trial-request");
            let store =
                SpentStore::from_snapshot(history.ok_or("pipeline state snapshot missing")?);
            pipeline_capture(clock, std::slice::from_ref(&spec.job.id), || {
                store.record_checked(&bound, &ids, b"ok").map_err(err)
            })?;
            observations.insert(spec.job.id.clone(), result.clone());
        }
    }
    assets.accepted_children = holders;
    assets.hot_children = hot_children;
    let mut judge_inputs = BTreeMap::new();
    for double_use in [false, true] {
        if !specs
            .iter()
            .any(|s| matches!(s.task,Task::Judge{double_use:d,..} if d==double_use))
        {
            continue;
        }
        if let std::collections::btree_map::Entry::Vacant(entry) = assets.accepted_children.entry(1)
        {
            let (_, child) = f.child_from_wallet(&wallet, 1, true, &mut rng)?;
            entry.insert(child.holder);
        }
        let holder = &assets.accepted_children[&1];
        let mut context = sequence.to_be_bytes().to_vec();
        context.extend([b'J', b'A', u8::from(double_use)]);
        let a = if let Some(token) = &reference_k1 {
            token.clone()
        } else {
            pipeline_evidence(&f, holder, &context, &mut rng)?
        };
        context = sequence.to_be_bytes().to_vec();
        context.extend([b'J', b'B', u8::from(double_use)]);
        let b = if double_use {
            pipeline_evidence(&f, holder, &context, &mut rng)?
        } else {
            let (_, child) = f.child_from_wallet(&wallet, 1, true, &mut rng)?;
            pipeline_evidence(&f, &child.holder, &context, &mut rng)?
        };
        let expected_key = if double_use {
            G1::generator() * holder.ska
        } else {
            wallet.parent()[3]
        };
        judge_inputs.insert(double_use, (a, b, expected_key));
    }
    let mut pending = specs.iter().collect::<Vec<_>>();
    pending.sort_by_key(|s| match s.task {
        Task::Judge {
            double_use,
            mode,
            validated,
        } => (
            0,
            usize::from(double_use),
            ((usize::from(mode == Mode::Randomized) + 2 - (trial % 2) as usize) % 2)
                + 2 * usize::from(validated),
        ),
        _ => (1, 0, 0),
    });
    for spec in pending {
        if observations.contains_key(&spec.job.id) {
            continue;
        }
        if let Task::Judge {
            mode,
            validated,
            double_use,
        } = spec.task
        {
            let (a, b, expected) = judge_inputs
                .get(&double_use)
                .ok_or("judge input slot missing")?;
            if validated {
                need(
                    f.context.valid(a, Mode::Specification, &mut rng)
                        && f.context.valid(b, Mode::Specification, &mut rng),
                    "validated evidence producer rejected",
                )?;
            }
            let wire = [a.wire_encode(), b.wire_encode()];
            let result = pipeline_capture(clock, std::slice::from_ref(&spec.job.id), || {
                if validated {
                    spend::identify_validated(&f.pp, &f.ip, a, 0, b, 0)
                } else {
                    let received = decode_received(f.verifier.runtime_view(), &wire)?;
                    f.context.judge_received(
                        &received[0],
                        0,
                        &received[1],
                        0,
                        mode,
                        &mut verifier_rng,
                    )
                }
                .ok_or("pipeline Judge rejected".into())
            })?;
            let branch = if double_use {
                spend::Responsibility::DoubleUse
            } else {
                spend::Responsibility::DoubleAlloc
            };
            need(
                result == (branch, *expected),
                "pipeline Judge recovered wrong responsibility",
            )?;
            let digest = format!("{:x}", Sha256::digest(wire.concat()));
            request_digests.push(digest.clone());
            observations.insert(spec.job.id.clone(),json!({"responsibility":format!("{:?}",branch),"received_message_digest":digest,"same_evidence_across_profiles":true,"record_a_from_same_slot_online":reference_k1.is_some(),"native_valid_included":!validated}));
        } else if let Task::Provision { agents, issuer: _ } = spec.task {
            let system = matching_ids(
                &specs,
                |t| matches!(t,Task::Provision{agents:a,issuer:false} if *a==agents),
            );
            let issuer = matching_ids(
                &specs,
                |t| matches!(t,Task::Provision{agents:a,issuer:true} if *a==agents),
            );
            let source = system
                .first()
                .or_else(|| issuer.first())
                .ok_or("provision capture missing")?
                .clone();
            if let std::collections::btree_map::Entry::Vacant(entry) =
                assets.provision_installed.entry(agents)
            {
                entry.insert(provision_installations(&f, agents)?);
            }
            let installed = assets.provision_installed[&agents].clone();
            let retained = Rc::new(RefCell::new(None));
            let body = provision_action_with_assets(
                f.clone(),
                agents,
                system.is_empty(),
                StdRng::seed_from_u64(
                    pipeline_seed(f.config, trial, sequence).wrapping_add(agents as u64),
                ),
                installed,
                Some(retained.clone()),
            )?;
            let value = clock.capture(&source, |clock| {
                body(&mut SelectedClock { clock, span: None })
            })?;
            for id in system.iter().skip(1) {
                clock.capture_alias(id, &source, "whole")?;
            }
            if !system.is_empty() {
                for id in &issuer {
                    clock.capture_alias(id, &source, "provision.issuer")?;
                }
            } else {
                for id in issuer.iter().skip(1) {
                    clock.capture_alias(id, &source, "whole")?;
                }
            }
            if let Some(value) = retained.borrow_mut().take() {
                assets.wallet = value;
                assets.accepted_children.clear();
                assets.hot_children.clear();
            }
            for id in system.iter().chain(&issuer) {
                let mut output = value.clone();
                output["public_installation_asset_reused"] = json!(true);
                observations.insert(id.clone(), output);
            }
        } else {
            let body = prepare_action_for_wallet(
                f.clone(),
                spec.task.clone(),
                pipeline_seed(f.config, trial, sequence).wrapping_add(observations.len() as u64),
                wallet.clone(),
            )?;
            let value = clock.capture(&spec.job.id, |clock| {
                body(&mut SelectedClock { clock, span: None })
            })?;
            if let Some(digest) = value["received_message_digest"].as_str() {
                request_digests.push(digest.to_string());
            }
            observations.insert(spec.job.id.clone(), value);
        }
    }
    Ok(
        json!({"pipeline":true,"sample_trial":trial,"slot_sequence":sequence,"config":f.config.workload(),
        "actual_request_digests":request_digests,"job_results":observations,"wallet_asset_reused":!issuance_active,
        "core_actual_issuance_flows":usize::from(issuance_active),"core_actual_delegation_flows":core_delegation_flows,
        "core_generated_token_batches":core_token_batches,"independent_snapshot_worlds_per_k":true,
        "verification_profile_schedules":verification_schedules,
        "accepted_child_asset_slots":assets.accepted_children.len(),"hot_opening_asset_slots":assets.hot_children.len(),
        "session_intermediates_retained_between_samples":false,"retained_setup_outputs":usize::from(assets.retained_setup.is_some()),
        "retained_keygen_outputs":usize::from(assets.retained_keygen.is_some()),"formal_samples":0}),
    )
}

fn token_result(tokens: &[Token]) -> Value {
    let bytes: Vec<_> = tokens.iter().map(Token::wire_encode).collect();
    let mut hash = Sha256::new();
    for b in &bytes {
        hash.update((b.len() as u64).to_be_bytes());
        hash.update(b);
    }
    json!({"native_tokens":tokens.len(),"actual_units":tokens.iter().map(|t|t.units.len()).sum::<usize>(),
        "native_message_bytes":bytes.iter().map(Vec::len).sum::<usize>(),"wire_sha256":format!("{:x}",hash.finalize()),
        "block_units":tokens.iter().map(|t|t.units.len()).collect::<Vec<_>>(),"sigma_variables":tokens.iter().map(|t|t.proof.z.len()).collect::<Vec<_>>(),
        "range_bit_proofs":tokens.iter().map(|t|t.proof.bits.len()).collect::<Vec<_>>()})
}
#[cfg(test)]
fn make_tokens(
    f: &Fixture,
    k: usize,
    ablation: bool,
    context: &[u8],
    rng: &mut StdRng,
) -> Result<Vec<Token>> {
    make_tokens_for_wallet(f, &f.wallet, k, ablation, context, rng)
}
fn make_tokens_for_wallet(
    f: &Fixture,
    wallet: &Wallet,
    k: usize,
    ablation: bool,
    context: &[u8],
    rng: &mut StdRng,
) -> Result<Vec<Token>> {
    let (_, mut child) = f.child_from_wallet(wallet, k.div_ceil(f.pp.s), true, rng)?;
    let policy = f.config.policy();
    let positions = (0..k).collect::<Vec<_>>();
    let mut tokens = vec![];
    for chunk in positions.chunks(if ablation { 1 } else { 64 }) {
        let pp = f.agent.runtime_view();
        let p = spend::prepare_spend_installed(pp, &f.ip, &mut child.holder, chunk, &policy, rng)?;
        tokens.push(spend::finish_spend(pp, &f.ip, p, context, rng)?);
    }
    let wire = tokens.iter().map(Token::wire_encode).collect::<Vec<_>>();
    need(
        verify_received(
            f.verifier.runtime_view(),
            &f.ip,
            &wire,
            Mode::Specification,
            false,
            rng,
        )?,
        "native fixture tokens rejected",
    )?;
    Ok(tokens)
}
fn decode_received(pp: &PublicParameters, wire: &[Vec<u8>]) -> Result<Vec<ReceivedToken>> {
    let _received = instrumentation::span("receive.strict_decoding");
    need(!wire.is_empty(), "empty received DARLT batch")?;
    wire.iter()
        .map(|bytes| ReceivedToken::wire_decode(pp, bytes))
        .collect()
}
fn verify_received(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    wire: &[Vec<u8>],
    mode: Mode,
    per_block: bool,
    rng: &mut impl rand::RngCore,
) -> Result<bool> {
    // Fix the complete received batch in checked native objects before any
    // verifier algorithm or its independently sampled batching coins run.
    let tokens = decode_received(pp, wire)?;
    Ok(if per_block {
        tokens
            .iter()
            .all(|t| spend::valid_received_installed(pp, ip, t, mode, rng))
    } else {
        spend::valid_many_received_installed(pp, ip, &tokens, mode, rng)
    })
}
fn checked(f: &Fixture, tokens: &[Token], rng: &mut StdRng) -> Result<Value> {
    let wire = tokens.iter().map(Token::wire_encode).collect::<Vec<_>>();
    need(
        verify_received(
            f.verifier.runtime_view(),
            &f.ip,
            &wire,
            Mode::Specification,
            false,
            rng,
        )?,
        "DARLT measured result rejected",
    )?;
    let out = token_result(tokens);
    for t in tokens {
        need(
            Token::wire_decode(&f.pp, &t.wire_encode())?.wire_encode() == t.wire_encode(),
            "token codec mismatch",
        )?;
    }
    Ok(out)
}

fn prepare_action(f: Arc<Fixture>, task: Task, seed: u64) -> Result<Body> {
    let wallet = f.wallet.clone();
    prepare_action_for_wallet(f, task, seed, wallet)
}
fn prepare_action_for_wallet(
    f: Arc<Fixture>,
    task: Task,
    seed: u64,
    base_wallet: Wallet,
) -> Result<Body> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut verifier_rng = batch_rng()?;
    match task {
        Task::Setup => unreachable!(),
        Task::Keygen => Ok(Box::new(move |clock| {
            let (ip, _) = clock.measure(|| protocol::keygen(&f.pp, &mut rng))?;
            protocol::install(&f.pp, &ip)?;
            Ok(json!({"issuer_public_bytes":ip.encode().len()}))
        })),
        Task::Install(role) => {
            let p = RoleParameters::from_setup(&f.pp, role)?;
            let wire = p.encode();
            let manifest = p.manifest();
            let key = f.ip.encode();
            Ok(Box::new(move |clock| {
                let installed = clock.measure(|| {
                    let p = RoleParameters::decode(&wire, &manifest)?;
                    let key = decode_issuer(&key)?;
                    p.install_issuer(&key)?;
                    Ok((p, key))
                })?;
                Ok(
                    json!({"role":role.name(),"parameter_bytes":wire.len(),"issuer_public_bytes":key.len(),"dimensions":installed.0.dimensions(),"actual_key_proof_verified":true}),
                )
            }))
        }
        Task::IssueRequest => Ok(Box::new(move |clock| {
            let (attrs, private) = f.config.attributes();
            let (q, sec, wire) = clock.measure(|| {
                let (q, s) = protocol::prepare_request(
                    &f.pp,
                    &f.ip,
                    S::from(91),
                    &attrs,
                    &private,
                    &mut rng,
                )?;
                let b = q.encode();
                Ok((q, s, b))
            })?;
            let parsed = protocol::ReceivedIssueRequest::decode(&f.pp, &wire)?;
            let response =
                protocol::issue_received_installed(&f.pp, &f.ip, &f.sk, &parsed, 1, &mut rng)?;
            protocol::accept(&f.pp, &f.ip, &q, &sec, &response, &mut verifier_rng)?;
            Ok(
                json!({"request_bytes":wire.len(),"strict_roundtrip":parsed.request().encode()==wire}),
            )
        })),
        Task::IssueIssuer | Task::IssueAccept => {
            let (attrs, private) = f.config.attributes();
            let (q, sec) =
                protocol::prepare_request(&f.pp, &f.ip, S::from(91), &attrs, &private, &mut rng)?;
            let request = q.encode();
            if matches!(task, Task::IssueIssuer) {
                Ok(Box::new(move |clock| {
                    let (response, wire) = clock.measure(|| {
                        let q = protocol::ReceivedIssueRequest::decode(&f.pp, &request)?;
                        let r = protocol::issue_received_installed(
                            &f.pp, &f.ip, &f.sk, &q, 1, &mut rng,
                        )?;
                        let b = r.encode();
                        Ok((r, b))
                    })?;
                    let parsed = protocol::ReceivedIssueResponse::decode(&f.pp, &wire)?;
                    protocol::accept_received_installed(
                        &f.pp,
                        &f.ip,
                        &q,
                        &sec,
                        &parsed,
                        &mut verifier_rng,
                    )?;
                    Ok(
                        json!({"response_bytes":wire.len(),"actual_issuer_calls":1,"strict_roundtrip":response.encode()==parsed.response().encode()}),
                    )
                }))
            } else {
                let response = protocol::issue(&f.pp, &f.ip, &f.sk, &q, 1, &mut rng)?.encode();
                Ok(Box::new(move |clock| {
                    let w = clock.measure(|| {
                        let r = protocol::ReceivedIssueResponse::decode(&f.pp, &response)?;
                        protocol::accept_received_installed(
                            &f.pp,
                            &f.ip,
                            &q,
                            &sec,
                            &r,
                            &mut verifier_rng,
                        )
                    })?;
                    Ok(
                        json!({"accepted_parent":format!("{:x}",Sha256::digest(w.id())),"response_bytes":response.len(),"parent_opening_cache":w.parent_opening_cache_len()}),
                    )
                }))
            }
        }
        Task::Parent(hot) => {
            let mut wallet = base_wallet.clone();
            if hot {
                wallet.parent_opening(&f.pp, 0)?;
            }
            let before = wallet.parent_opening_cache_len();
            Ok(Box::new(move |clock| {
                clock.measure(|| wallet.parent_opening(&f.pp, 0))?;
                Ok(
                    json!({"cache_before":before,"cache_after":wallet.parent_opening_cache_len(),"actual_pools":1,"columns":2}),
                )
            }))
        }
        Task::DelegateRequest => Ok(Box::new(move |clock| {
            let (q, b) = clock.measure(|| {
                let q = f
                    .context
                    .delegation_request(b"trial-agent", S::from(111), &mut rng)?;
                let b = q.encode();
                Ok((q, b))
            })?;
            need(
                decode_recipient_request(&b)?.encode() == q.encode(),
                "recipient codec mismatch",
            )?;
            Ok(json!({"request_bytes":b.len()}))
        })),
        Task::DelegateSend { gamma, hot } | Task::SelfAllocate { gamma, hot } => {
            need(
                gamma <= f.pp.w,
                "delegation scope exceeds actual pool count",
            )?;
            let self_use = matches!(task, Task::SelfAllocate { .. });
            let c = f.context.fresh_holder_context();
            let mut wallet = base_wallet.clone();
            let pools = (0..gamma).collect::<Vec<_>>();
            if hot {
                for b in &pools {
                    wallet.parent_opening(&f.pp, *b)?;
                }
            }
            let before = wallet.parent_opening_cache_len();
            let request = c
                .delegation_request(b"trial-agent", S::from(111), &mut rng)?
                .encode();
            Ok(Box::new(move |clock| {
                if self_use {
                    let child = clock
                        .measure(|| c.self_derive(&mut wallet, b"trial-self", &pools, &mut rng))?;
                    need(child.holder.gamma() == pools, "local scope mismatch")?;
                    Ok(
                        json!({"gamma":gamma,"cache_before":before,"cache_after":wallet.parent_opening_cache_len(),"network_message_bytes":0,"child_registered":true}),
                    )
                } else {
                    let (delivery, wire) = clock.measure(|| {
                        let request =
                            protocol::ReceivedRecipientRequest::decode(f.pp.id, &request)?;
                        let d = c.delegate_received(
                            &mut wallet,
                            &request,
                            &pools,
                            &vec![true; f.pp.k_del],
                            &mut rng,
                        )?;
                        let bytes = d.delivery.encode();
                        Ok((d, bytes))
                    })?;
                    let holder = receive(&f, &delivery, &wire, S::from(111), &mut verifier_rng)?;
                    need(holder.gamma() == pools, "remote scope mismatch")?;
                    Ok(
                        json!({"gamma":gamma,"cache_before":before,"cache_after":wallet.parent_opening_cache_len(),"delivery_bytes":wire.len(),"recipient_full_checks":true}),
                    )
                }
            }))
        }
        Task::DelegateReceive(gamma) => {
            let c = f.context.fresh_holder_context();
            let mut wallet = base_wallet.clone();
            let q = c.delegation_request(b"trial-agent", S::from(111), &mut rng)?;
            let q = protocol::ReceivedRecipientRequest::decode(f.pp.id, &q.encode())?;
            let d = c.delegate_received(
                &mut wallet,
                &q,
                &(0..gamma).collect::<Vec<_>>(),
                &vec![true; f.pp.k_del],
                &mut rng,
            )?;
            let wire = d.delivery.encode();
            Ok(Box::new(move |clock| {
                let h =
                    clock.measure(|| receive(&f, &d, &wire, S::from(111), &mut verifier_rng))?;
                Ok(
                    json!({"gamma":h.gamma().len(),"quota":h.gamma().len()*f.pp.s,"delivery_bytes":wire.len(),"recipient_full_checks":true}),
                )
            }))
        }
        Task::Scope(hot) => {
            let (_, mut child) = f.child_from_wallet(&base_wallet, 1, hot, &mut rng)?;
            let before = child.holder.scope_opening_cache_len();
            Ok(Box::new(move |clock| {
                clock.measure(|| child.holder.scope_opening(&f.pp, 0))?;
                Ok(
                    json!({"cache_before":before,"cache_after":child.holder.scope_opening_cache_len(),"actual_pools":1}),
                )
            }))
        }
        Task::Prepare(k) | Task::Online(k) => {
            let online = matches!(task, Task::Online(_));
            let (_, mut child) =
                f.child_from_wallet(&base_wallet, k.div_ceil(f.pp.s), true, &mut rng)?;
            Ok(Box::new(move |clock| {
                let policy = f.config.policy();
                let positions = (0..k).collect::<Vec<_>>();
                let mut tokens = vec![];
                let mut shapes = vec![];
                for chunk in positions.chunks(64) {
                    let pp = f.agent.runtime_view();
                    let p = if online {
                        spend::prepare_spend_installed(
                            pp,
                            &f.ip,
                            &mut child.holder,
                            chunk,
                            &policy,
                            &mut rng,
                        )?
                    } else {
                        clock.measure(|| {
                            spend::prepare_spend_installed(
                                pp,
                                &f.ip,
                                &mut child.holder,
                                chunk,
                                &policy,
                                &mut rng,
                            )
                        })?
                    };
                    let shape = p.query_shape();
                    shapes.push(json!({"units":shape.units,"distinct_pools":shape.distinct_pools,"distinct_offsets":shape.distinct_offsets,"first_pool_offset":shape.first_pool_offset}));
                    let t = if online {
                        clock.measure(|| {
                            spend::finish_spend(pp, &f.ip, p, b"trial/scope", &mut rng)
                        })?
                    } else {
                        spend::finish_spend(pp, &f.ip, p, b"trial/scope", &mut rng)?
                    };
                    tokens.push(t);
                }
                let mut out = checked(&f, &tokens, &mut rng)?;
                out["actual_query_shapes"] = json!(shapes);
                Ok(out)
            }))
        }
        Task::Encode(k)
        | Task::Decode(k)
        | Task::DecodeAblation(k)
        | Task::Verify { k, .. }
        | Task::Inclusive { k, .. }
        | Task::State(k) => {
            let ablation = matches!(
                task,
                Task::Verify { ablation: true, .. }
                    | Task::Inclusive { ablation: true, .. }
                    | Task::DecodeAblation(_)
            );
            let tokens =
                make_tokens_for_wallet(&f, &base_wallet, k, ablation, b"trial/scope", &mut rng)?;
            let wire = tokens.iter().map(Token::wire_encode).collect::<Vec<_>>();
            Ok(Box::new(move |clock| {
                match task {
                    Task::Encode(_) => {
                        let b = clock.measure(|| {
                            Ok(tokens.iter().map(Token::wire_encode).collect::<Vec<_>>())
                        })?;
                        need(b == wire, "encoding changed native bytes")?;
                    }
                    Task::Decode(_) | Task::DecodeAblation(_) => {
                        let parsed =
                            clock.measure(|| decode_received(f.verifier.runtime_view(), &wire))?;
                        need(
                            parsed
                                .iter()
                                .map(ReceivedToken::wire_encode)
                                .collect::<Vec<_>>()
                                == wire,
                            "decoded native bytes differ",
                        )?;
                    }
                    Task::Verify {
                        mode, per_block, ..
                    } => {
                        let pp = f.verifier.runtime_view();
                        let ok = clock.measure(|| {
                            verify_received(pp, &f.ip, &wire, mode, per_block, &mut verifier_rng)
                        })?;
                        need(ok, "honest native verification rejected")?;
                    }
                    Task::Inclusive {
                        mode, per_block, ..
                    } => {
                        let adapter = if per_block {
                            crate::adapters::ReceivedDarlt::per_block(&f.context)
                        } else {
                            crate::adapters::ReceivedDarlt::new(&f.context)
                        };
                        let store =
                            SpentStore::with_preexisting_records(10000, adapter.namespace(), 48)
                                .map_err(err)?;
                        let mode = if mode == Mode::Specification {
                            crate::batch_runtime::Mode::Specification
                        } else {
                            crate::batch_runtime::Mode::Randomized
                        };
                        let result = clock.measure(|| {
                            let received = decode_received(f.verifier.runtime_view(), &wire)?;
                            crate::batch_runtime::verify_and_record(
                                &adapter,
                                &received,
                                b"trial-request",
                                b"ok",
                                &store,
                                mode,
                                &mut verifier_rng,
                            )
                            .map_err(err)
                        })?;
                        need(
                            result.newly_registered == k && !result.replayed,
                            "inclusive registration mismatch",
                        )?;
                        need(
                            store.counts().map_err(err)? == (10001, 10000 + k),
                            "inclusive store lost native units",
                        )?;
                    }
                    Task::State(_) => {
                        let adapter = crate::adapters::Darlt::new(&f.context);
                        let namespace = adapter.namespace();
                        let ids = tokens
                            .iter()
                            .flat_map(Token::serials)
                            .map(|s| Identifier::new(namespace, &s).map_err(err))
                            .collect::<Result<Vec<_>>>()?;
                        let actual_bound =
                            crate::batch_runtime::bound_request(&adapter, &tokens, b"fresh-state");
                        let store = SpentStore::with_preexisting_records(10000, namespace, 48)
                            .map_err(err)?;
                        let accepted = clock.measure(|| {
                            store
                                .record_checked(&actual_bound, &ids, b"ok")
                                .map_err(err)
                        })?;
                        need(
                            accepted.newly_registered == k && !accepted.replayed,
                            "atomic spend registration mismatch",
                        )?;
                        need(
                            store.counts().map_err(err)? == (10001, 10000 + k),
                            "standalone state lost native units",
                        )?;
                    }
                    _ => unreachable!(),
                }
                Ok(token_result(&tokens))
            }))
        }
        Task::Judge {
            mode,
            validated,
            double_use,
        } => {
            let (a, b) = if double_use {
                let (_, mut child) = f.child_from_wallet(&base_wallet, 1, true, &mut rng)?;
                let mut tokens = vec![];
                for context in [b"judge-A", b"judge-B"] {
                    let p = spend::prepare_spend_installed(
                        f.agent.runtime_view(),
                        &f.ip,
                        &mut child.holder,
                        &[0],
                        &f.config.policy(),
                        &mut rng,
                    )?;
                    let t =
                        spend::finish_spend(f.agent.runtime_view(), &f.ip, p, context, &mut rng)?;
                    checked(&f, std::slice::from_ref(&t), &mut rng)?;
                    tokens.push(t);
                }
                let b = tokens.pop().unwrap();
                let a = tokens.pop().unwrap();
                need(
                    a.units[0].aid == b.units[0].aid,
                    "double-use fixture changed authorization",
                )?;
                (a, b)
            } else {
                (
                    make_tokens_for_wallet(&f, &base_wallet, 1, false, b"judge-A", &mut rng)?
                        .remove(0),
                    make_tokens_for_wallet(&f, &base_wallet, 1, false, b"judge-B", &mut rng)?
                        .remove(0),
                )
            };
            let wire = [a.wire_encode(), b.wire_encode()];
            Ok(Box::new(move |clock| {
                let result = clock.measure(|| {
                    if validated {
                        spend::identify_validated(&f.pp, &f.ip, &a, 0, &b, 0)
                    } else {
                        let received = decode_received(f.verifier.runtime_view(), &wire)?;
                        f.context.judge_received(
                            &received[0],
                            0,
                            &received[1],
                            0,
                            mode,
                            &mut verifier_rng,
                        )
                    }
                    .ok_or("judge failed".into())
                })?;
                let expected_branch = if double_use {
                    spend::Responsibility::DoubleUse
                } else {
                    spend::Responsibility::DoubleAlloc
                };
                let expected_key =
                    crate::ops::mul(G1::generator(), S::from(if double_use { 111 } else { 91 }));
                need(
                    result.0 == expected_branch && result.1 == expected_key,
                    "Judge recovered wrong responsibility or key",
                )?;
                Ok(
                    json!({"responsibility":format!("{:?}",result.0),"public_key_bytes":result.1.to_compressed().len(),"native_valid_included":!validated,"received_message_digest":format!("{:x}",Sha256::digest(wire.concat()))}),
                )
            }))
        }
        Task::Metadata { full, bit } => {
            let token = if bit == 1 {
                make_tokens_for_wallet(&f, &base_wallet, 1, false, b"read-bit", &mut rng)?.remove(0)
            } else {
                let (attrs, private) = f.config.attributes();
                let (q, s) = protocol::prepare_request(
                    &f.pp,
                    &f.ip,
                    S::from(91),
                    &attrs,
                    &private,
                    &mut rng,
                )?;
                let r = protocol::issue(&f.pp, &f.ip, &f.sk, &q, bit, &mut rng)?;
                let mut w = protocol::accept(&f.pp, &f.ip, &q, &s, &r, &mut verifier_rng)?;
                let c = f.context.fresh_holder_context();
                let mut child = c.self_derive(&mut w, b"metadata-bit0", &[0], &mut rng)?;
                let p = spend::prepare_spend_installed(
                    &f.pp,
                    &f.ip,
                    &mut child.holder,
                    &[0],
                    &f.config.policy(),
                    &mut rng,
                )?;
                spend::finish_spend(&f.pp, &f.ip, p, b"read-bit", &mut rng)?
            };
            let reader = f.context.metadata_reader(f.sk.metadata_secrets)?;
            let wire = token.wire_encode();
            let verified_token = Token::wire_decode(f.verifier.runtime_view(), &wire)?;
            let record = f
                .context
                .verify_metadata_record(&verified_token, Mode::Randomized, &mut verifier_rng)
                .ok_or("metadata record rejected")?;
            Ok(Box::new(move |clock| {
                let b = clock.measure(|| {
                    if full {
                        let received =
                            ReceivedToken::wire_decode(f.verifier.runtime_view(), &wire)?;
                        f.context.read_bit_received(
                            &received,
                            &f.sk.metadata_secrets,
                            Mode::Randomized,
                            &mut verifier_rng,
                        )
                    } else {
                        reader.read_validated(&record)
                    }
                    .ok_or("metadata bit missing".into())
                })?;
                need(b == bit, "wrong hidden bit")?;
                Ok(
                    json!({"bit":b,"native_valid_included":full,"already_verified_immutable_record":!full,"received_message_digest":format!("{:x}",Sha256::digest(&wire))}),
                )
            }))
        }
        Task::CrossChild => {
            let c = f.context.fresh_holder_context();
            let mut wallet = base_wallet.clone();
            let mut a = c.self_derive(&mut wallet, b"cross-A", &[0], &mut rng)?;
            let b = c.self_derive(&mut wallet, b"cross-B", &[1], &mut rng)?;
            let prior = c.spend_block(
                &mut a,
                &(0..15).collect::<Vec<_>>(),
                &f.config.policy(),
                b"cross-prior-context",
                b"cross-prior-request",
                &mut rng,
            )?;
            checked(&f, std::slice::from_ref(&prior), &mut rng)?;
            let requests = vec![(a.id, vec![15]), (b.id, (16..32).collect())];
            let mut children = [a, b];
            Ok(Box::new(move |clock| {
                let tokens = clock.measure(|| {
                    c.spend_chunks(
                        &mut children,
                        requests,
                        &f.config.policy(),
                        b"cross-child-context",
                        b"cross-child-request",
                        &mut rng,
                    )
                })?;
                let mut amounts = tokens.iter().map(|t| t.units.len()).collect::<Vec<_>>();
                amounts.sort();
                need(amounts == [1, 16], "cross-child grouping changed")?;
                let mut out = checked(&f, &tokens, &mut rng)?;
                out["actual_children"] = json!(2);
                out["prior_units_actually_spent"] = json!(15);
                Ok(out)
            }))
        }
        Task::PartialPool => {
            let (c, mut child) = f.child_from_wallet(&base_wallet, 2, true, &mut rng)?;
            let policy = f.config.policy();
            let prior = c.spend_block(
                &mut child,
                &(0..15).collect::<Vec<_>>(),
                &policy,
                b"prior-pool-context",
                b"prior-pool-request",
                &mut rng,
            )?;
            checked(&f, std::slice::from_ref(&prior), &mut rng)?;
            let positions =
                spend::select_sequential_units(&f.pp, &child.holder, &(0..15).collect(), 16)?;
            let shape = spend::query_shape(&f.pp, &positions)?;
            need(
                shape.distinct_pools == 2 && shape.first_pool_offset == 15,
                "partial-pool native query shape mismatch",
            )?;
            Ok(Box::new(move |clock| {
                let token = clock.measure(|| {
                    c.spend_block(
                        &mut child,
                        &positions,
                        &policy,
                        b"partial-pool-context",
                        b"partial-pool-request",
                        &mut rng,
                    )
                })?;
                let mut out = checked(&f, &[token], &mut rng)?;
                out["actual_query_shape"] = json!({"distinct_pools":shape.distinct_pools,"distinct_offsets":shape.distinct_offsets,"first_pool_offset":shape.first_pool_offset,"prior_units_actually_spent":15});
                Ok(out)
            }))
        }
        Task::Provision { agents, issuer } => provision_action(f, agents, issuer, rng),
    }
}

fn receive(f: &Fixture, d: &Delegation, bytes: &[u8], key: S, rng: &mut StdRng) -> Result<Holder> {
    let parsed = protocol::ReceivedDelivery::decode(f.agent.runtime_view(), bytes)?;
    let holder = protocol::complete_received_installed(
        f.agent.runtime_view(),
        &f.ip,
        &parsed,
        key,
        None,
        Mode::Randomized,
        rng,
    )?;
    let store = HolderStore::new();
    store
        .register_parent(
            d.parent,
            crate::darlt::context::key_id(holder.parent[3]),
            f.pp.w,
            f.pp.s,
        )
        .map_err(err)?;
    store
        .receive_child(
            d.parent,
            d.child,
            crate::darlt::context::key_id(crate::ops::mul(G1::generator(), key)),
            holder.gamma(),
        )
        .map_err(err)?;
    Ok(holder)
}

fn provision_action(
    f: Arc<Fixture>,
    agents: usize,
    issuer_only: bool,
    rng: StdRng,
) -> Result<Body> {
    let installed = provision_installations(&f, agents)?;
    provision_action_with_assets(f, agents, issuer_only, rng, installed, None)
}
fn provision_installations(f: &Fixture, agents: usize) -> Result<Rc<Vec<RoleParameters>>> {
    // Every agent actually receives and installs its own public packet outside
    // the period configuration ledger. The separately scheduled install jobs
    // expose this cost; this loop does not borrow another participant's cache.
    let packet = f.agent.encode();
    let key = f.ip.encode();
    let manifest = f.agent.manifest();
    let mut installed = vec![];
    for _ in 0..agents {
        let p = RoleParameters::decode(&packet, &manifest)?;
        let ip = decode_issuer(&key)?;
        p.install_issuer(&ip)?;
        installed.push(p);
    }
    Ok(Rc::new(installed))
}
fn provision_action_with_assets(
    f: Arc<Fixture>,
    agents: usize,
    issuer_only: bool,
    mut rng: StdRng,
    installed: Rc<Vec<RoleParameters>>,
    retained: Option<Rc<RefCell<Option<Wallet>>>>,
) -> Result<Body> {
    let (attrs, private) = f.config.attributes();
    let mut verifier_rng = batch_rng()?;
    if issuer_only {
        let (q, sec) =
            protocol::prepare_request(&f.pp, &f.ip, S::from(91), &attrs, &private, &mut rng)?;
        let wire = q.encode();
        return Ok(Box::new(move |clock| {
            let (_response, bytes) = clock.measure(|| {
                let parsed = protocol::ReceivedIssueRequest::decode(&f.pp, &wire)?;
                let r =
                    protocol::issue_received_installed(&f.pp, &f.ip, &f.sk, &parsed, 1, &mut rng)?;
                let b = r.encode();
                Ok((r, b))
            })?;
            let received = protocol::ReceivedIssueResponse::decode(&f.pp, &bytes)?;
            let accepted = protocol::accept_received_installed(
                &f.pp,
                &f.ip,
                &q,
                &sec,
                &received,
                &mut verifier_rng,
            )?;
            if let Some(retained) = &retained {
                *retained.borrow_mut() = Some(accepted);
            }
            Ok(
                json!({"agents":agents,"actual_issuer_calls":1,"actual_delegation_calls":0,"actual_request_digest":format!("{:x}",Sha256::digest(&wire)),"response_bytes":bytes.len(),"public_install_packets":agents,"public_install_outside_account":true}),
            )
        }));
    }
    let c = f.context.fresh_holder_context();
    let keys = (0..agents)
        .map(|i| S::from(111 + i as u64))
        .collect::<Vec<_>>();
    Ok(Box::new(move |clock| {
        let output = clock.measure(|| {
            let (q, sec) =
                protocol::prepare_request(&f.pp, &f.ip, S::from(91), &attrs, &private, &mut rng)?;
            let qb = q.encode();
            let rb = {
                let _issuer = instrumentation::span("provision.issuer");
                let q2 = protocol::ReceivedIssueRequest::decode(&f.pp, &qb)?;
                let response =
                    protocol::issue_received_installed(&f.pp, &f.ip, &f.sk, &q2, 1, &mut rng)?;
                response.encode()
            };
            let r2 = protocol::ReceivedIssueResponse::decode(&f.pp, &rb)?;
            let mut wallet = protocol::accept_received_installed(
                &f.pp,
                &f.ip,
                &q,
                &sec,
                &r2,
                &mut verifier_rng,
            )?;
            let mut bytes = qb.len() + rb.len();
            let mut quotas = vec![];
            let mut allpools = BTreeSet::new();
            let mut stores = vec![];
            let mut holders = vec![];
            for (i, (key, p)) in keys.iter().zip(installed.iter()).enumerate() {
                let gamma = (i * (64 / agents)..(i + 1) * (64 / agents)).collect::<Vec<_>>();
                for b in &gamma {
                    need(allpools.insert(*b), "overlapping agent pools")?;
                    wallet.parent_opening(&f.pp, *b)?;
                }
                let request = spseq_fc::request_installed(
                    &f.pp.id,
                    &f.ip.encode(),
                    &(i as u64).to_be_bytes(),
                    *key,
                    &mut rng,
                )?;
                let qb = request.encode();
                bytes += qb.len();
                let q = protocol::ReceivedRecipientRequest::decode(f.pp.id, &qb)?;
                let d = c.delegate_received(
                    &mut wallet,
                    &q,
                    &gamma,
                    &vec![true; f.pp.k_del],
                    &mut rng,
                )?;
                let db = d.delivery.encode();
                bytes += db.len();
                let parsed = protocol::ReceivedDelivery::decode(p.runtime_view(), &db)?;
                let holder = protocol::complete_received_installed(
                    p.runtime_view(),
                    &f.ip,
                    &parsed,
                    *key,
                    None,
                    Mode::Randomized,
                    &mut verifier_rng,
                )?;
                let state = HolderStore::new();
                state
                    .register_parent(
                        d.parent,
                        crate::darlt::context::key_id(holder.parent[3]),
                        f.pp.w,
                        f.pp.s,
                    )
                    .map_err(err)?;
                state
                    .receive_child(
                        d.parent,
                        d.child,
                        crate::darlt::context::key_id(crate::ops::mul(G1::generator(), *key)),
                        holder.gamma(),
                    )
                    .map_err(err)?;
                quotas.push(holder.gamma().len() * f.pp.s);
                stores.push(state);
                holders.push(holder);
            }
            need(
                allpools.len() == 64
                    && quotas.iter().all(|q| *q == 1024 / agents)
                    && quotas.iter().sum::<usize>() == 1024,
                "equal-budget configuration mismatch",
            )?;
            Ok((
                bytes,
                quotas,
                wallet.parent_opening_cache_len(),
                holders,
                stores,
                wallet,
                qb,
            ))
        })?;
        if let Some(retained) = &retained {
            let mut accepted = output.5;
            accepted.openings.clear();
            *retained.borrow_mut() = Some(accepted);
        }
        Ok(
            json!({"agents":agents,"total_quota":1024,"actual_agent_quotas":output.1,"actual_cold_parent_pools":output.2,"actual_issuer_calls":1,"actual_delegation_calls":agents,"actual_request_digest":format!("{:x}",Sha256::digest(&output.6)),"native_message_wire_bytes":output.0,"allocated_pools_pairwise_disjoint":true,"public_install_packets":agents,"public_install_outside_account":true,"first_scope_opening_outside_account":true,"setup_keygen_outside_account":true}),
        )
    }))
}

// The existing encoders define these formats. Decoders below accept only
// canonical scalar/point encodings and exact installed-schema dimensions.
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.at.checked_add(n).ok_or("wire length overflow")?;
        let out = self
            .bytes
            .get(self.at..end)
            .ok_or("truncated native message")?;
        self.at = end;
        Ok(out)
    }
    fn number(&mut self) -> Result<usize> {
        usize::try_from(u64::from_be_bytes(self.take(8)?.try_into().unwrap())).map_err(err)
    }
    fn frame(&mut self) -> Result<&'a [u8]> {
        let n = self.number()?;
        self.take(n)
    }
    fn fr(&mut self) -> Result<S> {
        Option::<S>::from(S::from_bytes_be(&self.take(32)?.try_into().unwrap()))
            .ok_or("noncanonical native scalar".into())
    }
    fn g1(&mut self) -> Result<G1> {
        let _span = instrumentation::span("point_decode_and_subgroup");
        Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed(
            &self.take(48)?.try_into().unwrap(),
        ))
        .map(G1::from)
        .ok_or("invalid native G1 encoding/subgroup".into())
    }
    fn g2(&mut self) -> Result<G2> {
        let _span = instrumentation::span("point_decode_and_subgroup");
        Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed(
            &self.take(96)?.try_into().unwrap(),
        ))
        .map(G2::from)
        .ok_or("invalid native G2 encoding/subgroup".into())
    }
    #[cfg(test)]
    fn frs(&mut self, n: usize) -> Result<Vec<S>> {
        need(self.number()? == n, "wrong native scalar vector dimension")?;
        (0..n).map(|_| self.fr()).collect()
    }
    fn g1s(&mut self, n: usize) -> Result<Vec<G1>> {
        need(self.number()? == n, "wrong native G1 vector dimension")?;
        (0..n).map(|_| self.g1()).collect()
    }
    fn end(self) -> Result<()> {
        need(self.at == self.bytes.len(), "trailing native message bytes")
    }
}
fn decode_issuer(bytes: &[u8]) -> Result<IssuerPublic> {
    let _span = instrumentation::span("strict_decoding");
    let mut r = Reader::new(bytes);
    need(r.number()? == 9, "issuer VK dimension")?;
    let vk = (0..9).map(|_| r.g2()).collect::<Result<_>>()?;
    let metadata = r.g1s(2)?;
    let key_proof = sigma::Proof::decode(r.frame()?, 11, 0)?;
    r.end()?;
    Ok(IssuerPublic {
        vk,
        metadata_keys: [metadata[0], metadata[1]],
        key_proof,
    })
}
#[cfg(test)]
fn decode_request(pp: &PublicParameters, bytes: &[u8]) -> Result<protocol::IssueRequest> {
    let _span = instrumentation::span("strict_decoding");
    let mut r = Reader::new(bytes);
    let pku = r.g1()?;
    let q = [r.g1()?, r.g1()?];
    let cdel = r.g1()?;
    let cprv = r.g1()?;
    let mdel = r.frs(pp.k_del)?;
    let mprv = r.frs(pp.k_prv)?;
    let proof = sigma::Proof::decode(r.frame()?, 1 + 2 * (pp.w + 1) + 2, 0)?;
    r.end()?;
    Ok(protocol::IssueRequest {
        pku,
        q,
        cdel,
        cprv,
        mdel,
        mprv,
        proof,
    })
}
#[cfg(test)]
fn decode_response(pp: &PublicParameters, bytes: &[u8]) -> Result<protocol::IssueResponse> {
    let _span = instrumentation::span("strict_decoding");
    let mut r = Reader::new(bytes);
    let shares = [r.frs(pp.w)?, r.frs(pp.w)?];
    let e = r.g1()?;
    let signature = spseq_fc::Sig {
        z: r.g1()?,
        y: r.g1()?,
        yhat: r.g2()?,
    };
    let mut d = Reader::new(r.frame()?);
    let base = spseq_fc::Dk {
        k0: d.g1()?,
        ka: d.g1()?,
        attrs: d.g1s(pp.k_del)?,
        pools: d.g1s(pp.w)?,
    };
    let kz = [d.g1()?, d.g1()?];
    d.end()?;
    let metadata_proof =
        crate::metadata::MetadataProof::from_bytes(r.take(crate::metadata::PROOF_PAYLOAD_BYTES)?)
            .map_err(|e| format!("{e:?}"))?;
    r.end()?;
    Ok(protocol::IssueResponse {
        shares,
        e,
        signature,
        dk: protocol::DerivationKey { base, kz },
        metadata_proof,
    })
}
fn decode_recipient_request(bytes: &[u8]) -> Result<spseq_fc::Request> {
    let _span = instrumentation::span("strict_decoding");
    let mut r = Reader::new(bytes);
    let sid = r.frame()?.to_vec();
    let pka = r.g1()?;
    let a = r.g1()?;
    let z = r.fr()?;
    r.end()?;
    Ok(spseq_fc::Request {
        sid,
        pka,
        proof: spseq_fc::Schnorr { a, z },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn test_pipeline(specs: Vec<Spec>) -> Factory {
        Factory {
            specs,
            fixtures: BTreeMap::new(),
            pipeline_assets: BTreeMap::new(),
        }
    }
    fn run_clock_free_pipeline(
        factory: &mut Factory,
        ids: &[String],
        trial: u64,
    ) -> (Value, BTreeMap<String, Value>) {
        let action = factory.prepare_pipeline(ids, trial).unwrap();
        let mut clock = BoundaryClock::new(crate::experiment::RunMode::ClockFree, None).unwrap();
        let result = action(&mut clock).unwrap();
        assert!(clock
            .observations()
            .values()
            .all(|v| v["ok"] == true && v["elapsed_ns"].is_null()));
        (result, clock.observations().clone())
    }
    #[test]
    fn pipeline_uses_real_upstream_outputs_and_distinct_complete_sample_requests() {
        let c = Config::default();
        let mut specs = vec![];
        specs.push(spec(
            "online/1".into(),
            "agent",
            "online_generation",
            c,
            Task::Online(1),
        ));
        for (id, role, stage, task) in [
            ("request", "user", "issue_request", Task::IssueRequest),
            ("issuer", "issuer", "issue_response", Task::IssueIssuer),
            ("accept", "user", "issue_accept", Task::IssueAccept),
            (
                "delegate-request",
                "agent",
                "delegate_request",
                Task::DelegateRequest,
            ),
            (
                "delegate",
                "user",
                "delegate_send",
                Task::DelegateSend {
                    gamma: 1,
                    hot: false,
                },
            ),
            (
                "receive",
                "agent",
                "delegate_receive",
                Task::DelegateReceive(1),
            ),
            ("scope-cold", "agent", "scope_opening", Task::Scope(false)),
            ("scope-hot", "agent", "scope_opening", Task::Scope(true)),
            ("prep", "agent", "preparation", Task::Prepare(16)),
            ("online", "agent", "online_generation", Task::Online(16)),
        ] {
            specs.push(spec(id.into(), role, stage, c, task));
        }
        for (id, mode, per_block) in [
            ("spec", Mode::Specification, false),
            ("random-block", Mode::Randomized, true),
            ("random-across", Mode::Randomized, false),
        ] {
            specs.push(spec(
                id.into(),
                "verifier",
                "inclusive_verification",
                c,
                Task::Inclusive {
                    k: 16,
                    mode,
                    per_block,
                    ablation: false,
                },
            ));
        }
        specs.push(spec(
            "alias-random".into(),
            "verifier",
            "inclusive_verification",
            c,
            Task::Inclusive {
                k: 16,
                mode: Mode::Randomized,
                per_block: false,
                ablation: false,
            },
        ));
        for double_use in [false, true] {
            for mode in [Mode::Specification, Mode::Randomized] {
                specs.push(spec(
                    format!("judge/{double_use}/{mode:?}"),
                    "authority",
                    "identify",
                    c,
                    Task::Judge {
                        mode,
                        validated: false,
                        double_use,
                    },
                ));
            }
        }
        let ids = specs.iter().map(|s| s.job.id.clone()).collect::<Vec<_>>();
        let mut factory = test_pipeline(specs);
        let (first, clock) = run_clock_free_pipeline(&mut factory, &ids, 33_001);
        assert_eq!(first["core_actual_issuance_flows"], 1);
        assert_eq!(first["core_actual_delegation_flows"], 1);
        assert_eq!(first["core_generated_token_batches"], 2);
        let rows = &first["job_results"];
        let wire = rows["prep"]["wire_sha256"].clone();
        assert_eq!(rows["online"]["native_message_bytes"], 8599);
        for id in [
            "online",
            "spec",
            "random-block",
            "random-across",
            "alias-random",
        ] {
            assert_eq!(rows[id]["wire_sha256"], wire);
        }
        for id in ["spec", "random-block", "random-across", "alias-random"] {
            assert_eq!(rows[id]["state_before"], json!([10000, 10000]));
            assert_eq!(rows[id]["state_after"], json!([10001, 10016]));
        }
        assert_eq!(rows["scope-cold"]["cache_before"], 0);
        assert_eq!(rows["scope-hot"]["cache_before"], 1);
        assert_eq!(clock.len(), ids.len());
        assert_eq!(clock["alias-random"]["derived"], true);
        for branch in [false, true] {
            let a = format!("judge/{branch}/Specification");
            let b = format!("judge/{branch}/Randomized");
            assert_eq!(
                rows[&a]["received_message_digest"],
                rows[&b]["received_message_digest"]
            );
            assert_eq!(rows[&a]["record_a_from_same_slot_online"], true);
        }
        let next_ids = vec!["spec".into(), "random-block".into(), "random-across".into()];
        let (second, _) = run_clock_free_pipeline(&mut factory, &next_ids, 33_001);
        assert_eq!(second["core_actual_issuance_flows"], 0);
        assert_eq!(second["core_actual_delegation_flows"], 0);
        assert_eq!(second["accepted_child_asset_slots"], 1);
        assert_eq!(second["wallet_asset_reused"], true);
        assert_ne!(second["job_results"]["spec"]["wire_sha256"], wire);
        assert_eq!(factory.pipeline_assets.len(), 1);
        let mut mapped = new().unwrap();
        mapped.fixtures = std::mem::take(&mut factory.fixtures);
        mapped.pipeline_assets = std::mem::take(&mut factory.pipeline_assets);
        let ids = [
            "darlt/prepare/k16",
            "darlt/online/k16",
            "darlt/inclusive/RandomizedAcrossBlocks/native/k16",
        ]
        .map(str::to_string);
        let bindings = crate::campaign::plan(&mapped.jobs());
        let (_, observations) = run_clock_free_pipeline(&mut mapped, &ids, 33_005);
        let mut components = 0;
        for binding in bindings
            .iter()
            .filter(|b| b.usage == crate::campaign::Use::Derived && b.job.substage != "whole")
        {
            for parent in binding.parent_ids.iter().filter(|id| ids.contains(id)) {
                let component = binding.component.as_deref().unwrap();
                let name = component.strip_suffix(":exclusive").unwrap_or(component);
                assert!(
                    observations[parent]["darlt_spans"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|span| span["report"]["rows"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .any(|row| row["name"] == name && row["calls"].as_u64().unwrap() > 0)),
                    "missing live component {} of {}",
                    component,
                    parent
                );
                components += 1;
            }
        }
        assert!(components > 0);
    }
    #[test]
    fn pipeline_packs_all_nine_k_points_in_independent_wallet_worlds() {
        let c = Config {
            n: 256,
            s: 16,
            del: 6,
            private: 4,
            range: None,
        };
        let mut specs = vec![];
        for k in [1, 2, 4, 8, 16, 32, 64, 96, 128] {
            specs.push(spec(
                format!("native/{k}"),
                "verifier",
                "inclusive_verification",
                c,
                Task::Inclusive {
                    k,
                    mode: Mode::Randomized,
                    per_block: false,
                    ablation: false,
                },
            ));
        }
        specs.push(spec(
            "ablation/128".into(),
            "verifier",
            "inclusive_verification",
            c,
            Task::Inclusive {
                k: 128,
                mode: Mode::Specification,
                per_block: false,
                ablation: true,
            },
        ));
        let ids = specs.iter().map(|s| s.job.id.clone()).collect::<Vec<_>>();
        let mut factory = test_pipeline(specs);
        let (result, clock) = run_clock_free_pipeline(&mut factory, &ids, 33_002);
        assert_eq!(clock.len(), 10);
        assert_eq!(result["core_actual_issuance_flows"], 0);
        assert_eq!(result["core_generated_token_batches"], 10);
        assert_eq!(
            result["job_results"]["native/96"]["block_units"],
            json!([64, 32])
        );
        assert_eq!(
            result["job_results"]["native/128"]["block_units"],
            json!([64, 64])
        );
        assert_eq!(
            result["job_results"]["ablation/128"]["block_units"],
            json!(vec![1; 128])
        );
        assert_eq!(
            result["session_intermediates_retained_between_samples"],
            false
        );
        for k in [1, 2, 4, 8, 16, 32, 64, 96, 128] {
            assert_eq!(
                result["job_results"][format!("native/{k}")]["state_after"],
                json!([10001, 10000 + k])
            );
        }
    }
    #[test]
    fn pipeline_provision_derives_the_issuer_only_when_system_is_active() {
        let c = Config::default();
        let specs = vec![
            spec(
                "system".into(),
                "system",
                "provisioning_system",
                c,
                Task::Provision {
                    agents: 2,
                    issuer: false,
                },
            ),
            spec(
                "issuer".into(),
                "issuer",
                "provisioning_issuer",
                c,
                Task::Provision {
                    agents: 2,
                    issuer: true,
                },
            ),
        ];
        let mut factory = test_pipeline(specs);
        let (first, clock) =
            run_clock_free_pipeline(&mut factory, &["system".into(), "issuer".into()], 33_003);
        assert_eq!(clock["issuer"]["derived"], true);
        assert_eq!(clock["issuer"]["source_job"], "system");
        assert_eq!(first["job_results"]["system"]["actual_issuer_calls"], 1);
        assert_eq!(first["job_results"]["system"]["actual_delegation_calls"], 2);
        assert_eq!(
            first["job_results"]["system"]["actual_agent_quotas"],
            json!([512, 512])
        );
        let (next, clock) = run_clock_free_pipeline(&mut factory, &["issuer".into()], 33_004);
        assert_eq!(clock["issuer"]["derived"], false);
        assert_eq!(next["job_results"]["issuer"]["actual_issuer_calls"], 1);
        assert_eq!(next["job_results"]["issuer"]["actual_delegation_calls"], 0);
        assert_ne!(
            first["job_results"]["system"]["actual_request_digest"],
            next["job_results"]["issuer"]["actual_request_digest"]
        );
    }
    #[cfg(feature = "subgroup-audit")]
    fn received_field_inventory(tokens: &[Token]) -> Vec<Value> {
        fn field(out: &mut Vec<Value>, name: String, kind: &str, bytes: &[u8]) {
            let hex = bytes.iter().map(|v| format!("{v:02x}")).collect::<String>();
            out.push(json!({"field":name,"kind":kind,"encoding_hex":hex}));
        }
        let mut out = vec![];
        for (block, t) in tokens.iter().enumerate() {
            let prefix = format!("block{block}");
            for (i, p) in t.auth.message.iter().enumerate() {
                field(
                    &mut out,
                    format!("{prefix}/auth.M[{i}]"),
                    "G1",
                    &p.to_compressed(),
                );
            }
            field(
                &mut out,
                format!("{prefix}/auth.Z"),
                "G1",
                &t.auth.signature.z.to_compressed(),
            );
            field(
                &mut out,
                format!("{prefix}/auth.Y"),
                "G1",
                &t.auth.signature.y.to_compressed(),
            );
            field(
                &mut out,
                format!("{prefix}/auth.Yhat"),
                "G2",
                &t.auth.signature.yhat.to_compressed(),
            );
            for (name, p) in [
                ("scope", t.scope),
                ("offset_table", t.offset_table),
                ("vector0", t.commitments[0]),
                ("vector1", t.commitments[1]),
                ("vector2", t.commitments[2]),
                ("seed_query", t.seed_query),
            ] {
                field(
                    &mut out,
                    format!("{prefix}/{name}"),
                    "G1",
                    &p.to_compressed(),
                );
            }
            for (i, u) in t.units.iter().enumerate() {
                for (name, p) in [("SN", u.sn), ("AID", u.aid), ("Tu", u.tu), ("Ta", u.ta)] {
                    field(
                        &mut out,
                        format!("{prefix}/unit[{i}]/{name}"),
                        "G1",
                        &p.to_compressed(),
                    );
                }
            }
            for (i, p) in t.lookups.iter().enumerate() {
                for (name, point) in [
                    ("C_I", p.c_i),
                    ("Z_I", p.z_i),
                    ("U", p.u),
                    ("H_2", p.h_2),
                    ("Ubar", p.u_bar),
                    ("H_2multi", p.h_2_multi),
                    ("H_1", p.h_1),
                    ("Ubar_a", p.u_bar_a),
                    ("H_2a", p.h_2_a),
                    ("Q_ord", p.q_ord),
                    ("Q_v", p.q_v),
                    ("Q_part", p.q_part),
                    ("Q_3", p.q_3),
                    ("Q_b", p.q_b),
                ] {
                    field(
                        &mut out,
                        format!("{prefix}/caulk[{i}]/{name}"),
                        "G1",
                        &point.to_compressed(),
                    );
                }
                field(
                    &mut out,
                    format!("{prefix}/caulk[{i}]/H_1main"),
                    "G2",
                    &p.h_1_main.to_compressed(),
                );
            }
            for (i, p) in t.range_commitments.iter().enumerate() {
                field(
                    &mut out,
                    format!("{prefix}/range[{i}]"),
                    "G1",
                    &p.to_compressed(),
                );
            }
        }
        out
    }
    #[cfg(feature = "subgroup-audit")]
    #[test]
    fn received_points_are_checked_once_in_every_complete_boundary() {
        let f = Fixture::new(Config::default()).unwrap();
        let mut rng = StdRng::seed_from_u64(32_032);
        let mut runs = vec![];
        for ablation in [false, true] {
            let tokens = make_tokens(&f, 16, ablation, b"once-per-field", &mut rng).unwrap();
            let fields = received_field_inventory(&tokens);
            let wire = tokens.iter().map(Token::wire_encode).collect::<Vec<_>>();
            for (label, mode, per_block) in [
                ("specification", Mode::Specification, false),
                ("randomized-per-block", Mode::Randomized, true),
                ("randomized-across-blocks", Mode::Randomized, false),
            ] {
                let (ok, audit) = crate::subgroup_audit::collect(|| {
                    verify_received(
                        f.verifier.runtime_view(),
                        &f.ip,
                        &wire,
                        mode,
                        per_block,
                        &mut rng,
                    )
                    .unwrap()
                });
                assert!(ok);
                assert_eq!(audit.events.len(), fields.len());
                for (event, field) in audit.events.iter().zip(&fields) {
                    assert_eq!(event.operation, "checked_decode");
                    assert_eq!(event.kind, field["kind"]);
                    assert_eq!(event.encoding_hex, field["encoding_hex"]);
                }
                runs.push(json!({"boundary":label,"ablation":ablation,"k":16,"fields":fields,"audit":audit}));
            }
            let adapter = crate::adapters::ReceivedDarlt::new(&f.context);
            let store =
                SpentStore::with_preexisting_records(10000, adapter.namespace(), 48).unwrap();
            let (accepted, audit) = crate::subgroup_audit::collect(|| {
                let received = decode_received(f.verifier.runtime_view(), &wire).unwrap();
                crate::batch_runtime::verify_and_record(
                    &adapter,
                    &received,
                    b"full-request",
                    b"ok",
                    &store,
                    crate::batch_runtime::Mode::Specification,
                    &mut rng,
                )
                .unwrap()
            });
            assert_eq!(accepted.newly_registered, 16);
            assert_eq!(audit.events.len(), fields.len());
            assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
            runs.push(json!({"boundary":"inclusive-10000-records","ablation":ablation,"k":16,"fields":fields,"audit":audit}));
            let (bit, audit) = crate::subgroup_audit::collect(|| {
                let received =
                    ReceivedToken::wire_decode(f.verifier.runtime_view(), &wire[0]).unwrap();
                f.context.read_bit_received(
                    &received,
                    &f.sk.metadata_secrets,
                    Mode::Specification,
                    &mut rng,
                )
            });
            assert_eq!(bit, Some(1));
            let first_fields = received_field_inventory(&tokens[..1]);
            assert_eq!(audit.events.len(), first_fields.len());
            assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
            runs.push(json!({"boundary":"native-full-read","ablation":ablation,"fields":first_fields,"audit":audit}));
        }
        let a = make_tokens(&f, 1, false, b"judge-A", &mut rng)
            .unwrap()
            .remove(0);
        let b = make_tokens(&f, 1, false, b"judge-B", &mut rng)
            .unwrap()
            .remove(0);
        let fields = received_field_inventory(&[a.clone(), b.clone()]);
        let (identified, audit) = crate::subgroup_audit::collect(|| {
            let a =
                ReceivedToken::wire_decode(f.verifier.runtime_view(), &a.wire_encode()).unwrap();
            let b =
                ReceivedToken::wire_decode(f.verifier.runtime_view(), &b.wire_encode()).unwrap();
            f.context
                .judge_received(&a, 0, &b, 0, Mode::Specification, &mut rng)
        });
        assert_eq!(
            identified,
            Some((
                spend::Responsibility::DoubleAlloc,
                G1::generator() * S::from(91)
            ))
        );
        assert_eq!(audit.events.len(), fields.len());
        assert!(audit.events.iter().all(|e| e.operation == "checked_decode"));
        runs.push(json!({"boundary":"full-judge","fields":fields,"audit":audit}));
        let mut fine_jobs = vec![];
        let mut factory = new().unwrap();
        for profile in ["Specification", "RandomizedAcrossBlocks"] {
            for direction in ["inclusive", "exclusive"] {
                let id = format!("darlt/verify/{profile}/native/k16/substage/point_decode_and_subgroup/{direction}");
                let action = factory.prepare(&id, 32_034).unwrap();
                let mut clock = crate::experiment::BoundaryClock::new(
                    crate::experiment::RunMode::ClockFree,
                    None,
                )
                .unwrap();
                action(&mut clock).unwrap();
                assert_eq!(clock.segments(), &[None]);
                fine_jobs.push(json!({"id":id,"ok":true,"time_ns":null,"formal_samples":0}));
            }
        }
        std::fs::write(
            std::env::temp_dir().join("darlt-subgroup-diagnostic.json"),
            serde_json::to_vec_pretty(
                &json!({"formal_samples":0,"clock_free":true,"runs":runs,"fine_jobs":fine_jobs}),
            )
            .unwrap(),
        )
        .unwrap();
    }
    #[test]
    fn sealed_received_algorithms_preserve_native_equations_and_parameter_binding() {
        let f = Fixture::new(Config {
            n: 32,
            s: 8,
            del: 4,
            private: 1,
            range: Some(8),
        })
        .unwrap();
        let mut rng = StdRng::seed_from_u64(32_033);
        let original = make_tokens(&f, 3, false, b"unchanged-native-proof", &mut rng)
            .unwrap()
            .remove(0);
        let parsed =
            ReceivedToken::wire_decode(f.verifier.runtime_view(), &original.wire_encode()).unwrap();
        assert!(parsed.native_equations_match(f.verifier.runtime_view(), &f.ip));
        for mode in [Mode::Specification, Mode::Randomized] {
            assert!(f.context.valid_received(&parsed, mode, &mut rng));
        }
        let mut mutations = vec![];
        let mut t = original.clone();
        t.proof.c += S::ONE;
        mutations.push(t);
        let mut t = original.clone();
        t.proof.z[0] += S::ONE;
        mutations.push(t);
        let mut t = original.clone();
        t.context.push(1);
        mutations.push(t);
        let mut t = original.clone();
        t.auth.signature.z = G1::identity();
        mutations.push(t);
        let mut t = original.clone();
        t.lookups[0].q_ord = G1::identity();
        mutations.push(t);
        for t in mutations {
            let parsed =
                ReceivedToken::wire_decode(f.verifier.runtime_view(), &t.wire_encode()).unwrap();
            for mode in [Mode::Specification, Mode::Randomized] {
                assert!(!f.context.valid(&t, mode, &mut rng));
                assert!(!f.context.valid_received(&parsed, mode, &mut rng));
            }
        }
        let other = Fixture::new(Config {
            n: 64,
            s: 8,
            del: 4,
            private: 1,
            range: Some(8),
        })
        .unwrap();
        assert!(!other
            .context
            .valid_received(&parsed, Mode::Specification, &mut rng));
    }
    #[test]
    fn clock_free_instrumentation_preserves_complete_native_token_bytes() {
        let f = Fixture::new(Config {
            n: 32,
            s: 8,
            del: 3,
            private: 1,
            range: None,
        })
        .unwrap();
        let mut plain_rng = StdRng::seed_from_u64(30_334);
        let plain = make_tokens(&f, 3, false, b"byte-check", &mut plain_rng).unwrap();
        let mut observed_rng = StdRng::seed_from_u64(30_334);
        let (observed, report) = instrumentation::collect(instrumentation::Mode::ClockFree, || {
            make_tokens(&f, 3, false, b"byte-check", &mut observed_rng)
        })
        .unwrap();
        let observed = observed.unwrap();
        assert_eq!(
            plain.iter().map(Token::wire_encode).collect::<Vec<_>>(),
            observed.iter().map(Token::wire_encode).collect::<Vec<_>>()
        );
        assert!(report
            .rows
            .iter()
            .all(|r| r.inclusive_ns.is_none() && r.exclusive_ns.is_none()));
        for name in [
            "hash_to_group",
            "polynomial",
            "sigma_response",
            "fiat_shamir",
        ] {
            assert!(report.duration(name, true).is_ok());
        }
    }
    #[test]
    fn inventory_contains_full_independent_scale_grids_and_safe_profiles() {
        let factory = new().unwrap();
        let jobs = factory.jobs();
        let fixed_receiver_jobs = jobs
            .iter()
            .filter(|j| {
                j.substage == "whole"
                    && matches!(
                        j.stage.as_str(),
                        "issue_accept" | "delegate_receive" | "native_read"
                    )
            })
            .collect::<Vec<_>>();
        assert_eq!(fixed_receiver_jobs.len(), 28);
        for job in fixed_receiver_jobs {
            assert_eq!(job.profile, "Randomized");
            assert_eq!(job.boundary["pairing_batch_weight_bits"], 128);
        }
        let judges = jobs
            .iter()
            .filter(|j| j.stage == "identify")
            .collect::<Vec<_>>();
        assert_eq!(judges.len(), 4);
        assert_eq!(
            judges
                .iter()
                .map(|j| (
                    j.workload["judge_branch"].as_str().unwrap(),
                    j.profile.as_str()
                ))
                .collect::<BTreeSet<_>>()
                .len(),
            4
        );
        assert_eq!(
            judges
                .iter()
                .map(|j| crate::campaign::measurement_key(j))
                .collect::<BTreeSet<_>>()
                .len(),
            4
        );
        assert_eq!(
            jobs.iter()
                .filter(|j| j.id.starts_with("darlt/scan/"))
                .count(),
            18 * 11
        );
        for a in [5, 10, 15, 20, 25, 30] {
            let j = jobs
                .iter()
                .find(|j| j.id == format!("darlt/scan/attributes/{a}/online"))
                .unwrap();
            assert_eq!(j.workload["attributes"], a);
            assert_eq!(j.workload["private_attributes"], 0);
        }
        for j in jobs {
            assert!(!j.boundary["network_included"].as_bool().unwrap());
            assert!(!j.boundary["persistence_included"].as_bool().unwrap());
            if [
                "verification_crypto",
                "inclusive_verification",
                "strict_decoding",
            ]
            .contains(&j.stage.as_str())
            {
                for flag in [
                    "strict_decoding_included",
                    "received_bytes_first",
                    "subgroup_checks_included",
                    "native_format_checks_included",
                ] {
                    assert_eq!(j.boundary[flag], true, "{} {flag}", j.id);
                }
            }
            if j.stage == "strict_decoding" {
                assert_eq!(j.boundary["decode_only"], true);
                assert_eq!(
                    j.boundary["parent_verification_stage"],
                    "verification_crypto"
                );
            }
        }
    }
    fn subgroup_fixtures() -> ([u8; 48], [u8; 96]) {
        let one = (1u64..256)
            .find_map(|i| {
                let mut b = [0; 48];
                b[0] = 0x80;
                b[40..].copy_from_slice(&i.to_be_bytes());
                let p = Option::<blstrs::G1Affine>::from(
                    blstrs::G1Affine::from_compressed_unchecked(&b),
                )?;
                (bool::from(p.is_on_curve())
                    && !bool::from(p.is_torsion_free())
                    && p.to_compressed() == b)
                    .then_some(b)
            })
            .expect("canonical on-curve G1 outside prime subgroup");
        let two = (1u64..256)
            .find_map(|i| {
                let mut b = [0; 96];
                b[0] = 0x80;
                b[88..].copy_from_slice(&i.to_be_bytes());
                let p = Option::<blstrs::G2Affine>::from(
                    blstrs::G2Affine::from_compressed_unchecked(&b),
                )?;
                (bool::from(p.is_on_curve())
                    && !bool::from(p.is_torsion_free())
                    && p.to_compressed() == b)
                    .then_some(b)
            })
            .expect("canonical on-curve G2 outside prime subgroup");
        (one, two)
    }
    #[test]
    fn every_received_group_and_sigma_or_caulk_scalar_is_strictly_decoded() {
        let f = Fixture::new(Config {
            n: 32,
            s: 8,
            del: 4,
            private: 1,
            range: Some(8),
        })
        .unwrap();
        let mut rng = StdRng::seed_from_u64(31_023);
        let token = make_tokens(&f, 3, false, b"decoder-fields", &mut rng)
            .unwrap()
            .remove(0);
        let wire = token.wire_encode();
        let ledger = crate::darlt::evidence::token_ledger(&token).unwrap();
        let (bad1, bad2) = subgroup_fixtures();
        let (mut g1, mut g2, mut scalars) = (0, 0, 0);
        for field in &ledger {
            let at = field["offset"].as_u64().unwrap() as usize;
            let n1 = field["g1"].as_u64().unwrap() as usize;
            let n2 = field["g2"].as_u64().unwrap() as usize;
            for i in 0..n1 {
                let mut bad = wire.clone();
                bad[at + 48 * i..at + 48 * (i + 1)].copy_from_slice(&bad1);
                assert!(
                    Token::wire_decode(f.verifier.runtime_view(), &bad).is_err(),
                    "G1 {}[{i}]",
                    field["field"]
                );
                g1 += 1;
            }
            for i in 0..n2 {
                let start = at + 48 * n1 + 96 * i;
                let mut bad = wire.clone();
                bad[start..start + 96].copy_from_slice(&bad2);
                assert!(
                    Token::wire_decode(f.verifier.runtime_view(), &bad).is_err(),
                    "G2 {}[{i}]",
                    field["field"]
                );
                g2 += 1;
            }
            let nf = field["fr"].as_u64().unwrap() as usize;
            for i in 0..nf {
                let start = at + 48 * n1 + 96 * n2 + 32 * i;
                let mut bad = wire.clone();
                bad[start..start + 32].fill(255);
                assert!(
                    Token::wire_decode(f.verifier.runtime_view(), &bad).is_err(),
                    "Fr {}[{i}]",
                    field["field"]
                );
                scalars += 1;
            }
        }
        assert_eq!(g1, 45 + 4 * 3 + token.range_commitments.len());
        assert_eq!(g2, 3);
        let mut trailing = wire.clone();
        trailing.push(0);
        assert!(Token::wire_decode(&f.pp, &trailing).is_err());
        assert!(Token::wire_decode(&f.pp, &wire[..wire.len() - 1]).is_err());
        let units = ledger
            .iter()
            .find(|x| x["field"] == "units.length")
            .unwrap()["offset"]
            .as_u64()
            .unwrap() as usize;
        let mut shape = wire.clone();
        shape[units..units + 8].copy_from_slice(&65u64.to_be_bytes());
        assert!(Token::wire_decode(&f.pp, &shape).is_err());
        let policy = ledger.iter().find(|x| x["field"] == "policy").unwrap()["offset"]
            .as_u64()
            .unwrap() as usize;
        let mut scalar = wire.clone();
        scalar[policy + 25..policy + 57].fill(255);
        assert!(Token::wire_decode(&f.pp, &scalar).is_err());
        eprintln!("receive-boundary audit strict received fields: G1={g1},G2={g2},nested/Sigma Fr={scalars},range commitments={}",token.range_commitments.len());
    }
    #[test]
    fn native_identity_rules_allow_zero_commitments_and_reject_only_required_nonzero_fields() {
        let f = Fixture::new(Config {
            n: 32,
            s: 8,
            del: 4,
            private: 1,
            range: Some(8),
        })
        .unwrap();
        let mut rng = StdRng::seed_from_u64(31_024);
        let original = make_tokens(&f, 1, false, b"identity-format", &mut rng)
            .unwrap()
            .remove(0);
        let mut allowed = original.clone();
        allowed.auth.signature.z = G1::identity();
        allowed.scope = G1::identity();
        allowed.offset_table = G1::identity();
        allowed.seed_query = G1::identity();
        allowed.commitments.fill(G1::identity());
        allowed.range_commitments.fill(G1::identity());
        allowed.proof.c = S::ZERO;
        allowed.proof.z.fill(S::ZERO);
        allowed.proof.bits.fill([S::ZERO; 3]);
        for p in &mut allowed.lookups {
            p.c_i = G1::identity();
            p.u = G1::identity();
            p.h_2 = G1::identity();
            p.u_bar = G1::identity();
            p.h_2_multi = G1::identity();
            p.h_1 = G1::identity();
            p.u_bar_a = G1::identity();
            p.h_2_a = G1::identity();
            p.q_ord = G1::identity();
            p.q_v = G1::identity();
            p.q_part = G1::identity();
            p.q_3 = G1::identity();
            p.q_b = G1::identity();
            p.h_1_main = G2::identity();
            p.v_1 = S::ZERO;
            p.v_2 = S::ZERO;
            p.v_2_prime = S::ZERO;
            p.v_3_prime = S::ZERO;
        }
        // This is a positive format test, not a claim that altered commitments
        // still satisfy the original signature or proof equations.
        let wire = allowed.wire_encode();
        assert_eq!(
            Token::wire_decode(f.verifier.runtime_view(), &wire)
                .unwrap()
                .wire_encode(),
            wire
        );
        for i in 0..9 {
            let mut bad = original.clone();
            bad.auth.message[i] = G1::identity();
            assert!(Token::wire_decode(&f.pp, &bad.wire_encode()).is_err());
        }
        let mut bad = original.clone();
        bad.auth.signature.y = G1::identity();
        assert!(Token::wire_decode(&f.pp, &bad.wire_encode()).is_err());
        let mut bad = original.clone();
        bad.auth.signature.yhat = G2::identity();
        assert!(Token::wire_decode(&f.pp, &bad.wire_encode()).is_err());
        for role in 0..2 {
            let mut bad = original.clone();
            bad.lookups[role].z_i = G1::identity();
            assert!(Token::wire_decode(&f.pp, &bad.wire_encode()).is_err());
        }
        for column in 0..4 {
            let mut bad = original.clone();
            let u = &mut bad.units[0];
            match column {
                0 => u.sn = G1::identity(),
                1 => u.aid = G1::identity(),
                2 => u.tu = G1::identity(),
                _ => u.ta = G1::identity(),
            };
            assert!(Token::wire_decode(&f.pp, &bad.wire_encode()).is_err());
        }
    }
    struct NoVerifierCoins;
    impl rand::RngCore for NoVerifierCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("coins before complete received batch validation")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("coins before complete received batch validation")
        }
        fn fill_bytes(&mut self, _: &mut [u8]) {
            panic!("coins before complete received batch validation")
        }
        fn try_fill_bytes(&mut self, _: &mut [u8]) -> std::result::Result<(), rand::Error> {
            panic!("coins before complete received batch validation")
        }
    }
    #[test]
    fn malformed_second_packet_is_rejected_before_any_randomized_verifier_coins() {
        let f = Fixture::new(Config {
            n: 32,
            s: 8,
            del: 3,
            private: 1,
            range: None,
        })
        .unwrap();
        let mut rng = StdRng::seed_from_u64(31_025);
        let token = make_tokens(&f, 1, false, b"batch-fixed-before-coins", &mut rng)
            .unwrap()
            .remove(0);
        let wire = token.wire_encode();
        let mut malformed = wire.clone();
        malformed.push(0);
        for per_block in [false, true] {
            assert!(verify_received(
                f.verifier.runtime_view(),
                &f.ip,
                &[wire.clone(), malformed.clone()],
                Mode::Randomized,
                per_block,
                &mut NoVerifierCoins
            )
            .is_err());
        }
    }
    #[test]
    fn strict_lifecycle_codecs_preserve_bytes_and_reject_malformed_inputs() {
        let f = Fixture::new(Config {
            n: 32,
            s: 8,
            del: 3,
            private: 1,
            range: None,
        })
        .unwrap();
        let mut rng = StdRng::seed_from_u64(30_991);
        let (attrs, private) = f.config.attributes();
        let (q, s) =
            protocol::prepare_request(&f.pp, &f.ip, S::from(91), &attrs, &private, &mut rng)
                .unwrap();
        let b = q.encode();
        assert_eq!(decode_request(&f.pp, &b).unwrap().encode(), b);
        let res = protocol::issue(&f.pp, &f.ip, &f.sk, &q, 1, &mut rng).unwrap();
        let rb = res.encode();
        let parsed = decode_response(&f.pp, &rb).unwrap();
        assert_eq!(parsed.encode(), rb);
        protocol::accept(&f.pp, &f.ip, &q, &s, &parsed, &mut rng).unwrap();
        for (input, kind) in [(&b, 0), (&rb, 1)] {
            let mut trailing = input.clone();
            trailing.push(0);
            let mut bad = input.clone();
            bad[..48].fill(255);
            let decode = |x: &[u8]| {
                if kind == 0 {
                    decode_request(&f.pp, x).map(|_| ())
                } else {
                    decode_response(&f.pp, x).map(|_| ())
                }
            };
            assert!(decode(&input[..input.len() - 1]).is_err());
            assert!(decode(&trailing).is_err());
            assert!(decode(&bad).is_err());
        }
        let q = f
            .context
            .delegation_request(b"codec-recipient", S::from(111), &mut rng)
            .unwrap();
        assert_eq!(
            decode_recipient_request(&q.encode()).unwrap().encode(),
            q.encode()
        );
        assert_eq!(
            decode_issuer(&f.ip.encode()).unwrap().encode(),
            f.ip.encode()
        );
    }
}
