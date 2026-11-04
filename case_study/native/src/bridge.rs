//! Case-study bridge with strict received-message decoding.
mod public_codec;
use baseline_core::{
    msb23::{pok, scheme as msb, wire},
    slw25 as slw, sma2rt as sma,
};
use blstrs::G1Projective as G1;
use darlt_spseq_fc::{
    darlt::{
        context::ProtocolContext,
        protocol::{self, PublicParameters, Wallet},
        spend::{self, Atom, Policy, ReceivedToken},
        state::request_hash,
        verification::Mode,
    },
    polynomial::S,
};
use ff::Field;
use group::Group;
use rand::{
    rngs::{OsRng, StdRng},
    SeedableRng,
};
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    sync::{mpsc, Arc},
    thread,
    time::Instant,
};
type Result<T> = std::result::Result<T, String>;
fn err<E: std::fmt::Display>(e: E) -> String {
    e.to_string()
}
fn rng() -> StdRng {
    StdRng::from_rng(OsRng).expect("operating-system RNG unavailable")
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn unhex(s: &str) -> Result<Vec<u8>> {
    if !s.len().is_multiple_of(2) || s.len() > 4 * 1024 * 1024 || !s.is_ascii() {
        return Err("hex length".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(err))
        .collect()
}
fn s<'a>(v: &'a Value, key: &str) -> Result<&'a str> {
    v[key].as_str().ok_or_else(|| format!("{key} missing"))
}
fn id(v: &Value) -> Result<String> {
    v["instance"]
        .as_str()
        .or_else(|| v["instance_id"].as_str())
        .map(str::to_owned)
        .ok_or("instance missing".into())
}
fn list(v: &Value, key: &str) -> Result<Vec<usize>> {
    v[key]
        .as_array()
        .ok_or_else(|| format!("{key} array missing"))?
        .iter()
        .map(|x| {
            x.as_u64()
                .and_then(|x| usize::try_from(x).ok())
                .ok_or("integer list required".into())
        })
        .collect()
}
fn wires(v: &Value) -> Result<Vec<Vec<u8>>> {
    let a = v["wire_hex"].as_array().ok_or("wire_hex array missing")?;
    if a.is_empty() || a.len() > 128 {
        return Err("wire count".into());
    }
    a.iter()
        .map(|x| unhex(x.as_str().ok_or("wire hex string")?))
        .collect()
}
fn requirements(p: &Value) -> Result<Vec<(usize, u64)>> {
    let mut out = vec![];
    if let Some(a) = p["required_attrs"].as_array() {
        for x in a {
            let i = x["index"].as_u64().ok_or("required index")? as usize;
            let value = x["value"].as_u64().ok_or("required value")?;
            if i >= 10 {
                return Err("attribute index".into());
            }
            out.push((i, value));
        }
    } else {
        let i = p["required_attr"]
            .as_u64()
            .or_else(|| p["capability"].as_u64())
            .unwrap_or(1) as usize;
        if i >= 10 {
            return Err("attribute index".into());
        }
        out.push((i, 1));
    }
    out.sort();
    if out.windows(2).any(|x| x[0].0 == x[1].0) {
        return Err("duplicate required attribute".into());
    }
    Ok(out)
}
fn period(p: &Value) -> Result<u64> {
    p["period"]
        .as_u64()
        .filter(|x| *x == 1)
        .ok_or("issued epoch requires period 1".into())
}
fn policy(p: &Value) -> Result<Policy> {
    let mut atoms = vec![Atom::Equal(0, S::from(period(p)?))];
    for (i, value) in requirements(p)? {
        if i == 0 {
            if value != period(p)? {
                return Err("period attribute conflict".into());
            }
        } else {
            atoms.push(Atom::Equal(i, S::from(value)));
        }
    }
    Ok(Policy {
        period: period(p)?,
        atoms,
    })
}
fn sma_policy(p: &Value) -> Result<sma::Policy> {
    let mut atoms = vec![sma::Atom::Reveal(0, S::from(period(p)?))];
    for (i, value) in requirements(p)? {
        if i == 0 {
            if value != period(p)? {
                return Err("period attribute conflict".into());
            }
        } else {
            atoms.push(sma::Atom::Reveal(i, S::from(value)));
        }
    }
    Ok(sma::Policy { atoms })
}
fn msb_disclosure(p: &Value) -> Result<msb::Disclosure> {
    period(p)?;
    let req = requirements(p)?;
    if req.len() != 1 || req[0].1 != 1 {
        return Err("native MSB template requires one capability and fixed resource tag".into());
    }
    let i = req[0].0;
    let resource = if i == 0 { S::from(102) } else { S::from(101) };
    let cap = S::from(101 + i as u64);
    let mut root = vec![resource, cap];
    root.sort_by_key(|x| x.to_bytes_be());
    Ok(msb::Disclosure {
        indices: vec![1, 2],
        sets: vec![root, vec![msb::period_attribute()]],
    })
}
fn slw_disclosure(p: &Value) -> Result<(Vec<usize>, Vec<S>)> {
    period(p)?;
    let mut indices = vec![2];
    for (i, value) in requirements(p)? {
        if value != 1 {
            return Err("native attribute tag requires value1".into());
        }
        if i != 0 {
            indices.push(i + 2)
        }
    }
    indices.sort();
    let values = indices
        .iter()
        .map(|i| S::from(100 + (*i - 2) as u64))
        .collect();
    Ok((indices, values))
}
fn authorize(v: &Value) -> Result<bool> {
    if v["timing"] != true {
        return Ok(false);
    }
    if cfg!(feature = "subgroup-audit") {
        return Err("case study subgroup-audit build cannot collect timed measurements".into());
    }
    let plan: Value =
        serde_json::from_slice(&std::fs::read(s(v, "authorization_file")?).map_err(err)?)
            .map_err(err)?;
    let window = &plan["timing_window"];
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(err)?
        .as_secs_f64();
    let start = window["start_unix_seconds"]
        .as_f64()
        .ok_or("case study timing window start missing")?;
    let end = if window["end_unix_seconds"].is_null() {
        None
    } else {
        Some(
            window["end_unix_seconds"]
                .as_f64()
                .ok_or("case study timing window end must be numeric or null")?,
        )
    };
    if plan["case_study_authorized"] != true
        || plan["timing_enabled"] != true
        || !start.is_finite()
        || now < start
        || end.is_some_and(|e| !e.is_finite() || now > e)
    {
        return Err("case study timing not authorized".into());
    }
    Ok(true)
}
fn started(enabled: bool) -> Option<Instant> {
    enabled.then(Instant::now)
}
fn elapsed(start: Option<Instant>) -> Option<u64> {
    start.map(|t| t.elapsed().as_nanos() as u64)
}
fn timing(v: &mut Value, name: &str, n: Option<u64>) {
    if let Some(n) = n {
        v["timing"][name] = json!(n)
    }
}
fn hashkey(p: G1) -> String {
    hex(&p.to_compressed())
}

struct Darlt {
    pp: Arc<PublicParameters>,
    ip: Arc<protocol::IssuerPublic>,
    ctx: ProtocolContext,
    wallet: Wallet,
    child: darlt_spseq_fc::darlt::context::Child,
    agent: S,
    owner: S,
    pools: Vec<usize>,
    delta: Vec<bool>,
    ablation: bool,
    actors: BTreeMap<String, darlt_spseq_fc::darlt::context::Child>,
}
struct DarltParent {
    pp: Arc<PublicParameters>,
    ip: Arc<protocol::IssuerPublic>,
    ctx: ProtocolContext,
    wallet: Wallet,
    owner: S,
}
struct Sma {
    public_material: Value,
    installed: sma::InstalledInstance,
    wallet: sma::Wallet,
    user: String,
}
struct Msb {
    registered: msb::Registered,
    child: msb::Credential,
}
struct Slw {
    pk: slw::PublicKey,
    holder: slw::Holder,
    child: slw::Credential,
}
enum Instance {
    Darlt(Box<Darlt>),
    Sma(Box<Sma>),
    Msb(Box<Msb>),
    Slw(Box<Slw>),
}
type OnlineReply = (Vec<Vec<u8>>, protocol::Holder, Option<u64>);
struct DarltPending {
    tx: mpsc::Sender<Vec<u8>>,
    rx: mpsc::Receiver<Result<OnlineReply>>,
    thread: thread::JoinHandle<()>,
    ablation: bool,
}
enum Prepared {
    Darlt(DarltPending),
    Sma(Vec<sma::Prepared>),
    Msb(Box<msb::PreparedPolicyShow>),
    Slw(Box<slw::ShowPrepared>, Vec<u8>),
}
struct Pending {
    instance: String,
    actor: String,
    policy: Value,
    k: usize,
    state: Prepared,
}
enum Prover {
    Msb(Box<msb::ShowProverState>),
    SlwFirst(Box<slw::ShowPrepared>),
    SlwLast(Box<slw::ShowHolderAwaitThird>),
}
enum Verifier {
    Msb(Box<msb::ShowVerifierState>),
    SlwFirst(Box<slw::ShowVerifierProfileAwaitFirst>),
    SlwLast(Box<slw::ShowVerifierProfileAwaitFourth>),
}
struct Live {
    instance: String,
    policy: Value,
    context: Vec<u8>,
    state: Verifier,
}
#[derive(Clone)]
#[allow(clippy::large_enum_variant)]
enum PublicVerifier {
    Darlt(ProtocolContext),
    Sma(sma::InstalledInstance),
}
enum VerifierView<'a> {
    Darlt(&'a ProtocolContext),
    Sma(&'a sma::InstalledInstance),
}
struct Evidence {
    instance: String,
    wires: Vec<Vec<u8>>,
    context: Vec<u8>,
    policy: Value,
}
pub struct Bridge {
    role: String,
    public_instances: BTreeMap<String, PublicVerifier>,
    public_materials: BTreeMap<String, PublicVerifier>,
    public_bindings: BTreeMap<String, String>,
    timing: bool,
    next: u64,
    instances: BTreeMap<String, Instance>,
    parents: BTreeMap<String, DarltParent>,
    darlt_issuer_issue_calls: u64,
    pending: BTreeMap<String, Pending>,
    provers: BTreeMap<String, (String, Prover)>,
    verifiers: BTreeMap<String, Live>,
    evidence: BTreeMap<String, Evidence>,
}
impl Bridge {
    pub fn new(timing: bool) -> Self {
        Self {
            role: "direct".into(),
            public_instances: BTreeMap::new(),
            public_materials: BTreeMap::new(),
            public_bindings: BTreeMap::new(),
            timing,
            next: 0,
            instances: BTreeMap::new(),
            parents: BTreeMap::new(),
            darlt_issuer_issue_calls: 0,
            pending: BTreeMap::new(),
            provers: BTreeMap::new(),
            verifiers: BTreeMap::new(),
            evidence: BTreeMap::new(),
        }
    }
    fn handle(&mut self, prefix: &str) -> String {
        self.next += 1;
        format!("{prefix}-{}", self.next)
    }
    fn set_role(&mut self, v: &Value) -> Result<Value> {
        let role = s(v, "role")?;
        if !matches!(role, "direct" | "agent" | "server") {
            return Err("unknown native process role".into());
        }
        if self.role != role
            && (!self.instances.is_empty()
                || !self.parents.is_empty()
                || !self.public_instances.is_empty())
        {
            return Err("native role cannot change after state installation".into());
        }
        self.role = role.into();
        Ok(json!({"role":self.role,"process_id":std::process::id()}))
    }
    fn verifier_view(&self, name: &str) -> Result<VerifierView<'_>> {
        if let Some(public) = self.public_instances.get(name) {
            return Ok(match public {
                PublicVerifier::Darlt(ctx) => VerifierView::Darlt(ctx),
                PublicVerifier::Sma(installed) => VerifierView::Sma(installed),
            });
        }
        match self
            .instances
            .get(name)
            .ok_or("unknown verifier instance")?
        {
            Instance::Darlt(d) => Ok(VerifierView::Darlt(&d.ctx)),
            Instance::Sma(d) => Ok(VerifierView::Sma(&d.installed)),
            _ => Err("interactive scheme needs server_round".into()),
        }
    }
    fn export_verifier(&self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        let (scheme, material) = match self.instances.get(&name).ok_or("instance absent")? {
            Instance::Darlt(d) => ("DARLT", public_codec::darlt_export(&d.pp, &d.ip)),
            Instance::Sma(d) => ("SMA²RT", d.public_material.clone()),
            _ => return Err("public export supports DARLT and SMA²RT".into()),
        };
        Ok(
            json!({"version":"DARLT/public-verifier","instance":name,"scheme":scheme,"material_id":public_codec::digest(&material)?,"material":material}),
        )
    }
    fn install_verifier(&mut self, v: &Value) -> Result<Value> {
        let p = &v["package"];
        if s(p, "version")? != "DARLT/public-verifier" {
            return Err("public verifier version".into());
        }
        let name = id(p)?;
        if self.instances.contains_key(&name) || self.parents.contains_key(&name) {
            return Err("instance has private state".into());
        }
        let material_id = s(p, "material_id")?.to_owned();
        if material_id != public_codec::digest(&p["material"])? {
            return Err("public verifier material digest".into());
        }
        let scheme = s(p, "scheme")?;
        if !matches!(scheme, "DARLT" | "SMA²RT") {
            return Err("public verifier scheme".into());
        }
        if let Some(previous) = self.public_bindings.get(&name) {
            if previous != &material_id {
                return Err("conflicting public verifier instance".into());
            }
            if !matches!(
                (scheme, self.public_instances.get(&name)),
                ("DARLT", Some(PublicVerifier::Darlt(_)))
                    | ("SMA²RT", Some(PublicVerifier::Sma(_)))
            ) {
                return Err("public verifier scheme/material conflict".into());
            }
            return Ok(
                json!({"instance":name,"material_id":material_id,"cached":true,"idempotent":true}),
            );
        }
        let t = started(self.timing);
        let cached = self.public_materials.contains_key(&material_id);
        let public = if let Some(public) = self.public_materials.get(&material_id) {
            match (scheme, public) {
                ("DARLT", PublicVerifier::Darlt(_)) | ("SMA²RT", PublicVerifier::Sma(_)) => {
                    public.clone()
                }
                _ => return Err("public verifier scheme/material conflict".into()),
            }
        } else {
            match scheme {
                "DARLT" => PublicVerifier::Darlt(public_codec::darlt_import(&p["material"])?),
                _ => PublicVerifier::Sma(public_codec::sma_import(&p["material"])?),
            }
        };
        self.public_materials
            .entry(material_id.clone())
            .or_insert_with(|| public.clone());
        self.public_instances.insert(name.clone(), public);
        self.public_bindings
            .insert(name.clone(), material_id.clone());
        let mut answer = json!({"instance":name,"material_id":material_id,"cached":cached,"idempotent":false,"public_only":true});
        timing(&mut answer, "installation_ns", elapsed(t));
        Ok(answer)
    }
    pub fn command(&mut self, v: Value) -> Result<Value> {
        self.timing = authorize(&v)?;
        let op = s(&v, "op")?;
        if (self.role == "agent"
            && matches!(op, "verify" | "judge" | "server_round" | "install_verifier"))
            || (self.role == "server"
                && !matches!(
                    op,
                    "set_role" | "install_verifier" | "verify" | "judge" | "metadata"
                ))
        {
            return Err(format!("operation {op} denied for {} process", self.role));
        }
        match op {
            "set_role" => self.set_role(&v),
            "export_verifier" => self.export_verifier(&v),
            "install_verifier" => self.install_verifier(&v),
            "init" => self.init(&v),
            "issue_parent" => self.issue_parent(&v),
            "delegate_child" => self.delegate_child(&v),
            "prepare" => self.prepare(&v),
            "online" => self.online(&v),
            "verify" => self.verify(&v),
            "server_round" => self.server_round(&v),
            "client_round" => self.client_round(&v),
            "judge" => self.judge(&v),
            "reallocate" => self.reallocate(&v),
            "attack_material" => self.attack_material(&v),
            "metadata" => Ok(
                json!({"construction":"DARLT","strict_received":true,"subgroup_checks_per_received_element":1,"SET_coefficient_bits":128,"clock_free":!self.timing,"role":self.role,"process_id":std::process::id(),"private_instance_count":self.instances.len(),"public_verifier_instance_count":self.public_instances.len(),"public_material_count":self.public_materials.len(),"public_only_installed":self.instances.is_empty()&&self.parents.is_empty(),"darlt_issuer_issue_calls_total":self.darlt_issuer_issue_calls,"shared_parent_count":self.parents.len()}),
            ),
            _ => Err("unknown operation".into()),
        }
    }
    fn issue_parent(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        if self.parents.contains_key(&name) || self.instances.contains_key(&name) {
            return Err("parent or instance exists".into());
        }
        let mut r = rng();
        let total = started(self.timing);
        let t = started(self.timing);
        let pp = Arc::new(PublicParameters::setup(
            1024,
            16,
            64,
            6,
            4,
            b"DARLT/period/one",
            &mut r,
        )?);
        let setup_ns = elapsed(t);
        let t = started(self.timing);
        let (ip, sk) = protocol::keygen(&pp, &mut r)?;
        let ip = Arc::new(ip);
        let keygen_ns = elapsed(t);
        let t = started(self.timing);
        let ctx = ProtocolContext::new(pp.clone(), ip.clone())?;
        let installation_ns = elapsed(t);
        let owner = S::random(&mut r);
        let issuance = started(self.timing);
        let t = started(self.timing);
        let (q, sec) =
            protocol::prepare_request(&pp, &ip, owner, &[S::ONE; 6], &[S::ONE; 4], &mut r)?;
        let issue_request_ns = elapsed(t);
        let t = started(self.timing);
        self.darlt_issuer_issue_calls += 1;
        let response = protocol::issue(&pp, &ip, &sk, &q, 1, &mut r)?;
        let issuer_response_ns = elapsed(t);
        let t = started(self.timing);
        let wallet = protocol::accept(&pp, &ip, &q, &sec, &response, &mut r)?;
        let issue_accept_ns = elapsed(t);
        let issuance_ns = elapsed(issuance);
        let mut answer = json!({"parent":name,"instance":name,"scheme":"DARLT",
            "N":pp.n,"s":pp.s,"w":pp.w,"k_max":pp.k_max,
            "attributes":{"delegatable":pp.k_del,"private":pp.k_prv},
            "user_public_key":hashkey(G1::generator()*owner),
            "credential_id":hex(&wallet.id()),"issuer_public_key_id":hex(&request_hash(&ip.encode())),
            "public_parameters_id":hex(&pp.id),
            "issuer_issue_calls":1,"darlt_issuer_issue_calls_total":self.darlt_issuer_issue_calls,
            "timing_enabled":self.timing});
        timing(&mut answer, "setup_ns", setup_ns);
        timing(&mut answer, "keygen_ns", keygen_ns);
        timing(&mut answer, "parameter_installation_ns", installation_ns);
        timing(&mut answer, "issue_request_ns", issue_request_ns);
        timing(&mut answer, "issuer_response_ns", issuer_response_ns);
        timing(&mut answer, "issue_accept_ns", issue_accept_ns);
        timing(&mut answer, "issuance_ns", issuance_ns);
        timing(&mut answer, "parent_initialization_ns", elapsed(total));
        self.parents.insert(
            name,
            DarltParent {
                pp,
                ip,
                ctx,
                wallet,
                owner,
            },
        );
        Ok(answer)
    }

    fn delegate_child(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        if self.instances.contains_key(&name) || self.parents.contains_key(&name) {
            return Err("parent or instance exists".into());
        }
        let parent_id = s(v, "parent")?.to_owned();
        let pools = list(v, "pools")?;
        let grant = if v["allowed_attrs"].is_array() {
            list(v, "allowed_attrs")?
        } else {
            vec![0, 1, 2, 3]
        };
        if grant.iter().any(|&i| i >= 6) {
            return Err("delegatable attribute index out of range".into());
        }
        let scheme = v["scheme"].as_str().unwrap_or("DARLT");
        if !matches!(scheme, "DARLT" | "DARLT-ablation") {
            return Err("shared parent requires a DARLT variant".into());
        }
        let delta = (0..6).map(|i| grant.contains(&i)).collect::<Vec<_>>();
        let parent = self.parents.get_mut(&parent_id).ok_or("unknown parent")?;
        let mut r = rng();
        let mut weights = rng();
        let agent = S::random(&mut r);
        let total = started(self.timing);
        let t = started(self.timing);
        let request = parent
            .ctx
            .delegation_request(name.as_bytes(), agent, &mut r)?;
        let request_ns = elapsed(t);
        let t = started(self.timing);
        let delivery = parent
            .ctx
            .delegate(&mut parent.wallet, &request, &pools, &delta, &mut r)?;
        let derive_ns = elapsed(t);
        let t = started(self.timing);
        let child = parent
            .ctx
            .receive(&delivery, agent, None, Mode::Randomized, &mut weights)?;
        let receive_ns = elapsed(t);
        let delegation_ns = elapsed(total);
        let mut answer = json!({"instance":name,"parent":parent_id,"scheme":scheme,
            "N":parent.pp.n,"s":parent.pp.s,"w":parent.pp.w,"k_max":parent.pp.k_max,
            "attributes":{"delegatable":parent.pp.k_del,"private":parent.pp.k_prv},
            "agent_public_key":hashkey(G1::generator()*agent),
            "user_public_key":hashkey(G1::generator()*parent.owner),
            "credential_id":hex(&parent.wallet.id()),"issuer_public_key_id":hex(&request_hash(&parent.ip.encode())),
            "public_parameters_id":hex(&parent.pp.id),
            "pools":pools,"allowed_attrs":(0..6).filter(|i|delta[*i]).collect::<Vec<_>>(),
            "delegated_units":pools.len()*parent.pp.s,"positions":"global: pool*s+offset",
            "issuer_issue_calls":1,"darlt_issuer_issue_calls_total":self.darlt_issuer_issue_calls,
            "timing_enabled":self.timing});
        timing(&mut answer, "delegation_request_ns", request_ns);
        timing(&mut answer, "delegation_derive_ns", derive_ns);
        timing(&mut answer, "delegation_receive_ns", receive_ns);
        timing(&mut answer, "delegation_ns", delegation_ns);
        let instance = Darlt {
            pp: parent.pp.clone(),
            ip: parent.ip.clone(),
            ctx: parent.ctx.clone(),
            wallet: parent.wallet.clone(),
            child,
            agent,
            owner: parent.owner,
            pools,
            delta,
            ablation: scheme == "DARLT-ablation",
            actors: BTreeMap::new(),
        };
        self.instances
            .insert(name, Instance::Darlt(Box::new(instance)));
        Ok(answer)
    }

    fn init(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        if self.instances.contains_key(&name) {
            return Err("instance exists".into());
        }
        let scheme = s(v, "scheme")?;
        let mut r = rng();
        let mut weights = rng();
        let mut delegation_ns = None;
        let instance = match scheme {
            "DARLT" | "DARLT-ablation" => {
                let pp = Arc::new(PublicParameters::setup(
                    1024,
                    16,
                    64,
                    6,
                    4,
                    b"DARLT/period/one",
                    &mut r,
                )?);
                let (ip, sk) = protocol::keygen(&pp, &mut r)?;
                let ip = Arc::new(ip);
                let ctx = ProtocolContext::new(pp.clone(), ip.clone())?;
                let owner = S::random(&mut r);
                let agent = S::random(&mut r);
                let (q, sec) =
                    protocol::prepare_request(&pp, &ip, owner, &[S::ONE; 6], &[S::ONE; 4], &mut r)?;
                self.darlt_issuer_issue_calls += 1;
                let response = protocol::issue(&pp, &ip, &sk, &q, 1, &mut r)?;
                let mut wallet = protocol::accept(&pp, &ip, &q, &sec, &response, &mut r)?;
                let pools = if v["pools"].is_array() {
                    list(v, "pools")?
                } else {
                    vec![0, 1, 2, 3]
                };
                let grant = if v["allowed_attrs"].is_array() {
                    list(v, "allowed_attrs")?
                } else {
                    vec![0, 1, 2, 3]
                };
                let delta = (0..6).map(|i| grant.contains(&i)).collect::<Vec<_>>();
                let delegation_start = started(self.timing);
                let request = ctx.delegation_request(name.as_bytes(), agent, &mut r)?;
                let delivery = ctx.delegate(&mut wallet, &request, &pools, &delta, &mut r)?;
                let child = ctx.receive(&delivery, agent, None, Mode::Randomized, &mut weights)?;
                delegation_ns = elapsed(delegation_start);
                Instance::Darlt(Box::new(Darlt {
                    pp,
                    ip,
                    ctx,
                    wallet,
                    child,
                    agent,
                    owner,
                    pools,
                    delta,
                    ablation: scheme == "DARLT-ablation",
                    actors: BTreeMap::new(),
                }))
            }
            "SMA²RT" | "SMA2RT" | "SMA²RT (shared)" => {
                let pp = sma::setup(10, 1024);
                let issuer = sma::ikeygen(&pp, &mut r);
                let meta = sma::vkeygen(&pp, &mut r);
                let user = sma::ukeygen(&mut r);
                let installed = sma::install_instance(&pp, &issuer, &meta).map_err(err)?;
                let p = sma_policy(&json!({"period":1,"required_attr":1}))?;
                let (pending, request) =
                    sma::request_installed(&installed, &user, &[S::ONE; 10], &p, &mut r)
                        .map_err(err)?;
                let response =
                    sma::respond_installed(&installed, &issuer, &meta, &request, &p, 1, &mut r)
                        .map_err(err)?;
                let wallet = sma::receive_received_set(
                    &installed,
                    pending,
                    sma::ReceivedCredential::decode(&response.bytes()).map_err(err)?,
                    &mut weights,
                )
                .map_err(err)?;
                Instance::Sma(Box::new(Sma {
                    public_material: public_codec::sma_export(&pp, &issuer, &meta),
                    installed,
                    wallet,
                    user: hashkey(user.public_key()),
                }))
            }
            "MSB+23" => {
                let (pp, issuer) = msb::setup(10, &mut r).map_err(err)?;
                let reg = msb::install_cache(
                    wire::decode_parameters_checked(&wire::encode_parameters(&pp)).map_err(err)?,
                )
                .map_err(err)?;
                let user = msb::user_keygen(&mut r);
                let agent = msb::user_keygen(&mut r);
                let (q, pending) =
                    msb::issue_begin(&reg, &user, (101..111).map(S::from).collect(), &mut r)
                        .map_err(err)?;
                let (c, vs) = msb::issue_challenge_checked(
                    &reg,
                    wire::decode_issue_request_checked(&wire::encode_issue_request(&q))
                        .map_err(err)?,
                    &mut r,
                )
                .map_err(err)?;
                let (response, pending) = msb::issue_respond(pending, c).map_err(err)?;
                let d = msb::issue_issuer_received(
                    &reg,
                    &issuer,
                    vs,
                    pok::ReceivedResponse::from_bytes(&response.bytes()).map_err(err)?,
                    &mut r,
                )
                .map_err(err)?;
                let parent = msb::issue_finish_checked_random_pairing_key_rngs(
                    &reg,
                    pending,
                    wire::decode_issue_delivery_checked(&wire::encode_issue_delivery(&d))
                        .map_err(err)?,
                    &mut weights,
                    &mut r,
                )
                .map_err(err)?;
                let (q, pending) =
                    msb::delegate_begin(&reg, &agent, vec![msb::period_attribute()], &mut r)
                        .map_err(err)?;
                let d = msb::delegate_sender_checked(
                    &reg,
                    &parent,
                    wire::decode_delegate_request_checked(&wire::encode_delegate_request(&q))
                        .map_err(err)?,
                    &mut r,
                )
                .map_err(err)?;
                let child = msb::delegate_finish_checked_random_rngs(
                    &reg,
                    pending,
                    wire::decode_delegate_delivery_checked(&wire::encode_delegate_delivery(&d))
                        .map_err(err)?,
                    &mut weights,
                    &mut r,
                )
                .map_err(err)?;
                Instance::Msb(Box::new(Msb {
                    registered: reg,
                    child,
                }))
            }
            "SLW+25" => {
                let (pk, issuer) = slw::setup(10, &mut r).map_err(err)?;
                let pk = slw::PublicKey::decode_install_profile(
                    &pk.encode(),
                    slw::VerificationMode::Randomized,
                    &mut weights,
                )
                .map_err(err)?;
                let user = slw::Holder::generate(&mut r);
                let holder = slw::Holder::generate(&mut r);
                let attrs = (100..110).map(S::from).collect::<Vec<_>>();
                let (parent, _) = slw::run_issue_profile(
                    &pk,
                    &issuer,
                    &user,
                    &attrs,
                    slw::VerificationMode::Randomized,
                    &mut r,
                )
                .map_err(err)?;
                let (child, _) = slw::run_delegate_profile(
                    &pk,
                    &user,
                    &holder,
                    &parent,
                    &(2..12).collect::<Vec<_>>(),
                    slw::VerificationMode::Randomized,
                    &mut r,
                )
                .map_err(err)?;
                Instance::Slw(Box::new(Slw { pk, holder, child }))
            }
            _ => return Err("unknown scheme".into()),
        };
        let mut answer = json!({"instance":name,"scheme":scheme,"timing_enabled":self.timing});
        if let Instance::Darlt(d) = &instance {
            answer["N"] = json!(d.pp.n);
            answer["s"] = json!(d.pp.s);
            answer["w"] = json!(d.pp.w);
            answer["k_max"] = json!(d.pp.k_max);
            answer["attributes"] = json!({"delegatable":d.pp.k_del,"private":d.pp.k_prv});
            answer["agent_public_key"] = json!(hashkey(G1::generator() * d.agent));
            answer["user_public_key"] = json!(hashkey(G1::generator() * d.owner));
            answer["pools"] = json!(d.pools);
            answer["allowed_attrs"] = json!((0..6).filter(|i| d.delta[*i]).collect::<Vec<_>>());
            answer["delegated_units"] = json!(d.pools.len() * 16);
        }
        if let Instance::Sma(d) = &instance {
            answer["native_capacity"] = json!(1024);
            answer["native_attribute_count"] = json!(10);
            answer["native_agent_quota"] = json!(false);
            answer["user_public_key"] = json!(d.user);
            answer["sharing"] =
                json!("agent holds the original user wallet and native user secret");
        }
        if let Instance::Msb(_) = &instance {
            answer["native_quota"] = json!(false);
            answer["application_quota"] = json!("enforced by the service's scope and quota grant");
            answer["native_attribute_count"] = json!(10);
            answer["native_show_template"] = json!(
                "two business tags plus the native period tag; one live presentation per tool call"
            );
            answer["native_tag_mapping"] =
                json!("business tag i = 101+i; fixed resource tag 101 and selected capability tag");
        }
        if let Instance::Slw(_) = &instance {
            answer["native_quota"] = json!(false);
            answer["application_quota"] = json!("enforced by the service's scope and quota grant");
            answer["native_attribute_count"] = json!(10);
            answer["native_show_template"] =
                json!("one live partial-credential presentation per tool call");
            answer["native_tag_mapping"] =
                json!("policy attribute i maps to coordinate i+2 with native value 100+i");
        }
        timing(&mut answer, "delegation_ns", delegation_ns);
        self.instances.insert(name, instance);
        Ok(answer)
    }
    fn prepare(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        let k = v["k"].as_u64().unwrap_or(1) as usize;
        if k == 0 || k > 64 {
            return Err("k out of range".into());
        }
        let p = v["policy"].clone();
        period(&p)?;
        let positions = if v["positions"].is_array() {
            list(v, "positions")?
        } else if v["slots"].is_array() {
            list(v, "slots")?
        } else {
            (0..k).collect()
        };
        if positions.len() != k {
            return Err("positions length".into());
        }
        let mut r = rng();
        let t = started(self.timing);
        let state = match self.instances.get(&name).ok_or("unknown instance")? {
            Instance::Darlt(d) => {
                let pp = d.pp.clone();
                let ip = d.ip.clone();
                let actor = v["actor"].as_str().unwrap_or("agent");
                let holder = if actor == "agent" {
                    d.child.holder.clone()
                } else {
                    d.actors.get(actor).ok_or("unknown actor")?.holder.clone()
                };
                let ablation = v["ablation"].as_bool().unwrap_or(d.ablation);
                let p = policy(&p)?;
                let enabled = self.timing;
                let (tx, rx) = mpsc::channel::<Vec<u8>>();
                let (reply_tx, reply_rx) = mpsc::channel();
                let (ready_tx, ready_rx) = mpsc::channel();
                let thread = thread::spawn(move || {
                    let run = (|| -> Result<()> {
                        let mut holders = vec![holder; if ablation { k } else { 1 }];
                        let groups = if ablation {
                            positions.into_iter().map(|p| vec![p]).collect::<Vec<_>>()
                        } else {
                            vec![positions]
                        };
                        let mut local = rng();
                        let t = started(enabled);
                        let prepared = holders
                            .iter_mut()
                            .zip(groups)
                            .map(|(h, g)| spend::prepare_spend(&pp, &ip, h, &g, &p, &mut local))
                            .collect::<Result<Vec<_>>>()?;
                        let _ = ready_tx.send(Ok(elapsed(t)));
                        let ctx = rx.recv().map_err(err)?;
                        let t = started(enabled);
                        let result = prepared
                            .into_iter()
                            .map(|prepared| {
                                spend::finish_spend(&pp, &ip, prepared, &ctx, &mut local)
                                    .map(|x| x.wire_encode())
                            })
                            .collect::<Result<Vec<_>>>()?;
                        let online_ns = elapsed(t);
                        // Return the holder with its native scope-opening cache.
                        let holder = holders.into_iter().next().ok_or("holder absent")?;
                        let _ = reply_tx.send(Ok((result, holder, online_ns)));
                        Ok(())
                    })();
                    if let Err(e) = run {
                        let _ = ready_tx.send(Err(e.clone()));
                        let _ = reply_tx.send(Err(e));
                    }
                });
                let prep_ns = ready_rx.recv().map_err(err)??;
                let state = Prepared::Darlt(DarltPending {
                    tx,
                    rx: reply_rx,
                    thread,
                    ablation,
                });
                let handle = self.handle("prepared");
                self.pending.insert(
                    handle.clone(),
                    Pending {
                        instance: name,
                        actor: actor.to_owned(),
                        policy: p_to_json(v),
                        k,
                        state,
                    },
                );
                let mut answer = json!({"handle":handle,"k":k,"timing_enabled":enabled});
                answer["ablation"] = json!(ablation);
                timing(&mut answer, "preparation_ns", prep_ns);
                return Ok(answer);
            }
            Instance::Sma(d) => {
                let p = sma_policy(&p)?;
                Prepared::Sma(
                    positions
                        .iter()
                        .map(|pos| {
                            sma::precompute_policy_installed(
                                &d.installed,
                                &d.wallet,
                                *pos as u64,
                                &p,
                                &mut r,
                            )
                            .map_err(err)
                        })
                        .collect::<Result<Vec<_>>>()?,
                )
            }
            Instance::Msb(d) => Prepared::Msb(Box::new(
                msb::show_prepare_policy(&d.registered, &d.child, msb_disclosure(&p)?, &mut r)
                    .map_err(err)?,
            )),
            Instance::Slw(d) => {
                let (indices, _) = slw_disclosure(&p)?;
                let (state, prefix) = slw::show_prepare_profile(
                    &d.pk,
                    &d.holder,
                    &d.child,
                    &indices,
                    slw::VerificationMode::Randomized,
                    &mut r,
                )
                .map_err(err)?;
                Prepared::Slw(Box::new(state), prefix)
            }
        };
        let ns = elapsed(t);
        let handle = self.handle("prepared");
        self.pending.insert(
            handle.clone(),
            Pending {
                instance: name,
                actor: v["actor"].as_str().unwrap_or("agent").to_owned(),
                policy: p,
                k,
                state,
            },
        );
        let mut answer = json!({"handle":handle,"k":k,"timing_enabled":self.timing});
        timing(&mut answer, "preparation_ns", ns);
        Ok(answer)
    }
    fn online(&mut self, v: &Value) -> Result<Value> {
        let handle = s(v, "handle")?;
        let pending = self
            .pending
            .remove(handle)
            .ok_or("unknown or consumed prepared handle")?;
        if v["policy"] != pending.policy {
            return Err("prepared policy mismatch".into());
        }
        let context = s(v, "context")?.as_bytes().to_vec();
        if context.is_empty() {
            return Err("context empty".into());
        }
        let t = started(self.timing);
        let mut kind = "noninteractive";
        let mut session = None;
        let wires = match pending.state {
            Prepared::Darlt(p) => {
                let ablation = p.ablation;
                p.tx.send(context).map_err(err)?;
                let (result, holder, ns) = p.rx.recv().map_err(err)??;
                p.thread.join().map_err(|_| "prepare thread panicked")?;
                let Instance::Darlt(d) = self
                    .instances
                    .get_mut(&pending.instance)
                    .ok_or("instance absent")?
                else {
                    return Err("scheme mismatch".into());
                };
                if pending.actor == "agent" {
                    d.child.holder = holder;
                } else {
                    d.actors
                        .get_mut(&pending.actor)
                        .ok_or("actor absent")?
                        .holder = holder;
                }
                let serials: Vec<String> = vec![];
                let mut answer = json!({"wire_hex":result.iter().map(|b|hex(b)).collect::<Vec<_>>(),"serials":serials,"kind":kind,"k":pending.k,"timing_enabled":self.timing});
                answer["ablation"] = json!(ablation);
                answer["token_count"] = json!(result.len());
                timing(&mut answer, "online_ns", ns);
                return Ok(answer);
            }
            Prepared::Sma(prepared) => {
                let Instance::Sma(d) = self
                    .instances
                    .get(&pending.instance)
                    .ok_or("instance absent")?
                else {
                    return Err("scheme mismatch".into());
                };
                let p = sma_policy(&pending.policy)?;
                prepared
                    .into_iter()
                    .map(|x| {
                        sma::show_online_installed(&d.installed, x, &context, &p)
                            .map(|x| x.bytes())
                            .map_err(err)
                    })
                    .collect::<Result<Vec<_>>>()?
            }
            Prepared::Msb(prepared) => {
                let Instance::Msb(d) = self
                    .instances
                    .get(&pending.instance)
                    .ok_or("instance absent")?
                else {
                    return Err("scheme mismatch".into());
                };
                let (first, prover) =
                    msb::show_begin_prepared(&d.registered, *prepared, context).map_err(err)?;
                let id = self.handle("prover");
                self.provers.insert(
                    id.clone(),
                    (pending.instance.clone(), Prover::Msb(Box::new(prover))),
                );
                kind = "interactive";
                session = Some(id);
                vec![wire::encode_show_first(&first)]
            }
            Prepared::Slw(prepared, prefix) => {
                let id = self.handle("prover");
                self.provers.insert(
                    id.clone(),
                    (pending.instance.clone(), Prover::SlwFirst(prepared)),
                );
                kind = "interactive";
                session = Some(id);
                vec![prefix]
            }
        };
        let ns = elapsed(t);
        let serials: Vec<String> = vec![];
        let mut answer = json!({"wire_hex":wires.iter().map(|b|hex(b)).collect::<Vec<_>>(),"serials":serials,"kind":kind,"session":session,"k":pending.k,"timing_enabled":self.timing});
        timing(&mut answer, "online_ns", ns);
        Ok(answer)
    }
    fn verify(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        let ww = wires(v)?;
        let context = s(v, "context")?.as_bytes();
        let p = &v["policy"];
        let mut weights = rng();
        let t = started(self.timing);
        let (valid, serials, decode_ns, verify_ns) = match self.verifier_view(&name)? {
            VerifierView::Darlt(ctx) => {
                let received = ww
                    .iter()
                    .map(|w| ReceivedToken::wire_decode(ctx.parameters(), w))
                    .collect::<Result<Vec<_>>>()?;
                let decode = elapsed(t);
                let t = started(self.timing);
                let expected = policy(p)?;
                let bound = received.iter().all(|x| {
                    x.token().context == context && x.token().policy.encode() == expected.encode()
                });
                let valid =
                    bound && ctx.valid_many_received(&received, Mode::Randomized, &mut weights);
                let verify = elapsed(t);
                let serials = received
                    .iter()
                    .flat_map(|x| x.serials())
                    .map(|x| hex(&x))
                    .collect::<Vec<_>>();
                (valid, serials, decode, verify)
            }
            VerifierView::Sma(installed) => {
                let p = sma_policy(p)?;
                let received = ww
                    .iter()
                    .map(|w| {
                        sma::CheckedToken::decode_received_installed(installed, w, &p).map_err(err)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let decode = elapsed(t);
                let t = started(self.timing);
                let valid = sma::verify_random_batch_checked(
                    installed,
                    &received,
                    context,
                    &p,
                    &mut weights,
                );
                let verify = elapsed(t);
                let serials = received
                    .iter()
                    .map(|x| hex(&x.as_token().serial.to_compressed()))
                    .collect();
                (valid, serials, decode, verify)
            }
        };
        let evidence = if valid {
            let eid = self.handle("evidence");
            self.evidence.insert(
                eid.clone(),
                Evidence {
                    instance: name,
                    wires: ww,
                    context: context.to_vec(),
                    policy: p.clone(),
                },
            );
            Some(eid)
        } else {
            None
        };
        let mut answer = json!({"valid":valid,"serials":serials,"unit_count":serials.len(),"evidence_handle":evidence,"timing_enabled":self.timing});
        timing(&mut answer, "decode_ns", decode_ns);
        timing(&mut answer, "verification_ns", verify_ns);
        Ok(answer)
    }
    fn server_round(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        let session = s(v, "session_id")?.to_owned();
        let round = v["round"].as_u64().ok_or("round missing")?;
        let ww = wires(v)?;
        if ww.len() != 1 {
            return Err("one native interactive show required".into());
        }
        let b = &ww[0];
        let context = s(v, "context")?.as_bytes().to_vec();
        let p = v["policy"].clone();
        let mut live = rng();
        let mut weights = rng();
        let t = started(self.timing);
        let mut answer = match self.instances.get(&name).ok_or("instance absent")? {
            Instance::Msb(d) => {
                if round == 1 {
                    if self.verifiers.contains_key(&session) {
                        return Err("live session exists".into());
                    }
                    let disclosure = msb_disclosure(&p)?;
                    let received =
                        msb::decode_show_first_received(&d.registered, b, &disclosure, &context)
                            .map_err(err)?;
                    let decode = elapsed(t);
                    let t = started(self.timing);
                    let (c, state) = msb::show_challenge_checked(
                        &d.registered,
                        received,
                        &disclosure,
                        &context,
                        &mut live,
                    )
                    .map_err(err)?;
                    let verify = elapsed(t);
                    self.verifiers.insert(
                        session.clone(),
                        Live {
                            instance: name,
                            policy: p,
                            context,
                            state: Verifier::Msb(Box::new(state)),
                        },
                    );
                    let mut a = json!({"complete":false,"wire_hex":[hex(&c.bytes())],"round":1});
                    timing(&mut a, "decode_ns", decode);
                    timing(&mut a, "verification_ns", verify);
                    a
                } else if round == 2 {
                    let saved = self
                        .verifiers
                        .remove(&session)
                        .ok_or("live session missing")?;
                    if saved.instance != name || saved.policy != p || saved.context != context {
                        return Err("session binding".into());
                    }
                    let Verifier::Msb(state) = saved.state else {
                        return Err("session scheme".into());
                    };
                    let received = msb::decode_show_response_received(&state, b).map_err(err)?;
                    let decode = elapsed(t);
                    let t = started(self.timing);
                    let frozen =
                        msb::freeze_show_received(&d.registered, *state, received).map_err(err)?;
                    let valid = msb::verify_frozen_show(
                        &d.registered,
                        &frozen,
                        baseline_core::pairing_verify::Mode::Randomized,
                        &mut weights,
                    );
                    let verify = elapsed(t);
                    let mut a = json!({"complete":true,"valid":valid,"serials":[],"unit_count":0,"round":2});
                    timing(&mut a, "decode_ns", decode);
                    timing(&mut a, "verification_ns", verify);
                    a
                } else {
                    return Err("MSB round".into());
                }
            }
            Instance::Slw(d) => {
                if round == 1 {
                    if self.verifiers.contains_key(&session) {
                        return Err("live session exists".into());
                    }
                    let (indices, values) = slw_disclosure(&p)?;
                    let received = slw::decode_show_prefix_received(&d.pk, b, &indices, &values)
                        .map_err(err)?;
                    let decode = elapsed(t);
                    let t = started(self.timing);
                    let (state, c) = slw::show_verifier_begin_received_profile_rngs(
                        &d.pk,
                        received,
                        slw::VerificationMode::Randomized,
                        &mut weights,
                        &mut live,
                    )
                    .map_err(err)?;
                    let verify = elapsed(t);
                    self.verifiers.insert(
                        session.clone(),
                        Live {
                            instance: name,
                            policy: p,
                            context,
                            state: Verifier::SlwFirst(Box::new(state)),
                        },
                    );
                    let mut a = json!({"complete":false,"wire_hex":[hex(&c)],"round":1});
                    timing(&mut a, "decode_ns", decode);
                    timing(&mut a, "verification_ns", verify);
                    a
                } else {
                    let saved = self
                        .verifiers
                        .remove(&session)
                        .ok_or("live session missing")?;
                    if saved.instance != name || saved.policy != p || saved.context != context {
                        return Err("session binding".into());
                    }
                    match saved.state {
                        Verifier::SlwFirst(state) if round == 2 => {
                            let received =
                                slw::decode_show_first_received(&state, b).map_err(err)?;
                            let decode = elapsed(t);
                            let t = started(self.timing);
                            let (state, c) = slw::show_verifier_challenge_received_profile(
                                *state, received, &mut live,
                            )
                            .map_err(err)?;
                            let verify = elapsed(t);
                            self.verifiers.insert(
                                session.clone(),
                                Live {
                                    instance: name,
                                    policy: p,
                                    context,
                                    state: Verifier::SlwLast(Box::new(state)),
                                },
                            );
                            let mut a = json!({"complete":false,"wire_hex":[hex(&c)],"round":2});
                            timing(&mut a, "decode_ns", decode);
                            timing(&mut a, "verification_ns", verify);
                            a
                        }
                        Verifier::SlwLast(state) if round == 3 => {
                            let received =
                                slw::decode_show_final_received(&state, b).map_err(err)?;
                            let decode = elapsed(t);
                            let t = started(self.timing);
                            let valid = slw::show_verifier_finish_many_received_profile(
                                vec![(*state, received)],
                                slw::VerificationMode::Randomized,
                                &mut weights,
                            )
                            .map_err(err)?;
                            let verify = elapsed(t);
                            let mut a = json!({"complete":true,"valid":valid,"serials":[],"unit_count":0,"round":3});
                            timing(&mut a, "decode_ns", decode);
                            timing(&mut a, "verification_ns", verify);
                            a
                        }
                        _ => return Err("SLW round".into()),
                    }
                }
            }
            _ => return Err("noninteractive scheme".into()),
        };
        answer["timing_enabled"] = json!(self.timing);
        Ok(answer)
    }
    fn client_round(&mut self, v: &Value) -> Result<Value> {
        let session = s(v, "session")?.to_owned();
        let (name, prover) = self
            .provers
            .remove(&session)
            .ok_or("prover missing or consumed")?;
        let ww = wires(v)?;
        if ww.len() != 1 {
            return Err("one interactive challenge".into());
        }
        let mut r = rng();
        let t = started(self.timing);
        let (bytes, next) = match prover {
            Prover::Msb(state) => {
                let c = pok::Challenge::from_bytes(&ww[0]).map_err(err)?;
                let response = msb::show_respond(*state, c).map_err(err)?;
                (response.bytes(), None)
            }
            Prover::SlwFirst(mut state) => {
                let Instance::Slw(d) = self.instances.get(&name).ok_or("instance absent")? else {
                    return Err("scheme".into());
                };
                let (state, bytes) =
                    slw::show_holder_first(&d.pk, &mut state, &ww[0], &mut r).map_err(err)?;
                (bytes, Some(Prover::SlwLast(Box::new(state))))
            }
            Prover::SlwLast(state) => {
                (slw::show_holder_respond(*state, &ww[0]).map_err(err)?, None)
            }
        };
        if let Some(state) = next {
            self.provers.insert(session.clone(), (name, state));
        }
        let mut answer =
            json!({"wire_hex":[hex(&bytes)],"session":session,"timing_enabled":self.timing});
        timing(&mut answer, "online_ns", elapsed(t));
        Ok(answer)
    }
    fn judge(&mut self, v: &Value) -> Result<Value> {
        let a = self
            .evidence
            .get(s(v, "evidence_a")?)
            .ok_or("evidence A missing")?;
        let b = self
            .evidence
            .get(s(v, "evidence_b")?)
            .ok_or("evidence B missing")?;
        if a.instance != b.instance {
            return Err("different instances".into());
        }
        let mut weights = rng();
        let result = match self.verifier_view(&a.instance)? {
            VerifierView::Darlt(ctx) => {
                let aa = a
                    .wires
                    .iter()
                    .map(|w| ReceivedToken::wire_decode(ctx.parameters(), w))
                    .collect::<Result<Vec<_>>>()?;
                let bb = b
                    .wires
                    .iter()
                    .map(|w| ReceivedToken::wire_decode(ctx.parameters(), w))
                    .collect::<Result<Vec<_>>>()?;
                let mut result = None;
                for x in &aa {
                    for y in &bb {
                        for i in 0..x.token().units.len() {
                            for j in 0..y.token().units.len() {
                                if let Some((kind, key)) =
                                    ctx.judge_received(x, i, y, j, Mode::Randomized, &mut weights)
                                {
                                    result = Some((
                                        if kind == spend::Responsibility::DoubleUse {
                                            "agent"
                                        } else {
                                            "user"
                                        },
                                        hashkey(key),
                                    ));
                                    break;
                                }
                            }
                        }
                    }
                }
                result
            }
            VerifierView::Sma(installed) => {
                let pa = sma_policy(&a.policy)?;
                let pb = sma_policy(&b.policy)?;
                let aa = a
                    .wires
                    .iter()
                    .map(|w| {
                        sma::CheckedToken::decode_received_installed(installed, w, &pa).map_err(err)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let bb = b
                    .wires
                    .iter()
                    .map(|w| {
                        sma::CheckedToken::decode_received_installed(installed, w, &pb).map_err(err)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let valid =
                    sma::verify_random_batch_checked(installed, &aa, &a.context, &pa, &mut weights)
                        && sma::verify_random_batch_checked(
                            installed,
                            &bb,
                            &b.context,
                            &pb,
                            &mut weights,
                        );
                let mut result = None;
                if valid {
                    for x in &aa {
                        for y in &bb {
                            if let Some(key) = sma::identify_valid_records(
                                &sma::Record {
                                    token: x.as_token().clone(),
                                    context: a.context.clone(),
                                    policy: pa.clone(),
                                },
                                &sma::Record {
                                    token: y.as_token().clone(),
                                    context: b.context.clone(),
                                    policy: pb.clone(),
                                },
                            ) {
                                result = Some(("user", hashkey(key)));
                            }
                        }
                    }
                }
                result
            }
        };
        Ok(match result {
            Some((classification, key)) => {
                json!({"classification":classification,"public_key":key})
            }
            None => json!({"classification":"none"}),
        })
    }
    fn reallocate(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        let actor = s(v, "actor")?.to_owned();
        if actor != "second" && actor != "user" {
            return Err("reallocation actor must be second or user".into());
        }
        let Instance::Darlt(d) = self.instances.get_mut(&name).ok_or("instance absent")? else {
            return Err("no native anonymous pool-allocation interface".into());
        };
        let ctx = ProtocolContext::new(d.pp.clone(), d.ip.clone())?;
        let mut wallet = d.wallet.clone();
        let mut r = rng();
        let (child, key) = if actor == "user" {
            (
                ctx.self_derive(
                    &mut wallet,
                    b"adversarial repeated self allocation",
                    &d.pools,
                    &mut r,
                )?,
                d.owner,
            )
        } else {
            let key = S::random(&mut r);
            let req =
                ctx.delegation_request(b"adversarial repeated remote allocation", key, &mut r)?;
            let delivery = ctx.delegate(&mut wallet, &req, &d.pools, &d.delta, &mut r)?;
            (
                ctx.receive(&delivery, key, None, Mode::Randomized, &mut r)?,
                key,
            )
        };
        d.actors.insert(actor.clone(), child);
        Ok(
            json!({"actor":actor,"public_key":hashkey(G1::generator()*key),"pools":d.pools,"adversarial_owner_state_fork":true}),
        )
    }
    fn attack_material(&mut self, v: &Value) -> Result<Value> {
        let name = id(v)?;
        let attack = s(v, "attack")?;
        let mut r = rng();
        match self.instances.get_mut(&name).ok_or("instance absent")? {
            Instance::Darlt(d) => {
                if attack == "stolen_without_key" {
                    let ctx = ProtocolContext::new(d.pp.clone(), d.ip.clone())?;
                    let request = ctx.delegation_request(b"stolen-check", d.agent, &mut r)?;
                    let mut wallet = d.wallet.clone();
                    let delivery =
                        ctx.delegate(&mut wallet, &request, &d.pools, &d.delta, &mut r)?;
                    let wrong = S::random(&mut r);
                    return Ok(
                        json!({"blocked":ctx.receive(&delivery,wrong,None,Mode::Randomized,&mut r).is_err(),"reason":"recipient secret does not match authorization"}),
                    );
                }
                Err("attack not implemented".into())
            }
            Instance::Sma(_) => Ok(
                json!({"blocked":false,"reason":"shared original wallet includes the native holder witness; no agent key exists"}),
            ),
            _ => Err("attack not applicable".into()),
        }
    }
}
fn p_to_json(v: &Value) -> Value {
    v["policy"].clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    fn p(index: usize) -> Value {
        json!({"period":1,"required_attrs":[{"index":index,"value":1}]})
    }
    fn no_clock(v: &Value) {
        match v {
            Value::Object(m) => {
                for (k, v) in m {
                    assert!(!k.ends_with("_ns"), "untimed duration {k}");
                    no_clock(v)
                }
            }
            Value::Array(a) => a.iter().for_each(no_clock),
            _ => {}
        }
    }
    fn call(b: &mut Bridge, v: Value) -> Value {
        let out = b.command(v).unwrap();
        no_clock(&out);
        out
    }
    fn show(
        b: &mut Bridge,
        name: &str,
        k: usize,
        actor: &str,
        context: &str,
        policy: Value,
    ) -> Value {
        let prepared = call(
            b,
            json!({"op":"prepare","instance":name,"k":k,"actor":actor,"policy":policy}),
        );
        call(
            b,
            json!({"op":"online","handle":prepared["handle"],"context":context,"policy":policy}),
        )
    }
    fn verify(b: &mut Bridge, name: &str, token: &Value, context: &str, policy: Value) -> Value {
        call(
            b,
            json!({"op":"verify","instance":name,"wire_hex":token["wire_hex"],"context":context,"policy":policy}),
        )
    }
    fn public_packet_only(v: &Value) {
        match v {
            Value::Object(m) => {
                for (key, value) in m {
                    assert!(!matches!(
                        key.as_str(),
                        "sk" | "secret"
                            | "wallet"
                            | "holder"
                            | "witness"
                            | "owner"
                            | "agent"
                            | "trapdoor"
                    ));
                    public_packet_only(value);
                }
            }
            Value::Array(a) => a.iter().for_each(public_packet_only),
            _ => {}
        }
    }
    #[test]
    fn public_only_dual_role_darlt_verifier_and_judge() {
        let mut agent = Bridge::new(false);
        let mut server = Bridge::new(false);
        call(&mut agent, json!({"op":"set_role","role":"agent"}));
        call(&mut server, json!({"op":"set_role","role":"server"}));
        call(&mut agent, json!({"op":"issue_parent","instance":"parent"}));
        let first = call(
            &mut agent,
            json!({"op":"delegate_child","parent":"parent","instance":"d0","pools":[0],"allowed_attrs":[0,1,2,3]}),
        );
        call(
            &mut agent,
            json!({"op":"delegate_child","parent":"parent","instance":"d1","pools":[1],"allowed_attrs":[0,1,2,3]}),
        );
        for name in ["d0", "d1"] {
            let package = call(&mut agent, json!({"op":"export_verifier","instance":name}));
            public_packet_only(&package);
            let installed = call(
                &mut server,
                json!({"op":"install_verifier","package":package}),
            );
            assert_eq!(installed["cached"], name == "d1");
            assert_eq!(
                call(
                    &mut server,
                    json!({"op":"install_verifier","package":package})
                )["idempotent"],
                true
            );
            let mut bad = package.clone();
            bad["material"]["public_parameters"]["id"] = json!("00".repeat(32));
            assert!(server
                .command(json!({"op":"install_verifier","package":bad}))
                .is_err());
        }
        let mut evidence = vec![];
        for (n, ablation) in [("first", false), ("second", true)] {
            let prep = call(
                &mut agent,
                json!({"op":"prepare","instance":"d0","k":2,"positions":[0,1],"policy":p(1),"ablation":ablation}),
            );
            let token = call(
                &mut agent,
                json!({"op":"online","handle":prep["handle"],"context":n,"policy":p(1)}),
            );
            let accepted = verify(&mut server, "d0", &token, n, p(1));
            assert_eq!(accepted["valid"], true);
            assert_eq!(accepted["unit_count"], 2);
            assert_eq!(
                verify(&mut server, "d0", &token, "wrong request", p(1))["valid"],
                false
            );
            assert_eq!(verify(&mut server, "d0", &token, n, p(2))["valid"], false);
            let mut malformed = token.clone();
            malformed["wire_hex"][0] = json!("00");
            assert!(server.command(json!({"op":"verify","instance":"d0","wire_hex":malformed["wire_hex"],"context":n,"policy":p(1)})).is_err());
            evidence.push(accepted["evidence_handle"].clone());
        }
        let verdict = call(
            &mut server,
            json!({"op":"judge","evidence_a":evidence[0],"evidence_b":evidence[1]}),
        );
        assert_eq!(verdict["classification"], "agent");
        assert_eq!(verdict["public_key"], first["agent_public_key"]);
        call(
            &mut agent,
            json!({"op":"reallocate","instance":"d0","actor":"user"}),
        );
        let overlap = show(&mut agent, "d0", 1, "user", "owner overlap", p(1));
        let owner_evidence = verify(&mut server, "d0", &overlap, "owner overlap", p(1));
        assert_eq!(owner_evidence["valid"], true);
        assert_eq!(
            call(
                &mut server,
                json!({"op":"judge","evidence_a":evidence[0],"evidence_b":owner_evidence["evidence_handle"]})
            )["classification"],
            "user"
        );
        assert!(server
            .command(json!({"op":"prepare","instance":"d0","k":1,"policy":p(1)}))
            .is_err());
        assert!(server
            .command(json!({"op":"init","scheme":"DARLT","instance":"private"}))
            .is_err());
        assert!(agent.command(json!({"op":"verify"})).is_err());
        assert!(agent.command(json!({"op":"judge"})).is_err());
        assert!(server
            .command(json!({"op":"set_role","role":"direct"}))
            .is_err());
        let meta = call(&mut server, json!({"op":"metadata"}));
        assert_eq!(meta["role"], "server");
        assert_eq!(meta["private_instance_count"], 0);
        assert_eq!(meta["shared_parent_count"], 0);
        assert_eq!(meta["darlt_issuer_issue_calls_total"], 0);
        assert_eq!(meta["public_verifier_instance_count"], 2);
        assert_eq!(meta["public_material_count"], 1);
        assert_eq!(meta["public_only_installed"], true);
        assert!(server.pending.is_empty());
    }
    #[test]
    fn public_only_sma_verifier_and_stolen_wallet_judge() {
        let mut agent = Bridge::new(false);
        let mut server = Bridge::new(false);
        call(&mut agent, json!({"op":"set_role","role":"agent"}));
        call(&mut server, json!({"op":"set_role","role":"server"}));
        let init = call(
            &mut agent,
            json!({"op":"init","scheme":"SMA²RT","instance":"s"}),
        );
        let package = call(&mut agent, json!({"op":"export_verifier","instance":"s"}));
        public_packet_only(&package);
        call(
            &mut server,
            json!({"op":"install_verifier","package":package}),
        );
        let mut evidence = vec![];
        for nonce in ["honest holder", "stolen holder"] {
            let token = show(&mut agent, "s", 2, "agent", nonce, p(1));
            let accepted = verify(&mut server, "s", &token, nonce, p(1));
            assert_eq!(accepted["valid"], true);
            assert_eq!(accepted["unit_count"], 2);
            assert_eq!(
                verify(&mut server, "s", &token, "wrong context", p(1))["valid"],
                false
            );
            evidence.push(accepted["evidence_handle"].clone());
        }
        let verdict = call(
            &mut server,
            json!({"op":"judge","evidence_a":evidence[0],"evidence_b":evidence[1]}),
        );
        assert_eq!(verdict["classification"], "user");
        assert_eq!(verdict["public_key"], init["user_public_key"]);
        assert!(server.instances.is_empty() && server.parents.is_empty());
    }
    #[test]
    fn shared_issuance_twenty_children_and_global_positions() {
        let mut b = Bridge::new(false);
        let parent = call(&mut b, json!({"op":"issue_parent","instance":"shared"}));
        assert_eq!(parent["issuer_issue_calls"], 1);
        let mut recipients = std::collections::BTreeSet::new();
        for i in 0..20 {
            let pools = if i < 10 {
                vec![i]
            } else {
                (10 + (i - 10) * 4..14 + (i - 10) * 4).collect::<Vec<_>>()
            };
            let child = call(
                &mut b,
                json!({"op":"delegate_child","parent":"shared",
                "instance":format!("child-{i}"),"pools":pools,"allowed_attrs":[0,1,2,3,4,5]}),
            );
            assert_eq!(child["issuer_issue_calls"], 1);
            assert_eq!(child["darlt_issuer_issue_calls_total"], 1);
            assert_eq!(child["user_public_key"], parent["user_public_key"]);
            assert_eq!(child["credential_id"], parent["credential_id"]);
            assert_eq!(
                child["issuer_public_key_id"],
                parent["issuer_public_key_id"]
            );
            assert_eq!(
                child["public_parameters_id"],
                parent["public_parameters_id"]
            );
            assert_eq!(child["delegated_units"], if i < 10 { 16 } else { 64 });
            assert!(recipients.insert(child["agent_public_key"].as_str().unwrap().to_owned()));
        }
        assert_eq!(recipients.len(), 20);
        assert!(b
            .command(json!({"op":"issue_parent","instance":"shared"}))
            .is_err());
        assert!(b
            .command(
                json!({"op":"delegate_child","parent":"shared","instance":"overlap",
            "pools":[49],"allowed_attrs":[0,1]})
            )
            .is_err());
        assert!(b
            .command(json!({"op":"prepare","instance":"child-10","k":1,
            "positions":[0],"policy":p(1)}))
            .is_err());
        let prepared = call(
            &mut b,
            json!({"op":"prepare","instance":"child-10","k":2,
            "positions":[160,176],"policy":p(1)}),
        );
        let token = call(
            &mut b,
            json!({"op":"online","handle":prepared["handle"],
            "context":"global coordinates cross pool","policy":p(1)}),
        );
        let verdict = verify(
            &mut b,
            "child-10",
            &token,
            "global coordinates cross pool",
            p(1),
        );
        assert_eq!(verdict["valid"], true);
        assert_eq!(verdict["unit_count"], 2);
        let meta = call(&mut b, json!({"op":"metadata"}));
        assert_eq!(meta["darlt_issuer_issue_calls_total"], 1);
        assert_eq!(meta["shared_parent_count"], 1);
    }

    #[test]
    fn shared_parent_scalar_ablation_keeps_native_single_unit_tokens() {
        let mut b = Bridge::new(false);
        call(&mut b, json!({"op":"issue_parent","instance":"parent"}));
        call(
            &mut b,
            json!({"op":"delegate_child","parent":"parent","instance":"child",
            "pools":[7],"allowed_attrs":[0,1,2,3]}),
        );
        for ablation in [false, true] {
            let prepared = call(
                &mut b,
                json!({"op":"prepare","instance":"child","k":2,
                "positions":[112,113],"policy":p(1),"ablation":ablation}),
            );
            assert_eq!(prepared["ablation"], ablation);
            let token = call(
                &mut b,
                json!({"op":"online","handle":prepared["handle"],
                "context":"shared scalar variant","policy":p(1)}),
            );
            assert_eq!(token["ablation"], ablation);
            assert_eq!(
                token["wire_hex"].as_array().unwrap().len(),
                if ablation { 2 } else { 1 }
            );
            assert_eq!(
                verify(&mut b, "child", &token, "shared scalar variant", p(1))["valid"],
                true
            );
        }
        assert_eq!(
            call(&mut b, json!({"op":"metadata"}))["darlt_issuer_issue_calls_total"],
            1
        );
    }

    #[test]
    fn darlt_native_boundaries_and_adjudication() {
        let mut b = Bridge::new(false);
        let init = call(&mut b, json!({"op":"init","scheme":"DARLT","instance":"d"}));
        for k in [1, 8] {
            let t = show(&mut b, "d", k, "agent", "good context", p(1));
            assert_eq!(t["wire_hex"].as_array().unwrap().len(), 1);
            let verified = verify(&mut b, "d", &t, "good context", p(1));
            assert_eq!(verified["valid"], true);
            assert_eq!(verified["unit_count"], k);
            assert_eq!(
                verify(&mut b, "d", &t, "changed context", p(1))["valid"],
                false
            );
            assert_eq!(
                verify(&mut b, "d", &t, "good context", p(2))["valid"],
                false
            );
        }
        for index in [4, 6] {
            assert!(b
                .command(json!({"op":"prepare","instance":"d","k":1,"policy":p(index)}))
                .is_err());
        }
        assert!(b
            .command(json!({"op":"prepare","instance":"d","k":1,"positions":[64],"policy":p(1)}))
            .is_err());
        assert_eq!(
            call(
                &mut b,
                json!({"op":"attack_material","instance":"d","attack":"stolen_without_key"})
            )["blocked"],
            true
        );
        let a = show(&mut b, "d", 1, "agent", "verifier A unique nonce", p(1));
        let av = verify(&mut b, "d", &a, "verifier A unique nonce", p(1));
        let c = show(&mut b, "d", 1, "agent", "verifier B unique nonce", p(1));
        let cv = verify(&mut b, "d", &c, "verifier B unique nonce", p(1));
        assert_eq!(av["valid"], true);
        assert_eq!(cv["valid"], true);
        let verdict = call(
            &mut b,
            json!({"op":"judge","evidence_a":av["evidence_handle"],"evidence_b":cv["evidence_handle"]}),
        );
        assert_eq!(verdict["classification"], "agent");
        assert_eq!(verdict["public_key"], init["agent_public_key"]);
        for actor in ["second", "user"] {
            call(
                &mut b,
                json!({"op":"reallocate","instance":"d","actor":actor}),
            );
            let t = show(&mut b, "d", 1, actor, "overlap separate verifier", p(1));
            let tv = verify(&mut b, "d", &t, "overlap separate verifier", p(1));
            assert_eq!(tv["valid"], true);
            let verdict = call(
                &mut b,
                json!({"op":"judge","evidence_a":av["evidence_handle"],"evidence_b":tv["evidence_handle"]}),
            );
            assert_eq!(verdict["classification"], "user");
            assert_eq!(verdict["public_key"], init["user_public_key"]);
        }
    }
    #[test]
    fn scalar_ablation_is_eight_real_single_unit_tokens() {
        let mut b = Bridge::new(false);
        call(
            &mut b,
            json!({"op":"init","scheme":"DARLT-ablation","instance":"da"}),
        );
        let t = show(&mut b, "da", 8, "agent", "ablation request", p(3));
        assert_eq!(t["wire_hex"].as_array().unwrap().len(), 8);
        let verified = verify(&mut b, "da", &t, "ablation request", p(3));
        assert_eq!(verified["valid"], true);
        assert_eq!(verified["unit_count"], 8);
    }
    #[test]
    fn shared_sma_native_tokens_and_stolen_wallet() {
        let mut b = Bridge::new(false);
        let init = call(
            &mut b,
            json!({"op":"init","scheme":"SMA²RT","instance":"s"}),
        );
        for k in [1, 8] {
            let t = show(&mut b, "s", k, "stolen", "SMA request", p(3));
            assert_eq!(t["wire_hex"].as_array().unwrap().len(), k);
            assert_eq!(verify(&mut b, "s", &t, "SMA request", p(3))["valid"], true);
            assert_eq!(
                verify(&mut b, "s", &t, "wrong context", p(3))["valid"],
                false
            );
        }
        let a = show(&mut b, "s", 1, "agent", "SMA first", p(1));
        let av = verify(&mut b, "s", &a, "SMA first", p(1));
        let c = show(&mut b, "s", 1, "stolen", "SMA second", p(1));
        let cv = verify(&mut b, "s", &c, "SMA second", p(1));
        let verdict = call(
            &mut b,
            json!({"op":"judge","evidence_a":av["evidence_handle"],"evidence_b":cv["evidence_handle"]}),
        );
        assert_eq!(verdict["classification"], "user");
        assert_eq!(verdict["public_key"], init["user_public_key"]);
    }
    #[test]
    fn native_interactions_are_live_and_single_show_for_cost_eight() {
        let mut b = Bridge::new(false);
        for (scheme, name, rounds) in [("MSB+23", "m", 2), ("SLW+25", "l", 3)] {
            call(&mut b, json!({"op":"init","scheme":scheme,"instance":name}));
            for k in [1, 8] {
                let pp = p(if k == 1 { 1 } else { 3 });
                let token = show(&mut b, name, k, "agent", "interactive request", pp.clone());
                assert_eq!(token["wire_hex"].as_array().unwrap().len(), 1);
                let mut message = token["wire_hex"].clone();
                let prover = token["session"].clone();
                let sid = format!("{name}-{k}");
                for round in 1..=rounds {
                    let response = call(
                        &mut b,
                        json!({"op":"server_round","instance":name,"session_id":sid,"round":round,"wire_hex":message,"context":"interactive request","policy":pp}),
                    );
                    if round == rounds {
                        assert_eq!(response["complete"], true);
                        assert_eq!(response["valid"], true);
                    } else {
                        let response = call(
                            &mut b,
                            json!({"op":"client_round","session":prover,"wire_hex":response["wire_hex"]}),
                        );
                        message = response["wire_hex"].clone();
                    }
                }
                assert!(b
                    .command(json!({"op":"client_round","session":prover,"wire_hex":["00"]}))
                    .is_err());
            }
        }
    }
    #[test]
    fn timing_requires_window_authorization() {
        let mut b = Bridge::new(false);
        assert!(b.command(json!({"op":"metadata","timing":true})).is_err());
        let out = b.command(json!({"op":"metadata"})).unwrap();
        assert_eq!(out["clock_free"], true);
    }

    #[test]
    fn malformed_hex_is_rejected_without_panicking() {
        for value in ["🧪", "x0", "0", "é"] {
            assert!(unhex(value).is_err());
        }
    }

    #[cfg(feature = "subgroup-audit")]
    #[test]
    fn verification_checks_exactly_the_received_decoder_elements() {
        use baseline_core::subgroup_audit::collect;
        fn compare(
            expected: baseline_core::subgroup_audit::Audit,
            actual: baseline_core::subgroup_audit::Audit,
            label: &str,
        ) {
            assert!(expected.enabled && actual.enabled);
            assert!(!expected.events.is_empty(), "empty decoder audit {label}");
            assert_eq!(
                serde_json::to_value(&expected.events).unwrap(),
                serde_json::to_value(&actual.events).unwrap(),
                "extra or missing subgroup checks: {label}"
            );
            println!(
                "SG_AUDIT {label}: {} strict-decoder events, zero extra verification events",
                actual.events.len()
            );
        }
        let mut b = Bridge::new(false);
        for (scheme, name) in [
            ("DARLT", "d"),
            ("DARLT-ablation", "da"),
            ("SMA²RT", "s"),
            ("MSB+23", "m"),
            ("SLW+25", "l"),
        ] {
            call(&mut b, json!({"op":"init","scheme":scheme,"instance":name}));
            let mut public_server = Bridge::new(false);
            if matches!(scheme, "DARLT" | "DARLT-ablation" | "SMA²RT") {
                call(&mut public_server, json!({"op":"set_role","role":"server"}));
                let package = call(&mut b, json!({"op":"export_verifier","instance":name}));
                call(
                    &mut public_server,
                    json!({"op":"install_verifier","package":package}),
                );
            }
            for k in [1, 8] {
                let pp = p(if k == 1 { 1 } else { 3 });
                let token = show(&mut b, name, k, "agent", "audit context", pp.clone());
                let mut message = token["wire_hex"].clone();
                if token["kind"] == "noninteractive" {
                    let bytes = wires(&token).unwrap();
                    let (_, expected) = collect(|| match b.instances.get(name).unwrap() {
                        Instance::Darlt(d) => {
                            for w in &bytes {
                                ReceivedToken::wire_decode(d.ctx.parameters(), w).unwrap();
                            }
                        }
                        Instance::Sma(d) => {
                            for w in &bytes {
                                sma::CheckedToken::decode_received_installed(
                                    &d.installed,
                                    w,
                                    &sma_policy(&pp).unwrap(),
                                )
                                .unwrap();
                            }
                        }
                        _ => unreachable!(),
                    });
                    let (result, actual) =
                        collect(|| verify(&mut b, name, &token, "audit context", pp.clone()));
                    assert_eq!(result["valid"], true);
                    let (public_result, public_actual) = collect(|| {
                        verify(
                            &mut public_server,
                            name,
                            &token,
                            "audit context",
                            pp.clone(),
                        )
                    });
                    assert_eq!(public_result["valid"], true);
                    assert_eq!(
                        serde_json::to_value(&expected.events).unwrap(),
                        serde_json::to_value(&public_actual.events).unwrap(),
                        "public verifier extra/missing subgroup checks: {name}/k{k}"
                    );
                    compare(expected, actual, &format!("{name}/k{k}"));
                } else {
                    let rounds = if name == "m" { 2 } else { 3 };
                    let sid = format!("audit-{name}-{k}");
                    for round in 1..=rounds {
                        let bytes = unhex(message[0].as_str().unwrap()).unwrap();
                        let (_, expected) = collect(|| match b.instances.get(name).unwrap() {
                            Instance::Msb(d) if round == 1 => {
                                msb::decode_show_first_received(
                                    &d.registered,
                                    &bytes,
                                    &msb_disclosure(&pp).unwrap(),
                                    b"audit context",
                                )
                                .unwrap();
                            }
                            Instance::Msb(_) => {
                                let Verifier::Msb(state) = &b.verifiers.get(&sid).unwrap().state
                                else {
                                    unreachable!()
                                };
                                msb::decode_show_response_received(state, &bytes).unwrap();
                            }
                            Instance::Slw(d) if round == 1 => {
                                let (indices, values) = slw_disclosure(&pp).unwrap();
                                slw::decode_show_prefix_received(&d.pk, &bytes, &indices, &values)
                                    .unwrap();
                            }
                            Instance::Slw(_) if round == 2 => {
                                let Verifier::SlwFirst(state) =
                                    &b.verifiers.get(&sid).unwrap().state
                                else {
                                    unreachable!()
                                };
                                slw::decode_show_first_received(state, &bytes).unwrap();
                            }
                            Instance::Slw(_) => {
                                let Verifier::SlwLast(state) =
                                    &b.verifiers.get(&sid).unwrap().state
                                else {
                                    unreachable!()
                                };
                                slw::decode_show_final_received(state, &bytes).unwrap();
                            }
                            _ => unreachable!(),
                        });
                        let (response, actual) = collect(|| {
                            call(
                                &mut b,
                                json!({"op":"server_round","instance":name,"session_id":sid,"round":round,"wire_hex":message,"context":"audit context","policy":pp}),
                            )
                        });
                        // Scalar-only last rounds can legitimately contain no group element.
                        if expected.events.is_empty() {
                            assert!(actual.events.is_empty());
                        } else {
                            compare(expected, actual, &format!("{name}/k{k}/round{round}"));
                        }
                        if round == rounds {
                            assert_eq!(response["valid"], true);
                        } else {
                            message = call(&mut b, json!({"op":"client_round","session":token["session"],"wire_hex":response["wire_hex"]}))["wire_hex"].clone();
                        }
                    }
                }
            }
        }
    }
}
