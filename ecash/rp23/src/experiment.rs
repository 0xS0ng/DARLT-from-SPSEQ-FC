//! Native role/stage callbacks for the common interleaved experiment worker.
use crate::{api::*, backend::VerificationMode, shared_runtime::*};
use darlt_spseq_fc::{
    batch_runtime::{self as rt, Adapter, Mode},
    common::spent::{Identifier, SpentSnapshot, SpentStore},
    experiment::{Action, BoundaryClock, Job, Worker},
    sampling::SampleClass,
};
use rand::{
    rngs::{OsRng, StdRng},
    RngCore, SeedableRng,
};
use serde_json::{json, Value};
use std::{cell::RefCell, rc::Rc};
const K: [u64; 9] = [1, 2, 4, 8, 16, 32, 64, 96, 128];
const M: [u8; 16] = [7; 16];
fn verifier_rng(clock: &BoundaryClock, reproducible_seed: u64) -> Result<StdRng> {
    if clock.mode() == darlt_spseq_fc::experiment::RunMode::Formal {
        let mut seed = [0u8; 32];
        OsRng.try_fill_bytes(&mut seed).map_err(|e| e.to_string())?;
        Ok(StdRng::from_seed(seed))
    } else {
        Ok(StdRng::seed_from_u64(reproducible_seed))
    }
}
fn divisible_parameters(capacity: u64) -> crate::divisible::setup::Parameters {
    crate::divisible::setup::Parameters::new_with_capacity(
        crate::divisible::setup::GroupParameters::new().expect("fixed group parameters"),
        capacity,
    )
}
#[derive(Clone)]
struct Selection {
    scheme: bool,
    phase: &'static str,
    k: u64,
    random: bool,
    cold: bool,
    prior: bool,
}
fn native_capture<T>(
    clock: &mut BoundaryClock,
    id: Option<&str>,
    run: impl FnOnce() -> Result<T>,
) -> Result<T> {
    if let Some(id) = id {
        clock.capture(id, |c| c.measure(run))
    } else {
        run()
    }
}
macro_rules! fixture_pool {
    ($fixture:ident,$context:ty,$wallet:ty,$verifier:ident,$idbytes:expr) => {
        struct $fixture {
            wallet: $wallet,
            fresh: SpentSnapshot,
            prior: Option<($wallet, SpentSnapshot)>,
        }
        impl $fixture {
            fn new(ctx: &$context, wallet: $wallet) -> Result<Self> {
                let adapter = $verifier::new(ctx, M);
                let store =
                    SpentStore::with_preexisting_records(10000, adapter.namespace(), $idbytes)
                        .map_err(|e| e.to_string())?;
                Ok(Self {
                    wallet,
                    fresh: store.snapshot().map_err(|e| e.to_string())?,
                    prior: None,
                })
            }
            fn branch(&mut self, ctx: &$context, prior: bool) -> Result<($wallet, SpentSnapshot)> {
                if !prior {
                    return Ok((self.wallet.fixture_branch(), self.fresh.clone()));
                }
                if self.prior.is_none() {
                    let mut w = self.wallet.fixture_branch();
                    let p = ctx
                        .prepare(&mut w, 512, M)?
                        .finish(PayInfo::new(M, [254; 16]))?;
                    let p = ctx.check_payment(p)?;
                    let adapter = $verifier::new(ctx, M);
                    let store = SpentStore::from_snapshot(&self.fresh);
                    rt::verify_and_record(
                        &adapter,
                        &[p],
                        b"genuine-prior512",
                        b"accepted",
                        &store,
                        Mode::Specification,
                        &mut StdRng::seed_from_u64(512),
                    )
                    .map_err(|e| e.to_string())?;
                    self.prior = Some((w, store.snapshot().map_err(|e| e.to_string())?));
                }
                let (w, s) = self.prior.as_ref().unwrap();
                Ok((w.fixture_branch(), s.clone()))
            }
        }
    };
}
fixture_pool!(CompactFixture, Compact, CompactWallet, CompactVerifier, 48);
fixture_pool!(
    DivisibleFixture,
    Divisible,
    DivisibleWallet,
    DivisibleVerifier,
    288
);
pub struct Factory {
    c: Rc<RefCell<Rc<Compact>>>,
    d: Rc<RefCell<Rc<Divisible>>>,
    c_fixture: Rc<RefCell<Option<CompactFixture>>>,
    c_bytes: Rc<RefCell<Option<Value>>>,
    d_bytes: Rc<RefCell<Option<Value>>>,
    d_fixture: Rc<RefCell<Option<DivisibleFixture>>>,
    capacity: u64,
    jobs: Vec<(Job, Selection)>,
}
pub fn new() -> Result<Factory> {
    Factory::with_capacity(1024)
}
impl Factory {
    pub fn with_capacity(capacity: u64) -> Result<Self> {
        let c = Rc::new(Compact::new(capacity)?);
        let d = Rc::new(Divisible::new(capacity)?);
        d.install_public_pairing_bases(
            &K.into_iter().filter(|k| *k <= capacity).collect::<Vec<_>>(),
        );
        let mut jobs = vec![];
        for scheme in [false, true] {
            let name = if scheme { "RP23-D" } else { "RP23-C" };
            for (phase, role) in [
                ("setup", "public"),
                ("keygen", "issuer"),
                ("issue_request", "client"),
                ("issue_response", "issuer"),
                ("issue_receive", "client"),
            ] {
                let mut j = Job::new(&format!("{name}/{phase}"), name, role, phase);
                j.workload =
                    json!({"capacity":capacity,"threshold":2,"authorities":3,"contacted":2});
                if phase == "setup" {
                    j.class = if scheme {
                        SampleClass::LongCallback
                    } else {
                        SampleClass::SlowProtocol
                    };
                }
                j.boundary = json!({"native_phase":phase,"wire_codec":"canonical_v1","counterparty_work":"outside"});
                if phase == "issue_receive" {
                    j.profile = "Randomized".into();
                    j.boundary["batch_pairing_equations"] = json!(3);
                    j.boundary["batch_coefficient_bits"] = json!(128);
                    j.boundary["batch_coefficient_distribution"] =
                        json!("independent uniform nonzero integer in 1..2^128-1 embedded in Fr");
                    j.boundary["formal_verifier_randomness"] = json!("Rand0.8 StdRng ChaCha12 seeded from OsRng 256 bits outside native timing; coefficients drawn inside");
                }
                jobs.push((
                    j,
                    Selection {
                        scheme,
                        phase,
                        k: 1,
                        random: false,
                        cold: false,
                        prior: false,
                    },
                ));
            }
            for prior in [false, true] {
                let ks = if prior {
                    vec![16]
                } else {
                    K.into_iter().filter(|k| *k <= capacity).collect()
                };
                if prior && capacity < 528 {
                    continue;
                }
                for k in ks {
                    for (phase, role) in [
                        ("install", "public"),
                        ("preparation", "client"),
                        ("online", "client"),
                        ("native_total_reference", "client"),
                        ("merchant_verify", "merchant"),
                        ("strict_decoding", "merchant"),
                        ("deposit", "bank"),
                        ("state", "bank"),
                        ("backend", "bank"),
                        ("inclusive_reference", "merchant_bank"),
                    ] {
                        if phase == "install" && (!scheme || prior) {
                            continue;
                        }
                        for random in if matches!(phase, "merchant_verify" | "inclusive_reference")
                        {
                            vec![false, true]
                        } else {
                            vec![false]
                        } {
                            if !random
                                && matches!(phase, "merchant_verify" | "inclusive_reference")
                                && ![1, 16, 64].contains(&k)
                            {
                                continue;
                            }
                            for cold in if scheme
                                && matches!(
                                    phase,
                                    "preparation"
                                        | "native_total_reference"
                                        | "merchant_verify"
                                        | "inclusive_reference"
                                ) {
                                vec![false, true]
                            } else {
                                vec![false]
                            } {
                                let profile = if phase == "strict_decoding" {
                                    "shared"
                                } else if random {
                                    "Randomized"
                                } else {
                                    "Specification"
                                };
                                let cache = if cold { "cold" } else { "hot" };
                                let scenario = if prior { "post_prior512" } else { "fresh" };
                                let mut j = Job::new(
                                    &format!("{name}/{scenario}/k{k}/{phase}/{profile}/{cache}"),
                                    name,
                                    role,
                                    phase,
                                );
                                j.profile = profile.into();
                                j.cache = cache.into();
                                j.workload = json!({"capacity":capacity,"k":k,"native_payments":1,"native_intervals":1,"history_records":10000,"genuine_prior_units":if prior{512}else{0},"wallet_model":"native_sequential_counter","scenario":scenario});
                                j.boundary = json!({"fresh_nonce_online":true,"merchant_known_preparation":true,"payinfo_public_input_bytes":32,"cold_public_pairing_install_inside":cold,"inclusive_reference_not_summed":phase=="inclusive_reference","backend_excludes_merchant_crypto":phase=="backend","request_binding_included":matches!(phase,"backend"|"inclusive_reference"),"state_store_body_only":phase=="state","state_external_inputs":"complete_native_identifiers_and_complete_bound_request"});
                                if matches!(
                                    phase,
                                    "merchant_verify" | "inclusive_reference" | "strict_decoding"
                                ) {
                                    for key in [
                                        "strict_decoding_included",
                                        "received_bytes_first",
                                        "subgroup_checks_included",
                                        "native_format_checks_included",
                                    ] {
                                        j.boundary[key] = json!(true);
                                    }
                                    j.boundary["subgroup_checks_per_received_element"] = json!(1);
                                    j.boundary["received_input_provenance"] =
                                        json!("sealed_checked_input");
                                    j.boundary["received_gt_elements"] = json!(0);
                                    j.boundary["identity_policy"]=json!("native field-specific signature h nonidentity; other group identities preserved");
                                    j.boundary["fixed_formal_verification_profile"] =
                                        json!("Randomized");
                                    j.boundary["batch_coefficient_bits"] = json!(128);
                                    j.boundary["batch_scope"] = json!("all complete pairing acceptance equations in this verification step, across native payments");
                                    j.boundary["single_equation_policy"] = json!(
                                        "exact native equation; no redundant random exponent"
                                    );
                                    j.boundary["protocol_Sigma_and_FS_unchanged"] = json!(true);
                                    j.boundary["Deposit_pairing_outputs"] = json!("complete native serial derivation, not acceptance-equation residuals");
                                    j.boundary["formal_verifier_randomness"] = json!("Rand0.8 StdRng ChaCha12 seeded from OsRng 256 bits outside native timing; coefficients drawn inside");
                                }
                                j.boundary["pipeline_input_pool"]=json!("fixed_native_issued_wallet_and_public_material; per-slot new native Spend and complete request");
                                j.boundary["cross_sample_specific_token_cache"] = json!(false);
                                if phase == "strict_decoding" {
                                    j.boundary["decode_only"] = json!(true);
                                    j.boundary["parent_verification_stage"] =
                                        json!("merchant_verify");
                                }
                                if matches!(phase, "preparation" | "native_total_reference") {
                                    j.class = SampleClass::SlowProtocol;
                                }
                                jobs.push((
                                    j,
                                    Selection {
                                        scheme,
                                        phase,
                                        k,
                                        random,
                                        cold,
                                        prior,
                                    },
                                ));
                            }
                        }
                    }
                }
            }
        }
        Ok(Self {
            c: Rc::new(RefCell::new(c)),
            d: Rc::new(RefCell::new(d)),
            c_fixture: Rc::new(RefCell::new(None)),
            c_bytes: Rc::new(RefCell::new(None)),
            d_bytes: Rc::new(RefCell::new(None)),
            d_fixture: Rc::new(RefCell::new(None)),
            capacity,
            jobs,
        })
    }
}
impl Worker for Factory {
    fn counter_scope_active(&self) -> bool {
        crate::backend::counts_active()
    }

    fn jobs(&self) -> Vec<Job> {
        self.jobs.iter().map(|(j, _)| j.clone()).collect()
    }
    fn prepare_pipeline(&mut self, ids: &[String], trial: u64) -> Result<Action> {
        if ids.is_empty() {
            return Err("empty RP pipeline".into());
        }
        let selected = ids
            .iter()
            .map(|id| {
                self.jobs
                    .iter()
                    .find(|(j, _)| &j.id == id)
                    .cloned()
                    .ok_or("unknown RP pipeline job".to_owned())
            })
            .collect::<Result<Vec<_>>>()?;
        let scheme = selected[0].1.scheme;
        if selected.iter().any(|(_, s)| s.scheme != scheme) {
            return Err("RP pipeline crosses schemes".into());
        }
        let capacity = self.capacity;
        macro_rules! pipeline {($context:ident,$fixture:ident,$ctxcell:expr,$fixturecell:expr,$sizescell:expr,$request:ident,$response:ident,$verifier:ident,$setup:path,$cold:expr,$warm:expr)=>{{
            let ctxcell=$ctxcell;let fixturecell=$fixturecell;let sizescell=$sizescell;
            Ok(Box::new(move|clock:&mut BoundaryClock|{
                let mut ctx=ctxcell.borrow().clone();let mut role_bytes=vec![];
                let baseid=|phase:&str|selected.iter().find(|(_,s)|s.phase==phase).map(|(j,_)|j.id.as_str());
                if let Some(id)=baseid("setup"){
                    let parameters=native_capture(clock,Some(id),||Ok($setup(capacity)))?;
                    ctx=Rc::new($context::from_parameters(parameters)?);
                    *ctxcell.borrow_mut()=ctx.clone();*fixturecell.borrow_mut()=None;*sizescell.borrow_mut()=None;
                }
                if let Some(id)=baseid("keygen"){
                    ctx=Rc::new(native_capture(clock,Some(id),||ctx.rekey())?);
                    *ctxcell.borrow_mut()=ctx.clone();*fixturecell.borrow_mut()=None;*sizescell.borrow_mut()=None;
                }
                let issuance=selected.iter().any(|(_,s)|matches!(s.phase,"issue_request"|"issue_response"|"issue_receive"));
                let needs_wallet=selected.iter().any(|(_,s)|!matches!(s.phase,"setup"|"keygen"|"install"));
                if issuance||(needs_wallet&&fixturecell.borrow().is_none()){
                    let(pending,request_wire)=native_capture(clock,baseid("issue_request"),||{
                        let(p,r)=ctx.client_request()?;Ok((p,r.encode()))
                    })?;
                    let response_wire=native_capture(clock,baseid("issue_response"),||{
                        let r=$request::decode(&request_wire)?;Ok(ctx.issuer_responses(&r)?.encode())
                    })?;
                    let mut receiving_coins=verifier_rng(clock,trial^0x3301)?;
                    let wallet=native_capture(clock,baseid("issue_receive"),||ctx.client_receive_with_verification(pending,$response::decode(&response_wire)?,VerificationMode::Randomized,&mut receiving_coins))?;
                    role_bytes.push(json!({"role_job_ids":selected.iter().filter(|(_,s)|matches!(s.phase,"issue_request"|"issue_response"|"issue_receive")).map(|(j,_)|j.id.as_str()).collect::<Vec<_>>(),"request_bytes":request_wire.len(),"response_bytes":response_wire.len(),"wallet_component_bytes":wallet.serialized_component_lengths(),"source":"same native request/response/wallet objects passed through this pipeline"}));
                    if fixturecell.borrow().is_none(){*fixturecell.borrow_mut()=Some($fixture::new(&ctx,wallet)?);}
                }
                let mut cases=std::collections::BTreeMap::<(u64,bool),Vec<(Job,Selection)>>::new();
                for(j,s)in &selected{
                    if !matches!(s.phase,"setup"|"keygen"|"issue_request"|"issue_response"|"issue_receive"){
                        cases.entry((s.k,s.prior)).or_default().push((j.clone(),s.clone()));
                    }
                }
                let mut traces=vec![];
                for((k,prior),jobs)in cases{
                    for(j,s)in &jobs{if s.phase=="install"{
                        $cold(&ctx);
                        native_capture(clock,Some(&j.id),||{$warm(&ctx,k);Ok(())})?;
                    }}
                    let branch=||fixturecell.borrow_mut().as_mut().ok_or("RP wallet pool missing".to_owned())?.branch(&ctx,prior);
                    for(j,s)in &jobs{if s.phase=="native_total_reference"{
                        let(w,_)=branch()?;if s.cold{$cold(&ctx);}else{$warm(&ctx,k);}
                        let p=native_capture(clock,Some(&j.id),||ctx.spend(&w,k,PayInfo::new(M,{let mut n=[0;16];n[..8].copy_from_slice(&trial.to_le_bytes());n[8..].copy_from_slice(&(k^u64::from(prior).wrapping_shl(63)).to_le_bytes());n})))?;
                        std::hint::black_box(p);
                    }}
                    if jobs.iter().all(|(_,s)|matches!(s.phase,"install"|"native_total_reference")){continue;}
                    let(mut wallet,snapshot)=branch()?;
                    let start=wallet.next_index();
                    let mut nonce=[0;16];nonce[..8].copy_from_slice(&trial.to_le_bytes());nonce[8..].copy_from_slice(&(k^u64::from(prior).wrapping_shl(63)).to_le_bytes());
                    let info=PayInfo::new(M,nonce);
                    let preparation=jobs.iter().filter(|(_,s)|s.phase=="preparation").min_by_key(|(_,s)|s.cold);
                    if preparation.is_some_and(|(_,s)|s.cold){$cold(&ctx);}else{$warm(&ctx,k);}
                    let prepared=native_capture(clock,preparation.map(|(j,_)|j.id.as_str()),||ctx.prepare(&mut wallet,k,M))?;
                    let online=jobs.iter().find(|(_,s)|s.phase=="online");
                    let(_payment,wire)=native_capture(clock,online.map(|(j,_)|j.id.as_str()),||{
                        let p=prepared.finish(info)?;let wire=p.encode();Ok((p,wire))
                    })?;
                    for(j,s)in &jobs{if s.phase=="preparation"&&Some(j.id.as_str())!=preparation.map(|(j,_)|j.id.as_str()){
                        let(mut w,_)=branch()?;if s.cold{$cold(&ctx);}else{$warm(&ctx,k);}
                        let p=native_capture(clock,Some(&j.id),||ctx.prepare(&mut w,k,M))?;
                        std::hint::black_box(p.finish(info)?);
                    }}
                    let payinfo=info.0.to_vec();
                    let frames=[ReceivedPayment{payment_bytes:&wire,payinfo_bytes:&payinfo}];
                    let mut request=b"random/native-complete-request/v1".to_vec();request.extend(trial.to_le_bytes());request.extend(k.to_le_bytes());request.push(u8::from(prior));
                    let a=$verifier::new(&ctx,M);
                    let mut accepted=None;
                    let mut decoder_source=None;
                    let mut verification_jobs:Vec<_>=jobs.iter().filter(|(_,s)|matches!(s.phase,"merchant_verify"|"inclusive_reference")).collect();
                    if !verification_jobs.is_empty(){let rotate=trial as usize%verification_jobs.len();verification_jobs.rotate_left(rotate);}
                    for(j,s)in verification_jobs{
                        if s.cold{$cold(&ctx);}else{$warm(&ctx,k);}
                        let store=SpentStore::from_snapshot(&snapshot);
                        let mut rng=verifier_rng(clock,trial^0x3300)?;
                        let mode=if s.random{Mode::Randomized}else{Mode::Specification};
                        let decoded=clock.capture(&j.id,|c|c.measure(||{
                            let decoded={let _span=darlt_spseq_fc::darlt::instrumentation::span("receive.strict_decoding");ctx.decode_received(&frames,&M)?};
                            if s.phase=="merchant_verify"{
                                if !a.verify(&decoded,mode,&mut rng){return Err("RP merchant rejected".into());}
                            }else{
                                let result=rt::verify_and_record(&a,&decoded,&request,b"accepted",&store,mode,&mut rng).map_err(|e|e.to_string())?;
                                if result.newly_registered!=k as usize{return Err("RP inclusive registration mismatch".into());}
                            }
                            Ok(decoded)
                        }))?;
                        if decoder_source.is_none(){decoder_source=Some(j.id.clone());}
                        if accepted.is_none(){accepted=Some(decoded);}
                    }
                    for(j,s)in &jobs{if s.phase=="strict_decoding"{
                        let source=decoder_source.as_ref().ok_or("RP decoder requires main verification in the same pipeline slot")?;
                        clock.capture_alias(&j.id,source,"receive.strict_decoding")?;
                    }}
                    if accepted.is_none(){
                        let p=ctx.decode_received(&frames,&M)?;
                        if !a.verify(&p,Mode::Specification,&mut StdRng::seed_from_u64(trial)){return Err("RP pipeline output rejected".into());}
                        accepted=Some(p);
                    }
                    let checked=accepted.as_ref().unwrap();
                    let complete_request=rt::bound_request(&a,checked,&request);
                    let digest=darlt_spseq_fc::common::state::request_hash(&complete_request);
                    let digest_hex=digest.iter().map(|x|format!("{x:02x}")).collect::<String>();
                    for(j,s)in &jobs{
                        match s.phase{
                            "deposit"=>{let ids=native_capture(clock,Some(&j.id),||a.identifiers(checked))?;if ids.len()!=k as usize{return Err("RP Deposit count mismatch".into());}std::hint::black_box(ids);},
                            "state"=>{
                                let store=SpentStore::from_snapshot(&snapshot);
                                let ids=a.identifiers(checked)?.iter().map(|x|Identifier::new(a.namespace(),x).map_err(|e|e.to_string())).collect::<Result<Vec<_>>>()?;
                                native_capture(clock,Some(&j.id),||store.record_checked(&complete_request,&ids,b"accepted").map_err(|e|e.to_string()))?;
                            },
                            "backend"=>{
                                let store=SpentStore::from_snapshot(&snapshot);
                                native_capture(clock,Some(&j.id),||{
                                    let ids=a.identifiers(checked)?.iter().map(|x|Identifier::new(a.namespace(),x).map_err(|e|e.to_string())).collect::<Result<Vec<_>>>()?;
                                    let request=rt::bound_request(&a,checked,&request);
                                    store.record_checked(&request,&ids,b"accepted").map_err(|e|e.to_string())
                                })?;
                            },_=>{}
                        }
                    }
                    traces.push(json!({"k":k,"scenario":if prior{"post_prior512"}else{"fresh"},"start_index":start,"counter_after":wallet.next_index(),"native_intervals":1,"payment_bytes":wire.len(),"payinfo_bytes":32,"wire_bytes":wire.len()+32,"actual_request_digest":digest_hex,"native_payment_digest":darlt_spseq_fc::common::state::request_hash(&wire).iter().map(|x|format!("{x:02x}")).collect::<String>(),"job_ids":jobs.iter().map(|(j,_)|j.id.as_str()).collect::<Vec<_>>(),"all_verification_profiles_share_wire":true,"state_snapshot_restored_per_candidate":true,"cross_sample_token_or_verdict_cache":false,"fixed_wallet_reused":true}));
                }
                let public_job_ids=selected.iter().filter(|(_,s)|matches!(s.phase,"setup"|"keygen"|"install"|"issue_request"|"issue_response"|"issue_receive")).map(|(j,_)|j.id.clone()).collect::<Vec<_>>();
                if !public_job_ids.is_empty()&&sizescell.borrow().is_none(){*sizescell.borrow_mut()=Some(ctx.serialized_public_component_lengths());}
                let public_packages=if public_job_ids.is_empty(){Value::Null}else{sizescell.borrow().clone().unwrap()};
                Ok(json!({"pipeline":true,"trial":trial,"cases":traces,"role_bytes":role_bytes,"public_package_bytes":public_packages,"public_package_job_ids":public_job_ids,"RAM_reuse":["immutable_public_parameters","issuer_keys","native_issued_wallet","prior_state_snapshot"],"different_complete_request_per_sample":true}))
            })as Action)
        }};}
        if scheme {
            pipeline!(
                Divisible,
                DivisibleFixture,
                self.d.clone(),
                self.d_fixture.clone(),
                self.d_bytes.clone(),
                DivisibleIssueRequest,
                DivisibleIssuerResponses,
                DivisibleVerifier,
                divisible_parameters,
                |x: &Divisible| x.clear_pairing_cache(),
                |x: &Divisible, k: u64| x.install_public_pairing_bases(&[k])
            )
        } else {
            pipeline!(
                Compact,
                CompactFixture,
                self.c.clone(),
                self.c_fixture.clone(),
                self.c_bytes.clone(),
                CompactIssueRequest,
                CompactIssuerResponses,
                CompactVerifier,
                crate::compact::setup::setup,
                |_: &Compact| {},
                |_: &Compact, _: u64| {}
            )
        }
    }
    fn prepare(&mut self, id: &str, trial: u64) -> Result<Action> {
        let s = self
            .jobs
            .iter()
            .find(|(j, _)| j.id == id)
            .map(|(_, s)| s.clone())
            .ok_or("unknown RP job")?;
        let capacity = self.capacity;
        let mut nonce = [0u8; 16];
        nonce[..8].copy_from_slice(&trial.to_le_bytes());
        nonce[8..].copy_from_slice(&s.k.to_le_bytes());
        let info = PayInfo::new(M, nonce);
        macro_rules! bind {($ctx:expr,$request:ident,$response:ident,$payment:ident,$verifier:ident,$idbytes:expr,$setup:path,$cold:expr,$warm:expr)=>{{
    let ctx = $ctx;
    match s.phase {
        "setup" => Ok(Box::new(move |clock: &mut BoundaryClock| {
            let p = clock.measure(|| Ok($setup(capacity)))?;
            std::hint::black_box(p);
            Ok(json!({"capacity":capacity}))
        }) as Action),

        "issue_request" => Ok(Box::new(move |clock: &mut BoundaryClock| {
            let (pending, wire) = clock.measure(|| {
                let (p, r) = ctx.client_request()?;
                Ok((p, r.encode()))
            })?;
            let r = $request::decode(&wire)?;
            let response = ctx.issuer_responses(&r)?;
            ctx.client_receive(pending, response)?;
            Ok(json!({"request_bytes":wire.len()}))
        }) as Action),
        "issue_response" => {
            let (pending, r) = ctx.client_request()?;
            let wire = r.encode();
            Ok(Box::new(move |clock: &mut BoundaryClock| {
                let bytes = clock.measure(|| {
                    let r = $request::decode(&wire)?;
                    Ok(ctx.issuer_responses(&r)?.encode())
                })?;
                ctx.client_receive(pending, $response::decode(&bytes)?)?;
                Ok(
                    json!({"request_bytes":wire.len(),"response_bytes":bytes.len(),"authorities_contacted":2}),
                )
            }) as Action)
        }
        "issue_receive" => {
            let (pending, r) = ctx.client_request()?;
            let wire = ctx.issuer_responses(&r)?.encode();
            Ok(Box::new(move |clock: &mut BoundaryClock| {
                let mut coins=verifier_rng(clock,trial^0x3301)?;
                let w = clock.measure(|| ctx.client_receive_with_verification(pending, $response::decode(&wire)?, VerificationMode::Randomized, &mut coins))?;
                Ok(
                    json!({"response_bytes":wire.len(),"counter_after":w.next_index(),"shares_verified":2}),
                )
            }) as Action)
        }
        _ => {
            let mut wallet = ctx.issue()?;
            if !s.cold {
                $warm(&ctx, s.k);
            }
            let adapter = $verifier::new(&ctx, M);
            let store =
                SpentStore::with_preexisting_records(10000, adapter.namespace(), $idbytes)
                    .map_err(|e| e.to_string())?;
            if s.prior {
                let p = ctx
                    .prepare(&mut wallet, 512, M)?
                    .finish(PayInfo::new(M, [254; 16]))?;
                let p = ctx.check_payment(p)?;
                rt::verify_and_record(
                    &adapter,
                    &[p],
                    b"genuine-prior512",
                    b"accepted",
                    &store,
                    Mode::Specification,
                    &mut StdRng::seed_from_u64(trial ^ 512),
                )
                .map_err(|e| format!("{e:?}"))?;
            }
            drop(adapter);
            let expected_start = wallet.next_index();
            if matches!(s.phase, "preparation" | "online" | "native_total_reference") {
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let p = match s.phase {
                        "preparation" => {
                            if s.cold {
                                $cold(&ctx);
                            }
                            let prepared = clock.measure(|| ctx.prepare(&mut wallet, s.k, M))?;
                            prepared.finish(info)?
                        }
                        "online" => {
                            let prepared = ctx.prepare(&mut wallet, s.k, M)?;
                            clock.measure(|| {
                                let p = prepared.finish(info)?;
                                let wire = p.encode();
                                std::hint::black_box(wire);
                                Ok(p)
                            })?
                        }
                        _ => {
                            if s.cold {
                                $cold(&ctx);
                            }
                            clock.measure(|| ctx.spend(&wallet, s.k, info))?
                        }
                    };
                    if !ctx.verify(
                        std::slice::from_ref(&p),
                        &M,
                        VerificationMode::Specification,
                        &mut StdRng::seed_from_u64(trial),
                    ) {
                        return Err("native generation check rejected".into());
                    }
                    Ok(
                        json!({"payment_bytes":p.encode().len(),"payinfo_bytes":32,"wire_bytes":p.encode().len()+32,"k":s.k,"start_index":expected_start,"counter_after":wallet.next_index(),"native_intervals":1}),
                    )
                }) as Action)
            } else {
                let p = ctx.prepare(&mut wallet, s.k, M)?.finish(info)?;
                let wire = p.encode();
                let payinfo_wire=info.0.to_vec();
                let p = ctx.decode_received(&[ReceivedPayment{payment_bytes:&wire,payinfo_bytes:&payinfo_wire}],&M)?.pop().unwrap();
                let a = $verifier::new(&ctx, M);
                if !a.verify(
                    std::slice::from_ref(&p),
                    Mode::Specification,
                    &mut StdRng::seed_from_u64(trial),
                ) {
                    return Err("fixture crypto rejected".into());
                }
                let ids = if s.phase == "state" {
                    Some(a.identifiers(std::slice::from_ref(&p))?)
                } else {
                    None
                };
                drop(a);
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let mut rng = verifier_rng(clock, trial ^ 0x2026)?;
                    let a = $verifier::new(&ctx, M);
                    let mode = if s.random {
                        Mode::Randomized
                    } else {
                        Mode::Specification
                    };
                    if s.cold {
                        $cold(&ctx);
                    }
                    let result: Value = match s.phase {
                        "merchant_verify" => {
                            let ok = clock.measure(|| {
                                let decoded=ctx.decode_received(&[ReceivedPayment{payment_bytes:&wire,payinfo_bytes:&payinfo_wire}],&M)?;
                                Ok(a.verify(&decoded, mode, &mut rng))
                            })?;
                            if !ok {
                                return Err("merchant rejected".into());
                            }
                            json!({"accepted":true})
                        }
                        "strict_decoding" => {
                            let decoded=clock.measure(||ctx.decode_received(&[ReceivedPayment{payment_bytes:&wire,payinfo_bytes:&payinfo_wire}],&M))?;
                            json!({"decoded_payments":decoded.len(),"decoded_amount":decoded[0].amount(),"decode_only":true})
                        }
                        "deposit" => {
                            let recovered =
                                clock.measure(|| a.identifiers(std::slice::from_ref(&p)))?;
                            json!({"serials":recovered.len()})
                        }
                        "state" => {
                            let ids=ids.unwrap().iter().map(|x|Identifier::new(a.namespace(),x).map_err(|e|e.to_string())).collect::<Result<Vec<_>>>()?;
                            let request=rt::bound_request(&a,std::slice::from_ref(&p),b"fresh-payment");
                            let accepted=clock.measure(||store.record_checked(&request,&ids,b"accepted").map_err(|e|e.to_string()))?;
                            json!({"registered":accepted.newly_registered,"state_scope":"record_checked_body_only"})
                        }
                        "backend" => {
                            let accepted = clock.measure(|| {
                                let ids = a
                                    .identifiers(std::slice::from_ref(&p))?
                                    .iter()
                                    .map(|x| {
                                        Identifier::new(a.namespace(), x).map_err(|e| e.to_string())
                                    })
                                    .collect::<Result<Vec<_>>>()?;
                                let request = rt::bound_request(
                                    &a,
                                    std::slice::from_ref(&p),
                                    b"fresh-payment",
                                );
                                store
                                    .record_checked(&request, &ids, b"accepted")
                                    .map_err(|e| e.to_string())
                            })?;
                            json!({"registered":accepted.newly_registered})
                        }
                        "inclusive_reference" => {
                            let accepted = clock.measure(|| {
                                let decoded=ctx.decode_received(&[ReceivedPayment{payment_bytes:&wire,payinfo_bytes:&payinfo_wire}],&M)?;
                                rt::verify_and_record(
                                    &a,
                                    &decoded,
                                    b"fresh-payment",
                                    b"accepted",
                                    &store,
                                    mode,
                                    &mut rng,
                                )
                                .map_err(|e| format!("{e:?}"))
                            })?;
                            json!({"registered":accepted.newly_registered})
                        }
                        _ => return Err("unknown native phase".into()),
                    };
                    Ok(
                        json!({"native_result":result,"payment_bytes":wire.len(),"payinfo_bytes":32,"wire_bytes":wire.len()+32,"k":s.k,"start_index":expected_start,"native_intervals":1,"state_records":store.counts().map_err(|e|e.to_string())?}),
                    )
                }) as Action)
            }
        }
    }
  }}}
        if s.phase == "install" {
            let ctx = self.d.borrow().clone();
            return Ok(Box::new(move |clock: &mut BoundaryClock| {
                ctx.parameters.clear_pairing_cache();
                clock.measure(|| {
                    ctx.install_public_pairing_bases(&[s.k]);
                    Ok(())
                })?;
                Ok(
                    json!({"amount":s.k,"fixed_targets":7,"amount_targets":1,"cache":"first_install","not_added_twice_to_cold_total":true}),
                )
            }));
        }
        // Only the native threshold keygen and aggregation are in this role boundary.
        if s.phase == "keygen" {
            return if s.scheme {
                let ctx = self.d.borrow().clone();
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let key = clock.measure(|| {
                        let a = crate::divisible::ttp_keygen_authorities(&ctx.parameters, 2, 3)
                            .map_err(|e| e.to_string())?;
                        crate::divisible::aggregate_verification_keys(
                            &a[..2]
                                .iter()
                                .map(|a| a.verification_key())
                                .collect::<Vec<_>>(),
                            Some(&[1, 2]),
                        )
                        .map_err(|e| e.to_string())
                    })?;
                    std::hint::black_box(key);
                    Ok(json!({"threshold":2,"authorities":3,"aggregated":2}))
                }))
            } else {
                let ctx = self.c.borrow().clone();
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let key = clock.measure(|| {
                        let a = crate::compact::ttp_keygen(ctx.parameters.grp(), 2, 3)
                            .map_err(|e| e.to_string())?;
                        crate::compact::aggregate_verification_keys(
                            &a[..2]
                                .iter()
                                .map(|a| a.verification_key())
                                .collect::<Vec<_>>(),
                            Some(&[1, 2]),
                        )
                        .map_err(|e| e.to_string())
                    })?;
                    std::hint::black_box(key);
                    Ok(json!({"threshold":2,"authorities":3,"aggregated":2}))
                }))
            };
        }
        if s.scheme {
            bind!(
                self.d.borrow().clone(),
                DivisibleIssueRequest,
                DivisibleIssuerResponses,
                DivisiblePayment,
                DivisibleVerifier,
                288,
                divisible_parameters,
                |x: &Divisible| x.parameters.clear_pairing_cache(),
                |x: &Divisible, k: u64| x.install_public_pairing_bases(&[k])
            )
        } else {
            bind!(
                self.c.borrow().clone(),
                CompactIssueRequest,
                CompactIssuerResponses,
                CompactPayment,
                CompactVerifier,
                48,
                crate::compact::setup::setup,
                |_: &Compact| {},
                |_: &Compact, _: u64| {}
            )
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use darlt_spseq_fc::experiment::{BoundaryClock, RunMode};
    #[test]
    fn pipeline_reuses_native_wallet_but_not_token_and_restores_each_candidate_state() {
        use darlt_spseq_fc::experiment::RunMode;
        let mut f = Factory::with_capacity(16).unwrap();
        for scheme in ["RP23-C", "RP23-D"] {
            let ids: Vec<_> = f
                .jobs()
                .iter()
                .filter(|j| {
                    j.scheme == scheme
                        && [1, 16].iter().any(|k| j.workload["k"] == *k)
                        && !matches!(j.stage.as_str(), "install" | "native_total_reference")
                })
                .map(|j| j.id.clone())
                .collect();
            let mut digests = vec![];
            for trial in [33001, 33002] {
                let action = f.prepare_pipeline(&ids, trial).unwrap();
                let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
                let value = action(&mut clock).unwrap();
                assert_eq!(clock.observations().len(), ids.len());
                assert!(clock
                    .observations()
                    .values()
                    .all(|x| x["ok"] == true && x["elapsed_ns"].is_null()));
                let case = &value["cases"][0];
                assert_eq!(case["state_snapshot_restored_per_candidate"], true);
                digests.push(case["actual_request_digest"].clone());
            }
            assert_ne!(digests[0], digests[1]);
        }
    }
    #[test]
    fn pipeline_real_setup_and_keygen_outputs_replace_ram_references() {
        use darlt_spseq_fc::experiment::RunMode;
        let mut f = Factory::with_capacity(8).unwrap();
        let old = f.d.borrow().issuer_scope_material();
        let action = f
            .prepare_pipeline(&["RP23-D/setup".into(), "RP23-D/keygen".into()], 33003)
            .unwrap();
        let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
        action(&mut clock).unwrap();
        assert_ne!(old, f.d.borrow().issuer_scope_material());
        assert_eq!(clock.observations().len(), 2);
        assert!(f.d_fixture.borrow().is_none());
        for scheme in ["RP23-C", "RP23-D"] {
            let ids = ["issue_request", "issue_response", "issue_receive"]
                .map(|phase| format!("{scheme}/{phase}"));
            let action = f.prepare_pipeline(&ids, 33008).unwrap();
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
            let value = action(&mut clock).unwrap();
            let row = &value["role_bytes"][0];
            assert_eq!(row["role_job_ids"], serde_json::to_value(&ids).unwrap());
            assert_eq!(row["request_bytes"], 457);
            assert_eq!(row["response_bytes"], 201);
            let (components, public) = if scheme == "RP23-C" {
                (
                    f.c_fixture
                        .borrow()
                        .as_ref()
                        .unwrap()
                        .wallet
                        .serialized_component_lengths(),
                    f.c.borrow().serialized_public_component_lengths(),
                )
            } else {
                (
                    f.d_fixture
                        .borrow()
                        .as_ref()
                        .unwrap()
                        .wallet
                        .serialized_component_lengths(),
                    f.d.borrow().serialized_public_component_lengths(),
                )
            };
            assert_eq!(row["wallet_component_bytes"], components);
            assert_eq!(value["public_package_bytes"], public);
            assert!(row["wallet_component_bytes"]["unified_wallet_codec"].is_null());
            assert_eq!(clock.observations().len(), 3);
        }
    }
    #[test]
    fn all_small_native_callbacks_execute_without_clocks() {
        let mut f = Factory::with_capacity(4).unwrap();
        for job in f.jobs() {
            let action = f.prepare(&job.id, 1).unwrap();
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
            let v = action(&mut clock).unwrap();
            assert!(!v.is_null(), "{}", job.id);
            assert!(!clock.segments().is_empty(), "{}", job.id);
            assert_eq!(clock.elapsed_ns(), None);
        }
    }
}
