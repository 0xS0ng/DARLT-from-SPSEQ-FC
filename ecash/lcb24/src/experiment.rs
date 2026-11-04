//! Schedulable native LCB roles. Bank verification is the common blstrs Groth16
//! check; the separate backend stage performs only native leaf recovery/state.
use crate::{
    blstrs_bridge as bridge, encoded, err, Bank, JubJub, Result, Schnorr, Signature,
    SignatureScheme, Wallet,
};
use ark_ec::ProjectiveCurve;
use ark_serialize::CanonicalDeserialize;
use ark_std::rand::{
    rngs::{OsRng, StdRng},
    RngCore, SeedableRng,
};
use darlt_spseq_fc::{
    batch_runtime::{self as rt, Adapter, Mode},
    common::spent::{Identifier, SpentSnapshot, SpentStore},
    experiment::{Action, BoundaryClock, Job, Worker},
    lcb24::{decode_received, Key, RandomProfile, Verifier},
    sampling::{Invocation, NativeOperation, Phase, SampleClass},
};
use serde_json::json;
use std::{cell::RefCell, collections::BTreeMap, rc::Rc};
const K: [usize; 9] = [1, 2, 4, 8, 16, 32, 64, 96, 128];
fn verifier_rng(clock: &BoundaryClock, reproducible_seed: u64) -> Result<StdRng> {
    if clock.mode() == darlt_spseq_fc::experiment::RunMode::Formal {
        let mut seed = [0u8; 32];
        OsRng.try_fill_bytes(&mut seed).map_err(err)?;
        Ok(StdRng::from_seed(seed))
    } else {
        Ok(StdRng::seed_from_u64(reproducible_seed))
    }
}
fn signature_bytes(s: &Signature<JubJub>) -> Vec<u8> {
    let mut b = encoded(&s.prover_response);
    b.extend(s.verifier_challenge);
    b
}
fn signature_decode(b: &[u8]) -> Result<Signature<JubJub>> {
    if b.len() != 64 {
        return Err("Schnorr response length".into());
    }
    let prover_response =
        <<JubJub as ProjectiveCurve>::ScalarField>::deserialize(&b[..32]).map_err(err)?;
    Ok(Signature {
        prover_response,
        verifier_challenge: b[32..].try_into().unwrap(),
    })
}
#[derive(Clone)]
struct Selection {
    phase: &'static str,
    k: usize,
    random: bool,
    pair: bool,
    cold: bool,
    sparse: bool,
}
fn wallet_component_bytes<const H: usize>(wallet: &Wallet<H>) -> serde_json::Value {
    json!({"native_signature_response":signature_bytes(&wallet.signature).len(),"native_commitment_scalar":encoded(&wallet.commitment).len(),"native_root_scalar":encoded(&wallet.root).len(),"native_opening_scalar":encoded(&wallet.opening).len(),"native_master_seed":wallet.master.len(),"native_leaf_proof_objects_total":wallet.proof_cache_bytes(),"unified_wallet_codec":serde_json::Value::Null})
}
fn public_component_bytes<const H: usize>(bank: &Bank<H>, key: &Key) -> serde_json::Value {
    json!({"native_groth16_proving_key":bank.proving_key_bytes(),"native_groth16_verification_key":encoded(&bank.verifying_key).len(),"native_schnorr_public_key":encoded(&bank.sig_public).len(),"native_schnorr_generator":encoded(&bank.sig_params.generator).len(),"installed_blstrs_key_package":key.bytes().len(),"proving_key_includes_verification_key":true,"unified_public_parameter_codec":serde_json::Value::Null})
}
struct PoolSnapshots<const H: usize> {
    fresh: SpentSnapshot,
    sparse: Option<(Wallet<H>, SpentSnapshot)>,
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
pub struct Factory<const H: usize = 10> {
    bank: Rc<RefCell<Rc<Bank<H>>>>,
    key: Rc<RefCell<Rc<Key>>>,
    inventory: Rc<RefCell<Option<Rc<Wallet<H>>>>>,
    snapshots: Rc<RefCell<Option<PoolSnapshots<H>>>>,
    asset_origin: Rc<RefCell<String>>,
    public_bytes: Rc<RefCell<Option<serde_json::Value>>>,
    jobs: Vec<(Job, Selection)>,
    calibrations: BTreeMap<String, Rc<RefCell<crate::calibration::Fixture>>>,
}
pub fn new() -> Result<Factory<10>> {
    Factory::<10>::new_for_height()
}
impl<const H: usize> Factory<H> {
    pub fn new_for_height() -> Result<Self> {
        let bank = Rc::new(Bank::<H>::setup(&mut StdRng::seed_from_u64(
            215_240_000 + H as u64,
        ))?);
        let key = Rc::new(bridge::key(&bank)?);
        let mut jobs = vec![];
        let capacity = 1usize << H;
        for (phase, role) in [
            ("setup", "public"),
            ("keygen", "issuer"),
            ("install", "bank"),
            ("issue_request", "client"),
            ("issue_response", "issuer"),
            ("issue_receive", "client"),
            ("full_inventory", "client"),
        ] {
            let mut j = Job::new(&format!("LCB24/{phase}"), "LCB24", role, phase);
            j.workload = json!({"capacity":capacity});
            j.boundary = json!({"native_prover_backend":"Arkworks0.3","native_verifier_backend":"blstrs0.7.1/blst0.3.17","proofs":if phase=="full_inventory"{capacity}else{0},"installation_not_added_twice":true});
            if matches!(phase, "setup" | "full_inventory") {
                j.class = if phase == "full_inventory" {
                    SampleClass::LongCallback
                } else {
                    SampleClass::SlowProtocol
                };
            }
            jobs.push((
                j,
                Selection {
                    phase,
                    k: 1,
                    random: false,
                    pair: false,
                    cold: false,
                    sparse: false,
                },
            ));
        }
        for sparse in [false, true] {
            if sparse && capacity != 1024 {
                continue;
            }
            for k in if sparse {
                vec![16]
            } else {
                K.into_iter().filter(|k| *k <= capacity).collect()
            } {
                for (phase, role) in [
                    ("preparation", "client"),
                    ("online", "client"),
                    ("native_total_reference", "client"),
                    ("bank_verify", "bank"),
                    ("strict_decoding", "bank"),
                    ("deposit", "bank"),
                    ("state", "bank"),
                    ("backend", "bank"),
                    ("inclusive_reference", "bank"),
                ] {
                    for random in if matches!(phase, "bank_verify" | "inclusive_reference") {
                        vec![false, true]
                    } else {
                        vec![false]
                    } {
                        for pair in if random {
                            vec![false, true]
                        } else {
                            vec![false]
                        } {
                            if !random
                                && matches!(phase, "bank_verify" | "inclusive_reference")
                                && ![1, 16, 64].contains(&k)
                            {
                                continue;
                            }
                            for cold in if matches!(phase, "bank_verify" | "inclusive_reference") {
                                vec![false, true]
                            } else {
                                vec![false]
                            } {
                                let scenario = if sparse { "post_sparse512" } else { "fresh" };
                                let profile = if phase == "strict_decoding" {
                                    "shared"
                                } else if !random {
                                    "Specification"
                                } else if pair {
                                    "RandomizedPairingAnchor"
                                } else {
                                    "RandomizedCachedGtAnchor"
                                };
                                let cache = if cold { "cold" } else { "hot" };
                                let mut j = Job::new(
                                    &format!("LCB24/{scenario}/k{k}/{phase}/{profile}/{cache}"),
                                    "LCB24",
                                    role,
                                    phase,
                                );
                                j.profile = profile.into();
                                j.cache = cache.into();
                                j.workload = json!({"capacity":capacity,"k":k,"scenario":scenario,"genuine_prior_units":if sparse{512}else{0},"history_records":10000,"selected_blocks":if sparse{16}else{k.count_ones() as usize}});
                                j.boundary = json!({"bank_verification_column":"complete_blstrs_Groth16","backend_excludes_Groth16":phase=="backend","cold_includes_key_install":cold,"inclusive_reference_not_summed":phase=="inclusive_reference","preparation_inventory":"known_workload_selected_leftmost_proofs","online_context_bound":false,"preencoded_one_use_delivery":phase=="online","point_conversion_and_encoding_in_preparation":true,"request_binding_included":matches!(phase,"backend"|"inclusive_reference"),"state_store_body_only":phase=="state","state_external_inputs":"complete_native_identifiers_and_complete_bound_request"});
                                if matches!(
                                    phase,
                                    "bank_verify" | "inclusive_reference" | "strict_decoding"
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
                                    j.boundary["seed_instance_binding"]=json!("native verifier pre-weight check, not a proof equation in the decoder");
                                    j.boundary["identity_policy"]=json!("native proof A/B/C identities remain permitted by format; Groth16 validity still verified");
                                    j.boundary["fixed_formal_verification_profile"] =
                                        json!("RandomizedCachedGtAnchor");
                                    j.boundary["batch_coefficient_bits"] = json!(128);
                                    j.boundary["batch_scope"] = json!("all native Groth16 block equations in this verification step, across payments");
                                    j.boundary["fixed_anchor_source"] = json!("native prepared verification key alpha-beta GT value; chosen by algorithm, not timing");
                                    j.boundary["single_equation_policy"] = json!(
                                        "exact native equation; no redundant random exponent"
                                    );
                                    j.boundary["formal_verifier_randomness"] = json!("Rand0.8 StdRng ChaCha12 seeded from OsRng 256 bits outside native timing; coefficients drawn inside");
                                }
                                j.boundary["pipeline_input_pool"]=json!("fixed_native_issued_wallet_and_precomputed_Groth16_stock; new complete application request per slot");
                                j.boundary["native_proof_bytes_may_repeat_between_samples"] =
                                    json!(true);
                                j.boundary["cross_sample_specific_token_cache"] = json!(false);
                                if phase == "strict_decoding" {
                                    j.boundary["decode_only"] = json!(true);
                                    j.boundary["parent_verification_stage"] = json!("bank_verify");
                                }
                                if phase == "preparation" {
                                    j.class = if sparse {
                                        SampleClass::LongCallback
                                    } else {
                                        SampleClass::SlowProtocol
                                    };
                                }
                                jobs.push((
                                    j,
                                    Selection {
                                        phase,
                                        k,
                                        random,
                                        pair,
                                        cold,
                                        sparse,
                                    },
                                ));
                            }
                        }
                    }
                }
            }
        }
        for (phase, operation, sizes) in [
            ("calibrate_pairing", "pairing", vec![1]),
            (
                "calibrate_g1_msm",
                "G1_MSM",
                crate::calibration::MSM_SIZES.to_vec(),
            ),
            (
                "calibrate_g2_msm",
                "G2_MSM",
                crate::calibration::MSM_SIZES.to_vec(),
            ),
        ] {
            for k in sizes {
                for random in [false, true] {
                    let backend = if random { "blstrs0.7.1" } else { "Arkworks0.3" };
                    let mut j = Job::new(
                        &format!("LCB24/calibration/{operation}/n{k}/{backend}"),
                        "LCB24",
                        "primitive",
                        "calibration",
                    );
                    j.substage = operation.into();
                    j.profile = backend.into();
                    j.class = SampleClass::Primitive;
                    j.workload =
                        json!({"size":k,"mathematically_identical_cross_backend_fixture":true});
                    j.boundary = json!({"fixture_generation_and_conversion":"outside","primitive_only":true});
                    jobs.push((
                        j,
                        Selection {
                            phase,
                            k,
                            random,
                            pair: false,
                            cold: false,
                            sparse: false,
                        },
                    ));
                }
            }
        }
        Ok(Self {
            bank: Rc::new(RefCell::new(bank)),
            key: Rc::new(RefCell::new(key)),
            snapshots: Rc::new(RefCell::new(None)),
            asset_origin: Rc::new(RefCell::new("uninitialized".into())),
            public_bytes: Rc::new(RefCell::new(None)),
            inventory: Rc::new(RefCell::new(None)),
            jobs,
            calibrations: BTreeMap::new(),
        })
    }
    // Full inventory is constructed once for fixture reuse. Its cost has its own
    // independent callback, and is never charged to an online/verification stage.
    fn inventory(&mut self) -> Result<Rc<Wallet<H>>> {
        if let Some(w) = self.inventory.borrow().as_ref() {
            if w.prepared_proofs() == w.capacity() {
                return Ok(w.clone());
            }
        }
        let mut rng = StdRng::seed_from_u64(215_240_100 + H as u64);
        let bank = self.bank.borrow().clone();
        let existing = self.inventory.borrow().clone();
        let asset = if let Some(w) = existing {
            w
        } else {
            let w = Rc::new(bank.issue_wallet(&mut rng)?);
            *self.inventory.borrow_mut() = Some(w.clone());
            *self.asset_origin.borrow_mut() =
                "dependency_initialization_once/native_issue_wallet".into();
            w
        };
        let mut w = bridge::fixture_branch(&bank, &asset)?;
        bank.precompute_all(&mut w, &mut rng)?;
        let w = Rc::new(w);
        *self.inventory.borrow_mut() = Some(w.clone());
        Ok(w)
    }
}
impl<const H: usize> Worker for Factory<H> {
    fn jobs(&self) -> Vec<Job> {
        self.jobs.iter().map(|(j, _)| j.clone()).collect()
    }
    fn prepare_pipeline(&mut self, ids: &[String], trial: u64) -> Result<Action> {
        if ids.is_empty() {
            return Err("empty LCB pipeline".into());
        }
        let selected = ids
            .iter()
            .map(|id| {
                self.jobs
                    .iter()
                    .find(|(j, _)| &j.id == id)
                    .cloned()
                    .ok_or("unknown LCB pipeline job".to_owned())
            })
            .collect::<Result<Vec<_>>>()?;
        if selected
            .iter()
            .all(|(_, s)| s.phase.starts_with("calibrate_"))
        {
            let mut actions = BTreeMap::<(String, usize), Vec<(String, Action)>>::new();
            for (j, s) in &selected {
                actions
                    .entry((s.phase.into(), s.k))
                    .or_default()
                    .push((j.id.clone(), self.prepare(&j.id, trial)?));
            }
            return Ok(Box::new(move |clock| {
                let mut results = vec![];
                for (_, mut pair) in actions {
                    if !pair.is_empty() {
                        let rotate = trial as usize % pair.len();
                        pair.rotate_left(rotate);
                    }
                    for (id, action) in pair {
                        let value = clock.capture(&id, action)?;
                        results.push(json!({"job":id,"value":value}));
                    }
                }
                Ok(json!({"pipeline":true,"calibration":true,"primitive_results":results}))
            }));
        }
        let request_phase = |p: &str| {
            matches!(
                p,
                "preparation"
                    | "online"
                    | "native_total_reference"
                    | "bank_verify"
                    | "strict_decoding"
                    | "deposit"
                    | "state"
                    | "backend"
                    | "inclusive_reference"
            )
        };
        let request = selected.iter().any(|(_, s)| request_phase(s.phase));
        if request && selected.iter().any(|(_, s)| !request_phase(s.phase)) {
            return Err("LCB setup/issuance/materialization and fixed-stock request families need separate slots".into());
        }
        let bankcell = self.bank.clone();
        let keycell = self.key.clone();
        let inventory = self.inventory.clone();
        let snapshots = self.snapshots.clone();
        let asset_origin = self.asset_origin.clone();
        let public_bytes = self.public_bytes.clone();
        if !request {
            return Ok(Box::new(move |clock: &mut BoundaryClock| {
                let mut bank = bankcell.borrow().clone();
                let mut role_bytes = vec![];
                let baseid = |phase: &str| {
                    selected
                        .iter()
                        .find(|(_, s)| s.phase == phase)
                        .map(|(j, _)| j.id.as_str())
                };
                let mut rng = StdRng::seed_from_u64(trial ^ 0x330024);
                if let Some(id) = baseid("setup") {
                    bank = Rc::new(native_capture(clock, Some(id), || {
                        Bank::<H>::setup(&mut rng)
                    })?);
                    *bankcell.borrow_mut() = bank.clone();
                    *keycell.borrow_mut() = Rc::new(bridge::key(&bank)?);
                    *inventory.borrow_mut() = None;
                    *snapshots.borrow_mut() = None;
                    *asset_origin.borrow_mut() = "uninitialized".into();
                    *public_bytes.borrow_mut() = None;
                }
                if let Some(id) = baseid("keygen") {
                    let key = native_capture(clock, Some(id), || {
                        Schnorr::<JubJub>::keygen(&bank.sig_params, &mut rng).map_err(err)
                    })?;
                    // The native circuit binds Bank's issuer key as a constant.
                    // This separate keygen reference is not silently substituted into that circuit.
                    let _ = std::hint::black_box(key);
                }
                if let Some(id) = baseid("install") {
                    let key = native_capture(clock, Some(id), || bridge::key(&bank))?;
                    *keycell.borrow_mut() = Rc::new(key);
                }
                if selected.iter().any(|(_, s)| {
                    matches!(
                        s.phase,
                        "issue_request" | "issue_response" | "issue_receive"
                    )
                }) {
                    let (pending, request_wire) =
                        native_capture(clock, baseid("issue_request"), || {
                            let p = bank.customer_request(&mut rng)?;
                            let wire = p.request_bytes();
                            Ok((p, wire))
                        })?;
                    let response = native_capture(clock, baseid("issue_response"), || {
                        let commitment =
                            crate::Fr::deserialize(request_wire.as_slice()).map_err(err)?;
                        Ok(signature_bytes(
                            &bank.issuer_response(commitment, &mut rng)?,
                        ))
                    })?;
                    let wallet = native_capture(clock, baseid("issue_receive"), || {
                        bank.customer_receive(pending, signature_decode(&response)?)
                    })?;
                    role_bytes.push(json!({"role_job_ids":selected.iter().filter(|(_,s)|matches!(s.phase,"issue_request"|"issue_response"|"issue_receive")).map(|(j,_)|j.id.as_str()).collect::<Vec<_>>(),"request_bytes":request_wire.len(),"response_bytes":response.len(),"wallet_component_bytes":wallet_component_bytes(&wallet),"source":"same native request/response/accepted wallet objects passed through this pipeline"}));
                    if inventory.borrow().is_none() {
                        *inventory.borrow_mut() = Some(Rc::new(wallet));
                        *snapshots.borrow_mut() = None;
                        *asset_origin.borrow_mut() = "first_pipeline_issue_receive".into();
                    }
                }
                if let Some(id) = baseid("full_inventory") {
                    let existing = inventory.borrow().clone();
                    let asset = if let Some(w) = existing {
                        w
                    } else {
                        let w = Rc::new(bank.issue_wallet(&mut rng)?);
                        *inventory.borrow_mut() = Some(w.clone());
                        *asset_origin.borrow_mut() =
                            "dependency_initialization_once/native_issue_wallet".into();
                        w
                    };
                    let mut wallet = bridge::fixture_branch(&bank, &asset)?;
                    wallet.proofs = Rc::new(Default::default());
                    let n = native_capture(clock, Some(id), || {
                        bank.precompute_all(&mut wallet, &mut rng)
                    })?;
                    let stock = Rc::new(wallet);
                    if let Some(pool) = snapshots.borrow_mut().as_mut() {
                        if let Some((sparse, _)) = pool.sparse.as_mut() {
                            sparse.proofs = stock.proofs.clone();
                        }
                    }
                    *inventory.borrow_mut() = Some(stock);
                    return Ok(
                        json!({"pipeline":true,"native_Ark_Groth16_proofs":n,"RAM_stock_updated_from_real_output":true,"full_inventory_cache_hit":false,"stock_source":format!("native_precompute_all_from/{}",asset_origin.borrow()),"fixed_wallet_statement_reused":true,"precomputed_proof_bytes":inventory.borrow().as_ref().unwrap().proof_cache_bytes(),"wallet_component_bytes":wallet_component_bytes(inventory.borrow().as_ref().unwrap()),"role_job_ids":selected.iter().map(|(j,_)|j.id.as_str()).collect::<Vec<_>>()}),
                    );
                }
                if public_bytes.borrow().is_none() {
                    *public_bytes.borrow_mut() =
                        Some(public_component_bytes(&bank, &keycell.borrow()));
                }
                Ok(
                    json!({"pipeline":true,"role_bytes":role_bytes,"public_package_bytes":public_bytes.borrow().clone().unwrap(),"public_package_job_ids":selected.iter().map(|(j,_)|j.id.as_str()).collect::<Vec<_>>(),"RAM_setup_and_first_issued_wallet_retained":true,"keygen_reference_not_substituted_into_constant_circuit_key":baseid("keygen").is_some(),"fixed_asset_source":asset_origin.borrow().clone()}),
                )
            }));
        }
        let stock = self.inventory()?;
        let bank = self.bank.borrow().clone();
        let key = self.key.borrow().clone();
        if snapshots.borrow().is_none() {
            let v = Verifier::<H>::new(&key, RandomProfile::CachedGtAnchor);
            let store =
                SpentStore::with_preexisting_records(10000, v.namespace(), 32).map_err(err)?;
            *snapshots.borrow_mut() = Some(PoolSnapshots {
                fresh: store.snapshot().map_err(err)?,
                sparse: None,
            });
        }
        if selected.iter().any(|(_, s)| s.sparse)
            && snapshots.borrow().as_ref().unwrap().sparse.is_none()
        {
            let mut wallet = bridge::fixture_branch(&bank, &stock)?;
            let evens: Vec<_> = (0..1024).step_by(2).map(|i| (0, i)).collect();
            let p = bridge::payment::<H>(&bank.spend_prepared_blocks(&mut wallet, &evens)?)?;
            let wire = p.encode();
            let checked = decode_received::<H>(&[&wire])?;
            let v = Verifier::<H>::new(&key, RandomProfile::CachedGtAnchor);
            let store = SpentStore::from_snapshot(&snapshots.borrow().as_ref().unwrap().fresh);
            rt::verify_and_record(
                &v,
                &checked,
                b"genuine-prior-even512",
                b"accepted",
                &store,
                Mode::Randomized,
                &mut StdRng::seed_from_u64(512),
            )
            .map_err(err)?;
            snapshots.borrow_mut().as_mut().unwrap().sparse =
                Some((wallet, store.snapshot().map_err(err)?));
        }
        Ok(Box::new(move |clock: &mut BoundaryClock| {
            let mut cases = BTreeMap::<(usize, bool), Vec<(Job, Selection)>>::new();
            for (j, s) in &selected {
                cases
                    .entry((s.k, s.sparse))
                    .or_default()
                    .push((j.clone(), s.clone()));
            }
            let mut traces = vec![];
            for ((k, sparse), jobs) in cases {
                let branch = || -> Result<(Wallet<H>, SpentSnapshot)> {
                    let pool = snapshots.borrow();
                    let pool = pool.as_ref().ok_or("LCB state snapshots missing")?;
                    if sparse {
                        let (w, s) = pool.sparse.as_ref().ok_or("LCB sparse history missing")?;
                        Ok((bridge::fixture_branch(&bank, w)?, s.clone()))
                    } else {
                        Ok((bridge::fixture_branch(&bank, &stock)?, pool.fresh.clone()))
                    }
                };
                for (j, s) in &jobs {
                    if s.phase == "native_total_reference" {
                        let (mut w, _) = branch()?;
                        let p =
                            native_capture(clock, Some(&j.id), || bank.spend_prepared(&mut w, k))?;
                        std::hint::black_box(p);
                    }
                }
                if jobs
                    .iter()
                    .all(|(_, s)| s.phase == "native_total_reference")
                {
                    continue;
                }
                let (mut wallet, snapshot) = branch()?;
                let preparation = jobs.iter().find(|(_, s)| s.phase == "preparation");
                if preparation.is_some() {
                    wallet.proofs = Rc::new(Default::default());
                }
                let mut rng = StdRng::seed_from_u64(trial ^ (k as u64) ^ 0x330024);
                let (native, _payment, wire) =
                    native_capture(clock, preparation.map(|(j, _)| j.id.as_str()), || {
                        if preparation.is_some() {
                            bank.precompute_amount(&mut wallet, k, &mut rng)?;
                        }
                        let native = bank.spend_prepared(&mut wallet, k)?;
                        let payment = bridge::payment::<H>(&native)?;
                        let wire = payment.encode();
                        Ok((native, payment, wire))
                    })?;
                let online = jobs.iter().find(|(_, s)| s.phase == "online");
                let wire = native_capture(clock, online.map(|(j, _)| j.id.as_str()), || Ok(wire))?;
                let mut request = b"random/LCB24-complete-request/v1".to_vec();
                request.extend(trial.to_le_bytes());
                request.extend((k as u64).to_le_bytes());
                request.push(u8::from(sparse));
                let mut accepted = None;
                let mut decoder_source = None;
                let mut verification_jobs: Vec<_> = jobs
                    .iter()
                    .filter(|(_, s)| matches!(s.phase, "bank_verify" | "inclusive_reference"))
                    .collect();
                if !verification_jobs.is_empty() {
                    let rotate = trial as usize % verification_jobs.len();
                    verification_jobs.rotate_left(rotate);
                }
                for (j, s) in verification_jobs {
                    let store = SpentStore::from_snapshot(&snapshot);
                    let mode = if s.random {
                        Mode::Randomized
                    } else {
                        Mode::Specification
                    };
                    let profile = if s.pair {
                        RandomProfile::PairingAnchor
                    } else {
                        RandomProfile::CachedGtAnchor
                    };
                    let mut coins = verifier_rng(clock, trial ^ 0x3300)?;
                    let checked = clock.capture(&j.id, |c| {
                        c.measure(|| {
                            let decoded = {
                                let _span = darlt_spseq_fc::darlt::instrumentation::span(
                                    "receive.strict_decoding",
                                );
                                decode_received::<H>(&[&wire])?
                            };
                            let cold = s.cold.then(|| bridge::key(&bank)).transpose()?;
                            let current = cold.as_ref().unwrap_or(&key);
                            if s.phase == "bank_verify" {
                                current.verify_checked::<H>(&decoded, mode, profile, &mut coins)?;
                            } else {
                                let v = Verifier::<H>::new(current, profile);
                                let result = rt::verify_and_record(
                                    &v,
                                    &decoded,
                                    &request,
                                    b"accepted",
                                    &store,
                                    mode,
                                    &mut coins,
                                )
                                .map_err(err)?;
                                if result.newly_registered != k {
                                    return Err("LCB inclusive registration mismatch".into());
                                }
                            }
                            Ok(decoded)
                        })
                    })?;
                    if decoder_source.is_none() {
                        decoder_source = Some(j.id.clone());
                    }
                    if accepted.is_none() {
                        accepted = Some(checked);
                    }
                }
                for (j, s) in &jobs {
                    if s.phase == "strict_decoding" {
                        let source = decoder_source.as_ref().ok_or(
                            "LCB decoder requires main bank verification in the same slot",
                        )?;
                        clock.capture_alias(&j.id, source, "receive.strict_decoding")?;
                    }
                }
                if accepted.is_none() {
                    let checked = decode_received::<H>(&[&wire])?;
                    key.verify_checked::<H>(
                        &checked,
                        Mode::Specification,
                        RandomProfile::CachedGtAnchor,
                        &mut rng,
                    )?;
                    accepted = Some(checked);
                }
                let checked = accepted.as_ref().unwrap();
                let v = Verifier::<H>::new(&key, RandomProfile::CachedGtAnchor);
                let complete_request = rt::bound_request(&v, checked, &request);
                let digest = darlt_spseq_fc::common::state::request_hash(&complete_request)
                    .iter()
                    .map(|x| format!("{x:02x}"))
                    .collect::<String>();
                for (j, s) in &jobs {
                    match s.phase {
                        "deposit" => {
                            let ids = native_capture(clock, Some(&j.id), || {
                                checked[0].redeem_serials::<H>()
                            })?;
                            if ids.len() != k {
                                return Err("LCB Deposit count mismatch".into());
                            }
                            std::hint::black_box(ids);
                        }
                        "state" => {
                            let store = SpentStore::from_snapshot(&snapshot);
                            let ids = checked[0]
                                .redeem_serials::<H>()?
                                .iter()
                                .map(|x| Identifier::new(v.namespace(), x).map_err(err))
                                .collect::<Result<Vec<_>>>()?;
                            native_capture(clock, Some(&j.id), || {
                                store
                                    .record_checked(&complete_request, &ids, b"accepted")
                                    .map_err(err)
                            })?;
                        }
                        "backend" => {
                            let store = SpentStore::from_snapshot(&snapshot);
                            native_capture(clock, Some(&j.id), || {
                                let ids = checked[0]
                                    .redeem_serials::<H>()?
                                    .iter()
                                    .map(|x| Identifier::new(v.namespace(), x).map_err(err))
                                    .collect::<Result<Vec<_>>>()?;
                                let request = rt::bound_request(&v, checked, &request);
                                store
                                    .record_checked(&request, &ids, b"accepted")
                                    .map_err(err)
                            })?;
                        }
                        _ => {}
                    }
                }
                traces.push(json!({"k":k,"scenario":if sparse{"post_sparse512"}else{"fresh"},"native_blocks":native.blocks.len(),"denoms":native.blocks.iter().map(|b|b.denom).collect::<Vec<_>>(),"payment_bytes":wire.len(),"actual_request_digest":digest,"native_payment_digest":darlt_spseq_fc::common::state::request_hash(&wire).iter().map(|x|format!("{x:02x}")).collect::<String>(),"job_ids":jobs.iter().map(|(j,_)|j.id.as_str()).collect::<Vec<_>>(),"native_statement_reused":true,"native_proof_bytes_reused":preparation.is_none(),"fresh_native_proofs_prepared_this_slot":preparation.is_some(),"complete_application_request_fresh":true,"all_verification_profiles_share_wire":true,"state_snapshot_restored_per_candidate":true,"cross_sample_specific_token_or_verdict_cache":false,"stock_proofs":stock.prepared_proofs(),"fixed_asset_source":asset_origin.borrow().clone()}));
            }
            Ok(
                json!({"pipeline":true,"trial":trial,"cases":traces,"RAM_reuse":["Bank_setup","installed_native_key","native_issued_wallet","precomputed_leaf_proofs","immutable_Merkle_tree","state_snapshot"],"single_threaded_Ark_features":true}),
            )
        }))
    }
    fn prepare(&mut self, id: &str, trial: u64) -> Result<Action> {
        let s = self
            .jobs
            .iter()
            .find(|(j, _)| j.id == id)
            .map(|(_, s)| s.clone())
            .ok_or("unknown LCB job")?;
        let bank = self.bank.borrow().clone();
        let key = self.key.borrow().clone();
        let mut rng = StdRng::seed_from_u64(trial ^ 0x215240);
        if s.phase.starts_with("calibrate_") {
            let operation = match s.phase {
                "calibrate_pairing" => crate::calibration::Operation::Pairing,
                "calibrate_g1_msm" => crate::calibration::Operation::G1Msm(s.k),
                _ => crate::calibration::Operation::G2Msm(s.k),
            };
            let fixture_key = format!("{}/{}", s.phase, s.k);
            let fixture = if let Some(existing) = self.calibrations.get(&fixture_key) {
                existing.clone()
            } else {
                let base_seed = darlt_spseq_fc::common::state::request_hash(fixture_key.as_bytes());
                let mut bases =
                    StdRng::seed_from_u64(u64::from_le_bytes(base_seed[..8].try_into().unwrap()));
                let fixture = crate::calibration::Fixture::new(operation, &mut bases)?;
                fixture.check_msm_equivalence()?;
                let fixture = Rc::new(RefCell::new(fixture));
                self.calibrations
                    .insert(fixture_key.clone(), fixture.clone());
                fixture
            };
            let invocation = Invocation {
                attempt: 0,
                phase: Phase::Retained,
                round: 0,
                candidate: usize::from(s.random),
                index: trial as usize,
            };
            fixture.borrow_mut().prepare(&invocation)?;
            let input_digest = fixture.borrow().input_digest();
            return Ok(Box::new(move |clock: &mut BoundaryClock| {
                let mut fixture = fixture.borrow_mut();
                clock.measure(|| fixture.execute(&invocation))?;
                Ok(
                    json!({"size":s.k,"backend":if s.random{"blstrs0.7.1"}else{"Arkworks0.3"},"primitive":s.phase,"input_digest":input_digest,"fresh_mathematical_input_per_trial":true}),
                )
            }));
        }
        match s.phase {
            "setup" => Ok(Box::new(move |clock: &mut BoundaryClock| {
                let b = clock.measure(|| Bank::<H>::setup(&mut rng))?;
                Ok(
                    json!({"capacity":1usize<<H,"proving_key_bytes":b.proving_key_bytes(),"verification_material_bytes":b.issuer_verification_material_bytes()}),
                )
            })),
            "keygen" => Ok(Box::new(move |clock: &mut BoundaryClock| {
                let (pk, sk) = clock.measure(|| {
                    Schnorr::<JubJub>::keygen(&bank.sig_params, &mut rng).map_err(err)
                })?;
                std::hint::black_box(sk);
                Ok(json!({"public_key_bytes":encoded(&pk).len()}))
            })),
            "install" => Ok(Box::new(move |clock: &mut BoundaryClock| {
                let k = clock.measure(|| bridge::key(&bank))?;
                Ok(json!({"installed_key_bytes":k.bytes().len()}))
            })),
            "issue_request" => Ok(Box::new(move |clock: &mut BoundaryClock| {
                let (p, wire) = clock.measure(|| {
                    let p = bank.customer_request(&mut rng)?;
                    let wire = p.request_bytes();
                    Ok((p, wire))
                })?;
                let response = bank.issuer_response(p.commitment(), &mut rng)?;
                bank.customer_receive(p, response)?;
                Ok(json!({"request_bytes":wire.len()}))
            })),
            "issue_response" => {
                let p = bank.customer_request(&mut rng)?;
                let raw = p.request_bytes();
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let bytes = clock.measure(|| {
                        let commitment = crate::Fr::deserialize(raw.as_slice()).map_err(err)?;
                        Ok(signature_bytes(
                            &bank.issuer_response(commitment, &mut rng)?,
                        ))
                    })?;
                    bank.customer_receive(p, signature_decode(&bytes)?)?;
                    Ok(json!({"request_bytes":raw.len(),"response_bytes":bytes.len()}))
                }))
            }
            "issue_receive" => {
                let p = bank.customer_request(&mut rng)?;
                let raw = signature_bytes(&bank.issuer_response(p.commitment(), &mut rng)?);
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let w = clock.measure(|| bank.customer_receive(p, signature_decode(&raw)?))?;
                    Ok(json!({"response_bytes":raw.len(),"capacity":w.capacity()}))
                }))
            }
            "full_inventory" => {
                let mut w = bank.issue_wallet(&mut rng)?;
                let inventory = self.inventory.clone();
                let snapshots = self.snapshots.clone();
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let proofs = clock.measure(|| bank.precompute_all(&mut w, &mut rng))?;
                    let bytes = w.proof_cache_bytes();
                    *inventory.borrow_mut() = Some(Rc::new(w));
                    *snapshots.borrow_mut() = None;
                    Ok(
                        json!({"native_Ark_Groth16_proofs":proofs,"proof_cache_bytes":bytes,"full_inventory":true}),
                    )
                }))
            }
            _ => {
                let mut w = if s.phase == "preparation" && !s.sparse {
                    bank.issue_wallet(&mut rng)?
                } else {
                    bridge::fixture_branch(&bank, self.inventory()?.as_ref())?
                };
                let verifier = Verifier::<H>::new(&key, RandomProfile::CachedGtAnchor);
                let store = SpentStore::with_preexisting_records(10000, verifier.namespace(), 32)
                    .map_err(err)?;
                if s.sparse {
                    let evens: Vec<_> = (0..1024).step_by(2).map(|i| (0, i)).collect();
                    let p = bridge::payment::<H>(&bank.spend_prepared_blocks(&mut w, &evens)?)?
                        .checked::<H>()?;
                    rt::verify_and_record(
                        &verifier,
                        &[p],
                        b"genuine-prior-even512",
                        b"accepted",
                        &store,
                        Mode::Randomized,
                        &mut rng,
                    )
                    .map_err(err)?;
                    if s.phase == "preparation" {
                        w.proofs = Rc::new(Default::default());
                    }
                }
                if s.phase == "preparation" {
                    return Ok(Box::new(move |clock: &mut BoundaryClock| {
                        let before = w.prepared_proofs();
                        let (n, p, wire) = clock.measure(|| {
                            let n = bank.precompute_amount(&mut w, s.k, &mut rng)?;
                            let p = bridge::payment::<H>(&bank.spend_prepared(&mut w, s.k)?)?;
                            let wire = p.encode();
                            Ok((n, p, wire))
                        })?;
                        key.verify::<H>(
                            &[p],
                            Mode::Specification,
                            RandomProfile::CachedGtAnchor,
                            &mut rng,
                        )?;
                        Ok(
                            json!({"new_native_Groth16_proofs":n-before,"prepared_proofs":n,"k":s.k,"full_inventory":false,"backend":"Arkworks0.3","payment_bytes":wire.len(),"wallet_state_advanced_in_preparation":true,"point_conversion_and_encoding_included":true}),
                        )
                    }));
                }
                if s.phase == "online" {
                    let p = bridge::payment::<H>(&bank.spend_prepared(&mut w, s.k)?)?;
                    key.verify::<H>(
                        std::slice::from_ref(&p),
                        Mode::Specification,
                        RandomProfile::CachedGtAnchor,
                        &mut rng,
                    )?;
                    let wire = p.encode();
                    let blocks = p.blocks.len();
                    let unused = w.unused();
                    return Ok(Box::new(move |clock: &mut BoundaryClock| {
                        let wire = clock.measure(move || Ok(wire))?;
                        std::hint::black_box(&wire);
                        Ok(
                            json!({"k":s.k,"native_blocks":blocks,"payment_bytes":wire.len(),"unused_after":unused,"one_use_preencoded_delivery":true,"online_group_operations":0}),
                        )
                    }));
                }
                if s.phase == "native_total_reference" {
                    return Ok(Box::new(move |clock: &mut BoundaryClock| {
                        let p = clock.measure(|| bank.spend_prepared(&mut w, s.k))?;
                        Ok(
                            json!({"k":s.k,"native_blocks":p.blocks.len(),"native_reference":"spend_prepared_without_adapter_conversion_or_serialization","payment_bytes":p.encode().len()}),
                        )
                    }));
                }
                let native = bank.spend_prepared(&mut w, s.k)?;
                let p = bridge::payment::<H>(&native)?;
                let wire = p.encode();
                let p = decode_received::<H>(&[wire.as_slice()])?.pop().unwrap();
                key.verify_checked::<H>(
                    std::slice::from_ref(&p),
                    Mode::Specification,
                    RandomProfile::CachedGtAnchor,
                    &mut rng,
                )?;
                if bank.expand_after_verification(&native)?.serials != p.redeem_serials::<H>()? {
                    return Err("native/common serial mismatch".into());
                }
                let ids = if s.phase == "state" {
                    Some(p.redeem_serials::<H>()?)
                } else {
                    None
                };
                Ok(Box::new(move |clock: &mut BoundaryClock| {
                    let mode = if s.random {
                        Mode::Randomized
                    } else {
                        Mode::Specification
                    };
                    let profile = if s.pair {
                        RandomProfile::PairingAnchor
                    } else {
                        RandomProfile::CachedGtAnchor
                    };
                    let mut coins = verifier_rng(clock, trial ^ 0x3300)?;
                    // The hot key is already checked and installed; a cold total installs the
                    // actual same mathematical key inside its measured boundary.
                    let result = match s.phase {
                        "bank_verify" => {
                            clock.measure(|| {
                                let decoded = decode_received::<H>(&[wire.as_slice()])?;
                                let cold = s.cold.then(|| bridge::key(&bank)).transpose()?;
                                cold.as_ref()
                                    .unwrap_or(&key)
                                    .verify_checked::<H>(&decoded, mode, profile, &mut coins)
                            })?;
                            json!({"accepted":true})
                        }
                        "strict_decoding" => {
                            let decoded =
                                clock.measure(|| decode_received::<H>(&[wire.as_slice()]))?;
                            json!({"decoded_payments":decoded.len(),"decoded_amount":decoded[0].amount,"decoded_native_blocks":decoded[0].blocks.len(),"decode_only":true})
                        }
                        "deposit" => {
                            let ids = clock.measure(|| p.redeem_serials::<H>())?;
                            json!({"serials":ids.len()})
                        }
                        "state" => {
                            let v = Verifier::<H>::new(&key, profile);
                            let ids = ids
                                .unwrap()
                                .iter()
                                .map(|x| Identifier::new(v.namespace(), x).map_err(err))
                                .collect::<Result<Vec<_>>>()?;
                            let request =
                                rt::bound_request(&v, std::slice::from_ref(&p), b"new-payment");
                            let accepted = clock.measure(|| {
                                store
                                    .record_checked(&request, &ids, b"accepted")
                                    .map_err(err)
                            })?;
                            json!({"registered":accepted.newly_registered,"state_scope":"record_checked_body_only"})
                        }
                        "backend" => {
                            let v = Verifier::<H>::new(&key, profile);
                            let a = clock.measure(|| {
                                let ids = p
                                    .redeem_serials::<H>()?
                                    .iter()
                                    .map(|x| Identifier::new(v.namespace(), x).map_err(err))
                                    .collect::<Result<Vec<_>>>()?;
                                {
                                    let request = rt::bound_request(
                                        &v,
                                        std::slice::from_ref(&p),
                                        b"new-payment",
                                    );
                                    store.record_checked(&request, &ids, b"accepted")
                                }
                                .map_err(err)
                            })?;
                            json!({"registered":a.newly_registered})
                        }
                        "inclusive_reference" => {
                            let a = clock.measure(|| {
                                let decoded = decode_received::<H>(&[wire.as_slice()])?;
                                let cold = s.cold.then(|| bridge::key(&bank)).transpose()?;
                                let v = Verifier::<H>::new(cold.as_ref().unwrap_or(&key), profile);
                                rt::verify_and_record(
                                    &v,
                                    &decoded,
                                    b"new-payment",
                                    b"accepted",
                                    &store,
                                    mode,
                                    &mut coins,
                                )
                                .map_err(err)
                            })?;
                            json!({"registered":a.newly_registered})
                        }
                        _ => return Err("unknown native LCB phase".into()),
                    };
                    Ok(
                        json!({"native_result":result,"k":s.k,"native_blocks":p.blocks.len(),"denoms":p.blocks.iter().map(|b|b.denom).collect::<Vec<_>>(),"payment_bytes":wire.len(),"prior_units":if s.sparse{512}else{0},"state_after":store.counts().map_err(err)?}),
                    )
                }))
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use darlt_spseq_fc::experiment::{BoundaryClock, RunMode};
    #[test]
    fn pipeline_calibration_updates_trial_inputs_and_shares_the_two_backends() {
        use darlt_spseq_fc::experiment::RunMode;
        let mut f = Factory::<1>::new_for_height().unwrap();
        let ids = vec![
            "LCB24/calibration/G1_MSM/n16/Arkworks0.3".into(),
            "LCB24/calibration/G1_MSM/n16/blstrs0.7.1".into(),
        ];
        let mut previous = None;
        for trial in [33006, 33007] {
            let action = f.prepare_pipeline(&ids, trial).unwrap();
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
            let value = action(&mut clock).unwrap();
            let results = value["primitive_results"].as_array().unwrap();
            assert_eq!(
                results[0]["value"]["input_digest"],
                results[1]["value"]["input_digest"]
            );
            let digest = results[0]["value"]["input_digest"].clone();
            if let Some(previous) = previous {
                assert_ne!(previous, digest);
            }
            previous = Some(digest);
            assert_eq!(f.calibrations.len(), 1);
            assert_eq!(clock.observations().len(), 2);
        }
    }
    #[test]
    fn pipeline_stock_reuse_changes_complete_request_and_shares_same_slot_wire() {
        use darlt_spseq_fc::experiment::RunMode;
        let mut f = Factory::<2>::new_for_height().unwrap();
        let ids: Vec<_> = f
            .jobs()
            .iter()
            .filter(|j| {
                j.workload["k"] == 1
                    && matches!(
                        j.stage.as_str(),
                        "online"
                            | "bank_verify"
                            | "strict_decoding"
                            | "deposit"
                            | "state"
                            | "backend"
                            | "inclusive_reference"
                    )
            })
            .map(|j| j.id.clone())
            .collect();
        let mut results = vec![];
        let mut stocks = vec![];
        for trial in [33001, 33002] {
            let action = f.prepare_pipeline(&ids, trial).unwrap();
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
            let value = action(&mut clock).unwrap();
            assert_eq!(clock.observations().len(), ids.len());
            assert!(clock
                .observations()
                .values()
                .all(|x| x["ok"] == true && x["elapsed_ns"].is_null()));
            assert_eq!(value["cases"][0]["native_proof_bytes_reused"], true);
            results.push(value["cases"][0].clone());
            stocks.push(Rc::as_ptr(f.inventory.borrow().as_ref().unwrap()));
        }
        assert_eq!(stocks[0], stocks[1]);
        assert_eq!(
            results[0]["native_payment_digest"],
            results[1]["native_payment_digest"]
        );
        assert_ne!(
            results[0]["actual_request_digest"],
            results[1]["actual_request_digest"]
        );
        let mut prepared_ids = ids.clone();
        prepared_ids.push(
            f.jobs()
                .iter()
                .find(|j| j.stage == "preparation" && j.workload["k"] == 1)
                .unwrap()
                .id
                .clone(),
        );
        let action = f.prepare_pipeline(&prepared_ids, 33003).unwrap();
        let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
        let prepared = action(&mut clock).unwrap();
        assert_eq!(
            prepared["cases"][0]["fresh_native_proofs_prepared_this_slot"],
            true
        );
        assert_ne!(
            prepared["cases"][0]["native_payment_digest"],
            results[0]["native_payment_digest"]
        );
        assert_eq!(
            Rc::as_ptr(f.inventory.borrow().as_ref().unwrap()),
            stocks[0]
        );
        assert_eq!(clock.observations().len(), prepared_ids.len());
    }
    #[test]
    fn pipeline_full_inventory_is_real_and_updates_one_ram_stock() {
        use darlt_spseq_fc::experiment::RunMode;
        let mut f = Factory::<1>::new_for_height().unwrap();
        let issuance = vec![
            "LCB24/issue_request".into(),
            "LCB24/issue_response".into(),
            "LCB24/issue_receive".into(),
        ];
        let issue = f.prepare_pipeline(&issuance, 33000).unwrap();
        let mut issue_clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
        let issue_value = issue(&mut issue_clock).unwrap();
        {
            let received = f.inventory.borrow();
            let received = received.as_ref().unwrap();
            assert_eq!(
                issue_value["role_bytes"][0]["role_job_ids"],
                serde_json::to_value(&issuance).unwrap()
            );
            assert_eq!(
                issue_value["role_bytes"][0]["request_bytes"],
                encoded(&received.commitment).len()
            );
            assert_eq!(
                issue_value["role_bytes"][0]["response_bytes"],
                signature_bytes(&received.signature).len()
            );
            assert_eq!(
                issue_value["role_bytes"][0]["wallet_component_bytes"],
                wallet_component_bytes(received)
            );
            assert_eq!(
                issue_value["public_package_bytes"],
                public_component_bytes(&f.bank.borrow(), &f.key.borrow())
            );
        }

        assert_eq!(issue_clock.observations().len(), 3);
        assert_eq!(&*f.asset_origin.borrow(), "first_pipeline_issue_receive");
        let received_statement = encoded(&f.inventory.borrow().as_ref().unwrap().commitment);
        let mut statements = vec![];
        let mut proofs = vec![];
        let mut history = None;
        let mut remaining_serials = None;
        for trial in [33004, 33005] {
            let action = f
                .prepare_pipeline(&["LCB24/full_inventory".into()], trial)
                .unwrap();
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
            let value = action(&mut clock).unwrap();
            assert_eq!(value["native_Ark_Groth16_proofs"], 2);
            assert_eq!(value["full_inventory_cache_hit"], false);
            assert_eq!(
                value["precomputed_proof_bytes"],
                f.inventory.borrow().as_ref().unwrap().proof_cache_bytes()
            );
            assert_eq!(
                value["wallet_component_bytes"],
                wallet_component_bytes(f.inventory.borrow().as_ref().unwrap())
            );
            assert_eq!(f.inventory.borrow().as_ref().unwrap().prepared_proofs(), 2);
            let stock = f.inventory.borrow();
            let stock = stock.as_ref().unwrap();
            statements.push(encoded(&stock.commitment));
            proofs.push(
                blake3::hash(&stock.proofs.values().flat_map(encoded).collect::<Vec<_>>())
                    .to_hex()
                    .to_string(),
            );
            let bank = f.bank.borrow().clone();
            let key = f.key.borrow().clone();
            let v = Verifier::<1>::new(&key, RandomProfile::CachedGtAnchor);
            if trial == 33004 {
                let mut sparse = bridge::fixture_branch(&bank, stock).unwrap();
                let p = bridge::payment::<1>(
                    &bank.spend_prepared_blocks(&mut sparse, &[(0, 0)]).unwrap(),
                )
                .unwrap();
                let wire = p.encode();
                let checked = decode_received::<1>(&[&wire]).unwrap();
                let store = SpentStore::with_preexisting_records(4, v.namespace(), 32).unwrap();
                let fresh = store.snapshot().unwrap();
                rt::verify_and_record(
                    &v,
                    &checked,
                    b"fixed-prior",
                    b"accepted",
                    &store,
                    Mode::Specification,
                    &mut StdRng::seed_from_u64(1),
                )
                .unwrap();
                let request = rt::bound_request(&v, &checked, b"fixed-prior");
                let ids = v
                    .identifiers(&checked)
                    .unwrap()
                    .iter()
                    .map(|x| Identifier::new(v.namespace(), x).unwrap())
                    .collect::<Vec<_>>();
                history = Some((request, ids, store.counts().unwrap()));
                let mut next = bridge::fixture_branch(&bank, &sparse).unwrap();
                let p = bridge::payment::<1>(
                    &bank.spend_prepared_blocks(&mut next, &[(0, 1)]).unwrap(),
                )
                .unwrap();
                key.verify_received::<1>(
                    &[&p.encode()],
                    Mode::Specification,
                    RandomProfile::CachedGtAnchor,
                    &mut StdRng::seed_from_u64(2),
                )
                .unwrap();
                remaining_serials = Some(p.redeem_serials::<1>().unwrap());
                *f.snapshots.borrow_mut() = Some(PoolSnapshots {
                    fresh,
                    sparse: Some((sparse, store.snapshot().unwrap())),
                });
            } else {
                let snapshots = f.snapshots.borrow();
                let pool = snapshots
                    .as_ref()
                    .expect("inventory regeneration retained snapshots");
                let (sparse, snapshot) = pool.sparse.as_ref().unwrap();
                assert_eq!(sparse.used, vec![true, false]);
                assert!(Rc::ptr_eq(&sparse.proofs, &stock.proofs));
                assert_eq!(
                    SpentStore::from_snapshot(&pool.fresh).counts().unwrap(),
                    (4, 4)
                );
                let store = SpentStore::from_snapshot(snapshot);
                let (request, ids, counts) = history.as_ref().unwrap();
                assert_eq!(&store.counts().unwrap(), counts);
                assert!(
                    store
                        .record_checked(request, ids, b"replacement")
                        .unwrap()
                        .replayed
                );
                assert_eq!(&store.counts().unwrap(), counts);
                let mut next = bridge::fixture_branch(&bank, sparse).unwrap();
                let p = bridge::payment::<1>(
                    &bank.spend_prepared_blocks(&mut next, &[(0, 1)]).unwrap(),
                )
                .unwrap();
                key.verify_received::<1>(
                    &[&p.encode()],
                    Mode::Specification,
                    RandomProfile::CachedGtAnchor,
                    &mut StdRng::seed_from_u64(2),
                )
                .unwrap();
                assert_eq!(
                    p.redeem_serials::<1>().unwrap(),
                    remaining_serials.as_ref().unwrap().clone()
                );
            }
        }
        assert_eq!(statements[0], received_statement);
        assert_eq!(statements[0], statements[1]);
        assert_ne!(proofs[0], proofs[1]);
    }
    #[test]
    fn every_small_native_role_stage_executes_without_clock() {
        let mut f = Factory::<2>::new_for_height().unwrap();
        for j in f.jobs() {
            let action = f.prepare(&j.id, 1).unwrap();
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None).unwrap();
            let v = action(&mut clock).unwrap();
            assert!(!v.is_null(), "{}", j.id);
            assert!(!clock.segments().is_empty(), "{}", j.id);
            assert_eq!(clock.elapsed_ns(), None);
        }
        assert_eq!(f.calibrations.len(), 21);
        let _action = f
            .prepare("LCB24/calibration/G1_MSM/n16/Arkworks0.3", 99999)
            .unwrap();
        let before = f.calibrations["calibrate_g1_msm/16"].clone();
        let _action = f
            .prepare("LCB24/calibration/G1_MSM/n16/blstrs0.7.1", 99999)
            .unwrap();
        assert_eq!(f.calibrations.len(), 21);
        assert!(Rc::ptr_eq(&before, &f.calibrations["calibrate_g1_msm/16"]));
    }
    #[test]
    fn native_signature_response_codec_is_complete_and_strict() {
        let mut rng = StdRng::seed_from_u64(123);
        let b = Bank::<1>::setup(&mut rng).unwrap();
        let pending = b.customer_request(&mut rng).unwrap();
        let sig = b.issuer_response(pending.commitment(), &mut rng).unwrap();
        let raw = signature_bytes(&sig);
        assert_eq!(raw.len(), 64);
        let decoded = signature_decode(&raw).unwrap();
        assert_eq!(signature_bytes(&decoded), raw);
        b.customer_receive(pending, decoded).unwrap();
        assert!(signature_decode(&raw[..63]).is_err());
        let mut bad = raw;
        bad[..32].fill(255);
        assert!(signature_decode(&bad).is_err());
    }
}
