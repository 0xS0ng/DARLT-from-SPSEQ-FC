//! Repeatable native role/stage workers for the six established baselines.
//! Each role records its actual local native segments. Pipeline outputs are
//! forwarded directly; immutable public installations and source wallets persist.
use crate::{
    experiment::{Action, BoundaryClock, Job, Worker},
    harness::{Role, Scheme, Stage},
};
use baseline_core::{
    arithmetic::S,
    bhn26 as niat, hintoken as hin, klo26 as cpat,
    msb23::{scheme as msb, wire},
    slw25 as slw, sma2rt as sma,
};
use ff::Field;
use rand::{rngs::StdRng, RngCore, SeedableRng};
use serde_json::{json, Value};
use std::{
    any::Any,
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

type Result<T> = std::result::Result<T, String>;
type Cache = Rc<RefCell<BTreeMap<String, Rc<dyn Any>>>>;
const KS: [usize; 9] = crate::campaign::K_VALUES;
const DONE: &str = "selected public-fixture boundary complete";
struct Output<T> {
    value: T,
    messages: Option<Vec<Vec<u8>>>,
}
impl<T> Output<T> {
    fn value(value: T) -> Self {
        Self {
            value,
            messages: None,
        }
    }
    fn with_messages(value: T, messages: Vec<Vec<u8>>) -> Self {
        Self {
            value,
            messages: Some(messages),
        }
    }
}

#[derive(Clone, Copy, Default)]
struct WireFields {
    g1: usize,
    g2: usize,
    gt: usize,
    fr: usize,
}
impl WireFields {
    fn add(&mut self, other: Self) {
        self.g1 += other.g1;
        self.g2 += other.g2;
        self.gt += other.gt;
        self.fr += other.fr;
    }
    fn json(self) -> Value {
        json!({"G1":self.g1,"G2":self.g2,"GT":self.gt,"Fr":self.fr})
    }
}
fn decode_sma(
    h: &sma::InstalledInstance,
    policy: &sma::Policy,
    bytes: &[Vec<u8>],
) -> Result<Vec<sma::CheckedToken>> {
    bytes
        .iter()
        .map(|b| sma::CheckedToken::decode_received_installed(h, b, policy).map_err(native_error))
        .collect()
}
fn decode_niat(bytes: &[Vec<u8>]) -> Result<Vec<niat::CheckedToken>> {
    bytes
        .iter()
        .map(|b| niat::CheckedToken::decode(b).map_err(native_error))
        .collect()
}
fn decode_cpat(policy: &cpat::Policy, bytes: &[Vec<u8>]) -> Result<Vec<cpat::CheckedToken>> {
    bytes
        .iter()
        .map(|b| {
            let token = cpat::CheckedToken::decode_received(b).map_err(native_error)?;
            need(
                policy.allowed.contains(&token.as_token().tag),
                "unexpected native service tag",
            )?;
            Ok(token)
        })
        .collect()
}
fn decode_hin(bytes: &[Vec<u8>]) -> Result<Vec<hin::CheckedToken>> {
    bytes
        .iter()
        .map(|b| hin::CheckedToken::decode(b).map_err(native_error))
        .collect()
}
// Statistics only: inspect frame widths, never decompress points or create a
// value usable by a native algorithm. Failure produces absent statistics; the
// actual strict decoder inside the selected boundary alone decides acceptance.
fn slw_wire_fields(bytes: &[u8]) -> WireFields {
    fn parse(bytes: &[u8]) -> Option<WireFields> {
        struct Frame<'a> {
            bytes: &'a [u8],
            at: usize,
        }
        impl<'a> Frame<'a> {
            fn take(&mut self, n: usize) -> Option<&'a [u8]> {
                let end = self.at.checked_add(n)?;
                let out = self.bytes.get(self.at..end)?;
                self.at = end;
                Some(out)
            }
            fn u64(&mut self) -> Option<usize> {
                usize::try_from(u64::from_be_bytes(self.take(8)?.try_into().ok()?)).ok()
            }
            fn u32(&mut self) -> Option<usize> {
                Some(u32::from_be_bytes(self.take(4)?.try_into().ok()?) as usize)
            }
        }
        let mut r = Frame { bytes, at: 0 };
        if r.take(5)? != b"BLSB\x01" {
            return None;
        }
        let n = r.u64()?;
        let tag = r.take(n)?;
        let fields = match tag {
            b"SLW24-show-prefix-v1" => {
                let keep = r.u64()?;
                r.take(keep.checked_mul(4)?)?;
                let values = r.u64()?;
                r.take(values.checked_mul(4)?)?;
                r.take(values.checked_mul(32)?)?;
                r.take(2 * 48 + 2 * 96)?;
                WireFields {
                    g1: 2,
                    g2: 2,
                    gt: 0,
                    fr: values,
                }
            }
            b"CDM-P2-v1" => {
                r.take(32)?;
                let mut out = WireFields {
                    fr: 1,
                    ..Default::default()
                };
                for _ in 0..2 {
                    match r.take(1)?[0] {
                        0 => {
                            r.take(96)?;
                            out.g2 += 1
                        }
                        1 => {
                            r.take(288)?;
                            out.gt += 1
                        }
                        _ => return None,
                    }
                }
                out
            }
            b"CDM-P4-v1" => {
                r.take(32)?;
                let first = r.u32()?;
                r.take(first.checked_mul(32)?)?;
                let last = r.u32()?;
                r.take(last.checked_mul(32)?)?;
                WireFields {
                    fr: 1 + first + last,
                    ..Default::default()
                }
            }
            _ => return None,
        };
        (r.at == bytes.len()).then_some(fields)
    }
    parse(bytes).unwrap_or_default()
}

// Same public-ID precheck as batch_runtime::duplicate_diagnosis, applied to
// these four sealed received families before invoking native verification.
// No signature/proof result, group check or decoded input is cached here.
fn received_duplicate_precheck<D: Any>(received: &D) -> Result<()> {
    let any = received as &dyn Any;
    let ids = if let Some(tokens) = any.downcast_ref::<Vec<sma::CheckedToken>>() {
        tokens
            .iter()
            .map(|t| t.as_token().serial.to_compressed().to_vec())
            .collect::<Vec<_>>()
    } else if let Some(tokens) = any.downcast_ref::<Vec<niat::CheckedToken>>() {
        tokens
            .iter()
            .map(|t| niat::redemption_tag(t.as_token()).to_vec())
            .collect()
    } else if let Some(tokens) = any.downcast_ref::<Vec<cpat::CheckedToken>>() {
        tokens
            .iter()
            .map(|t| {
                let t = t.as_token();
                let mut id = (t.tag.len() as u64).to_be_bytes().to_vec();
                id.extend(&t.tag);
                id.extend(t.delta.to_compressed());
                id
            })
            .collect()
    } else if let Some(tokens) = any.downcast_ref::<Vec<hin::CheckedToken>>() {
        tokens.iter().map(|t| t.as_token().message_id()).collect()
    } else {
        return Err("unknown sealed received family for duplicate-ID precheck".into());
    };
    let mut owners = BTreeMap::<Vec<u8>, Vec<usize>>::new();
    for (i, id) in ids.into_iter().enumerate() {
        owners.entry(id).or_default().push(i);
    }
    let bad = owners
        .into_values()
        .filter(|v| v.len() > 1)
        .flatten()
        .collect::<BTreeSet<_>>();
    need(bad.is_empty(), "duplicate complete native identifiers")
}

fn slot_application_operation(trial: u64, k: usize, attributes: usize) -> [u8; 25] {
    let mut operation = [0u8; 25];
    operation[0] = 0x33;
    operation[1..9].copy_from_slice(&trial.to_be_bytes());
    operation[9..17].copy_from_slice(&(k as u64).to_be_bytes());
    operation[17..25].copy_from_slice(&(attributes as u64).to_be_bytes());
    operation
}

struct Phase {
    role: Role,
    stage: Stage,
    profile: &'static str,
    encode: bool,
    decode: bool,
}
impl Phase {
    fn new(role: Role, stage: Stage, profile: &'static str) -> Self {
        Self {
            role,
            stage,
            profile,
            encode: false,
            decode: false,
        }
    }
    fn encoded(mut self) -> Self {
        self.encode = true;
        self
    }
    fn decoded(mut self) -> Self {
        self.decode = true;
        self
    }
}
fn name<T: serde::Serialize>(v: T) -> String {
    serde_json::to_value(v).unwrap().as_str().unwrap().into()
}
fn group(role: Role, stage: Stage) -> Stage {
    if role == Role::Issuer && stage == Stage::VerificationCrypto {
        Stage::IssueResponse
    } else if role == Role::Agent && stage == Stage::DelegateRequest {
        Stage::DelegateReceive
    } else {
        stage
    }
}
fn profile(scheme: Scheme, phase: &Phase) -> String {
    if phase.stage == Stage::Install {
        phase.profile.into()
    } else if scheme == Scheme::Niat
        && matches!(phase.stage, Stage::IssueResponse | Stage::IssueAccept)
    {
        "Prepared".into()
    } else if matches!(scheme, Scheme::Msb23 | Scheme::Slw25)
        && ((phase.role == Role::Verifier
            && matches!(
                phase.stage,
                Stage::VerificationCrypto | Stage::InclusiveVerification
            ))
            || matches!(
                phase.stage,
                Stage::IssueAccept | Stage::DelegateReceive | Stage::DelegateRequest
            ))
    {
        "Randomized".into()
    } else if matches!(
        phase.stage,
        Stage::VerificationCrypto | Stage::InclusiveVerification | Stage::SharedState
    ) && phase.role == Role::Verifier
    {
        phase.profile.into()
    } else if matches!(phase.stage, Stage::MetadataRead | Stage::NativeRead) {
        "bit0".into()
    } else {
        "native".into()
    }
}
#[derive(Clone)]
struct Spec {
    job: Job,
    scheme: Scheme,
    role: Role,
    stage: Stage,
    k: Option<usize>,
    event_profile: String,
    bit: u8,
}
struct Recorder<'a> {
    attributes: usize,
    profile: String,
    bit: u8,
    cache: Cache,
    clock: Option<&'a mut BoundaryClock>,
    target: Option<Spec>,
    pipeline_targets: Vec<Spec>,
    pipeline_trial: Option<u64>,
    retained: BTreeMap<String, Rc<dyn Any>>,
    pipeline_observations: BTreeMap<String, Value>,
    pipeline_requests: BTreeMap<usize, Value>,
    pipeline_profile_order: BTreeMap<usize, Vec<String>>,
    catalog: BTreeMap<String, Spec>,
    segments: usize,
    message_sizes: Vec<usize>,
    completed_profiles: Vec<String>,
    last_messages: Option<Vec<Vec<u8>>>,
    received_fields: WireFields,
    received_sizes: Vec<usize>,
}
impl Recorder<'_> {
    fn decode_only(&self) -> bool {
        self.target
            .as_ref()
            .is_some_and(|t| t.job.boundary["decode_only"] == true)
    }
    fn decoded_observation(&mut self, fields: WireFields, bytes: &[Vec<u8>], phase: &str) {
        self.received_fields.add(fields);
        self.received_sizes.extend(bytes.iter().map(Vec::len));
        self.completed_profiles.push(format!(
            "{}:{phase}",
            if self.decode_only() {
                "strict_decode"
            } else {
                "received_decode_and_native"
            }
        ));
    }
    fn spec(&self, scheme: Scheme, phase: &Phase, k: Option<usize>) -> Spec {
        let stage = group(phase.role, phase.stage);
        let p = if self.is_pipeline()
            && matches!(scheme, Scheme::Msb23 | Scheme::Slw25)
            && phase.role == Role::Verifier
            && matches!(
                phase.stage,
                Stage::VerificationCrypto | Stage::InclusiveVerification
            ) {
            self.profile.clone()
        } else {
            profile(scheme, phase)
        };
        let dimension = matches!(scheme, Scheme::Sma2rt | Scheme::Msb23 | Scheme::Slw25)
            .then_some(self.attributes);
        let id = format!(
            "baseline/{}/a{}/{}/{}/k{}/{}",
            name(scheme),
            dimension.map_or("na".into(), |a| a.to_string()),
            name(phase.role),
            name(stage),
            k.map_or("na".into(), |v| v.to_string()),
            p
        );
        let mut job = Job::new(&id, scheme.label(), &name(phase.role), &name(stage));
        job.profile = p.clone();
        job.cache = if stage == Stage::Install {
            "cold"
        } else if matches!(stage, Stage::Setup | Stage::KeyGeneration) {
            "not_applicable"
        } else {
            "hot"
        }
        .into();
        job.workload = json!({"k":k,"attributes":dimension,"n":if scheme==Scheme::Sma2rt{Some(1024)}else{None},
            "variant":p,"native_semantics":if matches!(scheme,Scheme::Msb23|Scheme::Slw25){"k complete native presentations; no native quota"}else{"native independent units or declared wallet"},
            "fixture_initialization":"unmeasured fresh one-use state; reused validated immutable public installation",
            "actual_business_attributes":dimension,
            "native_capacity_parameter":if scheme==Scheme::Msb23{Some(self.attributes)}else{None},
            "period_coordinate_count":if scheme==Scheme::Msb23{Some(1)}else{None},
            "native_signed_coordinates":match scheme{Scheme::Niat=>Some(3),Scheme::Cpat|Scheme::HinToken=>Some(4),_=>None},
            "known_before_context":["policy","service_tag","unit_selection"],"online_context":if matches!(scheme,Scheme::Sma2rt|Scheme::Msb23|Scheme::Slw25){"fresh context or live verifier messages"}else{"native protocol has no added context proof"}});
        job.boundary = json!({"safe":true,"network_included":false,"persistence_included":false,"shared_state_included":false,
            "wire_encoding_included":phase.encode,"strict_decoding_included":phase.decode,"live_role_segments":true});
        if scheme == Scheme::Niat && phase.profile == "native_C3_original_all_ones_reference" {
            job.boundary["safe"] = json!(false);
            job.boundary["reference_only"] = json!(true);
            job.workload["reference_reason"]=json!("original all-ones aggregate; excluded from safe runtime and fastest-variant selection");
        }
        if (phase.role == Role::Verifier
            && matches!(
                stage,
                Stage::VerificationCrypto | Stage::InclusiveVerification
            ))
            || (stage == Stage::NativeRead
                && matches!(scheme, Scheme::Niat | Scheme::Cpat | Scheme::HinToken))
        {
            for key in [
                "strict_decoding_included",
                "received_bytes_first",
                "subgroup_checks_included",
                "native_format_checks_included",
            ] {
                job.boundary[key] = json!(true);
            }
            job.boundary["subgroup_checks_per_received_element"] = json!(1);
            job.boundary["received_input_provenance"] = json!("sealed_checked_input");
            if !matches!(scheme, Scheme::Msb23 | Scheme::Slw25) {
                job.boundary["all_packets_decoded_before_algorithm"] = json!(true);
            } else {
                job.boundary["received_each_live_leg_first"] = json!(true);
            }
        }
        if matches!(
            stage,
            Stage::Setup
                | Stage::KeyGeneration
                | Stage::Install
                | Stage::IssueRequest
                | Stage::IssueResponse
                | Stage::IssueAccept
                | Stage::DelegateRequest
                | Stage::DelegateSend
                | Stage::DelegateReceive
        ) {
            job.boundary["optional_unmapped_role_candidate"] = json!(true);
        }
        job.boundary["same_call_strict_decoding_component"] = json!(
            phase.role == Role::Verifier
                && matches!(
                    stage,
                    Stage::VerificationCrypto | Stage::InclusiveVerification
                )
        );
        Spec {
            job,
            scheme,
            role: phase.role,
            stage,
            k,
            event_profile: if phase.role == Role::Verifier
                && matches!(
                    phase.stage,
                    Stage::VerificationCrypto | Stage::InclusiveVerification | Stage::SharedState
                )
                && !matches!(scheme, Scheme::Msb23 | Scheme::Slw25)
            {
                phase.profile.into()
            } else {
                String::new()
            },
            bit: 0,
        }
    }
    fn matches(t: &Spec, s: &Spec, pipeline: bool) -> bool {
        if pipeline && t.job.boundary["decode_only"] == true {
            return false;
        }
        t.scheme == s.scheme
            && t.role == s.role
            && (t.stage == s.stage
                || (t.stage == Stage::InclusiveVerification
                    && s.stage == Stage::VerificationCrypto
                    && s.role == Role::Verifier
                    && (pipeline || matches!(s.scheme, Scheme::Msb23 | Scheme::Slw25))))
            && t.k == s.k
            && (t.event_profile.is_empty() || t.event_profile == s.event_profile)
            && (!pipeline
                || !matches!(s.scheme, Scheme::Msb23 | Scheme::Slw25)
                || !matches!(
                    s.stage,
                    Stage::VerificationCrypto | Stage::InclusiveVerification
                )
                || t.job.profile == s.job.profile)
    }
    fn is_pipeline(&self) -> bool {
        self.pipeline_trial.is_some()
    }
    fn selected(&self, s: &Spec) -> bool {
        self.target
            .as_ref()
            .is_some_and(|t| Self::matches(t, s, false))
            || self
                .pipeline_targets
                .iter()
                .any(|t| Self::matches(t, s, true))
    }
    fn pipeline_matches(&self, s: &Spec) -> Vec<Spec> {
        self.pipeline_targets
            .iter()
            .filter(|t| Self::matches(t, s, true))
            .cloned()
            .collect()
    }
    fn verifier_profiles(&mut self, scheme: Scheme, k: usize) -> Vec<String> {
        let mut profiles = self
            .pipeline_targets
            .iter()
            .filter(|s| {
                s.scheme == scheme
                    && s.k == Some(k)
                    && matches!(
                        s.stage,
                        Stage::VerificationCrypto | Stage::InclusiveVerification
                    )
                    && s.job.boundary["decode_only"] != true
            })
            .map(|s| s.job.profile.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if profiles.is_empty() {
            profiles.push("Randomized".into());
        }
        let offset = self.pipeline_trial.unwrap_or(0) as usize % profiles.len();
        profiles.rotate_left(offset);
        self.pipeline_profile_order.insert(k, profiles.clone());
        profiles
    }
    fn received_key(&self, scheme: Scheme, k: Option<usize>, profile: &str) -> String {
        format!("{}/{k:?}/{profile}", name(scheme))
    }
    fn application_operation(&self, k: usize) -> Vec<u8> {
        self.pipeline_trial.map_or_else(
            || b"baseline-native-operation".to_vec(),
            |trial| slot_application_operation(trial, k, self.attributes).to_vec(),
        )
    }
    fn record_pipeline_observation(&mut self, job: &str, wire: &[Vec<u8>], k: usize) {
        use sha2::{Digest, Sha256};
        let mut complete = self.application_operation(k);
        for bytes in wire {
            framed(&mut complete, bytes);
        }
        let hash = Sha256::digest(&complete)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        let observed=self.pipeline_observations.entry(job.into()).or_insert_with(||json!({"received_only_sha256":hash,"application_nonce":self.pipeline_trial,"proof_or_token_result_memoized":false}));
        observed["actual_received_message_sizes"] =
            json!(wire.iter().map(Vec::len).collect::<Vec<_>>());
    }
    fn pipeline_rng(&self, scheme: Scheme, k: usize, domain: &str) -> StdRng {
        use sha2::{Digest, Sha256};
        let mut hash = Sha256::new();
        hash.update(b"DARLT/sampling/native-pipeline-rng-seed/v1");
        hash.update(self.pipeline_trial.unwrap_or(0).to_be_bytes());
        hash.update((self.attributes as u64).to_be_bytes());
        hash.update((k as u64).to_be_bytes());
        hash.update(name(scheme).as_bytes());
        hash.update(domain.as_bytes());
        StdRng::from_seed(hash.finalize().into())
    }
    fn verification_rng(&self, scheme: Scheme, k: usize, domain: &str) -> Result<StdRng> {
        weight_rng_for_mode(
            self.clock
                .as_ref()
                .map_or(crate::experiment::RunMode::ClockFree, |clock| clock.mode()),
            self.pipeline_rng(scheme, k, domain),
        )
    }
    fn capture<T>(&mut self, spec: &Spec, action: impl FnOnce() -> Result<T>) -> Result<T> {
        let clock = self.clock.as_deref_mut().ok_or("pipeline clock missing")?;
        clock.capture(&spec.job.id, |clock| clock.measure(action))
    }
    fn remember(&mut self, s: Spec, phase: &Phase) {
        self.catalog
            .entry(s.job.id.clone())
            .and_modify(|old| {
                old.job.boundary["wire_encoding_included"] = json!(
                    old.job.boundary["wire_encoding_included"]
                        .as_bool()
                        .unwrap()
                        || phase.encode
                );
                old.job.boundary["strict_decoding_included"] = json!(
                    old.job.boundary["strict_decoding_included"]
                        .as_bool()
                        .unwrap()
                        || phase.decode
                );
            })
            .or_insert(s);
    }
    fn observe_output<T>(&mut self, spec: &Spec, out: &Output<T>) -> Result<()> {
        if !self.is_pipeline() {
            return Ok(());
        }
        let packets = out
            .messages
            .as_ref()
            .map(|messages| {
                messages
                    .iter()
                    .map(|wire| {
                        let hash = crate::common::state::request_hash(wire)
                            .iter()
                            .map(|b| format!("{b:02x}"))
                            .collect::<String>();
                        json!({"wire_bytes":wire.len(),"wire_sha256":hash})
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        for target in self.pipeline_matches(spec) {
            let observed = self
                .pipeline_observations
                .entry(target.job.id)
                .or_insert_with(|| json!({"actual_stage_output_forwarded":true}));
            let (sizes_key, packets_key) = if spec.stage == Stage::Install {
                (
                    "actual_public_package_message_sizes",
                    "public_package_packets",
                )
            } else {
                ("actual_outbound_message_sizes", "sent_packets")
            };
            if !observed[sizes_key].is_array() {
                observed[sizes_key] = json!([]);
            }
            if !observed[packets_key].is_array() {
                observed[packets_key] = json!([]);
            }
            observed[sizes_key]
                .as_array_mut()
                .ok_or("packet sizes metadata")?
                .extend(packets.iter().map(|p| p["wire_bytes"].clone()));
            observed[packets_key]
                .as_array_mut()
                .ok_or("packet metadata")?
                .extend(packets.iter().cloned());
            if spec.stage == Stage::Install {
                observed["public_package_direction"] = json!("received_public_packet");
                observed["local_install_no_wire"] = json!(packets.is_empty());
            }
        }
        Ok(())
    }
    fn run<T>(
        &mut self,
        scheme: Scheme,
        phase: Phase,
        k: Option<usize>,
        action: impl FnOnce() -> Result<Output<T>>,
    ) -> Result<T> {
        let s = self.spec(scheme, &phase, k);
        let selected = self.selected(&s) && !self.decode_only();
        self.remember(s.clone(), &phase);
        let out = if selected {
            self.segments += 1;
            if self.is_pipeline() {
                let matches = self.pipeline_matches(&s);
                let first = matches.first().ok_or("pipeline stage selection")?;
                let value = self.capture(first, action)?;
                for other in matches.iter().skip(1) {
                    self.clock
                        .as_deref_mut()
                        .ok_or("pipeline clock missing")?
                        .capture_alias(&other.job.id, &first.job.id, "whole")?;
                }
                value
            } else {
                self.clock
                    .as_deref_mut()
                    .ok_or("clock absent")?
                    .measure(action)?
            }
        } else {
            action()?
        };
        if selected {
            self.observe_output(&s, &out)?;
            if let Some(m) = &out.messages {
                self.message_sizes.extend(m.iter().map(Vec::len));
            }
            self.completed_profiles.push(phase.profile.into());
        }
        self.last_messages = out.messages;
        Ok(out.value)
    }

    #[allow(clippy::too_many_arguments)]
    fn received<D, T>(
        &mut self,
        scheme: Scheme,
        phase: Phase,
        k: Option<usize>,
        bytes: &[Vec<u8>],
        fields: WireFields,
        decode: impl FnOnce() -> Result<D>,
        native: impl FnOnce(D) -> Result<Output<T>>,
    ) -> Result<T> {
        if self.is_pipeline() {
            let spec = self.spec(scheme, &phase, k);
            let matches = self.pipeline_matches(&spec);
            self.remember(spec.clone(), &phase);
            let source = matches
                .iter()
                .find(|s| s.stage == Stage::InclusiveVerification)
                .or(matches.first());
            let out = if let Some(source) = source {
                self.segments += 1;
                self.capture(source, || {
                    let _crypto = crate::darlt::instrumentation::span("verification.crypto");
                    let received = {
                        let _decode =
                            crate::darlt::instrumentation::span("receive.strict_decoding");
                        decode()?
                    };
                    native(received)
                })?
            } else {
                native(decode()?)?
            };
            if let Some(source) = source {
                self.decoded_observation(fields, bytes, phase.profile);
                self.record_pipeline_observation(&source.job.id, bytes, k.unwrap_or(1));
            }
            self.last_messages = out.messages;
            return Ok(out.value);
        }
        let spec = self.spec(scheme, &phase, k);
        let selected = self.selected(&spec);
        self.remember(spec, &phase);
        let standalone = self.decode_only();
        let out = if selected && standalone {
            let decoded = self
                .clock
                .as_deref_mut()
                .ok_or("decode clock missing")?
                .measure(decode)?;
            self.segments += 1;
            self.decoded_observation(fields, bytes, phase.profile);
            if !matches!(scheme, Scheme::Msb23 | Scheme::Slw25) {
                std::hint::black_box(decoded);
                return Err(DONE.into());
            }
            native(decoded)?
        } else if selected {
            self.segments += 1;
            let out = self
                .clock
                .as_deref_mut()
                .ok_or("native receive clock missing")?
                .measure(|| native(decode()?))?;
            self.decoded_observation(fields, bytes, phase.profile);
            if let Some(messages) = &out.messages {
                self.message_sizes.extend(messages.iter().map(Vec::len));
            }
            if phase.role == Role::Verifier
                && phase.stage == Stage::VerificationCrypto
                && !matches!(scheme, Scheme::Msb23 | Scheme::Slw25)
            {
                std::hint::black_box(out.value);
                self.last_messages = out.messages;
                return Err(DONE.into());
            }
            out
        } else {
            native(decode()?)?
        };
        self.last_messages = out.messages;
        Ok(out.value)
    }
    #[allow(clippy::too_many_arguments)]
    fn received_tokens<D: Any, T>(
        &mut self,
        scheme: Scheme,
        phase: Phase,
        k: Option<usize>,
        bytes: &[Vec<u8>],
        fields: WireFields,
        decode: impl FnOnce() -> Result<D>,
        native: impl FnOnce(&D) -> Result<Output<T>>,
    ) -> Result<T> {
        if !self.is_pipeline() {
            return self.received(scheme, phase, k, bytes, fields, decode, |received| {
                native(&received)
            });
        }
        let spec = self.spec(scheme, &phase, k);
        let matches = self.pipeline_matches(&spec);
        self.remember(spec.clone(), &phase);
        let source = matches
            .iter()
            .find(|s| s.stage == Stage::InclusiveVerification)
            .or(matches.first());
        let inclusive = source.is_some_and(|s| s.stage == Stage::InclusiveVerification);
        let action = || {
            let _crypto = crate::darlt::instrumentation::span("verification.crypto");
            let received = {
                let _decode = crate::darlt::instrumentation::span("receive.strict_decoding");
                decode()?
            };
            if inclusive {
                received_duplicate_precheck(&received)?;
            }
            let out = native(&received)?;
            Ok((received, out))
        };
        let (received, out) = if let Some(source) = source {
            self.segments += 1;
            self.capture(source, action)?
        } else {
            action()?
        };
        if phase.role == Role::Verifier && phase.stage == Stage::VerificationCrypto {
            let key = self.received_key(scheme, k, phase.profile);
            self.retained.insert(key, Rc::new(received));
        }
        if phase.role == Role::Verifier
            && phase.stage == Stage::VerificationCrypto
            && phase.profile == fixed_baseline_profile(scheme)
            && k == Some(1)
        {
            for target in self.pipeline_targets.iter().filter(|s| {
                s.stage == Stage::MetadataRead && s.scheme == scheme && s.bit == self.bit
            }) {
                let observed = self
                    .pipeline_observations
                    .entry(target.job.id.clone())
                    .or_insert_with(|| json!({}));
                observed["input_record_provenance"] =
                    json!("full_native_verification_in_same_sample");
                observed["input_record_cached_across_samples"] = json!(false);
                observed["input_record_verification_profile"] = json!(phase.profile);
            }
        }
        if let Some(source) = source {
            self.decoded_observation(fields, bytes, phase.profile);
            self.record_pipeline_observation(&source.job.id, bytes, k.unwrap_or(1));
        }
        self.last_messages = out.messages;
        Ok(out.value)
    }
    fn cached<T: Any>(
        &mut self,
        scheme: Scheme,
        phase: Phase,
        k: Option<usize>,
        action: impl FnOnce() -> Result<Output<T>>,
    ) -> Result<Rc<T>> {
        let s = self.spec(scheme, &phase, k);
        let selected = self.selected(&s);
        self.remember(s.clone(), &phase);
        if selected && !self.is_pipeline() {
            let out = self
                .clock
                .as_deref_mut()
                .ok_or("clock absent")?
                .measure(action)?;
            self.segments += 1;
            if let Some(m) = &out.messages {
                self.message_sizes.extend(m.iter().map(Vec::len));
            }
            self.completed_profiles.push(phase.profile.into());
            std::hint::black_box(out.value);
            return Err(DONE.into());
        }
        if selected && self.is_pipeline() && s.stage == Stage::Install {
            let matches = self.pipeline_matches(&s);
            let first = matches.first().ok_or("pipeline install selection")?;
            let value = self.capture(first, action)?;
            self.segments += 1;
            self.observe_output(&s, &value)?;
            let out = Rc::new(value.value);
            self.cache
                .borrow_mut()
                .insert(s.job.id.clone(), out.clone());
            return Ok(out);
        }
        let key = s.job.id.clone();
        if let Some(old) = self.cache.borrow().get(&key) {
            return old
                .clone()
                .downcast::<T>()
                .map_err(|_| "public fixture cache type mismatch".into());
        }
        let out = if selected && self.is_pipeline() {
            let matches = self.pipeline_matches(&s);
            let first = matches.first().ok_or("pipeline cached stage selection")?;
            let value = self.capture(first, action)?;
            self.segments += 1;
            value
        } else {
            action()?
        };
        if selected {
            self.observe_output(&s, &out)?;
        }
        let out = Rc::new(out.value);
        self.cache.borrow_mut().insert(key, out.clone());
        Ok(out)
    }
}
struct Native<'a, 'b> {
    recorder: &'a mut Recorder<'b>,
    scheme: Scheme,
}
impl Native<'_, '_> {
    fn take_messages(&mut self) -> Result<Vec<Vec<u8>>> {
        self.recorder
            .last_messages
            .take()
            .ok_or_else(|| "native sender message missing".into())
    }
    fn take_one(&mut self) -> Result<Vec<u8>> {
        let mut messages = self.take_messages()?;
        need(messages.len() == 1, "native single-message shape")?;
        Ok(messages.remove(0))
    }
    fn record<T>(
        &mut self,
        phase: Phase,
        k: Option<usize>,
        action: impl FnOnce() -> Result<Output<T>>,
    ) -> Result<T> {
        self.recorder.run(self.scheme, phase, k, action)
    }

    fn received<D, T>(
        &mut self,
        phase: Phase,
        k: Option<usize>,
        bytes: &[Vec<u8>],
        fields: WireFields,
        decode: impl FnOnce() -> Result<D>,
        native: impl FnOnce(D) -> Result<Output<T>>,
    ) -> Result<T> {
        self.recorder
            .received(self.scheme, phase, k, bytes, fields, decode, native)
    }
    fn note_received<'p>(
        &mut self,
        receiver: (Role, Stage),
        k: Option<usize>,
        packets: impl IntoIterator<Item = &'p [u8]>,
        sender: (Role, Stage),
    ) -> Result<()> {
        if !self.recorder.is_pipeline() {
            return Ok(());
        }
        let receiver_stage = group(receiver.0, receiver.1);
        let sender_stage = group(sender.0, sender.1);
        let sender_id = self
            .recorder
            .pipeline_targets
            .iter()
            .find(|s| {
                s.scheme == self.scheme && s.role == sender.0 && s.stage == sender_stage && s.k == k
            })
            .map(|s| s.job.id.clone());
        let received=packets.into_iter().map(|wire|{
            let hash=crate::common::state::request_hash(wire).iter().map(|b|format!("{b:02x}")).collect::<String>();
            json!({"sender_job_id":sender_id,"sender_role":name(sender.0),"sender_stage":name(sender_stage),"wire_bytes":wire.len(),"wire_sha256":hash})
        }).collect::<Vec<_>>();
        for target in self.recorder.pipeline_targets.iter().filter(|s| {
            s.scheme == self.scheme && s.role == receiver.0 && s.stage == receiver_stage && s.k == k
        }) {
            let observed = self
                .recorder
                .pipeline_observations
                .entry(target.job.id.clone())
                .or_insert_with(|| json!({}));
            if !observed["received_packets"].is_array() {
                observed["received_packets"] = json!([]);
            }
            observed["received_packets"]
                .as_array_mut()
                .ok_or("received packet metadata")?
                .extend(received.iter().cloned());
        }
        Ok(())
    }
    fn note_request<A: crate::batch_runtime::Adapter>(
        &mut self,
        adapter: &A,
        items: &[A::Item],
        k: usize,
    ) -> Result<()> {
        if !self.recorder.is_pipeline() {
            return Ok(());
        }
        let operation = self.recorder.application_operation(k);
        let complete = crate::batch_runtime::bound_request(adapter, items, &operation);
        let digest = crate::common::state::request_hash(&complete)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        let messages = items
            .iter()
            .flat_map(|item| adapter.wire_messages(item))
            .collect::<Vec<_>>();
        let summary = json!({"complete_application_request_sha256":digest,"complete_request_hash_scope":"native_adapter_bound_request",
            "complete_application_request_bytes":complete.len(),"actual_native_message_sizes":messages.iter().map(Vec::len).collect::<Vec<_>>(),
            "actual_native_wire_bytes":messages.iter().map(Vec::len).sum::<usize>(),"application_nonce":self.recorder.pipeline_trial,
            "proof_or_token_result_memoized":false});
        if let Some(previous) = self.recorder.pipeline_requests.get(&k) {
            need(
                previous == &summary,
                "same-slot request changed between native verification profiles",
            )?;
        } else {
            self.recorder.pipeline_requests.insert(k, summary.clone());
        }
        for target in self
            .recorder
            .pipeline_targets
            .iter()
            .filter(|s| s.k == Some(k))
        {
            let observed = self
                .recorder
                .pipeline_observations
                .entry(target.job.id.clone())
                .or_insert_with(|| json!({}));
            for (key, value) in summary.as_object().ok_or("request summary shape")? {
                observed[key] = value.clone();
            }
        }
        Ok(())
    }
    fn verification_order(&mut self, k: usize, names: &[&'static str]) -> Vec<&'static str> {
        let mut order = names
            .iter()
            .copied()
            .filter(|profile| {
                self.wants_profile(profile, k)
                    || (*profile == fixed_baseline_profile(self.scheme)
                        && k == 1
                        && self.wants_stage(Stage::MetadataRead))
            })
            .collect::<Vec<_>>();
        if self.recorder.is_pipeline() && !order.is_empty() {
            let offset = self.recorder.pipeline_trial.unwrap_or(0) as usize % order.len();
            order.rotate_left(offset);
        }
        if self.recorder.is_pipeline() {
            self.recorder
                .pipeline_profile_order
                .insert(k, order.iter().map(|s| (*s).to_owned()).collect());
        }
        order
    }
    fn wants_verification_profile(&self, profile: &str, k: usize) -> bool {
        self.wants_profile(profile, k)
            || (k == 1
                && self.wants_stage(Stage::MetadataRead)
                && profile == fixed_baseline_profile(self.scheme))
    }
    fn wants_stage(&self, stage: Stage) -> bool {
        !self.recorder.is_pipeline()
            || self
                .recorder
                .pipeline_targets
                .iter()
                .any(|s| s.scheme == self.scheme && s.stage == stage)
    }
    fn wants_profile(&self, profile: &str, k: usize) -> bool {
        !self.recorder.is_pipeline()
            || self.recorder.pipeline_targets.iter().any(|s| {
                s.scheme == self.scheme
                    && s.k == Some(k)
                    && s.job.boundary["decode_only"] != true
                    && ((matches!(
                        s.stage,
                        Stage::VerificationCrypto | Stage::InclusiveVerification
                    ) && (s.event_profile == profile
                        || (matches!(self.scheme, Scheme::Msb23 | Scheme::Slw25)
                            && s.job.profile == profile)))
                        || (s.stage == Stage::SharedState
                            && profile == fixed_baseline_profile(self.scheme)))
            })
    }
    fn received_tokens<D: Any, T>(
        &mut self,
        phase: Phase,
        k: Option<usize>,
        bytes: &[Vec<u8>],
        fields: WireFields,
        decode: impl FnOnce() -> Result<D>,
        native: impl FnOnce(&D) -> Result<Output<T>>,
    ) -> Result<T> {
        self.recorder
            .received_tokens(self.scheme, phase, k, bytes, fields, decode, native)
    }
    fn source_asset<T: Any>(
        &mut self,
        tag: &str,
        k: Option<usize>,
        refresh_stages: &[Stage],
        action: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Rc<T>> {
        let key = format!(
            "pipeline-source/{}/{}/{k:?}/bit{}",
            name(self.scheme),
            tag,
            self.recorder.bit
        );
        let refresh = self.recorder.pipeline_targets.iter().any(|s| {
            s.scheme == self.scheme
                && refresh_stages.contains(&s.stage)
                && (s.k == k || s.k.is_none())
        });
        if self.recorder.is_pipeline() && !refresh {
            if let Some(old) = self.recorder.cache.borrow().get(&key).cloned() {
                return old
                    .downcast::<T>()
                    .map_err(|_| "pipeline source asset type".into());
            }
        }
        let out = Rc::new(action(self)?);
        if self.recorder.is_pipeline() {
            self.recorder.cache.borrow_mut().insert(key, out.clone());
        }
        Ok(out)
    }
    fn cached<T: Any>(
        &mut self,
        phase: Phase,
        k: Option<usize>,
        action: impl FnOnce() -> Result<Output<T>>,
    ) -> Result<Rc<T>> {
        self.recorder.cached(self.scheme, phase, k, action)
    }
}
fn need(value: bool, message: &str) -> Result<()> {
    if value {
        Ok(())
    } else {
        Err(message.into())
    }
}
fn native_error(e: impl std::fmt::Display) -> String {
    e.to_string()
}
fn execute_scheme(s: Scheme, r: &mut Recorder<'_>, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    match s {
        Scheme::Sma2rt => sma_phases(r, rng, ks),
        Scheme::Niat => niat_phases(r, rng, ks),
        Scheme::Cpat => cpat_phases(r, rng, ks),
        Scheme::HinToken => hin_phases(r, rng, ks),
        Scheme::Msb23 => msb_phases(r, rng, ks),
        Scheme::Slw25 => slw_phases(r, rng, ks),
        _ => Err("not an established baseline".into()),
    }
}
pub struct Factory {
    attributes: usize,
    cache: Cache,
    specs: Vec<Spec>,
}
impl Factory {
    pub fn new() -> Result<Self> {
        Self::for_attributes(10)
    }
    pub fn for_attributes(attributes: usize) -> Result<Self> {
        need(
            [5, 10, 15, 20, 25, 30].contains(&attributes),
            "unsupported business attribute count",
        )?;
        let cache = Rc::new(RefCell::new(BTreeMap::new()));
        let mut specs = vec![];
        let schemes = if attributes == 10 {
            vec![
                Scheme::Sma2rt,
                Scheme::Niat,
                Scheme::Cpat,
                Scheme::HinToken,
                Scheme::Msb23,
                Scheme::Slw25,
            ]
        } else {
            vec![Scheme::Sma2rt, Scheme::Msb23, Scheme::Slw25]
        };
        for scheme in schemes {
            let mut recorder = Recorder {
                attributes,
                profile: "Randomized".into(),
                bit: 0,
                cache: cache.clone(),
                clock: None,
                target: None,
                pipeline_targets: vec![],
                pipeline_trial: None,
                retained: BTreeMap::new(),
                pipeline_observations: BTreeMap::new(),
                pipeline_requests: BTreeMap::new(),
                pipeline_profile_order: BTreeMap::new(),
                catalog: BTreeMap::new(),
                segments: 0,
                message_sizes: vec![],
                completed_profiles: vec![],
                last_messages: None,
                received_fields: WireFields::default(),
                received_sizes: vec![],
            };
            execute_scheme(
                scheme,
                &mut recorder,
                &mut StdRng::seed_from_u64(230_030 + attributes as u64),
                &[1],
            )?;
            for spec in recorder.catalog.into_values() {
                if attributes != 10
                    && !matches!(
                        spec.stage,
                        Stage::Preparation
                            | Stage::OnlineGeneration
                            | Stage::VerificationCrypto
                            | Stage::InclusiveVerification
                            | Stage::SharedState
                    )
                {
                    continue;
                }
                if attributes != 10
                    && spec.role != Role::Verifier
                    && !matches!(spec.stage, Stage::Preparation | Stage::OnlineGeneration)
                {
                    continue;
                }
                let points = if spec.k.is_some()
                    && !matches!(spec.stage, Stage::MetadataRead | Stage::NativeRead)
                {
                    if attributes == 10 {
                        KS.to_vec()
                    } else {
                        vec![16]
                    }
                } else {
                    vec![spec.k.unwrap_or(1)]
                };
                let profiles = if matches!(scheme, Scheme::Msb23 | Scheme::Slw25)
                    && ((spec.role == Role::Verifier
                        && matches!(
                            spec.stage,
                            Stage::VerificationCrypto | Stage::InclusiveVerification
                        ))
                        || matches!(spec.stage, Stage::IssueAccept | Stage::DelegateReceive))
                {
                    if scheme == Scheme::Msb23 && spec.stage == Stage::IssueAccept {
                        vec![
                            "Specification",
                            "RandomizedCachedGt",
                            "RandomizedPairingKey",
                        ]
                    } else {
                        vec!["Specification", "Randomized"]
                    }
                } else if scheme == Scheme::Niat
                    && matches!(spec.stage, Stage::IssueResponse | Stage::IssueAccept)
                {
                    vec!["NativeTotal", "Prepared"]
                } else if matches!(spec.stage, Stage::MetadataRead | Stage::NativeRead) {
                    vec!["bit0", "bit1"]
                } else {
                    vec![spec.job.profile.as_str()]
                };
                for k in points {
                    for profile in &profiles {
                        let mut s = spec.clone();
                        s.k = spec.k.map(|_| k);
                        s.job.profile = (*profile).into();
                        s.job.workload["k"] = json!(s.k);
                        s.job.workload["variant"] = json!(profile);
                        s.bit = u8::from(*profile == "bit1");
                        s.job.workload["metadata_bit"] =
                            if matches!(s.stage, Stage::MetadataRead | Stage::NativeRead) {
                                json!(s.bit)
                            } else {
                                Value::Null
                            };
                        s.job.id = format!(
                            "baseline/{}/a{}/{}/{}/k{}/{}",
                            name(scheme),
                            if matches!(scheme, Scheme::Sma2rt | Scheme::Msb23 | Scheme::Slw25) {
                                attributes.to_string()
                            } else {
                                "na".into()
                            },
                            name(s.role),
                            name(s.stage),
                            s.k.map_or("na".into(), |v| v.to_string()),
                            profile
                        );
                        specs.push(s);
                    }
                }
            }
        }
        if attributes == 10 {
            let mut aliases = vec![];
            for spec in &specs {
                if spec.stage != Stage::Install {
                    continue;
                }
                let actors = match spec.scheme {
                    Scheme::Sma2rt => vec![Role::Issuer, Role::Verifier],
                    Scheme::Niat => vec![Role::Issuer, Role::Verifier, Role::Reader],
                    Scheme::Cpat if spec.role == Role::User => {
                        vec![Role::Issuer, Role::Verifier, Role::Reader]
                    }
                    Scheme::Msb23 => vec![Role::Issuer, Role::Agent, Role::Verifier],
                    Scheme::Slw25 => vec![Role::Issuer, Role::User, Role::Agent],
                    Scheme::HinToken => vec![Role::Reader],
                    _ => vec![],
                };
                for actor in actors {
                    let mut alias = spec.clone();
                    alias.job.id = format!("{}/installed-for-{}", spec.job.id, name(actor));
                    alias.job.role = name(actor);
                    alias.job.workload["installed_role"] = json!(name(actor));
                    aliases.push(alias);
                }
            }
            specs.extend(aliases);
        }
        if attributes == 10 {
            for agents in [1, 2, 4, 8, 16, 32, 64] {
                for (stage, role) in [
                    (Stage::ProvisioningIssuer, Role::Issuer),
                    (Stage::ProvisioningSystem, Role::System),
                ] {
                    let id = format!("baseline/sma2rt/a10/equal-budget/A{agents}/{}", name(stage));
                    let mut job = Job::new(&id, "SMA²RT", &name(role), &name(stage));
                    job.profile = "native_equal_total_budget".into();
                    job.workload = json!({"agents":agents,"attributes":10,"n_per_agent":1024/agents,"total_quota":1024,"variant":"native_equal_total_budget","amortization_divisor":agents});
                    job.boundary = json!({"safe":true,"network_included":false,"persistence_included":false,"shared_state_included":false,"setup_keygen_and_install_included":false,"wire_encoding_included":true,"strict_decoding_included":true,"one_actual_issuance_per_agent":true});
                    specs.push(Spec {
                        job,
                        scheme: Scheme::Sma2rt,
                        role,
                        stage,
                        k: None,
                        event_profile: String::new(),
                        bit: 1,
                    });
                }
            }
        }
        if attributes == 10 {
            for agents in [1, 2, 4, 8, 16, 32, 64] {
                for role in [Role::Issuer, Role::Agent] {
                    let id = format!(
                        "baseline/sma2rt/a10/equal-budget/A{agents}/install/{}",
                        name(role)
                    );
                    let mut job = Job::new(&id, "SMA²RT", &name(role), "install");
                    job.cache = "cold".into();
                    job.profile = "native_equal_budget_public_installation".into();
                    job.workload = json!({"agents":agents,"attributes":10,"n_per_agent":1024/agents,"variant":"native_equal_budget_public_installation","actual_install_calls":if role==Role::Issuer{1}else{agents}});
                    job.boundary = json!({"safe":true,"network_included":false,"persistence_included":false,"shared_state_included":false,"wire_encoding_included":false,"strict_decoding_included":true,"setup_keygen_included":false,"key_proofs_and_cache_included":true});
                    specs.push(Spec {
                        job,
                        scheme: Scheme::Sma2rt,
                        role,
                        stage: Stage::Install,
                        k: None,
                        event_profile: String::new(),
                        bit: 1,
                    });
                }
            }
        }
        let mut input_groups: BTreeMap<(String, Option<usize>), Vec<&Spec>> = BTreeMap::new();
        for spec in specs
            .iter()
            .filter(|s| s.role == Role::Verifier && s.stage == Stage::VerificationCrypto)
        {
            input_groups
                .entry((name(spec.scheme), spec.k))
                .or_default()
                .push(spec);
        }
        let decoders = input_groups.into_values().map(|parents| {
            let spec = parents.iter().copied().find(|s| s.job.boundary["safe"] == true).expect("native wire decoder has safe parent");
            let mut decoded = spec.clone();
            decoded.job.id.push_str("/decode-only");
            decoded.job.stage = "strict_decoding".into();
            decoded.job.substage = "whole".into();
            let profiles = parents.iter().map(|s| s.job.profile.clone()).collect::<BTreeSet<_>>();
            decoded.job.boundary = json!({"subgroup_checks_per_received_element":1,"received_input_provenance":"sealed_checked_input","decode_only":true,"parent_verification_stage":"verification_crypto","applies_to_verification_stages":["verification_crypto","inclusive_verification"],"applies_to_profiles":profiles,"safe":true,"shared_state_included":false,"signature_and_sigma_algebra_included":false,"wire_encoding_included":false,"strict_decoding_included":true,"received_bytes_first":true,"subgroup_checks_included":true,"native_format_checks_included":true,"network_included":false,"persistence_included":false});
            decoded
        }).collect::<Vec<_>>();
        specs.extend(decoders);
        let unique = specs
            .iter()
            .map(|s| s.job.id.as_str())
            .collect::<BTreeSet<_>>();
        need(unique.len() == specs.len(), "duplicate native jobs")?;
        Ok(Self {
            attributes,
            cache: Rc::new(RefCell::new(BTreeMap::new())),
            specs,
        })
    }
}
pub fn new() -> Result<Factory> {
    Factory::new()
}

impl Worker for Factory {
    fn jobs(&self) -> Vec<Job> {
        self.specs.iter().map(|s| s.job.clone()).collect()
    }
    fn prepare_pipeline(&mut self, ids: &[String], trial: u64) -> Result<Action> {
        need(!ids.is_empty(), "empty established-baseline pipeline")?;
        let targets = ids
            .iter()
            .map(|id| {
                self.specs
                    .iter()
                    .find(|s| s.job.id == *id)
                    .cloned()
                    .ok_or_else(|| format!("unknown pipeline job {id}"))
            })
            .collect::<Result<Vec<_>>>()?;
        for target in targets
            .iter()
            .filter(|s| s.job.boundary["decode_only"] == true)
        {
            need(
                targets.iter().any(|s| {
                    s.k == target.k
                        && s.scheme == target.scheme
                        && s.job.boundary["decode_only"] != true
                        && matches!(
                            s.stage,
                            Stage::VerificationCrypto | Stage::InclusiveVerification
                        )
                }),
                "strict decoding is a same-call component, not an independent pipeline",
            )?;
        }
        if targets.iter().any(|s| s.job.workload["agents"].is_u64()) {
            return sma_provision_pipeline(targets, trial, self.cache.clone());
        }
        let scheme = targets[0].scheme;
        need(
            targets.iter().all(|s| s.scheme == scheme),
            "pipeline mixes native schemes",
        )?;
        need(
            targets
                .iter()
                .filter(|s| matches!(s.stage, Stage::MetadataRead | Stage::NativeRead))
                .map(|s| s.bit)
                .collect::<BTreeSet<_>>()
                .len()
                <= 1,
            "pipeline mixes read-bit source worlds",
        )?;
        for stage in [
            Stage::IssueAccept,
            Stage::DelegateReceive,
            Stage::IssueResponse,
        ] {
            let profiles = targets
                .iter()
                .filter(|s| s.stage == stage)
                .map(|s| s.job.profile.as_str())
                .collect::<BTreeSet<_>>();
            need(
                profiles.len() <= 1,
                "optional upstream receive variants require separate native pipelines",
            )?;
        }
        let attributes = self.attributes;
        let cache = self.cache.clone();
        Ok(Box::new(move |clock| {
            let mut ks = targets
                .iter()
                .filter_map(|s| s.k)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            if ks.is_empty() {
                ks.push(1);
            }
            let bit = targets
                .iter()
                .find(|s| matches!(s.stage, Stage::MetadataRead | Stage::NativeRead))
                .map_or(0, |s| s.bit);
            let upstream_profile = targets
                .iter()
                .find(|s| s.stage == Stage::IssueAccept)
                .or_else(|| targets.iter().find(|s| s.stage == Stage::DelegateReceive))
                .or_else(|| targets.iter().find(|s| s.stage == Stage::IssueResponse))
                .map_or("Randomized", |s| s.job.profile.as_str())
                .to_owned();
            let mut recorder = Recorder {
                attributes,
                profile: upstream_profile,
                bit,
                cache,
                clock: Some(clock),
                target: None,
                pipeline_targets: targets.clone(),
                pipeline_trial: Some(trial),
                retained: BTreeMap::new(),
                pipeline_observations: BTreeMap::new(),
                pipeline_requests: BTreeMap::new(),
                pipeline_profile_order: BTreeMap::new(),
                catalog: BTreeMap::new(),
                segments: 0,
                message_sizes: vec![],
                completed_profiles: vec![],
                last_messages: None,
                received_fields: WireFields::default(),
                received_sizes: vec![],
            };
            let mut rng = recorder.pipeline_rng(scheme, 0, "native-generation");
            execute_scheme(scheme, &mut recorder, &mut rng, &ks)?;
            // Aliases observe components from this exact execution; they never run a decoder or native verification again.
            for target in &targets {
                if target.job.boundary["decode_only"] == true {
                    if let Some(source) = targets
                        .iter()
                        .find(|s| {
                            s.scheme == target.scheme
                                && s.k == target.k
                                && s.stage == Stage::InclusiveVerification
                        })
                        .or_else(|| {
                            targets.iter().find(|s| {
                                s.scheme == target.scheme
                                    && s.k == target.k
                                    && s.stage == Stage::VerificationCrypto
                                    && s.job.boundary["safe"] == true
                            })
                        })
                    {
                        recorder
                            .clock
                            .as_deref_mut()
                            .ok_or("pipeline clock missing")?
                            .capture_alias(
                                &target.job.id,
                                &source.job.id,
                                "receive.strict_decoding",
                            )?;
                    }
                } else if target.stage == Stage::VerificationCrypto {
                    if let Some(source) = targets.iter().find(|s| {
                        s.scheme == target.scheme
                            && s.k == target.k
                            && s.stage == Stage::InclusiveVerification
                            && s.job.profile == target.job.profile
                    }) {
                        recorder
                            .clock
                            .as_deref_mut()
                            .ok_or("pipeline clock missing")?
                            .capture_alias(&target.job.id, &source.job.id, "verification.crypto")?;
                    }
                }
            }
            Ok(
                json!({"correctness":"PASS","pipeline":true,"sample_slot":trial,"inputpool_alive_slots":1,
                "actual_stage_outputs_forwarded":true,"same_slot_wire_shared_across_verification_profiles":true,
                "cross_sample_request_nonce":trial,"oneuse_preparation_fresh_each_slot":true,
                "verification_profile_order":recorder.pipeline_profile_order,"actual_received_fields":recorder.received_fields.json(),"complete_requests":recorder.pipeline_requests,"observations":recorder.pipeline_observations}),
            )
        }))
    }
    fn prepare(&mut self, id: &str, trial: u64) -> Result<Action> {
        let target = self
            .specs
            .iter()
            .find(|s| s.job.id == id)
            .cloned()
            .ok_or_else(|| format!("unknown established-baseline job {id}"))?;
        let attributes = self.attributes;
        let cache = self.cache.clone();
        if target.stage == Stage::Install && target.job.workload["agents"].is_u64() {
            return Ok(sma_provision_install_action(
                target.job.workload["agents"].as_u64().unwrap() as usize,
                target.role == Role::Issuer,
                cache,
            ));
        }
        if matches!(
            target.stage,
            Stage::ProvisioningIssuer | Stage::ProvisioningSystem
        ) {
            return Ok(sma_provision_action(
                target.job.workload["agents"]
                    .as_u64()
                    .ok_or("agent count")? as usize,
                target.stage == Stage::ProvisioningIssuer,
                trial,
                cache,
            ));
        }
        Ok(Box::new(move |clock| {
            let shared = target.job.boundary["decode_only"] != true
                && matches!(
                    target.stage,
                    Stage::InclusiveVerification | Stage::SharedState
                );
            let scheme = target.scheme;
            let ks = [target.k.unwrap_or(1)];
            let seed = 230_214_000u64
                .wrapping_add(trial.wrapping_mul(1_000_003))
                .wrapping_add(attributes as u64 * 10_000)
                .wrapping_add(ks[0] as u64 * 4)
                .wrapping_add(target.bit as u64);
            let profile = if target.job.profile == "native" {
                "Randomized".into()
            } else {
                target.job.profile.clone()
            };
            let mut recorder = Recorder {
                attributes,
                profile,
                bit: target.bit,
                cache,
                clock: Some(clock),
                target: Some(target),
                pipeline_targets: vec![],
                pipeline_trial: None,
                retained: BTreeMap::new(),
                pipeline_observations: BTreeMap::new(),
                pipeline_requests: BTreeMap::new(),
                pipeline_profile_order: BTreeMap::new(),
                catalog: BTreeMap::new(),
                segments: 0,
                message_sizes: vec![],
                completed_profiles: vec![],
                last_messages: None,
                received_fields: WireFields::default(),
                received_sizes: vec![],
            };
            if let Err(e) =
                execute_scheme(scheme, &mut recorder, &mut StdRng::seed_from_u64(seed), &ks)
            {
                if e != DONE {
                    return Err(e);
                }
            }
            need(recorder.segments > 0, "selected native role did not run")?;
            Ok(
                json!({"correctness":"PASS","measured_native_segments":recorder.segments,"native_segment_names":recorder.completed_profiles,
                "actual_outbound_message_sizes":if recorder.message_sizes.is_empty(){Value::Null}else{json!(recorder.message_sizes)},
                "actual_outbound_wire_bytes":if recorder.message_sizes.is_empty(){Value::Null}else{json!(recorder.message_sizes.iter().sum::<usize>())},
                "unmeasured_fixture_and_counterpart_progression":true,"shared_state_included":shared,
                "decode_only":recorder.decode_only(),"actual_received_message_sizes":recorder.received_sizes,"actual_received_fields":recorder.received_fields.json()}),
            )
        }))
    }
}

fn weight_rng_for_mode(mode: crate::experiment::RunMode, fallback: StdRng) -> Result<StdRng> {
    if mode == crate::experiment::RunMode::Formal {
        // Seed before capture. Native SET calls draw/reject 16 bytes inside capture.
        let mut seed = [0u8; 32];
        rand::rngs::OsRng
            .try_fill_bytes(&mut seed)
            .map_err(native_error)?;
        Ok(StdRng::from_seed(seed))
    } else {
        Ok(fallback)
    }
}
fn fixed_baseline_profile(scheme: Scheme) -> &'static str {
    match scheme {
        Scheme::Sma2rt => "safe_random_complete_batch",
        Scheme::Niat => "native_C3_random_second_equation",
        Scheme::Cpat => "safe_random_FHS_same_metadata_cached",
        Scheme::HinToken => "safe_random_batch_by_same_issuer_cached_anchor",
        Scheme::Msb23 | Scheme::Slw25 => "Randomized",
        _ => "",
    }
}
fn sma_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let attributes = recorder.attributes;
    let mut f = Native {
        recorder,
        scheme: Scheme::Sma2rt,
    };
    let pp = f.cached(
        Phase::new(Role::System, Stage::Setup, "native_parameters").encoded(),
        None,
        || {
            let p = sma::setup(attributes, 1024);
            let b = p.bytes();
            Ok(Output::with_messages(p, vec![b]))
        },
    )?;
    let issuer = f.cached(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "issuer_keygen"),
        None,
        || Ok(Output::value(sma::ikeygen(&pp, rng))),
    )?;
    let reader = f.cached(
        Phase::new(Role::Reader, Stage::KeyGeneration, "metadata_keygen"),
        None,
        || Ok(Output::value(sma::vkeygen(&pp, rng))),
    )?;
    let user = f.cached(
        Phase::new(Role::User, Stage::KeyGeneration, "holder_keygen"),
        None,
        || Ok(Output::value(sma::ukeygen(rng))),
    )?;
    let public_wire = sma_public_bytes(&pp, &issuer, &reader);
    let installed = f.cached(
        Phase::new(
            Role::User,
            Stage::Install,
            "parameters_issuer_metadata_key_proofs_and_cache",
        )
        .decoded(),
        None,
        || {
            let (pp, issuer, reader) = sma_public(&public_wire)?;
            Ok(Output::with_messages(
                sma::install_instance(&pp, &issuer, &reader).map_err(native_error)?,
                vec![public_wire.clone()],
            ))
        },
    )?;
    let attrs = (0..attributes)
        .map(|i| {
            if i == 0 {
                S::ONE
            } else {
                S::from(20 + i as u64)
            }
        })
        .collect::<Vec<_>>();
    let policy = sma::Policy {
        atoms: (0..3).map(|i| sma::Atom::Reveal(i, attrs[i])).collect(),
    };
    let wallet = f.source_asset(
        "issued-wallet",
        None,
        &[
            Stage::IssueRequest,
            Stage::IssueResponse,
            Stage::IssueAccept,
        ],
        |f| {
            let (pending, request) = f.record(
                Phase::new(Role::User, Stage::IssueRequest, "native_issue_request").encoded(),
                None,
                || {
                    let (p, q) = sma::request_installed(&installed, &user, &attrs, &policy, rng)
                        .map_err(native_error)?;
                    let b = q.bytes();
                    Ok(Output::with_messages((p, q), vec![b]))
                },
            )?;
            let request_wire = request.bytes();
            let bit = f.recorder.bit;
            f.note_received(
                (Role::Issuer, Stage::IssueResponse),
                None,
                std::iter::once(request_wire.as_slice()),
                (Role::User, Stage::IssueRequest),
            )?;
            let response = f.record(
                Phase::new(Role::Issuer, Stage::IssueResponse, "native_issuer_response")
                    .encoded()
                    .decoded(),
                None,
                || {
                    let request =
                        sma::ReceivedRequest::decode(&request_wire).map_err(native_error)?;
                    let c = sma::respond_received_installed(
                        &installed,
                        &issuer,
                        &reader,
                        request,
                        &policy,
                        bit as usize,
                        rng,
                    )
                    .map_err(native_error)?;
                    let b = c.bytes();
                    Ok(Output::with_messages(c, vec![b]))
                },
            )?;
            let response_wire = response.bytes();
            f.note_received(
                (Role::User, Stage::IssueAccept),
                None,
                std::iter::once(response_wire.as_slice()),
                (Role::Issuer, Stage::IssueResponse),
            )?;
            let mut receive_weights =
                f.recorder
                    .verification_rng(Scheme::Sma2rt, 1, "issue-receive-weights")?;
            let wallet = f.record(
                Phase::new(
                    Role::User,
                    Stage::IssueAccept,
                    "native_receive_signature_and_proof_checks",
                )
                .decoded(),
                None,
                || {
                    Ok(Output::value(
                        sma::receive_received_set(
                            &installed,
                            pending,
                            sma::ReceivedCredential::decode(&response_wire)
                                .map_err(native_error)?,
                            &mut receive_weights,
                        )
                        .map_err(native_error)?,
                    ))
                },
            )?;
            Ok(wallet)
        },
    )?;
    let bit = f.recorder.bit;
    for &k in ks {
        if f.recorder.is_pipeline() {
            f.recorder.retained.clear();
            *rng = f
                .recorder
                .pipeline_rng(Scheme::Sma2rt, k, "slot-generation");
        }

        let prepared = f.record(
            Phase::new(
                Role::User,
                Stage::Preparation,
                "installed_known_policy_native_token_precomputation",
            ),
            Some(k),
            || {
                let p = (0..k)
                    .map(|i| {
                        sma::precompute_policy_installed(
                            &installed, &wallet, i as u64, &policy, rng,
                        )
                        .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Output::value(p))
            },
        )?;
        let mut context = [0u8; 32];
        rng.fill_bytes(&mut context);
        let tokens = f.record(
            Phase::new(
                Role::User,
                Stage::OnlineGeneration,
                "native_context_and_policy_binding",
            )
            .encoded(),
            Some(k),
            || {
                let t = prepared
                    .into_iter()
                    .map(|p| {
                        sma::show_online_installed(&installed, p, &context, &policy)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = t.iter().map(sma::Token::bytes).collect();
                Ok(Output::with_messages(t, b))
            },
        )?;
        let token_wires = f.take_messages()?;
        f.note_request(
            &crate::adapters::Sma::new(&installed, &policy, &context),
            &tokens,
            k,
        )?;
        let token_fields = tokens.iter().fold(WireFields::default(), |mut fields, t| {
            fields.add(WireFields {
                g1: 10 + t.bits.len(),
                g2: 1,
                gt: 0,
                fr: 1 + t.proof.z.len() + 3 * t.proof.orz.len(),
            });
            fields
        });
        for selected_profile in f.verification_order(
            k,
            &[
                "native_sequential_specification",
                "safe_random_complete_batch",
            ],
        ) {
            if selected_profile == "native_sequential_specification"
                && f.wants_profile("native_sequential_specification", k)
            {
                f.received_tokens(
                    Phase::new(
                        Role::Verifier,
                        Stage::VerificationCrypto,
                        "native_sequential_specification",
                    ),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_sma(&installed, &policy, &token_wires),
                    |tokens| {
                        need(
                            tokens
                                .iter()
                                .all(|t| sma::verify_checked(&installed, t, &context, &policy)),
                            "SMA native verification",
                        )?;
                        Ok(Output::value(()))
                    },
                )?;
                f.accept_received(
                    checked_sma(&installed, &policy, &context, &tokens)?,
                    "native_sequential_specification",
                    crate::batch_runtime::Mode::Specification,
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || {
                        decode_sma(&installed, &policy, &token_wires)
                    }),
                )?;
            }
            if selected_profile == "safe_random_complete_batch"
                && f.wants_verification_profile("safe_random_complete_batch", k)
            {
                if f.recorder.is_pipeline() {
                    *rng = f.recorder.verification_rng(
                        Scheme::Sma2rt,
                        k,
                        "weights/safe_random_complete_batch",
                    )?;
                }
                f.received_tokens(
                    Phase::new(
                        Role::Verifier,
                        Stage::VerificationCrypto,
                        "safe_random_complete_batch",
                    ),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_sma(&installed, &policy, &token_wires),
                    |tokens| {
                        need(
                            sma::verify_random_batch_checked(
                                &installed, tokens, &context, &policy, rng,
                            ),
                            "SMA random verification",
                        )?;
                        Ok(Output::value(()))
                    },
                )?;
                f.accept_received(
                    checked_sma(&installed, &policy, &context, &tokens)?,
                    "safe_random_complete_batch",
                    crate::batch_runtime::Mode::Randomized,
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || {
                        decode_sma(&installed, &policy, &token_wires)
                    }),
                )?;
            }
        }
        if (!f.recorder.is_pipeline() || k == 1) && f.wants_stage(Stage::MetadataRead) {
            f.record(
                Phase::new(
                    Role::Reader,
                    Stage::MetadataRead,
                    "one_previously_verified_record_bit0",
                ),
                Some(1),
                || {
                    need(
                        sma::recover_metadata(&reader, &tokens[0]) == Some(bit as usize),
                        "SMA read",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
    }
    Ok(())
}

fn niat_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let native_total = recorder.profile == "NativeTotal";
    let mut f = Native {
        recorder,
        scheme: Scheme::Niat,
    };
    let keys = f.cached(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "native_issuer_keygen").encoded(),
        None,
        || {
            let keys = niat::IssuerKeys::generate(rng);
            let b = keys.public.encode();
            Ok(Output::with_messages(keys, vec![b]))
        },
    )?;
    let public_wire = keys.public.encode();
    let installed = f.cached(
        Phase::new(
            Role::User,
            Stage::Install,
            "native_issuer_validation_and_pairing_anchor_cache",
        )
        .decoded(),
        None,
        || {
            Ok(Output::with_messages(
                niat::install_wire(&public_wire).map_err(native_error)?,
                vec![public_wire.clone()],
            ))
        },
    )?;
    let client = f.cached(
        Phase::new(Role::User, Stage::KeyGeneration, "native_client_keygen"),
        None,
        || Ok(Output::value(niat::ClientKeys::generate(rng))),
    )?;
    let bit = f.recorder.bit;
    for &k in ks {
        if f.recorder.is_pipeline() {
            f.recorder.retained.clear();
            *rng = f.recorder.pipeline_rng(Scheme::Niat, k, "slot-generation");
        }

        let tokens = f.source_asset(
            "issued-native-token-wallet",
            Some(k),
            &[
                Stage::IssueRequest,
                Stage::IssueResponse,
                Stage::IssueAccept,
                Stage::Preparation,
            ],
            |f| {
                f.record(
                    Phase::new(
                        Role::User,
                        Stage::IssueRequest,
                        "one_client_request_per_independent_issuance",
                    )
                    .encoded(),
                    Some(k),
                    || {
                        let b = (0..k)
                            .map(|_| niat::encode_client_request(client.public_key()))
                            .collect();
                        Ok(Output::with_messages((), b))
                    },
                )?;
                let issuer_prepared = f.record(
                    Phase::new(
                        Role::Issuer,
                        Stage::Preparation,
                        "native_issuer_independent_signing_randomness",
                    ),
                    Some(k),
                    || {
                        Ok(Output::value(
                            (0..k)
                                .map(|_| niat::prepare_issue(&installed, rng))
                                .collect::<Vec<_>>(),
                        ))
                    },
                )?;
                let request_wire = niat::encode_client_request(client.public_key());
                f.note_received(
                    (Role::Issuer, Stage::IssueResponse),
                    Some(k),
                    std::iter::repeat_n(request_wire.as_slice(), k),
                    (Role::User, Stage::IssueRequest),
                )?;
                let responses = f.record(
                    Phase::new(
                        Role::Issuer,
                        Stage::IssueResponse,
                        "native_k_independent_issuances",
                    )
                    .encoded()
                    .decoded(),
                    Some(k),
                    || {
                        let v = issuer_prepared
                            .into_iter()
                            .enumerate()
                            .map(|(i, prepared)| {
                                let bit = ((i + bit as usize) % 2) as u8;
                                if native_total {
                                    // The total reference still receives the complete request.
                                    niat::prepare_issue(&installed, rng).issue_wire(
                                        &installed,
                                        &keys.secret,
                                        &request_wire,
                                        bit,
                                        rng,
                                    )
                                } else {
                                    prepared.issue_wire(
                                        &installed,
                                        &keys.secret,
                                        &request_wire,
                                        bit,
                                        rng,
                                    )
                                }
                                .map_err(native_error)
                            })
                            .collect::<Result<Vec<_>>>()?;
                        let b = v.iter().map(niat::IssueMessage::encode).collect();
                        Ok(Output::with_messages(v, b))
                    },
                )?;
                let obtain_prepared = f.record(
                    Phase::new(
                        Role::User,
                        Stage::Preparation,
                        "native_client_inverse_and_representation_randomness",
                    ),
                    Some(k),
                    || {
                        Ok(Output::value(
                            (0..k)
                                .map(|_| client.prepare_obtain(rng))
                                .collect::<Vec<_>>(),
                        ))
                    },
                )?;
                let response_wires = responses
                    .iter()
                    .map(niat::IssueMessage::encode)
                    .collect::<Vec<_>>();
                f.note_received(
                    (Role::User, Stage::IssueAccept),
                    Some(k),
                    response_wires.iter().map(Vec::as_slice),
                    (Role::Issuer, Stage::IssueResponse),
                )?;
                let mut receive_weights =
                    f.recorder
                        .verification_rng(Scheme::Niat, k, "issue-receive-weights")?;
                let tokens = f.record(
                    Phase::new(
                        Role::User,
                        Stage::IssueAccept,
                        "native_obtain_and_signature_checks",
                    )
                    .decoded(),
                    Some(k),
                    || {
                        let t = obtain_prepared
                            .into_iter()
                            .zip(&response_wires)
                            .map(|(prepared, bytes)| {
                                if native_total {
                                    client.prepare_obtain(rng).obtain_wire_set(
                                        &installed,
                                        bytes,
                                        &mut receive_weights,
                                    )
                                } else {
                                    prepared.obtain_wire_set(
                                        &installed,
                                        bytes,
                                        &mut receive_weights,
                                    )
                                }
                                .map_err(native_error)
                            })
                            .collect::<Result<Vec<_>>>()?;
                        Ok(Output::value(t))
                    },
                )?;
                Ok(tokens)
            },
        )?;
        f.record(
            Phase::new(
                Role::User,
                Stage::OnlineGeneration,
                "send_already_issued_native_tokens_no_new_show",
            )
            .encoded(),
            Some(k),
            || {
                Ok(Output::with_messages(
                    (),
                    tokens.iter().map(niat::Token::encode).collect(),
                ))
            },
        )?;
        let token_wires = f.take_messages()?;
        f.note_request(
            &crate::adapters::Niat::new(&installed, niat::RedemptionBatch::RandomSecondEquation)?,
            &tokens,
            k,
        )?;
        let token_fields = WireFields {
            g1: 4 * tokens.len(),
            g2: tokens.len(),
            gt: 0,
            fr: 0,
        };
        let mut verified = vec![];
        for selected_profile in f.verification_order(
            k,
            &[
                "native_sequential_specification",
                "native_C3_original_all_ones_reference",
                "native_C3_random_second_equation",
                "safe_random_FHS",
                "safe_random_FHS_cached_anchor",
            ],
        ) {
            if selected_profile == "native_sequential_specification"
                && f.wants_profile("native_sequential_specification", k)
            {
                verified = f.received_tokens(
                    Phase::new(
                        Role::Verifier,
                        Stage::VerificationCrypto,
                        "native_sequential_specification",
                    ),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_niat(&token_wires),
                    |tokens| {
                        let v = tokens
                            .iter()
                            .map(|t| {
                                niat::verify_token_checked(&installed, t).map_err(native_error)
                            })
                            .collect::<Result<Vec<_>>>()?;
                        Ok(Output::value(v))
                    },
                )?;
            }
            if selected_profile == "native_sequential_specification"
                && f.wants_profile("native_sequential_specification", k)
            {
                f.accept_received(
                    checked_niat(
                        &installed,
                        niat::RedemptionBatch::RandomSecondEquation,
                        &tokens,
                    )?,
                    "native_sequential_specification",
                    crate::batch_runtime::Mode::Specification,
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || decode_niat(&token_wires)),
                )?;
            }
            for (mode, name) in [
                (
                    niat::RedemptionBatch::OriginalAllOnes,
                    "native_C3_original_all_ones_reference",
                ),
                (
                    niat::RedemptionBatch::RandomSecondEquation,
                    "native_C3_random_second_equation",
                ),
                (niat::RedemptionBatch::RandomFhs, "safe_random_FHS"),
                (
                    niat::RedemptionBatch::RandomFhsCachedAnchor,
                    "safe_random_FHS_cached_anchor",
                ),
            ] {
                if name != selected_profile {
                    continue;
                }
                if !f.wants_verification_profile(name, k) {
                    continue;
                }
                if f.recorder.is_pipeline() {
                    *rng =
                        f.recorder
                            .verification_rng(Scheme::Niat, k, &format!("weights/{name}"))?;
                }

                let accepted = f.received_tokens(
                    Phase::new(Role::Verifier, Stage::VerificationCrypto, name),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_niat(&token_wires),
                    |tokens| {
                        Ok(Output::value(
                            niat::verify_batch_redemption_checked(&installed, tokens, mode, rng)
                                .map_err(native_error)?,
                        ))
                    },
                )?;
                if name == fixed_baseline_profile(Scheme::Niat) {
                    verified = accepted;
                }
                if mode == niat::RedemptionBatch::OriginalAllOnes {
                    continue;
                }
                f.accept_received(
                    checked_niat(&installed, mode, &tokens)?,
                    name,
                    crate::batch_runtime::Mode::Randomized,
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || decode_niat(&token_wires)),
                )?;
            }
        }
        if (!f.recorder.is_pipeline() || k == 1) && f.wants_stage(Stage::MetadataRead) {
            f.record(
                Phase::new(
                    Role::Reader,
                    Stage::MetadataRead,
                    "one_previously_verified_record_bit0",
                ),
                Some(1),
                || {
                    need(
                        niat::read_bit_extract(&keys.secret, &verified[0]).map_err(native_error)?
                            == bit,
                        "NIAT read",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
        if (!f.recorder.is_pipeline() || k == 1) && f.wants_stage(Stage::NativeRead) {
            let mut read_weights =
                f.recorder
                    .verification_rng(Scheme::Niat, 1, "native-full-read-weights")?;
            f.received_tokens(
                Phase::new(
                    Role::Reader,
                    Stage::NativeRead,
                    "native_Read_includes_Verify_one_record",
                )
                .decoded(),
                Some(1),
                std::slice::from_ref(&token_wires[0]),
                token_fields,
                || decode_niat(std::slice::from_ref(&token_wires[0])),
                |received| {
                    need(
                        niat::read_bit_total_set_checked(
                            &installed,
                            &keys.secret,
                            &received[0],
                            &mut read_weights,
                        )
                        .map_err(native_error)?
                            == bit,
                        "NIAT total read",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
    }
    Ok(())
}

fn cpat_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::Cpat,
    };
    let issuer = f.cached(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "native_issuer_keygen"),
        None,
        || Ok(Output::value(cpat::keygen(rng))),
    )?;
    let public_wire = cpat_public_bytes(&issuer.pk);
    let key = f.cached(
        Phase::new(Role::User, Stage::Install, "issuer_key_proof_installation").decoded(),
        None,
        || {
            Ok(Output::with_messages(
                cpat::validate_key(&cpat_public(&public_wire)?).map_err(native_error)?,
                vec![public_wire.clone()],
            ))
        },
    )?;
    let metadata = [0x66; 32];
    let tag = vec![0x55; 32];
    let policy = cpat::Policy {
        allowed: BTreeSet::from([tag.clone()]),
    };
    let cached_metadata = f.cached(
        Phase::new(
            Role::Verifier,
            Stage::Install,
            "same_metadata_key_combination_installation",
        ),
        None,
        || Ok(Output::value(cpat::install_metadata(&key, &metadata))),
    )?;
    let bit = f.recorder.bit;
    for &k in ks {
        if f.recorder.is_pipeline() {
            f.recorder.retained.clear();
            *rng = f.recorder.pipeline_rng(Scheme::Cpat, k, "slot-generation");
        }

        let wallets = f.source_asset(
            "issued-wallets",
            Some(k),
            &[
                Stage::IssueRequest,
                Stage::IssueResponse,
                Stage::IssueAccept,
            ],
            |f| {
                let requests = f.record(
                    Phase::new(
                        Role::User,
                        Stage::IssueRequest,
                        "native_k_independent_pretoken_requests",
                    )
                    .encoded(),
                    Some(k),
                    || {
                        let v = (0..k)
                            .map(|_| cpat::request(&key, &metadata, rng))
                            .collect::<Vec<_>>();
                        let b = v.iter().map(|(q, _)| cpat_request_bytes(q)).collect();
                        Ok(Output::with_messages(v, b))
                    },
                )?;
                let request_wires = requests
                    .iter()
                    .map(|(q, _)| cpat_request_bytes(q))
                    .collect::<Vec<_>>();
                f.note_received(
                    (Role::Issuer, Stage::IssueResponse),
                    Some(k),
                    request_wires.iter().map(Vec::as_slice),
                    (Role::User, Stage::IssueRequest),
                )?;
                let responses = f.record(
                    Phase::new(
                        Role::Issuer,
                        Stage::IssueResponse,
                        "native_k_pretoken_responses",
                    )
                    .encoded()
                    .decoded(),
                    Some(k),
                    || {
                        let v = requests
                            .iter()
                            .enumerate()
                            .map(|(i, (_q, _))| {
                                let q = cpat::ReceivedRequest::decode(&request_wires[i])
                                    .map_err(native_error)?;
                                cpat::issue_received_installed(
                                    &key,
                                    &issuer,
                                    q,
                                    &metadata,
                                    (i + bit as usize) % 2,
                                    rng,
                                )
                                .map_err(native_error)
                            })
                            .collect::<Result<Vec<_>>>()?;
                        let b = v.iter().map(cpat_response_bytes).collect();
                        Ok(Output::with_messages(v, b))
                    },
                )?;
                let response_wires = responses
                    .iter()
                    .map(cpat_response_bytes)
                    .collect::<Vec<_>>();
                f.note_received(
                    (Role::User, Stage::IssueAccept),
                    Some(k),
                    response_wires.iter().map(Vec::as_slice),
                    (Role::Issuer, Stage::IssueResponse),
                )?;
                let mut receive_weights =
                    f.recorder
                        .verification_rng(Scheme::Cpat, k, "issue-receive-weights")?;
                let wallets = f.record(
                    Phase::new(
                        Role::User,
                        Stage::IssueAccept,
                        "receive_signature_verified_once_cached_immutable_wallet",
                    )
                    .decoded(),
                    Some(k),
                    || {
                        Ok(Output::value(
                            requests
                                .into_iter()
                                .zip(&response_wires)
                                .map(|((_, p), d)| {
                                    cpat::receive_received_set(
                                        p,
                                        cpat::ReceivedResponse::decode(d).map_err(native_error)?,
                                        &mut receive_weights,
                                    )
                                    .map_err(native_error)
                                })
                                .collect::<Result<Vec<_>>>()?,
                        ))
                    },
                )?;
                Ok(wallets)
            },
        )?;
        let prepared = f.record(
            Phase::new(
                Role::User,
                Stage::Preparation,
                "known_tag_complete_native_Redeem",
            ),
            Some(k),
            || {
                Ok(Output::value(
                    wallets
                        .iter()
                        .map(|w| cpat::prepare_redemption(&key, w, &tag, rng).map_err(native_error))
                        .collect::<Result<Vec<_>>>()?,
                ))
            },
        )?;
        let tokens = f.record(
            Phase::new(
                Role::User,
                Stage::OnlineGeneration,
                "present_already_prepared_tokens",
            )
            .encoded(),
            Some(k),
            || {
                let t = prepared.into_iter().map(cpat::present).collect::<Vec<_>>();
                let b = t.iter().map(cpat::Token::encode).collect();
                Ok(Output::with_messages(t, b))
            },
        )?;
        let token_wires = f.take_messages()?;
        f.note_request(
            &crate::adapters::Cpat::four_coordinate(&key, &policy, &metadata),
            &tokens,
            k,
        )?;
        let token_fields = WireFields {
            g1: 6 * tokens.len(),
            g2: tokens.len(),
            gt: 0,
            fr: 2 * tokens.len(),
        };
        let mut verified = vec![];
        for selected_profile in f.verification_order(
            k,
            &[
                "native_sequential_specification",
                "safe_random_FHS_four_coordinate",
                "safe_random_FHS_same_metadata_cached",
            ],
        ) {
            if selected_profile == "native_sequential_specification"
                && f.wants_profile("native_sequential_specification", k)
            {
                verified = f.received_tokens(
                    Phase::new(
                        Role::Verifier,
                        Stage::VerificationCrypto,
                        "native_sequential_specification",
                    ),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_cpat(&policy, &token_wires),
                    |tokens| {
                        Ok(Output::value(
                            tokens
                                .iter()
                                .map(|t| {
                                    cpat::verify_record_checked(&key, &policy, &metadata, t)
                                        .map_err(native_error)
                                })
                                .collect::<Result<Vec<_>>>()?,
                        ))
                    },
                )?;
            }
            if selected_profile == "native_sequential_specification"
                && f.wants_profile("native_sequential_specification", k)
            {
                f.accept_received(
                    checked_cpat(&key, &policy, &metadata, None, &tokens)?,
                    "native_sequential_specification",
                    crate::batch_runtime::Mode::Specification,
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || {
                        decode_cpat(&policy, &token_wires)
                    }),
                )?;
            }
            if selected_profile == "safe_random_FHS_four_coordinate"
                && f.wants_profile("safe_random_FHS_four_coordinate", k)
            {
                if f.recorder.is_pipeline() {
                    *rng = f.recorder.verification_rng(
                        Scheme::Cpat,
                        k,
                        "weights/safe_random_FHS_four_coordinate",
                    )?;
                }
                f.received_tokens(
                    Phase::new(
                        Role::Verifier,
                        Stage::VerificationCrypto,
                        "safe_random_FHS_four_coordinate",
                    ),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_cpat(&policy, &token_wires),
                    |tokens| {
                        need(
                            cpat::verify_random_batch_checked(
                                &key, &policy, &metadata, tokens, rng,
                            ),
                            "CPAT full random",
                        )?;
                        Ok(Output::value(()))
                    },
                )?;
                f.accept_received(
                    checked_cpat(&key, &policy, &metadata, None, &tokens)?,
                    "safe_random_FHS_four_coordinate",
                    crate::batch_runtime::Mode::Randomized,
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || {
                        decode_cpat(&policy, &token_wires)
                    }),
                )?;
            }
            if selected_profile == "safe_random_FHS_same_metadata_cached"
                && f.wants_verification_profile("safe_random_FHS_same_metadata_cached", k)
            {
                if f.recorder.is_pipeline() {
                    *rng = f.recorder.verification_rng(
                        Scheme::Cpat,
                        k,
                        "weights/safe_random_FHS_same_metadata_cached",
                    )?;
                }
                let needs_record = k == 1 && f.wants_stage(Stage::MetadataRead);
                let accepted = f.received_tokens(
                    Phase::new(
                        Role::Verifier,
                        Stage::VerificationCrypto,
                        "safe_random_FHS_same_metadata_cached",
                    ),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_cpat(&policy, &token_wires),
                    |tokens| {
                        if needs_record {
                            Ok(Output::value(
                                cpat::verify_random_batch_metadata_records_checked(
                                    &cached_metadata,
                                    &policy,
                                    tokens,
                                    rng,
                                )
                                .map_err(native_error)?,
                            ))
                        } else {
                            need(
                                cpat::verify_random_batch_metadata_checked(
                                    &cached_metadata,
                                    &policy,
                                    tokens,
                                    rng,
                                ),
                                "CPAT same metadata random",
                            )?;
                            Ok(Output::value(vec![]))
                        }
                    },
                )?;
                if needs_record {
                    verified = accepted;
                }
                f.accept_received(
                    checked_cpat(&key, &policy, &metadata, Some(&cached_metadata), &tokens)?,
                    "safe_random_FHS_same_metadata_cached",
                    crate::batch_runtime::Mode::Randomized,
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || {
                        decode_cpat(&policy, &token_wires)
                    }),
                )?;
            }
        }
        if (!f.recorder.is_pipeline() || k == 1) && f.wants_stage(Stage::MetadataRead) {
            f.record(
                Phase::new(
                    Role::Reader,
                    Stage::MetadataRead,
                    "one_previously_verified_record_bit0",
                ),
                Some(1),
                || {
                    need(
                        cpat::read_bit_validated(&issuer, &verified[0]).map_err(native_error)?
                            == bit as usize,
                        "CPAT read",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
        if (!f.recorder.is_pipeline() || k == 1) && f.wants_stage(Stage::NativeRead) {
            let mut read_weights =
                f.recorder
                    .verification_rng(Scheme::Cpat, 1, "native-full-read-weights")?;
            f.received_tokens(
                Phase::new(
                    Role::Reader,
                    Stage::NativeRead,
                    "native_Read_includes_Verify_one_record",
                )
                .decoded(),
                Some(1),
                std::slice::from_ref(&token_wires[0]),
                token_fields,
                || decode_cpat(&policy, std::slice::from_ref(&token_wires[0])),
                |received| {
                    need(
                        cpat::read_bit_set_checked(
                            &issuer,
                            &cached_metadata,
                            &policy,
                            &received[0],
                            &mut read_weights,
                        )
                        .map_err(native_error)?
                            == bit as usize,
                        "CPAT native read",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
    }
    Ok(())
}

fn hin_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::HinToken,
    };
    let setup = f.cached(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "native_issuer_keygen").encoded(),
        None,
        || {
            let (p, s) = hin::issuer_keygen(rng);
            let b = p.encode();
            Ok(Output::with_messages((p, s), vec![b]))
        },
    )?;
    let (public, secret) = &*setup;
    let reader_setup = f.cached(
        Phase::new(Role::Reader, Stage::KeyGeneration, "native_reader_keygen").encoded(),
        None,
        || {
            let (p, s) = hin::reader_keygen(rng);
            let b = p.encode().to_vec();
            Ok(Output::with_messages((p, s), vec![b]))
        },
    )?;
    let (reader, reader_secret) = &*reader_setup;
    let public_wire = public.encode();
    let installed = f.cached(
        Phase::new(
            Role::Verifier,
            Stage::Install,
            "issuer_validation_and_fixed_pairing_anchor_installation",
        )
        .decoded(),
        None,
        || {
            Ok(Output::with_messages(
                hin_public(&public_wire)?.install().map_err(native_error)?,
                vec![public_wire.clone()],
            ))
        },
    )?;
    let bit = f.recorder.bit;
    for &k in ks {
        if f.recorder.is_pipeline() {
            f.recorder.retained.clear();
            *rng = f
                .recorder
                .pipeline_rng(Scheme::HinToken, k, "slot-generation");
        }

        let tokens = f.source_asset(
            "issued-native-token-wallet",
            Some(k),
            &[
                Stage::IssueRequest,
                Stage::IssueResponse,
                Stage::IssueAccept,
            ],
            |f| {
                let requests = f.record(
                    Phase::new(Role::User, Stage::IssueRequest, "native_k_token_requests")
                        .encoded(),
                    Some(k),
                    || {
                        let v = (0..k)
                            .map(|_| hin::request(reader, rng).map_err(native_error))
                            .collect::<Result<Vec<_>>>()?;
                        let b = v.iter().map(|(q, _)| q.encode()).collect();
                        Ok(Output::with_messages(v, b))
                    },
                )?;
                let request_wires = f.take_messages()?;
                f.note_received(
                    (Role::Issuer, Stage::IssueResponse),
                    Some(k),
                    request_wires.iter().map(Vec::as_slice),
                    (Role::User, Stage::IssueRequest),
                )?;
                let _responses = f.record(
                    Phase::new(
                        Role::Issuer,
                        Stage::IssueResponse,
                        "native_k_token_responses",
                    )
                    .encoded()
                    .decoded(),
                    Some(k),
                    || {
                        let v = requests
                            .iter()
                            .enumerate()
                            .map(|(i, (_q, _))| {
                                let q = hin::ReceivedRequest::decode(&request_wires[i])
                                    .map_err(native_error)?;
                                hin::issue_received(
                                    secret,
                                    reader,
                                    q,
                                    ((i + bit as usize) % 2) as u8,
                                    rng,
                                )
                                .map_err(native_error)
                            })
                            .collect::<Result<Vec<_>>>()?;
                        let b = v.iter().map(hin::Response::encode).collect();
                        Ok(Output::with_messages(v, b))
                    },
                )?;
                let response_wires = f.take_messages()?;
                f.note_received(
                    (Role::User, Stage::IssueAccept),
                    Some(k),
                    response_wires.iter().map(Vec::as_slice),
                    (Role::Issuer, Stage::IssueResponse),
                )?;
                let tokens = f.record(
                    Phase::new(
                        Role::User,
                        Stage::IssueAccept,
                        "native_User1_proof_acceptance_and_representation_change",
                    )
                    .decoded(),
                    Some(k),
                    || {
                        let v = requests
                            .into_iter()
                            .zip(&response_wires)
                            .map(|((_, p), d)| {
                                hin::receive_received(
                                    p,
                                    hin::ReceivedResponse::decode(d).map_err(native_error)?,
                                    rng,
                                )
                                .map_err(native_error)
                            })
                            .collect::<Result<Vec<_>>>()?;
                        Ok(Output::value(v))
                    },
                )?;
                Ok(tokens)
            },
        )?;
        f.record(
            Phase::new(
                Role::User,
                Stage::OnlineGeneration,
                "send_already_issued_native_TokenLite_no_new_show",
            )
            .encoded(),
            Some(k),
            || {
                Ok(Output::with_messages(
                    (),
                    tokens.iter().map(hin::Token::encode).collect(),
                ))
            },
        )?;
        let token_wires = f.take_messages()?;
        f.note_request(
            &crate::adapters::Hin::new(&installed, hin::VerificationMode::Randomized),
            &tokens,
            k,
        )?;
        let token_fields = WireFields {
            g1: 5 * tokens.len(),
            g2: tokens.len(),
            gt: 0,
            fr: 0,
        };
        let mut verified = vec![];
        for selected_profile in f.verification_order(
            k,
            &[
                "native_sequential_specification",
                "safe_random_batch_by_same_issuer",
                "safe_random_batch_by_same_issuer_cached_anchor",
            ],
        ) {
            for (mode, name) in [
                (
                    hin::VerificationMode::Specification,
                    "native_sequential_specification",
                ),
                (
                    hin::VerificationMode::Randomized,
                    "safe_random_batch_by_same_issuer",
                ),
                (
                    hin::VerificationMode::RandomizedCachedAnchor,
                    "safe_random_batch_by_same_issuer_cached_anchor",
                ),
            ] {
                if name != selected_profile || !f.wants_verification_profile(name, k) {
                    continue;
                }
                if f.recorder.is_pipeline() {
                    *rng = f.recorder.verification_rng(
                        Scheme::HinToken,
                        k,
                        &format!("weights/{name}"),
                    )?;
                }

                let needs_record = k == 1
                    && f.wants_stage(Stage::MetadataRead)
                    && name == fixed_baseline_profile(Scheme::HinToken);
                let accepted = f.received_tokens(
                    Phase::new(Role::Verifier, Stage::VerificationCrypto, name),
                    Some(k),
                    &token_wires,
                    token_fields,
                    || decode_hin(&token_wires),
                    |tokens| {
                        if needs_record {
                            Ok(Output::value(
                                hin::verify_batch_records_checked(&installed, tokens, mode, rng)
                                    .ok_or("HinToken fixed verification")?,
                            ))
                        } else {
                            need(
                                hin::verify_batch_checked(&installed, tokens, mode, rng),
                                "HinToken verification",
                            )?;
                            Ok(Output::value(vec![]))
                        }
                    },
                )?;
                if needs_record {
                    verified = accepted;
                }
                f.accept_received(
                    checked_hin(&installed, mode, &tokens)?,
                    name,
                    if mode == hin::VerificationMode::Specification {
                        crate::batch_runtime::Mode::Specification
                    } else {
                        crate::batch_runtime::Mode::Randomized
                    },
                    rng,
                    Receipt::bytes(&token_wires, token_fields, || decode_hin(&token_wires)),
                )?;
            }
        }
        if (!f.recorder.is_pipeline() || k == 1) && f.wants_stage(Stage::MetadataRead) {
            f.record(
                Phase::new(
                    Role::Reader,
                    Stage::MetadataRead,
                    "one_previously_verified_record_bit0",
                ),
                Some(1),
                || {
                    need(
                        hin::read_bit_validated(reader_secret, &verified[0]) == Some(bit),
                        "HinToken read",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
        if (!f.recorder.is_pipeline() || k == 1) && f.wants_stage(Stage::NativeRead) {
            let mut read_weights =
                f.recorder
                    .verification_rng(Scheme::HinToken, 1, "native-full-read-weights")?;
            f.received_tokens(
                Phase::new(
                    Role::Reader,
                    Stage::NativeRead,
                    "native_Read_includes_Verify_one_record",
                )
                .decoded(),
                Some(1),
                std::slice::from_ref(&token_wires[0]),
                token_fields,
                || decode_hin(std::slice::from_ref(&token_wires[0])),
                |received| {
                    need(
                        hin::read_total_checked(
                            reader_secret,
                            &installed,
                            &received[0],
                            hin::VerificationMode::RandomizedCachedAnchor,
                            &mut read_weights,
                        ) == Some(bit),
                        "HinToken native read",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
    }
    Ok(())
}

fn msb_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let attributes = recorder.attributes;
    let mut f = Native {
        recorder,
        scheme: Scheme::Msb23,
    };
    let setup = f.cached(
        Phase::new(
            Role::System,
            Stage::Setup,
            "native_parameters_and_issuer_keygen",
        )
        .encoded(),
        None,
        || {
            let (p, i) = msb::setup(attributes, rng).map_err(native_error)?;
            let b = wire::encode_parameters(&p);
            Ok(Output::with_messages((p, i), vec![b]))
        },
    )?;
    let (pp, issuer) = &*setup;
    let public_wire = wire::encode_parameters(pp);
    let registered = f.cached(
        Phase::new(
            Role::User,
            Stage::Install,
            "native_parameter_key_checks_fixed_pairings_and_PoK_base_cache",
        )
        .decoded(),
        None,
        || {
            Ok(Output::with_messages(
                msb::install_cache(
                    wire::decode_parameters_checked(&public_wire).map_err(native_error)?,
                )
                .map_err(native_error)?,
                vec![public_wire.clone()],
            ))
        },
    )?;
    let user = f.cached(
        Phase::new(Role::User, Stage::KeyGeneration, "native_holder_keygen"),
        None,
        || Ok(Output::value(msb::user_keygen(rng))),
    )?;
    let agent = f.cached(
        Phase::new(Role::Agent, Stage::KeyGeneration, "native_delegatee_keygen"),
        None,
        || Ok(Output::value(msb::user_keygen(rng))),
    )?;
    let parent = f.source_asset(
        "issued-parent",
        None,
        &[
            Stage::IssueRequest,
            Stage::IssueResponse,
            Stage::IssueAccept,
        ],
        |f| {
            let (_request, pending) = f.record(
                Phase::new(
                    Role::User,
                    Stage::IssueRequest,
                    "native_issue_first_message",
                )
                .encoded(),
                None,
                || {
                    let (q, s) = msb::issue_begin(
                        &registered,
                        &user,
                        (101..101 + attributes as u64).map(S::from).collect(),
                        rng,
                    )
                    .map_err(native_error)?;
                    let b = wire::encode_issue_request(&q);
                    Ok(Output::with_messages((q, s), vec![b]))
                },
            )?;
            let request_wire = f.take_one()?;
            f.note_received(
                (Role::Issuer, Stage::VerificationCrypto),
                None,
                std::iter::once(request_wire.as_slice()),
                (Role::User, Stage::IssueRequest),
            )?;
            let (_challenge, verifier) = f.record(
                Phase::new(
                    Role::Issuer,
                    Stage::VerificationCrypto,
                    "live_issue_verifier_challenge",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let (c, s) = msb::issue_challenge_checked(
                        &registered,
                        wire::decode_issue_request_checked(&request_wire).map_err(native_error)?,
                        rng,
                    )
                    .map_err(native_error)?;
                    let b = c.bytes();
                    Ok(Output::with_messages((c, s), vec![b]))
                },
            )?;
            let challenge_wire = f.take_one()?;
            f.note_received(
                (Role::User, Stage::IssueRequest),
                None,
                std::iter::once(challenge_wire.as_slice()),
                (Role::Issuer, Stage::IssueResponse),
            )?;
            let (_answer, pending) = f.record(
                Phase::new(
                    Role::User,
                    Stage::IssueRequest,
                    "live_issue_holder_response",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let (a, s) = msb::issue_respond(
                        pending,
                        baseline_core::msb23::pok::Challenge::from_bytes(&challenge_wire)
                            .map_err(native_error)?,
                    )
                    .map_err(native_error)?;
                    let b = a.bytes();
                    Ok(Output::with_messages((a, s), vec![b]))
                },
            )?;
            let answer_wire = f.take_one()?;
            f.note_received(
                (Role::Issuer, Stage::IssueResponse),
                None,
                std::iter::once(answer_wire.as_slice()),
                (Role::User, Stage::IssueRequest),
            )?;
            let _delivery = f.record(
                Phase::new(Role::Issuer, Stage::IssueResponse, "native_issue_delivery")
                    .encoded()
                    .decoded(),
                None,
                || {
                    let d = msb::issue_issuer_received(
                        &registered,
                        issuer,
                        verifier,
                        baseline_core::msb23::pok::ReceivedResponse::from_bytes(&answer_wire)
                            .map_err(native_error)?,
                        rng,
                    )
                    .map_err(native_error)?;
                    let b = wire::encode_issue_delivery(&d);
                    Ok(Output::with_messages(d, vec![b]))
                },
            )?;
            let delivery_wire = f.take_one()?;
            let receive_profile = f.recorder.profile.clone();
            f.note_received(
                (Role::User, Stage::IssueAccept),
                None,
                std::iter::once(delivery_wire.as_slice()),
                (Role::Issuer, Stage::IssueResponse),
            )?;
            let mut receive_weights =
                f.recorder
                    .verification_rng(Scheme::Msb23, 1, "issue-receive-weights")?;
            let parent = f.record(
                Phase::new(
                    Role::User,
                    Stage::IssueAccept,
                    "complete_Obtain_random_pairing_key_candidate",
                )
                .decoded(),
                None,
                || {
                    let delivery = wire::decode_issue_delivery_checked(&delivery_wire)
                        .map_err(native_error)?;
                    Ok(Output::value(
                        match receive_profile.as_str() {
                            "Specification" => {
                                msb::issue_finish_checked(&registered, pending, delivery, rng)
                            }
                            "RandomizedCachedGt" => msb::issue_finish_checked_random(
                                &registered,
                                pending,
                                delivery,
                                rng,
                            ),
                            _ => msb::issue_finish_checked_random_pairing_key_rngs(
                                &registered,
                                pending,
                                delivery,
                                &mut receive_weights,
                                rng,
                            ),
                        }
                        .map_err(native_error)?,
                    ))
                },
            )?;
            Ok(parent)
        },
    )?;
    let child = f.source_asset(
        "delegated-child",
        None,
        &[
            Stage::IssueRequest,
            Stage::IssueResponse,
            Stage::IssueAccept,
            Stage::DelegateRequest,
            Stage::DelegateSend,
            Stage::DelegateReceive,
        ],
        |f| {
            let (_request, pending) = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::DelegateRequest,
                    "native_delegatee_request",
                )
                .encoded(),
                None,
                || {
                    let (q, s) = msb::delegate_begin(
                        &registered,
                        &agent,
                        vec![msb::period_attribute()],
                        rng,
                    )
                    .map_err(native_error)?;
                    let b = wire::encode_delegate_request(&q);
                    Ok(Output::with_messages((q, s), vec![b]))
                },
            )?;
            let request_wire = f.take_one()?;
            f.note_received(
                (Role::User, Stage::DelegateSend),
                None,
                std::iter::once(request_wire.as_slice()),
                (Role::Agent, Stage::DelegateRequest),
            )?;
            let _delivery = f.record(
                Phase::new(Role::User, Stage::DelegateSend, "native_delegator_delivery")
                    .encoded()
                    .decoded(),
                None,
                || {
                    let d = msb::delegate_sender_checked(
                        &registered,
                        &parent,
                        wire::decode_delegate_request_checked(&request_wire)
                            .map_err(native_error)?,
                        rng,
                    )
                    .map_err(native_error)?;
                    let b = wire::encode_delegate_delivery(&d);
                    Ok(Output::with_messages(d, vec![b]))
                },
            )?;
            let delivery_wire = f.take_one()?;
            let delegate_profile = f.recorder.profile.clone();
            f.note_received(
                (Role::Agent, Stage::DelegateReceive),
                None,
                std::iter::once(delivery_wire.as_slice()),
                (Role::User, Stage::DelegateSend),
            )?;
            let mut receive_weights =
                f.recorder
                    .verification_rng(Scheme::Msb23, 1, "delegate-receive-weights")?;
            let child = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::DelegateReceive,
                    "native_delegatee_receive_random_profile",
                )
                .decoded(),
                None,
                || {
                    let delivery = wire::decode_delegate_delivery_checked(&delivery_wire)
                        .map_err(native_error)?;
                    Ok(Output::value(
                        if delegate_profile == "Specification" {
                            msb::delegate_finish_checked(&registered, pending, delivery, rng)
                        } else {
                            msb::delegate_finish_checked_random_rngs(
                                &registered,
                                pending,
                                delivery,
                                &mut receive_weights,
                                rng,
                            )
                        }
                        .map_err(native_error)?,
                    ))
                },
            )?;
            Ok(child)
        },
    )?;
    let show_profile = f.recorder.profile.clone();
    let disclosed = msb::Disclosure {
        indices: vec![1, 2],
        sets: vec![
            vec![S::from(101), S::from(102)],
            vec![msb::period_attribute()],
        ],
    };
    for &k in ks {
        if f.recorder.is_pipeline() {
            f.recorder.retained.clear();
            *rng = f.recorder.pipeline_rng(Scheme::Msb23, k, "slot-generation");
        }

        if f.recorder.is_pipeline() {
            msb_pipeline_present(&mut f, &registered, &child, &disclosed, k, rng)?;
            continue;
        }

        let prepared = f.record(
            Phase::new(
                Role::Agent,
                Stage::Preparation,
                "complete_presentations_known_policy_OpenSubset_AggregateAcross",
            ),
            Some(k),
            || {
                Ok(Output::value(
                    (0..k)
                        .map(|_| {
                            msb::show_prepare_policy(&registered, &child, disclosed.clone(), rng)
                                .map_err(native_error)
                        })
                        .collect::<Result<Vec<_>>>()?,
                ))
            },
        )?;
        let mut context = [0u8; 32];
        rng.fill_bytes(&mut context);
        let firsts = f.record(
            Phase::new(
                Role::Agent,
                Stage::OnlineGeneration,
                "complete_presentations_context_only_nym_PoK_first",
            )
            .encoded(),
            Some(k),
            || {
                let v = prepared
                    .into_iter()
                    .map(|p| {
                        msb::show_begin_prepared(&registered, p, context.to_vec())
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = v.iter().map(|(m, _)| wire::encode_show_first(m)).collect();
                Ok(Output::with_messages(v, b))
            },
        )?;
        let first_wires = f.take_messages()?;
        let first_fields = firsts
            .iter()
            .fold(WireFields::default(), |mut fields, (m, _)| {
                fields.add(WireFields {
                    g1: 6 + m.cs.len(),
                    g2: 1,
                    gt: 0,
                    fr: m.disclosed.sets.iter().map(Vec::len).sum(),
                });
                fields
            });
        let challenges = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_challenge",
            )
            .encoded()
            .decoded(),
            Some(k),
            &first_wires,
            first_fields,
            || {
                first_wires
                    .iter()
                    .map(|bytes| {
                        msb::decode_show_first_received(&registered, bytes, &disclosed, &context)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let values = received
                    .into_iter()
                    .map(|first| {
                        msb::show_challenge_checked(&registered, first, &disclosed, &context, rng)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let messages = values.iter().map(|(m, _)| m.bytes()).collect();
                Ok(Output::with_messages(values, messages))
            },
        )?;
        let challenge_wires = f.take_messages()?;
        let (_responses, verifiers) = f.record(
            Phase::new(
                Role::Agent,
                Stage::OnlineGeneration,
                "complete_presentations_live_holder_response",
            )
            .encoded()
            .decoded(),
            Some(k),
            || {
                let mut answers = vec![];
                let mut verifiers = vec![];
                for (i, ((_, p), (_challenge, v))) in firsts.into_iter().zip(challenges).enumerate()
                {
                    let challenge =
                        baseline_core::msb23::pok::Challenge::from_bytes(&challenge_wires[i])
                            .map_err(native_error)?;
                    answers.push(msb::show_respond(p, challenge).map_err(native_error)?);
                    verifiers.push(v);
                }
                let b = answers.iter().map(|a| a.bytes()).collect();
                Ok(Output::with_messages((answers, verifiers), b))
            },
        )?;
        let response_wires = f.take_messages()?;
        let response_fields =
            _responses
                .iter()
                .fold(WireFields::default(), |mut fields, response| {
                    fields.add(WireFields {
                        g1: response.announcements.len(),
                        g2: 0,
                        gt: 0,
                        fr: 1 + response.responses.len(),
                    });
                    fields
                });
        let records = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_native_final_random_profile",
            )
            .decoded(),
            Some(k),
            &response_wires,
            response_fields,
            || {
                verifiers
                    .into_iter()
                    .zip(&response_wires)
                    .map(|(state, bytes)| {
                        let response = msb::decode_show_response_received(&state, bytes)
                            .map_err(native_error)?;
                        Ok((state, response))
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let records = received
                    .into_iter()
                    .map(|(state, response)| {
                        msb::freeze_show_received(&registered, state, response)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                need(
                    msb::verify_frozen_shows(
                        &registered,
                        &records,
                        if show_profile == "Specification" {
                            baseline_core::pairing_verify::Mode::Specification
                        } else {
                            baseline_core::pairing_verify::Mode::Randomized
                        },
                        rng,
                    ),
                    "MSB live final",
                )?;
                Ok(Output::value(records))
            },
        )?;
        f.accept(
            crate::adapters::Msb::new(&registered),
            &records,
            if show_profile == "Specification" {
                "Specification"
            } else {
                "Randomized"
            },
            if show_profile == "Specification" {
                crate::batch_runtime::Mode::Specification
            } else {
                crate::batch_runtime::Mode::Randomized
            },
            rng,
            Receipt::Live,
        )?;
    }
    Ok(())
}

fn slw_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mode = if recorder.profile == "Specification" {
        slw::VerificationMode::Specification
    } else {
        slw::VerificationMode::Randomized
    };
    let attributes = recorder.attributes;
    let mut f = Native {
        recorder,
        scheme: Scheme::Slw25,
    };
    let setup = f.cached(
        Phase::new(
            Role::System,
            Stage::Setup,
            "flat_revocation_disabled_native_setup_and_local_install",
        )
        .encoded(),
        None,
        || {
            let (p, i) = slw::setup(attributes, rng).map_err(native_error)?;
            let b = p.encode();
            Ok(Output::with_messages((p, i), vec![b]))
        },
    )?;
    let (pk, issuer) = &*setup;
    let public_wire = pk.encode();
    let pk = f.cached(
        Phase::new(
            Role::Verifier,
            Stage::Install,
            "fresh_role_public_key_decode_checks_and_issuer_binding_cache",
        )
        .decoded(),
        None,
        || {
            Ok(Output::with_messages(
                slw::PublicKey::decode_install_profile(&public_wire, mode, rng)
                    .map_err(native_error)?,
                vec![public_wire.clone()],
            ))
        },
    )?;
    let user = f.cached(
        Phase::new(Role::User, Stage::KeyGeneration, "native_holder_secrets"),
        None,
        || Ok(Output::value(slw::Holder::generate(rng))),
    )?;
    let agent = f.cached(
        Phase::new(
            Role::Agent,
            Stage::KeyGeneration,
            "native_delegatee_secrets",
        ),
        None,
        || Ok(Output::value(slw::Holder::generate(rng))),
    )?;
    let attrs = (100..100 + attributes as u64)
        .map(S::from)
        .collect::<Vec<_>>();
    let parent = f.source_asset(
        "issued-parent",
        None,
        &[
            Stage::IssueRequest,
            Stage::IssueResponse,
            Stage::IssueAccept,
        ],
        |f| {
            let (mut pending, request) = f.record(
                Phase::new(Role::User, Stage::IssueRequest, "native_issue_request").encoded(),
                None,
                || {
                    let v = slw::issue_prepare(&pk, &user, &attrs).map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::Issuer, Stage::VerificationCrypto),
                None,
                std::iter::once(request.as_slice()),
                (Role::User, Stage::IssueRequest),
            )?;
            let (verifier, first) = f.record(
                Phase::new(
                    Role::Issuer,
                    Stage::VerificationCrypto,
                    "live_issue_verifier_first",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::issuer_begin(&pk, &request, rng).map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::User, Stage::IssueRequest),
                None,
                std::iter::once(first.as_slice()),
                (Role::Issuer, Stage::IssueResponse),
            )?;
            let (prover, second) = f.record(
                Phase::new(Role::User, Stage::IssueRequest, "live_issue_holder_first")
                    .encoded()
                    .decoded(),
                None,
                || {
                    let v = slw::holder_issue_first_prepared(&mut pending, &first, rng)
                        .map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::Issuer, Stage::VerificationCrypto),
                None,
                std::iter::once(second.as_slice()),
                (Role::User, Stage::IssueRequest),
            )?;
            let (verifier, third) = f.record(
                Phase::new(
                    Role::Issuer,
                    Stage::VerificationCrypto,
                    "live_issue_verifier_challenge",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::issuer_issue_challenge(verifier, &second, rng)
                        .map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::User, Stage::IssueRequest),
                None,
                std::iter::once(third.as_slice()),
                (Role::Issuer, Stage::IssueResponse),
            )?;
            let fourth = f.record(
                Phase::new(
                    Role::User,
                    Stage::IssueRequest,
                    "live_issue_holder_opening_check_and_response",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::holder_issue_respond(prover, &third).map_err(native_error)?;
                    Ok(Output::with_messages(v.clone(), vec![v]))
                },
            )?;
            f.note_received(
                (Role::Issuer, Stage::IssueResponse),
                None,
                std::iter::once(fourth.as_slice()),
                (Role::User, Stage::IssueRequest),
            )?;
            let response = f.record(
                Phase::new(
                    Role::Issuer,
                    Stage::IssueResponse,
                    "native_issue_signature_response",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::issuer_issue_finish(&pk, issuer, verifier, &fourth, rng)
                        .map_err(native_error)?;
                    Ok(Output::with_messages(v.clone(), vec![v]))
                },
            )?;
            f.note_received(
                (Role::User, Stage::IssueAccept),
                None,
                std::iter::once(response.as_slice()),
                (Role::Issuer, Stage::IssueResponse),
            )?;
            let mut receive_weights =
                f.recorder
                    .verification_rng(Scheme::Slw25, 1, "issue-receive-weights")?;
            let parent = f.record(
                Phase::new(
                    Role::User,
                    Stage::IssueAccept,
                    "native_receive_complete_signature_and_purge_checks",
                )
                .decoded(),
                None,
                || {
                    Ok(Output::value(
                        slw::receive_expected_profile(
                            &pk,
                            &user,
                            &response,
                            &(2..attributes + 2).collect::<Vec<_>>(),
                            &attrs,
                            mode,
                            &mut receive_weights,
                        )
                        .map_err(native_error)?,
                    ))
                },
            )?;
            Ok(parent)
        },
    )?;
    let keep = (2..attributes + 2).collect::<Vec<_>>();
    let child = f.source_asset(
        "delegated-child",
        None,
        &[
            Stage::IssueRequest,
            Stage::IssueResponse,
            Stage::IssueAccept,
            Stage::DelegateRequest,
            Stage::DelegateSend,
            Stage::DelegateReceive,
        ],
        |f| {
            let (mut pending, prefix) = f.record(
                Phase::new(
                    Role::User,
                    Stage::DelegateSend,
                    "native_delegate_preparation_and_prefix",
                )
                .encoded(),
                None,
                || {
                    let v = slw::delegate_prepare(&pk, &user, &parent, &keep, rng)
                        .map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::Agent, Stage::DelegateRequest),
                None,
                std::iter::once(prefix.as_slice()),
                (Role::User, Stage::DelegateSend),
            )?;
            let (receiver, cm) = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::DelegateRequest,
                    "native_receiver_commitment",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::receiver_cm(&pk, &agent, &prefix).map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::User, Stage::DelegateSend),
                None,
                std::iter::once(cm.as_slice()),
                (Role::Agent, Stage::DelegateRequest),
            )?;
            let (verifier, first) = f.record(
                Phase::new(
                    Role::User,
                    Stage::DelegateSend,
                    "live_delegator_verifier_first",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::delegator_begin(&mut pending, &cm, rng).map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::Agent, Stage::DelegateReceive),
                None,
                std::iter::once(first.as_slice()),
                (Role::User, Stage::DelegateSend),
            )?;
            let (prover, second) = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::DelegateReceive,
                    "live_receiver_holder_first",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::receiver_first(receiver, &first, rng).map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::User, Stage::DelegateSend),
                None,
                std::iter::once(second.as_slice()),
                (Role::Agent, Stage::DelegateReceive),
            )?;
            let (verifier, third) = f.record(
                Phase::new(Role::User, Stage::DelegateSend, "live_delegator_challenge")
                    .encoded()
                    .decoded(),
                None,
                || {
                    let v =
                        slw::delegator_challenge(verifier, &second, rng).map_err(native_error)?;
                    let b = v.1.clone();
                    Ok(Output::with_messages(v, vec![b]))
                },
            )?;
            f.note_received(
                (Role::Agent, Stage::DelegateReceive),
                None,
                std::iter::once(third.as_slice()),
                (Role::User, Stage::DelegateSend),
            )?;
            let fourth = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::DelegateReceive,
                    "live_receiver_opening_check_and_response",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::receiver_respond(prover, &third).map_err(native_error)?;
                    Ok(Output::with_messages(v.clone(), vec![v]))
                },
            )?;
            f.note_received(
                (Role::User, Stage::DelegateSend),
                None,
                std::iter::once(fourth.as_slice()),
                (Role::Agent, Stage::DelegateReceive),
            )?;
            let response = f.record(
                Phase::new(
                    Role::User,
                    Stage::DelegateSend,
                    "native_delegated_credential_response",
                )
                .encoded()
                .decoded(),
                None,
                || {
                    let v = slw::delegator_finish(verifier, &fourth).map_err(native_error)?;
                    Ok(Output::with_messages(v.clone(), vec![v]))
                },
            )?;
            f.note_received(
                (Role::Agent, Stage::DelegateReceive),
                None,
                std::iter::once(response.as_slice()),
                (Role::User, Stage::DelegateSend),
            )?;
            let mut receive_weights =
                f.recorder
                    .verification_rng(Scheme::Slw25, 1, "delegate-receive-weights")?;
            let child = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::DelegateReceive,
                    "native_delegatee_receive_complete_checks",
                )
                .decoded(),
                None,
                || {
                    Ok(Output::value(
                        slw::receive_expected_profile(
                            &pk,
                            &agent,
                            &response,
                            &keep,
                            &attrs,
                            mode,
                            &mut receive_weights,
                        )
                        .map_err(native_error)?,
                    ))
                },
            )?;
            Ok(child)
        },
    )?;
    let disclosed = [2, 3, 4];
    let values = [S::from(100), S::from(101), S::from(102)];
    for &k in ks {
        if f.recorder.is_pipeline() {
            f.recorder.retained.clear();
            *rng = f.recorder.pipeline_rng(Scheme::Slw25, k, "slot-generation");
        }

        if f.recorder.is_pipeline() {
            slw_pipeline_present(&mut f, &pk, &agent, &child, &disclosed, &values, k, rng)?;
            continue;
        }

        let prepared = f.record(
            Phase::new(
                Role::Agent,
                Stage::Preparation,
                "complete_presentations_fixed_CDM_true_and_simulated_branches",
            )
            .encoded(),
            Some(k),
            || {
                Ok(Output::value(
                    (0..k)
                        .map(|_| {
                            slw::show_prepare_profile(&pk, &agent, &child, &disclosed, mode, rng)
                                .map_err(native_error)
                        })
                        .collect::<Result<Vec<_>>>()?,
                ))
            },
        )?;
        let mut transcripts = prepared
            .iter()
            .map(|(_, prefix)| vec![prefix.clone()])
            .collect::<Vec<_>>();
        let prepared = f.record(
            Phase::new(
                Role::Agent,
                Stage::OnlineGeneration,
                "complete_presentations_send_prepared_prefixes",
            ),
            Some(k),
            || {
                let b = prepared.iter().map(|(_, prefix)| prefix.clone()).collect();
                Ok(Output::with_messages(prepared, b))
            },
        )?;
        let prefix_wires = f.take_messages()?;
        let prefix_fields = prefix_wires
            .iter()
            .fold(WireFields::default(), |mut fields, bytes| {
                fields.add(slw_wire_fields(bytes));
                fields
            });
        let verifiers = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_begin",
            )
            .encoded()
            .decoded(),
            Some(k),
            &prefix_wires,
            prefix_fields,
            || {
                prefix_wires
                    .iter()
                    .map(|bytes| {
                        slw::decode_show_prefix_received(&pk, bytes, &disclosed, &values)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let values = received
                    .into_iter()
                    .map(|prefix| {
                        slw::show_verifier_begin_received_profile(&pk, prefix, mode, rng)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let messages = values.iter().map(|(_, message)| message.clone()).collect();
                Ok(Output::with_messages(values, messages))
            },
        )?;
        for (messages, (_, msg)) in transcripts.iter_mut().zip(&verifiers) {
            messages.push(msg.clone());
        }
        let (provers, verifiers) = f.record(
            Phase::new(
                Role::Agent,
                Stage::OnlineGeneration,
                "complete_presentations_fresh_verifier_commitment_term_only",
            )
            .encoded()
            .decoded(),
            Some(k),
            || {
                let mut p = vec![];
                let mut vs = vec![];
                for ((mut prepared, _), (v, first)) in prepared.into_iter().zip(verifiers) {
                    p.push(
                        slw::show_holder_first(&pk, &mut prepared, &first, rng)
                            .map_err(native_error)?,
                    );
                    vs.push(v);
                }
                let b = p.iter().map(|(_, msg)| msg.clone()).collect();
                Ok(Output::with_messages((p, vs), b))
            },
        )?;
        for (messages, (_, msg)) in transcripts.iter_mut().zip(&provers) {
            messages.push(msg.clone());
        }
        let prover_wires = f.take_messages()?;
        let prover_fields = prover_wires
            .iter()
            .fold(WireFields::default(), |mut fields, bytes| {
                fields.add(slw_wire_fields(bytes));
                fields
            });
        let (provers, verifiers, thirds) = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_challenge",
            )
            .encoded()
            .decoded(),
            Some(k),
            &prover_wires,
            prover_fields,
            || {
                provers
                    .into_iter()
                    .zip(verifiers)
                    .zip(&prover_wires)
                    .map(|(((prover, _), verifier), bytes)| {
                        let message = slw::decode_show_first_received(&verifier, bytes)
                            .map_err(native_error)?;
                        Ok((prover, verifier, message))
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let mut ps = vec![];
                let mut vs = vec![];
                let mut messages = vec![];
                for (prover, verifier, message) in received {
                    let (verifier, third) =
                        slw::show_verifier_challenge_received_profile(verifier, message, rng)
                            .map_err(native_error)?;
                    ps.push(prover);
                    vs.push(verifier);
                    messages.push(third);
                }
                Ok(Output::with_messages((ps, vs, messages.clone()), messages))
            },
        )?;
        for (messages, msg) in transcripts.iter_mut().zip(&thirds) {
            messages.push(msg.clone());
        }
        let responses = f.record(
            Phase::new(
                Role::Agent,
                Stage::OnlineGeneration,
                "complete_presentations_check_fresh_opening_and_respond",
            )
            .encoded()
            .decoded(),
            Some(k),
            || {
                let v = provers
                    .into_iter()
                    .zip(thirds)
                    .map(|(p, m)| slw::show_holder_respond(p, &m).map_err(native_error))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Output::with_messages(v.clone(), v))
            },
        )?;
        for (messages, msg) in transcripts.iter_mut().zip(&responses) {
            messages.push(msg.clone());
        }
        let final_wires = f.take_messages()?;
        let final_fields = final_wires
            .iter()
            .fold(WireFields::default(), |mut fields, bytes| {
                fields.add(slw_wire_fields(bytes));
                fields
            });
        f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_native_final_random_profile",
            )
            .decoded(),
            Some(k),
            &final_wires,
            final_fields,
            || {
                verifiers
                    .into_iter()
                    .zip(&final_wires)
                    .map(|(state, bytes)| {
                        let message =
                            slw::decode_show_final_received(&state, bytes).map_err(native_error)?;
                        Ok((state, message))
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                need(
                    slw::show_verifier_finish_many_received_profile(received, mode, rng)
                        .map_err(native_error)?,
                    "SLW live final",
                )?;
                Ok(Output::value(()))
            },
        )?;
        let records = transcripts
            .into_iter()
            .map(|messages| {
                Ok(SlwLiveRecord {
                    messages: messages
                        .try_into()
                        .map_err(|_| "incomplete live transcript")?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let adapter = SlwLiveAdapter {
            namespace: crate::batch_runtime::Adapter::namespace(&crate::adapters::Slw::new(&pk))
                .to_vec(),
            issuer: pk.issuer_id(),
        };
        f.accept(
            adapter,
            &records,
            if mode == slw::VerificationMode::Specification {
                "Specification"
            } else {
                "Randomized"
            },
            if mode == slw::VerificationMode::Specification {
                crate::batch_runtime::Mode::Specification
            } else {
                crate::batch_runtime::Mode::Randomized
            },
            rng,
            Receipt::Live,
        )?;
    }
    Ok(())
}

fn msb_pipeline_present(
    f: &mut Native<'_, '_>,
    registered: &msb::Registered,
    child: &msb::Credential,
    disclosed: &msb::Disclosure,
    k: usize,
    rng: &mut StdRng,
) -> Result<()> {
    let prepared = f.record(
        Phase::new(
            Role::Agent,
            Stage::Preparation,
            "complete_presentations_known_policy_OpenSubset_AggregateAcross",
        ),
        Some(k),
        || {
            Ok(Output::value(
                (0..k)
                    .map(|_| {
                        msb::show_prepare_policy(registered, child, disclosed.clone(), rng)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?,
            ))
        },
    )?;
    let mut context = [0u8; 32];
    rng.fill_bytes(&mut context);
    let firsts = f.record(
        Phase::new(
            Role::Agent,
            Stage::OnlineGeneration,
            "complete_presentations_context_only_nym_PoK_first",
        )
        .encoded(),
        Some(k),
        || {
            let values = prepared
                .into_iter()
                .map(|p| {
                    msb::show_begin_prepared(registered, p, context.to_vec()).map_err(native_error)
                })
                .collect::<Result<Vec<_>>>()?;
            let messages = values
                .iter()
                .map(|(m, _)| wire::encode_show_first(m))
                .collect();
            Ok(Output::with_messages(values, messages))
        },
    )?;
    let first_wires = f.take_messages()?;
    let first_fields = firsts.iter().fold(WireFields::default(), |mut a, (m, _)| {
        a.add(WireFields {
            g1: 6 + m.cs.len(),
            g2: 1,
            gt: 0,
            fr: m.disclosed.sets.iter().map(Vec::len).sum(),
        });
        a
    });
    let mut firsts = Some(firsts);
    let mut original_challenges = None;
    let mut response_wires = None;
    let mut response_fields = WireFields::default();
    for profile in f.recorder.verifier_profiles(Scheme::Msb23, k) {
        f.recorder.profile = profile.clone();
        let mut live_rng = f
            .recorder
            .pipeline_rng(Scheme::Msb23, k, "live-verifier-challenges");
        let challenges = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_challenge",
            )
            .encoded()
            .decoded(),
            Some(k),
            &first_wires,
            first_fields,
            || {
                first_wires
                    .iter()
                    .map(|bytes| {
                        msb::decode_show_first_received(registered, bytes, disclosed, &context)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let values = received
                    .into_iter()
                    .map(|first| {
                        msb::show_challenge_checked(
                            registered,
                            first,
                            disclosed,
                            &context,
                            &mut live_rng,
                        )
                        .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let messages = values.iter().map(|(m, _)| m.bytes()).collect();
                Ok(Output::with_messages(values, messages))
            },
        )?;
        let challenge_wires = f.take_messages()?;
        if let Some(original) = &original_challenges {
            need(
                original == &challenge_wires,
                "MSB shared-slot native challenge bytes changed across verifier profiles",
            )?;
        } else {
            original_challenges = Some(challenge_wires.clone());
        }
        let verifiers = if let Some(firsts) = firsts.take() {
            let (responses, verifiers) = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::OnlineGeneration,
                    "complete_presentations_live_holder_response",
                )
                .encoded()
                .decoded(),
                Some(k),
                || {
                    let mut responses = vec![];
                    let mut verifiers = vec![];
                    for (i, ((_, prover), (_, verifier))) in
                        firsts.into_iter().zip(challenges).enumerate()
                    {
                        let challenge =
                            baseline_core::msb23::pok::Challenge::from_bytes(&challenge_wires[i])
                                .map_err(native_error)?;
                        responses.push(msb::show_respond(prover, challenge).map_err(native_error)?);
                        verifiers.push(verifier);
                    }
                    let messages = responses.iter().map(|r| r.bytes()).collect();
                    Ok(Output::with_messages((responses, verifiers), messages))
                },
            )?;
            response_fields = responses.iter().fold(WireFields::default(), |mut a, r| {
                a.add(WireFields {
                    g1: r.announcements.len(),
                    g2: 0,
                    gt: 0,
                    fr: 1 + r.responses.len(),
                });
                a
            });
            response_wires = Some(f.take_messages()?);
            verifiers
        } else {
            challenges
                .into_iter()
                .map(|(_, verifier)| verifier)
                .collect()
        };
        let responses = response_wires.as_ref().ok_or("MSB live response absent")?;
        let mut weights = f.recorder.verification_rng(
            Scheme::Msb23,
            k,
            &format!("verification-weights/{profile}"),
        )?;
        let records = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_native_final_random_profile",
            )
            .decoded(),
            Some(k),
            responses,
            response_fields,
            || {
                verifiers
                    .into_iter()
                    .zip(responses)
                    .map(|(state, bytes)| {
                        let response = msb::decode_show_response_received(&state, bytes)
                            .map_err(native_error)?;
                        Ok((state, response))
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let records = received
                    .into_iter()
                    .map(|(state, response)| {
                        msb::freeze_show_received(registered, state, response).map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                need(
                    msb::verify_frozen_shows(
                        registered,
                        &records,
                        if profile == "Specification" {
                            baseline_core::pairing_verify::Mode::Specification
                        } else {
                            baseline_core::pairing_verify::Mode::Randomized
                        },
                        &mut weights,
                    ),
                    "MSB native live final verification",
                )?;
                Ok(Output::value(records))
            },
        )?;
        f.note_request(&crate::adapters::Msb::new(registered), &records, k)?;
        f.accept(
            crate::adapters::Msb::new(registered),
            &records,
            if profile == "Specification" {
                "Specification"
            } else {
                "Randomized"
            },
            if profile == "Specification" {
                crate::batch_runtime::Mode::Specification
            } else {
                crate::batch_runtime::Mode::Randomized
            },
            rng,
            Receipt::Live,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn slw_pipeline_present(
    f: &mut Native<'_, '_>,
    pk: &slw::PublicKey,
    agent: &slw::Holder,
    child: &slw::Credential,
    disclosed: &[usize],
    values: &[S],
    k: usize,
    rng: &mut StdRng,
) -> Result<()> {
    let prepared = f.record(
        Phase::new(
            Role::Agent,
            Stage::Preparation,
            "complete_presentations_fixed_CDM_true_and_simulated_branches",
        )
        .encoded(),
        Some(k),
        || {
            Ok(Output::value(
                (0..k)
                    .map(|_| {
                        slw::show_prepare_profile(
                            pk,
                            agent,
                            child,
                            disclosed,
                            slw::VerificationMode::Randomized,
                            rng,
                        )
                        .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?,
            ))
        },
    )?;
    let prepared = f.record(
        Phase::new(
            Role::Agent,
            Stage::OnlineGeneration,
            "complete_presentations_send_prepared_prefixes",
        ),
        Some(k),
        || {
            let messages = prepared.iter().map(|(_, prefix)| prefix.clone()).collect();
            Ok(Output::with_messages(prepared, messages))
        },
    )?;
    let prefix_wires = f.take_messages()?;
    let prefix_fields = prefix_wires.iter().fold(WireFields::default(), |mut a, b| {
        a.add(slw_wire_fields(b));
        a
    });
    let mut prepared = Some(prepared);
    let mut original_first = None;
    let mut original_third = None;
    let mut prover_wires = None;
    let mut final_wires = None;
    for profile in f.recorder.verifier_profiles(Scheme::Slw25, k) {
        f.recorder.profile = profile.clone();
        let mode = if profile == "Specification" {
            slw::VerificationMode::Specification
        } else {
            slw::VerificationMode::Randomized
        };
        let mut first_rng = f
            .recorder
            .pipeline_rng(Scheme::Slw25, k, "live-verifier-first");
        let mut purge_weights =
            f.recorder
                .verification_rng(Scheme::Slw25, k, &format!("purge-weights/{profile}"))?;
        let verifiers = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_begin",
            )
            .encoded()
            .decoded(),
            Some(k),
            &prefix_wires,
            prefix_fields,
            || {
                prefix_wires
                    .iter()
                    .map(|bytes| {
                        slw::decode_show_prefix_received(pk, bytes, disclosed, values)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let values = slw::show_verifier_begin_many_received_profile_rngs(
                    pk,
                    received,
                    mode,
                    &mut purge_weights,
                    &mut first_rng,
                )
                .map_err(native_error)?;
                let messages = values.iter().map(|(_, m)| m.clone()).collect();
                Ok(Output::with_messages(values, messages))
            },
        )?;
        let first_wires = f.take_messages()?;
        if let Some(original) = &original_first {
            need(
                original == &first_wires,
                "SLW shared-slot native VFirst bytes changed across verifier profiles",
            )?;
        } else {
            original_first = Some(first_wires.clone());
        }
        let mut provers = None;
        let verifiers = if let Some(prepared) = prepared.take() {
            let (p, v) = f.record(
                Phase::new(
                    Role::Agent,
                    Stage::OnlineGeneration,
                    "complete_presentations_fresh_verifier_commitment_term_only",
                )
                .encoded()
                .decoded(),
                Some(k),
                || {
                    let mut p = vec![];
                    let mut v = vec![];
                    for ((mut prepared, _), (verifier, first)) in
                        prepared.into_iter().zip(verifiers)
                    {
                        p.push(
                            slw::show_holder_first(pk, &mut prepared, &first, rng)
                                .map_err(native_error)?,
                        );
                        v.push(verifier);
                    }
                    let messages = p.iter().map(|(_, m)| m.clone()).collect();
                    Ok(Output::with_messages((p, v), messages))
                },
            )?;
            prover_wires = Some(f.take_messages()?);
            provers = Some(p.into_iter().map(|(p, _)| p).collect::<Vec<_>>());
            v
        } else {
            verifiers
                .into_iter()
                .map(|(verifier, _)| verifier)
                .collect()
        };
        let prover_messages = prover_wires.as_ref().ok_or("SLW native PFirst absent")?;
        let prover_fields = prover_messages
            .iter()
            .fold(WireFields::default(), |mut a, b| {
                a.add(slw_wire_fields(b));
                a
            });
        let mut challenge_rng = f
            .recorder
            .pipeline_rng(Scheme::Slw25, k, "live-verifier-third");
        let verifiers = f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_challenge",
            )
            .encoded()
            .decoded(),
            Some(k),
            prover_messages,
            prover_fields,
            || {
                verifiers
                    .into_iter()
                    .zip(prover_messages)
                    .map(|(verifier, bytes)| {
                        let message = slw::decode_show_first_received(&verifier, bytes)
                            .map_err(native_error)?;
                        Ok((verifier, message))
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                let values = received
                    .into_iter()
                    .map(|(verifier, message)| {
                        slw::show_verifier_challenge_received_profile(
                            verifier,
                            message,
                            &mut challenge_rng,
                        )
                        .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let messages = values.iter().map(|(_, m)| m.clone()).collect();
                Ok(Output::with_messages(values, messages))
            },
        )?;
        let third_wires = f.take_messages()?;
        if let Some(original) = &original_third {
            need(
                original == &third_wires,
                "SLW shared-slot native VThird bytes changed across verifier profiles",
            )?;
        } else {
            original_third = Some(third_wires.clone());
        }
        if let Some(provers) = provers {
            f.record(
                Phase::new(
                    Role::Agent,
                    Stage::OnlineGeneration,
                    "complete_presentations_check_fresh_opening_and_respond",
                )
                .encoded()
                .decoded(),
                Some(k),
                || {
                    let messages = provers
                        .into_iter()
                        .zip(&third_wires)
                        .map(|(prover, third)| {
                            slw::show_holder_respond(prover, third).map_err(native_error)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    Ok(Output::with_messages((), messages))
                },
            )?;
            final_wires = Some(f.take_messages()?);
        }
        let finals = final_wires.as_ref().ok_or("SLW native PFinal absent")?;
        let final_fields = finals.iter().fold(WireFields::default(), |mut a, b| {
            a.add(slw_wire_fields(b));
            a
        });
        let mut weights = f.recorder.verification_rng(
            Scheme::Slw25,
            k,
            &format!("final-verification-weights/{profile}"),
        )?;
        f.received(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_native_final_random_profile",
            )
            .decoded(),
            Some(k),
            finals,
            final_fields,
            || {
                verifiers
                    .into_iter()
                    .zip(finals)
                    .map(|((state, _), bytes)| {
                        let final_message =
                            slw::decode_show_final_received(&state, bytes).map_err(native_error)?;
                        Ok((state, final_message))
                    })
                    .collect::<Result<Vec<_>>>()
            },
            |received| {
                need(
                    slw::show_verifier_finish_many_received_profile(received, mode, &mut weights)
                        .map_err(native_error)?,
                    "SLW native live final verification",
                )?;
                Ok(Output::value(()))
            },
        )?;
        let records = (0..k)
            .map(|i| SlwLiveRecord {
                messages: [
                    prefix_wires[i].clone(),
                    first_wires[i].clone(),
                    prover_messages[i].clone(),
                    third_wires[i].clone(),
                    finals[i].clone(),
                ],
            })
            .collect::<Vec<_>>();
        let adapter = SlwLiveAdapter {
            namespace: crate::batch_runtime::Adapter::namespace(&crate::adapters::Slw::new(pk))
                .to_vec(),
            issuer: pk.issuer_id(),
        };
        f.note_request(&adapter, &records, k)?;
        f.accept(
            adapter,
            &records,
            if profile == "Specification" {
                "Specification"
            } else {
                "Randomized"
            },
            if profile == "Specification" {
                crate::batch_runtime::Mode::Specification
            } else {
                crate::batch_runtime::Mode::Randomized
            },
            rng,
            Receipt::Live,
        )?;
    }
    Ok(())
}

// Native field order is retained. These bounded decoders authenticate every
// received group/scalar encoding; subsequent native proof checks are unchanged.
struct Raw<'a> {
    bytes: &'a [u8],
    offset: usize,
}
impl<'a> Raw<'a> {
    fn new(bytes: &'a [u8]) -> Result<Self> {
        need(bytes.len() <= 8 * 1024 * 1024, "native message too large")?;
        Ok(Self { bytes, offset: 0 })
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.offset.checked_add(n).ok_or("native length overflow")?;
        need(end <= self.bytes.len(), "truncated native message")?;
        let x = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(x)
    }
    fn len(&mut self) -> Result<usize> {
        usize::try_from(u64::from_be_bytes(self.take(8)?.try_into().unwrap())).map_err(native_error)
    }
    fn g1(&mut self) -> Result<baseline_core::arithmetic::G1> {
        baseline_core::canonical::decode_g1(self.take(48)?).map_err(native_error)
    }
    fn g2(&mut self) -> Result<baseline_core::arithmetic::G2> {
        baseline_core::canonical::decode_g2(self.take(96)?).map_err(native_error)
    }
    fn scalar(&mut self) -> Result<S> {
        baseline_core::canonical::decode_scalar(self.take(32)?).map_err(native_error)
    }
    fn proof(&mut self) -> Result<baseline_core::sma2rt_proof::Proof> {
        let n = self.len()?;
        let p = baseline_core::canonical::decode_proof(self.take(n)?).map_err(native_error)?;
        Ok(baseline_core::sma2rt_proof::Proof {
            c: p.c,
            z: p.z,
            orz: p.orz,
        })
    }
    fn finish(self) -> Result<()> {
        need(
            self.offset == self.bytes.len(),
            "trailing native message bytes",
        )
    }
}
#[cfg(test)]
fn sma_request(bytes: &[u8]) -> Result<sma::Request> {
    let mut r = Raw::new(bytes)?;
    let q = sma::Request {
        pk: r.g1()?,
        ca: r.g1()?,
        proof: r.proof()?,
    };
    r.finish()?;
    Ok(q)
}
#[cfg(test)]
fn sma_response(bytes: &[u8]) -> Result<sma::Credential> {
    let mut r = Raw::new(bytes)?;
    let c = sma::Credential {
        sig: sma::Signature {
            z: r.g1()?,
            y: r.g1()?,
            yhat: r.g2()?,
        },
        e: r.g1()?,
        ca: r.g1()?,
        cf: r.g1()?,
        zi: [r.scalar()?, r.scalar()?],
        encryption: r.proof()?,
    };
    r.finish()?;
    Ok(c)
}
fn cpat_request_bytes(q: &cpat::Request) -> Vec<u8> {
    let mut b = q.pkc.to_compressed().to_vec();
    b.extend(q.proof.c.to_bytes_be());
    b.extend(q.proof.z.to_bytes_be());
    b
}
#[cfg(test)]
fn cpat_request(bytes: &[u8]) -> Result<cpat::Request> {
    let mut r = Raw::new(bytes)?;
    let q = cpat::Request {
        pkc: r.g1()?,
        proof: cpat::DlProof {
            c: r.scalar()?,
            z: r.scalar()?,
        },
    };
    r.finish()?;
    Ok(q)
}
fn cpat_response_bytes(c: &cpat::Response) -> Vec<u8> {
    let mut b = vec![];
    for p in [c.r, c.pkc, c.x, c.sig.z, c.sig.y] {
        b.extend(p.to_compressed());
    }
    b.extend(c.sig.yh.to_compressed());
    for s in c.proof.c.into_iter().chain(c.proof.z) {
        b.extend(s.to_bytes_be());
    }
    b
}
#[cfg(test)]
fn cpat_response(bytes: &[u8]) -> Result<cpat::Response> {
    let mut r = Raw::new(bytes)?;
    let c = cpat::Response {
        r: r.g1()?,
        pkc: r.g1()?,
        x: r.g1()?,
        sig: cpat::Sig {
            z: r.g1()?,
            y: r.g1()?,
            yh: r.g2()?,
        },
        proof: cpat::OrProof {
            c: [r.scalar()?, r.scalar()?],
            z: [r.scalar()?, r.scalar()?],
        },
    };
    r.finish()?;
    Ok(c)
}

struct AcceptanceFixture {
    count: usize,
    ids: Vec<Vec<u8>>,
}
fn acceptance_fixture<A: crate::batch_runtime::Adapter>(
    a: &A,
    items: &[A::Item],
) -> Result<AcceptanceFixture> {
    Ok(AcceptanceFixture {
        count: items.len(),
        ids: a.identifiers(items)?,
    })
}
struct CheckedSma<'a> {
    base: crate::adapters::Sma<'a>,
    key: &'a sma::InstalledInstance,
    policy: &'a sma::Policy,
    context: &'a [u8],
}
fn checked_sma<'a>(
    key: &'a sma::InstalledInstance,
    policy: &'a sma::Policy,
    context: &'a [u8],
    raw: &[sma::Token],
) -> Result<(CheckedSma<'a>, AcceptanceFixture)> {
    let base = crate::adapters::Sma::new(key, policy, context);
    let fixture = acceptance_fixture(&base, raw)?;
    Ok((
        CheckedSma {
            base,
            key,
            policy,
            context,
        },
        fixture,
    ))
}
impl crate::batch_runtime::Adapter for CheckedSma<'_> {
    type Item = sma::CheckedToken;
    fn scheme(&self) -> &'static str {
        "SMA²RT"
    }
    fn namespace(&self) -> &[u8] {
        self.base.namespace()
    }
    fn verify<R: rand::RngCore + rand::CryptoRng>(
        &self,
        x: &[Self::Item],
        m: crate::batch_runtime::Mode,
        r: &mut R,
    ) -> bool {
        !x.is_empty()
            && if m == crate::batch_runtime::Mode::Specification {
                x.iter()
                    .all(|t| sma::verify_checked(self.key, t, self.context, self.policy))
            } else {
                sma::verify_random_batch_checked(self.key, x, self.context, self.policy, r)
            }
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>> {
        Ok(x.iter()
            .map(|t| t.as_token().serial.to_compressed().to_vec())
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.as_token().bytes()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}
struct CheckedNiat<'a> {
    base: crate::adapters::Niat<'a>,
    key: &'a niat::InstalledIssuer,
    variant: niat::RedemptionBatch,
}
fn checked_niat<'a>(
    key: &'a niat::InstalledIssuer,
    variant: niat::RedemptionBatch,
    raw: &[niat::Token],
) -> Result<(CheckedNiat<'a>, AcceptanceFixture)> {
    let base = crate::adapters::Niat::new(key, variant)?;
    let fixture = acceptance_fixture(&base, raw)?;
    Ok((CheckedNiat { base, key, variant }, fixture))
}
impl crate::batch_runtime::Adapter for CheckedNiat<'_> {
    type Item = niat::CheckedToken;
    fn scheme(&self) -> &'static str {
        "NIAT"
    }
    fn namespace(&self) -> &[u8] {
        self.base.namespace()
    }
    fn verify<R: rand::RngCore + rand::CryptoRng>(
        &self,
        x: &[Self::Item],
        m: crate::batch_runtime::Mode,
        r: &mut R,
    ) -> bool {
        !x.is_empty()
            && if m == crate::batch_runtime::Mode::Specification {
                x.iter()
                    .all(|t| niat::verify_token_checked(self.key, t).is_ok())
            } else {
                niat::verify_batch_redemption_checked(self.key, x, self.variant, r).is_ok()
            }
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>> {
        Ok(x.iter()
            .map(|t| niat::redemption_tag(t.as_token()).to_vec())
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.as_token().encode()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}
struct CheckedCpat<'a> {
    base: crate::adapters::Cpat<'a>,
    key: &'a cpat::ValidatedKey,
    policy: &'a cpat::Policy,
    metadata: &'a [u8],
    cached: Option<&'a cpat::InstalledMetadata>,
}
fn checked_cpat<'a>(
    key: &'a cpat::ValidatedKey,
    policy: &'a cpat::Policy,
    metadata: &'a [u8],
    cached: Option<&'a cpat::InstalledMetadata>,
    raw: &[cpat::Token],
) -> Result<(CheckedCpat<'a>, AcceptanceFixture)> {
    let base = crate::adapters::Cpat::four_coordinate(key, policy, metadata);
    let fixture = acceptance_fixture(&base, raw)?;
    Ok((
        CheckedCpat {
            base,
            key,
            policy,
            metadata,
            cached,
        },
        fixture,
    ))
}
impl crate::batch_runtime::Adapter for CheckedCpat<'_> {
    type Item = cpat::CheckedToken;
    fn scheme(&self) -> &'static str {
        "CPAT"
    }
    fn namespace(&self) -> &[u8] {
        self.base.namespace()
    }
    fn verify<R: rand::RngCore + rand::CryptoRng>(
        &self,
        x: &[Self::Item],
        m: crate::batch_runtime::Mode,
        r: &mut R,
    ) -> bool {
        !x.is_empty()
            && if m == crate::batch_runtime::Mode::Specification {
                x.iter()
                    .all(|t| cpat::verify_checked(self.key, self.policy, self.metadata, t))
            } else {
                match self.cached {
                    Some(c) => cpat::verify_random_batch_metadata_checked(c, self.policy, x, r),
                    None => cpat::verify_random_batch_checked(
                        self.key,
                        self.policy,
                        self.metadata,
                        x,
                        r,
                    ),
                }
            }
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>> {
        Ok(x.iter()
            .map(|t| {
                let t = t.as_token();
                let mut id = (t.tag.len() as u64).to_be_bytes().to_vec();
                id.extend(&t.tag);
                id.extend(t.delta.to_compressed());
                id
            })
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.as_token().encode()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}
struct CheckedHin<'a> {
    base: crate::adapters::Hin<'a>,
    key: &'a hin::InstalledIssuer,
    variant: hin::VerificationMode,
}
fn checked_hin<'a>(
    key: &'a hin::InstalledIssuer,
    variant: hin::VerificationMode,
    raw: &[hin::Token],
) -> Result<(CheckedHin<'a>, AcceptanceFixture)> {
    let base = crate::adapters::Hin::new(key, variant);
    let fixture = acceptance_fixture(&base, raw)?;
    Ok((CheckedHin { base, key, variant }, fixture))
}
impl crate::batch_runtime::Adapter for CheckedHin<'_> {
    type Item = hin::CheckedToken;
    fn scheme(&self) -> &'static str {
        "HinToken"
    }
    fn namespace(&self) -> &[u8] {
        self.base.namespace()
    }
    fn verify<R: rand::RngCore + rand::CryptoRng>(
        &self,
        x: &[Self::Item],
        m: crate::batch_runtime::Mode,
        r: &mut R,
    ) -> bool {
        hin::verify_batch_checked(
            self.key,
            x,
            if m == crate::batch_runtime::Mode::Specification {
                hin::VerificationMode::Specification
            } else {
                self.variant
            },
            r,
        )
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>> {
        Ok(x.iter().map(|t| t.as_token().message_id()).collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.as_token().encode()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

enum Receipt<'a, T> {
    Live,
    Bytes {
        wire: &'a [Vec<u8>],
        fields: WireFields,
        decode: Box<dyn FnOnce() -> Result<Vec<T>> + 'a>,
    },
}
impl<'a, T> Receipt<'a, T> {
    fn bytes(
        wire: &'a [Vec<u8>],
        fields: WireFields,
        decode: impl FnOnce() -> Result<Vec<T>> + 'a,
    ) -> Self {
        Self::Bytes {
            wire,
            fields,
            decode: Box::new(decode),
        }
    }
}
impl Native<'_, '_> {
    fn accept<A: crate::batch_runtime::Adapter>(
        &mut self,
        adapter: A,
        items: &[A::Item],
        profile: &'static str,
        mode: crate::batch_runtime::Mode,
        rng: &mut StdRng,
        receipt: Receipt<'_, A::Item>,
    ) -> Result<()>
    where
        A::Item: 'static,
    {
        self.accept_inner(adapter, items, profile, mode, rng, receipt, None)
    }
    fn accept_received<A: crate::batch_runtime::Adapter>(
        &mut self,
        ready: (A, AcceptanceFixture),
        profile: &'static str,
        mode: crate::batch_runtime::Mode,
        rng: &mut StdRng,
        receipt: Receipt<'_, A::Item>,
    ) -> Result<()>
    where
        A::Item: 'static,
    {
        self.accept_inner(ready.0, &[], profile, mode, rng, receipt, Some(ready.1))
    }
    #[allow(clippy::too_many_arguments)]
    fn accept_inner<A: crate::batch_runtime::Adapter>(
        &mut self,
        adapter: A,
        items: &[A::Item],
        profile: &'static str,
        mode: crate::batch_runtime::Mode,
        rng: &mut StdRng,
        mut receipt: Receipt<'_, A::Item>,
        fixture: Option<AcceptanceFixture>,
    ) -> Result<()>
    where
        A::Item: 'static,
    {
        let k = fixture.as_ref().map_or(items.len(), |f| f.count);
        if self.recorder.is_pipeline() {
            let retained;
            let accepted = if matches!(&receipt, Receipt::Bytes { .. }) {
                let key = self.recorder.received_key(self.scheme, Some(k), profile);
                retained = self
                    .recorder
                    .retained
                    .get(&key)
                    .cloned()
                    .ok_or("missing same-slot verified native input")?
                    .downcast::<Vec<A::Item>>()
                    .map_err(|_| "same-slot verified native input type")?;
                retained.as_slice()
            } else {
                items
            };
            need(!accepted.is_empty(), "empty pipeline native input")?;
            let operation = self.recorder.application_operation(k);
            let inclusive_phase = Phase::new(Role::Verifier, Stage::InclusiveVerification, profile);
            let inclusive_spec = self.recorder.spec(self.scheme, &inclusive_phase, Some(k));
            let matching = self.recorder.pipeline_matches(&inclusive_spec);
            let inclusive = matching.first();
            let native_spec = self.recorder.spec(
                self.scheme,
                &Phase::new(Role::Verifier, Stage::VerificationCrypto, profile),
                Some(k),
            );
            let native_matches = self.recorder.pipeline_matches(&native_spec);
            let source = inclusive.or(native_matches.first());
            if let Some(source) = source {
                let wire = accepted
                    .iter()
                    .flat_map(|item| adapter.wire_messages(item))
                    .collect::<Vec<_>>();
                self.recorder
                    .record_pipeline_observation(&source.job.id, &wire, k);
            }
            let state_phase = Phase::new(
                Role::Verifier,
                Stage::SharedState,
                "already_verified_complete_native_identifiers",
            );
            let state_spec = self.recorder.spec(self.scheme, &state_phase, Some(k));
            let state_targets = self.recorder.pipeline_matches(&state_spec);
            if inclusive.is_none() && state_targets.is_empty() {
                return Ok(());
            }
            let ids_fixture = adapter.identifiers(accepted)?;
            let namespace = crate::common::state::request_hash(adapter.namespace())
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>();
            let snapshot_key = format!(
                "pipeline-state-snapshot/{}/{k}/{namespace}",
                name(self.scheme)
            );
            let existing = self.recorder.cache.borrow().get(&snapshot_key).cloned();
            let snapshot = if let Some(existing) = existing {
                existing
                    .downcast::<crate::common::spent::SpentSnapshot>()
                    .map_err(|_| "state snapshot cache type")?
            } else {
                let initial = crate::common::spent::SpentStore::with_preexisting_records(
                    10000,
                    adapter.namespace(),
                    ids_fixture[0].len(),
                )
                .map_err(native_error)?;
                let snapshot = Rc::new(initial.snapshot().map_err(native_error)?);
                self.recorder
                    .cache
                    .borrow_mut()
                    .insert(snapshot_key, snapshot.clone());
                snapshot
            };
            let state = crate::common::spent::SpentStore::from_snapshot(&snapshot);
            if let Some(inclusive) = inclusive {
                let result = self.recorder.capture(inclusive, || {
                    let ids = adapter
                        .identifiers(accepted)?
                        .iter()
                        .map(|id| {
                            crate::common::spent::Identifier::new(adapter.namespace(), id)
                                .map_err(native_error)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let request =
                        crate::batch_runtime::bound_request(&adapter, accepted, &operation);
                    state
                        .record_checked(&request, &ids, b"accepted")
                        .map_err(native_error)
                })?;
                self.recorder.segments += 1;
                need(
                    result.newly_registered == ids_fixture.len() && !result.replayed,
                    "pipeline inclusive registration",
                )?;
                need(
                    state.counts().map_err(native_error)? == (10001, 10000 + ids_fixture.len()),
                    "pipeline inclusive state postcondition",
                )?;
            }
            if let Some(state_target) = state_targets.first() {
                if !self
                    .recorder
                    .clock
                    .as_ref()
                    .ok_or("pipeline clock missing")?
                    .observations()
                    .contains_key(&state_target.job.id)
                {
                    if let Some(inclusive) = inclusive {
                        self.recorder
                            .clock
                            .as_deref_mut()
                            .ok_or("pipeline clock missing")?
                            .capture_alias(
                                &state_target.job.id,
                                &inclusive.job.id,
                                "verification.state",
                            )?;
                    } else {
                        let ids = ids_fixture
                            .iter()
                            .map(|id| {
                                crate::common::spent::Identifier::new(adapter.namespace(), id)
                                    .map_err(native_error)
                            })
                            .collect::<Result<Vec<_>>>()?;
                        let request =
                            crate::batch_runtime::bound_request(&adapter, accepted, &operation);
                        let state = crate::common::spent::SpentStore::from_snapshot(&snapshot);
                        self.recorder.capture(state_target, || {
                            state
                                .record_checked(&request, &ids, b"accepted")
                                .map_err(native_error)
                        })?;
                        self.recorder.segments += 1;
                    }
                    let metadata = self
                        .recorder
                        .pipeline_observations
                        .entry(state_target.job.id.clone())
                        .or_insert_with(|| json!({}));
                    metadata["shared_state_scope"] = json!("record_checked_only");
                    metadata["restored_snapshot"] = json!(true);
                    metadata["same_call_as_inclusive"] = json!(inclusive.is_some());
                }
            }
            return Ok(());
        }
        let live_checked = matches!(&receipt, Receipt::Live);
        for stage in [Stage::InclusiveVerification, Stage::SharedState] {
            if stage == Stage::SharedState
                && profile != "native_sequential_specification"
                && !matches!(self.scheme, Scheme::Msb23 | Scheme::Slw25)
            {
                continue;
            }
            let phase = Phase::new(
                Role::Verifier,
                stage,
                if stage == Stage::SharedState {
                    "already_verified_complete_native_identifiers"
                } else {
                    profile
                },
            );
            let mut spec = self.recorder.spec(self.scheme, &phase, Some(k));
            spec.job.boundary["shared_state_included"] = json!(true);
            spec.job.boundary["wire_encoding_included"] =
                json!(stage == Stage::InclusiveVerification);
            spec.job.boundary["inclusive_total"] = json!(stage == Stage::InclusiveVerification);
            spec.job.workload["history_records"] = json!(10000);
            if stage == Stage::SharedState {
                spec.job.boundary["state_scope"] = json!("record_checked_only");
                spec.job.boundary["ids_and_full_request_prebuilt"] = json!(true);
            }
            let selected = self.recorder.selected(&spec);
            self.recorder.remember(spec, &phase);
            if !selected {
                continue;
            }
            if self.recorder.decode_only() {
                if let Receipt::Bytes {
                    wire,
                    fields,
                    decode,
                } = std::mem::replace(&mut receipt, Receipt::Live)
                {
                    let decoded = self
                        .recorder
                        .clock
                        .as_deref_mut()
                        .ok_or("decode clock missing")?
                        .measure(decode)?;
                    self.recorder.segments += 1;
                    self.recorder
                        .decoded_observation(fields, wire, phase.profile);
                    std::hint::black_box(decoded);
                    return Err(DONE.into());
                }
                // Live verifier receipt decoders were measured at their causal legs.
                return Ok(());
            }
            let computed_ids;
            let fixture_ids = if let Some(fixture) = &fixture {
                &fixture.ids
            } else {
                computed_ids = adapter.identifiers(items)?;
                &computed_ids
            };
            need(!fixture_ids.is_empty(), "empty acceptance fixture")?;
            let state = crate::common::spent::SpentStore::with_preexisting_records(
                10000,
                adapter.namespace(),
                fixture_ids[0].len(),
            )
            .map_err(native_error)?;
            let result = if stage == Stage::InclusiveVerification {
                if let Receipt::Bytes {
                    wire,
                    fields,
                    decode,
                } = std::mem::replace(&mut receipt, Receipt::Live)
                {
                    let result = self
                        .recorder
                        .clock
                        .as_deref_mut()
                        .ok_or("acceptance clock missing")?
                        .measure(|| {
                            let decoded = decode()?;
                            let result = crate::batch_runtime::verify_and_record(
                                &adapter,
                                &decoded,
                                b"baseline-native-operation",
                                b"accepted",
                                &state,
                                mode,
                                rng,
                            )
                            .map_err(native_error)?;
                            Ok(result)
                        })?;
                    self.recorder
                        .decoded_observation(fields, wire, phase.profile);
                    result
                } else {
                    self.recorder
                        .clock
                        .as_deref_mut()
                        .ok_or("live acceptance clock missing")?
                        .measure(|| {
                            let ids = adapter
                                .identifiers(items)?
                                .iter()
                                .map(|v| {
                                    crate::common::spent::Identifier::new(adapter.namespace(), v)
                                        .map_err(native_error)
                                })
                                .collect::<Result<Vec<_>>>()?;
                            let request = crate::batch_runtime::bound_request(
                                &adapter,
                                items,
                                b"baseline-native-operation",
                            );
                            state
                                .record_checked(&request, &ids, b"accepted")
                                .map_err(native_error)
                        })?
                }
            } else {
                let decoded = if let Receipt::Bytes { decode, .. } =
                    std::mem::replace(&mut receipt, Receipt::Live)
                {
                    Some(decode()?)
                } else {
                    None
                };
                let accepted_items = decoded.as_deref().unwrap_or(items);
                if !live_checked {
                    need(
                        adapter.verify(accepted_items, mode, rng),
                        "state fixture native verification",
                    )?;
                }
                let ids = adapter
                    .identifiers(accepted_items)?
                    .iter()
                    .map(|v| {
                        crate::common::spent::Identifier::new(adapter.namespace(), v)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let request = crate::batch_runtime::bound_request(
                    &adapter,
                    accepted_items,
                    b"baseline-native-operation",
                );
                self.recorder
                    .clock
                    .as_deref_mut()
                    .ok_or("state clock missing")?
                    .measure(|| {
                        state
                            .record_checked(&request, &ids, b"accepted")
                            .map_err(native_error)
                    })?
            };
            self.recorder.segments += 1;
            self.recorder.completed_profiles.push(
                if stage == Stage::SharedState {
                    "shared_state_complete_ids"
                } else {
                    "inclusive_native_acceptance"
                }
                .into(),
            );
            need(
                result.newly_registered == fixture_ids.len() && !result.replayed,
                "native acceptance count",
            )?;
            need(
                state.counts().map_err(native_error)? == (10001, 10000 + fixture_ids.len()),
                "native shared state postcondition",
            )?;
            return Err(DONE.into());
        }
        Ok(())
    }
}
struct SlwLiveRecord {
    messages: [Vec<u8>; 5],
}
struct SlwLiveAdapter {
    namespace: Vec<u8>,
    issuer: [u8; 32],
}
impl crate::batch_runtime::Adapter for SlwLiveAdapter {
    type Item = SlwLiveRecord;
    fn scheme(&self) -> &'static str {
        "SLW+25"
    }
    fn namespace(&self) -> &[u8] {
        &self.namespace
    }
    // This private capability is used only after the same live verifier passed;
    // no standalone adapter acceptance can bypass native cryptography.
    fn verify<R: rand::RngCore + rand::CryptoRng>(
        &self,
        _: &[Self::Item],
        _: crate::batch_runtime::Mode,
        _: &mut R,
    ) -> bool {
        false
    }
    fn identifiers(&self, items: &[Self::Item]) -> Result<Vec<Vec<u8>>> {
        use sha2::Digest;
        Ok(items
            .iter()
            .map(|item| {
                let mut w = baseline_core::encoding::Writer::new(b"SLW-frozen-live-session-v1");
                w.bytes(&self.issuer);
                for message in &item.messages {
                    w.bytes(message);
                }
                sha2::Sha256::digest(w.finish()).to_vec()
            })
            .collect())
    }
    fn wire_messages(&self, item: &Self::Item) -> Vec<Vec<u8>> {
        item.messages.to_vec()
    }
    fn public_identifiers(&self, item: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(item)).ok()
    }
}

struct SmaProvisionPublic {
    pp: sma::Params,
    issuer: sma::Issuer,
    reader: sma::MetadataKey,
    installed: sma::InstalledInstance,
    agents: Vec<sma::InstalledInstance>,
    public_wire: Vec<u8>,
}
fn sma_provision_public(agents: usize, cache: &Cache) -> Result<Rc<SmaProvisionPublic>> {
    let cache_key = format!("SMA/equal-budget/public/{agents}");
    let existing = cache.borrow().get(&cache_key).cloned();
    if let Some(value) = existing {
        return value
            .downcast::<SmaProvisionPublic>()
            .map_err(|_| "provisioning public cache type".into());
    }
    let mut rng = StdRng::seed_from_u64(230_930_000 + agents as u64);
    let pp = sma::setup(10, (1024 / agents) as u64);
    let issuer = sma::ikeygen(&pp, &mut rng);
    let reader = sma::vkeygen(&pp, &mut rng);
    let public_wire = sma_public_bytes(&pp, &issuer, &reader);
    let install = || {
        let (p, i, r) = sma_public(&public_wire)?;
        sma::install_instance(&p, &i, &r).map_err(native_error)
    };
    let installed = install()?;
    let actors = (0..agents).map(|_| install()).collect::<Result<Vec<_>>>()?;
    let public = Rc::new(SmaProvisionPublic {
        pp,
        issuer,
        reader,
        installed,
        agents: actors,
        public_wire,
    });
    cache.borrow_mut().insert(cache_key, public.clone());
    Ok(public)
}
fn sma_provision_pipeline(targets: Vec<Spec>, trial: u64, cache: Cache) -> Result<Action> {
    let agents = targets[0].job.workload["agents"]
        .as_u64()
        .ok_or("provisioning agents")? as usize;
    need(
        targets
            .iter()
            .all(|s| s.job.workload["agents"] == json!(agents)),
        "provisioning pipeline mixes agent counts",
    )?;
    Ok(Box::new(move |clock| {
        let public = sma_provision_public(agents, &cache)?;
        let mut rng = StdRng::seed_from_u64(
            230_933_000u64
                .wrapping_add(trial.wrapping_mul(1_000_003))
                .wrapping_add(agents as u64),
        );
        let issuer_target = targets
            .iter()
            .find(|s| s.stage == Stage::ProvisioningIssuer);
        let system_target = targets
            .iter()
            .find(|s| s.stage == Stage::ProvisioningSystem);
        let mut issuer_view = None;
        let mut agent_views = None;
        for target in targets.iter().filter(|s| s.stage == Stage::Install) {
            let calls = if target.role == Role::Issuer {
                1
            } else {
                agents
            };
            let installed = clock.capture(&target.job.id, |clock| {
                clock.measure(|| {
                    (0..calls)
                        .map(|_| {
                            let (p, i, r) = sma_public(&public.public_wire)?;
                            sma::install_instance(&p, &i, &r).map_err(native_error)
                        })
                        .collect::<Result<Vec<_>>>()
                })
            })?;
            if target.role == Role::Issuer {
                issuer_view = installed.into_iter().next();
            } else {
                agent_views = Some(installed);
            }
        }
        let installed = issuer_view.as_ref().unwrap_or(&public.installed);
        let actors = agent_views.as_deref().unwrap_or(&public.agents);
        let key_name = format!("SMA/equal-budget/holder-keys/{agents}");
        let existing = cache.borrow().get(&key_name).cloned();
        let keys = if let Some(existing) = existing {
            existing
                .downcast::<Vec<sma::UserKey>>()
                .map_err(|_| "provisioning holder keys type")?
        } else {
            let keys = Rc::new(
                (0..agents)
                    .map(|_| sma::ukeygen(&mut rng))
                    .collect::<Vec<_>>(),
            );
            cache.borrow_mut().insert(key_name, keys.clone());
            keys
        };
        let attrs = (0..10)
            .map(|i| if i == 0 { S::ONE } else { S::from(20 + i) })
            .collect::<Vec<_>>();
        let policy = sma::Policy {
            atoms: (0..3).map(|i| sma::Atom::Reveal(i, attrs[i])).collect(),
        };
        let mut receive_weights = weight_rng_for_mode(
            clock.mode(),
            StdRng::seed_from_u64(230_933_989u64.wrapping_add(trial)),
        )?;
        let mut messages = vec![];
        for (actor, key) in actors.iter().zip(keys.iter()) {
            let mut request = || {
                let (pending, request) =
                    sma::request_installed(actor, key, &attrs, &policy, &mut rng)
                        .map_err(native_error)?;
                Ok((pending, request.bytes()))
            };
            let (pending, request) = if let Some(system) = system_target {
                clock.capture(&system.job.id, |clock| clock.measure(request))?
            } else {
                request()?
            };
            let mut respond = || {
                let _issuer = crate::darlt::instrumentation::span("provision.issuer");
                let received = sma::ReceivedRequest::decode(&request).map_err(native_error)?;
                let response = sma::respond_received_installed(
                    installed,
                    &public.issuer,
                    &public.reader,
                    received,
                    &policy,
                    1,
                    &mut rng,
                )
                .map_err(native_error)?;
                Ok(response.bytes())
            };
            let response = if let Some(system) = system_target {
                clock.capture(&system.job.id, |clock| clock.measure(respond))?
            } else if let Some(issuer) = issuer_target {
                clock.capture(&issuer.job.id, |clock| clock.measure(respond))?
            } else {
                respond()?
            };
            let receive = || {
                sma::receive_received_set(
                    actor,
                    pending,
                    sma::ReceivedCredential::decode(&response).map_err(native_error)?,
                    &mut receive_weights,
                )
                .map_err(native_error)
            };
            let wallet = if let Some(system) = system_target {
                clock.capture(&system.job.id, |clock| clock.measure(receive))?
            } else {
                receive()?
            };
            std::hint::black_box(wallet);
            messages.push(request);
            messages.push(response);
        }
        if let (Some(issuer), Some(system)) = (issuer_target, system_target) {
            clock.capture_alias(&issuer.job.id, &system.job.id, "provision.issuer")?;
        }
        need(
            actors.len() * public.pp.n as usize == 1024,
            "provisioning pipeline equal quota",
        )?;
        let mut complete = b"SMA/equal-total-budget/native-configuration".to_vec();
        complete.extend(trial.to_be_bytes());
        complete.extend((agents as u64).to_be_bytes());
        for message in &messages {
            framed(&mut complete, message);
        }
        let hash = crate::common::state::request_hash(&complete)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        let metadata = json!({"complete_application_request_sha256":hash,"complete_application_request_bytes":complete.len(),
            "actual_configuration_message_bytes":messages.iter().map(Vec::len).sum::<usize>(),"actual_native_message_sizes":messages.iter().map(Vec::len).collect::<Vec<_>>(),
            "agents":agents,"actual_issuer_calls":agents,"actual_accepted_wallets":agents,"quota_each":1024/agents,"total_quota":1024,
            "issuer_and_system_same_actual_flows":true,"amortization_divisor":agents});
        let observations = targets
            .iter()
            .map(|s| (s.job.id.clone(), metadata.clone()))
            .collect::<BTreeMap<_, _>>();
        Ok(
            json!({"correctness":"PASS","pipeline":true,"sample_slot":trial,"inputpool_alive_slots":1,
            "actual_stage_outputs_forwarded":true,"observations":observations}),
        )
    }))
}

fn sma_provision_install_action(agents: usize, issuer: bool, cache: Cache) -> Action {
    Box::new(move |clock| {
        let public = sma_provision_public(agents, &cache)?;
        let calls = if issuer { 1 } else { agents };
        let installed = clock.measure(|| {
            (0..calls)
                .map(|_| {
                    let (p, i, r) = sma_public(&public.public_wire)?;
                    sma::install_instance(&p, &i, &r).map_err(native_error)
                })
                .collect::<Result<Vec<_>>>()
        })?;
        need(installed.len() == calls, "actor cold installation count")?;
        std::hint::black_box(installed);
        Ok(
            json!({"correctness":"PASS","agents":agents,"actual_install_calls":calls,"public_package_bytes_each":public.public_wire.len(),"role":if issuer{"issuer"}else{"agent"},"native_counter_bound_per_agent":public.pp.n,"setup_and_keygen_included":false,"decode_key_proofs_and_fixed_cache_included":true}),
        )
    })
}
fn sma_provision_action(agents: usize, issuer_only: bool, trial: u64, cache: Cache) -> Action {
    Box::new(move |clock| {
        let public = sma_provision_public(agents, &cache)?;
        let mut rng = StdRng::seed_from_u64(230_931_000 + trial.wrapping_mul(1009) + agents as u64);
        let attrs = (0..10)
            .map(|i| if i == 0 { S::ONE } else { S::from(20 + i) })
            .collect::<Vec<_>>();
        let policy = sma::Policy {
            atoms: (0..3).map(|i| sma::Atom::Reveal(i, attrs[i])).collect(),
        };
        let keys = (0..agents)
            .map(|_| sma::ukeygen(&mut rng))
            .collect::<Vec<_>>();
        let mut receive_weights = weight_rng_for_mode(
            clock.mode(),
            StdRng::seed_from_u64(230_931_989u64.wrapping_add(trial)),
        )?;
        let mut message_bytes = 0usize;
        let mut accepted = 0usize;
        for (agent, key) in public.agents.iter().zip(&keys) {
            let mut request = || {
                let (pending, request) =
                    sma::request_installed(agent, key, &attrs, &policy, &mut rng)
                        .map_err(native_error)?;
                let bytes = request.bytes();
                Ok((pending, bytes))
            };
            let (pending, request) = if issuer_only {
                request()?
            } else {
                clock.measure(request)?
            };
            message_bytes += request.len();
            let (response, response_bytes) = clock.measure(|| {
                let request = sma::ReceivedRequest::decode(&request).map_err(native_error)?;
                let response = sma::respond_received_installed(
                    &public.installed,
                    &public.issuer,
                    &public.reader,
                    request,
                    &policy,
                    1,
                    &mut rng,
                )
                .map_err(native_error)?;
                let bytes = response.bytes();
                Ok((response, bytes))
            })?;
            message_bytes += response_bytes.len();
            let receive = || {
                sma::receive_received_set(
                    agent,
                    pending,
                    sma::ReceivedCredential::decode(&response_bytes).map_err(native_error)?,
                    &mut receive_weights,
                )
                .map_err(native_error)
            };
            let wallet = if issuer_only {
                receive()?
            } else {
                clock.measure(receive)?
            };
            std::hint::black_box(wallet);
            std::hint::black_box(response);
            accepted += 1;
        }
        need(
            public.pp.n as usize * accepted == 1024,
            "actual provisioning total quota",
        )?;
        Ok(
            json!({"correctness":"PASS","agents":agents,"actual_issuer_calls":agents,"actual_accepted_wallets":accepted,
            "native_counter_bound_per_agent":public.pp.n,"actual_agent_quotas":vec![1024/agents;agents],"total_quota":1024,
            "actual_configuration_message_bytes":message_bytes,"amortization_divisor":agents,"account":if issuer_only{"issuer"}else{"system"},
            "setup_keygen_and_installation_included":false,"actual_independently_installed_agent_views":public.agents.len(),"public_package_bytes_each":public.public_wire.len(),"request_response_encode_and_strict_receive_decode":true,
            "native_execution":"A independent request/response/accept flows; never one measured issuance multiplied by A"}),
        )
    })
}

fn framed(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend((bytes.len() as u64).to_be_bytes());
    out.extend(bytes);
}
fn sma_public_bytes(pp: &sma::Params, issuer: &sma::Issuer, reader: &sma::MetadataKey) -> Vec<u8> {
    let mut b = vec![];
    framed(&mut b, &pp.bytes());
    for p in issuer.vk {
        b.extend(p.to_compressed());
    }
    b.extend(issuer.proof.c.to_bytes_be());
    b.extend((issuer.proof.z.len() as u64).to_be_bytes());
    for s in &issuer.proof.z {
        b.extend(s.to_bytes_be());
    }
    for p in reader.pk {
        b.extend(p.to_compressed());
    }
    framed(&mut b, &reader.proof.bytes());
    b
}
fn sma_public(bytes: &[u8]) -> Result<(sma::Params, sma::Issuer, sma::MetadataKey)> {
    let mut r = Raw::new(bytes)?;
    let n = r.len()?;
    let mut p = Raw::new(r.take(n)?)?;
    let tag = b"SMA2RT-profile-2/BLS12-381/v2";
    need(p.take(tag.len())? == tag, "wrong SMA public version")?;
    let k = p.len()?;
    need((1..=1024).contains(&k), "SMA business dimension")?;
    let n = p.len()? as u64;
    let anchor = p.g1()?;
    let u = p.g1()?;
    let h = p.g1()?;
    let bit_h = p.g1()?;
    let m = p.len()?;
    need(m == k + 3, "SMA public bases shape")?;
    let y = (0..m).map(|_| p.g1()).collect::<Result<Vec<_>>>()?;
    p.finish()?;
    let vk = [r.g2()?, r.g2()?, r.g2()?, r.g2()?];
    let c = r.scalar()?;
    let m = r.len()?;
    need(m == 4, "SMA key proof shape")?;
    let z = (0..m).map(|_| r.scalar()).collect::<Result<Vec<_>>>()?;
    let pk = [r.g1()?, r.g1()?];
    let proof = r.proof()?;
    r.finish()?;
    Ok((
        sma::Params {
            k,
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
fn cpat_public_bytes(pk: &cpat::PublicKey) -> Vec<u8> {
    let mut b = vec![];
    for p in pk.vk {
        b.extend(p.to_compressed());
    }
    for p in pk.bit {
        b.extend(p.to_compressed());
    }
    b.extend(pk.proof.c.to_bytes_be());
    for s in pk.proof.z {
        b.extend(s.to_bytes_be());
    }
    b
}
fn cpat_public(bytes: &[u8]) -> Result<cpat::PublicKey> {
    let mut r = Raw::new(bytes)?;
    let p = cpat::PublicKey {
        vk: [r.g2()?, r.g2()?, r.g2()?, r.g2()?],
        bit: [r.g1()?, r.g1()?],
        proof: cpat::KeyProof {
            c: r.scalar()?,
            z: [r.scalar()?, r.scalar()?, r.scalar()?, r.scalar()?],
        },
    };
    r.finish()?;
    Ok(p)
}
fn hin_public(bytes: &[u8]) -> Result<hin::IssuerPublic> {
    let mut r = Raw::new(bytes)?;
    let p = hin::IssuerPublic {
        points: [r.g2()?, r.g2()?, r.g2()?, r.g2()?],
    };
    r.finish()?;
    Ok(p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::experiment::RunMode;
    #[test]
    fn all_six_native_roles_k1_are_repeatable_and_clock_free() -> Result<()> {
        let mut factory = Factory::new()?;
        let jobs = factory.jobs();
        let schemes = jobs
            .iter()
            .map(|j| j.scheme.as_str())
            .collect::<BTreeSet<_>>();
        need(schemes.len() == 6, "six-scheme job coverage")?;
        let reference = jobs
            .iter()
            .filter(|j| j.boundary["safe"] == false)
            .collect::<Vec<_>>();
        need(
            reference.len() == KS.len()
                && reference.iter().all(|j| {
                    j.scheme == "NIAT"
                        && j.stage == "verification_crypto"
                        && j.boundary["reference_only"] == true
                }),
            "unsafe reference isolation",
        )?;
        let input_shapes = jobs
            .iter()
            .filter(|j| j.stage == "verification_crypto")
            .map(|j| (j.scheme.clone(), j.workload["k"].as_u64()))
            .collect::<BTreeSet<_>>();
        let decoders = jobs
            .iter()
            .filter(|j| j.stage == "strict_decoding")
            .collect::<Vec<_>>();
        need(
            decoders.len() == input_shapes.len(),
            "one independently scheduled input-only decoder per native wire shape",
        )?;
        for job in jobs.iter().filter(|j| {
            matches!(
                j.stage.as_str(),
                "verification_crypto" | "inclusive_verification" | "strict_decoding"
            )
        }) {
            for key in [
                "strict_decoding_included",
                "received_bytes_first",
                "subgroup_checks_included",
                "native_format_checks_included",
            ] {
                need(
                    job.boundary[key] == true,
                    "missing received verifier boundary",
                )?;
            }
            if job.stage == "strict_decoding" {
                need(
                    job.boundary["decode_only"] == true
                        && job.boundary["shared_state_included"] == false
                        && job.boundary["parent_verification_stage"].is_string(),
                    "decoder-only boundary contains native algebra or state",
                )?;
            }
        }
        for profile in ["NativeTotal", "Prepared"] {
            for stage in ["issue_response", "issue_accept"] {
                need(
                    jobs.iter()
                        .filter(|j| j.scheme == "NIAT" && j.stage == stage && j.profile == profile)
                        .count()
                        == KS.len(),
                    "NIAT native/prepared issuance coverage",
                )?;
            }
        }

        for job in jobs.iter().filter(|j| {
            !j.stage.starts_with("provisioning_") && j.workload["k"].as_u64().is_none_or(|k| k == 1)
        }) {
            let action = factory.prepare(&job.id, 1)?;
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
            let (out, audit) =
                baseline_core::subgroup_audit::collect_selected(|| action(&mut clock));
            let out = out.map_err(|e| format!("{}: {e}", job.id))?;
            need(out["correctness"] == "PASS", &job.id)?;
            if audit.enabled && job.boundary["subgroup_checks_per_received_element"] == 1 {
                let expected = &out["actual_received_fields"];
                for kind in ["G1", "G2", "GT"] {
                    need(
                        audit.events.iter().filter(|e| e.kind == kind).count() as u64
                            == expected[kind]
                                .as_u64()
                                .ok_or("missing received slot count")?,
                        &format!(
                            "{} duplicate or missing {kind} subgroup check: {:?}",
                            job.id, audit.events
                        ),
                    )?;
                }
                need(
                    audit.events.iter().all(|e| e.operation == "checked_decode"),
                    &format!("{} rechecked a decoded/derived group value", job.id),
                )?;
            }
            need(
                !clock.segments().is_empty() && clock.segments().iter().all(Option::is_none),
                "clockfree segment timing",
            )?;
            if job.stage == "inclusive_verification" {
                need(
                    out["shared_state_included"] == true,
                    "inclusive missing shared state",
                )?;
            }
        }
        need(
            baseline_core::encoding::snapshot_counts().is_none(),
            "worker enabled operation counters",
        )?;
        Ok(())
    }
    #[test]
    fn complete_interactive_sessions_and_state_are_separate_native_segments() -> Result<()> {
        let mut factory = Factory::new()?;
        for scheme in ["MSB+23", "SLW+25"] {
            for stage in [
                "online_generation",
                "verification_crypto",
                "inclusive_verification",
                "shared_state",
            ] {
                let job = factory
                    .jobs()
                    .into_iter()
                    .find(|j| {
                        j.scheme == scheme
                            && j.stage == stage
                            && j.workload["k"] == 16
                            && j.profile != "Specification"
                    })
                    .ok_or("missing interactive job")?;
                let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
                let out = factory.prepare(&job.id, 2)?(&mut clock)
                    .map_err(|e| format!("{}: {e}", job.id))?;
                need(
                    out["correctness"] == "PASS",
                    "interactive native stage failed",
                )?;
                if stage == "verification_crypto" || stage == "inclusive_verification" {
                    need(clock.segments().len() >= 2, "live verifier pieces omitted")?;
                }
            }
        }
        Ok(())
    }
    #[test]
    fn attributes_change_real_fixtures_without_inventing_dimensions() -> Result<()> {
        for a in [5, 15, 20, 25, 30] {
            let mut factory = Factory::for_attributes(a)?;
            for job in factory.jobs() {
                need(
                    job.workload["attributes"] == a && job.workload["k"] == 16,
                    "attribute scan workload",
                )?;
                need(
                    ["SMA²RT", "MSB+23", "SLW+25"].contains(&job.scheme.as_str()),
                    "invented baseline attribute dimension",
                )?;
                if job.scheme == "MSB+23" {
                    need(
                        job.workload["actual_business_attributes"] == a
                            && job.workload["native_capacity_parameter"] == a
                            && job.workload["period_coordinate_count"] == 1,
                        "MSB business dimension and extra period",
                    )?;
                }
                if job.stage == "online_generation" {
                    let mut c = BoundaryClock::new(RunMode::ClockFree, None)?;
                    factory.prepare(&job.id, 3)?(&mut c)?;
                }
            }
        }
        Ok(())
    }
    #[test]
    fn sma_real_equal_total_budget_two_accounts() -> Result<()> {
        let mut factory = Factory::new()?;
        for agents in [1, 2, 4, 8, 16, 32, 64] {
            for stage in ["provisioning_issuer", "provisioning_system"] {
                let job = factory
                    .jobs()
                    .into_iter()
                    .find(|j| j.stage == stage && j.workload["agents"] == agents)
                    .ok_or("missing provisioning account")?;
                let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
                let out = factory.prepare(&job.id, 4)?(&mut clock)?;
                need(
                    out["actual_issuer_calls"] == agents
                        && out["actual_agent_quotas"] == json!(vec![1024 / agents; agents]),
                    "provisioning actual quotas",
                )?;
                need(
                    clock.segments().len()
                        == agents * if stage == "provisioning_issuer" { 1 } else { 3 },
                    "provisioning role segments",
                )?;
            }
        }
        Ok(())
    }
    #[test]
    fn issuance_codecs_preserve_native_bytes_and_reject_truncation_and_tail() -> Result<()> {
        let mut rng = StdRng::seed_from_u64(230_333);
        let issuer = cpat::keygen(&mut rng);
        let key = cpat::validate_key(&issuer.pk).map_err(native_error)?;
        let pb = cpat_public_bytes(&issuer.pk);
        need(
            cpat_public_bytes(&cpat_public(&pb)?) == pb,
            "CPAT public package roundtrip",
        )?;
        let mut tail = pb.clone();
        tail.push(0);
        need(
            cpat_public(&tail).is_err() && cpat_public(&pb[..pb.len() - 1]).is_err(),
            "CPAT public bounds",
        )?;

        let (request, pending) = cpat::request(&key, b"metadata", &mut rng);
        let rb = cpat_request_bytes(&request);
        need(
            rb.len() == request.payload_bytes(),
            "CPAT actual request bytes",
        )?;
        let q = cpat_request(&rb)?;
        need(cpat_request_bytes(&q) == rb, "request byte roundtrip")?;
        let response = cpat::issue_installed(&key, &issuer, &q, b"metadata", 1, &mut rng)
            .map_err(native_error)?;
        let rb = cpat_response_bytes(&response);
        need(
            rb.len() == response.payload_bytes(),
            "CPAT actual response bytes",
        )?;
        let r = cpat_response(&rb)?;
        need(cpat_response_bytes(&r) == rb, "response byte roundtrip")?;
        cpat::receive(pending, &r).map_err(native_error)?;
        need(
            cpat_response(&rb[..rb.len() - 1]).is_err(),
            "truncated response accepted",
        )?;
        let mut tail = rb;
        tail.push(0);
        need(cpat_response(&tail).is_err(), "tail accepted")?;
        let pp = sma::setup(10, 1024);
        let issuer = sma::ikeygen(&pp, &mut rng);
        let reader = sma::vkeygen(&pp, &mut rng);
        let installed = sma::install_instance(&pp, &issuer, &reader).map_err(native_error)?;
        let pb = sma_public_bytes(&pp, &issuer, &reader);
        let (dp, di, dr) = sma_public(&pb)?;
        need(
            sma_public_bytes(&dp, &di, &dr) == pb,
            "SMA public package roundtrip",
        )?;
        let mut tail = pb.clone();
        tail.push(0);
        need(
            sma_public(&tail).is_err() && sma_public(&pb[..pb.len() - 1]).is_err(),
            "SMA public bounds",
        )?;

        let user = sma::ukeygen(&mut rng);
        let attrs = (0..10).map(|i| S::from(i + 1)).collect::<Vec<_>>();
        let policy = sma::Policy::default();
        let (pending, q) = sma::request_installed(&installed, &user, &attrs, &policy, &mut rng)
            .map_err(native_error)?;
        let qb = q.bytes();
        need(sma_request(&qb)?.bytes() == qb, "SMA request roundtrip")?;
        let c = sma::respond_installed(
            &installed,
            &issuer,
            &reader,
            &sma_request(&qb)?,
            &policy,
            1,
            &mut rng,
        )
        .map_err(native_error)?;
        let cb = c.bytes();
        need(sma_response(&cb)?.bytes() == cb, "SMA response roundtrip")?;
        sma::receive_installed(&installed, pending, &sma_response(&cb)?).map_err(native_error)?;
        let mut tail = cb.clone();
        tail.push(0);
        need(
            sma_response(&tail).is_err() && sma_response(&cb[..cb.len() - 1]).is_err(),
            "SMA response bounds",
        )?;
        Ok(())
    }
    fn no_native_algebra(action: impl FnOnce() -> Result<()>) -> Result<()> {
        baseline_core::encoding::start_counts();
        let result = action();
        let counts = baseline_core::encoding::stop_counts();
        result?;
        need(
            counts.p == 0
                && counts.mp_calls == 0
                && counts.mp_terms == 0
                && counts.e1 == 0
                && counts.e2 == 0
                && counts.et == 0
                && counts.msm_sizes.is_empty()
                && counts.msm2_sizes.is_empty()
                && counts.h1 == 0
                && counts.hz == 0,
            "input-only helper ran native verification algebra",
        )
    }
    fn offcurve_g1() -> [u8; 48] {
        // Small canonical x, compression flag set, infinity/sign flags clear.
        // Rejection by the unchecked subgroup decoder therefore has no curve root.
        (1u64..10000)
            .find_map(|x| {
                let mut bytes = [0; 48];
                bytes[0] = 0x80;
                bytes[40..].copy_from_slice(&x.to_be_bytes());
                bool::from(blstrs::G1Affine::from_compressed_unchecked(&bytes).is_none())
                    .then_some(bytes)
            })
            .unwrap()
    }
    fn offcurve_g2() -> [u8; 96] {
        (1u64..10000)
            .find_map(|x| {
                let mut bytes = [0; 96];
                bytes[0] = 0x80;
                bytes[88..].copy_from_slice(&x.to_be_bytes());
                bool::from(blstrs::G2Affine::from_compressed_unchecked(&bytes).is_none())
                    .then_some(bytes)
            })
            .unwrap()
    }
    fn subgroup_bad_g1() -> [u8; 48] {
        (1u64..10000)
            .find_map(|x| {
                let mut bytes = [0; 48];
                bytes[0] = 0x80;
                bytes[40..].copy_from_slice(&x.to_be_bytes());
                Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed_unchecked(
                    &bytes,
                ))
                .filter(|p| !bool::from(p.is_torsion_free()))
                .map(|_| bytes)
            })
            .unwrap()
    }
    fn subgroup_bad_g2() -> [u8; 96] {
        (1u64..10000)
            .find_map(|x| {
                let mut bytes = [0; 96];
                bytes[0] = 0x80;
                bytes[88..].copy_from_slice(&x.to_be_bytes());
                Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed_unchecked(
                    &bytes,
                ))
                .filter(|p| !bool::from(p.is_torsion_free()))
                .map(|_| bytes)
            })
            .unwrap()
    }
    fn check_wire_domains(
        bytes: &[u8],
        g1: &[(usize, bool)],
        g2: &[(usize, bool)],
        fr: &[usize],
        decode: impl Fn(&[u8]) -> bool,
    ) -> Result<()> {
        use baseline_core::arithmetic::{G1, G2};
        use group::Group;
        need(decode(bytes), "honest received wire rejected")?;
        for cut in [0, 1, bytes.len() - 1] {
            need(!decode(&bytes[..cut]), "truncated wire accepted")?;
        }
        let mut extra = bytes.to_vec();
        extra.push(0);
        need(!decode(&extra), "extra wire byte accepted")?;
        for &(offset, nonzero) in g1 {
            for invalid in [[255u8; 48], [0u8; 48], offcurve_g1(), subgroup_bad_g1()] {
                let mut bad = bytes.to_vec();
                bad[offset..offset + 48].copy_from_slice(&invalid);
                need(
                    !decode(&bad),
                    "G1 offcurve/subgroup invalid received field accepted",
                )?;
            }
            let mut unit = bytes.to_vec();
            unit[offset..offset + 48].copy_from_slice(&G1::identity().to_compressed());
            need(
                decode(&unit) != nonzero,
                "G1 native identity format rule changed",
            )?;
        }
        for &(offset, nonzero) in g2 {
            for invalid in [[255u8; 96], [0u8; 96], offcurve_g2(), subgroup_bad_g2()] {
                let mut bad = bytes.to_vec();
                bad[offset..offset + 96].copy_from_slice(&invalid);
                need(
                    !decode(&bad),
                    "G2 offcurve/subgroup invalid received field accepted",
                )?;
            }
            let mut unit = bytes.to_vec();
            unit[offset..offset + 96].copy_from_slice(&G2::identity().to_compressed());
            need(
                decode(&unit) != nonzero,
                "G2 native identity format rule changed",
            )?;
        }
        for &offset in fr {
            let mut bad = bytes.to_vec();
            bad[offset..offset + 32].fill(255);
            need(!decode(&bad), "noncanonical scalar accepted")?;
        }
        Ok(())
    }
    #[test]
    fn received_token_fields_are_canonical_subgroup_checked_and_native_identity_exact() -> Result<()>
    {
        let mut rng = StdRng::seed_from_u64(31_001);
        let pp = sma::setup(10, 1024);
        let issuer = sma::ikeygen(&pp, &mut rng);
        let reader = sma::vkeygen(&pp, &mut rng);
        let installed = sma::install_instance(&pp, &issuer, &reader).map_err(native_error)?;
        let user = sma::ukeygen(&mut rng);
        let attrs = (0..10).map(|x| S::from(x + 1)).collect::<Vec<_>>();
        let policy = sma::Policy {
            atoms: (0..3).map(|i| sma::Atom::Reveal(i, attrs[i])).collect(),
        };
        let (pending, request) =
            sma::request_installed(&installed, &user, &attrs, &policy, &mut rng)
                .map_err(native_error)?;
        let response =
            sma::respond_installed(&installed, &issuer, &reader, &request, &policy, 1, &mut rng)
                .map_err(native_error)?;
        let wallet =
            sma::receive_installed(&installed, pending, &response).map_err(native_error)?;
        let prepared = sma::precompute_policy_installed(&installed, &wallet, 0, &policy, &mut rng)
            .map_err(native_error)?;
        let token = sma::show_online_installed(&installed, prepared, b"ctx", &policy)
            .map_err(native_error)?;
        let bytes = token.bytes();
        let mut g1 = vec![(14, false), (62, true)];
        for i in 0..4 {
            g1.push((206 + i * 48, true));
        }
        g1.extend([(398, true), (446, false), (494, true), (542, false)]);
        for i in 0..token.bits.len() {
            g1.push((598 + i * 48, false));
        }
        let proof = 598 + token.bits.len() * 48 + 8;
        let mut scalar = vec![proof];
        let zs = proof + 32 + 8;
        for i in 0..token.proof.z.len() {
            scalar.push(zs + i * 32);
        }
        let ors = zs + token.proof.z.len() * 32 + 8;
        for i in 0..3 * token.proof.orz.len() {
            scalar.push(ors + i * 32);
        }
        check_wire_domains(&bytes, &g1, &[(110, true)], &scalar, |b| {
            sma::Token::from_received_installed(&installed, b, &policy).is_ok()
        })?;
        let mut dimension = bytes.clone();
        dimension[590..598].copy_from_slice(&11u64.to_be_bytes());
        need(
            sma::Token::from_received_installed(&installed, &dimension, &policy).is_err(),
            "SMA wrong range-vector dimension",
        )?;
        no_native_algebra(|| {
            sma::Token::from_received_installed(&installed, &bytes, &policy)
                .map_err(native_error)?;
            Ok(())
        })?;
        let keys = niat::IssuerKeys::generate(&mut rng);
        let key = keys.install().map_err(native_error)?;
        let client = niat::ClientKeys::generate(&mut rng);
        let message = niat::issue(&key, &keys.secret, client.public_key(), 1, &mut rng)
            .map_err(native_error)?;
        let token = niat::obtain(&key, &client, &message, &mut rng).map_err(native_error)?;
        let bytes = token.encode();
        let h = bytes.len() - 288;
        check_wire_domains(
            &bytes,
            &[(h, true), (h + 48, true), (h + 96, false), (h + 144, true)],
            &[(h + 192, true)],
            &[],
            |b| niat::Token::decode(b).is_ok(),
        )?;
        no_native_algebra(|| {
            niat::Token::decode(&bytes).map_err(native_error)?;
            Ok(())
        })?;
        let issuer = cpat::keygen(&mut rng);
        let key = cpat::validate_key(&issuer.pk).map_err(native_error)?;
        let (request, pending) = cpat::request(&key, b"metadata", &mut rng);
        let response = cpat::issue_installed(&key, &issuer, &request, b"metadata", 1, &mut rng)
            .map_err(native_error)?;
        let wallet = cpat::receive(pending, &response).map_err(native_error)?;
        let tag = [9u8; 32];
        let token = cpat::present(
            cpat::prepare_redemption(&key, &wallet, &tag, &mut rng).map_err(native_error)?,
        );
        let bytes = token.encode();
        let h = 10 + 8 + tag.len();
        check_wire_domains(
            &bytes,
            &[
                (h, false),
                (h + 48, true),
                (h + 96, false),
                (h + 144, false),
                (h + 192, false),
                (h + 240, true),
            ],
            &[(h + 288, true)],
            &[h + 384, h + 416],
            |b| cpat::Token::decode_received(b).is_ok(),
        )?;
        let mut length = bytes.clone();
        length[10..18].copy_from_slice(&u64::MAX.to_be_bytes());
        need(
            cpat::Token::decode_received(&length).is_err(),
            "CPAT max tag length",
        )?;
        no_native_algebra(|| {
            cpat::Token::decode_received(&bytes).map_err(native_error)?;
            Ok(())
        })?;
        let (public, secret) = hin::issuer_keygen(&mut rng);
        let (reader, _) = hin::reader_keygen(&mut rng);
        let (request, pending) = hin::request(&reader, &mut rng).map_err(native_error)?;
        let response = hin::issue(&secret, &reader, &request, 1, &mut rng).map_err(native_error)?;
        let token = hin::receive(pending, &response, &mut rng).map_err(native_error)?;
        need(
            hin::verify(
                &public.install().map_err(native_error)?,
                &token,
                hin::VerificationMode::Specification,
                &mut rng,
            ),
            "Hin honest native verify",
        )?;
        let bytes = token.encode();
        check_wire_domains(
            &bytes,
            &[
                (0, true),
                (48, false),
                (96, false),
                (144, false),
                (192, true),
            ],
            &[(240, true)],
            &[],
            |b| hin::Token::decode(b).is_ok(),
        )?;
        no_native_algebra(|| {
            hin::Token::decode(&bytes).map_err(native_error)?;
            Ok(())
        })?;
        Ok(())
    }
    #[test]
    fn live_slw_input_helpers_do_no_pairing_and_accept_native_gt_identity_format() -> Result<()> {
        use baseline_core::{
            arithmetic::{G1, G2, GT},
            cdm,
        };
        use group::Group;
        let mut rng = StdRng::seed_from_u64(31_224);
        let (pk, issuer) = slw::setup(10, &mut rng).map_err(native_error)?;
        let holder = slw::Holder::generate(&mut rng);
        let attrs = (100..110).map(S::from).collect::<Vec<_>>();
        let (credential, _) =
            slw::run_issue(&pk, &issuer, &holder, &attrs, &mut rng).map_err(native_error)?;
        let disclosed = [2, 3, 4];
        let values = [S::from(100), S::from(101), S::from(102)];
        let mode = slw::VerificationMode::Randomized;
        let (mut prepared, prefix) =
            slw::show_prepare_profile(&pk, &holder, &credential, &disclosed, mode, &mut rng)
                .map_err(native_error)?;
        no_native_algebra(|| {
            slw::decode_show_prefix_received(&pk, &prefix, &disclosed, &values)
                .map_err(native_error)?;
            Ok(())
        })?;
        need(
            slw::decode_show_prefix_received(&pk, &prefix, &[2, 3], &values[..2]).is_err(),
            "SLW wrong public disclosure accepted",
        )?;
        let points = prefix.len() - 2 * 48 - 2 * 96;
        check_wire_domains(
            &prefix,
            &[(points, false), (points + 48, false)],
            &[(points + 96, true), (points + 192, true)],
            &[points - 96, points - 64, points - 32],
            |bytes| slw::decode_show_prefix_received(&pk, bytes, &disclosed, &values).is_ok(),
        )?;
        let prefix_decoded = slw::decode_show_prefix_received(&pk, &prefix, &disclosed, &values)
            .map_err(native_error)?;
        let (vs, v1) =
            slw::show_verifier_begin_received_profile(&pk, prefix_decoded, mode, &mut rng)
                .map_err(native_error)?;
        let (ps, p2) =
            slw::show_holder_first(&pk, &mut prepared, &v1, &mut rng).map_err(native_error)?;
        no_native_algebra(|| {
            slw::decode_show_first_received(&vs, &p2).map_err(native_error)?;
            Ok(())
        })?;
        let mut first = cdm::PFirst::decode(&p2).map_err(native_error)?;
        first.true_first = cdm::Point::GT(GT::identity());
        first.opening_or_first = cdm::Point::GT(GT::identity());
        need(
            slw::decode_show_first_received(&vs, &first.encode()).is_ok(),
            "native GT identity input format rejected",
        )?;
        first.true_first = cdm::Point::G2(G2::generator());
        need(
            slw::decode_show_first_received(&vs, &first.encode()).is_err(),
            "CDM wrong group kind accepted",
        )?;
        for cut in [0, 1, p2.len() - 1] {
            need(
                slw::decode_show_first_received(&vs, &p2[..cut]).is_err(),
                "SLW PFirst truncation",
            )?;
        }
        let mut trailing = p2.clone();
        trailing.push(0);
        need(
            slw::decode_show_first_received(&vs, &trailing).is_err(),
            "SLW PFirst trailing byte",
        )?;
        let mut bad_scalar = p2.clone();
        bad_scalar[22..54].fill(255);
        need(
            slw::decode_show_first_received(&vs, &bad_scalar).is_err(),
            "SLW PFirst scalar",
        )?;
        for offset in [55, 344] {
            let mut bad_gt = p2.clone();
            bad_gt[offset..offset + 288].fill(0);
            need(
                slw::decode_show_first_received(&vs, &bad_gt).is_err(),
                "SLW PFirst GT subgroup",
            )?;
        }
        let received = slw::decode_show_first_received(&vs, &p2).map_err(native_error)?;
        let (vs, v3) = slw::show_verifier_challenge_received_profile(vs, received, &mut rng)
            .map_err(native_error)?;
        let p4 = slw::show_holder_respond(ps, &v3).map_err(native_error)?;
        no_native_algebra(|| {
            slw::decode_show_final_received(&vs, &p4).map_err(native_error)?;
            Ok(())
        })?;
        let mut final_message = cdm::PFourth::decode(&p4).map_err(native_error)?;
        final_message.true_responses.pop();
        need(
            slw::decode_show_final_received(&vs, &final_message.encode()).is_err(),
            "CDM wrong scalar dimension accepted",
        )?;
        let final_message = cdm::PFourth::decode(&p4).map_err(native_error)?;
        let mut scalar_offsets = vec![22];
        scalar_offsets.extend((0..final_message.true_responses.len()).map(|i| 58 + 32 * i));
        let opening = 58 + 32 * final_message.true_responses.len() + 4;
        scalar_offsets.extend((0..final_message.opening_responses.len()).map(|i| opening + 32 * i));
        check_wire_domains(&p4, &[], &[], &scalar_offsets, |bytes| {
            slw::decode_show_final_received(&vs, bytes).is_ok()
        })?;
        for bytes in [&prefix, &p4] {
            let mut tail = bytes.to_vec();
            tail.push(0);
            let check = if std::ptr::eq(bytes, &prefix) {
                slw::decode_show_prefix_received(&pk, &tail, &disclosed, &values).is_err()
            } else {
                slw::decode_show_final_received(&vs, &tail).is_err()
            };
            need(check, "live trailing byte accepted")?;
        }
        need(
            baseline_core::canonical::decode_gt(&[255; 288]).map_err(native_error)?
                == GT::identity(),
            "canonical GT identity sentinel",
        )?;
        need(
            baseline_core::canonical::decode_gt(&[0; 288]).is_err(),
            "non-subgroup torus input accepted",
        )?;
        let accepted = slw::decode_show_final_received(&vs, &p4).map_err(native_error)?;
        need(
            slw::show_verifier_finish_many_received_profile(vec![(vs, accepted)], mode, &mut rng)
                .map_err(native_error)?,
            "SLW original native algebra changed",
        )?;
        std::hint::black_box(G1::generator());
        Ok(())
    }
    #[test]
    fn malformed_last_packet_rejects_before_any_native_algorithm() -> Result<()> {
        let mut rng = StdRng::seed_from_u64(31_333);
        let issuer = cpat::keygen(&mut rng);
        let key = cpat::validate_key(&issuer.pk).map_err(native_error)?;
        let (q, pending) = cpat::request(&key, b"md", &mut rng);
        let response =
            cpat::issue_installed(&key, &issuer, &q, b"md", 0, &mut rng).map_err(native_error)?;
        let wallet = cpat::receive(pending, &response).map_err(native_error)?;
        let tag = vec![8; 32];
        let policy = cpat::Policy {
            allowed: BTreeSet::from([tag.clone()]),
        };
        let token = cpat::present(
            cpat::prepare_redemption(&key, &wallet, &tag, &mut rng).map_err(native_error)?,
        );
        let wire = token.encode();
        let mut bad = wire.clone();
        let n = bad.len();
        bad[n - 32..].fill(255);
        let wires = vec![wire, bad];
        let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
        let mut recorder = Recorder {
            attributes: 10,
            profile: "native".into(),
            bit: 0,
            cache: Rc::new(RefCell::new(BTreeMap::new())),
            clock: Some(&mut clock),
            target: None,
            pipeline_targets: vec![],
            pipeline_trial: None,
            retained: BTreeMap::new(),
            pipeline_observations: BTreeMap::new(),
            pipeline_requests: BTreeMap::new(),
            pipeline_profile_order: BTreeMap::new(),
            catalog: BTreeMap::new(),
            segments: 0,
            message_sizes: vec![],
            completed_profiles: vec![],
            last_messages: None,
            received_fields: WireFields::default(),
            received_sizes: vec![],
        };
        let phase = Phase::new(Role::Verifier, Stage::VerificationCrypto, "bad_input_guard");
        let spec = recorder.spec(Scheme::Cpat, &phase, Some(2));
        recorder.target = Some(spec);
        let mut called = false;
        let result = recorder.received(
            Scheme::Cpat,
            phase,
            Some(2),
            &wires,
            WireFields::default(),
            || decode_cpat(&policy, &wires),
            |_| {
                called = true;
                Ok(Output::value(()))
            },
        );
        need(
            result.is_err() && !called,
            "native algorithm ran before complete batch input decoding",
        )?;
        Ok(())
    }
    #[test]
    fn live_msb_pure_received_contracts_cover_every_point_and_response_shape() -> Result<()> {
        use baseline_core::msb23::pok;
        let mut rng = StdRng::seed_from_u64(31_723);
        let (pp, issuer) = msb::setup(10, &mut rng).map_err(native_error)?;
        let registered = msb::register(pp).map_err(native_error)?;
        let user = msb::user_keygen(&mut rng);
        let agent = msb::user_keygen(&mut rng);
        let (request, pending) = msb::issue_begin(
            &registered,
            &user,
            (101..111).map(S::from).collect(),
            &mut rng,
        )
        .map_err(native_error)?;
        let (challenge, verifier) =
            msb::issue_challenge(&registered, request, &mut rng).map_err(native_error)?;
        let (response, pending) = msb::issue_respond(pending, challenge).map_err(native_error)?;
        let delivery = msb::issue_issuer(&registered, &issuer, verifier, response, &mut rng)
            .map_err(native_error)?;
        let parent = msb::issue_finish_random_pairing_key(&registered, pending, delivery, &mut rng)
            .map_err(native_error)?;
        let (request, pending) =
            msb::delegate_begin(&registered, &agent, vec![msb::period_attribute()], &mut rng)
                .map_err(native_error)?;
        let delivery =
            msb::delegate_sender(&registered, &parent, request, &mut rng).map_err(native_error)?;
        let child = msb::delegate_finish_random(&registered, pending, delivery, &mut rng)
            .map_err(native_error)?;
        let disclosure = msb::Disclosure {
            indices: vec![1, 2],
            sets: vec![
                vec![S::from(101), S::from(102)],
                vec![msb::period_attribute()],
            ],
        };
        let context = vec![19; 32];
        let prepared = msb::show_prepare_policy(&registered, &child, disclosure.clone(), &mut rng)
            .map_err(native_error)?;
        let (first, prover) = msb::show_begin_prepared(&registered, prepared, context.clone())
            .map_err(native_error)?;
        let bytes = wire::encode_show_first(&first);
        let offset = |needle: &[u8]| -> usize {
            let positions = bytes
                .windows(needle.len())
                .enumerate()
                .filter_map(|(i, b)| (b == needle).then_some(i))
                .collect::<Vec<_>>();
            assert_eq!(positions.len(), 1);
            positions[0]
        };
        let mut g1 = vec![
            (offset(&first.sig.z.to_compressed()), false),
            (offset(&first.sig.y.to_compressed()), true),
            (offset(&first.sig.t.to_compressed()), false),
        ];
        g1.extend(first.cs.iter().map(|p| (offset(&p.to_compressed()), true)));
        g1.extend([
            (offset(&first.nym.to_compressed()), true),
            (offset(&first.witness.to_compressed()), true),
            (offset(&first.first.commitment.to_compressed()), false),
        ]);
        let g2 = [(offset(&first.sig.yhat.to_compressed()), true)];
        let scalar = first
            .disclosed
            .sets
            .iter()
            .flatten()
            .map(|s| offset(&s.to_bytes_be()))
            .collect::<Vec<_>>();
        check_wire_domains(&bytes, &g1, &g2, &scalar, |b| {
            msb::decode_show_first_received(&registered, b, &disclosure, &context).is_ok()
        })?;
        need(
            msb::decode_show_first_received(&registered, &bytes, &disclosure, b"wrongctx").is_err(),
            "MSB wrong context input contract",
        )?;
        no_native_algebra(|| {
            msb::decode_show_first_received(&registered, &bytes, &disclosure, &context)
                .map_err(native_error)?;
            Ok(())
        })?;
        let received = msb::decode_show_first_received(&registered, &bytes, &disclosure, &context)
            .map_err(native_error)?;
        let (challenge, verifier) =
            msb::show_challenge_checked(&registered, received, &disclosure, &context, &mut rng)
                .map_err(native_error)?;
        let response = msb::show_respond(prover, challenge).map_err(native_error)?;
        let bytes = response.bytes();
        let opening = 8 + response.announcements.len() * 48;
        let zs = opening + 32 + 8;
        let mut fr = vec![opening];
        fr.extend((0..response.responses.len()).map(|i| zs + 32 * i));
        check_wire_domains(
            &bytes,
            &(0..response.announcements.len())
                .map(|i| (8 + 48 * i, false))
                .collect::<Vec<_>>(),
            &[],
            &fr,
            |b| msb::decode_show_response_received(&verifier, b).is_ok(),
        )?;
        no_native_algebra(|| {
            msb::decode_show_response_received(&verifier, &bytes).map_err(native_error)?;
            Ok(())
        })?;
        let mut wrong = pok::Response::from_bytes(&bytes).map_err(native_error)?;
        wrong.responses.pop();
        need(
            msb::decode_show_response_received(&verifier, &wrong.bytes()).is_err(),
            "MSB wrong response dimension",
        )?;
        let response =
            msb::decode_show_response_received(&verifier, &bytes).map_err(native_error)?;
        let record =
            msb::freeze_show_received(&registered, verifier, response).map_err(native_error)?;
        need(
            msb::verify_frozen_show(
                &registered,
                &record,
                baseline_core::pairing_verify::Mode::Randomized,
                &mut rng,
            ),
            "MSB native algebra changed",
        )?;
        Ok(())
    }
    #[test]
    fn pipeline_six_schemes_share_real_wire_and_fresh_complete_requests() -> Result<()> {
        need(
            slot_application_operation(41, 16, 10).len() == b"baseline-native-operation".len()
                && slot_application_operation(41, 16, 10).len() == 25
                && slot_application_operation(41, 16, 10) != slot_application_operation(42, 16, 10),
            "fixed-size application nonce control",
        )?;

        for scheme in ["SMA²RT", "NIAT", "CPAT", "HinToken", "MSB+23", "SLW+25"] {
            let mut factory = Factory::new()?;
            let catalog = factory.jobs();
            let ids = catalog
                .iter()
                .filter(|j| {
                    j.scheme == scheme
                        && j.workload["k"] == 1
                        && ((j.stage == "inclusive_verification" && j.boundary["safe"] == true)
                            || matches!(j.stage.as_str(), "preparation" | "online_generation"))
                })
                .map(|j| j.id.clone())
                .collect::<Vec<_>>();
            need(!ids.is_empty(), &format!("missing pipeline jobs {scheme}"))?;
            let mut hashes = vec![];
            let mut orders = vec![];
            for trial in [41, 42] {
                let action = factory.prepare_pipeline(&ids, trial)?;
                let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
                let result = action(&mut clock).map_err(|e| format!("{scheme}: {e}"))?;
                need(
                    result["correctness"] == "PASS",
                    "pipeline native correctness",
                )?;
                for id in &ids {
                    need(
                        clock.observations().contains_key(id),
                        &format!("pipeline did not capture {id}"),
                    )?;
                }
                let request = result["complete_requests"]["1"]
                    ["complete_application_request_sha256"]
                    .as_str()
                    .ok_or("pipeline complete request missing")?
                    .to_owned();
                for id in ids.iter().filter(|id| {
                    catalog
                        .iter()
                        .any(|j| j.id == **id && j.stage == "inclusive_verification")
                }) {
                    need(
                        result["observations"][id]["complete_application_request_sha256"]
                            == request,
                        "same-slot verifier input mismatch",
                    )?;
                    let observation = &clock.observations()[id];
                    let rows = observation["darlt_spans"]
                        .as_array()
                        .ok_or("same-call spans missing")?;
                    need(
                        rows.iter().any(|r| {
                            r["report"]["rows"].as_array().is_some_and(|rows| {
                                rows.iter()
                                    .any(|row| row["name"] == "receive.strict_decoding")
                            })
                        }),
                        "same-call decoder not observed",
                    )?;
                    need(
                        observation["elapsed_ns"].is_null(),
                        "ClockFree pipeline persisted timing",
                    )?;
                }
                hashes.push(request);
                orders.push(result["verification_profile_order"]["1"].clone());
            }
            need(
                orders[0].is_array() && orders[0] != orders[1],
                "same-input candidate order did not rotate across trials",
            )?;
            need(
                hashes[0] != hashes[1],
                "complete request reused across sample slots",
            )?;
        }
        Ok(())
    }
    #[test]
    fn pipeline_msb_slw_complete_live_transcripts_are_identical_across_profiles() -> Result<()> {
        let mut factory = Factory::new()?;
        for scheme in ["MSB+23", "SLW+25"] {
            let ids = factory
                .jobs()
                .iter()
                .filter(|j| {
                    j.scheme == scheme
                        && j.stage == "inclusive_verification"
                        && j.workload["k"] == 16
                })
                .map(|j| j.id.clone())
                .collect::<Vec<_>>();
            need(ids.len() == 2, "interactive Spec/Random pipeline pair")?;
            let action = factory.prepare_pipeline(&ids, 71)?;
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
            let result = action(&mut clock)?;
            let summaries = ids
                .iter()
                .map(|id| result["observations"][id]["complete_application_request_sha256"].clone())
                .collect::<Vec<_>>();
            need(
                summaries[0].is_string() && summaries[0] == summaries[1],
                "full bidirectional native transcript changed across profiles",
            )?;
            let expected = if scheme == "MSB+23" { 3 } else { 4 };
            for id in &ids {
                need(
                    clock.observations()[id]["segment_count"] == expected,
                    "live verifier legs or actual state leg omitted",
                )?;
            }
        }
        Ok(())
    }
    #[test]
    fn pipeline_once_decode_is_shared_only_with_same_execution_components() -> Result<()> {
        let mut factory = Factory::new()?;
        for scheme in ["SMA²RT", "NIAT", "CPAT", "HinToken", "MSB+23", "SLW+25"] {
            let catalog = factory.jobs();
            let ids = catalog
                .iter()
                .filter(|j| {
                    j.scheme == scheme
                        && j.workload["k"] == 1
                        && ((j.boundary["safe"] == true
                            && matches!(
                                j.stage.as_str(),
                                "verification_crypto" | "inclusive_verification"
                            ))
                            || j.stage == "strict_decoding"
                            || j.stage == "shared_state")
                })
                .map(|j| j.id.clone())
                .collect::<Vec<_>>();
            let action = factory.prepare_pipeline(&ids, 81)?;
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
            let (result, audit) =
                baseline_core::subgroup_audit::collect_selected(|| action(&mut clock));
            let output = result?;
            for id in &ids {
                need(
                    clock.observations().contains_key(id),
                    &format!("missing same-call component {id}"),
                )?;
            }
            if audit.enabled {
                for kind in ["G1", "G2", "GT"] {
                    need(
                        audit.events.iter().filter(|e| e.kind == kind).count() as u64
                            == output["actual_received_fields"][kind]
                                .as_u64()
                                .ok_or("pipeline received field count")?,
                        "pipeline subgroup count differs from received slots",
                    )?;
                }
                need(
                    !audit.events.is_empty()
                        && audit.events.iter().all(|e| e.operation == "checked_decode"),
                    "pipeline repeated subgroup verification after sealed decode",
                )?;
            }
        }
        Ok(())
    }
    #[test]
    fn pipeline_native_full_read_both_bits_reuses_original_received_algorithm() -> Result<()> {
        let mut factory = Factory::new()?;
        let catalog = factory.jobs();
        for job in catalog.iter().filter(|j| j.stage == "native_read") {
            let action = factory.prepare_pipeline(std::slice::from_ref(&job.id), 91)?;
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
            let result = action(&mut clock)?;
            need(
                result["correctness"] == "PASS" && clock.observations().contains_key(&job.id),
                "native full Read pipeline",
            )?;
        }
        Ok(())
    }
    #[test]
    fn pipeline_fixed_wallet_assets_remain_same_and_equal_budget_accounts_share_flows() -> Result<()>
    {
        let mut factory = Factory::new()?;
        let catalog = factory.jobs();
        let ids = catalog
            .iter()
            .filter(|j| {
                j.scheme == "SMA²RT" && j.stage == "inclusive_verification" && j.workload["k"] == 1
            })
            .map(|j| j.id.clone())
            .collect::<Vec<_>>();
        let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
        factory.prepare_pipeline(&ids, 101)?(&mut clock)?;
        let assets = factory
            .cache
            .borrow()
            .iter()
            .filter(|(k, _)| k.starts_with("pipeline-source/"))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<Vec<_>>();
        let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
        factory.prepare_pipeline(&ids, 102)?(&mut clock)?;
        for (key, asset) in assets {
            need(
                Rc::ptr_eq(
                    &asset,
                    factory
                        .cache
                        .borrow()
                        .get(&key)
                        .ok_or("cached wallet disappeared")?,
                ),
                "fixed native wallet regenerated",
            )?;
        }
        for agents in [1, 4] {
            let ids = catalog
                .iter()
                .filter(|j| j.workload["agents"] == agents && j.stage.starts_with("provisioning_"))
                .map(|j| j.id.clone())
                .collect::<Vec<_>>();
            need(ids.len() == 2, "equal-budget two accounts")?;
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
            let result = factory.prepare_pipeline(&ids, 111)?(&mut clock)?;
            let issuer = ids
                .iter()
                .find(|id| id.ends_with("provisioning_issuer"))
                .ok_or("issuer account id")?;
            let system = ids
                .iter()
                .find(|id| id.ends_with("provisioning_system"))
                .ok_or("system account id")?;
            need(
                clock.observations()[system]["segment_count"] == 3 * agents,
                "system omitted native request/response/receive",
            )?;
            need(
                clock.observations()[issuer]["derived"] == true,
                "issuer account replayed native issuance",
            )?;
            need(
                result["observations"][issuer]["complete_application_request_sha256"]
                    == result["observations"][system]["complete_application_request_sha256"],
                "provisioning accounts used different flows",
            )?;
            need(
                result["observations"][system]["actual_issuer_calls"] == agents,
                "provisioning reused one issuance times A",
            )?;
        }
        Ok(())
    }
    #[test]
    fn pipeline_table_iii_public_packages_and_credentials_have_actual_role_wire_evidence(
    ) -> Result<()> {
        let mut factory = Factory::new()?;
        let catalog = factory.jobs();
        for scheme in ["SMA²RT", "NIAT", "CPAT", "HinToken", "MSB+23", "SLW+25"] {
            let ids = catalog
                .iter()
                .filter(|j| {
                    if j.scheme != scheme
                        || j.id.contains("/installed-for-")
                        || j.workload["agents"].is_u64()
                        || j.workload["k"].as_u64().is_some_and(|k| k != 1)
                    {
                        return false;
                    }
                    match j.stage.as_str() {
                        "install" => scheme != "CPAT" || j.role == "user",
                        "issue_request" => true,
                        "issue_response" => scheme != "NIAT" || j.profile == "NativeTotal",
                        "issue_accept" => match scheme {
                            "NIAT" => j.profile == "NativeTotal",
                            "MSB+23" => j.profile == "RandomizedPairingKey",
                            "SLW+25" => j.profile == "Randomized",
                            _ => true,
                        },
                        "delegate_send" => matches!(scheme, "MSB+23" | "SLW+25"),
                        "delegate_receive" => {
                            matches!(scheme, "MSB+23" | "SLW+25") && j.profile == "Randomized"
                        }
                        _ => false,
                    }
                })
                .map(|j| j.id.clone())
                .collect::<Vec<_>>();
            let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
            let result = factory.prepare_pipeline(&ids, 1501)?(&mut clock)
                .map_err(|e| format!("{scheme}: {e}"))?;
            for id in &ids {
                need(
                    clock.observations().contains_key(id),
                    &format!("missing TableIII role {id}"),
                )?;
            }
            for id in ids
                .iter()
                .filter(|id| catalog.iter().any(|j| j.id == **id && j.stage == "install"))
            {
                let packets = result["observations"][id]["public_package_packets"]
                    .as_array()
                    .ok_or("public package packet metadata missing")?;
                need(
                    !packets.is_empty()
                        && packets.iter().all(|p| {
                            p["wire_bytes"].as_u64().is_some_and(|n| n > 0)
                                && p["wire_sha256"].as_str().is_some_and(|s| s.len() == 64)
                        }),
                    "public packet size/hash absent",
                )?;
            }
            for id in ids.iter().filter(|id| {
                catalog.iter().any(|j| {
                    j.id == **id && matches!(j.stage.as_str(), "issue_accept" | "delegate_receive")
                })
            }) {
                let packets = result["observations"][id]["received_packets"]
                    .as_array()
                    .ok_or("credential received packet metadata missing")?;
                need(
                    !packets.is_empty(),
                    "credential receiver has no native packet",
                )?;
                for packet in packets {
                    let sender = packet["sender_job_id"]
                        .as_str()
                        .ok_or("credential sender association missing")?;
                    let sent = result["observations"][sender]["sent_packets"]
                        .as_array()
                        .ok_or("actual sender packet evidence missing")?;
                    need(
                        sent.iter().any(|p| {
                            p["wire_bytes"] == packet["wire_bytes"]
                                && p["wire_sha256"] == packet["wire_sha256"]
                        }),
                        "received credential cannot be traced to actual native sender",
                    )?;
                }
            }
        }
        Ok(())
    }
    #[test]
    fn pipeline_metadata_read_two_bits_always_uses_this_sample_full_verification() -> Result<()> {
        let mut factory = Factory::new()?;
        let jobs = factory
            .jobs()
            .into_iter()
            .filter(|j| j.stage == "metadata_read")
            .collect::<Vec<_>>();
        need(
            jobs.len() == 8,
            "four functional schemes times two metadata bits",
        )?;
        for job in jobs {
            for trial in [1601, 1602] {
                let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
                let result =
                    factory.prepare_pipeline(std::slice::from_ref(&job.id), trial)?(&mut clock)?;
                let record = &result["observations"][&job.id];
                need(
                    record["input_record_provenance"] == "full_native_verification_in_same_sample"
                        && record["input_record_cached_across_samples"] == false
                        && record["input_record_verification_profile"]
                            == fixed_baseline_profile(match job.scheme.as_str() {
                                "SMA²RT" => Scheme::Sma2rt,
                                "NIAT" => Scheme::Niat,
                                "CPAT" => Scheme::Cpat,
                                "HinToken" => Scheme::HinToken,
                                _ => return Err("unexpected Read scheme".into()),
                            }),
                    "Read used a cached, Specification, or unverified record",
                )?;
                need(
                    clock.observations()[&job.id]["elapsed_ns"].is_null(),
                    "Read test persisted timing",
                )?;
            }
        }
        Ok(())
    }
    #[test]
    #[cfg(feature = "subgroup-audit")]
    fn pipeline_fixed_receive_steps_check_each_received_group_once() -> Result<()> {
        let mut factory = Factory::new()?;
        let jobs = factory.jobs();
        let mut rows = vec![];
        for scheme in ["SMA²RT", "NIAT", "CPAT", "HinToken", "MSB+23", "SLW+25"] {
            let selected = jobs
                .iter()
                .filter(|j| {
                    j.scheme == scheme
                        && j.workload["k"].as_u64().is_none_or(|k| k == 1)
                        && matches!(
                            j.stage.as_str(),
                            "issue_request"
                                | "issue_response"
                                | "issue_accept"
                                | "delegate_send"
                                | "delegate_receive"
                                | "verification_crypto"
                        )
                        && match (scheme, j.stage.as_str()) {
                            ("NIAT", "issue_accept" | "issue_response") => {
                                j.profile == "NativeTotal"
                            }
                            ("MSB+23", "issue_accept") => j.profile == "RandomizedPairingKey",
                            ("MSB+23", "delegate_receive")
                            | ("SLW+25", "issue_accept" | "delegate_receive") => {
                                j.profile == "Randomized"
                            }
                            (_, "verification_crypto") => j.role != "verifier",
                            _ => true,
                        }
                })
                .collect::<Vec<_>>();
            need(!selected.is_empty(), "missing dynamic role audit")?;
            for job in selected {
                let action = factory.prepare_pipeline(std::slice::from_ref(&job.id), 9033)?;
                let mut clock = BoundaryClock::new(RunMode::ClockFree, None)?;
                let (result, audit) =
                    baseline_core::subgroup_audit::collect_selected(|| action(&mut clock));
                result.map_err(|e| format!("{}: {e}", job.id))?;
                let decodes = audit
                    .events
                    .iter()
                    .filter(|e| e.operation == "checked_decode")
                    .collect::<Vec<_>>();
                for event in audit.events.iter().filter(|e| e.operation == "membership") {
                    need(
                        !decodes
                            .iter()
                            .any(|d| d.kind == event.kind && d.encoding_hex == event.encoding_hex),
                        &format!("{} rechecked received encoding: {:?}", job.id, event),
                    )?;
                }
                // These unframed native messages have fixed literal point counts.
                let expected = match (scheme, job.stage.as_str()) {
                    ("SMA²RT", "issue_response") => Some((2, 0)),
                    ("SMA²RT", "issue_accept") => Some((5, 1)),
                    ("NIAT", "issue_response") => Some((1, 0)),
                    ("NIAT", "issue_accept") => Some((3, 1)),
                    ("CPAT", "issue_response") => Some((1, 0)),
                    ("CPAT", "issue_accept") => Some((5, 1)),
                    ("HinToken", "issue_response") => Some((2, 0)),
                    ("HinToken", "issue_accept") => Some((4, 1)),
                    ("MSB+23", "issue_response") => Some((6, 0)),
                    ("MSB+23", "issue_accept") => Some((16, 1)),
                    ("MSB+23", "delegate_send") => Some((1, 0)),
                    ("MSB+23", "delegate_receive") => Some((6, 1)),
                    _ => None,
                };
                let count = |kind: &str| decodes.iter().filter(|e| e.kind == kind).count();
                if let Some((g1, g2)) = expected {
                    need(
                        count("G1") == g1 && count("G2") == g2,
                        &format!(
                            "{} wrong received point count {}/{} expected {g1}/{g2}",
                            job.id,
                            count("G1"),
                            count("G2")
                        ),
                    )?;
                }
                rows.push(json!({"job_id":job.id,"G1_checked_decode":count("G1"),"G2_checked_decode":count("G2"),"GT_checked_decode":count("GT"),"received_encoding_native_rechecks":0,"events":audit.events}));
            }
        }
        println!(
            "FIXED_SET_RECEIVE_AUDIT={}",
            serde_json::to_string(&rows).map_err(native_error)?
        );
        Ok(())
    }
    #[test]
    fn sealed_receive_set_keeps_proofs_and_rejects_bad_signatures() -> Result<()> {
        use baseline_core::curve::{start_counts, stop_counts, G1};
        use group::Group;
        let mut rng = StdRng::seed_from_u64(202033);
        let mut weights = StdRng::seed_from_u64(202034);
        let issuer = cpat::keygen(&mut rng);
        let key = cpat::validate_key(&issuer.pk).map_err(native_error)?;
        for bad in [false, true] {
            let (request, pending) = cpat::request(&key, b"metadata", &mut rng);
            let request = cpat::ReceivedRequest::decode(&cpat_request_bytes(&request))
                .map_err(native_error)?;
            let mut response =
                cpat::issue_received_installed(&key, &issuer, request, b"metadata", 1, &mut rng)
                    .map_err(native_error)?;
            if bad {
                response.sig.z += G1::generator();
            }
            let bytes = cpat_response_bytes(&response);
            need(
                cpat::ReceivedResponse::decode(&bytes[..bytes.len() - 1]).is_err(),
                "CPAT sealed truncation",
            )?;
            let received = cpat::ReceivedResponse::decode(&bytes).map_err(native_error)?;
            start_counts();
            let accepted = cpat::receive_received_set(pending, received, &mut weights);
            let count = stop_counts();
            need(
                accepted.is_ok() != bad,
                "CPAT SET accepted invalid signature",
            )?;
            need(
                count.p + count.mp_calls == 1,
                "CPAT Receive did not share its two PPE",
            )?;
        }
        let pp = sma::setup(10, 1024);
        let issuer = sma::ikeygen(&pp, &mut rng);
        let reader = sma::vkeygen(&pp, &mut rng);
        let installed = sma::install_instance(&pp, &issuer, &reader).map_err(native_error)?;
        let user = sma::ukeygen(&mut rng);
        let attrs = (1..=10).map(S::from).collect::<Vec<_>>();
        let policy = sma::Policy::default();
        for bad in [false, true] {
            let (pending, request) =
                sma::request_installed(&installed, &user, &attrs, &policy, &mut rng)
                    .map_err(native_error)?;
            let request = sma::ReceivedRequest::decode(&request.bytes()).map_err(native_error)?;
            let mut response = sma::respond_received_installed(
                &installed, &issuer, &reader, request, &policy, 1, &mut rng,
            )
            .map_err(native_error)?;
            if bad {
                response.sig.z += G1::generator();
            }
            let bytes = response.bytes();
            need(
                sma::ReceivedCredential::decode(&bytes[..bytes.len() - 1]).is_err(),
                "SMA sealed truncation",
            )?;
            let received = sma::ReceivedCredential::decode(&bytes).map_err(native_error)?;
            start_counts();
            let accepted = sma::receive_received_set(&installed, pending, received, &mut weights);
            let count = stop_counts();
            need(
                accepted.is_ok() != bad,
                "SMA SET accepted invalid signature",
            )?;
            need(
                count.p + count.mp_calls == 1,
                "SMA Receive did not share its two PPE",
            )?;
        }
        let issuer = niat::IssuerKeys::generate(&mut rng);
        let installed = issuer.install().map_err(native_error)?;
        let client = niat::ClientKeys::generate(&mut rng);
        for bad in [false, true] {
            let mut response = niat::prepare_issue(&installed, &mut rng)
                .issue_wire(
                    &installed,
                    &issuer.secret,
                    &niat::encode_client_request(client.public_key()),
                    1,
                    &mut rng,
                )
                .map_err(native_error)?;
            if bad {
                response.signature.z += G1::generator();
            }
            let prepared = client.prepare_obtain(&mut rng);
            let bytes = response.encode();
            start_counts();
            let accepted = prepared.obtain_wire_set(&installed, &bytes, &mut weights);
            let count = stop_counts();
            need(
                accepted.is_ok() != bad,
                "NIAT SET accepted invalid signature",
            )?;
            need(
                count.p + count.mp_calls == 1,
                "NIAT Obtain did not share its two PPE",
            )?;
        }
        Ok(())
    }
}
