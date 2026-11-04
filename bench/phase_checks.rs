//! Actual role callbacks for the runtime-check preparation and native-interaction boundaries.
//! These checks execute role callbacks without collecting timing samples.
use crate::harness::{
    Boundary, Cache, Label, Mode, NativeObjects, Output, Recorder, Role, Scheme, Stage, Substage,
    Workload,
};
use baseline_core::{
    arithmetic::S,
    bhn26 as niat, hintoken as hin, klo26 as cpat,
    msb23::{scheme as msb, wire},
    slw25 as slw, sma2rt as sma,
};
use ff::Field;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::{json, Value};
use std::collections::BTreeSet;

type Result<T> = std::result::Result<T, String>;

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
struct Native<'a> {
    recorder: &'a mut Recorder,
    scheme: Scheme,
    attributes: Option<usize>,
}
impl Native<'_> {
    fn record<T>(
        &mut self,
        phase: Phase,
        k: Option<usize>,
        action: impl FnOnce() -> Result<Output<T>>,
    ) -> Result<T> {
        let cache = match phase.stage {
            Stage::Install => Cache::Cold,
            Stage::KeyGeneration | Stage::Setup => Cache::NotApplicable,
            _ => Cache::Hot,
        };
        let tokens = if matches!(self.scheme, Scheme::Msb23 | Scheme::Slw25) {
            None
        } else {
            k
        };
        self.recorder
            .record(
                Label {
                    scheme: self.scheme,
                    role: phase.role,
                    stage: phase.stage,
                    substage: Substage::Whole,
                    cache,
                    profile: phase.profile.into(),
                    boundary: Boundary {
                        wire_encoding_included: phase.encode,
                        strict_decoding_included: phase.decode,
                        ..Boundary::default()
                    },
                },
                Workload {
                    k,
                    n: (self.scheme == Scheme::Sma2rt).then_some(1024),
                    attributes: self.attributes,
                    native_objects: NativeObjects {
                        tokens,
                        ..NativeObjects::default()
                    },
                    ..Workload::default()
                },
                action,
            )
            .map_err(|e| format!("{} {}: {e}", self.scheme.label(), phase.profile))
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

fn sma_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::Sma2rt,
        attributes: Some(10),
    };
    let pp = f.record(
        Phase::new(Role::System, Stage::Setup, "native_parameters").encoded(),
        None,
        || {
            let p = sma::setup(10, 1024);
            let b = p.bytes();
            Ok(Output::with_messages(p, vec![b]))
        },
    )?;
    let issuer = f.record(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "issuer_keygen"),
        None,
        || Ok(Output::value(sma::ikeygen(&pp, rng))),
    )?;
    let reader = f.record(
        Phase::new(Role::Reader, Stage::KeyGeneration, "metadata_keygen"),
        None,
        || Ok(Output::value(sma::vkeygen(&pp, rng))),
    )?;
    let user = f.record(
        Phase::new(Role::User, Stage::KeyGeneration, "holder_keygen"),
        None,
        || Ok(Output::value(sma::ukeygen(rng))),
    )?;
    let installed = f.record(
        Phase::new(
            Role::User,
            Stage::Install,
            "parameters_issuer_metadata_key_proofs_and_cache",
        ),
        None,
        || {
            Ok(Output::value(
                sma::install_instance(&pp, &issuer, &reader).map_err(native_error)?,
            ))
        },
    )?;
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
    let response = f.record(
        Phase::new(Role::Issuer, Stage::IssueResponse, "native_issuer_response").encoded(),
        None,
        || {
            let c = sma::respond_installed(&installed, &issuer, &reader, &request, &policy, 0, rng)
                .map_err(native_error)?;
            let b = c.bytes();
            Ok(Output::with_messages(c, vec![b]))
        },
    )?;
    let wallet = f.record(
        Phase::new(
            Role::User,
            Stage::IssueAccept,
            "native_receive_signature_and_proof_checks",
        ),
        None,
        || {
            Ok(Output::value(
                sma::receive_installed(&installed, pending, &response).map_err(native_error)?,
            ))
        },
    )?;
    for &k in ks {
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
                        sma::show_online_installed(&installed, p, &[42; 32], &policy)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = t.iter().map(sma::Token::bytes).collect();
                Ok(Output::with_messages(t, b))
            },
        )?;
        f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "native_sequential_specification",
            ),
            Some(k),
            || {
                need(
                    tokens
                        .iter()
                        .all(|t| sma::verify_installed(&installed, t, &[42; 32], &policy)),
                    "SMA native verification",
                )?;
                Ok(Output::value(()))
            },
        )?;
        f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "safe_random_complete_batch",
            ),
            Some(k),
            || {
                need(
                    sma::verify_random_batch_installed(
                        &installed, &tokens, &[42; 32], &policy, rng,
                    ),
                    "SMA random verification",
                )?;
                Ok(Output::value(()))
            },
        )?;
        f.record(
            Phase::new(
                Role::Reader,
                Stage::MetadataRead,
                "one_previously_verified_record_bit0",
            ),
            Some(1),
            || {
                need(
                    sma::recover_metadata(&reader, &tokens[0]) == Some(0),
                    "SMA read",
                )?;
                Ok(Output::value(()))
            },
        )?;
    }
    Ok(())
}

fn niat_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::Niat,
        attributes: None,
    };
    let keys = f.record(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "native_issuer_keygen").encoded(),
        None,
        || {
            let keys = niat::IssuerKeys::generate(rng);
            let b = keys.public.encode();
            Ok(Output::with_messages(keys, vec![b]))
        },
    )?;
    let installed = f.record(
        Phase::new(
            Role::User,
            Stage::Install,
            "native_issuer_validation_and_pairing_anchor_cache",
        ),
        None,
        || Ok(Output::value(keys.install().map_err(native_error)?)),
    )?;
    let client = f.record(
        Phase::new(Role::User, Stage::KeyGeneration, "native_client_keygen"),
        None,
        || Ok(Output::value(niat::ClientKeys::generate(rng))),
    )?;
    for &k in ks {
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
        let responses = f.record(
            Phase::new(
                Role::Issuer,
                Stage::IssueResponse,
                "native_k_independent_issuances",
            )
            .encoded(),
            Some(k),
            || {
                let v = (0..k)
                    .map(|i| {
                        niat::issue(
                            &installed,
                            &keys.secret,
                            client.public_key(),
                            (i % 2) as u8,
                            rng,
                        )
                        .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = v.iter().map(niat::IssueMessage::encode).collect();
                Ok(Output::with_messages(v, b))
            },
        )?;
        let tokens = f.record(
            Phase::new(
                Role::User,
                Stage::IssueAccept,
                "native_obtain_and_signature_checks",
            ),
            Some(k),
            || {
                let t = responses
                    .iter()
                    .map(|r| niat::obtain(&installed, &client, r, rng).map_err(native_error))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Output::value(t))
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
        let verified = f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "native_sequential_specification",
            ),
            Some(k),
            || {
                let v = tokens
                    .iter()
                    .map(|t| niat::verify_token(&installed, t).map_err(native_error))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Output::value(v))
            },
        )?;
        for (mode, name) in [
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
            f.record(
                Phase::new(Role::Verifier, Stage::VerificationCrypto, name),
                Some(k),
                || {
                    niat::verify_batch_redemption(&installed, &tokens, mode, rng)
                        .map_err(native_error)?;
                    Ok(Output::value(()))
                },
            )?;
        }
        f.record(
            Phase::new(
                Role::Reader,
                Stage::MetadataRead,
                "one_previously_verified_record_bit0",
            ),
            Some(1),
            || {
                need(
                    niat::read_bit_extract(&keys.secret, &verified[0]).map_err(native_error)? == 0,
                    "NIAT read",
                )?;
                Ok(Output::value(()))
            },
        )?;
        f.record(
            Phase::new(
                Role::Reader,
                Stage::NativeRead,
                "native_Read_includes_Verify_one_record",
            ),
            Some(1),
            || {
                need(
                    niat::read_bit_total(&installed, &keys.secret, &tokens[0])
                        .map_err(native_error)?
                        == 0,
                    "NIAT total read",
                )?;
                Ok(Output::value(()))
            },
        )?;
    }
    Ok(())
}

fn cpat_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::Cpat,
        attributes: None,
    };
    let issuer = f.record(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "native_issuer_keygen"),
        None,
        || Ok(Output::value(cpat::keygen(rng))),
    )?;
    let key = f.record(
        Phase::new(Role::User, Stage::Install, "issuer_key_proof_installation"),
        None,
        || {
            Ok(Output::value(
                cpat::validate_key(&issuer.pk).map_err(native_error)?,
            ))
        },
    )?;
    let metadata = [0x66; 32];
    let tag = vec![0x55; 32];
    let policy = cpat::Policy {
        allowed: BTreeSet::from([tag.clone()]),
    };
    let cached_metadata = f.record(
        Phase::new(
            Role::Verifier,
            Stage::Install,
            "same_metadata_key_combination_installation",
        ),
        None,
        || Ok(Output::value(cpat::install_metadata(&key, &metadata))),
    )?;
    for &k in ks {
        let requests = f.record(
            Phase::new(
                Role::User,
                Stage::IssueRequest,
                "native_k_independent_pretoken_requests_no_full_codec",
            ),
            Some(k),
            || {
                Ok(Output::value(
                    (0..k)
                        .map(|_| cpat::request(&key, &metadata, rng))
                        .collect::<Vec<_>>(),
                ))
            },
        )?;
        let responses = f.record(
            Phase::new(
                Role::Issuer,
                Stage::IssueResponse,
                "native_k_pretoken_responses_no_full_codec",
            ),
            Some(k),
            || {
                Ok(Output::value(
                    requests
                        .iter()
                        .enumerate()
                        .map(|(i, (q, _))| {
                            cpat::issue_installed(&key, &issuer, q, &metadata, i % 2, rng)
                                .map_err(native_error)
                        })
                        .collect::<Result<Vec<_>>>()?,
                ))
            },
        )?;
        let wallets = f.record(
            Phase::new(
                Role::User,
                Stage::IssueAccept,
                "receive_signature_verified_once_cached_immutable_wallet",
            ),
            Some(k),
            || {
                Ok(Output::value(
                    requests
                        .into_iter()
                        .zip(&responses)
                        .map(|((_, p), d)| cpat::receive(p, d).map_err(native_error))
                        .collect::<Result<Vec<_>>>()?,
                ))
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
        let verified = f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "native_sequential_specification",
            ),
            Some(k),
            || {
                Ok(Output::value(
                    tokens
                        .iter()
                        .map(|t| {
                            cpat::verify_record(&key, &policy, &metadata, t).map_err(native_error)
                        })
                        .collect::<Result<Vec<_>>>()?,
                ))
            },
        )?;
        f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "safe_random_FHS_four_coordinate",
            ),
            Some(k),
            || {
                need(
                    cpat::verify_random_batch(&key, &policy, &metadata, &tokens, rng),
                    "CPAT full random",
                )?;
                Ok(Output::value(()))
            },
        )?;
        f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "safe_random_FHS_same_metadata_cached",
            ),
            Some(k),
            || {
                need(
                    cpat::verify_random_batch_metadata(&cached_metadata, &policy, &tokens, rng),
                    "CPAT same metadata random",
                )?;
                Ok(Output::value(()))
            },
        )?;
        f.record(
            Phase::new(
                Role::Reader,
                Stage::MetadataRead,
                "one_previously_verified_record_bit0",
            ),
            Some(1),
            || {
                need(
                    cpat::read_bit_validated(&issuer, &verified[0]).map_err(native_error)? == 0,
                    "CPAT read",
                )?;
                Ok(Output::value(()))
            },
        )?;
        f.record(
            Phase::new(
                Role::Reader,
                Stage::NativeRead,
                "native_Read_includes_Verify_one_record",
            ),
            Some(1),
            || {
                need(
                    cpat::read_bit(&issuer, &key, &policy, &metadata, &tokens[0])
                        .map_err(native_error)?
                        == 0,
                    "CPAT native read",
                )?;
                Ok(Output::value(()))
            },
        )?;
    }
    Ok(())
}

fn hin_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::HinToken,
        attributes: None,
    };
    let (public, secret) = f.record(
        Phase::new(Role::Issuer, Stage::KeyGeneration, "native_issuer_keygen").encoded(),
        None,
        || {
            let (p, s) = hin::issuer_keygen(rng);
            let b = p.encode();
            Ok(Output::with_messages((p, s), vec![b]))
        },
    )?;
    let (reader, reader_secret) = f.record(
        Phase::new(Role::Reader, Stage::KeyGeneration, "native_reader_keygen").encoded(),
        None,
        || {
            let (p, s) = hin::reader_keygen(rng);
            let b = p.encode().to_vec();
            Ok(Output::with_messages((p, s), vec![b]))
        },
    )?;
    let installed = f.record(
        Phase::new(
            Role::Verifier,
            Stage::Install,
            "issuer_validation_and_fixed_pairing_anchor_installation",
        ),
        None,
        || Ok(Output::value(public.install().map_err(native_error)?)),
    )?;
    for &k in ks {
        let requests = f.record(
            Phase::new(Role::User, Stage::IssueRequest, "native_k_token_requests").encoded(),
            Some(k),
            || {
                let v = (0..k)
                    .map(|_| hin::request(&reader, rng).map_err(native_error))
                    .collect::<Result<Vec<_>>>()?;
                let b = v.iter().map(|(q, _)| q.encode()).collect();
                Ok(Output::with_messages(v, b))
            },
        )?;
        let responses = f.record(
            Phase::new(
                Role::Issuer,
                Stage::IssueResponse,
                "native_k_token_responses",
            )
            .encoded(),
            Some(k),
            || {
                let v = requests
                    .iter()
                    .enumerate()
                    .map(|(i, (q, _))| {
                        hin::issue(&secret, &reader, q, (i % 2) as u8, rng).map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = v.iter().map(hin::Response::encode).collect();
                Ok(Output::with_messages(v, b))
            },
        )?;
        let tokens = f.record(
            Phase::new(
                Role::User,
                Stage::IssueAccept,
                "native_User1_proof_acceptance_and_representation_change",
            ),
            Some(k),
            || {
                let v = requests
                    .into_iter()
                    .zip(&responses)
                    .map(|((_, p), d)| hin::receive(p, d, rng).map_err(native_error))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Output::value(v))
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
            f.record(
                Phase::new(Role::Verifier, Stage::VerificationCrypto, name),
                Some(k),
                || {
                    need(
                        hin::verify_batch(&installed, &tokens, mode, rng),
                        "HinToken verification",
                    )?;
                    Ok(Output::value(()))
                },
            )?;
        }
        f.record(
            Phase::new(
                Role::Reader,
                Stage::MetadataRead,
                "one_previously_verified_record_bit0",
            ),
            Some(1),
            || {
                need(
                    hin::read_bit(&reader_secret, &tokens[0]) == Some(0),
                    "HinToken read",
                )?;
                Ok(Output::value(()))
            },
        )?;
        f.record(
            Phase::new(
                Role::Reader,
                Stage::NativeRead,
                "native_Read_includes_Verify_one_record",
            ),
            Some(1),
            || {
                need(
                    hin::read_total(
                        &reader_secret,
                        &installed,
                        &tokens[0],
                        hin::VerificationMode::Specification,
                        rng,
                    ) == Some(0),
                    "HinToken native read",
                )?;
                Ok(Output::value(()))
            },
        )?;
    }
    Ok(())
}

fn msb_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::Msb23,
        attributes: Some(10),
    };
    let (pp, issuer) = f.record(
        Phase::new(
            Role::System,
            Stage::Setup,
            "native_parameters_and_issuer_keygen",
        )
        .encoded(),
        None,
        || {
            let (p, i) = msb::setup(9, rng).map_err(native_error)?;
            let b = wire::encode_parameters(&p);
            Ok(Output::with_messages((p, i), vec![b]))
        },
    )?;
    let registered = f.record(
        Phase::new(
            Role::User,
            Stage::Install,
            "native_parameter_key_checks_fixed_pairings_and_PoK_base_cache",
        ),
        None,
        || Ok(Output::value(msb::register(pp).map_err(native_error)?)),
    )?;
    let user = f.record(
        Phase::new(Role::User, Stage::KeyGeneration, "native_holder_keygen"),
        None,
        || Ok(Output::value(msb::user_keygen(rng))),
    )?;
    let agent = f.record(
        Phase::new(Role::Agent, Stage::KeyGeneration, "native_delegatee_keygen"),
        None,
        || Ok(Output::value(msb::user_keygen(rng))),
    )?;
    let (request, pending) = f.record(
        Phase::new(
            Role::User,
            Stage::IssueRequest,
            "native_issue_first_message",
        )
        .encoded(),
        None,
        || {
            let (q, s) =
                msb::issue_begin(&registered, &user, (101..110).map(S::from).collect(), rng)
                    .map_err(native_error)?;
            let b = wire::encode_issue_request(&q);
            Ok(Output::with_messages((q, s), vec![b]))
        },
    )?;
    let (challenge, verifier) = f.record(
        Phase::new(
            Role::Issuer,
            Stage::VerificationCrypto,
            "live_issue_verifier_challenge",
        )
        .encoded(),
        None,
        || {
            let (c, s) = msb::issue_challenge(&registered, request, rng).map_err(native_error)?;
            let b = c.bytes();
            Ok(Output::with_messages((c, s), vec![b]))
        },
    )?;
    let (answer, pending) = f.record(
        Phase::new(
            Role::User,
            Stage::IssueRequest,
            "live_issue_holder_response",
        )
        .encoded(),
        None,
        || {
            let (a, s) = msb::issue_respond(pending, challenge).map_err(native_error)?;
            let b = a.bytes();
            Ok(Output::with_messages((a, s), vec![b]))
        },
    )?;
    let delivery = f.record(
        Phase::new(Role::Issuer, Stage::IssueResponse, "native_issue_delivery").encoded(),
        None,
        || {
            let d = msb::issue_issuer(&registered, &issuer, verifier, answer, rng)
                .map_err(native_error)?;
            let b = wire::encode_issue_delivery(&d);
            Ok(Output::with_messages(d, vec![b]))
        },
    )?;
    let parent = f.record(
        Phase::new(
            Role::User,
            Stage::IssueAccept,
            "complete_Obtain_random_pairing_key_candidate",
        ),
        None,
        || {
            Ok(Output::value(
                msb::issue_finish_random_pairing_key(&registered, pending, delivery, rng)
                    .map_err(native_error)?,
            ))
        },
    )?;
    let (request, pending) = f.record(
        Phase::new(
            Role::Agent,
            Stage::DelegateRequest,
            "native_delegatee_request",
        )
        .encoded(),
        None,
        || {
            let (q, s) =
                msb::delegate_begin(&registered, &agent, vec![msb::period_attribute()], rng)
                    .map_err(native_error)?;
            let b = wire::encode_delegate_request(&q);
            Ok(Output::with_messages((q, s), vec![b]))
        },
    )?;
    let delivery = f.record(
        Phase::new(Role::User, Stage::DelegateSend, "native_delegator_delivery").encoded(),
        None,
        || {
            let d =
                msb::delegate_sender(&registered, &parent, request, rng).map_err(native_error)?;
            let b = wire::encode_delegate_delivery(&d);
            Ok(Output::with_messages(d, vec![b]))
        },
    )?;
    let child = f.record(
        Phase::new(
            Role::Agent,
            Stage::DelegateReceive,
            "native_delegatee_receive_random_profile",
        ),
        None,
        || {
            Ok(Output::value(
                msb::delegate_finish_random(&registered, pending, delivery, rng)
                    .map_err(native_error)?,
            ))
        },
    )?;
    let disclosed = msb::Disclosure {
        indices: vec![1, 2],
        sets: vec![
            vec![S::from(101), S::from(102)],
            vec![msb::period_attribute()],
        ],
    };
    for &k in ks {
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
                        msb::show_begin_prepared(&registered, p, vec![42; 32]).map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = v.iter().map(|(m, _)| wire::encode_show_first(m)).collect();
                Ok(Output::with_messages(v, b))
            },
        )?;
        let challenges = f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_challenge",
            )
            .encoded(),
            Some(k),
            || {
                let v = firsts
                    .iter()
                    .map(|(m, _)| {
                        msb::show_challenge(&registered, m.clone(), &disclosed, &[42; 32], rng)
                            .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = v.iter().map(|(m, _)| m.bytes()).collect();
                Ok(Output::with_messages(v, b))
            },
        )?;
        let (responses, verifiers) = f.record(
            Phase::new(
                Role::Agent,
                Stage::OnlineGeneration,
                "complete_presentations_live_holder_response",
            )
            .encoded(),
            Some(k),
            || {
                let mut answers = vec![];
                let mut verifiers = vec![];
                for ((_, p), (challenge, v)) in firsts.into_iter().zip(challenges) {
                    answers.push(msb::show_respond(p, challenge).map_err(native_error)?);
                    verifiers.push(v);
                }
                let b = answers.iter().map(|a| a.bytes()).collect();
                Ok(Output::with_messages((answers, verifiers), b))
            },
        )?;
        f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_native_final_random_profile",
            ),
            Some(k),
            || {
                for (v, response) in verifiers.into_iter().zip(responses) {
                    need(
                        msb::show_verify_random(&registered, v, response, rng),
                        "MSB live final",
                    )?;
                }
                Ok(Output::value(()))
            },
        )?;
    }
    Ok(())
}

fn slw_phases(recorder: &mut Recorder, rng: &mut StdRng, ks: &[usize]) -> Result<()> {
    let mut f = Native {
        recorder,
        scheme: Scheme::Slw25,
        attributes: Some(10),
    };
    let (pk, issuer) = f.record(
        Phase::new(
            Role::System,
            Stage::Setup,
            "flat_revocation_disabled_native_setup_and_local_install",
        )
        .encoded(),
        None,
        || {
            let (p, i) = slw::setup(10, rng).map_err(native_error)?;
            let b = p.encode();
            Ok(Output::with_messages((p, i), vec![b]))
        },
    )?;
    let pk = f.record(
        Phase::new(
            Role::Verifier,
            Stage::Install,
            "fresh_role_public_key_decode_checks_and_issuer_binding_cache",
        )
        .encoded()
        .decoded(),
        None,
        || {
            Ok(Output::value(
                slw::PublicKey::decode_install_profile(
                    &pk.encode(),
                    slw::VerificationMode::Randomized,
                    rng,
                )
                .map_err(native_error)?,
            ))
        },
    )?;
    let user = f.record(
        Phase::new(Role::User, Stage::KeyGeneration, "native_holder_secrets"),
        None,
        || Ok(Output::value(slw::Holder::generate(rng))),
    )?;
    let agent = f.record(
        Phase::new(
            Role::Agent,
            Stage::KeyGeneration,
            "native_delegatee_secrets",
        ),
        None,
        || Ok(Output::value(slw::Holder::generate(rng))),
    )?;
    let attrs = (100..110).map(S::from).collect::<Vec<_>>();
    let (mut pending, request) = f.record(
        Phase::new(Role::User, Stage::IssueRequest, "native_issue_request").encoded(),
        None,
        || {
            let v = slw::issue_prepare(&pk, &user, &attrs).map_err(native_error)?;
            let b = v.1.clone();
            Ok(Output::with_messages(v, vec![b]))
        },
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
            let v = slw::issuer_issue_challenge(verifier, &second, rng).map_err(native_error)?;
            let b = v.1.clone();
            Ok(Output::with_messages(v, vec![b]))
        },
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
            let v = slw::issuer_issue_finish(&pk, &issuer, verifier, &fourth, rng)
                .map_err(native_error)?;
            Ok(Output::with_messages(v.clone(), vec![v]))
        },
    )?;
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
                    &(2..12).collect::<Vec<_>>(),
                    &attrs,
                    slw::VerificationMode::Randomized,
                    rng,
                )
                .map_err(native_error)?,
            ))
        },
    )?;
    let keep = (2..12).collect::<Vec<_>>();
    let (mut pending, prefix) = f.record(
        Phase::new(
            Role::User,
            Stage::DelegateSend,
            "native_delegate_preparation_and_prefix",
        )
        .encoded(),
        None,
        || {
            let v = slw::delegate_prepare(&pk, &user, &parent, &keep, rng).map_err(native_error)?;
            let b = v.1.clone();
            Ok(Output::with_messages(v, vec![b]))
        },
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
    let (verifier, third) = f.record(
        Phase::new(Role::User, Stage::DelegateSend, "live_delegator_challenge")
            .encoded()
            .decoded(),
        None,
        || {
            let v = slw::delegator_challenge(verifier, &second, rng).map_err(native_error)?;
            let b = v.1.clone();
            Ok(Output::with_messages(v, vec![b]))
        },
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
                    slw::VerificationMode::Randomized,
                    rng,
                )
                .map_err(native_error)?,
            ))
        },
    )?;
    let disclosed = [2, 3, 4];
    let values = [S::from(100), S::from(101), S::from(102)];
    for &k in ks {
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
                                &pk,
                                &agent,
                                &child,
                                &disclosed,
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
                let b = prepared.iter().map(|(_, prefix)| prefix.clone()).collect();
                Ok(Output::with_messages(prepared, b))
            },
        )?;
        let verifiers = f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_begin",
            )
            .encoded()
            .decoded(),
            Some(k),
            || {
                let v = prepared
                    .iter()
                    .map(|(_, prefix)| {
                        slw::show_verifier_begin_profile(
                            &pk,
                            prefix,
                            &disclosed,
                            &values,
                            slw::VerificationMode::Randomized,
                            rng,
                        )
                        .map_err(native_error)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let b = v.iter().map(|(_, msg)| msg.clone()).collect();
                Ok(Output::with_messages(v, b))
            },
        )?;
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
        let (provers, verifiers, thirds) = f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_verifier_challenge",
            )
            .encoded()
            .decoded(),
            Some(k),
            || {
                let mut ps = vec![];
                let mut vs = vec![];
                let mut messages = vec![];
                for ((p, second), v) in provers.into_iter().zip(verifiers) {
                    let (v, msg) = slw::show_verifier_challenge_profile(v, &second, rng)
                        .map_err(native_error)?;
                    ps.push(p);
                    vs.push(v);
                    messages.push(msg);
                }
                Ok(Output::with_messages((ps, vs, messages.clone()), messages))
            },
        )?;
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
        f.record(
            Phase::new(
                Role::Verifier,
                Stage::VerificationCrypto,
                "complete_presentations_live_native_final_random_profile",
            )
            .decoded(),
            Some(k),
            || {
                for (v, m) in verifiers.into_iter().zip(responses) {
                    need(
                        slw::show_verifier_finish_profile(v, &m, rng).map_err(native_error)?,
                        "SLW live final",
                    )?;
                }
                Ok(Output::value(()))
            },
        )?;
    }
    Ok(())
}

pub fn run() -> Result<Vec<Value>> {
    run_grid(&[1, 16, 64])
}
fn run_grid(ks: &[usize]) -> Result<Vec<Value>> {
    let mut recorder = Recorder::new(Mode::ClockFree).map_err(native_error)?;
    let mut rng = StdRng::seed_from_u64(214_901);
    sma_phases(&mut recorder, &mut rng, ks)?;
    niat_phases(&mut recorder, &mut rng, ks)?;
    cpat_phases(&mut recorder, &mut rng, ks)?;
    hin_phases(&mut recorder, &mut rng, ks)?;
    msb_phases(&mut recorder, &mut rng, ks)?;
    slw_phases(&mut recorder, &mut rng, ks)?;
    let mut rows=recorder.into_records().into_iter().map(|r|{
        let dac=matches!(r.label.scheme,Scheme::Msb23|Scheme::Slw25);
        json!({"task":"runtime-check","phase":"native_role_phase","source":"fresh_protocol_execution",
            "timing_enabled":false,"formal_samples":0,"record":r,
            "workload_semantics":if dac {"one_presentation_or_k_complete_native_sessions_not_native_quota"} else {"native_wallet_or_independent_token_units_as_declared"}})
    }).collect::<Vec<_>>();
    rows.push(json!({"task":"runtime-check","phase":"native_role_phase_coverage","timing_enabled":false,"formal_samples":0,
        "schemes":["SMA²RT","NIAT","CPAT","HinToken","MSB+23","SLW+25"],"presentation_k":ks,
        "known_policy_main_paths":true,"native_live_interaction_preserved":true,"slw_revocation_enabled":false,
        "candidate_verification_rows_are_alternatives_not_additive":true,
        "cache_label_semantics":"installed public parameters and fixed relation caches; one-use nonces and prepared materials are freshly generated",
        "all_formal_role_stage_instrumentation_complete":false,"formal_runner_implemented":false,
        "omitted_or_separate":[
            "shared state/inclusive failure-runtime is checked separately; these cryptographic phases exclude state",
            "CPAT request/response/public-key full codecs are absent; actual wire byte fields are null, never payload-size estimates",
            "NIAT and HinToken have no native Show preparation stage; their issued tokens are sent by OnlineGeneration",
            "MSB/SLW k1 is one native presentation; k16/k64 are complete sessions, not quota spending",
            "cold-hot caches and all codec/subgroup/HtoG/polynomial/field/Sigma inner subcallbacks are not fully decomposed here",
            "wire flags describe explicit outer message codec calls; canonicalization internal to native FS hashing remains within its native callback",
            "no statistical sampler, timings, network or persistent storage execution is part of this collector"
        ]}));
    Ok(rows)
}

#[cfg(test)]
mod tests {
    #[test]
    fn real_native_role_callbacks_are_clock_free_and_keep_unknown_bytes_null() {
        let rows = super::run_grid(&[1]).unwrap();
        let records = rows
            .iter()
            .filter(|r| r["phase"] == "native_role_phase")
            .collect::<Vec<_>>();
        assert!(!records.is_empty());
        for row in &records {
            assert_eq!(row["record"]["callback_completed"], true);
            assert_eq!(row["timing_enabled"], false);
            assert_eq!(row["formal_samples"], 0);
            assert_eq!(row["record"]["mode"], "clock_free");
            assert!(row["record"].get("elapsed_ms").is_none());
        }
        let cp = records
            .iter()
            .find(|r| {
                r["record"]["label"]["profile"]
                    == "native_k_independent_pretoken_requests_no_full_codec"
            })
            .unwrap();
        assert!(cp["record"]["actual_wire_bytes"].is_null());
        let cp = records
            .iter()
            .find(|r| r["record"]["label"]["profile"] == "present_already_prepared_tokens")
            .unwrap();
        let c = &cp["record"]["counts"]["baseline"];
        assert_eq!(c["e1"], 0);
        assert_eq!(c["e2"], 0);
        assert_eq!(c["p"], 0);
        let slw = records
            .iter()
            .find(|r| {
                r["record"]["label"]["profile"]
                    == "complete_presentations_check_fresh_opening_and_respond"
            })
            .unwrap();
        assert!(slw["record"]["counts"]["baseline"]["p"].as_u64().unwrap() > 0);
    }
}
