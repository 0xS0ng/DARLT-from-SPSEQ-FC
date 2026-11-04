//! Clock-free integration of native cryptography, shared state and fallback.
//! Fresh-protocol correctness workloads without retained timing samples.
use crate::{
    adapters,
    batch_runtime::{self as runtime, Adapter, Mode},
    common::spent::SpentStore,
    common::state::StateError,
    darlt::{context::ProtocolContext, protocol, spend},
    ops,
};
use baseline_core::{
    arithmetic::{G1, S},
    bhn26 as niat, encoding, hintoken as hin, klo26 as cpat,
    msb23::{pok, scheme as msb},
    pairing_verify, slw25 as slw, sma2rt as sma,
};
use ff::Field;
use group::Group;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{collections::BTreeSet, sync::Arc};

pub const K_VALUES: [usize; 14] = [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 96, 128];

fn need(value: bool, message: &str) -> Result<(), String> {
    if value {
        Ok(())
    } else {
        Err(message.into())
    }
}

fn count<T>(rows: &mut Vec<Value>, mut row: Value, action: impl FnOnce() -> T) -> T {
    let darlt = row["scheme"] == "DARLT";
    if darlt {
        ops::reset();
    } else {
        encoding::start_counts();
    }
    let result = action();
    let enabled = !darlt || cfg!(feature = "op-counts");
    let counters = if darlt {
        let c = ops::stop();
        if enabled {
            json!(c)
        } else {
            Value::Null
        }
    } else {
        json!(encoding::stop_counts())
    };
    row["task"] = json!("runtime-check");
    row["source"] = json!("fresh_protocol_execution");
    row["timing_enabled"] = json!(false);
    row["formal_samples"] = json!(0);
    row["counter_backend"] = json!(if darlt {
        "darlt-feature"
    } else {
        "baseline-runtime"
    });
    row["op_counts_enabled"] = json!(enabled);
    row["value_type"] = json!(if enabled {
        "execution_count"
    } else {
        "correctness"
    });
    row["counts"] = counters;
    rows.push(row);
    result
}

fn semantics(scheme: &str) -> &'static str {
    match scheme {
        "MSB+23" | "SLW+25" => {
            "application_completed_presentation_replay_identifier_not_native_quota"
        }
        "NIAT" => "complete_native_two_point_redemption_tag",
        "HinToken" => "complete_native_three_point_normalized_message",
        "CPAT" => "complete_native_service_tag_and_delta",
        _ => "native_unit_serial",
    }
}

fn store(history: usize, namespace: &[u8], id_bytes: usize) -> Result<SpentStore, String> {
    // Same implementation and occupancy, with each issuer's complete native
    // identifier width. Historical records are synthetic storage fixtures.
    SpentStore::with_preexisting_records(history, namespace, id_bytes).map_err(|e| e.to_string())
}

fn grid_row<A: Adapter>(
    rows: &mut Vec<Value>,
    adapter: &A,
    items: &[A::Item],
    k: usize,
    variant: &str,
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let ids = adapter.identifiers(items)?;
    need(!ids.is_empty(), "empty native identifiers")?;
    let lengths = ids.iter().map(Vec::len).collect::<BTreeSet<_>>();
    let bytes = items
        .iter()
        .flat_map(|x| adapter.wire_messages(x))
        .map(|x| x.len())
        .sum::<usize>();
    for mode in [Mode::Specification, Mode::Randomized] {
        let state = store(history, adapter.namespace(), ids[0].len())?;
        let result = count(
            rows,
            json!({"scheme":adapter.scheme(),"phase":"runtime_verify_and_record",
            "variant":variant,"profile":format!("{mode:?}"),"k_requested":k,"native_objects":items.len(),
            "identifiers":ids.len(),"identifier_byte_lengths":lengths,"identifier_semantics":semantics(adapter.scheme()),
            "history_records":history,"history_id_bytes":ids[0].len(),"history_fixture":"synthetic_storage_records_under_active_issuer_namespace","wire_bytes":bytes,
            "wire_boundary":"sum_of_native_protocol_messages_no_application_state_frames",
            "state_binding_sha256":format!("{:x}",Sha256::digest(runtime::bound_request(adapter,items,b"grid-probe")))}),
            || {
                runtime::verify_and_record(
                    adapter,
                    items,
                    b"grid-probe",
                    b"accepted",
                    &state,
                    mode,
                    rng,
                )
            },
        );
        let result =
            result.map_err(|e| format!("{} {variant} k={k} {mode:?}: {e}", adapter.scheme()))?;
        need(
            result.newly_registered == ids.len() && !result.replayed,
            "honest runtime registration mismatch",
        )?;
        need(
            state.counts().map_err(|e| e.to_string())? == (history + 1, history + ids.len()),
            "honest runtime state count mismatch",
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn state_cases<A: Adapter>(
    rows: &mut Vec<Value>,
    adapter: &A,
    items: &[A::Item],
    variant: &str,
    history: usize,
    copy: impl Fn(&A::Item) -> Result<A::Item, String>,
    tamper: impl Fn(&A::Item) -> Result<A::Item, String>,
    rng: &mut StdRng,
) -> Result<(), String> {
    need(
        items.len() >= 4,
        "state cases require four genuine native objects",
    )?;
    let ids = adapter.identifiers(&items[..2])?;
    need(!ids.is_empty(), "empty state-case identifiers")?;
    let state = store(history, adapter.namespace(), ids[0].len())?;
    let base = state.counts().map_err(|e| e.to_string())?;
    let meta = |phase: &str| {
        json!({"scheme":adapter.scheme(),"phase":phase,"variant":variant,
        "profile":"Randomized","history_records":history,"history_id_bytes":ids[0].len(),"history_fixture":"synthetic_storage_records_under_active_issuer_namespace","identifier_semantics":semantics(adapter.scheme())})
    };
    let first = count(rows, meta("runtime_honest_accept"), || {
        runtime::verify_and_record(
            adapter,
            &items[..2],
            b"first",
            b"original-response",
            &state,
            Mode::Randomized,
            rng,
        )
    })
    .map_err(|e| e.to_string())?;
    need(
        first.newly_registered == ids.len(),
        "native identifier count was lost",
    )?;
    let after = state.counts().map_err(|e| e.to_string())?;
    need(
        after == (base.0 + 1, base.1 + ids.len()),
        "initial native commit was not atomic",
    )?;
    let retry = count(rows, meta("runtime_exact_retry"), || {
        runtime::verify_and_record(
            adapter,
            &items[..2],
            b"first",
            b"replacement-response",
            &state,
            Mode::Randomized,
            rng,
        )
    })
    .map_err(|e| e.to_string())?;
    need(
        retry.replayed && retry.newly_registered == 0 && retry.response == b"original-response",
        "exact retry did not retain original response",
    )?;
    let conflict = count(rows, meta("runtime_same_ids_new_request"), || {
        runtime::verify_and_record(
            adapter,
            &items[..2],
            b"different",
            b"",
            &state,
            Mode::Randomized,
            rng,
        )
    });
    need(
        matches!(conflict, Err(runtime::Error::State(StateError::SerialUsed))),
        "same identifiers under another request were accepted",
    )?;
    let overlap = count(
        rows,
        meta("runtime_used_and_fresh_no_prefix_commit"),
        || {
            runtime::verify_and_record(
                adapter,
                &items[1..3],
                b"partial-overlap",
                b"",
                &state,
                Mode::Randomized,
                rng,
            )
        },
    );
    need(
        matches!(overlap, Err(runtime::Error::State(StateError::SerialUsed))),
        "partial used state was not rejected",
    )?;
    need(
        state.counts().map_err(|e| e.to_string())? == after,
        "state conflict committed a prefix",
    )?;
    for bad_indices in [vec![1usize], vec![1, 3]] {
        let bad = items[..4]
            .iter()
            .enumerate()
            .map(|(i, x)| {
                if bad_indices.contains(&i) {
                    tamper(x)
                } else {
                    copy(x)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let clean = store(history, adapter.namespace(), ids[0].len())?;
        let mut row = meta("runtime_bad_proof_localization");
        row["expected_bad_indices"] = json!(bad_indices);
        let failed = count(rows, row, || {
            runtime::verify_and_record(
                adapter,
                &bad,
                b"bad-batch",
                b"",
                &clean,
                Mode::Randomized,
                rng,
            )
        });
        let diagnosis = match failed {
            Err(runtime::Error::CryptoRejected(d)) => d,
            _ => return Err("bad proof batch did not fail cryptographic verification".into()),
        };
        need(
            diagnosis.bad_indices == bad_indices,
            "shared fallback localized wrong native objects",
        )?;
        need(
            clean.counts().map_err(|e| e.to_string())? == base,
            "bad proof committed a good prefix",
        )?;
        rows.last_mut().unwrap()["diagnosis"] = json!(diagnosis);
    }
    let duplicated = vec![copy(&items[0])?, copy(&items[0])?];
    let clean = store(history, adapter.namespace(), ids[0].len())?;
    let failure = count(rows, meta("runtime_complete_identifier_duplicate"), || {
        runtime::verify_and_record(
            adapter,
            &duplicated,
            b"duplicated",
            b"",
            &clean,
            Mode::Randomized,
            rng,
        )
    });
    let diagnosis = match failure {
        Err(runtime::Error::CryptoRejected(d)) => d,
        _ => return Err("duplicate native identifiers not rejected".into()),
    };
    need(
        diagnosis.bad_indices == [0, 1] && diagnosis.reason == "duplicate complete identifiers",
        "duplicate diagnosis mismatch",
    )?;
    need(
        clean.counts().map_err(|e| e.to_string())? == base,
        "duplicate batch changed state",
    )?;
    rows.last_mut().unwrap()["diagnosis"] = json!(diagnosis);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn independent<A: Adapter>(
    rows: &mut Vec<Value>,
    adapter: &A,
    items: &[A::Item],
    grid: &[usize],
    variant: &str,
    history: usize,
    copy: impl Fn(&A::Item) -> Result<A::Item, String>,
    tamper: impl Fn(&A::Item) -> Result<A::Item, String>,
    rng: &mut StdRng,
) -> Result<(), String> {
    for &k in grid {
        grid_row(rows, adapter, &items[..k], k, variant, history, rng)?;
    }
    state_cases(rows, adapter, items, variant, history, copy, tamper, rng)
}

fn darlt(
    rows: &mut Vec<Value>,
    grid: &[usize],
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let pp = Arc::new(protocol::PublicParameters::setup(
        1024,
        16,
        64,
        6,
        4,
        b"native-runtime",
        rng,
    )?);
    let (ip, sk) = protocol::keygen(&pp, rng)?;
    let ip = Arc::new(ip);
    let context = ProtocolContext::new(pp.clone(), ip.clone())?;
    let (q, secrets) = protocol::prepare_request(
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
        rng,
    )?;
    let response = protocol::issue(&pp, &ip, &sk, &q, 1, rng)?;
    let mut wallet = protocol::accept(&pp, &ip, &q, &secrets, &response, rng)?;
    let child = context.self_derive(
        &mut wallet,
        b"runtime-child",
        &(0..8).collect::<Vec<_>>(),
        rng,
    )?;
    let policy = spend::Policy {
        period: 1,
        atoms: vec![
            spend::Atom::Equal(0, S::ONE),
            spend::Atom::Reveal(1, S::from(21)),
            spend::Atom::Reveal(2, S::from(22)),
        ],
    };
    let challenge = [0x42; 32];
    let mint = |positions: &[usize], r: &mut StdRng| -> Result<spend::Token, String> {
        // Each point uses an independent workload with a fresh
        // verifier store, not repeated consumption in one production wallet.
        let mut holder = child.holder.clone();
        let prepared =
            spend::prepare_spend_installed(&pp, &ip, &mut holder, positions, &policy, r)?;
        let token = spend::finish_spend(&pp, &ip, prepared, &challenge, r)?;
        spend::Token::wire_decode(&pp, &token.wire_encode())
    };
    let adapter = adapters::Darlt::new(&context);
    let per_block = adapters::Darlt::per_block(&context);
    for &k in grid {
        let positions = spend::select_sequential_units(&pp, &child.holder, &BTreeSet::new(), k)?;
        let shapes=positions.chunks(pp.k_max).map(|p| {
            let s=spend::query_shape(&pp,p)?;
            Ok(json!({"units":s.units,"distinct_pools":s.distinct_pools,"distinct_offsets":s.distinct_offsets,"first_pool_offset":s.first_pool_offset,"child_group":0}))
        }).collect::<Result<Vec<Value>,String>>()?;
        let blocks = positions
            .chunks(64)
            .map(|x| mint(x, rng))
            .collect::<Result<Vec<_>, _>>()?;
        let first = rows.len();
        grid_row(
            rows,
            &adapter,
            &blocks,
            k,
            "native-blocks-cross-token-random-runtime",
            history,
            rng,
        )?;
        grid_row(
            rows,
            &per_block,
            &blocks,
            k,
            "native-blocks-per-block-random-runtime",
            history,
            rng,
        )?;
        for row in &mut rows[first..] {
            row["native_query_shapes"] = json!(shapes);
            row["unit_selection"] = json!("fresh_alternative_workload_sequential_pools_one_child");
        }
    }
    let maximum = grid.iter().copied().max().unwrap_or(0).max(4);
    let singles = (0..maximum)
        .map(|i| mint(&[i], rng))
        .collect::<Result<Vec<_>, _>>()?;
    for &k in grid {
        let first = rows.len();
        grid_row(
            rows,
            &adapter,
            &singles[..k],
            k,
            "k-independent-single-unit-tokens-shared-state",
            history,
            rng,
        )?;
        let shapes=(0..k).map(|i| {
            let s=spend::query_shape(&pp,&[i])?;
            Ok(json!({"units":s.units,"distinct_pools":s.distinct_pools,"distinct_offsets":s.distinct_offsets,"first_pool_offset":s.first_pool_offset,"child_group":0}))
        }).collect::<Result<Vec<Value>,String>>()?;
        for row in &mut rows[first..] {
            row["native_query_shapes"] = json!(shapes);
            row["unit_selection"] =
                json!("fresh_alternative_workload_sequential_pools_independent_single_unit_tokens");
        }
    }
    state_cases(
        rows,
        &adapter,
        &singles,
        "native-one-unit-state-cases",
        history,
        |x| Ok(x.clone()),
        |x| {
            let mut t = x.clone();
            t.proof.z[0] += S::ONE;
            Ok(t)
        },
        rng,
    )?;
    if grid.iter().any(|&k| k > 64) {
        let a = mint(&(0..64).collect::<Vec<_>>(), rng)?;
        let b = mint(&(32..96).collect::<Vec<_>>(), rng)?;
        need(
            context.valid(&a, crate::darlt::verification::Mode::Specification, rng)
                && context.valid(&b, crate::darlt::verification::Mode::Specification, rng),
            "individual native blocks are invalid",
        )?;
        let clean = store(history, adapter.namespace(), 48)?;
        let failed = count(
            rows,
            json!({"scheme":"DARLT","phase":"runtime_valid_blocks_overlap_rejected",
            "k_requested":128,"native_objects":2,"individually_valid":true,"overlapping_units":32,"history_records":history}),
            || {
                runtime::verify_and_record(
                    &adapter,
                    &[a, b],
                    b"overlapping-native-blocks",
                    b"",
                    &clean,
                    Mode::Randomized,
                    rng,
                )
            },
        );
        let d = match failed {
            Err(runtime::Error::CryptoRejected(d)) => d,
            _ => return Err("overlapping valid native blocks were accepted".into()),
        };
        need(
            d.bad_indices == [0, 1],
            "cross-block duplicate localization mismatch",
        )?;
        need(
            clean.counts().map_err(|e| e.to_string())? == (history, history),
            "cross-block duplicates changed state",
        )?;
        rows.last_mut().unwrap()["diagnosis"] = json!(d);

        // The block-level fallback and state transaction must cover the entire
        // 128-unit presentation, including a failure in its second block.
        let first = mint(&(0..64).collect::<Vec<_>>(), rng)?;
        let second = mint(&(64..128).collect::<Vec<_>>(), rng)?;
        need(
            context.valid(&first, crate::darlt::verification::Mode::Specification, rng)
                && context.valid(
                    &second,
                    crate::darlt::verification::Mode::Specification,
                    rng,
                ),
            "disjoint native 64-unit blocks are invalid",
        )?;
        for (candidate, variant) in [
            (&adapter, "native-blocks-cross-token-random-runtime"),
            (&per_block, "native-blocks-per-block-random-runtime"),
        ] {
            let clean = store(history, candidate.namespace(), 48)?;
            let mut bad_second = second.clone();
            bad_second.proof.z[0] += S::ONE;
            let failed = count(
                rows,
                json!({"scheme":"DARLT","phase":"runtime_bad_second_64_unit_block",
                "variant":variant,"profile":"Randomized","k_requested":128,"native_objects":2,
                "expected_bad_indices":[1],"history_records":history,"history_id_bytes":48,
                "history_fixture":"synthetic_storage_records_under_active_issuer_namespace"}),
                || {
                    runtime::verify_and_record(
                        candidate,
                        &[first.clone(), bad_second],
                        b"bad-second-native-block",
                        b"",
                        &clean,
                        Mode::Randomized,
                        rng,
                    )
                },
            );
            let diagnosis = match failed {
                Err(runtime::Error::CryptoRejected(d)) => d,
                _ => return Err("bad second native block was accepted".into()),
            };
            need(
                diagnosis.bad_indices == [1],
                "second native block fallback localized wrong block",
            )?;
            need(
                clean.counts().map_err(|e| e.to_string())? == (history, history),
                "bad second native block committed the first block",
            )?;
            rows.last_mut().unwrap()["diagnosis"] = json!(diagnosis);

            let seeded = store(history, candidate.namespace(), 48)?;
            let second_ids = candidate.identifiers(std::slice::from_ref(&second))?;
            need(second_ids.len() == 64, "second block lost native serials")?;
            let used_unit = singles
                .get(64)
                .ok_or("second-block history needs a genuine single-unit token")?;
            let used_ids = candidate.identifiers(std::slice::from_ref(used_unit))?;
            need(
                used_ids.len() == 1 && second_ids.contains(&used_ids[0]),
                "historical native unit does not belong to second block",
            )?;
            runtime::verify_and_record(
                candidate,
                std::slice::from_ref(used_unit),
                b"verified-native-second-block-history",
                b"accepted",
                &seeded,
                Mode::Specification,
                rng,
            )
            .map_err(|e| e.to_string())?;
            let before = seeded.counts().map_err(|e| e.to_string())?;
            let failure = count(
                rows,
                json!({"scheme":"DARLT","phase":"runtime_used_second_block_no_first_block_commit",
                "variant":variant,"profile":"Randomized","k_requested":128,"native_objects":2,
                "history_records":history,"history_id_bytes":48,"additional_preexisting_native_serials":1,
                "used_serial_origin":"accepted_genuine_single_unit_token_overlapping_second_native_block"}),
                || {
                    runtime::verify_and_record(
                        candidate,
                        &[first.clone(), second.clone()],
                        b"used-second-native-block",
                        b"",
                        &seeded,
                        Mode::Randomized,
                        rng,
                    )
                },
            );
            need(
                matches!(failure, Err(runtime::Error::State(StateError::SerialUsed))),
                "previously used second block serial did not reject whole presentation",
            )?;
            need(
                seeded.counts().map_err(|e| e.to_string())? == before,
                "second-block state conflict committed a first-block prefix",
            )?;
        }
    }
    Ok(())
}

fn sma(
    rows: &mut Vec<Value>,
    grid: &[usize],
    max: usize,
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let pp = sma::setup(10, 1024);
    let issuer = sma::ikeygen(&pp, rng);
    let reader = sma::vkeygen(&pp, rng);
    let user = sma::ukeygen(rng);
    let installed = sma::install_instance(&pp, &issuer, &reader).map_err(str::to_owned)?;
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
    let (wallet, _, _) =
        sma::issue(&pp, &issuer, &reader, &user, &attrs, &policy, 0, rng).map_err(str::to_owned)?;
    let context = [0x42; 32];
    let tokens = (0..max)
        .map(|i| {
            sma::show_installed(&installed, &wallet, i as u64, &context, &policy, rng)
                .map_err(str::to_owned)
        })
        .collect::<Result<Vec<_>, _>>()?;
    independent(
        rows,
        &adapters::Sma::new(&installed, &policy, &context),
        &tokens,
        grid,
        "verifier-random-fhs",
        history,
        |x| Ok(x.clone()),
        |x| {
            let mut t = x.clone();
            t.proof.z[0] += S::ONE;
            Ok(t)
        },
        rng,
    )
}

fn niat(
    rows: &mut Vec<Value>,
    grid: &[usize],
    max: usize,
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let keys = niat::IssuerKeys::generate(rng);
    let installed = keys.install().map_err(|e| e.to_string())?;
    let client = niat::ClientKeys::generate(rng);
    let tokens = (0..max)
        .map(|i| {
            let response = niat::issue(
                &installed,
                &keys.secret,
                client.public_key(),
                (i % 2) as u8,
                rng,
            )?;
            niat::obtain(&installed, &client, &response, rng)
        })
        .collect::<niat::Result<Vec<_>>>()
        .map_err(|e| e.to_string())?;
    for (variant, label) in [
        (
            niat::RedemptionBatch::RandomSecondEquation,
            "native-C3-random-eq2",
        ),
        (niat::RedemptionBatch::RandomFhs, "verifier-random-fhs"),
        (
            niat::RedemptionBatch::RandomFhsCachedAnchor,
            "verifier-random-fhs-cached-anchor",
        ),
    ] {
        independent(
            rows,
            &adapters::Niat::new(&installed, variant)?,
            &tokens,
            grid,
            label,
            history,
            |x| Ok(x.clone()),
            |x| {
                let mut t = x.clone();
                t.signature.z += G1::generator();
                Ok(t)
            },
            rng,
        )?;
    }
    Ok(())
}

fn cpat(
    rows: &mut Vec<Value>,
    grid: &[usize],
    max: usize,
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let issuer = cpat::keygen(rng);
    let key = cpat::validate_key(&issuer.pk).map_err(str::to_owned)?;
    let tag = [0x55; 32].to_vec();
    let metadata = [0x66; 32];
    let policy = cpat::Policy {
        allowed: BTreeSet::from([tag.clone()]),
    };
    let tokens = (0..max)
        .map(|i| {
            let (request, pending) = cpat::request(&key, &metadata, rng);
            let response = cpat::issue_installed(&key, &issuer, &request, &metadata, i % 2, rng)?;
            let wallet = cpat::receive(pending, &response)?;
            cpat::show(&key, &wallet, &tag, rng)
        })
        .collect::<cpat::Result<Vec<_>>>()
        .map_err(str::to_owned)?;
    for (adapter, label) in [
        (
            adapters::Cpat::new(&key, &policy, &metadata),
            "verifier-random-fhs-same-metadata",
        ),
        (
            adapters::Cpat::four_coordinate(&key, &policy, &metadata),
            "verifier-random-fhs-four-coordinate",
        ),
    ] {
        independent(
            rows,
            &adapter,
            &tokens,
            grid,
            label,
            history,
            |x| Ok(x.clone()),
            |x| {
                let mut t = x.clone();
                t.sig.z += G1::generator();
                Ok(t)
            },
            rng,
        )?;
    }
    Ok(())
}

fn msb_disclosure() -> msb::Disclosure {
    msb::Disclosure {
        indices: vec![1, 2],
        sets: vec![
            vec![S::from(21), S::from(22)],
            vec![msb::period_attribute()],
        ],
    }
}
fn msb_record(
    v: &msb::Registered,
    c: &msb::Credential,
    rng: &mut StdRng,
) -> Result<msb::FrozenShow, String> {
    let d = msb_disclosure();
    let context = vec![0x42; 32];
    let (first, ps) = msb::show_begin(v, c, d.clone(), context.clone(), rng)?;
    let (challenge, vs) = msb::show_challenge(v, first, &d, &context, rng)?;
    let response = msb::show_respond(ps, challenge)?;
    msb::freeze_show(v, vs, response)
}
fn msb_copy(x: &msb::FrozenShow) -> Result<msb::FrozenShow, String> {
    x.with_response_bytes(&x.wire_messages()[2])
}
fn msb_bad(x: &msb::FrozenShow) -> Result<msb::FrozenShow, String> {
    let mut response = pok::Response::from_bytes(&x.wire_messages()[2]).map_err(str::to_owned)?;
    response.responses[0] += S::ONE;
    x.with_response_bytes(&response.bytes())
}
fn msb(
    rows: &mut Vec<Value>,
    grid: &[usize],
    max: usize,
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let (pp, issuer) = msb::setup(9, rng)?;
    let key = msb::register(pp)?;
    let user = msb::user_keygen(rng);
    let agent = msb::user_keygen(rng);
    let attrs = vec![
        S::from(21),
        S::from(22),
        S::from(23),
        S::from(24),
        S::from(25),
        S::from(26),
        S::from(27),
        S::from(28),
        S::from(29),
    ];
    let (request, state) = msb::issue_begin(&key, &user, attrs, rng)?;
    let (challenge, vs) = msb::issue_challenge(&key, request, rng)?;
    let (response, state) = msb::issue_respond(state, challenge)?;
    let delivery = msb::issue_issuer(&key, &issuer, vs, response, rng)?;
    let parent = msb::issue_finish_random(&key, state, delivery, rng)?;
    let (request, state) = msb::delegate_begin(&key, &agent, vec![msb::period_attribute()], rng)?;
    let delivery = msb::delegate_sender(&key, &parent, request, rng)?;
    let child = msb::delegate_finish_random(&key, state, delivery, rng)?;
    let records = (0..max)
        .map(|_| msb_record(&key, &child, rng))
        .collect::<Result<Vec<_>, _>>()?;
    independent(
        rows,
        &adapters::Msb::new(&key),
        &records,
        grid,
        "full-signature-and-across-set-random-native-PoK",
        history,
        msb_copy,
        msb_bad,
        rng,
    )?;
    for mode in [Mode::Specification, Mode::Randomized] {
        let d = msb_disclosure();
        let context = vec![0x42; 32];
        let (first, ps) = msb::show_begin(&key, &child, d.clone(), context.clone(), rng)?;
        let (challenge, vs) = count(
            rows,
            json!({"scheme":"MSB+23","phase":"live_verifier_challenge","profile":format!("{mode:?}"),"k_requested":1,
            "boundary":"native_interactive_verifier_phase_not_frozen_recheck"}),
            || msb::show_challenge(&key, first, &d, &context, rng),
        )?;
        let response = msb::show_respond(ps, challenge)?;
        let accepted = count(
            rows,
            json!({"scheme":"MSB+23","phase":"live_verifier_finish","profile":format!("{mode:?}"),"k_requested":1,
            "boundary":"strict_received_proof_freeze_native_PoK_and_all_pairing_equations"}),
            || {
                let frozen = msb::freeze_show(&key, vs, response)?;
                Ok::<_, String>(msb::verify_frozen_show(
                    &key,
                    &frozen,
                    if mode == Mode::Specification {
                        pairing_verify::Mode::Specification
                    } else {
                        pairing_verify::Mode::Randomized
                    },
                    rng,
                ))
            },
        )?;
        need(accepted, "live MSB verification failed")?;
    }
    Ok(())
}

fn slw(
    rows: &mut Vec<Value>,
    grid: &[usize],
    max: usize,
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let (key, issuer) = slw::setup(10, rng).map_err(|e| e.to_string())?;
    let user = slw::Holder::generate(rng);
    let agent = slw::Holder::generate(rng);
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
    let (parent, _) = slw::run_issue_profile(
        &key,
        &issuer,
        &user,
        &attrs,
        pairing_verify::Mode::Randomized,
        rng,
    )
    .map_err(|e| e.to_string())?;
    let (child, _) = slw::run_delegate_profile(
        &key,
        &user,
        &agent,
        &parent,
        &[2, 3, 4, 5, 6, 7],
        pairing_verify::Mode::Randomized,
        rng,
    )
    .map_err(|e| e.to_string())?;
    let records = (0..max)
        .map(|_| {
            slw::run_show_frozen(
                &key,
                &agent,
                &child,
                &[2, 3, 4],
                pairing_verify::Mode::Randomized,
                rng,
            )
            .map_err(|e| e.to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    independent(
        rows,
        &adapters::Slw::new(&key),
        &records,
        grid,
        "full-purge-and-CDM-random-fixed-session-recheck",
        history,
        |x| Ok(x.clone()),
        |x| {
            let mut p4 =
                baseline_core::cdm::PFourth::decode(&x.messages()[4]).map_err(|e| e.to_string())?;
            p4.true_responses[0] += S::ONE;
            Ok(x.with_final_message(&p4.encode()))
        },
        rng,
    )?;
    for mode in [Mode::Specification, Mode::Randomized] {
        let profile = if mode == Mode::Specification {
            pairing_verify::Mode::Specification
        } else {
            pairing_verify::Mode::Randomized
        };
        let mut prep =
            slw::show_precompute(&key, &agent, &child, rng).map_err(|e| e.to_string())?;
        let (mut prep, prefix) = slw::show_bind_profile(&key, &mut prep, &[2, 3, 4], profile)
            .map_err(|e| e.to_string())?;
        let meta = |phase| {
            json!({"scheme":"SLW+25","phase":phase,"profile":format!("{mode:?}"),"k_requested":1,
            "boundary":"native_interactive_verifier_phase_not_frozen_recheck"})
        };
        let (vs, v1) = count(rows, meta("live_verifier_begin"), || {
            slw::show_verifier_begin_profile(
                &key,
                &prefix,
                &[2, 3, 4],
                &[S::ONE, S::from(21), S::from(22)],
                profile,
                rng,
            )
        })
        .map_err(|e| e.to_string())?;
        let (ps, p2) =
            slw::show_holder_first(&key, &mut prep, &v1, rng).map_err(|e| e.to_string())?;
        let (vs, v3) = count(rows, meta("live_verifier_challenge"), || {
            slw::show_verifier_challenge_profile(vs, &p2, rng)
        })
        .map_err(|e| e.to_string())?;
        let p4 = slw::show_holder_respond(ps, &v3).map_err(|e| e.to_string())?;
        let ok = count(rows, meta("live_verifier_finish"), || {
            slw::show_verifier_finish_profile(vs, &p4, rng)
        })
        .map_err(|e| e.to_string())?;
        need(ok, "live SLW verification failed")?;
    }
    Ok(())
}

fn hin(
    rows: &mut Vec<Value>,
    grid: &[usize],
    max: usize,
    history: usize,
    rng: &mut StdRng,
) -> Result<(), String> {
    let (key, issuer) = hin::issuer_keygen(rng);
    let installed = key.install().map_err(str::to_owned)?;
    let (reader, secret) = hin::reader_keygen(rng);
    let tokens = (0..max)
        .map(|i| {
            let (request, pending) = hin::request(&reader, rng)?;
            let response = hin::issue(&issuer, &reader, &request, (i % 2) as u8, rng)?;
            hin::receive(pending, &response, rng)
        })
        .collect::<hin::Result<Vec<_>>>()
        .map_err(str::to_owned)?;
    for (profile, label) in [
        (hin::VerificationMode::Randomized, "verifier-random-fhs"),
        (
            hin::VerificationMode::RandomizedCachedAnchor,
            "verifier-random-fhs-cached-anchor",
        ),
    ] {
        independent(
            rows,
            &adapters::Hin::new(&installed, profile),
            &tokens,
            grid,
            label,
            history,
            |x| Ok(x.clone()),
            |x| {
                let mut t = x.clone();
                t.signature.z += G1::generator();
                Ok(t)
            },
            rng,
        )?;
    }
    for (i, t) in tokens.iter().take(2).enumerate() {
        let bit = count(
            rows,
            json!({"scheme":"HinToken","phase":"designated_reader_read_only","k_requested":1,
            "expected_bit":i,"boundary":"native_Read_without_public_Verify_or_shared_state"}),
            || hin::read_bit(&secret, t),
        );
        need(
            bit == Some(i as u8),
            "HinToken designated reader returned the wrong bit",
        )?;
    }
    Ok(())
}

fn collect(grid: &[usize], history: usize) -> Result<Vec<Value>, String> {
    let mut rows = Vec::new();
    let mut rng = StdRng::seed_from_u64(212_028_001);
    let max = grid.iter().copied().max().unwrap_or(0).max(4);
    darlt(&mut rows, grid, history, &mut rng)?;
    sma(&mut rows, grid, max, history, &mut rng)?;
    niat(&mut rows, grid, max, history, &mut rng)?;
    cpat(&mut rows, grid, max, history, &mut rng)?;
    msb(&mut rows, grid, max, history, &mut rng)?;
    slw(&mut rows, grid, max, history, &mut rng)?;
    hin(&mut rows, grid, max, history, &mut rng)?;
    rows.push(json!({"task":"runtime-check","phase":"coverage","schemes":["DARLT","SMA²RT","NIAT","CPAT","MSB+23","SLW+25","HinToken"],
        "k_values":grid,"history_records":history,"generated_independent_baseline_objects_per_scheme":max,
        "context_bytes_where_native_supported":{"DARLT":32,"SMA²RT":32,"MSB+23":32},
        "CPAT_public_metadata_bytes":32,"CPAT_service_tag_bytes":32,
        "MSB_business_attributes":9,"MSB_period_coordinates_count":1,"MSB_period_attribute_value":7,"SLW_business_attributes":10,
        "native_quota_absent":["MSB+23","SLW+25"],
        "darlt":"genuine native block proofs for every k; alternative workload fixtures; overlap test uses two independently valid blocks",
        "interactive_timing_boundary":"fixed completed-session runtime rechecks do not replace full live verifier costs; live phase counter rows are separate",
        "source":"fresh_protocol_execution","timing_enabled":false,"formal_samples":0}));
    Ok(rows)
}

/// Seven native adapters, thirteen safe candidate profiles, full requested k grid,
/// and identical 10,000-record historical occupancy before each workload.
pub fn run() -> Result<Vec<Value>, String> {
    collect(&K_VALUES, 10_000)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_multiblock_failures_do_not_commit_a_good_block_prefix() {
        let mut rows = Vec::new();
        let mut rng = StdRng::seed_from_u64(212_028_002);
        darlt(&mut rows, &[65], 32, &mut rng).unwrap();
        let bad_blocks = rows
            .iter()
            .filter(|r| r["phase"] == "runtime_bad_second_64_unit_block")
            .collect::<Vec<_>>();
        assert_eq!(bad_blocks.len(), 2);
        assert!(bad_blocks
            .iter()
            .all(|r| r["diagnosis"]["bad_indices"] == json!([1])));
        assert_eq!(
            rows.iter()
                .filter(|r| r["phase"] == "runtime_used_second_block_no_first_block_commit")
                .count(),
            2
        );
    }

    #[test]
    fn all_native_adapters_use_shared_atomic_state_and_real_proof_fallback() {
        let rows = collect(&[1, 3], 32).unwrap();
        let schemes = rows
            .iter()
            .filter(|r| r["phase"] == "runtime_verify_and_record")
            .map(|r| r["scheme"].as_str().unwrap())
            .collect::<BTreeSet<_>>();
        assert_eq!(schemes.len(), 7);
        assert!(rows
            .iter()
            .all(|r| r["formal_samples"] == 0 && r["timing_enabled"] == false));
        for (scheme, length) in [
            ("NIAT", 96),
            ("HinToken", 144),
            ("MSB+23", 32),
            ("SLW+25", 32),
        ] {
            assert!(rows
                .iter()
                .filter(|r| r["phase"] == "runtime_verify_and_record" && r["scheme"] == scheme)
                .all(|r| r["identifier_byte_lengths"] == json!([length])));
        }
        assert!(rows
            .iter()
            .filter(|r| r["phase"] == "runtime_bad_proof_localization")
            .all(|r| r["diagnosis"]["bad_indices"] == r["expected_bad_indices"]));
    }
}
