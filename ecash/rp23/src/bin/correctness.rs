//! Fresh native lifecycles and actual backend counts. This program has no clock.
use darlt_spseq_fc::{
    batch_runtime::{self as rt, Adapter, Mode},
    common::spent::SpentStore,
};
use rand::{rngs::StdRng, SeedableRng};
use rp23_native::{
    api::*,
    backend::{self as b, VerificationMode as V},
    shared_runtime::*,
};
use serde_json::{json, Value};
const K: [u64; 14] = [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 96, 128];
const M: [u8; 16] = [7; 16];
fn row(mut v: Value) {
    v["task"] = json!("native-check");
    v["timing_enabled"] = json!(false);
    v["formal_samples"] = json!(0);
    v["native_backend"] = json!("blstrs0.7.1/blst0.3.17 no-threads");
    println!("{v}");
}
fn counted<T>(mut v: Value, run: impl FnOnce() -> T) -> T {
    b::start_counts();
    let result = run();
    v["counts"] = json!(b::stop_counts());
    v["value_type"] = json!("execution_count");
    row(v);
    result
}
fn shared<A: Adapter>(a: &A, p: &[A::Item], amount: usize, bytes: usize, rng: &mut StdRng) {
    let mut accepted_store = None;
    for mode in [Mode::Specification, Mode::Randomized] {
        let store = SpentStore::with_preexisting_records(10000, a.namespace(), bytes).unwrap();
        let accepted = counted(
            json!({"scheme":a.scheme(),"phase":"inclusive_verify_deposit_and_shared_state","profile":format!("{mode:?}"),"k":amount,"history_records":10000,"history_id_bytes":bytes,"history_fixture":"synthetic_storage_records_under_active_issuer_namespace"}),
            || {
                rt::verify_and_record(a, p, b"fresh-native-spend", b"accepted", &store, mode, rng)
                    .unwrap()
            },
        );
        assert_eq!(accepted.newly_registered, amount);
        assert_eq!(store.counts().unwrap(), (10001, 10000 + amount));
        if mode == Mode::Randomized {
            accepted_store = Some(store);
        }
    }
    let store = accepted_store.unwrap();
    let retry = rt::verify_and_record(
        a,
        p,
        b"fresh-native-spend",
        b"replacement",
        &store,
        Mode::Randomized,
        rng,
    )
    .unwrap();
    assert!(retry.replayed && retry.response == b"accepted");
    assert_eq!(store.counts().unwrap(), (10001, 10000 + amount));
}
fn main() {
    let mut rng = StdRng::seed_from_u64(214);
    let p = counted(
        json!({"scheme":"RP23-C","phase":"setup","capacity":1024}),
        || rp23_native::compact::setup::setup(1024),
    );
    let c = counted(
        json!({"scheme":"RP23-C","phase":"authority_keygen_and_vk_aggregation","threshold":2,"authorities_generated":3}),
        || Compact::from_parameters(p).unwrap(),
    );
    row(
        json!({"scheme":"RP23-C","phase":"public_parameters","capacity":1024,"actual_bytes":c.public_parameter_bytes().len(),"range_signatures":1024,"threshold":2,"authorities_generated":3,"authorities_contacted_per_issue":2}),
    );
    for k in K {
        let w = counted(
            json!({"scheme":"RP23-C","phase":"issue_complete_both_roles","capacity":1024,"k":k,"authorities_contacted":2}),
            || c.issue().unwrap(),
        );
        let (pending, request) = counted(
            json!({"scheme":"RP23-C","phase":"issue_client_request","k":k,"wire_bytes":null}),
            || c.client_request().unwrap(),
        );
        let responses = counted(
            json!({"scheme":"RP23-C","phase":"issue_issuer_responses","k":k,"authorities_contacted":2,"wire_bytes":null}),
            || c.issuer_responses(&request).unwrap(),
        );
        let mut prepared_wallet = counted(
            json!({"scheme":"RP23-C","phase":"issue_client_receive","k":k,"shares_verified":2}),
            || c.client_receive(pending, responses).unwrap(),
        );
        let info = PayInfo::new(M, [k as u8; 16]);
        let p = counted(
            json!({"scheme":"RP23-C","phase":"spend_native_total_reference","k":k,"native_payments":1}),
            || c.spend(&w, k, info).unwrap(),
        );
        let encoded = p.encode();
        let p = CompactPayment::decode(&encoded, info, 1024).unwrap();
        assert_eq!(p.encode(), encoded);
        row(
            json!({"scheme":"RP23-C","phase":"native_payment_size","k":k,"native_payments":1,"payment_bytes":encoded.len(),"merchant_payinfo_bytes":32,"wire_bytes":encoded.len()+32}),
        );
        let prepared = counted(
            json!({"scheme":"RP23-C","phase":"spend_preparation","k":k,"merchant_known":true,"fresh_nonce_known":false}),
            || c.prepare(&mut prepared_wallet, k, M).unwrap(),
        );
        let p = counted(
            json!({"scheme":"RP23-C","phase":"spend_online","k":k,"fresh_nonce_bytes":16}),
            || prepared.finish(info).unwrap(),
        );
        for m in [V::Specification, V::Randomized] {
            counted(
                json!({"scheme":"RP23-C","phase":"merchant_spend_verify","profile":format!("{m:?}"),"k":k}),
                || assert!(c.verify(std::slice::from_ref(&p), &M, m, &mut rng)),
            );
        }
        let ids = counted(
            json!({"scheme":"RP23-C","phase":"deposit_after_merchant_verification","k":k}),
            || {
                c.deposit_serials_after_verification(std::slice::from_ref(&p))
                    .unwrap()
            },
        );
        assert_eq!(ids.len(), k as usize);
        shared(
            &CompactVerifier::new(&c, M),
            &[c.check_payment(p).unwrap()],
            k as usize,
            48,
            &mut rng,
        );
    }
    let p = counted(
        json!({"scheme":"RP23-D","phase":"setup","capacity":1024}),
        || {
            rp23_native::divisible::setup::Parameters::new_with_capacity(
                rp23_native::divisible::setup::GroupParameters::new().unwrap(),
                1024,
            )
        },
    );
    let d = counted(
        json!({"scheme":"RP23-D","phase":"authority_keygen_and_vk_aggregation","threshold":2,"authorities_generated":3}),
        || Divisible::from_parameters(p).unwrap(),
    );
    row(
        json!({"scheme":"RP23-D","phase":"public_parameters","capacity":1024,"user_actual_bytes":d.user_public_parameter_bytes().len(),"deposit_actual_bytes":d.deposit_public_parameter_bytes().len(),"triangular_G2_points":d.authority_triangular_points(),"threshold":2,"authorities_generated":3,"authorities_contacted_per_issue":2,"wallet_end_convention":"one-based full capacity: l+V-1<=L","terminal_parameter_coverage":d.end_parameter_coverage()}),
    );
    counted(
        json!({"scheme":"RP23-D","phase":"install_public_pairing_bases","amounts":K,"boundary":"public cached pairing targets; each participant installation charged separately in role harness"}),
        || d.install_public_pairing_bases(&K),
    );
    for k in K {
        let w = counted(
            json!({"scheme":"RP23-D","phase":"issue_complete_both_roles","capacity":1024,"k":k,"authorities_contacted":2}),
            || d.issue().unwrap(),
        );
        let (pending, request) = counted(
            json!({"scheme":"RP23-D","phase":"issue_client_request","k":k,"wire_bytes":null}),
            || d.client_request().unwrap(),
        );
        let responses = counted(
            json!({"scheme":"RP23-D","phase":"issue_issuer_responses","k":k,"authorities_contacted":2,"wire_bytes":null}),
            || d.issuer_responses(&request).unwrap(),
        );
        let mut prepared_wallet = counted(
            json!({"scheme":"RP23-D","phase":"issue_client_receive","k":k,"shares_verified":2}),
            || d.client_receive(pending, responses).unwrap(),
        );
        let info = PayInfo::new(M, [k as u8; 16]);
        let p = counted(
            json!({"scheme":"RP23-D","phase":"spend_native_total_reference","k":k,"native_payments":1,"actual_contiguous_intervals":1}),
            || d.spend(&w, k, info).unwrap(),
        );
        let encoded = p.encode();
        let p = DivisiblePayment::decode(&encoded, info, 1024).unwrap();
        assert_eq!(p.encode(), encoded);
        row(
            json!({"scheme":"RP23-D","phase":"native_payment_size","k":k,"native_payments":1,"actual_contiguous_intervals":1,"payment_bytes":encoded.len(),"merchant_payinfo_bytes":32,"wire_bytes":encoded.len()+32}),
        );
        let prepared = counted(
            json!({"scheme":"RP23-D","phase":"spend_preparation","k":k,"merchant_known":true,"fresh_nonce_known":false}),
            || d.prepare(&mut prepared_wallet, k, M).unwrap(),
        );
        let p = counted(
            json!({"scheme":"RP23-D","phase":"spend_online","k":k,"fresh_nonce_bytes":16}),
            || prepared.finish(info).unwrap(),
        );
        for m in [V::Specification, V::Randomized] {
            counted(
                json!({"scheme":"RP23-D","phase":"merchant_spend_verify","profile":format!("{m:?}"),"k":k}),
                || assert!(d.verify(std::slice::from_ref(&p), &M, m, &mut rng)),
            );
        }
        let ids = counted(
            json!({"scheme":"RP23-D","phase":"deposit_after_merchant_verification","k":k}),
            || {
                d.deposit_serials_after_verification(std::slice::from_ref(&p))
                    .unwrap()
            },
        );
        assert_eq!(ids.len(), k as usize);
        shared(
            &DivisibleVerifier::new(&d, M),
            &[d.check_payment(p).unwrap()],
            k as usize,
            288,
            &mut rng,
        );
    }
    row(
        json!({"phase":"coverage","schemes":["RP23-C","RP23-D"],"k":K,"native_spend_once_per_amount":true,"full_native_deposit":true,"shared_state":true,"exact_retry":true,"fragmented_native_wallet":"native sequential counter; no external interval scheduler","fragmentation_note":"原生计数器顺序花费，钱包不会碎片化","formal_ready":false,"pending":["complete role/cold-hot/substage timing integration","same-window formal sampler and authorization"]}),
    );

    if let Some(path) = std::env::args().nth(1) {
        let rows = post_prior_scenario(&d, &mut rng);
        let text = rows
            .into_iter()
            .map(|r| r.to_string())
            .collect::<Vec<_>>()
            .join("\n")
            + "\n";
        std::fs::write(path, text).expect("write native post-prior scenario");
    }

    if let Some(path) = std::env::args().nth(2) {
        let rows = default_capacity_endpoint_checks(&d, &mut rng);
        std::fs::write(
            path,
            rows.into_iter()
                .map(|r| r.to_string())
                .collect::<Vec<_>>()
                .join("\n")
                + "\n",
        )
        .expect("write full-capacity endpoint evidence");
    }
}

fn scenario_capture<T>(rows: &mut Vec<Value>, mut row: Value, run: impl FnOnce() -> T) -> T {
    b::start_counts();
    let result = run();
    row["counts"] = json!(b::stop_counts());
    row["value_type"] = json!("execution_count");
    rows.push(row);
    result
}
fn post_prior_scenario(d: &Divisible, rng: &mut StdRng) -> Vec<Value> {
    let mut rows = vec![
        json!({"phase":"scenario","capacity":1024,"prior_amount":512,"amount":16,"native_interval_count":1,"allocator":"native sequential counter only","note":"原生计数器顺序花费，钱包不会碎片化","history_records":10000,"history_id_bytes":288,"history_fixture":"synthetic storage plus one genuine prior512 native payment"}),
    ];
    let (pending, request) = scenario_capture(
        &mut rows,
        json!({"phase":"issue_client_request","wire_bytes":null}),
        || d.client_request().unwrap(),
    );
    let response = scenario_capture(
        &mut rows,
        json!({"phase":"issue_issuer_responses","authorities_contacted":2,"wire_bytes":null}),
        || d.issuer_responses(&request).unwrap(),
    );
    let mut wallet = scenario_capture(
        &mut rows,
        json!({"phase":"issue_client_receive","shares_verified":2}),
        || d.client_receive(pending, response).unwrap(),
    );
    d.clear_pairing_cache();
    scenario_capture(
        &mut rows,
        json!({"phase":"install_public_pairing_bases","amounts":[512,16]}),
        || d.install_public_pairing_bases(&[512, 16]),
    );
    let before = wallet.next_index();
    assert_eq!(before, 1);
    let prepared = scenario_capture(
        &mut rows,
        json!({"phase":"prior_spend_preparation","k":512,"native_interval_count":1}),
        || d.prepare(&mut wallet, 512, M).unwrap(),
    );
    let prior = scenario_capture(
        &mut rows,
        json!({"phase":"prior_spend_online","k":512,"native_interval_count":1}),
        || prepared.finish(PayInfo::new(M, [200; 16])).unwrap(),
    );
    assert_eq!(wallet.next_index(), 513);
    let verifier = DivisibleVerifier::new(d, M);
    let original = SpentStore::with_preexisting_records(10000, verifier.namespace(), 288).unwrap();
    let accepted = scenario_capture(
        &mut rows,
        json!({"phase":"prior_inclusive_accept","k":512,"profile":"Randomized"}),
        || {
            rt::verify_and_record(
                &verifier,
                std::slice::from_ref(&d.check_payment(prior.clone()).unwrap()),
                b"prior512",
                b"prior accepted",
                &original,
                Mode::Randomized,
                rng,
            )
            .unwrap()
        },
    );
    assert_eq!(accepted.newly_registered, 512);
    assert_eq!(original.counts().unwrap(), (10001, 10512));
    rows.push(json!({"phase":"state_after_prior","requests":original.counts().unwrap().0,"identifiers":original.counts().unwrap().1,"genuine_preexisting_native_serials":512,"wallet_next_index_1based":wallet.next_index()}));
    let start = wallet.next_index();
    let prepared = scenario_capture(
        &mut rows,
        json!({"phase":"spend_preparation","k":16,"native_interval_count":1,"start_index_1based":start}),
        || d.prepare(&mut wallet, 16, M).unwrap(),
    );
    let payment = scenario_capture(
        &mut rows,
        json!({"phase":"spend_online","k":16,"fresh_nonce_bytes":16}),
        || prepared.finish(PayInfo::new(M, [201; 16])).unwrap(),
    );
    assert_eq!(wallet.next_index(), 529);
    let bytes = payment.encode();
    let payment = DivisiblePayment::decode(&bytes, payment.payinfo, 1024).unwrap();
    rows.push(json!({"phase":"native_payment_size","k":16,"native_interval_count":1,"start_index_1based":start,"end_index_1based":wallet.next_index()-1,"payment_bytes":bytes.len(),"merchant_payinfo_bytes":32,"wire_bytes":bytes.len()+32}));
    for mode in [V::Specification, V::Randomized] {
        scenario_capture(
            &mut rows,
            json!({"phase":"merchant_spend_verify","k":16,"profile":format!("{mode:?}")}),
            || assert!(d.verify(std::slice::from_ref(&payment), &M, mode, rng)),
        );
    }
    let ids = scenario_capture(
        &mut rows,
        json!({"phase":"deposit_after_merchant_verification","k":16}),
        || {
            d.deposit_serials_after_verification(std::slice::from_ref(&payment))
                .unwrap()
        },
    );
    assert_eq!(ids.len(), 16);
    assert_eq!(
        ids.iter().collect::<std::collections::BTreeSet<_>>().len(),
        16
    );
    for mode in [Mode::Specification, Mode::Randomized] {
        // The prior payment is genuinely accepted in each independent state fixture before the measured16.
        let store = SpentStore::with_preexisting_records(10000, verifier.namespace(), 288).unwrap();
        rt::verify_and_record(
            &verifier,
            std::slice::from_ref(&d.check_payment(prior.clone()).unwrap()),
            b"prior512",
            b"prior accepted",
            &store,
            Mode::Specification,
            rng,
        )
        .unwrap();
        assert_eq!(store.counts().unwrap(), (10001, 10512));
        let result = scenario_capture(
            &mut rows,
            json!({"phase":"inclusive_verify_deposit_and_shared_state","k":16,"profile":format!("{mode:?}"),"history_records":10000,"genuine_preexisting_native_serials":512,"preexisting_requests":10001,"preexisting_identifiers":10512}),
            || {
                rt::verify_and_record(
                    &verifier,
                    std::slice::from_ref(&d.check_payment(payment.clone()).unwrap()),
                    b"post-prior16",
                    b"first accepted",
                    &store,
                    mode,
                    rng,
                )
                .unwrap()
            },
        );
        assert_eq!(result.newly_registered, 16);
        assert_eq!(store.counts().unwrap(), (10002, 10528));
        let retry = rt::verify_and_record(
            &verifier,
            std::slice::from_ref(&d.check_payment(payment.clone()).unwrap()),
            b"post-prior16",
            b"replacement",
            &store,
            mode,
            rng,
        )
        .unwrap();
        assert!(
            retry.replayed && retry.response == b"first accepted" && retry.newly_registered == 0
        );
        rows.push(json!({"phase":"state_after_post_prior","profile":format!("{mode:?}"),"newly_registered":result.newly_registered,"requests":store.counts().unwrap().0,"identifiers":store.counts().unwrap().1,"exact_retry_keeps_first_response":true,"wallet_next_index_1based":wallet.next_index()}));
    }
    for r in &mut rows {
        r["task"] = json!("native-check");
        r["scheme"] = json!("RP23-D");
        r["scenario"] = json!("native_counter_after_sequential_prior512");
        r["timing_enabled"] = json!(false);
        r["formal_samples"] = json!(0);
    }
    rows
}

fn default_capacity_endpoint_checks(d: &Divisible, rng: &mut StdRng) -> Vec<Value> {
    let mut rows = vec![];
    let info = |n: u8| PayInfo::new(M, [n; 16]);
    for prepared in [false, true] {
        let mut full = d.issue().unwrap();
        let payment = if prepared {
            d.prepare(&mut full, 1024, M)
                .unwrap()
                .finish(info(210))
                .unwrap()
        } else {
            d.spend(&full, 1024, info(210)).unwrap()
        };
        assert_eq!(full.next_index(), 1025);
        for mode in [V::Specification, V::Randomized] {
            assert!(d.verify(std::slice::from_ref(&payment), &M, mode, rng));
        }
        let full_ids = d.deposit_serials_after_verification(&[payment]).unwrap();
        assert_eq!(full_ids.len(), 1024);
        assert_eq!(
            full_ids
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            1024
        );
        let mut split = d.issue().unwrap();
        let first = if prepared {
            d.prepare(&mut split, 1023, M)
                .unwrap()
                .finish(info(211))
                .unwrap()
        } else {
            d.spend(&split, 1023, info(211)).unwrap()
        };
        assert_eq!(split.next_index(), 1024);
        let last = if prepared {
            d.prepare(&mut split, 1, M)
                .unwrap()
                .finish(info(212))
                .unwrap()
        } else {
            d.spend(&split, 1, info(212)).unwrap()
        };
        assert_eq!(split.next_index(), 1025);
        for mode in [V::Specification, V::Randomized] {
            assert!(d.verify(&[first.clone(), last.clone()], &M, mode, rng));
        }
        let split_ids = d
            .deposit_serials_after_verification(&[first, last])
            .unwrap();
        assert_eq!(split_ids.len(), 1024);
        assert_eq!(
            split_ids
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            1024
        );
        assert!(d.spend(&full, 1, info(213)).is_err());
        assert!(d.prepare(&mut full, 1, M).is_err());
        assert!(d.spend(&split, 1, info(213)).is_err());
        assert!(d.prepare(&mut split, 1, M).is_err());
        assert_eq!((full.next_index(), split.next_index()), (1025, 1025));
        rows.push(json!({"task":"native-check","scheme":"RP23-D","scenario":"full_capacity_endpoint_correctness","phase":"full_capacity_endpoint_check","capacity":1024,"profile":if prepared{"Prepared"}else{"Native"},"fresh_full_amount":1024,"fresh_full_unique_serials":full_ids.len(),"split_amounts":[1023,1],"split_unique_serials":split_ids.len(),"both_wallet_counters_after":1025,"next_one_rejected_by_native_and_prepared":true,"merchant_spec_and_random_valid":true,"independent_wallets":true,"same_secret_branch_serial_equality_test":"L1/L16 unit fixture","timing_enabled":false,"formal_samples":0}));
    }
    rows
}
