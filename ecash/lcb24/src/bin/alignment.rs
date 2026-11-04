//! Native proof inventory and common-backend correctness checks.
use ark_std::rand::{rngs::StdRng, SeedableRng};
use darlt_spseq_fc::{
    batch_runtime::{self, Adapter, Mode},
    common::spent::SpentStore,
    harness::K_VALUES,
    lcb24::{decode_received, Payment, RandomProfile, Verifier},
    ops,
};
use lcb24_native::{blstrs_bridge as bridge, Bank, VerificationMode};
use serde_json::json;

fn counters() -> serde_json::Value {
    let c = ops::stop();
    if cfg!(feature = "op-counts") {
        json!(c)
    } else {
        serde_json::Value::Null
    }
}
fn check(
    key: &darlt_spseq_fc::lcb24::Key,
    payment: &Payment,
    native: &lcb24_native::Payment,
    bank: &Bank<10>,
    scenario: &str,
    prior: Option<&Payment>,
    rng: &mut StdRng,
) -> Result<(), String> {
    let native_ids = bank.expand_after_verification(native)?.serials;
    let wire = payment.encode();
    let decoded = decode_received::<10>(&[&wire])?.pop().unwrap();
    if native_ids != decoded.redeem_serials::<10>()? || wire.len() != native.encode().len() {
        return Err("native/blstrs serial or wire-size mismatch".into());
    }
    for profile in [RandomProfile::CachedGtAnchor, RandomProfile::PairingAnchor] {
        for mode in [Mode::Specification, Mode::Randomized] {
            let verifier = Verifier::<10>::new(key, profile);
            let store = SpentStore::with_preexisting_records(10000, verifier.namespace(), 32)
                .map_err(|e| e.to_string())?;
            if let Some(p) = prior {
                batch_runtime::verify_and_record(
                    &verifier,
                    std::slice::from_ref(&p.clone().checked::<10>()?),
                    b"prior-sparse-spend",
                    b"prior-accepted",
                    &store,
                    Mode::Randomized,
                    rng,
                )
                .map_err(|e| e.to_string())?;
            }
            let before = store.counts().map_err(|e| e.to_string())?;
            ops::reset();
            key.verify_checked::<10>(std::slice::from_ref(&decoded), mode, profile, rng)?;
            let crypto = counters();
            ops::reset();
            let ids = decoded.redeem_serials::<10>()?;
            let redeem = counters();
            ops::reset();
            let accepted = batch_runtime::verify_and_record(
                &verifier,
                std::slice::from_ref(&decoded),
                b"new-payment",
                b"accepted",
                &store,
                mode,
                rng,
            )
            .map_err(|e| e.to_string())?;
            let inclusive = counters();
            let after = store.counts().map_err(|e| e.to_string())?;
            if accepted.newly_registered != native.amount
                || ids.len() != native.amount
                || after != (before.0 + 1, before.1 + native.amount)
            {
                return Err("shared native amount/transaction mismatch".into());
            }
            let retry = batch_runtime::verify_and_record(
                &verifier,
                std::slice::from_ref(&decoded),
                b"new-payment",
                b"ignored",
                &store,
                mode,
                rng,
            )
            .map_err(|e| e.to_string())?;
            if !retry.replayed || retry.response != b"accepted" {
                return Err("exact native retry mismatch".into());
            }
            println!(
                "{}",
                json!({"task":"native-check","phase":"lcb24_blstrs_native_grid","scheme":"LCB24","scenario":scenario,
                "capacity":1024,"k":native.amount,"blocks":native.blocks.len(),"denoms":native.blocks.iter().map(|b|b.denom).collect::<Vec<_>>(),
                "mode":format!("{mode:?}"),"candidate":format!("{profile:?}"),"wire_bytes":wire.len(),"canonical_serials":ids.len(),"native_serial_bytes":32,
                "merchant_verify":null,"merchant_verify_reason":"no independent merchant Verify in native LCB24",
                "crypto_counts":crypto,"redemption_noncrypto_counts":redeem,"bank_acceptance_including_state_counts":inclusive,
                "native_prover_backend":"Arkworks0.3","verification_backend":"blstrs0.7.1/blst0.3.17/no-threads",
                "shared_state_before":before,"shared_state_after":after,"prior_sparse_units":prior.map(|p|p.amount).unwrap_or(0),
                "value_type":"correctness_actual_counts_and_wire_bytes","timing_enabled":false,"formal_samples":0})
            );
        }
    }
    Ok(())
}
fn main() -> Result<(), String> {
    let workload_only = std::env::args().skip(1).any(|a| a == "--workload-proofs");
    let mut rng = StdRng::seed_from_u64(214_241_024);
    let bank = Bank::<10>::setup(&mut rng)?;
    let mut original = bank.issue_wallet(&mut rng)?;
    if !workload_only {
        for chunk in (0..1024).collect::<Vec<_>>().chunks(64) {
            let n = bank.precompute_leaves(&mut original, chunk, &mut rng)?;
            eprintln!("LCB24 actual prepared leaf proofs: {n}/1024");
        }
    }
    let key = bridge::key(&bank)?;
    // Verify the entire real inventory as native leaf blocks under both
    // independent implementations, not merely as a predicted proof count.
    if !workload_only {
        let mut all = bridge::fixture_branch(&bank, &original)?;
        let selected: Vec<_> = (0..1024).map(|i| (0, i)).collect();
        let all = bank.spend_prepared_blocks(&mut all, &selected)?;
        bank.cryptographic_verify(&all, VerificationMode::Specification, &mut rng)?;
        let converted = bridge::payment::<10>(&all)?;
        key.verify::<10>(
            &[converted],
            Mode::Randomized,
            RandomProfile::CachedGtAnchor,
            &mut rng,
        )?;
        println!(
            "{}",
            json!({"task":"native-check","phase":"lcb24_full_native_inventory","capacity":1024,
        "real_leaf_proofs":original.prepared_proofs(),"proof_cache_encoded_bytes":original.proof_cache_bytes(),
        "proving_key_bytes":bank.proving_key_bytes(),"arkworks_issuer_verification_material_bytes":bank.issuer_verification_material_bytes(),
        "blstrs_key_encoding_bytes":key.bytes().len(),"all_1024_proofs_verified_by_native_specification":true,
        "all_1024_proofs_verified_by_blstrs_random":true,"offline_backend":"Arkworks0.3",
        "conversion":"offline checked affine coordinates to IETF, canonical Fr unchanged","timing_enabled":false,"formal_samples":0})
        );
    } else {
        println!(
            "{}",
            json!({"task":"native-check","phase":"lcb24_known_workload_preparation","capacity":1024,"full_1024_leaf_inventory_run":false,"single_equation_profile":"exact_native_no_random_power_needed","timing_enabled":false,"formal_samples":0})
        );
    }
    for k in K_VALUES {
        let mut w = bridge::fixture_branch(&bank, &original)?;
        bank.precompute_amount(&mut w, k, &mut rng)?;
        let p = bank.spend_prepared(&mut w, k)?;
        let converted = bridge::payment::<10>(&p)?;
        check(&key, &converted, &p, &bank, "fresh-wallet", None, &mut rng)?;
    }
    if workload_only {
        return Ok(());
    }
    let mut w = bridge::fixture_branch(&bank, &original)?;
    let evens: Vec<_> = (0..1024).step_by(2).map(|i| (0, i)).collect();
    let prior = bank.spend_prepared_blocks(&mut w, &evens)?;
    let prior = bridge::payment::<10>(&prior)?;
    let p = bank.spend_prepared(&mut w, 16)?;
    if p.blocks.len() != 16 || p.blocks.iter().any(|b| b.denom != 0) {
        return Err("actual fragmented native selector mismatch".into());
    }
    let converted = bridge::payment::<10>(&p)?;
    check(
        &key,
        &converted,
        &p,
        &bank,
        "512-prior-even-leaves",
        Some(&prior),
        &mut rng,
    )?;
    Ok(())
}
