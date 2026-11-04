use ark_std::rand::{rngs::StdRng, SeedableRng};
use darlt_spseq_fc::{
    batch_runtime::{self, Adapter, Mode},
    common::spent::SpentStore,
};
use lcb24_native::{common_state::Verifier, Bank, VerificationMode};

fn main() -> Result<(), String> {
    let mut rng = StdRng::seed_from_u64(2_122_401_024);
    let bank = Bank::<10>::setup(&mut rng)?;
    let request = bank.customer_request(&mut rng)?;
    let request_bytes = request.request_bytes().len();
    let response = bank.issuer_response(request.commitment(), &mut rng)?;
    let mut wallet = bank.customer_receive(request, response)?;
    // This is explicitly workload-specific preparation, not a full inventory.
    let amount = 13usize;
    let proofs = bank.precompute_amount(&mut wallet, amount, &mut rng)?;
    let payment = bank.spend_prepared(&mut wallet, amount)?;
    let spec = bank.cryptographic_verify(&payment, VerificationMode::Specification, &mut rng)?;
    let random = bank.cryptographic_verify(&payment, VerificationMode::Randomized, &mut rng)?;
    let adapter = Verifier::new(&bank);
    let state = SpentStore::with_preexisting_records(10000, adapter.namespace(), 32)
        .map_err(|e| e.to_string())?;
    let accepted = batch_runtime::verify_and_record(
        &adapter,
        std::slice::from_ref(&payment),
        b"LCB24-N1024-native-correctness",
        b"accepted",
        &state,
        Mode::Randomized,
        &mut rng,
    )
    .map_err(|e| e.to_string())?;
    let retry = batch_runtime::verify_and_record(
        &adapter,
        std::slice::from_ref(&payment),
        b"LCB24-N1024-native-correctness",
        b"ignored-new-response",
        &state,
        Mode::Specification,
        &mut rng,
    )
    .map_err(|e| e.to_string())?;
    let recovered = bank.expand_after_verification(&payment)?;
    let each: Vec<_> = payment
        .blocks
        .iter()
        .map(|b| {
            serde_json::json!({
                "denom_subtree_height":b.denom,
                "subtree_root_depth":10usize-b.denom as usize,
                "actual_leftmost_leaf_snark_path_depth":10,
                "amount":b.amount(),
                "expanded_leaves":lcb24_native::expand(b.seed,b.denom).expect("validated height").len()
            })
        })
        .collect();
    if recovered.expanded_leaves != amount
        || accepted.newly_registered != amount
        || !retry.replayed
        || retry.response != b"accepted"
    {
        return Err("native full redemption amount mismatch".into());
    }
    println!(
        "{}",
        serde_json::json!({
            "scheme":"LCB24", "native_backend":"Arkworks 0.3 / BLS12-381 / Groth16",
            "capacity":1024,"wallet_height":10,"amount":amount,
            "preparation":"workload-specific selected leaf proofs",
            "prepared_proofs":proofs,"native_issue_request_bytes":request_bytes,"full_1024_leaf_inventory_run":false,
            "blocks":each,"payment_bytes":payment.encode().len(),
            "issuer_verification_material_bytes":bank.issuer_verification_material_bytes(),
            "proving_key_bytes":bank.proving_key_bytes(),
            "specification_miller_terms":spec.miller_terms,
            "specification_final_exponentiations":spec.final_exponentiations,
            "random_miller_terms":random.miller_terms,
            "random_final_exponentiations":random.final_exponentiations,
            "random_gt_exponentiations":random.gt_exponentiations,
            "expanded_leaves":recovered.expanded_leaves,
            "shared_state_preexisting":10000,"shared_state_newly_registered":accepted.newly_registered,
            "shared_state_counts":state.counts().map_err(|e|e.to_string())?,"exact_retry_replayed":retry.replayed,
            "native_serial_bytes_each":recovered.serials.iter().map(|s|s.len()).collect::<Vec<_>>(),
            "timing_enabled":false
        })
    );
    Ok(())
}
