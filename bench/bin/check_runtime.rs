//! Current role phases, shared runtime and confirmed plan; no clock sampling.
fn main() -> Result<(), String> {
    let plan = darlt_spseq_fc::harness::validate_current_plan().map_err(|e| e.to_string())?;
    println!(
        "{}",
        serde_json::json!({"task":"runtime-check","phase":"harness_plan","value_type":"validated_plan_and_coverage_not_measurement","timing_enabled":false,"formal_samples":0,"plan":plan})
    );
    for mut row in darlt_spseq_fc::runtime_checks::run()? {
        row["task"] = serde_json::json!("runtime-check");
        println!("{row}");
    }
    for row in darlt_spseq_fc::phase_checks::run()? {
        println!("{row}");
    }
    Ok(())
}
