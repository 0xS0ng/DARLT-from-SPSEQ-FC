use std::path::PathBuf;
fn main() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let mut binaries = vec![];
    let mut out = None;
    let mut plan = PathBuf::from("bench/measurement_plan.json");
    let mut mode = "inventory".to_string();
    let mut filter = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--worker" => binaries.push(PathBuf::from(args.next().ok_or("worker path missing")?)),
            "--out" => out = Some(PathBuf::from(args.next().ok_or("output path missing")?)),
            "--plan" => plan = PathBuf::from(args.next().ok_or("plan path missing")?),
            "--mode" => mode = args.next().ok_or("mode missing")?,
            "--filter" => filter = args.next(),
            _ => return Err(format!("unknown argument {arg}")),
        }
    }
    if binaries.is_empty() {
        binaries = vec![
            "target/release/experiment_worker".into(),
            "ecash/rp23/target/release/worker".into(),
            "ecash/lcb24/target/release/worker".into(),
        ];
    }
    let plan = serde_json::from_slice(&std::fs::read(plan).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let result = darlt_spseq_fc::dispatch::run(
        &binaries,
        &mode,
        &plan,
        &out.ok_or("output path missing")?,
        filter.as_deref(),
    )?;
    println!("{result}");
    if result["status"] == "REMEASUREMENT_REQUIRED" {
        return Err("whole attempts retained; remeasurement required".into());
    }
    if result["status"] == "ESTIMATE_INCOMPLETE" {
        return Err("duration projection incomplete; see estimate_summary.json".into());
    }
    Ok(())
}
