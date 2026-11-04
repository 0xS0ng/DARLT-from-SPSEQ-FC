//! Actual equal-budget configurations and independent role/system accounting.
fn main() -> Result<(), String> {
    for row in darlt_spseq_fc::provisioning_checks::run()? {
        println!("{row}");
    }
    Ok(())
}
