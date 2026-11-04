//! Protocol correctness, wire accounting and operation counts.
fn main() {
    let result = (|| -> Result<(), String> {
        for row in darlt_spseq_fc::darlt::check::run()? {
            println!("{row}");
        }
        for row in darlt_spseq_fc::darlt::evidence::run()? {
            println!("{row}");
        }
        Ok(())
    })();
    if let Err(error) = result {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
