//! Fresh native baseline correctness, wire bytes and arithmetic counts.
fn main() {
    match baseline_core::checks::collect() {
        Ok(rows) => {
            for row in rows {
                println!("{row}");
            }
        }
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
