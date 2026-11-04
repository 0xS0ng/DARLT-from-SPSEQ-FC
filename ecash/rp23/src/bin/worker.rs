fn main() -> Result<(), String> {
    darlt_spseq_fc::experiment::serve(rp23_native::experiment::new()?)
}
