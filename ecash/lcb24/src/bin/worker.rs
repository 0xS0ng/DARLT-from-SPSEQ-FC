fn main() -> Result<(), String> {
    darlt_spseq_fc::experiment::serve(lcb24_native::experiment::new()?)
}
