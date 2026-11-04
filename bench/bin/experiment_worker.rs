fn main() -> Result<(), String> {
    use darlt_spseq_fc::{
        baseline_experiment, darlt_experiment,
        experiment::{Composite, Worker},
    };
    let mut workers: Vec<Box<dyn Worker>> = vec![Box::new(darlt_experiment::new()?)];
    for attributes in [5, 10, 15, 20, 25, 30] {
        workers.push(Box::new(baseline_experiment::Factory::for_attributes(
            attributes,
        )?));
    }
    darlt_spseq_fc::experiment::serve(Composite::new(workers)?)
}
