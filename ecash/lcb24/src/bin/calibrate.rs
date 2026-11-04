//! Joint native primitive runner; current false/null plan produces no samples.
use ark_std::rand::{rngs::StdRng, SeedableRng};
use darlt_spseq_fc::sampling::{Candidate, SampleClass, Sampler};
use lcb24_native::{
    calibration::{Fixture, Operation, MSM_SIZES},
    Result,
};
use serde_json::json;
fn main() -> Result<()> {
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "bench/measurement_plan.json".into());
    let plan: serde_json::Value =
        serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    if plan["timing_enabled"] != true || plan["timing_window"].is_null() {
        println!(
            "{}",
            json!({"task":"native-check","phase":"backend_calibration_pending_authorized_window","ratios":null,"timing_enabled":false,"formal_samples":0})
        );
        return Ok(());
    }
    let candidates = vec![
        Candidate {
            name: "Arkworks0.3".into(),
            class: SampleClass::Primitive,
            safe: true,
        },
        Candidate {
            name: "blstrs0.7.1".into(),
            class: SampleClass::Primitive,
            safe: true,
        },
    ];
    let mut operations = vec![Operation::Pairing];
    for n in MSM_SIZES {
        operations.extend([Operation::G1Msm(n), Operation::G2Msm(n)]);
    }
    let mut rng = StdRng::seed_from_u64(214_240_004);
    let mut sampler = Sampler::default();
    for operation in operations {
        let mut fixture = Fixture::new(operation, &mut rng)?;
        fixture.check_msm_equivalence()?;
        let attempt = sampler
            .run_wallclock_attempt(
                &plan,
                &format!("LCB24-calibration/{operation:?}"),
                &candidates,
                &mut fixture,
            )
            .map_err(|e| e.to_string())?;
        println!(
            "{}",
            serde_json::to_value(attempt).map_err(|e| e.to_string())?
        );
        let ratios = if attempt.outcome == darlt_spseq_fc::sampling::Outcome::Stable {
            Some(
                attempt.summaries[0].statistics.as_ref().unwrap().mean_ns
                    / attempt.summaries[1].statistics.as_ref().unwrap().mean_ns,
            )
        } else {
            None
        };
        println!(
            "{}",
            json!({"phase":"backend_ratio","operation":format!("{operation:?}"),"definition":"Arkworks mean / blstrs mean","ratio":ratios,"attempt":attempt.number,"outcome":attempt.outcome,"timing_enabled":true})
        );
        if attempt.outcome != darlt_spseq_fc::sampling::Outcome::Stable {
            return Err("calibration attempt retained; complete remeasurement required".into());
        }
    }
    Ok(())
}
