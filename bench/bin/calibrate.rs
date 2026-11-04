//! Single-thread BLS12-381 calibration; inputs are prepared outside each clock.
use blstrs::{Bls12, G1Projective as G1, G2Prepared, G2Projective as G2, Gt, Scalar};
use ff::Field;
use group::{Curve, Group};
use pairing::{MillerLoopResult, MultiMillerLoop};
use rand::{rngs::StdRng, SeedableRng};
use serde_json::{json, Value};
use std::{
    error::Error,
    fs::File,
    hint::black_box,
    io::{self, BufWriter, Write},
    path::PathBuf,
    time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
const WARMUP: usize = 10;
const FORMAL_SAMPLES: usize = 1000;
const MSM_SIZES: [usize; 9] = [1, 2, 4, 8, 16, 32, 64, 256, 1024];
const MILLER_SIZES: [usize; 7] = [1, 2, 4, 8, 16, 32, 64];

fn emit(out: &mut dyn Write, row: Value) -> Result<()> {
    serde_json::to_writer(&mut *out, &row)?;
    out.write_all(b"\n")?;
    Ok(())
}

fn timed<T>(operation: impl FnOnce() -> T) -> f64 {
    let start = Instant::now();
    black_box(operation());
    start.elapsed().as_secs_f64() * 1000.0
}

fn bench(
    out: &mut dyn Write,
    operation: &str,
    size: usize,
    samples: usize,
    mut sample: impl FnMut() -> f64,
) -> Result<()> {
    let mut values = Vec::with_capacity(samples);
    for index in 0..WARMUP + samples {
        let warmup = index < WARMUP;
        let elapsed_ms = sample();
        emit(
            out,
            json!({"type":"sample", "operation":operation, "size":size,
                "sample_index":if warmup {index} else {index-WARMUP},
                "elapsed_ms":elapsed_ms, "warmup":warmup}),
        )?;
        if !warmup {
            values.push(elapsed_ms);
        }
    }
    let mean = values.iter().sum::<f64>() / samples as f64;
    let sd = (samples > 1).then(|| {
        (values.iter().map(|v| (v - mean).powi(2)).sum::<f64>() / (samples - 1) as f64).sqrt()
    });
    emit(
        out,
        json!({"type":"summary", "operation":operation, "size":size,
            "n":samples, "warmup":WARMUP, "mean_ms":mean, "sd_ms":sd,
            "sd_convention":"sample standard deviation, denominator n-1"}),
    )
}

fn main() -> Result<()> {
    let mut output_path = None;
    let mut samples = FORMAL_SAMPLES;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out" => output_path = Some(PathBuf::from(args.next().ok_or("missing --out path")?)),
            "--samples" => samples = args.next().ok_or("missing --samples count")?.parse()?,
            "--help" | "-h" => {
                println!("primitives [--out PATH] [--samples N]\nDefault: stdout, 10 warmups and 1000 retained samples per operation.");
                return Ok(());
            }
            _ => return Err(format!("unknown argument: {arg}").into()),
        }
    }
    if samples == 0 {
        return Err("--samples must be positive".into());
    }
    let mut out: Box<dyn Write> = match output_path {
        Some(path) => {
            if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
                std::fs::create_dir_all(parent)?;
            }
            Box::new(BufWriter::new(File::create(path)?))
        }
        None => Box::new(BufWriter::new(io::stdout())),
    };
    emit(
        &mut *out,
        json!({"type":"session", "curve":"BLS12-381", "library":"blstrs 0.7.1",
        "blst":"0.3.17/no-threads", "threads":1, "clock":"std::time::Instant",
        "warmup":WARMUP, "samples":samples, "formal_profile":samples==FORMAL_SAMPLES,
        "instrumentation_enabled":cfg!(feature="op-counts"),
        "input_preparation":"random points and scalars outside each operation clock",
        "msm_inputs":"random points fixed per operation; fresh random scalars per sample",
        "miller_inputs":"random affine points fixed per operation; prepared variant reuses G2Prepared",
        "fixed_generator":"ordinary scalar multiplication on the generator, without extra fixed-base tables"}),
    )?;
    let mut rng = StdRng::seed_from_u64(1_970_131_000);
    let g1 = G1::generator();
    let g2 = G2::generator();
    let gt = Gt::generator();
    for variable in [false, true] {
        let suffix = if variable {
            "variable_base"
        } else {
            "fixed_generator"
        };
        bench(&mut *out, &format!("g1_exp_{suffix}"), 1, samples, || {
            let base = black_box(if variable {
                g1 * Scalar::random(&mut rng)
            } else {
                g1
            });
            let scalar = black_box(Scalar::random(&mut rng));
            timed(|| base * scalar)
        })?;
        bench(&mut *out, &format!("g2_exp_{suffix}"), 1, samples, || {
            let base = black_box(if variable {
                g2 * Scalar::random(&mut rng)
            } else {
                g2
            });
            let scalar = black_box(Scalar::random(&mut rng));
            timed(|| base * scalar)
        })?;
        bench(&mut *out, &format!("gt_exp_{suffix}"), 1, samples, || {
            let base = black_box(if variable {
                gt * Scalar::random(&mut rng)
            } else {
                gt
            });
            let scalar = black_box(Scalar::random(&mut rng));
            timed(|| base * scalar)
        })?;
    }
    bench(&mut *out, "pairing", 1, samples, || {
        let a = black_box((g1 * Scalar::random(&mut rng)).to_affine());
        let b = black_box((g2 * Scalar::random(&mut rng)).to_affine());
        timed(|| blstrs::pairing(&a, &b))
    })?;
    for size in MILLER_SIZES {
        let first: Vec<_> = (0..size)
            .map(|_| (g1 * Scalar::random(&mut rng)).to_affine())
            .collect();
        let second: Vec<_> = (0..size)
            .map(|_| (g2 * Scalar::random(&mut rng)).to_affine())
            .collect();
        let prepared: Vec<_> = second.iter().map(|p| G2Prepared::from(*p)).collect();
        let references: Vec<_> = first.iter().zip(&prepared).collect();
        bench(
            &mut *out,
            "multi_miller_plus_fe_prepared",
            size,
            samples,
            || timed(|| Bls12::multi_miller_loop(black_box(&references)).final_exponentiation()),
        )?;
        bench(
            &mut *out,
            "multi_miller_plus_fe_with_g2_prepare",
            size,
            samples,
            || {
                timed(|| {
                    let prepared: Vec<_> = black_box(&second)
                        .iter()
                        .map(|p| G2Prepared::from(*p))
                        .collect();
                    let references: Vec<_> = black_box(&first).iter().zip(&prepared).collect();
                    Bls12::multi_miller_loop(&references).final_exponentiation()
                })
            },
        )?;
    }
    for size in MSM_SIZES {
        let first: Vec<_> = (0..size).map(|_| g1 * Scalar::random(&mut rng)).collect();
        let second: Vec<_> = (0..size).map(|_| g2 * Scalar::random(&mut rng)).collect();
        bench(&mut *out, "g1_msm", size, samples, || {
            let scalars: Vec<_> = (0..size).map(|_| Scalar::random(&mut rng)).collect();
            timed(|| G1::multi_exp(black_box(&first), black_box(&scalars)))
        })?;
        bench(&mut *out, "g2_msm", size, samples, || {
            let scalars: Vec<_> = (0..size).map(|_| Scalar::random(&mut rng)).collect();
            timed(|| G2::multi_exp(black_box(&second), black_box(&scalars)))
        })?;
    }
    out.flush()?;
    Ok(())
}
