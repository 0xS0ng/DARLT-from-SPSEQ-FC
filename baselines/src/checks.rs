//! Clock-free correctness checks with fresh protocol inputs;
//! no earlier measurement file is read and no wall-clock value is produced.
use crate::{arithmetic::*, bhn26 as n, klo26 as c, msb23 as m, slw25 as l, sma2rt as s};
use rand::{rngs::StdRng, SeedableRng};
use serde_json::{json, Value};
use std::collections::BTreeSet;

const GRID: [usize; 14] = [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 96, 128];
fn row(scheme: &str, phase: &str, profile: &str, k: usize, bytes: usize, counts: Counts) -> Value {
    let wire_kind = if matches!(scheme, "MSB+23" | "SLW+25") {
        "full-bidirectional-interaction"
    } else {
        "sum-of-complete-token-encodings"
    };
    let miller = counts.p + counts.mp_terms;
    let fe = counts.p + counts.mp_calls;
    json!({"type":"baseline-check","scheme":scheme,"phase":phase,"profile":profile,"k":k,
        "valid":true,"formal":false,"formal_samples":0,"value_type":"correctness-and-operation-counts",
        "source":"fresh-protocol-run","wire_bytes":bytes,"wire_kind":wire_kind,"counts":counts,
        "miller_terms":miller,"final_exponentiations":fe})
}
/// All five native lifecycles, plus three schemes' genuine independent-token
/// random profiles and NIAT's two explicit App.C.3 profiles on the full k grid.
/// Run correctness checks without a timer.
pub fn collect() -> Result<Vec<Value>, String> {
    let mut rows = vec![];
    let mut rng = StdRng::seed_from_u64(207500);
    let pp = s::setup(10, 1024);
    let issuer = s::ikeygen(&pp, &mut rng);
    let meta = s::vkeygen(&pp, &mut rng);
    let key = s::ukeygen(&mut rng);
    let installed = s::install_instance(&pp, &issuer, &meta).map_err(str::to_owned)?;
    let attrs: Vec<_> = (0..10).map(|i| S::from(101 + i)).collect();
    let policy = s::Policy {
        atoms: (0..3).map(|i| s::Atom::Reveal(i, attrs[i])).collect(),
    };
    let (wallet, _, _) =
        s::issue(&pp, &issuer, &meta, &key, &attrs, &policy, 0, &mut rng).map_err(str::to_owned)?;
    let sma: Vec<_> = (0..128)
        .map(|i| {
            s::show_installed(
                &installed,
                &wallet,
                i,
                b"spend/test/ctx-v1",
                &policy,
                &mut rng,
            )
        })
        .collect::<Result<_, _>>()
        .map_err(str::to_owned)?;
    let ni = n::IssuerKeys::generate(&mut rng);
    let ns = ni.install().map_err(|e| e.to_string())?;
    let nc = n::ClientKeys::generate(&mut rng);
    let niat: Vec<_> = (0..128)
        .map(|i| {
            let response = n::issue(&ns, &ni.secret, nc.public_key(), (i % 2) as u8, &mut rng)?;
            n::obtain(&ns, &nc, &response, &mut rng)
        })
        .collect::<n::Result<_>>()
        .map_err(|e| e.to_string())?;
    let ci = c::keygen(&mut rng);
    let ck = c::validate_key(&ci.pk).map_err(str::to_owned)?;
    let cmd = c::install_metadata(&ck, b"public-metadata/v1");
    let tag = b"test/service-period/v1".to_vec();
    let cp = c::Policy {
        allowed: BTreeSet::from([tag.clone()]),
    };
    // Each unit has a genuinely separate issuance/client secret. Reusing one
    // credential with fresh representation randomness would repeat delta.
    let cpat: Vec<_> = (0..128)
        .map(|i| {
            let (req, state) = c::request(&ck, b"public-metadata/v1", &mut rng);
            let res = c::issue_installed(&ck, &ci, &req, b"public-metadata/v1", i % 2, &mut rng)?;
            let wallet = c::receive(state, &res)?;
            c::show(&ck, &wallet, &tag, &mut rng)
        })
        .collect::<c::Result<_>>()
        .map_err(str::to_owned)?;
    if sma
        .iter()
        .map(|t| enc1(t.serial))
        .collect::<BTreeSet<_>>()
        .len()
        != 128
        || niat
            .iter()
            .map(n::redemption_tag)
            .collect::<BTreeSet<_>>()
            .len()
            != 128
        || cpat
            .iter()
            .map(|t| enc1(t.delta))
            .collect::<BTreeSet<_>>()
            .len()
            != 128
    {
        return Err("nonindependent native units".into());
    }
    for k in GRID {
        let bytes = sma[..k].iter().map(s::Token::bytes).map(|b| b.len()).sum();
        start_counts();
        let valid = sma[..k]
            .iter()
            .all(|t| s::verify_installed(&installed, t, b"spend/test/ctx-v1", &policy));
        let counts = stop_counts();
        if !valid {
            return Err("SMA sequential rejected".into());
        }
        rows.push(row("SMA²RT", "Verify", "spec-sequential", k, bytes, counts));
        start_counts();
        let valid = s::verify_random_batch_installed(
            &installed,
            &sma[..k],
            b"spend/test/ctx-v1",
            &policy,
            &mut rng,
        );
        let counts = stop_counts();
        if !valid {
            return Err("SMA random batch rejected".into());
        }
        rows.push(row(
            "SMA²RT",
            "Verify",
            "verifier-random-fhs",
            k,
            bytes,
            counts,
        ));
        let bytes = cpat[..k].iter().map(|t| t.encode().len()).sum();
        start_counts();
        let valid = cpat[..k]
            .iter()
            .all(|t| c::verify(&ck, &cp, b"public-metadata/v1", t));
        let counts = stop_counts();
        if !valid {
            return Err("CPAT sequential rejected".into());
        }
        rows.push(row("CPAT", "Verify", "spec-sequential", k, bytes, counts));
        start_counts();
        let valid = c::verify_random_batch(&ck, &cp, b"public-metadata/v1", &cpat[..k], &mut rng);
        let counts = stop_counts();
        if !valid {
            return Err("CPAT random batch rejected".into());
        }
        rows.push(row(
            "CPAT",
            "Verify",
            "verifier-random-fhs",
            k,
            bytes,
            counts,
        ));
        start_counts();
        let valid = c::verify_random_batch_metadata(&cmd, &cp, &cpat[..k], &mut rng);
        let counts = stop_counts();
        if !valid {
            return Err("CPAT combined-metadata random batch rejected".into());
        }
        rows.push(row(
            "CPAT",
            "Verify",
            "verifier-random-fhs-same-md",
            k,
            bytes,
            counts,
        ));
        let bytes = niat[..k].iter().map(|t| t.encode().len()).sum();
        start_counts();
        let valid = niat[..k].iter().all(|t| n::public_verify(&ns, t));
        let counts = stop_counts();
        if !valid {
            return Err("NIAT sequential rejected".into());
        }
        rows.push(row("NIAT", "Verify", "spec-sequential", k, bytes, counts));
        for (mode, name) in [
            (n::RedemptionBatch::OriginalAllOnes, "native-C3-all-ones"),
            (
                n::RedemptionBatch::RandomSecondEquation,
                "native-C3-random-eq2",
            ),
            (n::RedemptionBatch::RandomFhs, "verifier-random-fhs"),
            (
                n::RedemptionBatch::RandomFhsCachedAnchor,
                "verifier-random-fhs-cached-anchor",
            ),
        ] {
            start_counts();
            let result = n::verify_batch_redemption(&ns, &niat[..k], mode, &mut rng);
            let counts = stop_counts();
            if result.is_err() {
                return Err(format!("NIAT {name} rejected"));
            }
            let mut value = row("NIAT", "Verify", name, k, bytes, counts);
            value["redemption_tag_bytes"] = json!(96);
            rows.push(value);
        }
    }
    collect_slw(&mut rows, &mut rng)?;
    collect_msb(&mut rows, &mut rng)?;
    Ok(rows)
}
fn collect_slw(rows: &mut Vec<Value>, rng: &mut StdRng) -> Result<(), String> {
    let (pk, sk) = l::setup(10, rng).map_err(|e| e.to_string())?;
    let old = l::Holder::generate(rng);
    let new = l::Holder::generate(rng);
    let attrs: Vec<_> = (100..110).map(S::from).collect();
    start_counts();
    let result = l::run_issue(&pk, &sk, &old, &attrs, rng);
    let counts = stop_counts();
    let (root, exchange) = result.map_err(|e| e.to_string())?;
    rows.push(row(
        "SLW+25",
        "Issue",
        "native-interactive-total",
        1,
        exchange.bytes(),
        counts,
    ));
    start_counts();
    let result = l::run_delegate(&pk, &old, &new, &root, &[2, 3, 4, 5, 6, 7], rng);
    let counts = stop_counts();
    let (child, exchange) = result.map_err(|e| e.to_string())?;
    rows.push(row(
        "SLW+25",
        "Delegate",
        "native-interactive-total",
        1,
        exchange.bytes(),
        counts,
    ));
    for (cred, holder, which) in [
        (&root, &old, "native-interactive-original-total"),
        (&child, &new, "native-interactive-child-total"),
    ] {
        start_counts();
        let result = l::run_show(&pk, holder, cred, &[2, 3, 4], rng);
        let counts = stop_counts();
        let exchange = result.map_err(|e| e.to_string())?;
        let mut value = row("SLW+25", "Show+Verify", which, 1, exchange.bytes(), counts);
        value["wire_kind"] = json!("full-bidirectional-interaction");
        value["business_attributes"] = json!(10);
        rows.push(value);
    }
    Ok(())
}
fn collect_msb(rows: &mut Vec<Value>, rng: &mut StdRng) -> Result<(), String> {
    use m::{scheme as s, wire as w};
    let (pp, issuer) = s::setup(9, rng)?;
    let v = s::register(pp)?;
    let user = s::user_keygen(rng);
    let agent = s::user_keygen(rng);
    start_counts();
    let (q, state) = s::issue_begin(&v, &user, (101..110).map(S::from).collect(), rng)?;
    let qb = w::encode_issue_request(&q).len();
    let (c, vs) = s::issue_challenge(&v, q, rng)?;
    let cb = c.bytes().len();
    let (response, state) = s::issue_respond(state, c)?;
    let rb = response.bytes().len();
    let d = s::issue_issuer(&v, &issuer, vs, response, rng)?;
    let db = w::encode_issue_delivery(&d).len();
    let root = s::issue_finish(&v, state, d, rng)?;
    let counts = stop_counts();
    rows.push(row(
        "MSB+23",
        "Issue",
        "native-interactive-total",
        1,
        qb + cb + rb + db,
        counts,
    ));
    start_counts();
    let (q, state) = s::delegate_begin(&v, &agent, vec![s::period_attribute()], rng)?;
    let qb = w::encode_delegate_request(&q).len();
    let d = s::delegate_sender(&v, &root, q, rng)?;
    let db = w::encode_delegate_delivery(&d).len();
    let child = s::delegate_finish(&v, state, d, rng)?;
    let counts = stop_counts();
    rows.push(row(
        "MSB+23",
        "Delegate",
        "native-interactive-total",
        1,
        qb + db,
        counts,
    ));
    for (cred, disclosed, which) in [
        (
            &root,
            s::Disclosure {
                indices: vec![1],
                sets: vec![vec![S::from(101), S::from(102), S::from(103)]],
            },
            "native-interactive-original-total",
        ),
        (
            &child,
            s::Disclosure {
                indices: vec![1, 2],
                sets: vec![
                    vec![S::from(101), S::from(102)],
                    vec![s::period_attribute()],
                ],
            },
            "native-interactive-child-total",
        ),
    ] {
        start_counts();
        let (q, state) = s::show_begin(
            &v,
            cred,
            disclosed.clone(),
            b"spend/test/ctx-v1".to_vec(),
            rng,
        )?;
        let qb = w::encode_show_first(&q).len();
        let (c, vs) = s::show_challenge(&v, q, &disclosed, b"spend/test/ctx-v1", rng)?;
        let cb = c.bytes().len();
        let response = s::show_respond(state, c)?;
        let rb = response.bytes().len();
        if !s::show_verify(&v, vs, response) {
            return Err("MSB native interaction rejected".into());
        }
        let counts = stop_counts();
        let mut value = row("MSB+23", "Show+Verify", which, 1, qb + cb + rb, counts);
        value["wire_kind"] = json!("full-bidirectional-interaction");
        value["business_attributes"] = json!(9);
        rows.push(value);
    }
    Ok(())
}
