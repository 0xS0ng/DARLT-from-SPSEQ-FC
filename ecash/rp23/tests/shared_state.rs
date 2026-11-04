use darlt_spseq_fc::{
    batch_runtime::{self as rt, Adapter, Error, Mode},
    common::spent::SpentStore,
    common::state::StateError,
};
use rand::{rngs::StdRng, SeedableRng};
use rp23_native::{api::*, shared_runtime::*};
const M: [u8; 16] = [7; 16];
fn info(n: u8) -> PayInfo {
    PayInfo::new(M, [n; 16])
}
fn exercise<A: Adapter>(
    adapter: &A,
    items: &[A::Item],
    bad: &[A::Item],
    ids_per_item: usize,
    id_bytes: usize,
) where
    A::Item: Clone,
{
    let mut r = StdRng::seed_from_u64(219);
    let s = SpentStore::with_preexisting_records(10000, adapter.namespace(), id_bytes).unwrap();
    let result = rt::verify_and_record(
        adapter,
        items,
        b"native-payment",
        b"first-response",
        &s,
        Mode::Randomized,
        &mut r,
    )
    .unwrap();
    assert_eq!(result.newly_registered, items.len() * ids_per_item);
    let counts = s.counts().unwrap();
    let retry = rt::verify_and_record(
        adapter,
        items,
        b"native-payment",
        b"replacement",
        &s,
        Mode::Randomized,
        &mut r,
    )
    .unwrap();
    assert!(retry.replayed);
    assert_eq!(retry.response, b"first-response");
    assert_eq!(s.counts().unwrap(), counts);
    assert!(matches!(
        rt::verify_and_record(
            adapter,
            items,
            b"new-request",
            b"",
            &s,
            Mode::Randomized,
            &mut r
        ),
        Err(Error::State(StateError::SerialUsed))
    ));
    assert_eq!(s.counts().unwrap(), counts);
    let duplicate = SpentStore::new();
    assert!(rt::verify_and_record(
        adapter,
        &[items[0].clone(), items[0].clone()],
        b"duplicate",
        b"",
        &duplicate,
        Mode::Randomized,
        &mut r
    )
    .is_err());
    assert_eq!(duplicate.counts().unwrap(), (0, 0));
    let fresh = SpentStore::new();
    let Err(Error::CryptoRejected(d)) =
        rt::verify_and_record(adapter, bad, b"bad", b"", &fresh, Mode::Randomized, &mut r)
    else {
        panic!("native cryptographic rejection")
    };
    assert_eq!(d.bad_indices, vec![1, 3]);
    assert_eq!(fresh.counts().unwrap(), (0, 0));
    assert!(d
        .attempts
        .iter()
        .filter(|a| a.items == 1)
        .all(|a| a.mode == Mode::Randomized));
    // A later already-spent native payment rejects the full request without registering its good prefix.
    let s = SpentStore::new();
    rt::verify_and_record(
        adapter,
        &items[3..4],
        b"previous",
        b"",
        &s,
        Mode::Specification,
        &mut r,
    )
    .unwrap();
    let counts = s.counts().unwrap();
    assert!(
        rt::verify_and_record(adapter, items, b"mixed", b"", &s, Mode::Randomized, &mut r).is_err()
    );
    assert_eq!(s.counts().unwrap(), counts);
}
#[test]
fn compact_shared_native_payment_state_and_balanced_fallback() {
    let c = Compact::new(64).unwrap();
    let w = c.issue().unwrap();
    let p: Vec<_> = (0..4).map(|i| c.spend(&w, 3, info(i)).unwrap()).collect();
    let mut bad = p.clone();
    for i in [1, 3] {
        bad[i].native.zk_proof = bad[i].native.zk_proof.with_invalid_challenge();
    }
    let p: Vec<_> = p.into_iter().map(|p| c.check_payment(p).unwrap()).collect();
    let bad: Vec<_> = bad
        .into_iter()
        .map(|p| c.check_payment(p).unwrap())
        .collect();
    exercise(&CompactVerifier::new(&c, M), &p, &bad, 3, 48);
}
#[test]
fn divisible_shared_complete_native_deposit_state_and_balanced_fallback() {
    let d = Divisible::new(64).unwrap();
    let w = d.issue().unwrap();
    let p: Vec<_> = (0..4).map(|i| d.spend(&w, 3, info(i)).unwrap()).collect();
    let mut bad = p.clone();
    for i in [1, 3] {
        bad[i].native.zk_proof = bad[i].native.zk_proof.with_invalid_challenge();
    }
    let p: Vec<_> = p.into_iter().map(|p| d.check_payment(p).unwrap()).collect();
    let bad: Vec<_> = bad
        .into_iter()
        .map(|p| d.check_payment(p).unwrap())
        .collect();
    exercise(&DivisibleVerifier::new(&d, M), &p, &bad, 3, 288);
}
