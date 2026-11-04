//! Shared cryptographic batch fallback and atomic state for protocol adapters.
use crate::{
    common::spent::{Identifier, SpentStore},
    common::state::{Acceptance, StateError},
};
use rand::{CryptoRng, RngCore};
use serde::Serialize;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub enum Mode {
    Specification,
    Randomized,
}

/// An adapter always retains its native statements/proofs and backend work.
/// Completed interactive transcripts are rechecked here for state/fallback;
/// live verifier message generation is timed separately in the role harness.
pub trait Adapter {
    type Item;
    fn scheme(&self) -> &'static str;
    fn namespace(&self) -> &[u8];
    fn verify<R: RngCore + CryptoRng>(&self, items: &[Self::Item], mode: Mode, rng: &mut R)
        -> bool;
    fn identifiers(&self, items: &[Self::Item]) -> Result<Vec<Vec<u8>>, String>;
    fn wire_messages(&self, item: &Self::Item) -> Vec<Vec<u8>>;
    fn public_identifiers(&self, _item: &Self::Item) -> Option<Vec<Vec<u8>>> {
        None
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Attempt {
    pub start: usize,
    pub items: usize,
    pub mode: Mode,
    pub accepted: bool,
}
#[derive(Clone, Debug, Serialize)]
pub struct Diagnosis {
    pub bad_indices: Vec<usize>,
    pub attempts: Vec<Attempt>,
    pub unit_of_localization: &'static str,
    pub reason: &'static str,
}
#[derive(Debug)]
pub enum Error {
    EmptyBatch,
    CryptoRejected(Diagnosis),
    Backend(String),
    State(StateError),
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}

/// Identical balanced binary splitting for every scheme. Native single-item
/// verification uses fresh verifier coins at every node, including a leaf.
/// This diagnoses proof/payment objects, not hidden units inside one proof.
pub fn diagnose<A: Adapter, R: RngCore + CryptoRng>(
    adapter: &A,
    items: &[A::Item],
    rng: &mut R,
) -> Diagnosis {
    diagnose_impl(adapter, items, rng, None)
}

fn diagnose_impl<A: Adapter, R: RngCore + CryptoRng>(
    adapter: &A,
    items: &[A::Item],
    rng: &mut R,
    first_failed: Option<Mode>,
) -> Diagnosis {
    fn visit<A: Adapter, R: RngCore + CryptoRng>(
        a: &A,
        x: &[A::Item],
        offset: usize,
        r: &mut R,
        out: &mut Diagnosis,
    ) {
        if x.is_empty() {
            return;
        }
        let mode = Mode::Randomized;
        let accepted = a.verify(x, mode, r);
        out.attempts.push(Attempt {
            start: offset,
            items: x.len(),
            mode,
            accepted,
        });
        if accepted {
            return;
        }
        if x.len() == 1 {
            out.bad_indices.push(offset);
            return;
        }
        let mid = x.len() / 2;
        visit(a, &x[..mid], offset, r, out);
        visit(a, &x[mid..], offset + mid, r, out);
    }
    if let Some(out) = duplicate_diagnosis(adapter, items) {
        return out;
    }
    let mut out = Diagnosis {
        bad_indices: vec![],
        attempts: vec![],
        unit_of_localization: "native token, native block, or completed native presentation",
        reason: "cryptographic verification failed",
    };
    if let Some(mode) = first_failed {
        out.attempts.push(Attempt {
            start: 0,
            items: items.len(),
            mode,
            accepted: false,
        });
        if items.len() == 1 {
            out.bad_indices.push(0);
        } else if !items.is_empty() {
            let mid = items.len() / 2;
            visit(adapter, &items[..mid], 0, rng, &mut out);
            visit(adapter, &items[mid..], mid, rng, &mut out);
        }
    } else {
        visit(adapter, items, 0, rng, &mut out);
    }
    out
}

fn duplicate_diagnosis<A: Adapter>(adapter: &A, items: &[A::Item]) -> Option<Diagnosis> {
    let mut owners = std::collections::BTreeMap::<Vec<u8>, Vec<usize>>::new();
    for (i, item) in items.iter().enumerate() {
        for id in adapter.public_identifiers(item)? {
            owners.entry(id).or_default().push(i);
        }
    }
    let bad: BTreeSet<_> = owners
        .into_values()
        .filter(|v| v.len() > 1)
        .flatten()
        .collect();
    (!bad.is_empty()).then(|| Diagnosis {
        bad_indices: bad.into_iter().collect(),
        attempts: vec![],
        unit_of_localization: "native token, native block, or completed native presentation",
        reason: "duplicate complete identifiers",
    })
}

pub fn bound_request<A: Adapter>(
    adapter: &A,
    items: &[A::Item],
    application_request: &[u8],
) -> Vec<u8> {
    fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
        out.extend((bytes.len() as u64).to_be_bytes());
        out.extend(bytes);
    }
    let mut out = b"DARLT-experiments/native-batch-state/v1".to_vec();
    frame(&mut out, adapter.scheme().as_bytes());
    frame(&mut out, adapter.namespace());
    frame(&mut out, application_request);
    out.extend((items.len() as u64).to_be_bytes());
    for item in items {
        let messages = adapter.wire_messages(item);
        out.extend((messages.len() as u64).to_be_bytes());
        for message in messages {
            frame(&mut out, &message);
        }
    }
    out
}

/// Full verification, native identifier recovery, then one shared atomic spent
/// transaction. No successful subset is registered when a bad batch is found.
pub fn verify_and_record<A: Adapter, R: RngCore + CryptoRng>(
    adapter: &A,
    items: &[A::Item],
    application_request: &[u8],
    response: &[u8],
    store: &SpentStore,
    mode: Mode,
    rng: &mut R,
) -> Result<Acceptance, Error> {
    if items.is_empty() {
        return Err(Error::EmptyBatch);
    }
    if application_request.is_empty() {
        return Err(Error::State(StateError::EmptyRequest));
    }
    if let Some(d) = duplicate_diagnosis(adapter, items) {
        return Err(Error::CryptoRejected(d));
    }
    if !adapter.verify(items, mode, rng) {
        return Err(Error::CryptoRejected(diagnose_impl(
            adapter,
            items,
            rng,
            Some(mode),
        )));
    }
    let ids = adapter
        .identifiers(items)
        .map_err(Error::Backend)?
        .iter()
        .map(|id| Identifier::new(adapter.namespace(), id))
        .collect::<Result<Vec<_>, _>>()
        .map_err(Error::State)?;
    let request = bound_request(adapter, items, application_request);
    store
        .record_checked(&request, &ids, response)
        .map_err(Error::State)
}

/// Return repeated native identifiers as an explicit pre-state diagnostic.
pub fn duplicate_ids(ids: &[Vec<u8>]) -> bool {
    let mut seen = BTreeSet::new();
    ids.iter().any(|id| !seen.insert(id))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    struct Fake;
    impl Adapter for Fake {
        type Item = (u8, bool);
        fn scheme(&self) -> &'static str {
            "state-test"
        }
        fn namespace(&self) -> &[u8] {
            b"checked-test-domain"
        }
        fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], _: Mode, _: &mut R) -> bool {
            !x.is_empty() && x.iter().all(|a| a.1)
        }
        fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
            Ok(x.iter().map(|a| vec![a.0; 96]).collect())
        }
        fn wire_messages(&self, x: &Self::Item) -> Vec<Vec<u8>> {
            vec![vec![x.0, u8::from(x.1)]]
        }
    }
    #[test]
    fn common_rule_balanced_localization_never_commits_a_good_prefix() {
        let mut r = StdRng::seed_from_u64(21202);
        let store = SpentStore::new();
        let bad = [(1, true), (2, false), (3, true), (4, false), (5, true)];
        let d = diagnose(&Fake, &bad, &mut r);
        assert_eq!(d.bad_indices, [1, 3]);
        assert!(d.attempts.iter().all(|a| a.mode == Mode::Randomized));
        assert!(d.attempts.iter().any(|a| a.items == 1));
        assert!(matches!(
            verify_and_record(&Fake, &bad, b"bad", b"", &store, Mode::Randomized, &mut r),
            Err(Error::CryptoRejected(_))
        ));
        assert_eq!(store.counts().unwrap(), (0, 0));
        let good = [(1, true), (2, true)];
        assert_eq!(
            verify_and_record(
                &Fake,
                &good,
                b"good",
                b"first",
                &store,
                Mode::Randomized,
                &mut r
            )
            .unwrap()
            .newly_registered,
            2
        );
        let retry = verify_and_record(
            &Fake,
            &good,
            b"good",
            b"newresponse",
            &store,
            Mode::Randomized,
            &mut r,
        )
        .unwrap();
        assert!(retry.replayed);
        assert_eq!(retry.response, b"first");
        assert!(matches!(
            verify_and_record(
                &Fake,
                &[(3, true), (1, true)],
                b"conflict",
                b"",
                &store,
                Mode::Randomized,
                &mut r
            ),
            Err(Error::State(StateError::SerialUsed))
        ));
        assert_eq!(store.counts().unwrap(), (1, 2));
    }
}
