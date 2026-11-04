//! Fixed-size serials and a facade over the shared verifier spent set.
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};
use std::fmt;

pub type RequestHash = [u8; 32];
pub const DEFAULT_PREEXISTING_RECORDS: usize = 10_000;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Serial(pub [u8; 48]);
impl Serialize for Serial {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.0)
    }
}
impl<'de> Deserialize<'de> for Serial {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> std::result::Result<Self, D::Error> {
        let value = Vec::<u8>::deserialize(deserializer)?;
        let bytes = value
            .try_into()
            .map_err(|_| serde::de::Error::custom("serial must contain 48 bytes"))?;
        Ok(Self(bytes))
    }
}
impl From<[u8; 48]> for Serial {
    fn from(value: [u8; 48]) -> Self {
        Self(value)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StateError {
    EmptyRequest,
    RequestHashMismatch,
    RequestHashCollision,
    EmptyBatch,
    DuplicateSerial,
    DuplicateUnit,
    SerialUsed,
    UnitReserved,
    InvalidWallet,
    WalletConflict,
    UnknownWallet,
    WrongOwner,
    InvalidScope,
    ScopeConflict,
    UnknownGrant,
    GrantConflict,
    OutsideScope,
    PoolUnavailable,
    UnknownReservation,
    RequestConflict,
    EmptyToken,
    InvalidIdentifier,
    TokenConflict,
    Snapshot(String),
    Io(String),
    Poisoned,
}
impl fmt::Display for StateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for StateError {}
pub type Result<T> = std::result::Result<T, StateError>;

pub fn request_hash(request: &[u8]) -> RequestHash {
    Sha256::digest(request).into()
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Acceptance {
    pub request_hash: RequestHash,
    pub response: Vec<u8>,
    pub replayed: bool,
    pub newly_registered: usize,
}
/// Fixed-size compatibility facade over the common opaque-identifier store.
#[derive(Clone, Default)]
pub struct VerifierStore {
    shared: crate::common::spent::SpentStore,
}
impl VerifierStore {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with_preexisting_records(count: usize) -> Result<Self> {
        Ok(Self {
            shared: crate::common::spent::SpentStore::with_preexisting_records(
                count,
                b"native-G1-serial",
                48,
            )?,
        })
    }
    pub fn benchmark() -> Result<Self> {
        Self::with_preexisting_records(DEFAULT_PREEXISTING_RECORDS)
    }
    pub fn record_checked(
        &self,
        request: &[u8],
        serials: &[Serial],
        response: &[u8],
    ) -> Result<Acceptance> {
        let ids = serials
            .iter()
            .map(|s| crate::common::spent::Identifier::new(b"native-G1-serial", &s.0))
            .collect::<Result<Vec<_>>>()?;
        self.shared.record_checked(request, &ids, response)
    }
    pub fn counts(&self) -> Result<(usize, usize)> {
        self.shared.counts()
    }
    pub fn contains(&self, serial: Serial) -> Result<bool> {
        self.shared.contains(&crate::common::spent::Identifier::new(
            b"native-G1-serial",
            &serial.0,
        )?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        sync::{Arc, Barrier},
        thread,
    };

    fn serial(value: u8) -> Serial {
        Serial([value; 48])
    }

    #[test]
    fn verifier_batch_conflict_does_not_insert_a_prefix_and_retry_is_exact() {
        let store = VerifierStore::new();
        store
            .record_checked(b"first", &[serial(1)], b"old result")
            .unwrap();
        assert_eq!(
            store.record_checked(b"second", &[serial(2), serial(1)], b"new"),
            Err(StateError::SerialUsed)
        );
        assert!(!store.contains(serial(2)).unwrap());
        assert_eq!(store.counts().unwrap(), (1, 1));
        let retry = store
            .record_checked(b"first", &[serial(1)], b"different response")
            .unwrap();
        assert!(retry.replayed);
        assert_eq!(retry.response, b"old result");
        assert_eq!(
            store.record_checked(b"first", &[serial(2)], b"ignored"),
            Err(StateError::RequestConflict)
        );
    }

    #[test]
    fn verifier_rejects_duplicate_batch_and_has_shared_preloaded_state() {
        let store = VerifierStore::benchmark().unwrap();
        assert_eq!(store.counts().unwrap(), (10_000, 10_000));
        assert_eq!(
            store.record_checked(b"dup", &[serial(8), serial(8)], b""),
            Err(StateError::DuplicateSerial)
        );
        store
            .clone()
            .record_checked(b"fresh", &[serial(8)], b"ok")
            .unwrap();
        assert!(store.contains(serial(8)).unwrap());
        assert_eq!(store.counts().unwrap(), (10_001, 10_001));
    }

    #[test]
    fn concurrent_verifier_accepts_only_one_overlapping_batch() {
        let store = VerifierStore::new();
        let barrier = Arc::new(Barrier::new(3));
        let jobs: Vec<_> = (0u8..2)
            .map(|i| {
                let store = store.clone();
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    barrier.wait();
                    store.record_checked(&[i + 1], &[serial(1), serial(i + 2)], b"ok")
                })
            })
            .collect();
        barrier.wait();
        let results: Vec<_> = jobs.into_iter().map(|job| job.join().unwrap()).collect();
        assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
        assert_eq!(store.counts().unwrap(), (1, 2));
    }
}
