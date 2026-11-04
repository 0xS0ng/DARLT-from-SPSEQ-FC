//! One opaque-identifier spent set for all native protocol adapters.
use crate::common::state::{request_hash, Acceptance, RequestHash, Result, StateError};
use std::{
    collections::{BTreeSet, HashMap},
    sync::{Arc, Mutex},
};

/// Store all native bytes, including both NIAT tag points. The server-owned
/// namespace binds the native scheme/key domain. Native service/period fields
/// remain in their original identifier; no new period reset is imposed on
/// globally single-use tokens.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Identifier {
    namespace: Vec<u8>,
    value: Vec<u8>,
}
impl Identifier {
    pub fn new(namespace: &[u8], value: &[u8]) -> Result<Self> {
        if namespace.is_empty()
            || namespace.len() > 512
            || value.is_empty()
            || value.len() > 8 * 1024 * 1024
        {
            return Err(StateError::InvalidIdentifier);
        }
        Ok(Self {
            namespace: namespace.to_vec(),
            value: value.to_vec(),
        })
    }
    pub fn namespace(&self) -> &[u8] {
        &self.namespace
    }
    pub fn value(&self) -> &[u8] {
        &self.value
    }
}
#[derive(Clone)]
struct Accepted {
    request: Vec<u8>,
    ids: Vec<Identifier>,
    response: Vec<u8>,
}
#[derive(Clone, Default)]
struct Inner {
    used: HashMap<Identifier, RequestHash>,
    requests: HashMap<RequestHash, Accepted>,
}
#[derive(Clone, Default)]
pub struct SpentStore {
    inner: Arc<Mutex<Inner>>,
}
/// An owned deep snapshot. Unlike `SpentStore::clone`, restored stores do not
/// share a mutex or any subsequently registered request with their source.
#[derive(Clone)]
pub struct SpentSnapshot {
    inner: Inner,
}
impl SpentStore {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn snapshot(&self) -> Result<SpentSnapshot> {
        Ok(SpentSnapshot {
            inner: self.inner.lock().map_err(|_| StateError::Poisoned)?.clone(),
        })
    }
    pub fn from_snapshot(snapshot: &SpentSnapshot) -> Self {
        Self {
            inner: Arc::new(Mutex::new(snapshot.inner.clone())),
        }
    }
    pub fn with_preexisting_records(
        count: usize,
        namespace: &[u8],
        id_bytes: usize,
    ) -> Result<Self> {
        if !(8..=8 * 1024 * 1024).contains(&id_bytes) {
            return Err(StateError::InvalidIdentifier);
        }
        let store = Self::new();
        for i in 0..count {
            let mut request = b"shared-preexisting-record/".to_vec();
            request.extend((i as u64).to_be_bytes());
            let mut id = vec![0; id_bytes];
            for (j, c) in id.chunks_mut(32).enumerate() {
                let mut x = request.clone();
                x.extend((j as u64).to_be_bytes());
                c.copy_from_slice(&request_hash(&x)[..c.len()]);
            }
            store.record_checked(&request, &[Identifier::new(namespace, &id)?], &[])?;
        }
        Ok(store)
    }
    /// The cryptographic caller supplies already-verified complete identifiers.
    /// Any conflict rejects the complete transaction before inserting a prefix.
    pub fn record_checked(
        &self,
        request: &[u8],
        ids: &[Identifier],
        response: &[u8],
    ) -> Result<Acceptance> {
        let _verification_span = crate::darlt::instrumentation::span("verification.state");
        let _span = crate::darlt::instrumentation::span("state_access");
        if request.is_empty() {
            return Err(StateError::EmptyRequest);
        }
        if ids.is_empty() {
            return Err(StateError::EmptyBatch);
        }
        let sorted: BTreeSet<_> = ids.iter().cloned().collect();
        if sorted.len() != ids.len() {
            return Err(StateError::DuplicateSerial);
        }
        let ids: Vec<_> = sorted.into_iter().collect();
        let hash = request_hash(request);
        let mut inner = self.inner.lock().map_err(|_| StateError::Poisoned)?;
        if let Some(old) = inner.requests.get(&hash) {
            if old.request != request {
                return Err(StateError::RequestHashCollision);
            }
            if old.ids != ids {
                return Err(StateError::RequestConflict);
            }
            return Ok(Acceptance {
                request_hash: hash,
                response: old.response.clone(),
                replayed: true,
                newly_registered: 0,
            });
        }
        if ids.iter().any(|id| inner.used.contains_key(id)) {
            return Err(StateError::SerialUsed);
        }
        let count = ids.len();
        for id in &ids {
            inner.used.insert(id.clone(), hash);
        }
        inner.requests.insert(
            hash,
            Accepted {
                request: request.to_vec(),
                ids,
                response: response.to_vec(),
            },
        );
        Ok(Acceptance {
            request_hash: hash,
            response: response.to_vec(),
            replayed: false,
            newly_registered: count,
        })
    }
    pub fn counts(&self) -> Result<(usize, usize)> {
        let inner = self.inner.lock().map_err(|_| StateError::Poisoned)?;
        Ok((inner.requests.len(), inner.used.len()))
    }
    pub fn contains(&self, id: &Identifier) -> Result<bool> {
        Ok(self
            .inner
            .lock()
            .map_err(|_| StateError::Poisoned)?
            .used
            .contains_key(id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{sync::Barrier, thread};
    fn id(v: u8) -> Identifier {
        Identifier::new(b"NIAT/issuer/period", &[v; 96]).unwrap()
    }
    #[test]
    fn restored_snapshots_are_deep_and_reexecute_registration() {
        let original = SpentStore::new();
        original
            .record_checked(b"history", &[id(1)], b"old")
            .unwrap();
        let snapshot = original.snapshot().unwrap();
        let a = SpentStore::from_snapshot(&snapshot);
        let b = SpentStore::from_snapshot(&snapshot);
        for store in [&a, &b] {
            let result = store.record_checked(b"new", &[id(2)], b"ok").unwrap();
            assert!(!result.replayed);
            assert_eq!(result.newly_registered, 1);
            assert_eq!(store.counts().unwrap(), (2, 2));
        }
        assert_eq!(original.counts().unwrap(), (1, 1));
        assert_eq!(
            SpentStore::from_snapshot(&snapshot).counts().unwrap(),
            (1, 1)
        );
    }
    #[test]
    fn complete_tags_exact_retry_and_conflict_atomicity() {
        let store = SpentStore::new();
        let a = id(1);
        let mut b = a.clone();
        b.value[95] = 2;
        assert_ne!(a, b);
        assert_eq!(a.value().len(), 96);
        store
            .record_checked(b"one", std::slice::from_ref(&a), b"first")
            .unwrap();
        assert_eq!(
            store.record_checked(b"two", &[b.clone(), a.clone()], b""),
            Err(StateError::SerialUsed)
        );
        assert!(!store.contains(&b).unwrap());
        assert!(
            store
                .record_checked(b"one", std::slice::from_ref(&a), b"different")
                .unwrap()
                .replayed
        );
        assert_eq!(
            store.record_checked(b"dup", &[b.clone(), b], b""),
            Err(StateError::DuplicateSerial)
        );
        assert_eq!(store.counts().unwrap(), (1, 1));
    }
    #[test]
    fn namespaces_preload_and_concurrent_atomic_commit() {
        let store = SpentStore::with_preexisting_records(10000, b"NIAT/issuer/period", 96).unwrap();
        assert_eq!(store.counts().unwrap(), (10000, 10000));
        let barrier = Arc::new(Barrier::new(3));
        let jobs: Vec<_> = (0u8..2)
            .map(|i| {
                let s = store.clone();
                let b = barrier.clone();
                thread::spawn(move || {
                    b.wait();
                    s.record_checked(&[i + 1], &[id(7), id(i + 8)], b"ok")
                })
            })
            .collect();
        barrier.wait();
        assert_eq!(
            jobs.into_iter()
                .map(|j| j.join().unwrap())
                .filter(Result::is_ok)
                .count(),
            1
        );
        assert_eq!(store.counts().unwrap(), (10001, 10002));
        assert!(store
            .record_checked(
                b"different-domain",
                &[Identifier::new(b"other-issuer", &[7; 96]).unwrap()],
                b""
            )
            .is_ok());
    }
}
