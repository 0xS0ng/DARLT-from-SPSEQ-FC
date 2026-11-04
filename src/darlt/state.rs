//! DARLT holder state: allocation creates the right to spend in a child.
//!
//! Cryptographic verification precedes receipt registration. A parent has no
//! spending handle. Allocation is permanent, including interrupted deliveries;
//! each child has its own unit locks, while serial locks span every child and
//! parent held by the same key. Snapshot encoding is separate from hot calls.
use crate::common::state::Serial;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeSet, HashMap},
    fmt,
    sync::{Arc, Mutex, MutexGuard},
};

pub type ParentId = [u8; 32];
pub type ChildId = [u8; 32];
pub type KeyId = [u8; 32];
pub type RequestHash = [u8; 32];

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Position {
    pub pool: usize,
    pub offset: usize,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Unit {
    pub position: Position,
    pub serial: Serial,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum PoolState {
    Unallocated,
    Allocated(ChildId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StateError {
    InvalidParent,
    ParentConflict,
    UnknownParent,
    WrongOwner,
    EmptyRequest,
    InvalidScope,
    ChildConflict,
    UnknownChild,
    WrongHolder,
    PoolUnavailable,
    RequestConflict,
    UnknownAllocation,
    EmptyDelivery,
    DeliveryConflict,
    EmptyBatch,
    DuplicateUnit,
    DuplicateSerial,
    OutsideScope,
    UnitReserved,
    SerialUsed,
    UnknownReservation,
    EmptyToken,
    TokenConflict,
    InvalidBlockSize,
    Snapshot(String),
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

fn checked_request(request: &[u8]) -> Result<RequestHash> {
    if request.is_empty() {
        Err(StateError::EmptyRequest)
    } else {
        Ok(request_hash(request))
    }
}

fn lock<T>(mutex: &Mutex<T>) -> Result<MutexGuard<'_, T>> {
    mutex.lock().map_err(|_| StateError::Poisoned)
}

fn canonical_pools(pools: &[usize], count: usize) -> Result<Vec<usize>> {
    if pools.is_empty() || pools.iter().any(|&pool| pool >= count) {
        return Err(StateError::InvalidScope);
    }
    let ordered: BTreeSet<_> = pools.iter().copied().collect();
    if ordered.len() != pools.len() {
        return Err(StateError::InvalidScope);
    }
    Ok(ordered.into_iter().collect())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
struct Parent {
    id: ParentId,
    owner: KeyId,
    pool_size: usize,
    pools: Vec<PoolState>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
struct Child {
    id: ChildId,
    parent: ParentId,
    recipient: KeyId,
    pools: Vec<usize>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
struct Allocation {
    parent: ParentId,
    owner: KeyId,
    child: ChildId,
    recipient: KeyId,
    request: Vec<u8>,
    pools: Vec<usize>,
    delivery: Option<Vec<u8>>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
struct Reservation {
    child: ChildId,
    key: KeyId,
    request: Vec<u8>,
    units: Vec<Unit>,
    token: Option<Vec<u8>>,
}

type AllocationKey = (ParentId, RequestHash);
type ReservationKey = (ChildId, RequestHash);

#[derive(Default)]
struct Inner {
    parents: HashMap<ParentId, Parent>,
    children: HashMap<ChildId, Child>,
    allocations: HashMap<AllocationKey, Allocation>,
    reservations: HashMap<ReservationKey, Reservation>,
    units: HashMap<(ChildId, Position), ReservationKey>,
    serials: HashMap<(KeyId, Serial), ReservationKey>,
}

#[derive(Clone, Default)]
pub struct HolderStore {
    inner: Arc<Mutex<Inner>>,
}

#[derive(Clone)]
pub struct ChildHandle {
    store: HolderStore,
    child: ChildId,
    key: KeyId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AllocationOutcome {
    pub child: ChildId,
    pub replayed: bool,
    pub delivery: Option<Vec<u8>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReservationOutcome {
    pub child: ChildId,
    pub request_hash: RequestHash,
    pub replayed: bool,
    pub token: Option<Vec<u8>>,
    pub units: usize,
}

impl HolderStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register_parent(
        &self,
        id: ParentId,
        owner: KeyId,
        pool_count: usize,
        pool_size: usize,
    ) -> Result<()> {
        let _span = crate::darlt::instrumentation::span("state_access");
        if pool_count == 0 || pool_size == 0 || pool_count.checked_mul(pool_size).is_none() {
            return Err(StateError::InvalidParent);
        }
        let mut inner = lock(&self.inner)?;
        if let Some(old) = inner.parents.get(&id) {
            return if (old.owner, old.pools.len(), old.pool_size) == (owner, pool_count, pool_size)
            {
                Ok(())
            } else {
                Err(StateError::ParentConflict)
            };
        }
        inner.parents.insert(
            id,
            Parent {
                id,
                owner,
                pool_size,
                pools: vec![PoolState::Unallocated; pool_count],
            },
        );
        Ok(())
    }

    /// Call after checking the recipient request and before producing a child.
    /// No release operation exists. An interrupted operation still owns its
    /// pools, and an exact retry retains the same child identity and delivery.
    #[allow(clippy::too_many_arguments)]
    pub fn allocate(
        &self,
        parent: ParentId,
        owner: KeyId,
        child: ChildId,
        recipient: KeyId,
        request: &[u8],
        pools: &[usize],
    ) -> Result<AllocationOutcome> {
        let _span = crate::darlt::instrumentation::span("state_access");
        let hash = checked_request(request)?;
        let mut inner = lock(&self.inner)?;
        let source = inner
            .parents
            .get(&parent)
            .ok_or(StateError::UnknownParent)?;
        if source.owner != owner {
            return Err(StateError::WrongOwner);
        }
        let pools = canonical_pools(pools, source.pools.len())?;
        if let Some(old) = inner.allocations.get(&(parent, hash)) {
            if (old.owner, old.child, old.recipient) != (owner, child, recipient)
                || old.request != request
                || old.pools != pools
            {
                return Err(StateError::RequestConflict);
            }
            return Ok(AllocationOutcome {
                child,
                replayed: true,
                delivery: old.delivery.clone(),
            });
        }
        if inner.children.contains_key(&child) {
            return Err(StateError::ChildConflict);
        }
        if pools
            .iter()
            .any(|&pool| source.pools[pool] != PoolState::Unallocated)
        {
            return Err(StateError::PoolUnavailable);
        }
        let source = inner.parents.get_mut(&parent).expect("checked parent");
        for &pool in &pools {
            source.pools[pool] = PoolState::Allocated(child);
        }
        inner.children.insert(
            child,
            Child {
                id: child,
                parent,
                recipient,
                pools: pools.clone(),
            },
        );
        inner.allocations.insert(
            (parent, hash),
            Allocation {
                parent,
                owner,
                child,
                recipient,
                request: request.to_vec(),
                pools,
                delivery: None,
            },
        );
        Ok(AllocationOutcome {
            child,
            replayed: false,
            delivery: None,
        })
    }

    /// Bind complete delivery bytes before transmission; this includes every
    /// freshly sampled table mask and authorization opening. Retries reuse them.
    pub fn bind_delivery(
        &self,
        parent: ParentId,
        owner: KeyId,
        request: &[u8],
        delivery: &[u8],
    ) -> Result<AllocationOutcome> {
        let _span = crate::darlt::instrumentation::span("state_access");
        let hash = checked_request(request)?;
        if delivery.is_empty() {
            return Err(StateError::EmptyDelivery);
        }
        let mut inner = lock(&self.inner)?;
        let entry = inner
            .allocations
            .get_mut(&(parent, hash))
            .ok_or(StateError::UnknownAllocation)?;
        if entry.owner != owner {
            return Err(StateError::WrongOwner);
        }
        if entry.request != request {
            return Err(StateError::RequestConflict);
        }
        let replayed = entry.delivery.is_some();
        if let Some(old) = &entry.delivery {
            if old != delivery {
                return Err(StateError::DeliveryConflict);
            }
        } else {
            entry.delivery = Some(delivery.to_vec());
        }
        Ok(AllocationOutcome {
            child: entry.child,
            replayed,
            delivery: entry.delivery.clone(),
        })
    }

    /// The receiver registers a child only after the complete cryptographic
    /// receipt checks. Its local store need not contain the owner's allocation
    /// history. Self-use and remote children obtain the same spending handle.
    pub fn receive_child(
        &self,
        parent: ParentId,
        child: ChildId,
        recipient: KeyId,
        pools: &[usize],
    ) -> Result<ChildHandle> {
        let _span = crate::darlt::instrumentation::span("state_access");
        let mut inner = lock(&self.inner)?;
        let source = inner
            .parents
            .get(&parent)
            .ok_or(StateError::UnknownParent)?;
        let entry = Child {
            id: child,
            parent,
            recipient,
            pools: canonical_pools(pools, source.pools.len())?,
        };
        if let Some(old) = inner.children.get(&child) {
            if *old != entry {
                return Err(StateError::ChildConflict);
            }
        } else {
            inner.children.insert(child, entry);
        }
        Ok(ChildHandle {
            store: self.clone(),
            child,
            key: recipient,
        })
    }

    pub fn child_handle(&self, child: ChildId, key: KeyId) -> Result<ChildHandle> {
        let _span = crate::darlt::instrumentation::span("state_access");
        if lock(&self.inner)?
            .children
            .get(&child)
            .ok_or(StateError::UnknownChild)?
            .recipient
            != key
        {
            return Err(StateError::WrongHolder);
        }
        Ok(ChildHandle {
            store: self.clone(),
            child,
            key,
        })
    }

    pub fn pool_states(&self, parent: ParentId) -> Result<Vec<PoolState>> {
        let _span = crate::darlt::instrumentation::span("state_access");
        Ok(lock(&self.inner)?
            .parents
            .get(&parent)
            .ok_or(StateError::UnknownParent)?
            .pools
            .clone())
    }

    pub fn serial_reserved(&self, key: KeyId, serial: Serial) -> Result<bool> {
        let _span = crate::darlt::instrumentation::span("state_access");
        Ok(lock(&self.inner)?.serials.contains_key(&(key, serial)))
    }

    /// (allocated children, unit reservations, serial locks).
    pub fn counts(&self) -> Result<(usize, usize, usize)> {
        let _span = crate::darlt::instrumentation::span("state_access");
        let inner = lock(&self.inner)?;
        Ok((
            inner.allocations.len(),
            inner.units.len(),
            inner.serials.len(),
        ))
    }
}

impl ChildHandle {
    pub fn child(&self) -> ChildId {
        self.child
    }

    /// Read the complete-request cache without computing a new preparation.
    /// An existing reservation with no token remains interrupted and locked.
    pub fn lookup(&self, request: &[u8]) -> Result<Option<ReservationOutcome>> {
        let _span = crate::darlt::instrumentation::span("state_access");
        let hash = checked_request(request)?;
        let inner = lock(&self.store.inner)?;
        let child = inner
            .children
            .get(&self.child)
            .ok_or(StateError::UnknownChild)?;
        if child.recipient != self.key {
            return Err(StateError::WrongHolder);
        }
        let Some(old) = inner.reservations.get(&(self.child, hash)) else {
            return Ok(None);
        };
        if old.key != self.key || old.request != request {
            return Err(StateError::RequestConflict);
        }
        Ok(Some(ReservationOutcome {
            child: self.child,
            request_hash: hash,
            replayed: true,
            token: old.token.clone(),
            units: old.units.len(),
        }))
    }

    /// Reserve the entire block atomically before finishing its token. The
    /// request bytes bind the exact intended context, policy and selected units.
    /// A replay with no token is an interrupted reservation, not a new attempt.
    pub fn reserve(&self, request: &[u8], units: &[Unit]) -> Result<ReservationOutcome> {
        let _span = crate::darlt::instrumentation::span("state_access");
        let hash = checked_request(request)?;
        if units.is_empty() {
            return Err(StateError::EmptyBatch);
        }
        let mut ordered = units.to_vec();
        ordered.sort_by_key(|unit| unit.position);
        if ordered
            .windows(2)
            .any(|pair| pair[0].position == pair[1].position)
        {
            return Err(StateError::DuplicateUnit);
        }
        if units
            .iter()
            .map(|unit| unit.serial)
            .collect::<BTreeSet<_>>()
            .len()
            != units.len()
        {
            return Err(StateError::DuplicateSerial);
        }
        let mut inner = lock(&self.store.inner)?;
        let child = inner
            .children
            .get(&self.child)
            .ok_or(StateError::UnknownChild)?;
        if child.recipient != self.key {
            return Err(StateError::WrongHolder);
        }
        let parent = inner
            .parents
            .get(&child.parent)
            .ok_or(StateError::UnknownParent)?;
        if ordered.iter().any(|unit| {
            unit.position.offset >= parent.pool_size
                || child.pools.binary_search(&unit.position.pool).is_err()
        }) {
            return Err(StateError::OutsideScope);
        }
        let reservation_key = (self.child, hash);
        if let Some(old) = inner.reservations.get(&reservation_key) {
            if old.key != self.key || old.request != request || old.units != ordered {
                return Err(StateError::RequestConflict);
            }
            return Ok(ReservationOutcome {
                child: self.child,
                request_hash: hash,
                replayed: true,
                token: old.token.clone(),
                units: ordered.len(),
            });
        }
        if ordered
            .iter()
            .any(|unit| inner.serials.contains_key(&(self.key, unit.serial)))
        {
            return Err(StateError::SerialUsed);
        }
        if ordered
            .iter()
            .any(|unit| inner.units.contains_key(&(self.child, unit.position)))
        {
            return Err(StateError::UnitReserved);
        }
        for unit in &ordered {
            inner
                .serials
                .insert((self.key, unit.serial), reservation_key);
            inner
                .units
                .insert((self.child, unit.position), reservation_key);
        }
        inner.reservations.insert(
            reservation_key,
            Reservation {
                child: self.child,
                key: self.key,
                request: request.to_vec(),
                units: ordered.clone(),
                token: None,
            },
        );
        Ok(ReservationOutcome {
            child: self.child,
            request_hash: hash,
            replayed: false,
            token: None,
            units: ordered.len(),
        })
    }

    pub fn bind_token(&self, request: &[u8], token: &[u8]) -> Result<ReservationOutcome> {
        let _span = crate::darlt::instrumentation::span("state_access");
        let hash = checked_request(request)?;
        if token.is_empty() {
            return Err(StateError::EmptyToken);
        }
        let mut inner = lock(&self.store.inner)?;
        let entry = inner
            .reservations
            .get_mut(&(self.child, hash))
            .ok_or(StateError::UnknownReservation)?;
        if entry.key != self.key || entry.request != request {
            return Err(StateError::RequestConflict);
        }
        let replayed = entry.token.is_some();
        if let Some(old) = &entry.token {
            if old != token {
                return Err(StateError::TokenConflict);
            }
        } else {
            entry.token = Some(token.to_vec());
        }
        Ok(ReservationOutcome {
            child: self.child,
            request_hash: hash,
            replayed,
            token: entry.token.clone(),
            units: entry.units.len(),
        })
    }
}

#[derive(Deserialize, Serialize)]
struct Snapshot {
    version: u32,
    parents: Vec<Parent>,
    children: Vec<Child>,
    allocations: Vec<Allocation>,
    reservations: Vec<Reservation>,
}

impl HolderStore {
    pub fn encode_snapshot(&self) -> Result<Vec<u8>> {
        let inner = lock(&self.inner)?;
        let mut snapshot = Snapshot {
            version: 21,
            parents: inner.parents.values().cloned().collect(),
            children: inner.children.values().cloned().collect(),
            allocations: inner.allocations.values().cloned().collect(),
            reservations: inner.reservations.values().cloned().collect(),
        };
        snapshot.parents.sort_by_key(|entry| entry.id);
        snapshot.children.sort_by_key(|entry| entry.id);
        snapshot
            .allocations
            .sort_by_key(|entry| (entry.parent, request_hash(&entry.request)));
        snapshot
            .reservations
            .sort_by_key(|entry| (entry.child, request_hash(&entry.request)));
        serde_json::to_vec(&snapshot).map_err(|error| StateError::Snapshot(error.to_string()))
    }

    /// Rebuild all locks from versioned records. Old Owner/SelfReserved
    /// snapshots do not silently gain DARLT semantics.
    pub fn decode_snapshot(bytes: &[u8]) -> Result<Self> {
        let snapshot: Snapshot = serde_json::from_slice(bytes)
            .map_err(|error| StateError::Snapshot(error.to_string()))?;
        if snapshot.version != 21 {
            return Err(StateError::Snapshot("unsupported version".into()));
        }
        let store = Self::new();
        let mut seen = BTreeSet::new();
        for parent in &snapshot.parents {
            if !seen.insert(parent.id) {
                return Err(StateError::Snapshot("duplicate parent".into()));
            }
            store.register_parent(
                parent.id,
                parent.owner,
                parent.pools.len(),
                parent.pool_size,
            )?;
        }
        let mut seen = BTreeSet::new();
        for entry in &snapshot.allocations {
            if !seen.insert((entry.parent, request_hash(&entry.request))) {
                return Err(StateError::Snapshot("duplicate allocation".into()));
            }
            store.allocate(
                entry.parent,
                entry.owner,
                entry.child,
                entry.recipient,
                &entry.request,
                &entry.pools,
            )?;
            if let Some(delivery) = &entry.delivery {
                store.bind_delivery(entry.parent, entry.owner, &entry.request, delivery)?;
            }
        }
        let mut seen = BTreeSet::new();
        for child in &snapshot.children {
            if !seen.insert(child.id) {
                return Err(StateError::Snapshot("duplicate child".into()));
            }
            store.receive_child(child.parent, child.id, child.recipient, &child.pools)?;
        }
        if lock(&store.inner)?.children.len() != snapshot.children.len() {
            return Err(StateError::Snapshot("missing allocated child".into()));
        }
        let mut seen = BTreeSet::new();
        for entry in &snapshot.reservations {
            if !seen.insert((entry.child, request_hash(&entry.request))) {
                return Err(StateError::Snapshot("duplicate reservation".into()));
            }
            let handle = store.child_handle(entry.child, entry.key)?;
            handle.reserve(&entry.request, &entry.units)?;
            if let Some(token) = &entry.token {
                handle.bind_token(&entry.request, token)?;
            }
        }
        for parent in &snapshot.parents {
            if store.pool_states(parent.id)? != parent.pools {
                return Err(StateError::Snapshot("pool allocation mismatch".into()));
            }
        }
        Ok(store)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Chunk {
    pub child: ChildId,
    pub positions: Vec<Position>,
}

/// Group every occurrence of the same child before splitting into blocks.
/// The first child occurrence and its unit order define the output order.
/// Position uniqueness is per child; aliases across distinct credentials are
/// rejected by the shared per-key serial lock when reserving actual serials.
pub fn split_requests(requests: Vec<(ChildId, Vec<Position>)>, k_max: usize) -> Result<Vec<Chunk>> {
    if k_max == 0 {
        return Err(StateError::InvalidBlockSize);
    }
    if requests.is_empty() {
        return Err(StateError::EmptyBatch);
    }
    let mut groups: Vec<(ChildId, Vec<Position>)> = Vec::new();
    let mut indices = HashMap::new();
    let mut seen = BTreeSet::new();
    for (child, positions) in requests {
        if positions.is_empty() {
            return Err(StateError::EmptyBatch);
        }
        let index = *indices.entry(child).or_insert_with(|| {
            groups.push((child, Vec::new()));
            groups.len() - 1
        });
        for position in positions {
            if !seen.insert((child, position)) {
                return Err(StateError::DuplicateUnit);
            }
            groups[index].1.push(position);
        }
    }
    Ok(groups
        .into_iter()
        .flat_map(|(child, positions)| {
            positions
                .chunks(k_max)
                .map(|chunk| Chunk {
                    child,
                    positions: chunk.to_vec(),
                })
                .collect::<Vec<_>>()
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{sync::Barrier, thread};

    fn unit(pool: usize, offset: usize, serial: u8) -> Unit {
        Unit {
            position: Position { pool, offset },
            serial: Serial([serial; 48]),
        }
    }

    fn store() -> HolderStore {
        let store = HolderStore::new();
        store.register_parent([1; 32], [2; 32], 4, 16).unwrap();
        store
    }

    #[test]
    fn parent_cannot_spend_and_self_use_requires_explicit_allocation() {
        let store = store();
        assert!(matches!(
            store.child_handle([1; 32], [2; 32]),
            Err(StateError::UnknownChild)
        ));
        store
            .allocate([1; 32], [2; 32], [3; 32], [2; 32], b"self child", &[1, 2])
            .unwrap();
        let before = store.pool_states([1; 32]).unwrap();
        let child = store.child_handle([3; 32], [2; 32]).unwrap();
        child.reserve(b"first spend", &[unit(1, 0, 7)]).unwrap();
        assert_eq!(store.pool_states([1; 32]).unwrap(), before);
        assert_eq!(
            before,
            vec![
                PoolState::Unallocated,
                PoolState::Allocated([3; 32]),
                PoolState::Allocated([3; 32]),
                PoolState::Unallocated
            ]
        );
        assert_eq!(
            child.reserve(b"outside", &[unit(0, 0, 8)]),
            Err(StateError::OutsideScope)
        );
        assert_eq!(
            child.reserve(b"bad offset", &[unit(1, 16, 8)]),
            Err(StateError::OutsideScope)
        );
    }

    #[test]
    fn interrupted_allocations_do_not_release_pools_or_partially_allocate() {
        let store = store();
        store
            .allocate([1; 32], [2; 32], [3; 32], [4; 32], b"first", &[0])
            .unwrap();
        assert_eq!(
            store.allocate([1; 32], [2; 32], [5; 32], [4; 32], b"overlap", &[0, 1]),
            Err(StateError::PoolUnavailable)
        );
        assert_eq!(
            store.pool_states([1; 32]).unwrap()[1],
            PoolState::Unallocated
        );
        let restored = HolderStore::decode_snapshot(&store.encode_snapshot().unwrap()).unwrap();
        assert_eq!(
            restored.pool_states([1; 32]).unwrap()[0],
            PoolState::Allocated([3; 32])
        );
        assert_eq!(
            restored.allocate([1; 32], [2; 32], [5; 32], [4; 32], b"after restart", &[0]),
            Err(StateError::PoolUnavailable)
        );
    }

    #[test]
    fn allocation_and_delivery_retries_bind_exact_child_and_bytes() {
        let store = store();
        assert!(
            !store
                .allocate([1; 32], [2; 32], [3; 32], [4; 32], b"request", &[0, 1])
                .unwrap()
                .replayed
        );
        assert!(
            !store
                .bind_delivery([1; 32], [2; 32], b"request", b"response")
                .unwrap()
                .replayed
        );
        let replay = store
            .allocate([1; 32], [2; 32], [3; 32], [4; 32], b"request", &[1, 0])
            .unwrap();
        assert!(replay.replayed);
        assert_eq!(replay.delivery.as_deref(), Some(&b"response"[..]));
        assert_eq!(
            store.allocate([1; 32], [2; 32], [5; 32], [4; 32], b"request", &[0, 1]),
            Err(StateError::RequestConflict)
        );
        assert_eq!(
            store.bind_delivery([1; 32], [2; 32], b"request", b"other"),
            Err(StateError::DeliveryConflict)
        );
        assert_eq!(
            store.bind_delivery([1; 32], [9; 32], b"request", b"response"),
            Err(StateError::WrongOwner)
        );
    }

    #[test]
    fn serial_locks_span_children_and_parents_with_the_same_holder_key() {
        let store = store();
        store.register_parent([8; 32], [2; 32], 4, 16).unwrap();
        store
            .allocate([1; 32], [2; 32], [3; 32], [4; 32], b"child a", &[0])
            .unwrap();
        store
            .allocate([8; 32], [2; 32], [5; 32], [4; 32], b"child b", &[0])
            .unwrap();
        let a = store.child_handle([3; 32], [4; 32]).unwrap();
        let b = store.child_handle([5; 32], [4; 32]).unwrap();
        a.reserve(b"a", &[unit(0, 0, 7)]).unwrap();
        assert_eq!(
            b.reserve(b"b", &[unit(0, 1, 7), unit(0, 2, 8)]),
            Err(StateError::SerialUsed)
        );
        assert!(!store.serial_reserved([4; 32], Serial([8; 48])).unwrap());
        b.reserve(b"c", &[unit(0, 0, 9)]).unwrap();
        assert_eq!(store.counts().unwrap(), (2, 2, 2));
        assert_eq!(
            a.reserve(b"new serial same unit", &[unit(0, 0, 10)]),
            Err(StateError::UnitReserved)
        );
    }

    #[test]
    fn interrupted_spend_and_exact_token_retries_persist() {
        let store = store();
        store
            .allocate([1; 32], [2; 32], [3; 32], [4; 32], b"child", &[0])
            .unwrap();
        let a = store.child_handle([3; 32], [4; 32]).unwrap();
        a.reserve(b"interrupted", &[unit(0, 0, 7)]).unwrap();
        a.reserve(b"bound", &[unit(0, 1, 8)]).unwrap();
        a.bind_token(b"bound", b"token A").unwrap();
        assert_eq!(
            a.bind_token(b"bound", b"token B"),
            Err(StateError::TokenConflict)
        );
        let restored = HolderStore::decode_snapshot(&store.encode_snapshot().unwrap()).unwrap();
        let a = restored.child_handle([3; 32], [4; 32]).unwrap();
        assert!(
            a.reserve(b"interrupted", &[unit(0, 0, 7)])
                .unwrap()
                .replayed
        );
        assert_eq!(
            a.reserve(b"new context", &[unit(0, 0, 7)]),
            Err(StateError::SerialUsed)
        );
        let replay = a.reserve(b"bound", &[unit(0, 1, 8)]).unwrap();
        assert_eq!(replay.token.as_deref(), Some(&b"token A"[..]));
        assert_eq!(
            a.reserve(b"bound", &[unit(0, 2, 9)]),
            Err(StateError::RequestConflict)
        );
    }

    #[test]
    fn receiver_can_register_only_received_scope_in_its_own_store() {
        let receiver = store();
        let child = receiver
            .receive_child([1; 32], [3; 32], [4; 32], &[2])
            .unwrap();
        child.reserve(b"received", &[unit(2, 0, 7)]).unwrap();
        assert!(receiver
            .pool_states([1; 32])
            .unwrap()
            .iter()
            .all(|p| *p == PoolState::Unallocated));
        assert!(matches!(
            receiver.child_handle([3; 32], [2; 32]),
            Err(StateError::WrongHolder)
        ));
        assert!(matches!(
            receiver.receive_child([1; 32], [3; 32], [4; 32], &[3]),
            Err(StateError::ChildConflict)
        ));
    }

    #[test]
    fn concurrent_allocations_have_one_winner() {
        let store = store();
        let barrier = Arc::new(Barrier::new(2));
        let joins: Vec<_> = (3u8..5)
            .map(|id| {
                let store = store.clone();
                let barrier = barrier.clone();
                thread::spawn(move || {
                    barrier.wait();
                    store.allocate([1; 32], [2; 32], [id; 32], [9; 32], &[id], &[0])
                })
            })
            .collect();
        assert_eq!(
            joins
                .into_iter()
                .map(|j| j.join().unwrap())
                .filter(Result::is_ok)
                .count(),
            1
        );
    }

    #[test]
    fn concurrent_serial_aliases_have_one_winner() {
        let store = store();
        store
            .allocate([1; 32], [2; 32], [3; 32], [9; 32], b"a", &[0])
            .unwrap();
        store
            .allocate([1; 32], [2; 32], [4; 32], [9; 32], b"b", &[1])
            .unwrap();
        let barrier = Arc::new(Barrier::new(2));
        let joins: Vec<_> = [(3, 0), (4, 1)]
            .into_iter()
            .map(|(id, pool)| {
                let child = store.child_handle([id; 32], [9; 32]).unwrap();
                let barrier = barrier.clone();
                thread::spawn(move || {
                    barrier.wait();
                    child.reserve(&[id], &[unit(pool, 0, 7)])
                })
            })
            .collect();
        assert_eq!(
            joins
                .into_iter()
                .map(|j| j.join().unwrap())
                .filter(Result::is_ok)
                .count(),
            1
        );
        assert_eq!(store.counts().unwrap(), (2, 1, 1));
    }

    #[test]
    fn snapshot_rejects_old_version_duplicates_and_changed_allocation() {
        let store = store();
        store
            .allocate([1; 32], [2; 32], [3; 32], [4; 32], b"a", &[0])
            .unwrap();
        let encoded = store.encode_snapshot().unwrap();
        let mut snapshot: Snapshot = serde_json::from_slice(&encoded).unwrap();
        snapshot.version = 1;
        assert!(HolderStore::decode_snapshot(&serde_json::to_vec(&snapshot).unwrap()).is_err());
        snapshot.version = 21;
        snapshot.parents[0].pools[0] = PoolState::Unallocated;
        assert!(HolderStore::decode_snapshot(&serde_json::to_vec(&snapshot).unwrap()).is_err());
        let mut snapshot: Snapshot = serde_json::from_slice(&encoded).unwrap();
        snapshot.children.push(snapshot.children[0].clone());
        assert!(HolderStore::decode_snapshot(&serde_json::to_vec(&snapshot).unwrap()).is_err());
    }

    #[test]
    fn blocks_are_grouped_by_child_before_splitting() {
        let pos = |offset| Position { pool: 0, offset };
        let blocks =
            split_requests(vec![([3; 32], vec![pos(0)]), ([4; 32], vec![pos(0)])], 64).unwrap();
        assert_eq!(
            blocks.iter().map(|b| b.positions.len()).collect::<Vec<_>>(),
            vec![1, 1]
        );
        let blocks = split_requests(
            vec![
                ([3; 32], vec![pos(0), pos(1)]),
                ([4; 32], vec![pos(0)]),
                ([3; 32], vec![pos(2), pos(3)]),
            ],
            3,
        )
        .unwrap();
        assert_eq!(
            blocks
                .iter()
                .map(|b| (b.child[0], b.positions.len()))
                .collect::<Vec<_>>(),
            vec![(3, 3), (3, 1), (4, 1)]
        );
        assert_eq!(blocks[1].positions, vec![pos(3)]);
        assert_eq!(
            split_requests(vec![([3; 32], vec![pos(0)]), ([3; 32], vec![pos(0)])], 64),
            Err(StateError::DuplicateUnit)
        );
        assert_eq!(
            split_requests(vec![([3; 32], vec![pos(0)])], 0),
            Err(StateError::InvalidBlockSize)
        );
    }
}
