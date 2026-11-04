//! Stateful DARLT facade. Only an explicitly allocated child can reserve units.
//!
//! Delivery bytes and token bytes are bound before transmission. Cryptographic
//! preparation/completion can be timed independently from these state calls.
use super::{
    params::Dimensions,
    protocol::{
        self, Delivery, Holder, IssueRequest, IssueResponse, IssuerPublic, IssuerSecret,
        OwnerOpening, PublicParameters, Wallet,
    },
    spend::{self, Policy, ReceivedToken, Token},
    state::{self, ChildId, HolderStore, KeyId, ParentId, Position, ReservationOutcome, Unit},
    verification::Mode,
};
use crate::{
    common::crypto::{frame, valid1, valid2},
    common::state::{Acceptance, Serial, VerifierStore},
    polynomial::{Domain, S},
    spseq_fc,
};
use blstrs::{G1Projective as G1, G2Projective as G2};
use ff::Field;
use group::Group;
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, sync::Arc};

pub type Result<T> = std::result::Result<T, String>;

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn key_id(public_key: G1) -> KeyId {
    let mut bytes = b"DARLT/key-fingerprint".to_vec();
    bytes.extend(public_key.to_compressed());
    Sha256::digest(bytes).into()
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn state_result<T>(result: state::Result<T>) -> Result<T> {
    result.map_err(|error| format!("DARLT holder state: {error}"))
}

/// Static installation checks. Honest Setup is the source of SRS algebraic
/// consistency; this checks every received object's encoding/group and the
/// installed dimensions, fingerprint and deterministic derived query cache.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn check_parameters(pp: &PublicParameters, ip: &IssuerPublic) -> Result<[u8; 32]> {
    let _span = crate::darlt::instrumentation::span("parameter_installation");
    let dim = Dimensions::new(pp.w, pp.s, pp.k_max)?;
    let srs = &pp.srs;
    if pp.w.checked_mul(pp.s) != Some(pp.n)
        || pp.k_del == 0
        || pp.k_del > 128
        || pp.k_prv > 128
        || srs.w != pp.w
        || srs.s != pp.s
        || srs.k_max != pp.k_max
        || srs.k_padded != dim.k_padded
        || srs.n != dim.n
        || srs.degree != dim.degree
        || srs.domain.size != dim.table_size
        || srs.g1.len() != dim.degree + 1
        || srs.lagrange.len() != pp.w.max(pp.s)
        || srs.k_hat.len() != pp.w.max(pp.s)
        || srs.d_hat.len() != pp.w
        || srs.o_hat.len() != pp.s
        || pp.fc.pools.len() != pp.w
        || pp.fc.attrs.len() != pp.k_del
        || pp.adel.len() != pp.k_del
        || pp.bprv.len() != pp.k_prv
        || pp.grant_bases.len() != pp.k_del
    {
        return Err("public parameter dimensions rejected".into());
    }
    let domain = Domain::new(dim.table_size)?;
    if srs.domain.omega != domain.omega
        || srs.domain.elements != domain.elements
        || srs.g2.keys().copied().collect::<Vec<_>>()
            != [
                0,
                1,
                2,
                3,
                dim.n,
                dim.degree - dim.n + 2,
                dim.degree - dim.n + 4,
            ]
        || srs.g1[0] != pp.ghat
        || srs.g2[&0] != G2::generator()
        || pp.fc.pools != srs.lagrange[..pp.w]
        || !spseq_fc::validate_instance(&pp.fc, &ip.vk)
    {
        return Err("public parameter domain or signature instance rejected".into());
    }
    if [pp.ghat, pp.h, pp.hdel, pp.hprv, srs.vanishing]
        .iter()
        .any(|point| !valid1(*point, true))
        || !valid1(srs.offset, false)
        || [&pp.adel, &pp.bprv, &pp.grant_bases, &srs.g1, &srs.lagrange]
            .into_iter()
            .flatten()
            .any(|point| !valid1(*point, false))
        || srs
            .g2
            .values()
            .chain(&srs.k_hat)
            .chain(&srs.d_hat)
            .chain(&srs.o_hat)
            .any(|point| !valid2(*point, false))
    {
        return Err("public parameter curve/subgroup rejected".into());
    }
    let mut size = 1;
    let mut expected = Vec::new();
    loop {
        expected.push(size);
        let installed = pp
            .query_bases
            .get(&size)
            .ok_or("missing query-domain cache")?;
        if installed.0.len() != size
            || installed.0.iter().any(|point| !valid1(*point, false))
            || !valid1(installed.1, true)
            || *installed != srs.query_basis(size)?
        {
            return Err("derived query-domain cache rejected".into());
        }
        if size == dim.k_padded {
            break;
        }
        size *= 2;
    }
    if pp.query_bases.keys().copied().collect::<Vec<_>>() != expected {
        return Err("unexpected query-domain cache".into());
    }
    let expected_id: [u8; 32] = Sha256::digest(pp.encode()).into();
    if pp.id != expected_id {
        return Err("public parameter fingerprint rejected".into());
    }
    Ok(expected_id)
}

#[derive(Clone)]
pub struct ProtocolContext {
    pp: Arc<PublicParameters>,
    ip: Arc<IssuerPublic>,
    parameter_digest: [u8; 32],
    issuer_public: Arc<[u8]>,
    state: HolderStore,
}

/// The identifiers are local state indices; they are not new token fields.
#[derive(Clone, Debug)]
pub struct Child {
    pub parent: ParentId,
    pub id: ChildId,
    pub holder: Holder,
}

#[derive(Clone, Debug)]
pub struct Delegation {
    pub parent: ParentId,
    pub child: ChildId,
    pub delivery: Delivery,
    pub replayed: bool,
}

/// Only successful native Valid can create this immutable metadata record.
/// It retains the signed points and the installed issuer binding, not a new
/// protocol message or a permission to skip validation on an arbitrary token.
pub struct VerifiedMetadataRecord {
    r: G1,
    e: G1,
    issuer: Arc<[u8]>,
}
pub struct MetadataReader {
    secrets: [S; 2],
    issuer: Arc<[u8]>,
}
impl MetadataReader {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn read_validated(&self, record: &VerifiedMetadataRecord) -> Option<usize> {
        if self.issuer != record.issuer {
            return None;
        }
        // Valid accepted a nonidentity R and installation accepted distinct
        // metadata public keys, so at most one bit can match this record.
        (0..2).find(|i| record.r * self.secrets[*i] == record.e)
    }
}

impl ProtocolContext {
    /// Reader-key acceptance is installation work, charged separately from
    /// reading one already-verified record.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn metadata_reader(&self, secrets: [S; 2]) -> Result<MetadataReader> {
        if secrets.map(|x| G1::generator() * x) != self.ip.metadata_keys {
            return Err("metadata reader key rejected".into());
        }
        Ok(MetadataReader {
            secrets,
            issuer: self.issuer_public.clone(),
        })
    }
    pub fn verify_metadata_record(
        &self,
        token: &Token,
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Option<VerifiedMetadataRecord> {
        self.valid(token, mode, rng)
            .then(|| VerifiedMetadataRecord {
                r: token.auth.message[4],
                e: token.auth.message[5],
                issuer: self.issuer_public.clone(),
            })
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn new(pp: Arc<PublicParameters>, ip: Arc<IssuerPublic>) -> Result<Self> {
        Self::with_state(pp, ip, HolderStore::new())
    }

    /// Share this store across contexts when the same holder key is used with
    /// multiple installed credentials. Its serial locks are keyed by key alone.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn with_state(
        pp: Arc<PublicParameters>,
        ip: Arc<IssuerPublic>,
        state: HolderStore,
    ) -> Result<Self> {
        let parameter_digest = check_parameters(&pp, &ip)?;
        protocol::install(&pp, &ip)?;
        let issuer_public = ip.encode().into();
        Ok(Self {
            pp,
            ip,
            parameter_digest,
            issuer_public,
            state,
        })
    }

    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn parameters(&self) -> &PublicParameters {
        &self.pp
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn issuer(&self) -> &IssuerPublic {
        &self.ip
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn holder_state(&self) -> &HolderStore {
        &self.state
    }

    /// A new local wallet-state namespace for the same accepted immutable
    /// installation. Parameter and issuer installation are not repeated here.
    pub(crate) fn fresh_holder_context(&self) -> Self {
        Self {
            pp: self.pp.clone(),
            ip: self.ip.clone(),
            parameter_digest: self.parameter_digest,
            issuer_public: self.issuer_public.clone(),
            state: HolderStore::new(),
        }
    }

    /// Recipient first message for an installed instance. The agent needs no
    /// parent message, parent credential, or parent secret.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn delegation_request(
        &self,
        sid: &[u8],
        ska: S,
        rng: &mut impl RngCore,
    ) -> Result<spseq_fc::Request> {
        spseq_fc::request_installed(&self.parameter_digest, &self.issuer_public, sid, ska, rng)
    }

    /// Register the accepted typed wallet returned by `protocol::accept`.
    /// Acceptance already checked its signature, metadata and derivation key;
    /// registration itself does not repeat pairings on the self-use path.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn register_wallet(&self, wallet: &Wallet) -> Result<ParentId> {
        if wallet.pp_id != self.pp.id
            || wallet.issuer_id != <[u8; 32]>::from(Sha256::digest(self.ip.encode()))
            || wallet.parent.len() != 8
            || wallet.sku == S::ZERO
            || wallet.parent[3] != G1::generator() * wallet.sku
            || wallet.seeds.iter().any(|row| row.len() != self.pp.w)
            || wallet.mdel.len() != self.pp.k_del
            || wallet.mprv.len() != self.pp.k_prv
        {
            return Err("accepted parent wallet dimensions or owner binding rejected".into());
        }
        let parent = wallet.id();
        state_result(self.state.register_parent(
            parent,
            key_id(wallet.parent[3]),
            self.pp.w,
            self.pp.s,
        ))?;
        Ok(parent)
    }

    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    fn allocation_request(
        &self,
        parent: ParentId,
        kind: &[u8],
        request: &[u8],
        gamma: &[usize],
        delta: &[bool],
    ) -> Result<Vec<u8>> {
        if request.is_empty() {
            return Err("empty allocation request".into());
        }
        let mut bytes = protocol::prefix(&self.pp, &self.ip);
        frame(&mut bytes, b"DARLT/Allocate/request/v1");
        bytes.extend(parent);
        frame(&mut bytes, kind);
        frame(&mut bytes, request);
        bytes.extend((gamma.len() as u64).to_be_bytes());
        for pool in gamma {
            bytes.extend((*pool as u64).to_be_bytes());
        }
        bytes.extend((delta.len() as u64).to_be_bytes());
        bytes.extend(delta.iter().map(|bit| u8::from(*bit)));
        Ok(bytes)
    }

    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    #[allow(clippy::too_many_arguments)]
    fn allocated_delivery(
        &self,
        wallet: &mut Wallet,
        recipient: G1,
        request: &[u8],
        gamma: &[usize],
        delta: &[bool],
        rng: &mut impl RngCore,
        received: Option<&spend::ReceivedInputs>,
    ) -> Result<Delegation> {
        protocol::scope_check(&self.pp, gamma, delta)?;
        let parent = self.register_wallet(wallet)?;
        let owner = key_id(wallet.parent[3]);
        let child: ChildId = Sha256::digest(request).into();
        let allocation = state_result(self.state.allocate(
            parent,
            owner,
            child,
            key_id(recipient),
            request,
            gamma,
        ))?;
        if let Some(bytes) = allocation.delivery {
            return Ok(Delegation {
                parent,
                child,
                delivery: Delivery::decode(&self.pp, &bytes)?,
                replayed: true,
            });
        }
        // Any failure here leaves the allocated pools and child id in place.
        let delivery = match received {
            Some(checked) => {
                protocol::derive_received(&self.pp, wallet, recipient, gamma, delta, rng, checked)
            }
            None => protocol::derive(&self.pp, wallet, recipient, gamma, delta, rng),
        }?;
        match self
            .state
            .bind_delivery(parent, owner, request, &delivery.encode())
        {
            Ok(_) => Ok(Delegation {
                parent,
                child,
                delivery,
                replayed: allocation.replayed,
            }),
            Err(state::StateError::DeliveryConflict) => {
                // Another exact concurrent retry may have bound the first
                // response while this caller was constructing an unused one.
                let cached = state_result(self.state.allocate(
                    parent,
                    owner,
                    child,
                    key_id(recipient),
                    request,
                    gamma,
                ))?;
                let bytes = cached
                    .delivery
                    .ok_or("concurrent allocation has no bound response")?;
                Ok(Delegation {
                    parent,
                    child,
                    delivery: Delivery::decode(&self.pp, &bytes)?,
                    replayed: true,
                })
            }
            Err(error) => Err(format!("DARLT holder state: {error}")),
        }
    }

    /// Verify the recipient proof against the installed instance before pool
    /// allocation. Parent binding is supplied by the local allocation state.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn delegate(
        &self,
        wallet: &mut Wallet,
        request: &spseq_fc::Request,
        gamma: &[usize],
        delta: &[bool],
        rng: &mut impl RngCore,
    ) -> Result<Delegation> {
        protocol::scope_check(&self.pp, gamma, delta)?;
        if !spseq_fc::verify_request_installed(&self.parameter_digest, &self.issuer_public, request)
        {
            return Err("recipient request rejected for installed instance".into());
        }
        let parent = self.register_wallet(wallet)?;
        let bound = self.allocation_request(parent, b"remote", &request.encode(), gamma, delta)?;
        self.allocated_delivery(wallet, request.pka, &bound, gamma, delta, rng, None)
    }
    pub(crate) fn delegate_received(
        &self,
        wallet: &mut Wallet,
        received: &protocol::ReceivedRecipientRequest,
        gamma: &[usize],
        delta: &[bool],
        rng: &mut impl RngCore,
    ) -> Result<Delegation> {
        protocol::scope_check(&self.pp, gamma, delta)?;
        let request = received.request();
        if !spseq_fc::verify_request_received(
            &self.parameter_digest,
            &self.issuer_public,
            request,
            received.inputs(),
        ) {
            return Err("received recipient request rejected for installed instance".into());
        }
        let parent = self.register_wallet(wallet)?;
        let bound = self.allocation_request(parent, b"remote", &request.encode(), gamma, delta)?;
        self.allocated_delivery(
            wallet,
            request.pka,
            &bound,
            gamma,
            delta,
            rng,
            Some(received.inputs()),
        )
    }

    /// Explicit local derivation, using the same allocation and mask refresh
    /// as remote delegation, with no pi_pk, pairing, or network message.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn self_derive(
        &self,
        wallet: &mut Wallet,
        local_request: &[u8],
        gamma: &[usize],
        rng: &mut impl RngCore,
    ) -> Result<Child> {
        let delta = vec![true; self.pp.k_del];
        protocol::scope_check(&self.pp, gamma, &delta)?;
        let parent = self.register_wallet(wallet)?;
        let bound = self.allocation_request(parent, b"local-self", local_request, gamma, &delta)?;
        let recipient = G1::generator() * wallet.sku;
        let delivery =
            self.allocated_delivery(wallet, recipient, &bound, gamma, &delta, rng, None)?;
        let holder = protocol::local_child(&self.pp, wallet, &delivery.delivery);
        state_result(
            self.state
                .receive_child(parent, delivery.child, key_id(recipient), gamma),
        )?;
        Ok(Child {
            parent,
            id: delivery.child,
            holder,
        })
    }

    /// Only this full receipt path registers remotely delivered spending rights.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn receive(
        &self,
        delivery: &Delegation,
        ska: S,
        owner: Option<OwnerOpening>,
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Result<Child> {
        let holder = protocol::complete_installed(
            &self.pp,
            &self.ip,
            &delivery.delivery,
            ska,
            owner,
            mode,
            rng,
        )?;
        state_result(self.state.register_parent(
            delivery.parent,
            key_id(holder.parent[3]),
            self.pp.w,
            self.pp.s,
        ))?;
        state_result(self.state.receive_child(
            delivery.parent,
            delivery.child,
            key_id(G1::generator() * ska),
            &holder.gamma,
        ))?;
        Ok(Child {
            parent: delivery.parent,
            id: delivery.child,
            holder,
        })
    }

    /// Reserve one prepared block. Serial computation belongs to preparation;
    /// state work is measured separately. There is deliberately no parent API.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn reserve_block(
        &self,
        child: &Child,
        request: &[u8],
        positions: &[usize],
        serials: &[[u8; 48]],
    ) -> Result<ReservationOutcome> {
        if positions.is_empty()
            || positions.len() > self.pp.k_max
            || positions.len() != serials.len()
        {
            return Err("invalid prepared block dimensions".into());
        }
        let units = positions
            .iter()
            .zip(serials)
            .map(|(&position, &serial)| {
                if position >= self.pp.n {
                    return Err("unit outside parameter capacity".to_string());
                }
                Ok(Unit {
                    position: Position {
                        pool: position / self.pp.s,
                        offset: position % self.pp.s,
                    },
                    serial: Serial(serial),
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let handle = state_result(
            self.state
                .child_handle(child.id, key_id(G1::generator() * child.holder.ska)),
        )?;
        state_result(handle.reserve(request, &units))
    }

    /// Bind the complete canonical token before transmission. An exact retry
    /// returns the already bound bytes; a different randomized token is refused.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn bind_token(
        &self,
        child: &Child,
        request: &[u8],
        bytes: &[u8],
    ) -> Result<ReservationOutcome> {
        let handle = state_result(
            self.state
                .child_handle(child.id, key_id(G1::generator() * child.holder.ska)),
        )?;
        state_result(handle.bind_token(request, bytes))
    }

    fn block_request(
        &self,
        child: ChildId,
        request: &[u8],
        positions: &[usize],
        policy: &Policy,
        context: &[u8],
    ) -> Result<Vec<u8>> {
        if request.is_empty()
            || context.is_empty()
            || positions.is_empty()
            || positions.len() > self.pp.k_max
        {
            return Err("empty or oversized block request".into());
        }
        let mut bound = protocol::prefix(&self.pp, &self.ip);
        frame(&mut bound, b"DARLT/batch-spend/request/v1");
        bound.extend(child);
        frame(&mut bound, request);
        frame(&mut bound, &policy.encode());
        frame(&mut bound, context);
        bound.extend((positions.len() as u64).to_be_bytes());
        for position in positions {
            bound.extend((*position as u64).to_be_bytes());
        }
        Ok(bound)
    }

    /// Functional block facade. Offline preparation computes serials once;
    /// the block is reserved before any online completion or transmission.
    /// Exact retries read the bound token without creating a fresh preparation.
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn spend_block(
        &self,
        child: &mut Child,
        positions: &[usize],
        policy: &Policy,
        context: &[u8],
        request: &[u8],
        rng: &mut impl RngCore,
    ) -> Result<Token> {
        let bound = self.block_request(child.id, request, positions, policy, context)?;
        let handle = state_result(
            self.state
                .child_handle(child.id, key_id(G1::generator() * child.holder.ska)),
        )?;
        if let Some(cached) = state_result(handle.lookup(&bound))? {
            let bytes = cached
                .token
                .ok_or("interrupted reservation has no token to replay")?;
            return Token::wire_decode(&self.pp, &bytes);
        }
        let prepared = spend::prepare_spend_installed(
            &self.pp,
            &self.ip,
            &mut child.holder,
            positions,
            policy,
            rng,
        )?;
        let serials = prepared.serials();
        let units = positions
            .iter()
            .zip(serials)
            .map(|(&position, serial)| Unit {
                position: Position {
                    pool: position / self.pp.s,
                    offset: position % self.pp.s,
                },
                serial: Serial(serial),
            })
            .collect::<Vec<_>>();
        let reserved = state_result(handle.reserve(&bound, &units))?;
        if reserved.replayed {
            let bytes = reserved
                .token
                .ok_or("concurrent reservation has no token to replay")?;
            return Token::wire_decode(&self.pp, &bytes);
        }
        let token = spend::finish_spend(&self.pp, &self.ip, prepared, context, rng)?;
        state_result(handle.bind_token(&bound, &token.wire_encode()))?;
        Ok(token)
    }

    /// Merge requests by child, then split within each child. Every output is
    /// a separate token with its own fixed authentication and serial block.
    #[allow(clippy::too_many_arguments)]
    pub fn spend_chunks(
        &self,
        children: &mut [Child],
        requests: Vec<(ChildId, Vec<usize>)>,
        policy: &Policy,
        context: &[u8],
        request: &[u8],
        rng: &mut impl RngCore,
    ) -> Result<Vec<Token>> {
        if request.is_empty() || context.is_empty() {
            return Err("empty complete spend request".into());
        }
        let mut indices = BTreeMap::new();
        for (index, child) in children.iter().enumerate() {
            if indices.insert(child.id, index).is_some() {
                return Err("duplicate child object".into());
            }
        }
        let typed = requests
            .into_iter()
            .map(|(child, positions)| {
                let index = *indices
                    .get(&child)
                    .ok_or("unknown child in spend request")?;
                let positions = positions
                    .into_iter()
                    .map(|position| {
                        if position >= self.pp.n
                            || !children[index]
                                .holder
                                .gamma
                                .contains(&(position / self.pp.s))
                        {
                            return Err("requested unit outside child scope".to_string());
                        }
                        Ok(Position {
                            pool: position / self.pp.s,
                            offset: position % self.pp.s,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok((child, positions))
            })
            .collect::<Result<Vec<_>>>()?;
        let blocks = state_result(state::split_requests(typed, self.pp.k_max))?;
        let mut tokens = Vec::with_capacity(blocks.len());
        for (index, block) in blocks.into_iter().enumerate() {
            let positions = block
                .positions
                .into_iter()
                .map(|position| position.pool * self.pp.s + position.offset)
                .collect::<Vec<_>>();
            let mut block_request = request.to_vec();
            frame(&mut block_request, b"child-grant/chunk");
            block_request.extend((index as u64).to_be_bytes());
            tokens.push(self.spend_block(
                &mut children[indices[&block.child]],
                &positions,
                policy,
                context,
                &block_request,
                rng,
            )?);
        }
        Ok(tokens)
    }

    /// Full dynamic token verification after immutable instance installation.
    pub fn valid(&self, token: &Token, mode: Mode, rng: &mut impl RngCore) -> bool {
        spend::valid_installed(&self.pp, &self.ip, token, mode, rng)
    }

    /// Fix and check all tokens before combining their pairing equations.
    /// This is shared by packed-block and independent-token experiments.
    pub fn valid_many(&self, tokens: &[Token], mode: Mode, rng: &mut impl RngCore) -> bool {
        spend::valid_many_installed(&self.pp, &self.ip, tokens, mode, rng)
    }
    /// Consume the immutable result of strict received decoding without
    /// repeating checks on the same received group elements.
    pub fn valid_received(
        &self,
        token: &ReceivedToken,
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> bool {
        spend::valid_received_installed(&self.pp, &self.ip, token, mode, rng)
    }
    pub fn valid_many_received(
        &self,
        tokens: &[ReceivedToken],
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> bool {
        spend::valid_many_received_installed(&self.pp, &self.ip, tokens, mode, rng)
    }

    /// Strict wire decoding, full dynamic verification, then atomic whole-block
    /// recording. The exact token bytes identify retries, rather than ctx alone.
    pub fn verify_and_record(
        &self,
        wire: &[u8],
        mode: Mode,
        rng: &mut impl RngCore,
        store: &VerifierStore,
        response: &[u8],
    ) -> Result<Acceptance> {
        let token = ReceivedToken::wire_decode(&self.pp, wire)?;
        if !self.valid_received(&token, mode, rng) {
            return Err("token rejected".into());
        }
        let serials = token.serials().into_iter().map(Serial).collect::<Vec<_>>();
        store
            .record_checked(wire, &serials, response)
            .map_err(|error| format!("verifier state: {error}"))
    }
}

/// One accepted issuance request per user for this installed issuer/period.
/// Eligibility is an external admission decision.
#[derive(Default)]
pub struct IssuerLedger {
    context: Option<[u8; 32]>,
    entries: BTreeMap<[u8; 48], (Vec<u8>, IssueResponse)>,
}
impl IssuerLedger {
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn respond(
        &mut self,
        pp: &PublicParameters,
        ip: &IssuerPublic,
        secret: &IssuerSecret,
        request: &IssueRequest,
        bit: usize,
        eligible: bool,
        rng: &mut impl RngCore,
    ) -> Result<(IssueResponse, bool)> {
        if !eligible || bit > 1 {
            return Err("issuer eligibility/metadata bit rejected".into());
        }
        let mut binding = pp.id.to_vec();
        binding.extend(ip.material());
        let binding: [u8; 32] = Sha256::digest(binding).into();
        if self.context.is_some_and(|old| old != binding) {
            return Err("issuer ledger belongs to another installed issuer/period".into());
        }
        let key = request.pku.to_compressed();
        let encoded = request.encode();
        if let Some((old, response)) = self.entries.get(&key) {
            return if *old == encoded {
                Ok((response.clone(), true))
            } else {
                Err("wallet already issued for this period".into())
            };
        }
        let response = protocol::issue(pp, ip, secret, request, bit, rng)?;
        self.context = Some(binding);
        self.entries.insert(key, (encoded, response.clone()));
        Ok((response, false))
    }
}

impl ProtocolContext {
    #[allow(clippy::too_many_arguments)]
    pub fn judge_received(
        &self,
        a: &ReceivedToken,
        ai: usize,
        b: &ReceivedToken,
        bi: usize,
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Option<(spend::Responsibility, G1)> {
        if !spend::valid_evidence_received_installed(&self.pp, &self.ip, a, b, mode, rng) {
            return None;
        }
        spend::identify_validated(&self.pp, &self.ip, a.token(), ai, b.token(), bi)
    }
    pub fn read_bit_received(
        &self,
        token: &ReceivedToken,
        secrets: &[S; 2],
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Option<usize> {
        if !self.valid_received(token, mode, rng)
            || secrets.map(|x| G1::generator() * x) != self.ip.metadata_keys
        {
            return None;
        }
        let token = token.token();
        let found: Vec<_> = (0..2)
            .filter(|i| token.auth.message[4] * secrets[*i] == token.auth.message[5])
            .collect();
        (found.len() == 1).then(|| found[0])
    }
    /// Adjudication always validates both complete records with installed keys.
    #[allow(clippy::too_many_arguments)]
    pub fn judge(
        &self,
        a: &Token,
        ai: usize,
        b: &Token,
        bi: usize,
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Option<(spend::Responsibility, G1)> {
        if !spend::valid_evidence_installed(&self.pp, &self.ip, a, b, mode, rng) {
            return None;
        }
        spend::identify_validated(&self.pp, &self.ip, a, ai, b, bi)
    }
    /// Reading the signed hidden bit includes one complete installed Valid.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn read_bit(
        &self,
        token: &Token,
        secrets: &[S; 2],
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Option<usize> {
        if !self.valid(token, mode, rng)
            || secrets.map(|x| G1::generator() * x) != self.ip.metadata_keys
        {
            return None;
        }
        let found: Vec<_> = (0..2)
            .filter(|i| token.auth.message[4] * secrets[*i] == token.auth.message[5])
            .collect();
        (found.len() == 1).then(|| found[0])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    fn fixture() -> (StdRng, ProtocolContext, Wallet, IssuerSecret) {
        fixture_with_bit(1)
    }
    fn fixture_with_bit(bit: usize) -> (StdRng, ProtocolContext, Wallet, IssuerSecret) {
        let mut rng = StdRng::seed_from_u64(0x2100c0);
        let pp = Arc::new(
            PublicParameters::setup(16, 4, 8, 3, 2, b"context test period", &mut rng).unwrap(),
        );
        let (ip, secret) = protocol::keygen(&pp, &mut rng).unwrap();
        let ip = Arc::new(ip);
        let (request, openings) =
            protocol::prepare_request(&pp, &ip, S::from(7), &[S::ONE; 3], &[S::ONE; 2], &mut rng)
                .unwrap();
        let response = protocol::issue(&pp, &ip, &secret, &request, bit, &mut rng).unwrap();
        let wallet = protocol::accept(&pp, &ip, &request, &openings, &response, &mut rng).unwrap();
        let context = ProtocolContext::new(pp, ip).unwrap();
        (rng, context, wallet, secret)
    }

    #[test]
    fn request_and_judge_batch_all_record_equations_without_weakening_serial_rules() {
        struct Coins {
            rng: StdRng,
            bytes: usize,
        }
        impl Coins {
            fn new() -> Self {
                Self {
                    rng: StdRng::seed_from_u64(33_024),
                    bytes: 0,
                }
            }
        }
        impl RngCore for Coins {
            fn next_u32(&mut self) -> u32 {
                self.bytes += 4;
                self.rng.next_u32()
            }
            fn next_u64(&mut self) -> u64 {
                self.bytes += 8;
                self.rng.next_u64()
            }
            fn fill_bytes(&mut self, b: &mut [u8]) {
                self.bytes += b.len();
                self.rng.fill_bytes(b);
            }
            fn try_fill_bytes(&mut self, b: &mut [u8]) -> std::result::Result<(), rand::Error> {
                self.bytes += b.len();
                self.rng.try_fill_bytes(b)
            }
        }
        let (mut rng, context, mut wallet, _) = fixture();
        let child = context
            .self_derive(&mut wallet, b"combined evidence", &[0, 1], &mut rng)
            .unwrap();
        let policy = Policy {
            period: 1,
            atoms: vec![spend::Atom::Equal(0, S::ONE)],
        };
        let mut records = vec![];
        for (position, ctx) in [
            (0, &b"context-a"[..]),
            (4, &b"context-c"[..]),
            (0, &b"context-b"[..]),
        ] {
            let mut holder = child.holder.clone();
            let prepared = spend::prepare_spend_installed(
                &context.pp,
                &context.ip,
                &mut holder,
                &[position],
                &policy,
                &mut rng,
            )
            .unwrap();
            let token =
                spend::finish_spend(&context.pp, &context.ip, prepared, ctx, &mut rng).unwrap();
            records.push(ReceivedToken::wire_decode(&context.pp, &token.wire_encode()).unwrap());
        }
        let mut coins = Coins::new();
        crate::ops::reset();
        assert!(context.valid_many_received(&records[..2], Mode::Randomized, &mut coins));
        let counts = crate::ops::stop();
        println!(
            "R033_STEP_BATCH {}",
            serde_json::json!({"step":"ValidAcrossBlocks","blocks":2,"coefficient_bytes_observed":coins.bytes,"coefficients_observed":coins.bytes/16,"counts":counts,"formal_samples":0})
        );
        assert_eq!(coins.bytes, 16 * 28);
        if cfg!(feature = "op-counts") {
            assert_eq!(counts.final_exponentiations, 1);
        }
        let mut coins = Coins::new();
        crate::ops::reset();
        assert_eq!(
            context.judge_received(&records[0], 0, &records[2], 0, Mode::Randomized, &mut coins),
            Some((spend::Responsibility::DoubleUse, child.holder.parent[3]))
        );
        let counts = crate::ops::stop();
        println!(
            "R033_STEP_BATCH {}",
            serde_json::json!({"step":"Judge","records":2,"coefficient_bytes_observed":coins.bytes,"coefficients_observed":coins.bytes/16,"counts":counts,"formal_samples":0})
        );
        assert_eq!(coins.bytes, 16 * 28);
        if cfg!(feature = "op-counts") {
            assert_eq!(counts.final_exponentiations, 1);
        }
        let mut coins = Coins::new();
        assert!(!spend::valid_many_received_installed(
            &context.pp,
            &context.ip,
            &[records.remove(2), records.remove(0)],
            Mode::Randomized,
            &mut coins
        ));
        assert_eq!(
            coins.bytes, 0,
            "ordinary payment must reject duplicate serials before coins"
        );
    }

    #[test]
    fn metadata_single_validated_record_separates_install_verify_and_incremental_read() {
        for bit in 0..2 {
            let (mut rng, context, mut wallet, secret) = fixture_with_bit(bit);
            let child = context
                .self_derive(&mut wallet, b"metadata-read-fixture", &[0], &mut rng)
                .unwrap();
            let id = child.id;
            let mut children = vec![child];
            let policy = Policy {
                period: 1,
                atoms: vec![spend::Atom::Equal(0, S::ONE)],
            };
            let token = context
                .spend_chunks(
                    &mut children,
                    vec![(id, vec![0])],
                    &policy,
                    b"metadata-context",
                    b"metadata-request",
                    &mut rng,
                )
                .unwrap()
                .remove(0);
            crate::ops::reset();
            let reader = context.metadata_reader(secret.metadata_secrets).unwrap();
            let installation = crate::ops::stop();
            let record = context
                .verify_metadata_record(&token, Mode::Specification, &mut rng)
                .unwrap();
            crate::ops::reset();
            assert_eq!(reader.read_validated(&record), Some(bit));
            let incremental = crate::ops::stop();
            crate::ops::reset();
            assert_eq!(
                context.read_bit(
                    &token,
                    &secret.metadata_secrets,
                    Mode::Specification,
                    &mut rng
                ),
                Some(bit)
            );
            let native_full = crate::ops::stop();
            let mut bad = token.clone();
            bad.proof.z[0] += S::ONE;
            assert!(context
                .verify_metadata_record(&bad, Mode::Specification, &mut rng)
                .is_none());
            assert!(context.metadata_reader([S::from(3), S::from(4)]).is_err());
            let (other, _) = protocol::keygen(context.parameters(), &mut rng).unwrap();
            let other = ProtocolContext::new(context.pp.clone(), Arc::new(other)).unwrap();
            let wrong = VerifiedMetadataRecord {
                r: record.r,
                e: record.e,
                issuer: other.issuer_public.clone(),
            };
            assert_eq!(reader.read_validated(&wrong), None);
            if cfg!(feature = "op-counts") {
                assert_eq!(installation.g1_exponentiations, 2);
                assert_eq!(incremental.g1_exponentiations, bit as u64 + 1);
                assert_eq!(incremental.final_exponentiations, 0);
                assert_eq!(native_full.final_exponentiations, 14);
            }
            println!(
                "CHECK_METADATA {}",
                serde_json::json!({"task":"alignment","scheme":"DARLT","phase":"single_verified_record_read",
            "bit":bit,"records":1,"reader_install_counts":cfg!(feature="op-counts").then_some(installation),
            "native_full_read_counts":cfg!(feature="op-counts").then_some(native_full),
            "incremental_read_counts":cfg!(feature="op-counts").then_some(incremental),"timing_enabled":false,"formal_samples":0})
            );
        }
    }

    #[test]
    fn refreshed_remote_delivery_uses_parent_independent_request_and_exact_retry() {
        let (mut rng, context, mut wallet, _) = fixture();
        let request = context
            .delegation_request(b"request a", S::from(11), &mut rng)
            .unwrap();
        let delivery = context
            .delegate(
                &mut wallet,
                &request,
                &[0, 2],
                &[true, true, false],
                &mut rng,
            )
            .unwrap();
        assert!(!delivery.replayed);
        assert_ne!(delivery.delivery.parent[1], wallet.parent[1]);
        assert!(spseq_fc::verify_request_installed(
            &context.parameter_digest,
            &context.issuer_public,
            &request
        ));
        let bytes = delivery.delivery.encode();
        assert_eq!(
            Delivery::decode(context.parameters(), &bytes)
                .unwrap()
                .encode(),
            bytes
        );
        let child = context
            .receive(&delivery, S::from(11), None, Mode::Specification, &mut rng)
            .unwrap();
        assert_eq!(child.holder.gamma, [0, 2]);
        let retry = context
            .delegate(
                &mut wallet,
                &request,
                &[0, 2],
                &[true, true, false],
                &mut rng,
            )
            .unwrap();
        assert!(retry.replayed);
        assert_eq!(retry.delivery.encode(), bytes);
        let mut invalid = request.clone();
        invalid.proof.z += S::ONE;
        assert!(context
            .delegate(&mut wallet, &invalid, &[1], &[true; 3], &mut rng)
            .is_err());
        assert_eq!(
            context.holder_state().pool_states(wallet.id()).unwrap()[1],
            state::PoolState::Unallocated
        );
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(Delivery::decode(context.parameters(), &extra).is_err());
        let mut torsion = bytes.clone();
        torsion[8..56].fill(0);
        torsion[8] = 0x80;
        assert!(Delivery::decode(context.parameters(), &torsion).is_err());
    }

    #[test]
    fn explicit_self_children_allocate_before_spending_and_keep_metadata() {
        let (mut rng, context, mut wallet, _) = fixture();
        let first = context
            .self_derive(&mut wallet, b"self first", &[0], &mut rng)
            .unwrap();
        let second = context
            .self_derive(&mut wallet, b"self second", &[1], &mut rng)
            .unwrap();
        assert_ne!(first.id, second.id);
        assert_eq!(first.holder.parent[4..6], wallet.parent[4..6]);
        assert!(first.holder.scope_openings.is_empty());
        assert!(context
            .self_derive(&mut wallet, b"overlap", &[0], &mut rng)
            .is_err());
        let signature = first.holder.signature.clone();
        let retry = context
            .self_derive(&mut wallet, b"self first", &[0], &mut rng)
            .unwrap();
        assert_eq!(retry.holder.signature.encode(), signature.encode());
        let before = context.holder_state().pool_states(wallet.id()).unwrap();
        context
            .reserve_block(&first, b"block a", &[0], &[[7; 48]])
            .unwrap();
        context
            .bind_token(&first, b"block a", b"complete token")
            .unwrap();
        assert_eq!(
            context.holder_state().pool_states(wallet.id()).unwrap(),
            before
        );
        assert!(context
            .reserve_block(&second, b"alias", &[4], &[[7; 48]])
            .is_err());
        let restored = ProtocolContext::with_state(
            context.pp.clone(),
            context.ip.clone(),
            HolderStore::decode_snapshot(&context.holder_state().encode_snapshot().unwrap())
                .unwrap(),
        )
        .unwrap();
        let replay = restored
            .self_derive(&mut wallet, b"self first", &[0], &mut rng)
            .unwrap();
        assert_eq!(replay.holder.signature.encode(), signature.encode());
        assert_eq!(
            restored
                .reserve_block(&replay, b"block a", &[0], &[[7; 48]])
                .unwrap()
                .token
                .as_deref(),
            Some(&b"complete token"[..])
        );
    }

    #[test]
    fn issuer_ledger_preserves_one_exact_response_and_rejects_second_request() {
        let (mut rng, context, _, secret) = fixture();
        let (request, _) = protocol::prepare_request(
            context.parameters(),
            context.issuer(),
            S::from(19),
            &[S::ONE; 3],
            &[S::ONE; 2],
            &mut rng,
        )
        .unwrap();
        let mut ledger = IssuerLedger::default();
        assert!(ledger
            .respond(
                context.parameters(),
                context.issuer(),
                &secret,
                &request,
                0,
                false,
                &mut rng
            )
            .is_err());
        let (first, replayed) = ledger
            .respond(
                context.parameters(),
                context.issuer(),
                &secret,
                &request,
                0,
                true,
                &mut rng,
            )
            .unwrap();
        assert!(!replayed);
        let (second, replayed) = ledger
            .respond(
                context.parameters(),
                context.issuer(),
                &secret,
                &request,
                1,
                true,
                &mut rng,
            )
            .unwrap();
        assert!(replayed);
        assert_eq!(first.encode(), second.encode());
        let (other, _) = protocol::prepare_request(
            context.parameters(),
            context.issuer(),
            S::from(19),
            &[S::ONE; 3],
            &[S::ONE; 2],
            &mut rng,
        )
        .unwrap();
        assert!(ledger
            .respond(
                context.parameters(),
                context.issuer(),
                &secret,
                &other,
                0,
                true,
                &mut rng
            )
            .is_err());
    }

    #[test]
    fn bad_delivery_advice_is_rejected_before_random_weights_are_sampled() {
        let (mut rng, context, mut wallet, _) = fixture();
        let request = context
            .delegation_request(b"frozen advice", S::from(11), &mut rng)
            .unwrap();
        let delivery = context
            .delegate(&mut wallet, &request, &[0], &[true; 3], &mut rng)
            .unwrap();
        for variant in 0..3 {
            let mut invalid = delivery.clone();
            match variant {
                0 => invalid.delivery.pools[0].seeds[0] = S::ZERO,
                1 => invalid.delivery.pools[0].pool = 1,
                _ => invalid.delivery.yhat = G2::identity(),
            }
            let mut coins = StdRng::seed_from_u64(0x210055);
            let mut expected = coins.clone();
            assert!(context
                .receive(&invalid, S::from(11), None, Mode::Randomized, &mut coins)
                .is_err());
            assert_eq!(coins.next_u64(), expected.next_u64());
        }
    }

    #[test]
    fn self_children_form_separate_tokens_and_retries_replay_exact_wire() {
        let (mut rng, context, mut wallet, _) = fixture();
        let a = context
            .self_derive(&mut wallet, b"self a", &[0], &mut rng)
            .unwrap();
        let b = context
            .self_derive(&mut wallet, b"self b", &[1], &mut rng)
            .unwrap();
        let ids = [a.id, b.id];
        let mut children = [a, b];
        let policy = Policy {
            period: 1,
            atoms: vec![spend::Atom::Equal(0, S::ONE)],
        };
        let requests = vec![(ids[0], vec![0]), (ids[1], vec![4])];
        let tokens = context
            .spend_chunks(
                &mut children,
                requests.clone(),
                &policy,
                b"tool context",
                b"tool request",
                &mut rng,
            )
            .unwrap();
        assert_eq!(tokens.len(), 2);
        let verifier = VerifierStore::new();
        for token in &tokens {
            assert!(context.valid(token, Mode::Specification, &mut rng));
            let recorded = context
                .verify_and_record(
                    &token.wire_encode(),
                    Mode::Randomized,
                    &mut rng,
                    &verifier,
                    b"tool result",
                )
                .unwrap();
            assert!(!recorded.replayed);
            assert_eq!(recorded.newly_registered, 1);
        }
        let repeated = context
            .spend_chunks(
                &mut children,
                requests,
                &policy,
                b"tool context",
                b"tool request",
                &mut rng,
            )
            .unwrap();
        assert_eq!(
            repeated.iter().map(Token::wire_encode).collect::<Vec<_>>(),
            tokens.iter().map(Token::wire_encode).collect::<Vec<_>>()
        );
        let replay = context
            .verify_and_record(
                &repeated[0].wire_encode(),
                Mode::Randomized,
                &mut rng,
                &verifier,
                b"new result",
            )
            .unwrap();
        assert!(replay.replayed);
        assert_eq!(replay.response, b"tool result");
        assert_eq!(verifier.counts().unwrap(), (2, 2));
    }

    #[test]
    fn installation_rejects_changed_extra_basis_and_derived_cache() {
        let mut rng = StdRng::seed_from_u64(0x210066);
        let mut pp =
            PublicParameters::setup(16, 8, 8, 3, 2, b"static installation", &mut rng).unwrap();
        let (ip, _) = protocol::keygen(&pp, &mut rng).unwrap();
        pp.srs.lagrange[3] += pp.ghat;
        assert!(check_parameters(&pp, &ip).is_err());
        pp.srs.lagrange[3] -= pp.ghat;
        pp.query_bases.get_mut(&8).unwrap().0[0] += pp.ghat;
        pp.id = Sha256::digest(pp.encode()).into();
        assert!(check_parameters(&pp, &ip).is_err());
    }

    #[test]
    fn recipient_request_uses_the_digest_accepted_at_installation() {
        let (mut rng, context, _, _) = fixture();
        assert_eq!(context.parameter_digest, context.parameters().id);
        assert_eq!(&*context.issuer_public, context.issuer().encode());
        let request = context
            .delegation_request(b"installed digest", S::from(11), &mut rng)
            .unwrap();
        assert!(spseq_fc::verify_request_installed(
            &context.parameter_digest,
            &context.issuer_public,
            &request,
        ));
        let mut digest = context.parameter_digest;
        digest[0] ^= 1;
        assert!(!spseq_fc::verify_request_installed(
            &digest,
            &context.issuer_public,
            &request,
        ));
        let mut pp =
            PublicParameters::setup(16, 4, 8, 3, 2, b"bad install digest", &mut rng).unwrap();
        let (ip, _) = protocol::keygen(&pp, &mut rng).unwrap();
        pp.id[0] ^= 1;
        assert!(ProtocolContext::new(Arc::new(pp), Arc::new(ip)).is_err());
    }

    #[cfg(feature = "op-counts")]
    #[test]
    fn hot_query_basis_uses_installed_cache_without_group_operations() {
        let (_, context, _, _) = fixture();
        crate::ops::reset();
        for k in [1, 2, 4, 8] {
            assert_eq!(context.parameters().query_basis(k).unwrap().0.len(), k);
        }
        assert_eq!(crate::ops::stop(), crate::ops::Counts::default());
    }
}
