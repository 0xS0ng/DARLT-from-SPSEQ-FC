//! Native verifier adapters using the same opaque-identifier state runtime.
use crate::{
    batch_runtime::{Adapter, Mode},
    darlt::{
        context::ProtocolContext,
        spend::{ReceivedToken as ReceivedDarltToken, Token as DarltToken},
        verification,
    },
};
use baseline_core::{
    bhn26 as niat, hintoken as hin, klo26 as cpat, msb23::scheme as msb, pairing_verify,
    slw25 as slw, sma2rt as sma,
};
use rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha256};

fn scope(label: &[u8], key: &[u8]) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update((label.len() as u64).to_be_bytes());
    h.update(label);
    h.update(key);
    h.finalize().to_vec()
}
fn mode(m: Mode) -> pairing_verify::Mode {
    if m == Mode::Specification {
        pairing_verify::Mode::Specification
    } else {
        pairing_verify::Mode::Randomized
    }
}

pub struct Darlt<'a> {
    context: &'a ProtocolContext,
    scope: Vec<u8>,
    across_blocks: bool,
}
impl<'a> Darlt<'a> {
    pub fn new(context: &'a ProtocolContext) -> Self {
        let mut key = context.parameters().id.to_vec();
        key.extend(context.issuer().material());
        Self {
            context,
            scope: scope(b"DARLT/scope", &key),
            across_blocks: true,
        }
    }
    pub fn per_block(context: &'a ProtocolContext) -> Self {
        let mut out = Self::new(context);
        out.across_blocks = false;
        out
    }
}
impl Adapter for Darlt<'_> {
    type Item = DarltToken;
    fn scheme(&self) -> &'static str {
        "DARLT"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[DarltToken], m: Mode, r: &mut R) -> bool {
        if m == Mode::Randomized && !self.across_blocks {
            return !x.is_empty()
                && x.iter()
                    .all(|t| self.context.valid(t, verification::Mode::Randomized, r));
        }
        self.context.valid_many(
            x,
            if m == Mode::Specification {
                verification::Mode::Specification
            } else {
                verification::Mode::Randomized
            },
            r,
        )
    }
    fn identifiers(&self, x: &[DarltToken]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter()
            .flat_map(|t| t.serials().into_iter().map(|s| s.to_vec()))
            .collect())
    }
    fn wire_messages(&self, t: &DarltToken) -> Vec<Vec<u8>> {
        vec![t.wire_encode()]
    }
    fn public_identifiers(&self, t: &DarltToken) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

/// Received-token adapter. Its item type can only be created by the complete
/// strict decoder and does not expose mutable checked input.
pub struct ReceivedDarlt<'a>(Darlt<'a>);
impl<'a> ReceivedDarlt<'a> {
    pub fn new(context: &'a ProtocolContext) -> Self {
        Self(Darlt::new(context))
    }
    pub fn per_block(context: &'a ProtocolContext) -> Self {
        Self(Darlt::per_block(context))
    }
}
impl Adapter for ReceivedDarlt<'_> {
    type Item = ReceivedDarltToken;
    fn scheme(&self) -> &'static str {
        "DARLT"
    }
    fn namespace(&self) -> &[u8] {
        &self.0.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], m: Mode, r: &mut R) -> bool {
        let m = if m == Mode::Specification {
            verification::Mode::Specification
        } else {
            verification::Mode::Randomized
        };
        if m == verification::Mode::Randomized && !self.0.across_blocks {
            !x.is_empty() && x.iter().all(|t| self.0.context.valid_received(t, m, r))
        } else {
            self.0.context.valid_many_received(x, m, r)
        }
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter()
            .flat_map(|t| t.serials().into_iter().map(|s| s.to_vec()))
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.wire_encode()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

pub struct Sma<'a> {
    key: &'a sma::InstalledInstance,
    policy: &'a sma::Policy,
    ctx: &'a [u8],
    scope: Vec<u8>,
}
impl<'a> Sma<'a> {
    pub fn new(key: &'a sma::InstalledInstance, policy: &'a sma::Policy, ctx: &'a [u8]) -> Self {
        let bytes: Vec<_> = key
            .issuer_vk()
            .iter()
            .flat_map(|p| p.to_compressed())
            .collect();
        Self {
            key,
            policy,
            ctx,
            scope: scope(b"SMA2RT", &bytes),
        }
    }
}
impl Adapter for Sma<'_> {
    type Item = sma::Token;
    fn scheme(&self) -> &'static str {
        "SMA²RT"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], m: Mode, r: &mut R) -> bool {
        !x.is_empty()
            && if m == Mode::Specification {
                x.iter()
                    .all(|t| sma::verify_installed(self.key, t, self.ctx, self.policy))
            } else {
                sma::verify_random_batch_installed(self.key, x, self.ctx, self.policy, r)
            }
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter()
            .map(|t| t.serial.to_compressed().to_vec())
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.bytes()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

pub struct Niat<'a> {
    key: &'a niat::InstalledIssuer,
    variant: niat::RedemptionBatch,
    scope: Vec<u8>,
}
impl<'a> Niat<'a> {
    pub fn new(
        key: &'a niat::InstalledIssuer,
        variant: niat::RedemptionBatch,
    ) -> Result<Self, String> {
        if variant == niat::RedemptionBatch::OriginalAllOnes {
            return Err("reference-only all-ones is not a runtime safe batch profile".into());
        }
        Ok(Self {
            key,
            variant,
            scope: scope(b"NIAT", &key.encode()),
        })
    }
}
impl Adapter for Niat<'_> {
    type Item = niat::Token;
    fn scheme(&self) -> &'static str {
        "NIAT"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], m: Mode, r: &mut R) -> bool {
        !x.is_empty()
            && if m == Mode::Specification {
                x.iter().all(|t| niat::public_verify(self.key, t))
            } else {
                niat::verify_batch_redemption(self.key, x, self.variant, r).is_ok()
            }
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter().map(|t| niat::redemption_tag(t).to_vec()).collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.encode()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

pub struct Cpat<'a> {
    key: &'a cpat::ValidatedKey,
    policy: &'a cpat::Policy,
    metadata: &'a [u8],
    cached: Option<cpat::InstalledMetadata>,
    scope: Vec<u8>,
}
impl<'a> Cpat<'a> {
    pub fn new(key: &'a cpat::ValidatedKey, policy: &'a cpat::Policy, metadata: &'a [u8]) -> Self {
        let bytes: Vec<_> = key
            .public_key()
            .vk
            .iter()
            .flat_map(|p| p.to_compressed())
            .collect();
        Self {
            key,
            policy,
            metadata,
            cached: Some(cpat::install_metadata(key, metadata)),
            scope: scope(b"CPAT-EQS", &bytes),
        }
    }
    pub fn four_coordinate(
        key: &'a cpat::ValidatedKey,
        policy: &'a cpat::Policy,
        metadata: &'a [u8],
    ) -> Self {
        let bytes: Vec<_> = key
            .public_key()
            .vk
            .iter()
            .flat_map(|p| p.to_compressed())
            .collect();
        Self {
            key,
            policy,
            metadata,
            cached: None,
            scope: scope(b"CPAT-EQS", &bytes),
        }
    }
}
impl Adapter for Cpat<'_> {
    type Item = cpat::Token;
    fn scheme(&self) -> &'static str {
        "CPAT"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], m: Mode, r: &mut R) -> bool {
        !x.is_empty()
            && if m == Mode::Specification {
                x.iter()
                    .all(|t| cpat::verify(self.key, self.policy, self.metadata, t))
            } else {
                match &self.cached {
                    Some(cached) => cpat::verify_random_batch_metadata(cached, self.policy, x, r),
                    None => cpat::verify_random_batch(self.key, self.policy, self.metadata, x, r),
                }
            }
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter()
            .map(|t| {
                let mut id = (t.tag.len() as u64).to_be_bytes().to_vec();
                id.extend(&t.tag);
                id.extend(t.delta.to_compressed());
                id
            })
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.encode()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

pub struct Msb<'a> {
    key: &'a msb::Registered,
    scope: Vec<u8>,
}
impl<'a> Msb<'a> {
    pub fn new(key: &'a msb::Registered) -> Self {
        Self {
            key,
            scope: scope(b"MSB+23/presentation", key.id()),
        }
    }
}
impl Adapter for Msb<'_> {
    type Item = msb::FrozenShow;
    fn scheme(&self) -> &'static str {
        "MSB+23"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], m: Mode, r: &mut R) -> bool {
        msb::verify_frozen_shows(self.key, x, mode(m), r)
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter()
            .map(|t| Sha256::digest(t.replay_binding()).to_vec())
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        t.wire_messages().to_vec()
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

pub struct Slw {
    issuer: [u8; 32],
    scope: Vec<u8>,
}
impl Slw {
    pub fn new(key: &slw::PublicKey) -> Self {
        let issuer = key.issuer_id();
        Self {
            issuer,
            scope: scope(b"SLW+25/presentation", &issuer),
        }
    }
}
impl Adapter for Slw {
    type Item = slw::FrozenShow;
    fn scheme(&self) -> &'static str {
        "SLW+25"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], m: Mode, r: &mut R) -> bool {
        x.iter().all(|t| t.issuer_id() == self.issuer)
            && slw::verify_frozen_batch(x, mode(m), r).unwrap_or(false)
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter()
            .map(|t| Sha256::digest(t.application_binding_bytes()).to_vec())
            .collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        t.messages().to_vec()
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}

pub struct Hin<'a> {
    key: &'a hin::InstalledIssuer,
    variant: hin::VerificationMode,
    scope: Vec<u8>,
}
impl<'a> Hin<'a> {
    pub fn new(key: &'a hin::InstalledIssuer, variant: hin::VerificationMode) -> Self {
        Self {
            key,
            variant,
            scope: scope(b"HinToken", &key.id()),
        }
    }
}
impl Adapter for Hin<'_> {
    type Item = hin::Token;
    fn scheme(&self) -> &'static str {
        "HinToken"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, x: &[Self::Item], m: Mode, r: &mut R) -> bool {
        hin::verify_batch(
            self.key,
            x,
            if m == Mode::Specification {
                hin::VerificationMode::Specification
            } else {
                self.variant
            },
            r,
        )
    }
    fn identifiers(&self, x: &[Self::Item]) -> Result<Vec<Vec<u8>>, String> {
        Ok(x.iter().map(hin::Token::message_id).collect())
    }
    fn wire_messages(&self, t: &Self::Item) -> Vec<Vec<u8>> {
        vec![t.encode()]
    }
    fn public_identifiers(&self, t: &Self::Item) -> Option<Vec<Vec<u8>>> {
        self.identifiers(std::slice::from_ref(t)).ok()
    }
}
