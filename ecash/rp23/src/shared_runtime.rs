//! The same atomic store and native-payment failure localization as the other schemes.
use crate::{api::*, backend::VerificationMode};
use darlt_spseq_fc::batch_runtime::{Adapter, Mode};
use rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha256};
fn scope(scheme: &[u8], key: &[u8]) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(scheme);
    h.update(key);
    h.finalize().to_vec()
}
fn mode(m: Mode) -> VerificationMode {
    if m == Mode::Specification {
        VerificationMode::Specification
    } else {
        VerificationMode::Randomized
    }
}
pub struct CompactVerifier<'a> {
    context: &'a Compact,
    merchant: [u8; 16],
    scope: Vec<u8>,
}
impl<'a> CompactVerifier<'a> {
    pub fn new(context: &'a Compact, merchant: [u8; 16]) -> Self {
        Self {
            context,
            merchant,
            scope: scope(b"RP23-C", &context.issuer_scope_material()),
        }
    }
}
impl Adapter for CompactVerifier<'_> {
    type Item = CheckedCompactPayment;
    fn scheme(&self) -> &'static str {
        "RP23-C"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, p: &[Self::Item], m: Mode, rng: &mut R) -> bool {
        self.context.verify_checked(p, &self.merchant, mode(m), rng)
    }
    fn identifiers(&self, p: &[Self::Item]) -> Result<Vec<Vec<u8>>> {
        self.context.deposit_serials_checked(p)
    }
    fn wire_messages(&self, p: &Self::Item) -> Vec<Vec<u8>> {
        vec![p.payinfo.0.to_vec(), p.encode()]
    }
    fn public_identifiers(&self, p: &Self::Item) -> Option<Vec<Vec<u8>>> {
        Some(
            p.native
                .ss
                .iter()
                .map(|p| p.to_compressed().to_vec())
                .collect(),
        )
    }
}
pub struct DivisibleVerifier<'a> {
    context: &'a Divisible,
    merchant: [u8; 16],
    scope: Vec<u8>,
}
impl<'a> DivisibleVerifier<'a> {
    pub fn new(context: &'a Divisible, merchant: [u8; 16]) -> Self {
        Self {
            context,
            merchant,
            scope: scope(b"RP23-D", &context.issuer_scope_material()),
        }
    }
}
impl Adapter for DivisibleVerifier<'_> {
    type Item = CheckedDivisiblePayment;
    fn scheme(&self) -> &'static str {
        "RP23-D"
    }
    fn namespace(&self) -> &[u8] {
        &self.scope
    }
    fn verify<R: RngCore + CryptoRng>(&self, p: &[Self::Item], m: Mode, rng: &mut R) -> bool {
        self.context.verify_checked(p, &self.merchant, mode(m), rng)
    }
    fn identifiers(&self, p: &[Self::Item]) -> Result<Vec<Vec<u8>>> {
        self.context.deposit_serials_checked(p)
    }
    fn wire_messages(&self, p: &Self::Item) -> Vec<Vec<u8>> {
        vec![p.payinfo.0.to_vec(), p.encode()]
    }
}
