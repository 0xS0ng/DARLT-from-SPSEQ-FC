//! Native LCB24 verification with the repository's one shared spent store.
use crate::{check_leftmost_binding, encoded, Bank, Payment, VerificationMode};
use ark_std::rand::{CryptoRng, RngCore};
use darlt_spseq_fc::{
    batch_runtime::{Adapter, Mode},
    common::state::request_hash,
};

/// One installed native Groth16 key; separate issuers cannot share an anchor.
/// The localization unit is a complete native Payment, not its hidden leaves.
pub struct Verifier<'a, const H: usize> {
    bank: &'a Bank<H>,
    namespace: Vec<u8>,
    random_mode: VerificationMode,
}
impl<'a, const H: usize> Verifier<'a, H> {
    pub fn new(bank: &'a Bank<H>) -> Self {
        let mut namespace = b"LCB24/native-Groth16-issuer/".to_vec();
        namespace.extend(request_hash(&encoded(&bank.verifying_key)));
        Self {
            bank,
            namespace,
            random_mode: VerificationMode::Randomized,
        }
    }
    /// Alternate fair candidate: an extra Miller term and G1 exponentiation
    /// instead of a GT exponentiation. Neither profile is selected by timing.
    pub fn with_pairing_anchor(bank: &'a Bank<H>) -> Self {
        let mut verifier = Self::new(bank);
        verifier.random_mode = VerificationMode::RandomizedPairingAnchor;
        verifier
    }
}
impl<const H: usize> Adapter for Verifier<'_, H> {
    type Item = Payment;
    fn scheme(&self) -> &'static str {
        "LCB24"
    }
    fn namespace(&self) -> &[u8] {
        &self.namespace
    }
    fn verify<R: RngCore + CryptoRng>(&self, items: &[Payment], mode: Mode, rng: &mut R) -> bool {
        // Each immutable payment retains its own k; a fallback subset never
        // inherits the original batch's total amount.
        if items
            .iter()
            .flat_map(|p| &p.blocks)
            .any(|b| check_leftmost_binding(b).is_err())
        {
            return false;
        }
        let mode = match mode {
            Mode::Specification => VerificationMode::Specification,
            Mode::Randomized => self.random_mode,
        };
        self.bank
            .cryptographic_verify_batch(items, mode, rng)
            .is_ok()
    }
    fn identifiers(&self, items: &[Payment]) -> Result<Vec<Vec<u8>>, String> {
        let mut out = vec![];
        for payment in items {
            out.extend(self.bank.expand_after_verification(payment)?.serials);
        }
        Ok(out)
    }
    fn wire_messages(&self, item: &Payment) -> Vec<Vec<u8>> {
        vec![item.encode()]
    }
}
