//! LCB24 native Groth16 verification on the common blstrs backend.
//! The Arkworks circuit/prover exports checked IETF points and canonical Fr.
//! Proof checking and complete CR-PRG redemption remain separate operations.
use crate::{
    batch_runtime::{Adapter, Mode},
    common::crypto::{valid1, valid2},
    common::state::request_hash,
    ops,
};
use blstrs::{
    G1Affine, G1Projective as G1, G2Affine, G2Prepared, G2Projective as G2, Gt, Scalar as S,
};
use ff::Field;
use group::Group;
use rand::{CryptoRng, RngCore};
use std::collections::BTreeSet;

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
pub struct Proof {
    pub a: G1,
    pub b: G2,
    pub c: G1,
}
#[derive(Clone, Debug)]
pub struct Block {
    pub denom: u8,
    pub seed: [u8; 32],
    pub instance: S,
    pub proof: Proof,
}
#[derive(Clone, Debug)]
pub struct Payment {
    pub amount: usize,
    pub blocks: Vec<Block>,
}
/// Immutable group-validation provenance. Neither mutable raw access nor an
/// unchecked constructor is exposed; format/seed binding remain native checks.
#[derive(Clone, Debug)]
pub struct CheckedPayment(Payment);
impl std::ops::Deref for CheckedPayment {
    type Target = Payment;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RandomProfile {
    CachedGtAnchor,
    PairingAnchor,
}
/// Installed key for the native one-public-input circuit. All dynamic key
/// material is validated once; no Arkworks group operations run in Verify.
pub struct Key {
    alpha: G1,
    beta: G2,
    gamma: G2,
    delta: G2,
    inputs: [G1; 2],
    anchor: Gt,
    bytes: Vec<u8>,
}
impl Key {
    pub fn install(alpha: G1, beta: G2, gamma: G2, delta: G2, inputs: [G1; 2]) -> Result<Self> {
        if ![alpha, inputs[0], inputs[1]]
            .iter()
            .all(|p| valid1(*p, false))
            || ![beta, gamma, delta].iter().all(|p| valid2(*p, true))
        {
            return Err("LCB24 verification key point/subgroup rejected".into());
        }
        Self::from_checked(alpha, beta, gamma, delta, inputs)
    }
    /// Strict canonical coordinate transport for installing the native circuit key.
    /// Each point is checked once here; the immutable key never accepts raw
    /// unchecked group objects through this path.
    pub fn install_uncompressed(
        alpha: &[u8; 96],
        beta: &[u8; 192],
        gamma: &[u8; 192],
        delta: &[u8; 192],
        inputs: &[[u8; 96]; 2],
    ) -> Result<Self> {
        fn g1(bytes: &[u8; 96], site: &str) -> Result<G1> {
            crate::subgroup_audit::decode("G1", bytes, site);
            let p = Option::<G1>::from(G1::from_uncompressed(bytes))
                .ok_or("LCB24 key G1 encoding/subgroup rejected")?;
            if p.to_uncompressed() != *bytes {
                return Err("LCB24 noncanonical key G1".into());
            }
            Ok(p)
        }
        fn g2(bytes: &[u8; 192], site: &str) -> Result<G2> {
            crate::subgroup_audit::decode("G2", bytes, site);
            let p = Option::<G2>::from(G2::from_uncompressed(bytes))
                .ok_or("LCB24 key G2 encoding/subgroup rejected")?;
            if p.to_uncompressed() != *bytes || bool::from(p.is_identity()) {
                return Err("LCB24 key G2 canonical/identity rejected".into());
            }
            Ok(p)
        }
        let alpha = g1(alpha, "lcb24::Key::install_uncompressed:alpha")?;
        let beta = g2(beta, "lcb24::Key::install_uncompressed:beta")?;
        let gamma = g2(gamma, "lcb24::Key::install_uncompressed:gamma")?;
        let delta = g2(delta, "lcb24::Key::install_uncompressed:delta")?;
        let inputs = [
            g1(&inputs[0], "lcb24::Key::install_uncompressed:input0")?,
            g1(&inputs[1], "lcb24::Key::install_uncompressed:input1")?,
        ];
        Self::from_checked(alpha, beta, gamma, delta, inputs)
    }
    /// Only callers in this implementation can construct an installed key from
    /// points; both public entry points have completed their field checks.
    fn from_checked(alpha: G1, beta: G2, gamma: G2, delta: G2, inputs: [G1; 2]) -> Result<Self> {
        let anchor = ops::pairing(&G1Affine::from(alpha), &G2Affine::from(beta));
        let mut bytes = vec![2];
        bytes.extend(alpha.to_compressed());
        for p in [beta, gamma, delta] {
            bytes.extend(p.to_compressed());
        }
        bytes.extend(2u64.to_be_bytes());
        for p in inputs {
            bytes.extend(p.to_compressed());
        }
        Ok(Self {
            alpha,
            beta,
            gamma,
            delta,
            inputs,
            anchor,
            bytes,
        })
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Received-message boundary: finish strict decoding of every block in
    /// every payment before the native batch verifier draws its first weight.
    pub fn verify_received<const H: usize>(
        &self,
        messages: &[&[u8]],
        mode: Mode,
        profile: RandomProfile,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> Result<()> {
        let decoded = decode_received::<H>(messages)?;
        self.verify_checked::<H>(&decoded, mode, profile, rng)
    }
    pub fn verify<const H: usize>(
        &self,
        payments: &[Payment],
        mode: Mode,
        profile: RandomProfile,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> Result<()> {
        for p in payments {
            p.validate_shape::<H>()?;
            p.check_groups()?;
        }
        self.verify_math::<H>(payments, mode, profile, rng)
    }
    pub fn verify_checked<const H: usize>(
        &self,
        payments: &[CheckedPayment],
        mode: Mode,
        profile: RandomProfile,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> Result<()> {
        let raw: Vec<_> = payments.iter().map(|p| &p.0).collect();
        self.verify_math::<H>(&raw, mode, profile, rng)
    }
    fn verify_math<const H: usize>(
        &self,
        payments: &[impl std::borrow::Borrow<Payment>],
        mode: Mode,
        profile: RandomProfile,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> Result<()> {
        if payments.is_empty() {
            return Err("empty LCB24 payment batch".into());
        }
        for p in payments {
            let p = p.borrow();
            p.validate_shape::<H>()?;
            for b in &p.blocks {
                check_leftmost(b)?;
            }
        }
        let blocks: Vec<_> = payments.iter().flat_map(|p| &p.borrow().blocks).collect();
        let inputs: Vec<_> = blocks
            .iter()
            .map(|b| ops::msm1(&self.inputs, &[S::ONE, b.instance]))
            .collect();
        // One native Groth16 equation has no second residual to cancel.
        // A nonzero random power is algebraically redundant in this case;
        // use the exact native check for both safe aggregation candidates.
        if mode == Mode::Specification || blocks.len() == 1 {
            for (b, input) in blocks.iter().zip(inputs) {
                if product(
                    &[
                        (b.proof.a, b.proof.b),
                        (-input, self.gamma),
                        (-b.proof.c, self.delta),
                    ],
                    3,
                ) != self.anchor
                {
                    return Err("LCB24 native Groth16 equation rejected".into());
                }
            }
        } else {
            // All statements, amounts, seed bindings and proof points have
            // been fixed and checked before these fresh independent weights.
            let weights: Vec<_> = blocks
                .iter()
                .map(|_| baseline_core::curve::random_batch_weight128(rng))
                .collect();
            let mut terms: Vec<_> = blocks
                .iter()
                .zip(&weights)
                .map(|(b, w)| (ops::mul(b.proof.a, *w), b.proof.b))
                .collect();
            terms.push((-ops::msm1(&inputs, &weights), self.gamma));
            let cs: Vec<_> = blocks.iter().map(|b| b.proof.c).collect();
            terms.push((-ops::msm1(&cs, &weights), self.delta));
            let sum: S = weights.iter().copied().sum();
            let target = match profile {
                RandomProfile::CachedGtAnchor => ops::mul(self.anchor, sum),
                RandomProfile::PairingAnchor => {
                    terms.push((-ops::mul(self.alpha, sum), self.beta));
                    Gt::identity()
                }
            };
            let original_terms = blocks.len()
                * if profile == RandomProfile::PairingAnchor {
                    4
                } else {
                    3
                };
            if product(&terms, original_terms) != target {
                return Err("LCB24 randomized Groth16 equation rejected".into());
            }
        }
        Ok(())
    }
}
fn product(terms: &[(G1, G2)], inputs: usize) -> Gt {
    let left: Vec<_> = terms.iter().map(|(g, _)| G1Affine::from(*g)).collect();
    let right: Vec<_> = terms
        .iter()
        .map(|(_, h)| G2Prepared::from(G2Affine::from(*h)))
        .collect();
    let refs: Vec<_> = left.iter().zip(&right).collect();
    ops::final_exponentiation(&ops::multi_miller_loop(&refs, inputs))
}
pub fn derive(seed: [u8; 32], bit: u8) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(&seed);
    h.update(&[bit]);
    *h.finalize().as_bytes()
}
/// Native modulo-Fr reduction of a 256-bit little-endian PRG output.
pub fn leaf_scalar(bytes: &[u8; 32]) -> S {
    let mut reduced = blst::blst_scalar::default();
    // Both arrays live through the call; blst reduces any 32-byte integer.
    // Its boolean only says whether the reduced value is nonzero, which is
    // not a constraint on this native public input/serial.
    unsafe {
        blst::blst_scalar_from_le_bytes(&mut reduced, bytes.as_ptr(), bytes.len());
    }
    Option::<S>::from(S::from_bytes_le(&reduced.b)).expect("blst returns canonical Fr")
}
pub fn check_leftmost(block: &Block) -> Result<()> {
    if block.denom > 16 {
        return Err("LCB24 subtree height is unsupported".into());
    }
    let mut leaf = block.seed;
    for _ in 0..block.denom {
        leaf = derive(leaf, 0);
    }
    if leaf_scalar(&leaf) != block.instance {
        return Err("LCB24 seed/leftmost binding rejected".into());
    }
    Ok(())
}
impl Payment {
    fn check_groups(&self) -> Result<()> {
        for b in &self.blocks {
            if !valid1(b.proof.a, false) || !valid2(b.proof.b, false) || !valid1(b.proof.c, false) {
                return Err("LCB24 proof point/subgroup rejected".into());
            }
        }
        Ok(())
    }
    /// Safe typed-to-checked boundary, checking each native proof field once.
    pub fn checked<const H: usize>(self) -> Result<CheckedPayment> {
        self.validate_shape::<H>()?;
        self.check_groups()?;
        Ok(CheckedPayment(self))
    }
    pub fn validate_shape<const H: usize>(&self) -> Result<()> {
        if H == 0
            || H > 16
            || self.amount == 0
            || self.amount > 1usize << H
            || self.blocks.is_empty()
            || self.blocks.len() > 1usize << H
        {
            return Err("LCB24 native amount/shape rejected".into());
        }
        let mut sum = 0usize;
        for b in &self.blocks {
            if b.denom as usize > H {
                return Err("LCB24 subtree height rejected".into());
            }
            sum = sum
                .checked_add(1usize << b.denom)
                .ok_or("LCB24 amount overflow")?;
        }
        if sum != self.amount {
            return Err("LCB24 block sum differs from amount".into());
        }
        Ok(())
    }
    /// Complete native backend: every selected subtree is fully expanded,
    /// every leaf is reduced to native Fr, all complete serials are distinct.
    pub fn redeem_serials<const H: usize>(&self) -> Result<Vec<Vec<u8>>> {
        self.validate_shape::<H>()?;
        let mut ids = vec![];
        let mut seen = BTreeSet::new();
        for b in &self.blocks {
            check_leftmost(b)?;
            let mut level = vec![b.seed];
            for _ in 0..b.denom {
                level = level
                    .into_iter()
                    .flat_map(|s| [derive(s, 0), derive(s, 1)])
                    .collect();
            }
            if level.len() != 1usize << b.denom {
                return Err("LCB24 expanded amount mismatch".into());
            }
            for leaf in level {
                let id = leaf_scalar(&leaf).to_bytes_le().to_vec();
                if !seen.insert(id.clone()) {
                    return Err("LCB24 duplicate full native serial".into());
                }
                ids.push(id);
            }
        }
        if ids.len() != self.amount {
            return Err("LCB24 native redeemed sum mismatch".into());
        }
        Ok(ids)
    }
    /// IETF-encoded BLS points after the offline Arkworks-to-blstrs bridge.
    /// Version2 distinguishes this from the author's Arkworks point encoding.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = vec![2];
        out.extend((self.amount as u64).to_be_bytes());
        out.extend((self.blocks.len() as u64).to_be_bytes());
        for b in &self.blocks {
            out.push(b.denom);
            out.extend(b.seed);
            out.extend(b.instance.to_bytes_le());
            out.extend(b.proof.a.to_compressed());
            out.extend(b.proof.b.to_compressed());
            out.extend(b.proof.c.to_compressed());
        }
        out
    }
    pub fn decode<const H: usize>(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < 17 || bytes[0] != 2 {
            return Err("LCB24 blstrs wire header rejected".into());
        }
        let amount = usize::try_from(u64::from_be_bytes(bytes[1..9].try_into().unwrap()))
            .map_err(|e| e.to_string())?;
        let count = usize::try_from(u64::from_be_bytes(bytes[9..17].try_into().unwrap()))
            .map_err(|e| e.to_string())?;
        if H == 0 || H > 16 || amount == 0 || amount > (1usize << H) || count > (1usize << H) {
            return Err("LCB24 native amount/block bound rejected".into());
        }
        if count == 0
            || count > 65536
            || count.checked_mul(257).and_then(|n| n.checked_add(17)) != Some(bytes.len())
        {
            return Err("LCB24 blstrs wire length rejected".into());
        }
        let mut blocks = vec![];
        for b in bytes[17..].chunks_exact(257) {
            let instance = Option::<S>::from(S::from_bytes_le(b[33..65].try_into().unwrap()))
                .ok_or("LCB24 noncanonical field")?;
            crate::subgroup_audit::decode("G1", &b[65..113], "lcb24::Payment::decode:A");
            let a = Option::<G1>::from(G1::from_compressed(b[65..113].try_into().unwrap()))
                .ok_or("LCB24 invalid proof A")?;
            crate::subgroup_audit::decode("G2", &b[113..209], "lcb24::Payment::decode:B");
            let bp = Option::<G2>::from(G2::from_compressed(b[113..209].try_into().unwrap()))
                .ok_or("LCB24 invalid proof B")?;
            crate::subgroup_audit::decode("G1", &b[209..257], "lcb24::Payment::decode:C");
            let c = Option::<G1>::from(G1::from_compressed(b[209..257].try_into().unwrap()))
                .ok_or("LCB24 invalid proof C")?;
            blocks.push(Block {
                denom: b[0],
                seed: b[1..33].try_into().unwrap(),
                instance,
                proof: Proof { a, b: bp, c },
            });
        }
        let out = Self { amount, blocks };
        out.validate_shape::<H>()?;
        if out.encode() != bytes {
            return Err("LCB24 noncanonical payment".into());
        }
        Ok(out)
    }
}
/// All received group elements use checked canonical point decoding. This
/// parser enforces native shape/EOF while preserving the native permission for
/// identity proof points; seed/instance binding remains a native pre-weight check.
pub fn decode_received<const H: usize>(messages: &[&[u8]]) -> Result<Vec<CheckedPayment>> {
    if messages.is_empty() {
        return Err("empty received LCB24 payment batch".into());
    }
    messages
        .iter()
        .map(|m| Payment::decode::<H>(m).map(CheckedPayment))
        .collect()
}
/// The common application transaction is a complete native Payment. There is
/// no independent merchant Verify interface in this bank-redemption scheme.
pub struct Verifier<'a, const H: usize> {
    key: &'a Key,
    namespace: Vec<u8>,
    profile: RandomProfile,
}
impl<'a, const H: usize> Verifier<'a, H> {
    pub fn new(key: &'a Key, profile: RandomProfile) -> Self {
        let mut namespace = b"LCB24/blstrs-Groth16-issuer/".to_vec();
        namespace.extend(request_hash(key.bytes()));
        Self {
            key,
            namespace,
            profile,
        }
    }
}
impl<const H: usize> Adapter for Verifier<'_, H> {
    type Item = CheckedPayment;
    fn scheme(&self) -> &'static str {
        "LCB24"
    }
    fn namespace(&self) -> &[u8] {
        &self.namespace
    }
    fn verify<R: RngCore + CryptoRng>(
        &self,
        items: &[CheckedPayment],
        mode: Mode,
        rng: &mut R,
    ) -> bool {
        self.key
            .verify_checked::<H>(items, mode, self.profile, rng)
            .is_ok()
    }
    fn identifiers(&self, items: &[CheckedPayment]) -> Result<Vec<Vec<u8>>> {
        let mut out = vec![];
        for p in items {
            out.extend(p.redeem_serials::<H>()?);
        }
        Ok(out)
    }
    fn wire_messages(&self, p: &CheckedPayment) -> Vec<Vec<u8>> {
        vec![p.encode()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[derive(Default)]
    struct BatchCoins(usize);
    impl RngCore for BatchCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("batch coefficient requests16bytes")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("batch coefficient requests16bytes")
        }
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            assert_eq!(dest.len(), 16);
            self.0 += 1;
            dest.copy_from_slice(&(self.0 as u128).to_le_bytes());
        }
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> std::result::Result<(), rand::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }
    impl CryptoRng for BatchCoins {}
    #[test]
    fn cached_anchor_batches_all_groth16_residuals_with_independent_128bit_coefficients() {
        let key = Key::install(
            G1::generator(),
            G2::generator(),
            G2::generator(),
            G2::generator(),
            [G1::identity(); 2],
        )
        .unwrap();
        // An algebraically valid installed-key fixture isolates each pairing
        // residual. Actual circuit/prover correctness has separate native tests.
        let payment = Payment {
            amount: 3,
            blocks: (1..=3)
                .map(|i| {
                    let seed = [i; 32];
                    Block {
                        denom: 0,
                        seed,
                        instance: leaf_scalar(&seed),
                        proof: Proof {
                            a: G1::generator() * S::from(2),
                            b: G2::generator(),
                            c: G1::generator(),
                        },
                    }
                })
                .collect(),
        };
        for corrupted in [None, Some(0usize), Some(1), Some(2)] {
            let mut p = payment.clone();
            if let Some(i) = corrupted {
                p.blocks[i].proof.c += G1::generator();
            }
            let wire = p.encode();
            let mut coins = BatchCoins::default();
            assert_eq!(
                key.verify_received::<2>(
                    &[&wire],
                    Mode::Randomized,
                    RandomProfile::CachedGtAnchor,
                    &mut coins
                )
                .is_ok(),
                corrupted.is_none()
            );
            assert_eq!(coins.0, 3);
        }
        let mut one = payment;
        one.amount = 1;
        one.blocks.truncate(1);
        let mut coins = BatchCoins::default();
        key.verify_received::<2>(
            &[&one.encode()],
            Mode::Randomized,
            RandomProfile::CachedGtAnchor,
            &mut coins,
        )
        .unwrap();
        assert_eq!(coins.0, 0);
    }
    #[test]
    fn leaf_reduction_accepts_zero_and_reduces_full_width() {
        assert_eq!(leaf_scalar(&[0; 32]), S::ZERO);
        assert_eq!(leaf_scalar(&S::ONE.to_bytes_le()), S::ONE);
        let bytes = [255; 32];
        let mut value = S::ZERO;
        for b in bytes.iter().rev() {
            value = value * S::from(256) + S::from(*b as u64);
        }
        assert_eq!(leaf_scalar(&bytes), value);
    }
    #[test]
    fn malformed_amount_wire_and_seed_reject_before_group_work() {
        let b = Block {
            denom: 0,
            seed: [3; 32],
            instance: leaf_scalar(&[3; 32]),
            proof: Proof {
                a: G1::generator(),
                b: G2::generator(),
                c: G1::generator(),
            },
        };
        let mut p = Payment {
            amount: 1,
            blocks: vec![b],
        };
        assert_eq!(
            Payment::decode::<4>(&p.encode()).unwrap().encode(),
            p.encode()
        );
        assert_eq!(p.redeem_serials::<4>().unwrap().len(), 1);
        p.amount = 2;
        assert!(p.validate_shape::<4>().is_err());
        p.amount = 1;
        p.blocks[0].seed[0] ^= 1;
        assert!(p.redeem_serials::<4>().is_err());
        let key = Key::install(
            G1::generator(),
            G2::generator(),
            G2::generator(),
            G2::generator(),
            [G1::generator(); 2],
        )
        .unwrap();
        assert!(key
            .verify::<4>(
                &[p],
                Mode::Randomized,
                RandomProfile::CachedGtAnchor,
                &mut StdRng::seed_from_u64(214)
            )
            .is_err());
    }
}
