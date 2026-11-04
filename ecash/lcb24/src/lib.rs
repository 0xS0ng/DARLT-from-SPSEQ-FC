//! Native LCB24 Groth16 circuit and complete CR-PRG redemption adapter.
pub mod blstrs_bridge;
#[allow(clippy::too_many_arguments)]
#[rustfmt::skip]
#[path = "../../../source-cache/private-billing/divtokens/src/dap/circuit.rs"]
pub mod circuit;
pub mod common_state;
#[allow(clippy::needless_range_loop, clippy::clone_on_copy)]
#[rustfmt::skip]
#[path = "../../../source-cache/private-billing/divtokens/src/schnorr/mod.rs"]
pub mod schnorr;
pub mod calibration;

use ark_bls12_381::{Bls12_381, Fr, G1Projective};
use ark_crypto_primitives::SNARK;
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ed_on_bls12_381::{constraints::EdwardsVar, EdwardsProjective as JubJub};
use ark_ff::{Field, One, PrimeField, UniformRand};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{CryptoRng, RngCore};
use arkworks_native_gadgets::{
    merkle_tree::SparseMerkleTree,
    poseidon::{sbox::PoseidonSbox, FieldHasher, Poseidon, PoseidonParameters},
};
use arkworks_r1cs_gadgets::poseidon::PoseidonGadget;
use arkworks_utils::{
    bytes_matrix_to_f, bytes_vec_to_f, poseidon_params::setup_poseidon_params, Curve,
};
use schnorr::constraints::SchnorrSignatureVerifyGadget;
use schnorr::{Parameters as SigParams, PublicKey, Schnorr, SecretKey, Signature, SignatureScheme};
use std::{
    collections::{BTreeSet, HashSet},
    sync::{Arc, Mutex},
};

type NativeCircuit<const H: usize> = circuit::SpendCircuit<
    Fr,
    JubJub,
    Schnorr<JubJub>,
    SchnorrSignatureVerifyGadget<JubJub, EdwardsVar>,
    PoseidonGadget<Fr>,
    H,
>;
type Tree<const H: usize> = SparseMerkleTree<Fr, Poseidon<Fr>, H>;
type G2Prepared = <Bls12_381 as PairingEngine>::G2Prepared;
pub type Result<T> = std::result::Result<T, String>;
fn err<E: std::fmt::Display>(e: E) -> String {
    e.to_string()
}
fn encoded<T: CanonicalSerialize>(v: &T) -> Vec<u8> {
    let mut b = vec![];
    v.serialize(&mut b)
        .expect("serialize native canonical object");
    b
}
fn msm(points: &[ark_bls12_381::G1Affine], scalars: &[Fr]) -> G1Projective {
    assert_eq!(points.len(), scalars.len());
    VariableBaseMSM::multi_scalar_mul(
        points,
        &scalars.iter().map(|s| s.into_repr()).collect::<Vec<_>>(),
    )
}
fn derive(seed: [u8; 32], bit: u8) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(&seed);
    h.update(&[bit]);
    *h.finalize().as_bytes()
}
/// Native collision-resistant PRG: H(key||0), H(key||1), exactly the author.
pub fn expand(seed: [u8; 32], denom: u8) -> Result<Vec<[u8; 32]>> {
    if denom > 20 {
        return Err("LCB subtree height exceeds supported resource bound".into());
    }
    let mut level = vec![seed];
    for _ in 0..denom {
        level = level
            .into_iter()
            .flat_map(|s| [derive(s, 0), derive(s, 1)])
            .collect();
    }
    Ok(level)
}
fn constrain<const H: usize>(key: [u8; 32], start: usize, denom: u8) -> [u8; 32] {
    let mut out = key;
    for bit in (denom as usize..H).rev() {
        out = derive(out, ((start >> bit) & 1) as u8)
    }
    out
}
fn hasher() -> Result<Poseidon<Fr>> {
    let p = setup_poseidon_params(Curve::Bls381, 3, 3).map_err(err)?;
    Ok(Poseidon {
        params: PoseidonParameters {
            mds_matrix: bytes_matrix_to_f(&p.mds),
            round_keys: bytes_vec_to_f(&p.rounds),
            full_rounds: p.full_rounds,
            partial_rounds: p.partial_rounds,
            sbox: PoseidonSbox(p.exp),
            width: p.width,
        },
    })
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerificationMode {
    Specification,
    Randomized,
    RandomizedPairingAnchor,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VerificationCounts {
    pub proofs: usize,
    pub miller_terms: usize,
    pub final_exponentiations: usize,
    pub gt_exponentiations: usize,
    pub g1_exponentiations: usize,
    pub g1_msm_sizes: Vec<usize>,
}

/// Owns only the native signature issuer secret and reusable circuit setup.
/// One setup key covers all denominations via the leftmost-leaf optimization.
pub struct Bank<const H: usize> {
    sig_params: SigParams<JubJub>,
    sig_public: PublicKey<JubJub>,
    sig_secret: SecretKey<JubJub>,
    hasher: Poseidon<Fr>,
    proving_key: ProvingKey<Bls12_381>,
    verifying_key: VerifyingKey<Bls12_381>,
    anchor: <Bls12_381 as PairingEngine>::Fqk,
}
/// Customer-owned state before the bank signs only its hiding commitment.
pub struct PendingWallet<const H: usize> {
    master: [u8; 32],
    leaves: Vec<Fr>,
    tree: Tree<H>,
    root: Fr,
    commitment: Fr,
    opening: Fr,
}
impl<const H: usize> PendingWallet<H> {
    pub fn commitment(&self) -> Fr {
        self.commitment
    }
    pub fn request_bytes(&self) -> Vec<u8> {
        encoded(&self.commitment)
    }
}
pub struct Wallet<const H: usize> {
    master: [u8; 32],
    leaves: Vec<Fr>,
    tree: std::rc::Rc<Tree<H>>,
    root: Fr,
    commitment: Fr,
    opening: Fr,
    signature: Signature<JubJub>,
    proofs: std::rc::Rc<std::collections::BTreeMap<usize, Proof<Bls12_381>>>,
    used: Vec<bool>,
}
impl<const H: usize> Wallet<H> {
    pub fn capacity(&self) -> usize {
        1usize << H
    }
    pub fn unused(&self) -> usize {
        self.used.iter().filter(|v| !**v).count()
    }
    pub fn prepared_proofs(&self) -> usize {
        self.proofs.len()
    }
    pub fn proof_cache_bytes(&self) -> usize {
        self.proofs.values().map(|p| encoded(p).len()).sum()
    }
}
#[derive(Clone)]
pub struct Block {
    pub denom: u8,
    pub seed: [u8; 32],
    pub instance: Fr,
    pub proof: Proof<Bls12_381>,
}
impl Block {
    pub fn amount(&self) -> Option<usize> {
        1usize.checked_shl(self.denom as u32)
    }
}
#[derive(Clone)]
pub struct Payment {
    pub amount: usize,
    pub blocks: Vec<Block>,
}
#[derive(Clone, Debug)]
pub struct Redemption {
    pub serials: Vec<Vec<u8>>,
    pub block_amounts: Vec<usize>,
    pub expanded_leaves: usize,
}
/// Standalone correctness state. The experiment adapter can instead pass
/// Redemption.serials to the repository's shared opaque-identifier store.
#[derive(Default, Clone)]
pub struct RedemptionState {
    used: Arc<Mutex<HashSet<Vec<u8>>>>,
}
impl RedemptionState {
    pub fn used_count(&self) -> usize {
        self.used.lock().expect("state lock").len()
    }
}

impl<const H: usize> Bank<H> {
    pub fn setup<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self> {
        if H == 0 || H > 16 {
            return Err("LCB wallet height must be 1..16".into());
        }
        let sig_params = Schnorr::<JubJub>::setup(rng).map_err(err)?;
        let (sig_public, sig_secret) = Schnorr::<JubJub>::keygen(&sig_params, rng).map_err(err)?;
        let hasher = hasher()?;
        let dummy = Self::make_wallet(&sig_params, sig_public, &sig_secret, &hasher, rng)?;
        let circuit = Self::make_circuit(&sig_params, sig_public, &hasher, &dummy, 0);
        let (proving_key, verifying_key) =
            Groth16::<Bls12_381>::circuit_specific_setup(circuit, rng).map_err(err)?;
        let anchor = Bls12_381::pairing(verifying_key.alpha_g1, verifying_key.beta_g2);
        Ok(Self {
            sig_params,
            sig_public,
            sig_secret,
            hasher,
            proving_key,
            verifying_key,
            anchor,
        })
    }
    fn make_request<R: RngCore + CryptoRng>(
        hasher: &Poseidon<Fr>,
        rng: &mut R,
    ) -> Result<PendingWallet<H>> {
        let mut master = [0; 32];
        rng.fill_bytes(&mut master);
        let leaves: Vec<_> = expand(master, H as u8)?
            .iter()
            .map(|b| Fr::from_le_bytes_mod_order(b))
            .collect();
        let tree = Tree::<H>::new_sequential(&leaves, hasher, &[0; 32]).map_err(err)?;
        let root = tree.root();
        let opening = Fr::rand(rng);
        let commitment = hasher.hash(&[root, opening]).map_err(err)?;
        Ok(PendingWallet {
            master,
            leaves,
            tree,
            root,
            commitment,
            opening,
        })
    }
    fn receive_request(
        params: &SigParams<JubJub>,
        pk: PublicKey<JubJub>,
        pending: PendingWallet<H>,
        signature: Signature<JubJub>,
    ) -> Result<Wallet<H>> {
        if !Schnorr::<JubJub>::verify(params, &pk, &pending.commitment, &signature).map_err(err)? {
            return Err("native signature acceptance failed".into());
        }
        Ok(Wallet {
            master: pending.master,
            leaves: pending.leaves,
            tree: std::rc::Rc::new(pending.tree),
            root: pending.root,
            commitment: pending.commitment,
            opening: pending.opening,
            signature,
            proofs: Default::default(),
            used: vec![false; 1usize << H],
        })
    }
    fn make_wallet<R: RngCore + CryptoRng>(
        params: &SigParams<JubJub>,
        pk: PublicKey<JubJub>,
        sk: &SecretKey<JubJub>,
        hasher: &Poseidon<Fr>,
        rng: &mut R,
    ) -> Result<Wallet<H>> {
        let pending = Self::make_request(hasher, rng)?;
        let signature =
            Schnorr::<JubJub>::sign(params, sk, &pending.commitment, rng).map_err(err)?;
        Self::receive_request(params, pk, pending, signature)
    }
    /// Customer PRG/tree/commitment preparation; the bank receives only com.
    pub fn customer_request<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> Result<PendingWallet<H>> {
        Self::make_request(&self.hasher, rng)
    }
    /// Native bank issue: sign the hiding commitment, with no tree expansion.
    pub fn issuer_response<R: RngCore + CryptoRng>(
        &self,
        commitment: Fr,
        rng: &mut R,
    ) -> Result<Signature<JubJub>> {
        Schnorr::<JubJub>::sign(&self.sig_params, &self.sig_secret, &commitment, rng).map_err(err)
    }
    /// Native customer issue_process: verify the returned Schnorr signature.
    pub fn customer_receive(
        &self,
        pending: PendingWallet<H>,
        signature: Signature<JubJub>,
    ) -> Result<Wallet<H>> {
        Self::receive_request(&self.sig_params, self.sig_public, pending, signature)
    }
    fn make_circuit(
        params: &SigParams<JubJub>,
        pk: PublicKey<JubJub>,
        hasher: &Poseidon<Fr>,
        wallet: &Wallet<H>,
        start: usize,
    ) -> NativeCircuit<H> {
        NativeCircuit::<H>::new(
            params.clone(),
            pk,
            wallet.signature.clone(),
            wallet.root,
            wallet.commitment,
            wallet.opening,
            wallet.leaves[start],
            wallet.tree.generate_membership_proof(start as u64),
            hasher.clone(),
        )
    }
    /// Convenience composition of the three native issuance roles.
    pub fn issue_wallet<R: RngCore + CryptoRng>(&self, rng: &mut R) -> Result<Wallet<H>> {
        let request = self.customer_request(rng)?;
        let response = self.issuer_response(request.commitment(), rng)?;
        self.customer_receive(request, response)
    }
    /// Build one real Groth16 proof per leaf before any online context. The
    /// published leftmost-leaf optimization reuses these proofs across all
    /// denominations: the SNARK statement is leaf membership, not its height.
    pub fn precompute_all<R: RngCore + CryptoRng>(
        &self,
        wallet: &mut Wallet<H>,
        rng: &mut R,
    ) -> Result<usize> {
        for start in 0..wallet.capacity() {
            self.precompute_leaf(wallet, start, rng)?;
        }
        Ok(wallet.prepared_proofs())
    }
    /// Selected-leaf proof preparation; callers can
    /// report progress while constructing the complete native inventory.
    pub fn precompute_leaves<R: RngCore + CryptoRng>(
        &self,
        wallet: &mut Wallet<H>,
        leaves: &[usize],
        rng: &mut R,
    ) -> Result<usize> {
        if leaves.iter().any(|i| *i >= wallet.capacity()) {
            return Err("leaf index out of bounds".into());
        }
        for &start in leaves {
            self.precompute_leaf(wallet, start, rng)?;
        }
        Ok(wallet.prepared_proofs())
    }
    /// Preparation for a publicly known workload is separately identified; it
    /// is not described as an all-amount inventory or as context-independent
    /// preparation if an application only reveals the amount online.
    pub fn precompute_amount<R: RngCore + CryptoRng>(
        &self,
        wallet: &mut Wallet<H>,
        amount: usize,
        rng: &mut R,
    ) -> Result<usize> {
        let selected = select::<H>(&wallet.used, amount)?;
        for (_, start) in selected {
            self.precompute_leaf(wallet, start, rng)?;
        }
        Ok(wallet.prepared_proofs())
    }
    fn precompute_leaf<R: RngCore + CryptoRng>(
        &self,
        wallet: &mut Wallet<H>,
        start: usize,
        rng: &mut R,
    ) -> Result<()> {
        if wallet.proofs.contains_key(&start) {
            return Ok(());
        }
        let circuit = Self::make_circuit(
            &self.sig_params,
            self.sig_public,
            &self.hasher,
            wallet,
            start,
        );
        let proof = Groth16::<Bls12_381>::prove(&self.proving_key, circuit, rng).map_err(err)?;
        std::rc::Rc::make_mut(&mut wallet.proofs).insert(start, proof);
        Ok(())
    }
    /// Native greedy binary-amount subtree selection. State is committed only
    /// after the complete request can be assembled from prepared proofs.
    pub fn spend_prepared(&self, wallet: &mut Wallet<H>, amount: usize) -> Result<Payment> {
        let selected = select::<H>(&wallet.used, amount)?;
        self.spend_prepared_blocks(wallet, &selected)
    }
    /// Explicit legal subtree selection for fragmented-inventory workloads.
    /// Every selected leaf must be available; failed selection consumes none.
    pub fn spend_prepared_blocks(
        &self,
        wallet: &mut Wallet<H>,
        selected: &[(u8, usize)],
    ) -> Result<Payment> {
        if selected.is_empty() {
            return Err("empty subtree selection".into());
        }
        let mut touched = BTreeSet::new();
        for &(denom, start) in selected {
            if denom as usize > H {
                return Err("subtree height out of bounds".into());
            }
            let size = 1usize << denom;
            if start % size != 0
                || start
                    .checked_add(size)
                    .is_none_or(|end| end > wallet.capacity())
            {
                return Err("unaligned or out-of-bounds subtree".into());
            }
            for i in start..start + size {
                if wallet.used[i] || !touched.insert(i) {
                    return Err("subtree unavailable or overlapping".into());
                }
            }
        }
        let amount = touched.len();
        let mut blocks = vec![];
        for &(denom, start) in selected {
            let proof = wallet
                .proofs
                .get(&start)
                .ok_or("leftmost-leaf proof not prepared")?
                .clone();
            blocks.push(Block {
                denom,
                seed: constrain::<H>(wallet.master, start, denom),
                instance: wallet.leaves[start],
                proof,
            });
        }
        for &(denom, start) in selected {
            for v in &mut wallet.used[start..start + (1usize << denom)] {
                *v = true
            }
        }
        Ok(Payment { amount, blocks })
    }
    /// Installed issuer verification material: canonical Groth16 VK plus
    /// Schnorr public key. Fixed parameters and the proving CRS are
    /// accounted separately, not silently included in this number.
    pub fn issuer_verification_material_bytes(&self) -> usize {
        encoded(&self.verifying_key).len() + encoded(&self.sig_public).len()
    }
    pub fn proving_key_bytes(&self) -> usize {
        encoded(&self.proving_key).len()
    }
    pub fn cryptographic_verify<R: RngCore + CryptoRng>(
        &self,
        payment: &Payment,
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<VerificationCounts> {
        shape::<H>(payment)?;
        self.verify_blocks(&payment.blocks.iter().collect::<Vec<_>>(), mode, rng)
    }
    /// Random aggregation is over native Groth16 proofs under this installed
    /// issuer key. Each payment retains its own amount/capacity constraints.
    pub fn cryptographic_verify_batch<R: RngCore + CryptoRng>(
        &self,
        payments: &[Payment],
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<VerificationCounts> {
        if payments.is_empty() {
            return Err("empty native Groth16 batch".into());
        }
        for payment in payments {
            shape::<H>(payment)?;
        }
        let blocks: Vec<_> = payments.iter().flat_map(|p| p.blocks.iter()).collect();
        self.verify_blocks(&blocks, mode, rng)
    }
    fn verify_blocks<R: RngCore + CryptoRng>(
        &self,
        blocks: &[&Block],
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<VerificationCounts> {
        for block in blocks {
            validate_proof(&block.proof)?;
        }
        let count = blocks.len();
        let inputs: Vec<_> = blocks
            .iter()
            .map(|b| msm(&self.verifying_key.gamma_abc_g1, &[Fr::one(), b.instance]))
            .collect();
        let mut stats = VerificationCounts {
            proofs: count,
            g1_msm_sizes: vec![2; count],
            ..Default::default()
        };
        if mode == VerificationMode::Specification {
            for (block, input) in blocks.iter().zip(inputs) {
                let terms = [
                    (block.proof.a.into(), block.proof.b.into()),
                    (
                        (-input).into_affine().into(),
                        self.verifying_key.gamma_g2.into(),
                    ),
                    (
                        (-block.proof.c.into_projective()).into_affine().into(),
                        self.verifying_key.delta_g2.into(),
                    ),
                ];
                let result = Bls12_381::product_of_pairings(terms.iter());
                stats.miller_terms += terms.len();
                stats.final_exponentiations += 1;
                if result != self.anchor {
                    return Err("native Groth16 equation rejected".into());
                }
            }
        } else {
            // Every proof, denominator, amount and public input is fixed and
            // subgroup-checked before independent nonzero verifier weights.
            let weights: Vec<_> = (0..count)
                .map(|_| loop {
                    let mut bytes = [0u8; 16];
                    rng.fill_bytes(&mut bytes);
                    if bytes.iter().any(|b| *b != 0) {
                        break Fr::from_le_bytes_mod_order(&bytes);
                    }
                })
                .collect();
            let mut terms: Vec<(<Bls12_381 as PairingEngine>::G1Prepared, G2Prepared)> = blocks
                .iter()
                .zip(&weights)
                .map(|(b, w)| {
                    (
                        (b.proof.a.mul(w.into_repr())).into_affine().into(),
                        b.proof.b.into(),
                    )
                })
                .collect();
            let input_sum = msm(
                &inputs.iter().map(|p| p.into_affine()).collect::<Vec<_>>(),
                &weights,
            );
            let c_sum = msm(
                &blocks.iter().map(|b| b.proof.c).collect::<Vec<_>>(),
                &weights,
            );
            terms.push((
                (-input_sum).into_affine().into(),
                self.verifying_key.gamma_g2.into(),
            ));
            terms.push((
                (-c_sum).into_affine().into(),
                self.verifying_key.delta_g2.into(),
            ));
            let weight_sum = weights.iter().copied().sum::<Fr>();
            let pairing_anchor = mode == VerificationMode::RandomizedPairingAnchor;
            let target = if pairing_anchor {
                // Algebraically identical candidate: move the installed
                // alpha-beta anchor into this pairing product. Its real G1
                // exponentiation replaces the cached-target GT exponentiation.
                terms.push((
                    (-self.verifying_key.alpha_g1.mul(weight_sum.into_repr()))
                        .into_affine()
                        .into(),
                    self.verifying_key.beta_g2.into(),
                ));
                <Bls12_381 as PairingEngine>::Fqk::one()
            } else {
                self.anchor.pow(weight_sum.into_repr())
            };
            let result = Bls12_381::product_of_pairings(terms.iter());
            stats.miller_terms = terms.len();
            stats.final_exponentiations = 1;
            stats.gt_exponentiations = usize::from(!pairing_anchor);
            stats.g1_exponentiations = count + usize::from(pairing_anchor);
            stats.g1_msm_sizes.extend([count, count]);
            if result != target {
                return Err("randomized Groth16 batch rejected".into());
            }
        }
        Ok(stats)
    }
    /// Complete CR-PRG redemption expansion, kept separate from the SNARK
    /// phase. Caller must have accepted cryptographic_verify for this immutable
    /// Payment. The convenience redeem method enforces both phases itself.
    pub fn expand_after_verification(&self, payment: &Payment) -> Result<Redemption> {
        shape::<H>(payment)?;
        let mut serials = vec![];
        let mut block_amounts = vec![];
        let mut seen = BTreeSet::new();
        for block in &payment.blocks {
            let leaves = expand(block.seed, block.denom)?;
            let amount = 1usize << block.denom;
            if leaves.len() != amount || Fr::from_le_bytes_mod_order(&leaves[0]) != block.instance {
                return Err("PRG leftmost leaf binding rejected".into());
            }
            block_amounts.push(amount);
            for leaf in leaves {
                let id = encoded(&Fr::from_le_bytes_mod_order(&leaf));
                if !seen.insert(id.clone()) {
                    return Err("duplicate PRG leaf in native redemption".into());
                }
                serials.push(id);
            }
        }
        if serials.len() != payment.amount {
            return Err("native redemption amount mismatch".into());
        }
        Ok(Redemption {
            expanded_leaves: serials.len(),
            serials,
            block_amounts,
        })
    }
    pub fn redeem<R: RngCore + CryptoRng>(
        &self,
        payment: &Payment,
        state: &RedemptionState,
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<Redemption> {
        self.cryptographic_verify(payment, mode, rng)?;
        let result = self.expand_after_verification(payment)?;
        let mut used = state.used.lock().map_err(|_| "redemption state poisoned")?;
        if result.serials.iter().any(|s| used.contains(s)) {
            return Err("native serial already redeemed".into());
        }
        used.extend(result.serials.iter().cloned());
        Ok(result)
    }
}
fn select<const H: usize>(used: &[bool], amount: usize) -> Result<Vec<(u8, usize)>> {
    if amount == 0 || amount > used.len() || used.iter().filter(|v| !**v).count() < amount {
        return Err("native amount out of bounds or unavailable".into());
    }
    let mut pending = used.to_vec();
    let mut selected = vec![];
    let mut remaining = amount;
    for denom in (0..=H as u8).rev() {
        let size = 1usize << denom;
        while remaining >= size {
            let Some(start) = (0..pending.len())
                .step_by(size)
                .find(|&s| pending[s..s + size].iter().all(|v| !*v))
            else {
                break;
            };
            for v in &mut pending[start..start + size] {
                *v = true;
            }
            selected.push((denom, start));
            remaining -= size;
        }
    }
    if remaining != 0 {
        return Err("insufficient legal unused subtrees".into());
    }
    Ok(selected)
}
/// Bind a constrained PRG key to the public leaf before any randomized verifier
/// weights. Full expansion and all serial checks remain in the redemption phase.
pub fn check_leftmost_binding(block: &Block) -> Result<()> {
    let mut leftmost = block.seed;
    for _ in 0..block.denom {
        leftmost = derive(leftmost, 0);
    }
    if Fr::from_le_bytes_mod_order(&leftmost) != block.instance {
        return Err("PRG leftmost leaf binding rejected".into());
    }
    Ok(())
}
fn shape<const H: usize>(payment: &Payment) -> Result<()> {
    if payment.amount == 0
        || payment.amount > (1usize << H)
        || payment.blocks.is_empty()
        || payment.blocks.len() > 1usize << H
    {
        return Err("invalid native redemption shape".into());
    }
    let mut total = 0usize;
    for b in &payment.blocks {
        if b.denom as usize > H {
            return Err("native subtree height out of range".into());
        }
        total = total
            .checked_add(b.amount().ok_or("native block amount overflow")?)
            .ok_or("native amount overflow")?;
    }
    if total != payment.amount {
        return Err("native block amounts do not sum to requested k".into());
    }
    Ok(())
}
fn validate_proof(p: &Proof<Bls12_381>) -> Result<()> {
    if !p.a.is_on_curve()
        || !p.a.is_in_correct_subgroup_assuming_on_curve()
        || !p.b.is_on_curve()
        || !p.b.is_in_correct_subgroup_assuming_on_curve()
        || !p.c.is_on_curve()
        || !p.c.is_in_correct_subgroup_assuming_on_curve()
    {
        return Err("invalid Groth16 proof point or subgroup".into());
    }
    Ok(())
}
impl Payment {
    /// Version + amount + count, followed by denomination, constrained seed,
    /// public input and actual canonical Groth16 proof for every native block.
    pub fn encode(&self) -> Vec<u8> {
        let mut b = vec![1];
        b.extend((self.amount as u64).to_be_bytes());
        b.extend((self.blocks.len() as u64).to_be_bytes());
        for block in &self.blocks {
            b.push(block.denom);
            b.extend(block.seed);
            b.extend(encoded(&block.instance));
            b.extend(encoded(&block.proof));
        }
        b
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < 17 || bytes[0] != 1 {
            return Err("invalid LCB wire header".into());
        }
        let amount =
            usize::try_from(u64::from_be_bytes(bytes[1..9].try_into().unwrap())).map_err(err)?;
        let count =
            usize::try_from(u64::from_be_bytes(bytes[9..17].try_into().unwrap())).map_err(err)?;
        if count == 0
            || count > 65536
            || count.checked_mul(257).and_then(|n| n.checked_add(17)) != Some(bytes.len())
        {
            return Err("invalid LCB wire length".into());
        }
        let mut blocks = vec![];
        for chunk in bytes[17..].chunks_exact(257) {
            let instance = Fr::deserialize(&chunk[33..65]).map_err(err)?;
            let proof = Proof::<Bls12_381>::deserialize(&chunk[65..]).map_err(err)?;
            validate_proof(&proof)?;
            blocks.push(Block {
                denom: chunk[0],
                seed: chunk[1..33].try_into().unwrap(),
                instance,
                proof,
            });
        }
        let payment = Self { amount, blocks };
        if payment.encode() != bytes {
            return Err("noncanonical LCB wire".into());
        }
        Ok(payment)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::{rngs::StdRng, Error as RandError, SeedableRng};

    struct NoCoins;
    impl RngCore for NoCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("coins requested before fixed-input validation")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("coins requested before fixed-input validation")
        }
        fn fill_bytes(&mut self, _: &mut [u8]) {
            panic!("coins requested before fixed-input validation")
        }
        fn try_fill_bytes(&mut self, _: &mut [u8]) -> std::result::Result<(), RandError> {
            panic!("coins requested before fixed-input validation")
        }
    }
    impl CryptoRng for NoCoins {}

    // Independent correctness branches retain one honestly generated proof
    // inventory. This helper is not an online-wallet workload or benchmark.
    fn branch<const H: usize>(_b: &Bank<H>, w: &Wallet<H>) -> Wallet<H> {
        Wallet {
            master: w.master,
            leaves: w.leaves.clone(),
            tree: w.tree.clone(),
            root: w.root,
            commitment: w.commitment,
            opening: w.opening,
            signature: w.signature.clone(),
            proofs: w.proofs.clone(),
            used: vec![false; w.capacity()],
        }
    }
    fn inspect<const H: usize>(b: &Bank<H>, p: &Payment, rng: &mut StdRng) -> Redemption {
        let spec = b
            .cryptographic_verify(p, VerificationMode::Specification, rng)
            .unwrap();
        let batch = b
            .cryptographic_verify(p, VerificationMode::Randomized, rng)
            .unwrap();
        assert_eq!(spec.miller_terms, 3 * p.blocks.len());
        assert_eq!(spec.final_exponentiations, p.blocks.len());
        assert_eq!(batch.miller_terms, p.blocks.len() + 2);
        assert_eq!(batch.final_exponentiations, 1);
        assert_eq!(batch.gt_exponentiations, 1);
        let pairing_anchor = b
            .cryptographic_verify(p, VerificationMode::RandomizedPairingAnchor, rng)
            .unwrap();
        assert_eq!(pairing_anchor.miller_terms, p.blocks.len() + 3);
        assert_eq!(pairing_anchor.final_exponentiations, 1);
        assert_eq!(pairing_anchor.gt_exponentiations, 0);
        assert_eq!(pairing_anchor.g1_exponentiations, p.blocks.len() + 1);
        let decoded = Payment::decode(&p.encode()).unwrap();
        assert_eq!(decoded.encode(), p.encode());
        assert_eq!(p.encode().len(), 17 + 257 * p.blocks.len());
        let r = b.expand_after_verification(&decoded).unwrap();
        assert_eq!(r.expanded_leaves, p.amount);
        assert_eq!(r.block_amounts.iter().sum::<usize>(), p.amount);
        assert_eq!(r.serials.iter().collect::<BTreeSet<_>>().len(), p.amount);
        for (block, amount) in p.blocks.iter().zip(&r.block_amounts) {
            assert_eq!(*amount, 1usize << block.denom);
            assert_eq!(expand(block.seed, block.denom).unwrap().len(), *amount);
            assert!(Groth16::<Bls12_381>::verify(
                &b.verifying_key,
                &[block.instance],
                &block.proof
            )
            .unwrap());
        }
        r
    }
    #[test]
    fn full_native_inventory_amounts_and_atomic_redemption_n8() {
        let mut rng = StdRng::seed_from_u64(212_240_008);
        let bank = Bank::<3>::setup(&mut rng).unwrap();
        let request = bank.customer_request(&mut rng).unwrap();
        assert_eq!(request.request_bytes().len(), 32);
        let mut bad_response = bank
            .issuer_response(request.commitment(), &mut rng)
            .unwrap();
        bad_response.prover_response += ark_ed_on_bls12_381::Fr::one();
        assert!(bank.customer_receive(request, bad_response).is_err());
        let mut original = bank.issue_wallet(&mut rng).unwrap();
        assert_eq!(bank.precompute_all(&mut original, &mut rng).unwrap(), 8);
        assert_eq!(bank.precompute_all(&mut original, &mut rng).unwrap(), 8);
        assert!(bank.issuer_verification_material_bytes() > 0);
        assert!(bank.proving_key_bytes() > bank.issuer_verification_material_bytes());
        for k in 1..=8 {
            let mut wallet = branch(&bank, &original);
            let payment = bank.spend_prepared(&mut wallet, k).unwrap();
            assert_eq!(payment.blocks.len(), k.count_ones() as usize);
            let recovered = inspect(&bank, &payment, &mut rng);
            assert_eq!(wallet.unused(), 8 - k);
            let state = RedemptionState::default();
            let accepted = bank
                .redeem(&payment, &state, VerificationMode::Randomized, &mut rng)
                .unwrap();
            assert_eq!(accepted.serials, recovered.serials);
            assert_eq!(state.used_count(), k);
            assert!(bank
                .redeem(&payment, &state, VerificationMode::Specification, &mut rng)
                .is_err());
            assert_eq!(state.used_count(), k);
        }

        let mut wallet = branch(&bank, &original);
        let payment = bank.spend_prepared(&mut wallet, 3).unwrap();
        let empty = RedemptionState::default();
        let mut wrong_amount = payment.clone();
        wrong_amount.amount += 1;
        assert!(bank
            .cryptographic_verify(&wrong_amount, VerificationMode::Randomized, &mut NoCoins)
            .is_err());
        let mut bad_proof = payment.clone();
        bad_proof.blocks[0].proof.a = (bad_proof.blocks[0].proof.a.into_projective()
            + G1Projective::prime_subgroup_generator())
        .into_affine();
        assert!(bank
            .redeem(
                &bad_proof,
                &empty,
                VerificationMode::Specification,
                &mut rng
            )
            .is_err());
        assert_eq!(empty.used_count(), 0);
        for mode in [
            VerificationMode::Randomized,
            VerificationMode::RandomizedPairingAnchor,
        ] {
            assert!(bank
                .cryptographic_verify(&bad_proof, mode, &mut rng)
                .is_err());
        }
        let mut bad_seed = payment.clone();
        bad_seed.blocks[0].seed[0] ^= 1;
        assert!(bank
            .cryptographic_verify(&bad_seed, VerificationMode::Specification, &mut rng)
            .is_ok());
        assert!(bank
            .redeem(&bad_seed, &empty, VerificationMode::Randomized, &mut rng)
            .is_err());
        assert_eq!(empty.used_count(), 0);
        let mut duplicate = payment.clone();
        duplicate.blocks = vec![payment.blocks[1].clone(), payment.blocks[1].clone()];
        duplicate.amount = 2;
        assert!(bank
            .cryptographic_verify(&duplicate, VerificationMode::Specification, &mut rng)
            .is_ok());
        assert!(bank
            .redeem(&duplicate, &empty, VerificationMode::Randomized, &mut rng)
            .is_err());
        assert_eq!(empty.used_count(), 0);
        let first = Payment {
            amount: 2,
            blocks: vec![payment.blocks[0].clone()],
        };
        bank.redeem(&first, &empty, VerificationMode::Specification, &mut rng)
            .unwrap();
        assert_eq!(empty.used_count(), 2);
        assert!(bank
            .redeem(&payment, &empty, VerificationMode::Randomized, &mut rng)
            .is_err());
        assert_eq!(empty.used_count(), 2); // third, unused leaf was not committed

        let point = (0..100)
            .find_map(|x| {
                ark_bls12_381::G1Affine::get_point_from_x(ark_bls12_381::Fq::from(x as u64), false)
                    .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
            })
            .unwrap();
        let mut bad_group = payment.clone();
        bad_group.blocks[0].proof.a = point;
        assert!(bank
            .cryptographic_verify(&bad_group, VerificationMode::Randomized, &mut NoCoins)
            .is_err());
        assert!(bank
            .cryptographic_verify(
                &bad_group,
                VerificationMode::RandomizedPairingAnchor,
                &mut NoCoins
            )
            .is_err());
        assert!(Payment::decode(&bad_group.encode()).is_err());
        let mut truncated = payment.encode();
        truncated.pop();
        assert!(Payment::decode(&truncated).is_err());
        let mut not_prepared = bank.issue_wallet(&mut rng).unwrap();
        assert!(bank.spend_prepared(&mut not_prepared, 3).is_err());
        assert_eq!(not_prepared.unused(), 8);
        assert!(bank.spend_prepared(&mut wallet, 0).is_err());
        assert_eq!(wallet.unused(), 5);
        assert!(bank.spend_prepared(&mut wallet, 8).is_err());
        assert_eq!(wallet.unused(), 5);

        use darlt_spseq_fc::{
            batch_runtime::{self as runtime, Adapter, Mode},
            common::spent::SpentStore,
            common::state::StateError,
        };
        let adapter = common_state::Verifier::new(&bank);
        let store = SpentStore::with_preexisting_records(10000, adapter.namespace(), 32).unwrap();
        let mut wallet = branch(&bank, &original);
        let payments: Vec<_> = [1, 2, 1, 4]
            .into_iter()
            .map(|k| bank.spend_prepared(&mut wallet, k).unwrap())
            .collect();
        let mut bad_batch = payments.clone();
        for i in [1, 3] {
            bad_batch[i].blocks[0].proof.a = (bad_batch[i].blocks[0].proof.a.into_projective()
                + G1Projective::prime_subgroup_generator())
            .into_affine();
        }
        let failure = runtime::verify_and_record(
            &adapter,
            &bad_batch,
            b"bad-batch",
            b"no",
            &store,
            Mode::Randomized,
            &mut rng,
        )
        .unwrap_err();
        match failure {
            runtime::Error::CryptoRejected(d) => {
                assert_eq!(d.bad_indices, [1, 3]);
                assert_eq!(d.attempts.len(), 7);
                assert!(d
                    .attempts
                    .iter()
                    .filter(|a| a.items == 1)
                    .all(|a| a.mode == Mode::Randomized));
            }
            other => panic!("unexpected failure {other:?}"),
        }
        assert_eq!(store.counts().unwrap(), (10000, 10000));
        let pairing_adapter = common_state::Verifier::with_pairing_anchor(&bank);
        assert!(pairing_adapter.verify(&payments, Mode::Randomized, &mut rng));
        let pairing_failure = runtime::diagnose(&pairing_adapter, &bad_batch, &mut rng);
        assert_eq!(pairing_failure.bad_indices, [1, 3]);
        let mut bad_seed_batch = payments.clone();
        bad_seed_batch[2].blocks[0].seed[0] ^= 1;
        match runtime::verify_and_record(
            &adapter,
            &bad_seed_batch,
            b"bad-seed",
            b"no",
            &store,
            Mode::Randomized,
            &mut rng,
        )
        .unwrap_err()
        {
            runtime::Error::CryptoRejected(d) => assert_eq!(d.bad_indices, [2]),
            other => panic!("unexpected seed failure {other:?}"),
        }
        assert_eq!(store.counts().unwrap(), (10000, 10000));
        let accepted = runtime::verify_and_record(
            &adapter,
            &payments,
            b"valid",
            b"first-response",
            &store,
            Mode::Randomized,
            &mut rng,
        )
        .unwrap();
        assert_eq!(accepted.newly_registered, 8);
        assert!(!accepted.replayed);
        let retried = runtime::verify_and_record(
            &adapter,
            &payments,
            b"valid",
            b"new-response",
            &store,
            Mode::Specification,
            &mut rng,
        )
        .unwrap();
        assert!(retried.replayed);
        assert_eq!(retried.response, b"first-response");
        assert_eq!(store.counts().unwrap(), (10001, 10008));
        assert!(matches!(
            runtime::verify_and_record(
                &adapter,
                &payments,
                b"new-request",
                b"",
                &store,
                Mode::Randomized,
                &mut rng
            ),
            Err(runtime::Error::State(StateError::SerialUsed))
        ));
        assert!(matches!(
            runtime::verify_and_record(
                &adapter,
                &[payments[0].clone(), payments[0].clone()],
                b"repeated-leaf",
                b"",
                &store,
                Mode::Randomized,
                &mut rng
            ),
            Err(runtime::Error::State(StateError::DuplicateSerial))
        ));
        assert_eq!(store.counts().unwrap(), (10001, 10008));
    }
    #[test]
    fn sequential_native_blocks_disjoint_n16() {
        let mut rng = StdRng::seed_from_u64(212_240_016);
        let bank = Bank::<4>::setup(&mut rng).unwrap();
        let mut wallet = bank.issue_wallet(&mut rng).unwrap();
        assert_eq!(bank.precompute_all(&mut wallet, &mut rng).unwrap(), 16);
        let state = RedemptionState::default();
        let mut all = BTreeSet::new();
        let mut payments = vec![];
        for k in [3usize, 5, 8] {
            let payment = bank.spend_prepared(&mut wallet, k).unwrap();
            let r = inspect(&bank, &payment, &mut rng);
            assert!(r.serials.into_iter().all(|id| all.insert(id)));
            bank.redeem(&payment, &state, VerificationMode::Randomized, &mut rng)
                .unwrap();
            payments.push(payment);
        }
        let batched = bank
            .cryptographic_verify_batch(&payments, VerificationMode::Randomized, &mut rng)
            .unwrap();
        assert_eq!(batched.proofs, 5);
        assert_eq!(batched.miller_terms, 7);
        assert_eq!(batched.final_exponentiations, 1);
        let pairing_batch = bank
            .cryptographic_verify_batch(
                &payments,
                VerificationMode::RandomizedPairingAnchor,
                &mut rng,
            )
            .unwrap();
        assert_eq!(pairing_batch.proofs, 5);
        assert_eq!(pairing_batch.miller_terms, 8);
        assert_eq!(pairing_batch.final_exponentiations, 1);
        assert_eq!(pairing_batch.gt_exponentiations, 0);
        assert_eq!(pairing_batch.g1_exponentiations, 6);
        assert_eq!(wallet.unused(), 0);
        assert_eq!(state.used_count(), 16);
        assert_eq!(all.len(), 16);
    }
    #[test]
    fn prg_amount_depth_mapping_and_selector() {
        let master = [42; 32];
        let all = expand(master, 4).unwrap();
        for denom in 0..=4 {
            for start in (0..16).step_by(1 << denom) {
                let seed = constrain::<4>(master, start, denom);
                assert_eq!(
                    expand(seed, denom).unwrap(),
                    all[start..start + (1 << denom)]
                );
            }
        }
        let fragmented: Vec<_> = (0..16).map(|i| i % 2 == 0).collect();
        let selected = select::<4>(&fragmented, 8).unwrap();
        assert_eq!(selected.len(), 8);
        assert!(selected.iter().all(|(d, _)| *d == 0));
        for k in 1usize..=16 {
            let blocks = select::<4>(&[false; 16], k).unwrap();
            assert_eq!(blocks.iter().map(|(d, _)| 1usize << d).sum::<usize>(), k);
        }
    }
}

pub mod experiment;
