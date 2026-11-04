//! BLS12-381 operations with call-level counters (no speculative cost model).
use blstrs::{Bls12, Compress, G1Affine, G2Affine, G2Prepared};
pub use blstrs::{G1Projective as G1, G2Projective as G2, Gt as GT, Scalar as S};
use ff::Field;
use group::{Curve, Group};
use pairing::{MillerLoopResult, MultiMillerLoop};
use rand::RngCore;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::cell::RefCell;
#[derive(Default, Clone, Debug, Serialize)]
pub struct Counts {
    pub e1: u64,
    pub e2: u64,
    pub et: u64,
    pub p: u64,
    pub mp_calls: u64,
    pub mp_terms: u64,
    pub h1: u64,
    pub mul1: u64,
    pub mul2: u64,
    pub mult: u64,
    pub msm_sizes: Vec<usize>,
    pub msm2_sizes: Vec<usize>,
}
thread_local! {static COUNTS:RefCell<Option<Counts>>=const{RefCell::new(None)};}
fn count(f: impl FnOnce(&mut Counts)) {
    COUNTS.with(|c| {
        if let Some(ref mut v) = *c.borrow_mut() {
            f(v)
        }
    })
}
pub fn start_counts() {
    COUNTS.with(|c| *c.borrow_mut() = Some(Counts::default()))
}
pub fn stop_counts() -> Counts {
    COUNTS.with(|c| c.borrow_mut().take().unwrap_or_default())
}
/// Read the active scope without resetting or stopping it.
pub fn snapshot_counts() -> Option<Counts> {
    COUNTS.with(|c| c.borrow().clone())
}
pub fn counts_active() -> bool {
    COUNTS.with(|c| c.borrow().is_some())
}
/// Profile-2 records its actual merged nontrivial MSM sizes without changing
/// the underlying native arithmetic or operation counts.
pub fn record_msm_size(n: usize) {
    count(|c| c.msm_sizes.push(n));
}
pub fn g1_mul(a: G1, b: S) -> G1 {
    count(|c| c.e1 += 1);
    a * b
}
pub fn g2_mul(a: G2, b: S) -> G2 {
    count(|c| c.e2 += 1);
    a * b
}
pub fn gt_mul(a: GT, b: S) -> GT {
    count(|c| c.et += 1);
    a * b
}
pub fn g1_add(a: G1, b: G1) -> G1 {
    count(|c| c.mul1 += 1);
    a + b
}
pub fn g2_add(a: G2, b: G2) -> G2 {
    count(|c| c.mul2 += 1);
    a + b
}
pub fn gt_add(a: GT, b: GT) -> GT {
    count(|c| c.mult += 1);
    a + b
}
pub fn pair(a: G1, b: G2) -> GT {
    count(|c| c.p += 1);
    blstrs::pairing(&a.to_affine(), &b.to_affine())
}
pub fn multi_pair(terms: &[(G1, G2)]) -> GT {
    count(|c| {
        c.mp_calls += 1;
        c.mp_terms += terms.len() as u64
    });
    let aa: Vec<G1Affine> = terms.iter().map(|t| t.0.to_affine()).collect();
    let bb: Vec<G2Prepared> = terms
        .iter()
        .map(|t| G2Prepared::from(t.1.to_affine()))
        .collect();
    let refs: Vec<_> = aa.iter().zip(bb.iter()).collect();
    Bls12::multi_miller_loop(&refs).final_exponentiation()
}
/// Execute one real blstrs/BLST multi-exponentiation, without counting its
/// internal work again as individual scalar multiplications.
pub fn sum1(terms: &[(G1, S)]) -> G1 {
    if terms.is_empty() {
        return G1::identity();
    }
    count(|c| c.msm_sizes.push(terms.len()));
    let (points, scalars): (Vec<_>, Vec<_>) = terms.iter().copied().unzip();
    G1::multi_exp(&points, &scalars)
}
/// Execute the corresponding real G2 backend MSM.
pub fn sum2(terms: &[(G2, S)]) -> G2 {
    if terms.is_empty() {
        return G2::identity();
    }
    count(|c| c.msm2_sizes.push(terms.len()));
    let (points, scalars): (Vec<_>, Vec<_>) = terms.iter().copied().unzip();
    G2::multi_exp(&points, &scalars)
}
pub fn random_scalar(rng: &mut impl RngCore) -> S {
    S::random(rng)
}
pub fn random_nonzero(rng: &mut impl RngCore) -> S {
    loop {
        let x = S::random(&mut *rng);
        if x != S::ZERO {
            return x;
        }
    }
}
/// Independent verifier coefficient in {1,...,2^128-1}. Callers provide a
/// cryptographic RNG. Sixteen uniform bytes inject into Fr without reduction,
/// since the complete 128-bit range is strictly below the BLS12-381 order.
/// This sampler is only for batch-verification weights; native proof/FS,
/// signature and nonce sampling continues to use its original distribution.
pub fn random_batch_weight128(rng: &mut impl RngCore) -> S {
    loop {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes[..16]);
        if bytes[..16].iter().any(|b| *b != 0) {
            return Option::<S>::from(S::from_bytes_le(&bytes))
                .expect("128-bit integer below Fr order");
        }
    }
}

pub fn inv(x: S) -> S {
    Option::<S>::from(x.invert()).expect("nonzero scalar required")
}
pub fn hash_g1(tag: &[u8], input: &[u8]) -> G1 {
    count(|c| c.h1 += 1);
    let mut dst = b"\x45\x56\x41\x5f\x44\x41\x52\x4c\x54\x5f\x56\x31\x5f".to_vec();
    dst.extend(tag);
    dst.extend(b"_BLS12381G1_XMD:SHA-256_SSWU_RO_");
    G1::hash_to_curve(input, &dst, &[])
}
/// Rejection sampling gives a canonical, nonzero SHA-256 challenge in Fr.
pub fn hash_scalar(tag: &[u8], input: &[u8]) -> S {
    ScalarHashPrefix::new(tag, input.len(), input).finish(&[])
}

/// A SHA-256 state after an exact prefix of the existing FS byte transcript.
/// Cloning the state does not replace the transcript by a digest.
#[derive(Clone)]
pub struct ScalarHashPrefix {
    state: Sha256,
    remaining: usize,
}
/// Immutable state after the original FS domain and tag. The input length
/// remains in its original position; callers cannot preabsorb an unknown length.
#[derive(Clone)]
pub struct ScalarHashDomain {
    state: Sha256,
}
impl ScalarHashDomain {
    pub fn new(tag: &[u8]) -> Self {
        let mut state = Sha256::new();
        state.update(b"\x45\x56\x41\x5f\x46\x53\x5f\x56\x31");
        state.update((tag.len() as u64).to_be_bytes());
        state.update(tag);
        Self { state }
    }
    pub fn prefix(&self, input_len: usize, prefix: &[u8]) -> ScalarHashPrefix {
        assert!(prefix.len() <= input_len);
        let mut state = self.state.clone();
        state.update((input_len as u64).to_be_bytes());
        state.update(prefix);
        ScalarHashPrefix {
            state,
            remaining: input_len - prefix.len(),
        }
    }
}
impl ScalarHashPrefix {
    pub fn new(tag: &[u8], input_len: usize, prefix: &[u8]) -> Self {
        ScalarHashDomain::new(tag).prefix(input_len, prefix)
    }
    pub fn finish(&self, suffix: &[u8]) -> S {
        assert_eq!(suffix.len(), self.remaining);
        let mut complete = self.state.clone();
        complete.update(suffix);
        for i in 0u64.. {
            let mut h = complete.clone();
            h.update(i.to_be_bytes());
            let b: [u8; 32] = h.finalize().into();
            if let Some(s) = Option::<S>::from(S::from_bytes_be(&b)) {
                if s != S::ZERO {
                    return s;
                }
            }
        }
        unreachable!()
    }
}

/// RFC 9380 expand_message_xmd SHA-256 for BLS12-381 G1 (L=64, count=2).
/// Only the state after Z_pad || message_prefix is reused. BLST still performs
/// exactly the same field reduction, SSWU/isogeny map and cofactor clearing.
#[derive(Clone)]
pub struct G1HashPrefix {
    state: Sha256,
    dst: Vec<u8>,
}
impl G1HashPrefix {
    pub fn new(tag: &[u8], prefix: &[u8]) -> Self {
        let mut dst = b"\x45\x56\x41\x5f\x44\x41\x52\x4c\x54\x5f\x56\x31\x5f".to_vec();
        dst.extend(tag);
        dst.extend(b"_BLS12381G1_XMD:SHA-256_SSWU_RO_");
        Self::with_dst(&dst, prefix)
    }
    pub fn with_dst(dst: &[u8], prefix: &[u8]) -> Self {
        let mut dst = if dst.len() > 255 {
            let mut h = Sha256::new();
            h.update(b"H2C-OVERSIZE-DST-");
            h.update(dst);
            h.finalize().to_vec()
        } else {
            dst.to_vec()
        };
        dst.push(dst.len() as u8);
        let mut state = Sha256::new();
        state.update([0u8; 64]);
        state.update(prefix);
        Self { state, dst }
    }
    pub fn finish(&self, suffix: &[u8]) -> G1 {
        count(|c| c.h1 += 1);
        let mut h = self.state.clone();
        h.update(suffix);
        h.update([0, 128, 0]); // I2OSP(128,2) || I2OSP(0,1)
        h.update(&self.dst);
        let b0: [u8; 32] = h.finalize().into();
        let mut previous = [0u8; 32];
        let mut uniform = [0u8; 128];
        for i in 1..=4u8 {
            let mut h = Sha256::new();
            if i == 1 {
                h.update(b0);
            } else {
                h.update(std::array::from_fn::<_, 32, _>(|j| b0[j] ^ previous[j]));
            }
            h.update([i]);
            h.update(&self.dst);
            previous = h.finalize().into();
            uniform[(i as usize - 1) * 32..i as usize * 32].copy_from_slice(&previous);
        }
        let mut u = blst::blst_fp::default();
        let mut v = blst::blst_fp::default();
        let mut out = G1::identity();
        // All pointers reference live, correctly sized buffers; map_to_g1
        // accepts the two reduced Fp inputs and writes a subgroup point.
        unsafe {
            blst::blst_fp_from_be_bytes(&mut u, uniform.as_ptr(), 64);
            blst::blst_fp_from_be_bytes(&mut v, uniform[64..].as_ptr(), 64);
            blst::blst_map_to_g1(out.as_mut(), &u, &v);
        }
        out
    }
}
pub fn digest(input: &[u8]) -> Vec<u8> {
    Sha256::digest(input).to_vec()
}
pub fn enc1(a: G1) -> Vec<u8> {
    a.to_compressed().to_vec()
}
pub fn enc2(a: G2) -> Vec<u8> {
    a.to_compressed().to_vec()
}
pub fn enct(a: GT) -> Vec<u8> {
    // The upstream torus codec cannot encode identity. Reserve a non-field
    // 288-byte string in this explicit experimental canonical profile.
    if a == GT::identity() {
        return vec![255; 288];
    }
    let mut v = vec![];
    a.write_compressed(&mut v).expect("GT compression");
    v
}
pub fn encs(a: S) -> Vec<u8> {
    a.to_bytes_be().to_vec()
}
pub fn frame(out: &mut Vec<u8>, x: &[u8]) {
    out.extend((x.len() as u64).to_be_bytes());
    out.extend(x)
}
pub fn valid1(a: G1, nonzero: bool) -> bool {
    (!nonzero || a != G1::identity()) && {
        crate::subgroup_audit::g1(&a, "curve::valid1");
        bool::from(G1Affine::from_compressed(&a.to_compressed()).is_some())
    }
}
pub fn valid2(a: G2, nonzero: bool) -> bool {
    (!nonzero || a != G2::identity()) && {
        crate::subgroup_audit::g2(&a, "curve::valid2");
        bool::from(G2Affine::from_compressed(&a.to_compressed()).is_some())
    }
}

#[cfg(test)]
mod batch_weight128_tests {
    use super::*;
    struct Bytes {
        blocks: Vec<[u8; 16]>,
        at: usize,
    }
    impl RngCore for Bytes {
        fn next_u32(&mut self) -> u32 {
            panic!("only exact 16-byte draws allowed")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("only exact 16-byte draws allowed")
        }
        fn fill_bytes(&mut self, out: &mut [u8]) {
            assert_eq!(out.len(), 16);
            out.copy_from_slice(&self.blocks[self.at]);
            self.at += 1;
        }
        fn try_fill_bytes(&mut self, out: &mut [u8]) -> Result<(), rand::Error> {
            self.fill_bytes(out);
            Ok(())
        }
    }
    #[test]
    fn batch_weight_is_uniform_range_injection_and_rejects_zero() {
        let mut one = [0u8; 16];
        one[0] = 1;
        let mut rng = Bytes {
            blocks: vec![[0; 16], one, [255; 16]],
            at: 0,
        };
        assert_eq!(random_batch_weight128(&mut rng), S::ONE);
        assert_eq!(rng.at, 2);
        let max = random_batch_weight128(&mut rng).to_bytes_le();
        assert_eq!(&max[..16], &[255; 16]);
        assert_eq!(&max[16..], &[0; 16]);
        assert_eq!(rng.at, 3);
    }
}
