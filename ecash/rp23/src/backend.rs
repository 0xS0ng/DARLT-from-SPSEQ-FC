//! BLS12-381 native operations and the author artifact's canonical transcript codecs.
pub use blstrs::Scalar;
use ff::Field;
use group::{prime::PrimeCurveAffine, Curve, Group};
use pairing::MultiMillerLoop;
use sha2::{Digest, Sha256};
use std::{cell::RefCell, iter::Sum, ops::*};

#[derive(Clone, Debug, Default, serde::Serialize, PartialEq, Eq)]
pub struct Counts {
    pub g1_exp: usize,
    pub g2_exp: usize,
    pub gt_exp: usize,
    pub miller_terms: usize,
    pub final_exponentiations: usize,
    pub g1_msm_sizes: Vec<usize>,
    pub g2_msm_sizes: Vec<usize>,
    pub hash_g1: usize,
    pub hash_g2: usize,
}
thread_local! { static COUNTS: RefCell<Option<Counts>>=const{RefCell::new(None)}; }
fn increment(value: &mut usize) {
    *value += 1;
}
fn record(f: impl FnOnce(&mut Counts)) {
    COUNTS.with(|c| {
        if let Some(c) = c.borrow_mut().as_mut() {
            f(c)
        }
    })
}
/// Whether this thread currently has a native operation-count scope enabled.
pub fn counts_active() -> bool {
    COUNTS.with(|c| c.borrow().is_some())
}
pub fn start_counts() {
    COUNTS.with(|c| {
        assert!(c.borrow().is_none());
        *c.borrow_mut() = Some(Counts::default());
    });
}
pub fn stop_counts() -> Counts {
    COUNTS.with(|c| c.borrow_mut().take().expect("active native counter scope"))
}

pub trait ScalarCompat {
    fn zero() -> Self;
    fn one() -> Self;
    fn from_bytes(b: &[u8; 32]) -> subtle::CtOption<Self>
    where
        Self: Sized;
    fn from_bytes_wide(b: &[u8; 64]) -> Self;
    fn to_bytes(&self) -> [u8; 32];
}
impl ScalarCompat for Scalar {
    fn zero() -> Self {
        Self::ZERO
    }
    fn one() -> Self {
        Self::ONE
    }
    fn from_bytes(b: &[u8; 32]) -> subtle::CtOption<Self> {
        Self::from_bytes_le(b)
    }
    fn from_bytes_wide(b: &[u8; 64]) -> Self {
        let mut x = Self::ZERO;
        for b in b.iter().rev() {
            x = x * Self::from(256) + Self::from(*b as u64);
        }
        x
    }
    fn to_bytes(&self) -> [u8; 32] {
        self.to_bytes_le()
    }
}
/// Exact XMD:SHA-256 expansion and 48-byte big-endian reduction used by author HashToField.
pub fn hash_scalar(msg: &[u8], dst: &[u8]) -> Scalar {
    assert!(dst.len() < 256);
    let mut d = dst.to_vec();
    d.push(dst.len() as u8);
    let mut h = Sha256::new();
    h.update([0u8; 64]);
    h.update(msg);
    h.update([0, 48, 0]);
    h.update(&d);
    let b0 = h.finalize();
    let mut h = Sha256::new();
    h.update(b0);
    h.update([1]);
    h.update(&d);
    let b1 = h.finalize();
    let mut h = Sha256::new();
    let x: Vec<_> = b0.iter().zip(b1.iter()).map(|(a, b)| a ^ b).collect();
    h.update(x);
    h.update([2]);
    h.update(&d);
    let b2 = h.finalize();
    let bytes: Vec<_> = b1.iter().chain(b2[..16].iter()).copied().collect();
    let mut x = Scalar::ZERO;
    for b in bytes {
        x = x * Scalar::from(256) + Scalar::from(b as u64);
    }
    x
}

macro_rules! points {
    ($p:ident,$a:ident,$inner:ty,$aff:ty,$n:literal,$exp:ident,$hash:ident,$msms:ident,$audit:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $p(pub(crate) $inner);
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $a(pub(crate) $aff);
        impl $p {
            pub fn identity() -> Self {
                Self(<$inner>::identity())
            }
            pub fn generator() -> Self {
                Self(<$inner>::generator())
            }
            pub fn is_identity(&self) -> subtle::Choice {
                self.0.is_identity()
            }
            pub fn to_affine(&self) -> $a {
                $a(self.0.to_affine())
            }
            pub fn to_bytes(&self) -> [u8; $n] {
                self.0.to_compressed()
            }
            pub fn to_compressed(&self) -> [u8; $n] {
                self.0.to_compressed()
            }
            pub fn hash_to_curve(msg: &[u8], dst: &[u8], aug: &[u8]) -> Self {
                record(|c| c.$hash += 1);
                Self(<$inner>::hash_to_curve(msg, dst, aug))
            }
            pub fn msm(points: &[Self], scalars: &[Scalar]) -> Self {
                assert_eq!(points.len(), scalars.len());
                record(|c| c.$msms.push(points.len()));
                Self(<$inner>::multi_exp(
                    &points.iter().map(|p| p.0).collect::<Vec<_>>(),
                    scalars,
                ))
            }
            pub fn checked(&self) -> bool {
                let p = self.0.to_affine();
                bool::from(p.is_on_curve()) && {
                    #[cfg(feature = "subgroup-audit")]
                    darlt_spseq_fc::subgroup_audit::$audit(
                        &self.0,
                        concat!("rp23::", stringify!($p), "::checked"),
                    );
                    bool::from(p.is_torsion_free())
                }
            }
        }
        impl $a {
            pub fn identity() -> Self {
                Self(<$aff>::identity())
            }
            pub fn generator() -> Self {
                Self(<$aff>::generator())
            }
            pub fn is_identity(&self) -> subtle::Choice {
                self.0.is_identity()
            }
            pub fn to_bytes(&self) -> [u8; $n] {
                self.to_compressed()
            }
            pub fn to_compressed(&self) -> [u8; $n] {
                self.0.to_compressed()
            }
            pub fn from_compressed(b: &[u8; $n]) -> subtle::CtOption<Self> {
                <$aff>::from_compressed(b).map(Self)
            }
            pub fn checked(&self) -> bool {
                bool::from(self.0.is_on_curve()) && {
                    #[cfg(feature = "subgroup-audit")]
                    darlt_spseq_fc::subgroup_audit::$audit(
                        &<$inner>::from(self.0),
                        concat!("rp23::", stringify!($a), "::checked"),
                    );
                    bool::from(self.0.is_torsion_free())
                }
            }
        }
        impl std::hash::Hash for $p {
            fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
                self.to_compressed().hash(h)
            }
        }
        impl Add<$p> for &$a {
            type Output = $p;
            fn add(self, r: $p) -> $p {
                $p(self.0 + r.0)
            }
        }
        impl From<$a> for $p {
            fn from(p: $a) -> Self {
                Self(p.0.into())
            }
        }
        impl Neg for $p {
            type Output = Self;
            fn neg(self) -> Self {
                Self(-self.0)
            }
        }
        impl Neg for &$p {
            type Output = $p;
            fn neg(self) -> $p {
                $p(-self.0)
            }
        }
        impl Neg for $a {
            type Output = Self;
            fn neg(self) -> Self {
                Self(-self.0)
            }
        }
        impl Neg for &$a {
            type Output = $a;
            fn neg(self) -> $a {
                $a(-self.0)
            }
        }
        impl Add for $p {
            type Output = Self;
            fn add(self, r: Self) -> Self {
                Self(self.0 + r.0)
            }
        }
        impl Add<&$p> for $p {
            type Output = Self;
            fn add(self, r: &Self) -> Self {
                Self(self.0 + r.0)
            }
        }
        impl Add<$p> for &$p {
            type Output = $p;
            fn add(self, r: $p) -> $p {
                $p(self.0 + r.0)
            }
        }
        impl Add<&$p> for &$p {
            type Output = $p;
            fn add(self, r: &$p) -> $p {
                $p(self.0 + r.0)
            }
        }
        impl Sub for $p {
            type Output = Self;
            fn sub(self, r: Self) -> Self {
                Self(self.0 - r.0)
            }
        }
        impl Sub<&$p> for $p {
            type Output = Self;
            fn sub(self, r: &Self) -> Self {
                Self(self.0 - r.0)
            }
        }
        impl Sub<$p> for &$p {
            type Output = $p;
            fn sub(self, r: $p) -> $p {
                $p(self.0 - r.0)
            }
        }
        impl Sub<&$p> for &$p {
            type Output = $p;
            fn sub(self, r: &$p) -> $p {
                $p(self.0 - r.0)
            }
        }
        impl AddAssign for $p {
            fn add_assign(&mut self, r: Self) {
                self.0 += r.0
            }
        }
        impl AddAssign<&$p> for $p {
            fn add_assign(&mut self, r: &Self) {
                self.0 += r.0
            }
        }
        impl SubAssign for $p {
            fn sub_assign(&mut self, r: Self) {
                self.0 -= r.0
            }
        }
        impl Mul<Scalar> for $p {
            type Output = Self;
            fn mul(self, r: Scalar) -> Self {
                record(|c| increment(&mut c.$exp));
                Self(self.0 * r)
            }
        }
        impl Mul<&Scalar> for $p {
            type Output = Self;
            fn mul(self, r: &Scalar) -> Self {
                self * *r
            }
        }
        impl Mul<Scalar> for &$p {
            type Output = $p;
            fn mul(self, r: Scalar) -> $p {
                *self * r
            }
        }
        impl Mul<&Scalar> for &$p {
            type Output = $p;
            fn mul(self, r: &Scalar) -> $p {
                *self * *r
            }
        }
        impl Mul<Scalar> for $a {
            type Output = $p;
            fn mul(self, r: Scalar) -> $p {
                record(|c| increment(&mut c.$exp));
                $p(self.0 * r)
            }
        }
        impl Mul<&Scalar> for $a {
            type Output = $p;
            fn mul(self, r: &Scalar) -> $p {
                self * *r
            }
        }
        impl Mul<Scalar> for &$a {
            type Output = $p;
            fn mul(self, r: Scalar) -> $p {
                *self * r
            }
        }
        impl Mul<&Scalar> for &$a {
            type Output = $p;
            fn mul(self, r: &Scalar) -> $p {
                *self * *r
            }
        }
        impl Sum for $p {
            fn sum<I: Iterator<Item = Self>>(i: I) -> Self {
                i.fold(Self::identity(), |a, b| a + b)
            }
        }
        impl<'a> Sum<&'a Self> for $p {
            fn sum<I: Iterator<Item = &'a Self>>(i: I) -> Self {
                i.copied().sum()
            }
        }
    };
}
points!(
    G1Projective,
    G1Affine,
    blstrs::G1Projective,
    blstrs::G1Affine,
    48,
    g1_exp,
    hash_g1,
    g1_msm_sizes,
    g1
);
points!(
    G2Projective,
    G2Affine,
    blstrs::G2Projective,
    blstrs::G2Affine,
    96,
    g2_exp,
    hash_g2,
    g2_msm_sizes,
    g2
);
#[derive(Debug, Clone)]
pub struct G2Prepared(blstrs::G2Prepared, G2Affine);
impl From<G2Affine> for G2Prepared {
    fn from(p: G2Affine) -> Self {
        Self(blstrs::G2Prepared::from(p.0), p)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gt(pub(crate) blstrs::Gt);
impl Gt {
    pub fn identity() -> Self {
        Self(blstrs::Gt::identity())
    }
    pub fn is_identity(&self) -> subtle::Choice {
        self.0.is_identity()
    }
}
impl Neg for Gt {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}
impl Neg for &Gt {
    type Output = Gt;
    fn neg(self) -> Gt {
        Gt(-self.0)
    }
}
impl Add for Gt {
    type Output = Self;
    fn add(self, r: Self) -> Self {
        Self(self.0 + r.0)
    }
}
impl Add<&Gt> for Gt {
    type Output = Self;
    fn add(self, r: &Self) -> Self {
        self + *r
    }
}
impl Sub for Gt {
    type Output = Self;
    fn sub(self, r: Self) -> Self {
        Self(self.0 - r.0)
    }
}
impl Sub<&Gt> for Gt {
    type Output = Self;
    fn sub(self, r: &Self) -> Self {
        self - *r
    }
}
impl AddAssign for Gt {
    fn add_assign(&mut self, r: Self) {
        self.0 += r.0
    }
}
impl Mul<Scalar> for Gt {
    type Output = Self;
    fn mul(self, r: Scalar) -> Self {
        record(|c| increment(&mut c.gt_exp));
        Self(self.0 * r)
    }
}
impl Mul<&Scalar> for Gt {
    type Output = Self;
    fn mul(self, r: &Scalar) -> Self {
        self * *r
    }
}
impl std::hash::Hash for Gt {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.to_compressed().hash(h)
    }
}
pub fn pairing(a: &G1Affine, b: &G2Affine) -> Gt {
    record(|c| {
        c.miller_terms += 1;
        c.final_exponentiations += 1
    });
    Gt(blstrs::pairing(&a.0, &b.0))
}
pub struct Miller(blstrs::MillerLoopResult);
pub fn multi_miller_loop(t: &[(&G1Affine, &G2Prepared)]) -> Miller {
    record(|c| c.miller_terms += t.len());
    Miller(blstrs::Bls12::multi_miller_loop(
        &t.iter().map(|(a, b)| (&a.0, &b.0)).collect::<Vec<_>>(),
    ))
}
impl Miller {
    pub fn final_exponentiation(self) -> Gt {
        use pairing::MillerLoopResult;
        record(|c| c.final_exponentiations += 1);
        Gt(self.0.final_exponentiation())
    }
}
/// Author GT codec is c1 plus a sign flag, not blstrs's torus encoding.
pub trait GtCompat {
    fn to_compressed(&self) -> [u8; 288];
}
impl GtCompat for Gt {
    fn to_compressed(&self) -> [u8; 288] {
        // Pinned blstrs0.7.1 Gt and Fp12 are repr(transparent) over blst_fp12.
        assert_eq!(
            std::mem::size_of::<blstrs::Gt>(),
            std::mem::size_of::<blst::blst_fp12>()
        );
        let raw: blst::blst_fp12 = unsafe { std::mem::transmute_copy(&self.0) };
        let mut out = [0; 288];
        for i in 0..3 {
            for j in 0..2 {
                unsafe {
                    blst::blst_bendian_from_fp(
                        out[(i * 2 + j) * 48..].as_mut_ptr(),
                        &raw.fp6[1].fp2[i].fp[j],
                    );
                }
            }
        }
        // Sign uses c0's lexicographic comparison with its negation in the author codec.
        let mut c0 = [0u8; 288];
        let mut minus = [0u8; 288];
        for i in 0..3 {
            for j in 0..2 {
                let pos = (i * 2 + j) * 48;
                unsafe {
                    blst::blst_bendian_from_fp(c0[pos..].as_mut_ptr(), &raw.fp6[0].fp2[i].fp[j]);
                    let mut n = raw.fp6[0].fp2[i].fp[j];
                    blst::blst_fp_cneg(&mut n, &raw.fp6[0].fp2[i].fp[j], true);
                    blst::blst_bendian_from_fp(minus[pos..].as_mut_ptr(), &n);
                }
            }
        }
        let largest = (0..6)
            .rev()
            .find_map(|i| {
                let a = &c0[i * 48..(i + 1) * 48];
                let b = &minus[i * 48..(i + 1) * 48];
                (a != b).then_some(a > b)
            })
            .unwrap_or(false);
        out[0] |= 0x80;
        if largest {
            out[0] |= 0x40;
        }
        out
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerificationMode {
    Specification,
    Randomized,
}
/// Uniform independent nonzero 128-bit batch coefficient. Protocol/FS random
/// scalars use their original full-field sampling and do not call this helper.
fn random_batch_weight128(rng: &mut (impl rand::RngCore + rand::CryptoRng)) -> Scalar {
    loop {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes[..16]);
        if bytes[..16].iter().any(|b| *b != 0) {
            // Every 128-bit integer is strictly below the BLS12-381 Fr modulus.
            return Option::<Scalar>::from(Scalar::from_bytes_le(&bytes)).unwrap();
        }
    }
}
type PairingEquation = Vec<(G1Affine, G2Affine)>;
thread_local! {static EQUATIONS:RefCell<Option<Vec<PairingEquation>>>=const{RefCell::new(None)};}
struct EquationScope;
impl Drop for EquationScope {
    fn drop(&mut self) {
        EQUATIONS.with(|c| {
            c.borrow_mut().take();
        });
    }
}
/// Collect only complete pairing equalities. Pairings used as Sigma inputs are computed normally.
pub fn verify_captured<R: rand::RngCore + rand::CryptoRng>(
    mode: VerificationMode,
    rng: &mut R,
    verify: impl FnOnce() -> bool,
) -> bool {
    verify_captured_impl(mode, rng, verify, |equations| {
        equations
            .iter()
            .flatten()
            .all(|(p, q)| p.checked() && q.checked())
    })
}
/// Only the API module can create this capability, after checked input validation.
pub(crate) fn verify_captured_checked<R: rand::RngCore + rand::CryptoRng>(
    mode: VerificationMode,
    rng: &mut R,
    _checked: &crate::api::CheckedGroups,
    verify: impl FnOnce() -> bool,
) -> bool {
    verify_captured_impl(mode, rng, verify, |_| true)
}
fn verify_captured_impl<R: rand::RngCore + rand::CryptoRng>(
    mode: VerificationMode,
    rng: &mut R,
    verify: impl FnOnce() -> bool,
    validate: impl FnOnce(&[PairingEquation]) -> bool,
) -> bool {
    EQUATIONS.with(|c| {
        assert!(c.borrow().is_none());
        *c.borrow_mut() = Some(vec![])
    });
    let _scope = EquationScope;
    if !verify() {
        return false;
    }
    let equations = EQUATIONS.with(|c| c.borrow_mut().take().unwrap());
    if equations.is_empty() || !validate(&equations) {
        return false;
    }
    // A single residual has no other residual with which to cancel. Its exact
    // native check is the same acceptance condition, without a redundant power.
    if mode == VerificationMode::Specification || equations.len() == 1 {
        return equations
            .iter()
            .all(|e| pairing_product(e).is_identity().into());
    }
    let mut groups =
        std::collections::BTreeMap::<Vec<u8>, (G2Affine, Vec<G1Projective>, Vec<Scalar>)>::new();
    for e in equations {
        let w = random_batch_weight128(rng);
        for (p, q) in e {
            let entry = groups
                .entry(q.to_compressed().to_vec())
                .or_insert((q, vec![], vec![]));
            entry.1.push(p.into());
            entry.2.push(w);
        }
    }
    let terms: Vec<_> = groups
        .into_values()
        .map(|(q, p, w)| (G1Projective::msm(&p, &w).to_affine(), q))
        .collect();
    pairing_product(&terms).is_identity().into()
}
pub fn pairing_product(terms: &[(G1Affine, G2Affine)]) -> Gt {
    let p: Vec<_> = terms
        .iter()
        .map(|(p, q)| (*p, G2Prepared::from(*q)))
        .collect();
    multi_miller_loop(&p.iter().map(|(p, q)| (p, q)).collect::<Vec<_>>()).final_exponentiation()
}
pub fn check_pairing_equality(p: &G1Affine, q: &G2Prepared, r: &G1Affine, s: &G2Prepared) -> bool {
    // Prepared inputs retain their canonical source affine point for safe regrouping.
    let equation = vec![(*p, q.1), (-*r, s.1)];
    if EQUATIONS.with(|c| {
        let mut c = c.borrow_mut();
        if let Some(v) = c.as_mut() {
            v.push(equation.clone());
            true
        } else {
            false
        }
    }) {
        return true;
    }
    pairing_product(&equation).is_identity().into()
}

pub(crate) struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}
impl<'a> Reader<'a> {
    pub fn new(b: &'a [u8]) -> Self {
        Self { bytes: b, pos: 0 }
    }
    fn take<const N: usize>(&mut self) -> Result<[u8; N], String> {
        let end = self.pos.checked_add(N).ok_or("length overflow")?;
        let a = self
            .bytes
            .get(self.pos..end)
            .ok_or("truncated native message")?
            .try_into()
            .unwrap();
        self.pos = end;
        Ok(a)
    }
    pub fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take::<1>()?[0])
    }
    pub fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take()?))
    }
    pub fn scalar(&mut self) -> Result<Scalar, String> {
        Option::<Scalar>::from(Scalar::from_bytes_le(&self.take()?))
            .ok_or("noncanonical scalar".into())
    }
    pub fn g1(&mut self) -> Result<G1Projective, String> {
        let bytes = self.take()?;
        darlt_spseq_fc::subgroup_audit::decode("G1", &bytes, "rp23::Reader::g1");
        Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed(&bytes))
            .map(|p| G1Projective(p.into()))
            .ok_or("invalid G1 encoding/subgroup".into())
    }
    pub fn g2(&mut self) -> Result<G2Projective, String> {
        let bytes = self.take()?;
        darlt_spseq_fc::subgroup_audit::decode("G2", &bytes, "rp23::Reader::g2");
        Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed(&bytes))
            .map(|p| G2Projective(p.into()))
            .ok_or("invalid G2 encoding/subgroup".into())
    }
    pub fn finish(self) -> Result<(), String> {
        if self.pos == self.bytes.len() {
            Ok(())
        } else {
            Err("trailing native bytes".into())
        }
    }
}

pub trait IntoMsm {
    type Output;
    fn msm(self) -> Self::Output;
}
impl IntoMsm for Vec<(G1Projective, Scalar)> {
    type Output = G1Projective;
    fn msm(self) -> Self::Output {
        let (p, s): (Vec<_>, Vec<_>) = self.into_iter().unzip();
        G1Projective::msm(&p, &s)
    }
}
impl IntoMsm for Vec<(G2Projective, Scalar)> {
    type Output = G2Projective;
    fn msm(self) -> Self::Output {
        let (p, s): (Vec<_>, Vec<_>) = self.into_iter().unzip();
        G2Projective::msm(&p, &s)
    }
}
pub trait NativeMsm: Sized {
    fn native_msm(points: &[Self], scalars: &[Scalar]) -> Self;
}
impl NativeMsm for Scalar {
    fn native_msm(p: &[Self], s: &[Scalar]) -> Self {
        p.iter().zip(s).map(|(p, s)| p * s).sum()
    }
}
impl NativeMsm for G1Projective {
    fn native_msm(p: &[Self], s: &[Scalar]) -> Self {
        Self::msm(p, s)
    }
}
impl NativeMsm for G2Projective {
    fn native_msm(p: &[Self], s: &[Scalar]) -> Self {
        Self::msm(p, s)
    }
}
macro_rules! key_msm {
    ($name:ident) => {
        impl NativeMsm for crate::$name::VerificationKeyAuth {
            fn native_msm(keys: &[Self], scalars: &[Scalar]) -> Self {
                let first = &keys[0];
                Self {
                    alpha: G2Projective::msm(
                        &keys.iter().map(|k| k.alpha).collect::<Vec<_>>(),
                        scalars,
                    ),
                    beta_g1: (0..first.beta_g1.len())
                        .map(|i| {
                            G1Projective::msm(
                                &keys.iter().map(|k| k.beta_g1[i]).collect::<Vec<_>>(),
                                scalars,
                            )
                        })
                        .collect(),
                    beta_g2: (0..first.beta_g2.len())
                        .map(|i| {
                            G2Projective::msm(
                                &keys.iter().map(|k| k.beta_g2[i]).collect::<Vec<_>>(),
                                scalars,
                            )
                        })
                        .collect(),
                }
            }
        }
    };
}
key_msm!(compact);
key_msm!(divisible);

#[cfg(test)]
mod tests {
    use super::*;
    struct Coefficients {
        values: std::collections::VecDeque<[u8; 16]>,
        draws: usize,
    }
    impl Coefficients {
        fn new(values: impl IntoIterator<Item = u128>) -> Self {
            Self {
                values: values.into_iter().map(u128::to_le_bytes).collect(),
                draws: 0,
            }
        }
    }
    impl rand::RngCore for Coefficients {
        fn next_u32(&mut self) -> u32 {
            panic!("coefficient sampling must request16bytes")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("coefficient sampling must request16bytes")
        }
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            assert_eq!(dest.len(), 16);
            self.draws += 1;
            dest.copy_from_slice(
                &self
                    .values
                    .pop_front()
                    .expect("independent coefficient draw"),
            );
        }
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }
    impl rand::CryptoRng for Coefficients {}
    #[test]
    fn batch_weights_are_nonzero_128_bit_integers_without_modular_bias() {
        let mut rng = Coefficients::new([0, u128::MAX, 1]);
        let a = random_batch_weight128(&mut rng).to_bytes_le();
        assert_eq!(&a[..16], &u128::MAX.to_le_bytes());
        assert!(a[16..].iter().all(|x| *x == 0));
        assert_eq!(rng.draws, 2);
        assert_eq!(random_batch_weight128(&mut rng), Scalar::ONE);
        assert_eq!(rng.draws, 3);
    }
    #[test]
    fn one_step_batches_all_pairing_equations_and_rejects_each_bad_residual() {
        let g = G1Affine::generator();
        let q = G2Prepared::from(G2Affine::generator());
        let bad = (G1Projective::generator() * Scalar::from(2u64)).to_affine();
        for corrupted in [None, Some(0), Some(1), Some(2), Some(3)] {
            let mut rng = Coefficients::new([1, 2, 3, 4]);
            start_counts();
            let accepted = verify_captured(VerificationMode::Randomized, &mut rng, || {
                (0..4).all(|i| {
                    check_pairing_equality(&g, &q, if corrupted == Some(i) { &bad } else { &g }, &q)
                })
            });
            let counts = stop_counts();
            assert_eq!(accepted, corrupted.is_none());
            assert_eq!(rng.draws, 4);
            assert_eq!(counts.final_exponentiations, 1);
        }
        assert!(verify_captured(
            VerificationMode::Randomized,
            &mut NoCoins,
            || { check_pairing_equality(&g, &q, &g, &q) }
        ));
    }
    struct NoCoins;
    impl rand::RngCore for NoCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("coins requested before subgroup rejection")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("coins requested before subgroup rejection")
        }
        fn fill_bytes(&mut self, _: &mut [u8]) {
            panic!("coins requested before subgroup rejection")
        }
        fn try_fill_bytes(&mut self, _: &mut [u8]) -> Result<(), rand::Error> {
            panic!("coins requested before subgroup rejection")
        }
    }
    impl rand::CryptoRng for NoCoins {}
    #[test]
    fn typed_and_captured_nonsubgroup_rejected_before_random_weights() {
        let raw = (1u64..256)
            .find_map(|i| {
                let mut b = [0; 48];
                b[0] = 0x80;
                b[40..].copy_from_slice(&i.to_be_bytes());
                let p = Option::<blstrs::G1Affine>::from(
                    blstrs::G1Affine::from_compressed_unchecked(&b),
                )?;
                (!bool::from(p.is_torsion_free())).then_some(p)
            })
            .unwrap();
        let bad = G1Projective(raw.into());
        assert!(!bad.checked());
        let c = crate::api::Compact::new(8).unwrap();
        let w = c.issue().unwrap();
        let mut p = c
            .spend(&w, 1, crate::api::PayInfo::new([7; 16], [0; 16]))
            .unwrap();
        p.native.ss[0] = bad;
        assert!(!c.verify(&[p], &[7; 16], VerificationMode::Randomized, &mut NoCoins));
        let g2 = G2Prepared::from(G2Affine::generator());
        assert!(!verify_captured(
            VerificationMode::Randomized,
            &mut NoCoins,
            || check_pairing_equality(&bad.to_affine(), &g2, &G1Affine::generator(), &g2)
        ));
    }
}

impl From<&G1Projective> for G1Projective {
    fn from(p: &G1Projective) -> Self {
        *p
    }
}
impl From<&G1Affine> for G1Projective {
    fn from(p: &G1Affine) -> Self {
        (*p).into()
    }
}
impl From<&G2Projective> for G2Projective {
    fn from(p: &G2Projective) -> Self {
        *p
    }
}
impl From<&G2Affine> for G2Projective {
    fn from(p: &G2Affine) -> Self {
        (*p).into()
    }
}
pub trait ScalarInput {
    fn scalar(self) -> Scalar;
}
impl ScalarInput for Scalar {
    fn scalar(self) -> Scalar {
        self
    }
}
impl ScalarInput for &Scalar {
    fn scalar(self) -> Scalar {
        *self
    }
}
pub fn scalar(s: impl ScalarInput) -> Scalar {
    s.scalar()
}
#[macro_export]
macro_rules! msm1{($(($p:expr,$s:expr)),+$(,)?)=>{$crate::backend::G1Projective::msm(&[$($crate::backend::G1Projective::from($p)),+],&[$($crate::backend::scalar($s)),+])};}
#[macro_export]
macro_rules! msm2{($(($p:expr,$s:expr)),+$(,)?)=>{$crate::backend::G2Projective::msm(&[$($crate::backend::G2Projective::from($p)),+],&[$($crate::backend::scalar($s)),+])};}

pub fn random_scalar() -> Scalar {
    #[cfg(test)]
    {
        if let Some(value) = TEST_RNG.with(|r| r.borrow_mut().as_mut().map(Scalar::random)) {
            return value;
        }
    }
    Scalar::random(rand::thread_rng())
}
#[cfg(test)]
thread_local! {static TEST_RNG:RefCell<Option<rand::rngs::StdRng>>=const{RefCell::new(None)};}
#[cfg(test)]
pub(crate) fn with_test_seed<T>(seed: u64, run: impl FnOnce() -> T) -> T {
    use rand::SeedableRng;
    struct Clear;
    impl Drop for Clear {
        fn drop(&mut self) {
            TEST_RNG.with(|r| {
                r.borrow_mut().take();
            });
        }
    }
    TEST_RNG.with(|r| {
        assert!(r.borrow().is_none());
        *r.borrow_mut() = Some(rand::rngs::StdRng::seed_from_u64(seed));
    });
    let _clear = Clear;
    run()
}
