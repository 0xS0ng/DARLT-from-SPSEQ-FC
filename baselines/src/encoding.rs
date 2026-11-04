//! Canonical, bounded messages for the BLS12-381 baseline profiles.
use crate::arithmetic::{G1, G2, GT, S};
#[cfg(test)]
use ff::Field;

use group::Group;
use sha2::{Digest, Sha256};
use std::cell::RefCell;

pub const MAX_BYTES: usize = 8 * 1024 * 1024;
pub const MAX_ITEMS: usize = 4096;
pub const GT_BYTES: usize = 288;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
impl From<crate::canonical::DecodeError> for Error {
    fn from(e: crate::canonical::DecodeError) -> Self {
        Self(e.to_string())
    }
}

thread_local! {static HZ:RefCell<Option<u64>>=const{RefCell::new(None)};}
pub fn start_counts() {
    crate::arithmetic::start_counts();
    HZ.with(|v| *v.borrow_mut() = Some(0));
}
pub fn stop_counts() -> crate::arithmetic::Counts {
    let mut c = crate::arithmetic::stop_counts();
    c.hz += HZ.with(|v| v.borrow_mut().take().unwrap_or(0));
    c
}
/// Read the complete arithmetic and encoding hash scopes without stopping
/// either layer. Native SLW/CDM hashes and arithmetic-prefix hashes are added.
pub fn snapshot_counts() -> Option<crate::arithmetic::Counts> {
    let mut counts = crate::arithmetic::snapshot_counts()?;
    counts.hz += HZ.with(|v| *v.borrow())?;
    Some(counts)
}
/// A domain-separated rejection sampler over the whole scalar field.
pub fn hash_fr(tag: &[u8], input: &[u8]) -> S {
    HZ.with(|v| {
        if let Some(n) = v.borrow_mut().as_mut() {
            *n += 1;
        }
    });
    let mut h = Sha256::new();
    h.update(b"BLS12-381-BASELINE-FR-V1");
    h.update((tag.len() as u64).to_be_bytes());
    h.update(tag);
    h.update((input.len() as u64).to_be_bytes());
    h.update(input);
    for i in 0u64.. {
        let mut t = h.clone();
        t.update(i.to_be_bytes());
        let b: [u8; 32] = t.finalize().into();
        if let Some(s) = Option::<S>::from(S::from_bytes_be(&b)) {
            return s;
        }
    }
    unreachable!()
}

pub struct Writer {
    out: Vec<u8>,
}
impl Writer {
    pub fn new(tag: &[u8]) -> Self {
        let mut v = Self {
            out: b"BLSB\x01".to_vec(),
        };
        v.bytes(tag);
        v
    }
    pub fn u8(&mut self, x: u8) {
        self.out.push(x);
    }
    pub fn u32(&mut self, x: u32) {
        self.out.extend(x.to_be_bytes());
    }
    pub fn u64(&mut self, x: u64) {
        self.out.extend(x.to_be_bytes());
    }
    pub fn fr(&mut self, x: S) {
        self.out.extend(x.to_bytes_be());
    }
    pub fn scalar(&mut self, x: S) {
        self.fr(x);
    }
    pub fn g1(&mut self, x: G1) {
        self.out.extend(x.to_compressed());
    }
    pub fn g2(&mut self, x: G2) {
        self.out.extend(x.to_compressed());
    }
    pub fn gt(&mut self, x: GT) {
        self.out.extend(crate::arithmetic::enct(x));
    }
    pub fn bytes(&mut self, x: &[u8]) {
        self.u64(x.len() as u64);
        self.out.extend(x);
    }
    pub fn indices(&mut self, x: &[usize]) {
        self.u64(x.len() as u64);
        for &i in x {
            self.u32(i.try_into().expect("bounded index"));
        }
    }
    pub fn finish(self) -> Vec<u8> {
        self.out
    }
}
pub struct Reader<'a> {
    input: &'a [u8],
    pos: usize,
}
impl<'a> Reader<'a> {
    pub fn new(input: &'a [u8], tag: &[u8]) -> Result<Self> {
        if input.len() > MAX_BYTES {
            return Err(Error("message limit".into()));
        }
        let mut r = Self { input, pos: 0 };
        if r.take(5)? != b"BLSB\x01" {
            return Err(Error("profile header".into()));
        }
        if r.bytes()?.as_slice() != tag {
            return Err(Error("message type".into()));
        }
        Ok(r)
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        if n > self.input.len() - self.pos {
            return Err(Error("truncated message".into()));
        }
        let start = self.pos;
        self.pos += n;
        Ok(&self.input[start..self.pos])
    }
    pub fn remaining(&self) -> usize {
        self.input.len() - self.pos
    }
    pub fn u8(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    pub fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().unwrap()))
    }
    pub fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(self.take(8)?.try_into().unwrap()))
    }
    pub fn fr(&mut self) -> Result<S> {
        Ok(crate::canonical::decode_scalar(self.take(32)?)?)
    }
    pub fn scalar(&mut self) -> Result<S> {
        self.fr()
    }
    pub fn g1(&mut self, nonzero: bool) -> Result<G1> {
        let g = crate::canonical::decode_g1(self.take(48)?)?;
        if nonzero && bool::from(g.is_identity()) {
            return Err(Error("G1 identity domain".into()));
        }
        Ok(g)
    }
    pub fn g2(&mut self, nonzero: bool) -> Result<G2> {
        let g = crate::canonical::decode_g2(self.take(96)?)?;
        if nonzero && bool::from(g.is_identity()) {
            return Err(Error("G2 identity domain".into()));
        }
        Ok(g)
    }
    pub fn gt(&mut self, nonzero: bool) -> Result<GT> {
        let g = crate::canonical::decode_gt(self.take(GT_BYTES)?)?;
        if nonzero && bool::from(g.is_identity()) {
            return Err(Error("GT identity domain".into()));
        }
        Ok(g)
    }
    pub fn bytes(&mut self) -> Result<Vec<u8>> {
        let n = self.u64()?;
        if n > MAX_BYTES as u64 {
            return Err(Error("frame limit".into()));
        }
        Ok(self.take(n as usize)?.to_vec())
    }
    pub fn indices(&mut self, max: usize) -> Result<Vec<usize>> {
        let n = self.u64()?;
        if n > MAX_ITEMS as u64 || n > (self.remaining() / 4) as u64 {
            return Err(Error("index count".into()));
        }
        let mut out = Vec::with_capacity(n as usize);
        for _ in 0..n {
            let i = self.u32()? as usize;
            if i >= max || out.last().is_some_and(|&p| p >= i) {
                return Err(Error("index domain/order".into()));
            }
            out.push(i);
        }
        Ok(out)
    }
    pub fn finish(self) -> Result<()> {
        if self.pos != self.input.len() {
            Err(Error("trailing bytes".into()))
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_fields_and_boundaries() {
        let mut w = Writer::new(b"codec");
        w.fr(S::ZERO);
        w.g1(G1::generator());
        w.g2(G2::generator());
        w.gt(GT::identity());
        w.indices(&[0, 2, 4]);
        let b = w.finish();
        let mut r = Reader::new(&b, b"codec").unwrap();
        assert_eq!(r.fr().unwrap(), S::ZERO);
        assert_eq!(r.g1(true).unwrap(), G1::generator());
        assert_eq!(r.g2(true).unwrap(), G2::generator());
        assert_eq!(r.gt(false).unwrap(), GT::identity());
        assert_eq!(r.indices(5).unwrap(), vec![0, 2, 4]);
        r.finish().unwrap();
        assert!(Reader::new(&b, b"other").is_err());
        let mut tail = b.clone();
        tail.push(0);
        let mut r = Reader::new(&tail, b"codec").unwrap();
        r.take(b.len() - r.pos).unwrap();
        assert!(r.finish().is_err());
        for n in 0..13 {
            assert!(Reader::new(&b[..n], b"codec").is_err());
        }
    }
    #[test]
    fn received_bad_points_and_noncanonical_scalars() {
        for size in [48, 96] {
            for fill in [0u8, 255u8] {
                let mut w = Writer::new(b"point");
                w.out.extend(vec![fill; size]);
                let b = w.finish();
                let mut r = Reader::new(&b, b"point").unwrap();
                assert!(if size == 48 {
                    r.g1(true).map(|_| ()).is_err()
                } else {
                    r.g2(true).map(|_| ()).is_err()
                });
            }
        }
        let mut w = Writer::new(b"zero");
        w.g1(G1::identity());
        w.g2(G2::identity());
        let b = w.finish();
        let mut r = Reader::new(&b, b"zero").unwrap();
        assert!(r.g1(true).is_err());
        let mut r = Reader::new(&b, b"zero").unwrap();
        r.g1(false).unwrap();
        assert!(r.g2(true).is_err());
        let mut w = Writer::new(b"scalar");
        w.out.extend([255; 32]);
        let b = w.finish();
        assert!(Reader::new(&b, b"scalar").unwrap().fr().is_err());
    }
}
