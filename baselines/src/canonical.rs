//! Bounded canonical field, subgroup and Sigma-proof decoding.
//! Decoding establishes canonical structure; it does not establish proof validity.
use crate::curve::{enc1, enc2, encs, enct, G1, G2, GT, S};
#[derive(Clone, Debug)]
pub struct DecodedSigmaProof {
    pub c: S,
    pub z: Vec<S>,
    pub orz: Vec<[S; 3]>,
}
use blstrs::{Compress, G1Affine, G2Affine};
use group::Group;
use std::fmt;

#[derive(Clone, Copy, Debug)]
pub struct DecodeLimits {
    /// Maximum size of one top-level object or nested frame, in bytes.
    pub max_bytes: usize,
    /// Maximum entries in any vector; also checked against remaining bytes.
    pub max_vector_items: usize,
    pub max_context_bytes: usize,
    /// Largest permitted attribute index (not a parameter-specific schema check).
    pub max_attribute_index: usize,
}
impl Default for DecodeLimits {
    fn default() -> Self {
        Self {
            max_bytes: 8 * 1024 * 1024,
            max_vector_items: 65_536,
            max_context_bytes: 1024 * 1024,
            max_attribute_index: 65_535,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    UnexpectedEof,
    TrailingBytes,
    LimitExceeded(&'static str),
    InvalidEncoding(&'static str),
    InvalidTag(u8),
}
impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for DecodeError {}
pub type Result<T> = std::result::Result<T, DecodeError>;

pub(crate) struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
    limits: DecodeLimits,
}
impl<'a> Reader<'a> {
    pub(crate) fn new(bytes: &'a [u8], limits: DecodeLimits) -> Result<Self> {
        if bytes.len() > limits.max_bytes {
            return Err(DecodeError::LimitExceeded("bytes"));
        }
        Ok(Self {
            bytes,
            pos: 0,
            limits,
        })
    }
    fn remaining(&self) -> usize {
        self.bytes.len() - self.pos
    }
    pub(crate) fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        if n > self.remaining() {
            return Err(DecodeError::UnexpectedEof);
        }
        let start = self.pos;
        self.pos += n;
        Ok(&self.bytes[start..self.pos])
    }
    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(self.take(8)?.try_into().unwrap()))
    }
    pub(crate) fn bounded_usize(&mut self, max: usize, field: &'static str) -> Result<usize> {
        let n = usize::try_from(self.u64()?).map_err(|_| DecodeError::LimitExceeded(field))?;
        if n > max {
            return Err(DecodeError::LimitExceeded(field));
        }
        Ok(n)
    }
    pub(crate) fn g1(&mut self) -> Result<G1> {
        decode_g1(self.take(48)?)
    }
    pub(crate) fn g2(&mut self) -> Result<G2> {
        decode_g2(self.take(96)?)
    }
    fn count(&mut self, min_size: usize) -> Result<usize> {
        let n = self.bounded_usize(self.limits.max_vector_items, "vector length")?;
        // Division avoids overflow even for adversarial u64 lengths.
        if min_size != 0 && n > self.remaining() / min_size {
            return Err(DecodeError::UnexpectedEof);
        }
        Ok(n)
    }
    pub(crate) fn finish(&self) -> Result<()> {
        if self.remaining() == 0 {
            Ok(())
        } else {
            Err(DecodeError::TrailingBytes)
        }
    }
    pub(crate) fn scalar(&mut self) -> Result<S> {
        decode_scalar(self.take(32)?)
    }
}

pub fn decode_scalar(bytes: &[u8]) -> Result<S> {
    let raw: &[u8; 32] = bytes
        .try_into()
        .map_err(|_| DecodeError::InvalidEncoding("scalar length"))?;
    let x =
        Option::<S>::from(S::from_bytes_be(raw)).ok_or(DecodeError::InvalidEncoding("scalar"))?;
    if encs(x) != bytes {
        return Err(DecodeError::InvalidEncoding("noncanonical scalar"));
    }
    Ok(x)
}
pub fn decode_g1(bytes: &[u8]) -> Result<G1> {
    let raw: &[u8; 48] = bytes
        .try_into()
        .map_err(|_| DecodeError::InvalidEncoding("G1 length"))?;
    crate::subgroup_audit::decode("G1", bytes, "canonical::decode_g1");
    let p = Option::<G1Affine>::from(G1Affine::from_compressed(raw))
        .ok_or(DecodeError::InvalidEncoding("G1 point or subgroup"))?;
    let p = G1::from(p);
    if enc1(p) != bytes {
        return Err(DecodeError::InvalidEncoding("noncanonical G1"));
    }
    Ok(p)
}
pub fn decode_g2(bytes: &[u8]) -> Result<G2> {
    let raw: &[u8; 96] = bytes
        .try_into()
        .map_err(|_| DecodeError::InvalidEncoding("G2 length"))?;
    crate::subgroup_audit::decode("G2", bytes, "canonical::decode_g2");
    let p = Option::<G2Affine>::from(G2Affine::from_compressed(raw))
        .ok_or(DecodeError::InvalidEncoding("G2 point or subgroup"))?;
    let p = G2::from(p);
    if enc2(p) != bytes {
        return Err(DecodeError::InvalidEncoding("noncanonical G2"));
    }
    Ok(p)
}
/// The project's 288-byte all-FF sentinel is the only encoding of GT identity.
/// All other strings use blstrs's checked torus codec and must re-encode exactly.
pub fn decode_gt(bytes: &[u8]) -> Result<GT> {
    if bytes.len() != 288 {
        return Err(DecodeError::InvalidEncoding("GT length"));
    }
    crate::subgroup_audit::decode("GT", bytes, "canonical::decode_gt");
    if bytes.iter().all(|&b| b == 255) {
        return Ok(GT::identity());
    }
    let x = GT::read_compressed(std::io::Cursor::new(bytes))
        .map_err(|_| DecodeError::InvalidEncoding("GT field or subgroup"))?;
    if enct(x) != bytes {
        return Err(DecodeError::InvalidEncoding("noncanonical GT"));
    }
    Ok(x)
}

pub fn decode_proof(bytes: &[u8]) -> Result<DecodedSigmaProof> {
    decode_proof_with_limits(bytes, DecodeLimits::default())
}
pub fn decode_proof_with_limits(bytes: &[u8], limits: DecodeLimits) -> Result<DecodedSigmaProof> {
    let mut r = Reader::new(bytes, limits)?;
    let c = r.scalar()?;
    let n = r.count(32)?;
    let mut z = Vec::with_capacity(n);
    for _ in 0..n {
        z.push(r.scalar()?);
    }
    let n = r.count(96)?;
    let mut orz = Vec::with_capacity(n);
    for _ in 0..n {
        orz.push([r.scalar()?, r.scalar()?, r.scalar()?]);
    }
    r.finish()?;
    Ok(DecodedSigmaProof { c, z, orz })
}
