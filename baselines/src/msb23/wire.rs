//! Versioned, bounded canonical encodings, including subgroup-checked decoding.
//! Public message decoding establishes shape, not cryptographic validity.
use super::{pok, scheme::*, set_commit};
use crate::arithmetic::*;
use blstrs::{G1Affine, G2Affine};
use ff::Field;
use group::Group;
const MAGIC: &[u8; 8] = b"SPUC002\0";
const MAX: usize = 8 * 1024 * 1024;
const ITEMS: usize = 4097;
fn begin(tag: u8) -> Vec<u8> {
    let mut b = MAGIC.to_vec();
    b.push(tag);
    b
}
fn n(b: &mut Vec<u8>, n: usize) {
    b.extend((n as u64).to_be_bytes())
}
fn points(b: &mut Vec<u8>, v: &[G1]) {
    n(b, v.len());
    for x in v {
        b.extend(enc1(*x))
    }
}
fn scalars(b: &mut Vec<u8>, v: &[S]) {
    n(b, v.len());
    for x in v {
        b.extend(encs(*x))
    }
}
fn sets(b: &mut Vec<u8>, v: &[Vec<S>]) {
    n(b, v.len());
    for x in v {
        scalars(b, x)
    }
}
fn sig(b: &mut Vec<u8>, s: &Signature) {
    b.extend(enc1(s.z));
    b.extend(enc1(s.y));
    b.extend(enc2(s.yhat));
    b.extend(enc1(s.t));
}
fn disclosure(b: &mut Vec<u8>, d: &Disclosure) {
    n(b, d.indices.len());
    for (i, s) in d.indices.iter().zip(&d.sets) {
        n(b, *i);
        scalars(b, s)
    }
}

pub fn parameters_statement(p: &PublicParameters) -> Vec<u8> {
    let mut b = begin(0);
    n(&mut b, p.sc.max_cardinality);
    points(&mut b, &p.sc.srs1);
    n(&mut b, p.sc.srs2.len());
    for x in &p.sc.srs2 {
        b.extend(enc2(*x))
    }
    b.extend(enc1(p.x0));
    n(&mut b, p.xs.len());
    for x in &p.xs {
        b.extend(enc2(*x))
    }
    b
}
pub fn encode_parameters(p: &PublicParameters) -> Vec<u8> {
    let mut b = begin(1);
    frame(&mut b, &parameters_statement(p));
    points(&mut b, &p.registration.a1);
    n(&mut b, p.registration.a2.len());
    for x in &p.registration.a2 {
        b.extend(enc2(*x))
    }
    scalars(&mut b, &p.registration.z);
    b
}
pub fn issue_statement(r: &IssueRequest) -> Vec<u8> {
    let mut b = begin(2);
    b.extend(r.session);
    b.extend(enc1(r.nym));
    points(&mut b, &r.blinded);
    sets(&mut b, &r.sets);
    b
}
pub fn encode_issue_request(r: &IssueRequest) -> Vec<u8> {
    let mut b = begin(3);
    frame(&mut b, &issue_statement(r));
    b.extend(r.first.bytes());
    b
}
pub fn encode_issue_delivery(r: &IssueDelivery) -> Vec<u8> {
    let mut b = begin(4);
    frame(&mut b, &r.request_id);
    sig(&mut b, &r.sig);
    points(&mut b, &r.cs);
    points(&mut b, &r.update_key);
    b
}
pub fn delegate_statement(r: &DelegateRequest) -> Vec<u8> {
    let mut b = begin(5);
    b.extend(r.session);
    b.extend(enc1(r.nym));
    scalars(&mut b, &r.added);
    b
}
pub fn encode_delegate_request(r: &DelegateRequest) -> Vec<u8> {
    let mut b = begin(6);
    frame(&mut b, &delegate_statement(r));
    b
}
pub fn encode_delegate_delivery(r: &DelegateDelivery) -> Vec<u8> {
    let mut b = begin(7);
    frame(&mut b, &r.request_id);
    sig(&mut b, &r.orphan);
    points(&mut b, &r.cs);
    sets(&mut b, &r.sets);
    scalars(&mut b, &r.openings);
    b
}
pub fn show_statement(r: &ShowFirst) -> Vec<u8> {
    let mut b = begin(8);
    frame(&mut b, &r.context);
    disclosure(&mut b, &r.disclosed);
    sig(&mut b, &r.sig);
    points(&mut b, &r.cs);
    b.extend(enc1(r.nym));
    b.extend(enc1(r.witness));
    b
}
/// Canonical bytes of policy-independent holder points. This crate-private
/// value is owned only by the non-Clone, consumed show preparation.
pub(crate) struct PreparedShowEncoding {
    tail: Vec<u8>,
    commitments: Vec<Vec<u8>>,
}
impl PreparedShowEncoding {
    pub(crate) fn new(signature: &Signature, cs: &[G1], nym: G1) -> Self {
        let commitments: Vec<_> = cs.iter().map(|&c| enc1(c)).collect();
        let mut tail = Vec::new();
        sig(&mut tail, signature);
        n(&mut tail, cs.len());
        for c in &commitments {
            tail.extend(c);
        }
        tail.extend(enc1(nym));
        Self { tail, commitments }
    }
    pub(crate) fn selected_commitments(&self, indices: &[usize]) -> Vec<&[u8]> {
        indices
            .iter()
            .map(|&i| self.commitments[i].as_slice())
            .collect()
    }
}
pub(crate) fn show_statement_prepared(r: &ShowFirst, encoded: &PreparedShowEncoding) -> Vec<u8> {
    // Context and disclosure precede the prepared points in the established
    // byte order, so this path caches encoding without extending a hash prefix.
    let mut b = begin(8);
    frame(&mut b, &r.context);
    disclosure(&mut b, &r.disclosed);
    b.extend(&encoded.tail);
    b.extend(enc1(r.witness));
    b
}
pub fn encode_show_first(r: &ShowFirst) -> Vec<u8> {
    let mut b = begin(9);
    frame(&mut b, &show_statement(r));
    b.extend(r.first.bytes());
    b
}
/// A persisted holder record includes secrets. It is never a transmitted token.
pub fn encode_credential(c: &Credential) -> Vec<u8> {
    let mut b = begin(10);
    sig(&mut b, &c.sig);
    points(&mut b, &c.cs);
    sets(&mut b, &c.sets);
    scalars(&mut b, &c.openings);
    b.extend(enc1(c.nym));
    b.extend(encs(c.aux));
    match &c.update {
        None => b.push(0),
        Some(u) => {
            b.push(1);
            points(&mut b, &u.key);
            b.extend(encs(u.private_mu))
        }
    }
    b
}

struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}
impl<'a> Reader<'a> {
    fn new(b: &'a [u8], tag: u8) -> Result<Self> {
        if b.len() > MAX {
            return Err("byte limit".into());
        }
        let mut r = Self { b, p: 0 };
        if r.take(8)? != MAGIC || r.take(1)?[0] != tag {
            return Err("wrong profile/tag".into());
        }
        Ok(r)
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        if n > self.b.len() - self.p {
            return Err("truncated object".into());
        }
        let p = self.p;
        self.p += n;
        Ok(&self.b[p..self.p])
    }
    fn count(&mut self, max: usize, min: usize) -> Result<usize> {
        let raw = u64::from_be_bytes(self.take(8)?.try_into().unwrap());
        let n = usize::try_from(raw).map_err(|_| "length overflow")?;
        if n > max || min > 0 && n > (self.b.len() - self.p) / min {
            return Err("length/count limit".into());
        }
        Ok(n)
    }
    fn frame(&mut self) -> Result<&'a [u8]> {
        let n = self.count(MAX, 1)?;
        self.take(n)
    }
    fn g1(&mut self) -> Result<G1> {
        let a: [u8; 48] = self.take(48)?.try_into().unwrap();
        crate::subgroup_audit::decode("G1", &a, "msb23::wire::g1");
        let p = Option::<G1Affine>::from(G1Affine::from_compressed(&a))
            .ok_or("invalid G1 subgroup encoding")?;
        if p.to_compressed() != a {
            return Err("noncanonical G1".into());
        }
        Ok(G1::from(p))
    }
    fn g2(&mut self) -> Result<G2> {
        let a: [u8; 96] = self.take(96)?.try_into().unwrap();
        crate::subgroup_audit::decode("G2", &a, "msb23::wire::g2");
        let p = Option::<G2Affine>::from(G2Affine::from_compressed(&a))
            .ok_or("invalid G2 subgroup encoding")?;
        if p.to_compressed() != a {
            return Err("noncanonical G2".into());
        }
        Ok(G2::from(p))
    }
    fn scalar(&mut self) -> Result<S> {
        let a: [u8; 32] = self.take(32)?.try_into().unwrap();
        Option::<S>::from(S::from_bytes_be(&a)).ok_or("invalid canonical scalar".into())
    }
    fn points(&mut self) -> Result<Vec<G1>> {
        let n = self.count(ITEMS, 48)?;
        (0..n).map(|_| self.g1()).collect()
    }
    fn scalars(&mut self) -> Result<Vec<S>> {
        let n = self.count(ITEMS, 32)?;
        (0..n).map(|_| self.scalar()).collect()
    }
    fn sets(&mut self) -> Result<Vec<Vec<S>>> {
        let n = self.count(3, 8)?;
        (0..n).map(|_| self.scalars()).collect()
    }
    fn sig(&mut self) -> Result<Signature> {
        Ok(Signature {
            z: self.g1()?,
            y: self.g1()?,
            yhat: self.g2()?,
            t: self.g1()?,
        })
    }
    fn disclosure(&mut self) -> Result<Disclosure> {
        let n = self.count(3, 16)?;
        let mut indices = Vec::new();
        let mut sets = Vec::new();
        for _ in 0..n {
            indices.push(self.count(2, 0)?);
            sets.push(self.scalars()?)
        }
        Ok(Disclosure { indices, sets })
    }
    fn end(self) -> Result<()> {
        if self.p == self.b.len() {
            Ok(())
        } else {
            Err("trailing bytes".into())
        }
    }
}
fn first(r: &mut Reader) -> Result<pok::First> {
    pok::First::from_bytes(r.take(48)?).map_err(str::to_owned)
}
pub fn decode_parameters(b: &[u8]) -> Result<PublicParameters> {
    let mut r = Reader::new(b, 1)?;
    let mut s = Reader::new(r.frame()?, 0)?;
    let max_cardinality = s.count(4096, 0)?;
    let srs1 = s.points()?;
    let n = s.count(ITEMS, 96)?;
    let srs2 = (0..n).map(|_| s.g2()).collect::<Result<Vec<_>>>()?;
    let x0 = s.g1()?;
    let n = s.count(5, 96)?;
    let xs = (0..n).map(|_| s.g2()).collect::<Result<Vec<_>>>()?;
    s.end()?;
    let a1 = r.points()?;
    let n = r.count(6, 96)?;
    let a2 = (0..n).map(|_| r.g2()).collect::<Result<Vec<_>>>()?;
    let z = r.scalars()?;
    r.end()?;
    Ok(PublicParameters {
        sc: set_commit::Params {
            srs1,
            srs2,
            max_cardinality,
        },
        x0,
        xs,
        registration: RegistrationProof { a1, a2, z },
    })
}
pub fn decode_issue_request(b: &[u8]) -> Result<IssueRequest> {
    let mut r = Reader::new(b, 3)?;
    let mut s = Reader::new(r.frame()?, 2)?;
    let session = s.take(32)?.try_into().unwrap();
    let nym = s.g1()?;
    let blinded = s.points()?;
    let sets = s.sets()?;
    s.end()?;
    let first = first(&mut r)?;
    r.end()?;
    Ok(IssueRequest {
        session,
        nym,
        blinded,
        sets,
        first,
    })
}
pub fn decode_issue_delivery(b: &[u8]) -> Result<IssueDelivery> {
    let mut r = Reader::new(b, 4)?;
    let request_id = r.frame()?.to_vec();
    let sig = r.sig()?;
    let cs = r.points()?;
    let update_key = r.points()?;
    r.end()?;
    if request_id.len() != 32 {
        return Err("request digest length".into());
    }
    Ok(IssueDelivery {
        request_id,
        sig,
        cs,
        update_key,
    })
}
pub fn decode_delegate_request(b: &[u8]) -> Result<DelegateRequest> {
    let mut r = Reader::new(b, 6)?;
    let mut s = Reader::new(r.frame()?, 5)?;
    let session = s.take(32)?.try_into().unwrap();
    let nym = s.g1()?;
    let added = s.scalars()?;
    s.end()?;
    r.end()?;
    Ok(DelegateRequest {
        session,
        nym,
        added,
    })
}
pub fn decode_delegate_delivery(b: &[u8]) -> Result<DelegateDelivery> {
    let mut r = Reader::new(b, 7)?;
    let request_id = r.frame()?.to_vec();
    let orphan = r.sig()?;
    let cs = r.points()?;
    let sets = r.sets()?;
    let openings = r.scalars()?;
    r.end()?;
    if request_id.len() != 32 {
        return Err("request digest length".into());
    }
    Ok(DelegateDelivery {
        request_id,
        orphan,
        cs,
        sets,
        openings,
    })
}
pub fn decode_show_first(b: &[u8]) -> Result<ShowFirst> {
    let mut r = Reader::new(b, 9)?;
    let mut s = Reader::new(r.frame()?, 8)?;
    let context = s.frame()?.to_vec();
    if context.len() > 4096 {
        return Err("context length limit".into());
    }
    let disclosed = s.disclosure()?;
    let sig = s.sig()?;
    let cs = s.points()?;
    let nym = s.g1()?;
    let witness = s.g1()?;
    s.end()?;
    let first = first(&mut r)?;
    r.end()?;
    Ok(ShowFirst {
        context,
        disclosed,
        sig,
        cs,
        nym,
        witness,
        first,
    })
}
#[allow(clippy::unnecessary_map_or)]
pub fn decode_credential(v: &Registered, b: &[u8]) -> Result<Credential> {
    let mut r = Reader::new(b, 10)?;
    let sig = r.sig()?;
    let cs = r.points()?;
    let sets = r.sets()?;
    let openings = r.scalars()?;
    let nym = r.g1()?;
    let aux = r.scalar()?;
    let update = match r.take(1)?[0] {
        0 => None,
        1 => Some(RootUpdate {
            key: r.points()?,
            private_mu: r.scalar()?,
        }),
        _ => return Err("invalid holder role tag".into()),
    };
    r.end()?;
    if aux == S::ZERO
        || g1_mul(G1::generator(), aux) != nym
        || sets.first() != Some(&vec![dummy_attribute()])
        || sets.get(1).map_or(true, |s| {
            s.len() != v.parameters().sc.max_cardinality
                || s.contains(&period_attribute())
                || s.contains(&dummy_attribute())
        })
        || (cs.len() == 3 && sets.get(2) != Some(&vec![period_attribute()]))
        || !decoded_credential_valid(v, nym, &cs, &sig, &sets, &openings)
    {
        return Err("invalid persisted holder credential".into());
    }
    match &update {
        None if cs.len() != 3 => return Err("terminal holder must have three commitments".into()),
        Some(u) => {
            if cs.len() != 2 || u.private_mu == S::ZERO || u.key.len() != v.pp.sc.srs1.len() {
                return Err("invalid root update state".into());
            }
            for (i, a) in u.key.iter().enumerate() {
                if *a == G1::identity()
                    || pair(*a, sig.yhat) != pair(g1_mul(v.pp.sc.srs1[i], u.private_mu), v.pp.xs[4])
                {
                    return Err("invalid root private-scale UK state".into());
                }
            }
        }
        _ => {}
    }
    // This decoder already verifies the complete signature, openings and
    // private-scale update key above. The local source binding is assigned
    // only after those checks, and is never part of the wire transcript.
    Ok(Credential {
        system_id: v.id().to_vec(),
        sig,
        cs,
        sets,
        openings,
        nym,
        aux,
        update,
    })
}

pub fn issue_request_payload(r: &IssueRequest) -> usize {
    32 + 48 + r.blinded.len() * 48 + r.sets.iter().map(|s| s.len() * 32).sum::<usize>() + 48
}
pub fn issue_delivery_payload(r: &IssueDelivery) -> usize {
    32 + 240 + r.cs.len() * 48 + r.update_key.len() * 48
}
pub fn delegate_request_payload(r: &DelegateRequest) -> usize {
    32 + 48 + r.added.len() * 32
}
pub fn delegate_delivery_payload(r: &DelegateDelivery) -> usize {
    32 + 240
        + r.cs.len() * 48
        + r.sets.iter().map(|s| s.len() * 32).sum::<usize>()
        + r.openings.len() * 32
}
pub fn show_first_payload(r: &ShowFirst) -> usize {
    r.context.len() + r.disclosed.count() * 32 + 240 + r.cs.len() * 48 + 48 + 48 + 48
}
pub fn proof_payload(r: &pok::Response) -> usize {
    r.announcements.len() * 48 + 32 + r.responses.len() * 32
}

/// Canonical decoding plus an immutable provenance seal. Raw decoders return
/// mutable messages; passing those later to raw protocol APIs remains strict.
pub fn decode_parameters_checked(b: &[u8]) -> Result<CheckedParameters> {
    register_decoded(decode_parameters(b)?)
}
pub fn decode_issue_request_checked(b: &[u8]) -> Result<CheckedIssueRequest> {
    decoded_issue_request(decode_issue_request(b)?)
}
pub fn decode_issue_delivery_checked(b: &[u8]) -> Result<CheckedIssueDelivery> {
    Ok(decoded_issue_delivery(decode_issue_delivery(b)?))
}
pub fn decode_delegate_request_checked(b: &[u8]) -> Result<CheckedDelegateRequest> {
    decoded_delegate_request(decode_delegate_request(b)?)
}
pub fn decode_delegate_delivery_checked(b: &[u8]) -> Result<CheckedDelegateDelivery> {
    Ok(decoded_delegate_delivery(decode_delegate_delivery(b)?))
}
pub fn decode_show_first_checked(b: &[u8]) -> Result<CheckedShowFirst> {
    decoded_show_first(decode_show_first(b)?)
}
