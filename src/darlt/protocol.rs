//! DARLT issuance and mask-refreshing derivation. Parent credentials cannot spend.
use super::{
    params::ReferenceString,
    sigma,
    verification::{self, Mode},
};
use crate::{
    common::crypto::{frame, hash_point, nonzero, points1, points2, scalars, valid1, valid2},
    metadata,
    polynomial::S,
    spseq_fc,
};
use blstrs::{G1Projective as G1, G2Projective as G2};
use ff::Field;
use group::Group;
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
pub type Result<T> = std::result::Result<T, String>;

/// Constructed only after this module's complete strict wire parser succeeds.
/// Neither a marker nor a mutable checked payload is exposed to callers.
pub(super) struct CheckedReceipt {
    parameter_id: [u8; 32],
}
impl CheckedReceipt {
    pub(super) fn parameter_id(&self) -> [u8; 32] {
        self.parameter_id
    }
}
pub(crate) struct ReceivedIssueResponse {
    response: IssueResponse,
    inputs: super::spend::ReceivedInputs,
}
pub(crate) struct ReceivedDelivery {
    delivery: Delivery,
    inputs: super::spend::ReceivedInputs,
}
pub(crate) struct ReceivedIssueRequest {
    request: IssueRequest,
    inputs: super::spend::ReceivedInputs,
}
pub(crate) struct ReceivedRecipientRequest {
    request: spseq_fc::Request,
    inputs: super::spend::ReceivedInputs,
}
impl ReceivedIssueRequest {
    pub(crate) fn request(&self) -> &IssueRequest {
        &self.request
    }
    pub(crate) fn decode(pp: &PublicParameters, bytes: &[u8]) -> Result<Self> {
        let _span = super::instrumentation::span("strict_decoding");
        let mut r = ReceiptReader { bytes, offset: 0 };
        let pku = r.g1()?;
        let q = [r.g1()?, r.g1()?];
        let cdel = r.g1()?;
        let cprv = r.g1()?;
        let mdel = r.scalars(pp.k_del)?;
        let mprv = r.scalars(pp.k_prv)?;
        let proof = sigma::Proof::decode(r.frame()?, 1 + 2 * (pp.w + 1) + 2, 0)?;
        r.finish()?;
        let request = IssueRequest {
            pku,
            q,
            cdel,
            cprv,
            mdel,
            mprv,
            proof,
        };
        if request.encode() != bytes {
            return Err("noncanonical issuance request".into());
        }
        Ok(Self {
            request,
            inputs: super::spend::ReceivedInputs::from_receipt(&CheckedReceipt {
                parameter_id: pp.id,
            }),
        })
    }
}
impl ReceivedRecipientRequest {
    pub(crate) fn decode(parameter_id: [u8; 32], bytes: &[u8]) -> Result<Self> {
        let _span = super::instrumentation::span("strict_decoding");
        let mut r = ReceiptReader { bytes, offset: 0 };
        let sid = r.frame()?.to_vec();
        let pka = r.g1()?;
        let a = r.g1()?;
        let z = r.scalar()?;
        r.finish()?;
        let request = spseq_fc::Request {
            sid,
            pka,
            proof: spseq_fc::Schnorr { a, z },
        };
        if request.encode() != bytes {
            return Err("noncanonical recipient request".into());
        }
        Ok(Self {
            request,
            inputs: super::spend::ReceivedInputs::from_receipt(&CheckedReceipt { parameter_id }),
        })
    }
    pub(super) fn request(&self) -> &spseq_fc::Request {
        &self.request
    }
    pub(super) fn inputs(&self) -> &super::spend::ReceivedInputs {
        &self.inputs
    }
}
impl ReceivedIssueResponse {
    pub(crate) fn response(&self) -> &IssueResponse {
        &self.response
    }
    pub(crate) fn decode(pp: &PublicParameters, bytes: &[u8]) -> Result<Self> {
        let _span = super::instrumentation::span("strict_decoding");
        let mut r = ReceiptReader { bytes, offset: 0 };
        let shares = [r.scalars(pp.w)?, r.scalars(pp.w)?];
        let e = r.g1()?;
        let signature = spseq_fc::Sig {
            z: r.g1()?,
            y: r.g1()?,
            yhat: r.g2()?,
        };
        let mut d = ReceiptReader {
            bytes: r.frame()?,
            offset: 0,
        };
        let base = spseq_fc::Dk {
            k0: d.g1()?,
            ka: d.g1()?,
            attrs: d.points(pp.k_del)?,
            pools: d.points(pp.w)?,
        };
        let kz = [d.g1()?, d.g1()?];
        d.finish()?;
        let metadata_proof =
            metadata::MetadataProof::from_bytes(r.take(metadata::PROOF_PAYLOAD_BYTES)?)
                .map_err(|e| format!("{e:?}"))?;
        r.finish()?;
        let response = IssueResponse {
            shares,
            e,
            signature,
            dk: DerivationKey { base, kz },
            metadata_proof,
        };
        if response.encode() != bytes {
            return Err("noncanonical issuance response".into());
        }
        Ok(Self {
            response,
            inputs: super::spend::ReceivedInputs::from_receipt(&CheckedReceipt {
                parameter_id: pp.id,
            }),
        })
    }
}
impl ReceivedDelivery {
    pub(crate) fn decode(pp: &PublicParameters, bytes: &[u8]) -> Result<Self> {
        let delivery = Delivery::decode(pp, bytes)?;
        Ok(Self {
            delivery,
            inputs: super::spend::ReceivedInputs::from_receipt(&CheckedReceipt {
                parameter_id: pp.id,
            }),
        })
    }
}
struct ReceiptReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}
impl<'a> ReceiptReader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(n)
            .ok_or("receipt length overflow")?;
        let out = self
            .bytes
            .get(self.offset..end)
            .ok_or("truncated receipt")?;
        self.offset = end;
        Ok(out)
    }
    fn number(&mut self) -> Result<usize> {
        usize::try_from(u64::from_be_bytes(self.take(8)?.try_into().unwrap()))
            .map_err(|_| "receipt dimension overflow".into())
    }
    fn frame(&mut self) -> Result<&'a [u8]> {
        let n = self.number()?;
        self.take(n)
    }
    fn scalar(&mut self) -> Result<S> {
        Option::<S>::from(S::from_bytes_be(&self.take(32)?.try_into().unwrap()))
            .ok_or("noncanonical receipt scalar".into())
    }
    fn scalars(&mut self, n: usize) -> Result<Vec<S>> {
        if self.number()? != n {
            return Err("receipt scalar dimension".into());
        }
        (0..n).map(|_| self.scalar()).collect()
    }
    fn points(&mut self, n: usize) -> Result<Vec<G1>> {
        if self.number()? != n {
            return Err("receipt point dimension".into());
        }
        (0..n).map(|_| self.g1()).collect()
    }
    fn g1(&mut self) -> Result<G1> {
        let _span = super::instrumentation::span("point_decode_and_subgroup");
        let raw: [u8; 48] = self.take(48)?.try_into().unwrap();
        crate::subgroup_audit::decode("G1", &raw, "darlt/receipt/G1");
        Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed(&raw))
            .map(G1::from)
            .ok_or("invalid receipt G1 encoding/subgroup".into())
    }
    fn g2(&mut self) -> Result<G2> {
        let _span = super::instrumentation::span("point_decode_and_subgroup");
        let raw: [u8; 96] = self.take(96)?.try_into().unwrap();
        crate::subgroup_audit::decode("G2", &raw, "darlt/receipt/G2");
        Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed(&raw))
            .map(G2::from)
            .ok_or("invalid receipt G2 encoding/subgroup".into())
    }
    fn finish(self) -> Result<()> {
        if self.offset != self.bytes.len() {
            return Err("trailing receipt bytes".into());
        }
        Ok(())
    }
}

pub struct PublicParameters {
    pub n: usize,
    pub s: usize,
    pub w: usize,
    pub k_max: usize,
    pub k_del: usize,
    pub k_prv: usize,
    pub srs: ReferenceString,
    pub fc: spseq_fc::Params,
    pub ghat: G1,
    pub h: G1,
    pub hdel: G1,
    pub adel: Vec<G1>,
    pub hprv: G1,
    pub bprv: Vec<G1>,
    pub grant_bases: Vec<G1>,
    /// Deterministic query-domain bases installed once. Account their storage
    /// as a derived cache, separately from the published monomial SRS.
    pub query_bases: BTreeMap<usize, (Vec<G1>, G1)>,
    pub id: [u8; 32],
}
impl PublicParameters {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn setup(
        n: usize,
        s: usize,
        k_max: usize,
        k_del: usize,
        k_prv: usize,
        epoch: &[u8],
        rng: &mut impl RngCore,
    ) -> Result<Self> {
        if s == 0
            || n == 0
            || !n.is_multiple_of(s)
            || k_del == 0
            || k_del > 128
            || k_prv > 128
            || epoch.is_empty()
        {
            return Err("invalid DARLT parameters".into());
        }
        let w = n / s;
        let mut prefix = b"DARLT-FC/setup/parameters".to_vec();
        frame(&mut prefix, epoch);
        for x in [n, s, k_max, k_del, k_prv] {
            prefix.extend((x as u64).to_be_bytes());
        }
        let base = |tag: &[u8]| hash_point(tag, &prefix);
        let bases = |tag: &[u8], count: usize| {
            (0..count)
                .map(|j| {
                    let mut label = tag.to_vec();
                    label.extend((j as u64).to_be_bytes());
                    base(&label)
                })
                .collect::<Vec<_>>()
        };
        let ghat = base(b"ghat");
        let srs = ReferenceString::new(w, s, k_max, ghat, rng)?;
        let fc = spseq_fc::Params::new(
            base(b"u"),
            base(b"h0"),
            bases(b"grant-bit", k_del),
            srs.lagrange[..w].to_vec(),
        )?;
        let mut query_bases = BTreeMap::new();
        let mut query_size = 1;
        loop {
            query_bases.insert(query_size, srs.query_basis(query_size)?);
            if query_size == srs.k_padded {
                break;
            }
            query_size *= 2;
        }
        let mut pp = Self {
            n,
            s,
            w,
            k_max,
            k_del,
            k_prv,
            srs,
            fc,
            ghat,
            h: base(b"h"),
            hdel: base(b"hdel"),
            adel: bases(b"adel", k_del),
            hprv: base(b"hprv"),
            bprv: bases(b"bprv", k_prv),
            grant_bases: bases(b"authorization", k_del),
            query_bases,
            id: [0; 32],
        };
        pp.id = Sha256::digest(pp.encode()).into();
        Ok(pp)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = b"DARLT/parameters/encoding".to_vec();
        for x in [
            self.n,
            self.s,
            self.w,
            self.k_max,
            self.k_del,
            self.k_prv,
            self.srs.domain.size,
            self.srs.n,
            self.srs.degree,
        ] {
            b.extend((x as u64).to_be_bytes());
        }
        frame(&mut b, &self.fc.encode());
        points1(
            &mut b,
            &[
                self.ghat,
                self.h,
                self.hdel,
                self.hprv,
                self.srs.vanishing,
                self.srs.offset,
            ],
        );
        for x in [
            &self.adel,
            &self.bprv,
            &self.grant_bases,
            &self.srs.g1,
            &self.srs.lagrange,
        ] {
            points1(&mut b, x);
        }
        b.extend((self.srs.g2.len() as u64).to_be_bytes());
        for (i, g) in &self.srs.g2 {
            b.extend((*i as u64).to_be_bytes());
            b.extend(g.to_compressed());
        }
        for x in [&self.srs.k_hat, &self.srs.d_hat, &self.srs.o_hat] {
            points2(&mut b, x);
        }
        b.extend((self.query_bases.len() as u64).to_be_bytes());
        for (size, (bases, vanishing)) in &self.query_bases {
            b.extend((*size as u64).to_be_bytes());
            points1(&mut b, bases);
            b.extend(vanishing.to_compressed());
        }
        b
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn query_basis(&self, k: usize) -> Result<(Vec<G1>, G1)> {
        self.query_bases
            .get(&k)
            .cloned()
            .ok_or("query domain was not installed".into())
    }
}
#[derive(Clone, Debug)]
pub struct IssuerPublic {
    pub vk: Vec<G2>,
    pub metadata_keys: [G1; 2],
    pub key_proof: sigma::Proof,
}
#[derive(Clone, Debug)]
pub struct IssuerSecret {
    pub signing: spseq_fc::KeyPair,
    pub metadata_secrets: [S; 2],
}
impl IssuerPublic {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn material(&self) -> Vec<u8> {
        let mut b = vec![];
        points2(&mut b, &self.vk);
        points1(&mut b, &self.metadata_keys);
        b
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = self.material();
        frame(&mut b, &self.key_proof.encode());
        b
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn key_statement(ip: &IssuerPublic) -> Result<sigma::Statement> {
    if ip.vk.len() != 9
        || ip.vk.iter().any(|p| !valid2(*p, true))
        || ip.metadata_keys.iter().any(|p| !valid1(*p, true))
        || ip.metadata_keys[0] == ip.metadata_keys[1]
    {
        return Err("invalid issuer key".into());
    }
    let mut st = sigma::Statement::new(11);
    for (i, p) in ip.vk.iter().enumerate() {
        st.g2.push(sigma::Eq2 {
            target: *p,
            terms: vec![(i, G2::generator(), S::ONE)],
        });
    }
    for (i, p) in ip.metadata_keys.iter().enumerate() {
        st.g1.push(sigma::Eq1 {
            target: *p,
            terms: vec![(9 + i, G1::generator(), S::ONE)],
        });
    }
    Ok(st)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn keygen(
    pp: &PublicParameters,
    rng: &mut impl RngCore,
) -> Result<(IssuerPublic, IssuerSecret)> {
    let signing = spseq_fc::keygen(rng);
    let a = nonzero(rng);
    let b = loop {
        let b = nonzero(rng);
        if b != a {
            break b;
        }
    };
    let mut ip = IssuerPublic {
        vk: signing.vk.clone(),
        metadata_keys: [G1::generator() * a, G1::generator() * b],
        key_proof: sigma::Proof {
            c: S::ZERO,
            z: vec![],
            bits: vec![],
        },
    };
    let mut prefix = pp.id.to_vec();
    prefix.extend(ip.material());
    let mut witness = signing.sk.clone();
    witness.extend([a, b]);
    ip.key_proof = key_statement(&ip)?.prove(b"DARLT/IKeyGen/proof", &prefix, &witness, rng)?;
    Ok((
        ip,
        IssuerSecret {
            signing,
            metadata_secrets: [a, b],
        },
    ))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn install(pp: &PublicParameters, ip: &IssuerPublic) -> Result<()> {
    let _span = crate::darlt::instrumentation::span("key_proof_installation");
    let mut prefix = pp.id.to_vec();
    prefix.extend(ip.material());
    if !key_statement(ip)?.verify(b"DARLT/IKeyGen/proof", &prefix, &ip.key_proof) {
        return Err("issuer knowledge proof rejected".into());
    }
    Ok(())
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn prefix(pp: &PublicParameters, ip: &IssuerPublic) -> Vec<u8> {
    let mut b = pp.id.to_vec();
    b.extend(ip.encode());
    b
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn attribute_commitment(h: G1, bases: &[G1], r: S, values: &[S]) -> Result<G1> {
    if bases.len() != values.len() {
        return Err("attribute dimension".into());
    }
    let mut points = vec![h];
    points.extend(bases);
    let mut scal = vec![r];
    scal.extend(values);
    Ok(crate::ops::msm1(&points, &scal))
}
#[derive(Clone, Debug)]
pub struct DerivationKey {
    pub base: spseq_fc::Dk,
    pub kz: [G1; 2],
}
impl DerivationKey {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = self.base.encode();
        for p in self.kz {
            b.extend(p.to_compressed());
        }
        b
    }
}
#[derive(Clone, Debug)]
pub struct IssueRequest {
    pub pku: G1,
    pub q: [G1; 2],
    pub cdel: G1,
    pub cprv: G1,
    pub mdel: Vec<S>,
    pub mprv: Vec<S>,
    pub proof: sigma::Proof,
}
#[derive(Clone, Debug)]
pub struct IssueSecrets {
    pub sku: S,
    pub seeds: [Vec<S>; 2],
    pub rhos: [S; 2],
    pub rdel: S,
    pub rprv: S,
}
#[derive(Clone, Debug)]
pub struct IssueResponse {
    pub shares: [Vec<S>; 2],
    pub e: G1,
    pub signature: spseq_fc::Sig,
    pub dk: DerivationKey,
    pub metadata_proof: metadata::MetadataProof,
}
#[derive(Clone, Debug)]
pub struct Wallet {
    pub(crate) pp_id: [u8; 32],
    pub(crate) issuer_id: [u8; 32],
    pub(crate) parent: Vec<G1>,
    pub(crate) signature: spseq_fc::Sig,
    pub(crate) dk: DerivationKey,
    pub(crate) sku: S,
    pub(crate) seeds: [Vec<S>; 2],
    pub(crate) rhos: [S; 2],
    pub(crate) mdel: Vec<S>,
    pub(crate) mprv: Vec<S>,
    pub(crate) rdel: S,
    pub(crate) rprv: S,
    pub(crate) openings: BTreeMap<usize, [G2; 2]>,
}
impl IssueRequest {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn core(&self) -> Vec<u8> {
        let mut b = vec![];
        b.extend(self.pku.to_compressed());
        for p in self.q {
            b.extend(p.to_compressed());
        }
        b.extend(self.cdel.to_compressed());
        b.extend(self.cprv.to_compressed());
        scalars(&mut b, &self.mdel);
        scalars(&mut b, &self.mprv);
        b
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = self.core();
        frame(&mut b, &self.proof.encode());
        b
    }
}
impl IssueResponse {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = vec![];
        for v in &self.shares {
            scalars(&mut b, v);
        }
        b.extend(self.e.to_compressed());
        b.extend(self.signature.encode());
        frame(&mut b, &self.dk.encode());
        b.extend(self.metadata_proof.to_bytes());
        b
    }
}
impl Wallet {
    pub fn parent(&self) -> &[G1] {
        &self.parent
    }
    pub fn signature(&self) -> &spseq_fc::Sig {
        &self.signature
    }
    pub fn parent_opening_cache_len(&self) -> usize {
        self.openings.len()
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn id(&self) -> [u8; 32] {
        let mut b = vec![];
        points1(&mut b, &self.parent);
        b.extend(self.signature.encode());
        Sha256::digest(b).into()
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn parent_opening(&mut self, pp: &PublicParameters, b: usize) -> Result<[G2; 2]> {
        let _span = crate::darlt::instrumentation::span("parent_opening_cache_and_compute");
        if self.pp_id != pp.id {
            return Err("parent opening parameter binding".into());
        }
        if b >= pp.w {
            return Err("pool out of bounds".into());
        }
        if let Some(w) = self.openings.get(&b) {
            return Ok(*w);
        }
        let value = [
            pp.srs.parent_opening(b, &self.seeds[0], self.rhos[0])?,
            pp.srs.parent_opening(b, &self.seeds[1], self.rhos[1])?,
        ];
        self.openings.insert(b, value);
        Ok(value)
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn issue_statement(pp: &PublicParameters, q: &IssueRequest) -> Result<sigma::Statement> {
    issue_statement_core(pp, q, None)
}
fn issue_statement_core(
    pp: &PublicParameters,
    q: &IssueRequest,
    received: Option<&super::spend::ReceivedInputs>,
) -> Result<sigma::Statement> {
    let point = |p: G1| received.map_or_else(|| valid1(p, true), |_| p != G1::identity());
    if q.mdel.len() != pp.k_del
        || q.mprv.len() != pp.k_prv
        || !point(q.pku)
        || q.q.iter().any(|p| !point(*p))
        || !point(q.cdel)
        || !point(q.cprv)
    {
        return Err("bad issuance request".into());
    }
    let mut st = sigma::Statement::new(1 + 2 * (pp.w + 1) + 2);
    st.g1.push(sigma::Eq1 {
        target: q.pku,
        terms: vec![(0, G1::generator(), S::ONE)],
    });
    for d in 0..2 {
        let start = 1 + d * (pp.w + 1);
        let mut terms: Vec<_> = pp
            .fc
            .pools
            .iter()
            .enumerate()
            .map(|(b, p)| (start + b, *p, S::ONE))
            .collect();
        terms.push((start + pp.w, pp.srs.vanishing, S::ONE));
        st.g1.push(sigma::Eq1 {
            target: q.q[d],
            terms,
        });
    }
    let base = 1 + 2 * (pp.w + 1);
    for (index, c, h, bases, values) in [
        (base, q.cdel, pp.hdel, &pp.adel, &q.mdel),
        (base + 1, q.cprv, pp.hprv, &pp.bprv, &q.mprv),
    ] {
        st.g1.push(sigma::Eq1 {
            target: c - attribute_commitment(G1::identity(), bases, S::ZERO, values)?,
            terms: vec![(index, h, S::ONE)],
        });
    }
    Ok(st)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn issue_prefix(pp: &PublicParameters, ip: &IssuerPublic, q: &IssueRequest) -> Vec<u8> {
    let mut b = prefix(pp, ip);
    frame(&mut b, &q.core());
    b
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn prepare_request(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    sku: S,
    mdel: &[S],
    mprv: &[S],
    rng: &mut impl RngCore,
) -> Result<(IssueRequest, IssueSecrets)> {
    if sku == S::ZERO || mdel.len() != pp.k_del || mprv.len() != pp.k_prv {
        return Err("bad issuance input".into());
    }
    let sec = IssueSecrets {
        sku,
        seeds: [
            (0..pp.w).map(|_| S::random(&mut *rng)).collect(),
            (0..pp.w).map(|_| S::random(&mut *rng)).collect(),
        ],
        rhos: [S::random(&mut *rng), S::random(&mut *rng)],
        rdel: nonzero(rng),
        rprv: nonzero(rng),
    };
    let q = std::array::from_fn(|d| {
        let mut p = pp.fc.pools.clone();
        p.push(pp.srs.vanishing);
        let mut x = sec.seeds[d].clone();
        x.push(sec.rhos[d]);
        crate::ops::msm1(&p, &x)
    });
    let mut req = IssueRequest {
        pku: G1::generator() * sku,
        q,
        cdel: attribute_commitment(pp.hdel, &pp.adel, sec.rdel, mdel)?,
        cprv: attribute_commitment(pp.hprv, &pp.bprv, sec.rprv, mprv)?,
        mdel: mdel.to_vec(),
        mprv: mprv.to_vec(),
        proof: sigma::Proof {
            c: S::ZERO,
            z: vec![],
            bits: vec![],
        },
    };
    let mut witness = vec![sku];
    for d in 0..2 {
        witness.extend(&sec.seeds[d]);
        witness.push(sec.rhos[d]);
    }
    witness.extend([sec.rdel, sec.rprv]);
    req.proof = issue_statement(pp, &req)?.prove(
        b"DARLT/Issue/proof",
        &issue_prefix(pp, ip, &req),
        &witness,
        rng,
    )?;
    Ok((req, sec))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn verify_request(pp: &PublicParameters, ip: &IssuerPublic, q: &IssueRequest) -> bool {
    issue_statement(pp, q)
        .is_ok_and(|st| st.verify(b"DARLT/Issue/proof", &issue_prefix(pp, ip, q), &q.proof))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn request_r(pp: &PublicParameters, ip: &IssuerPublic, q: &IssueRequest) -> G1 {
    hash_point(b"DARLT/Issue/metadata-base", &issue_prefix(pp, ip, q))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn response_prefix(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    q: &IssueRequest,
    r: &IssueResponse,
    parent: &[G1],
) -> Vec<u8> {
    let mut b = issue_prefix(pp, ip, q);
    points1(&mut b, parent);
    b.extend(r.signature.encode());
    frame(&mut b, &r.dk.encode());
    for v in &r.shares {
        scalars(&mut b, v);
    }
    b
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn issue(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    sk: &IssuerSecret,
    q: &IssueRequest,
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<IssueResponse> {
    issue_core(pp, ip, sk, q, bit, rng, None)
}
pub(crate) fn issue_received_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    sk: &IssuerSecret,
    q: &ReceivedIssueRequest,
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<IssueResponse> {
    if !q.inputs.matches_parameters(&pp.id) {
        return Err("received issue request parameter binding".into());
    }
    issue_core(pp, ip, sk, &q.request, bit, rng, Some(&q.inputs))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn issue_core(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    sk: &IssuerSecret,
    q: &IssueRequest,
    bit: usize,
    rng: &mut impl RngCore,
    received: Option<&super::spend::ReceivedInputs>,
) -> Result<IssueResponse> {
    let request_valid = match received {
        Some(checked) => issue_statement_core(pp, q, Some(checked)).is_ok_and(|st| {
            st.verify_received(
                b"DARLT/Issue/proof",
                &issue_prefix(pp, ip, q),
                &q.proof,
                checked,
            )
        }),
        None => verify_request(pp, ip, q),
    };
    if bit > 1
        || !request_valid
        || sk.signing.vk != ip.vk
        || sk.metadata_secrets.map(|x| G1::generator() * x) != ip.metadata_keys
    {
        return Err("issuance rejected".into());
    }
    let shares: [Vec<S>; 2] = [
        (0..pp.w).map(|_| S::random(&mut *rng)).collect(),
        (0..pp.w).map(|_| S::random(&mut *rng)).collect(),
    ];
    let u: [G1; 2] = std::array::from_fn(|d| q.q[d] + crate::ops::msm1(&pp.fc.pools, &shares[d]));
    let r = request_r(pp, ip, q);
    let e = r * sk.metadata_secrets[bit];
    let parent = vec![pp.fc.u, u[0], u[1], q.pku, r, e, q.cdel, q.cprv];
    let y = nonzero(rng);
    let inv = y.invert().unwrap();
    let power = y * sk.signing.sk[8];
    let signature = spseq_fc::Sig {
        z: crate::ops::msm1(&parent, &sk.signing.sk[..8]) * y,
        y: G1::generator() * inv,
        yhat: G2::generator() * inv,
    };
    let dk = DerivationKey {
        base: spseq_fc::Dk {
            k0: pp.fc.h0 * power,
            ka: G1::generator() * power,
            attrs: pp.fc.attrs.iter().map(|p| *p * power).collect(),
            pools: pp.fc.pools.iter().map(|p| *p * power).collect(),
        },
        kz: [
            pp.srs.vanishing * (y * sk.signing.sk[1]),
            pp.srs.vanishing * (y * sk.signing.sk[2]),
        ],
    };
    let dummy = metadata::MetadataProof {
        c: S::ZERO,
        c0: S::ZERO,
        z: [S::ZERO; 2],
    };
    let mut out = IssueResponse {
        shares,
        e,
        signature,
        dk,
        metadata_proof: dummy,
    };
    out.metadata_proof = metadata::prove(
        rng,
        &response_prefix(pp, ip, q, &out, &parent),
        &metadata::MetadataStatement {
            keys: ip.metadata_keys,
            r,
            e,
        },
        bit,
        sk.metadata_secrets[bit],
    )
    .map_err(|e| format!("{e:?}"))?;
    Ok(out)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn valid_seed(z: S, s: usize) -> bool {
    z != S::ZERO && z.to_bytes_be() <= (-S::from(s as u64)).to_bytes_be()
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn accept(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    q: &IssueRequest,
    sec: &IssueSecrets,
    res: &IssueResponse,
    rng: &mut impl RngCore,
) -> Result<Wallet> {
    accept_core(pp, ip, q, sec, res, None, rng)
}
pub(crate) fn accept_received_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    q: &IssueRequest,
    sec: &IssueSecrets,
    res: &ReceivedIssueResponse,
    rng: &mut impl RngCore,
) -> Result<Wallet> {
    if !res.inputs.matches_parameters(&pp.id) {
        return Err("received issuance parameter binding".into());
    }
    accept_core(pp, ip, q, sec, &res.response, Some(&res.inputs), rng)
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn accept_core(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    q: &IssueRequest,
    sec: &IssueSecrets,
    res: &IssueResponse,
    received: Option<&super::spend::ReceivedInputs>,
    rng: &mut impl RngCore,
) -> Result<Wallet> {
    if !verify_request(pp, ip, q)
        || G1::generator() * sec.sku != q.pku
        || sec.seeds.iter().chain(&res.shares).any(|x| x.len() != pp.w)
    {
        return Err("issuance response dimensions".into());
    }
    let seeds: [Vec<S>; 2] = std::array::from_fn(|d| {
        sec.seeds[d]
            .iter()
            .zip(&res.shares[d])
            .map(|(x, y)| *x + y)
            .collect()
    });
    if seeds.iter().flatten().any(|z| !valid_seed(*z, pp.s)) {
        return Err("zero unit seed interval".into());
    }
    let u: [G1; 2] = std::array::from_fn(|d| {
        crate::ops::msm1(&pp.fc.pools, &seeds[d]) + pp.srs.vanishing * sec.rhos[d]
    });
    for (d, u) in u.iter().enumerate() {
        if *u != q.q[d] + crate::ops::msm1(&pp.fc.pools, &res.shares[d]) {
            return Err("table share mismatch".into());
        }
    }
    if attribute_commitment(pp.hdel, &pp.adel, sec.rdel, &q.mdel)? != q.cdel
        || attribute_commitment(pp.hprv, &pp.bprv, sec.rprv, &q.mprv)? != q.cprv
    {
        return Err("attribute opening".into());
    }
    let r = request_r(pp, ip, q);
    let parent = vec![pp.fc.u, u[0], u[1], q.pku, r, res.e, q.cdel, q.cprv];
    if !metadata::verify(
        &response_prefix(pp, ip, q, res, &parent),
        &metadata::MetadataStatement {
            keys: ip.metadata_keys,
            r,
            e: res.e,
        },
        &res.metadata_proof,
    ) {
        return Err("issuer metadata".into());
    }
    let mut equations = match received {
        Some(checked) => {
            spseq_fc::signature_equations_received(&ip.vk, &parent, &res.signature, checked)
        }
        None => spseq_fc::signature_equations(&pp.fc, &ip.vk, &parent, &res.signature),
    }
    .ok_or("issuer signature input")?;
    let dk = &res.dk.base;
    if dk.attrs.len() != pp.k_del || dk.pools.len() != pp.w {
        return Err("derivation key dimensions".into());
    }
    let mut pairs = vec![(dk.k0, pp.fc.h0, 8), (dk.ka, G1::generator(), 8)];
    pairs.extend(dk.attrs.iter().zip(&pp.fc.attrs).map(|(a, b)| (*a, *b, 8)));
    pairs.extend(dk.pools.iter().zip(&pp.fc.pools).map(|(a, b)| (*a, *b, 8)));
    pairs.extend([
        (res.dk.kz[0], pp.srs.vanishing, 1),
        (res.dk.kz[1], pp.srs.vanishing, 2),
    ]);
    // The complete response is encoded and every dynamic point checked before coins.
    let _fixed = res.encode();
    if pairs
        .iter()
        .any(|(a, _, _)| received.map_or_else(|| !valid1(*a, true), |_| *a == G1::identity()))
    {
        return Err("invalid derivation key point".into());
    }
    equations.extend(
        pairs
            .into_iter()
            .map(|(point, base, key)| vec![(point, res.signature.yhat), (-base, ip.vk[key])]),
    );
    let checked = match received {
        Some(checked) => verification::check_received(&equations, Mode::Randomized, rng, checked),
        None => verification::check(&equations, Mode::Randomized, rng),
    }?;
    if !checked.accepted {
        return Err("issuer signature/derivation key batch rejected".into());
    }
    Ok(Wallet {
        pp_id: pp.id,
        issuer_id: Sha256::digest(ip.encode()).into(),
        parent,
        signature: res.signature.clone(),
        dk: res.dk.clone(),
        sku: sec.sku,
        seeds,
        rhos: sec.rhos,
        mdel: q.mdel.clone(),
        mprv: q.mprv.clone(),
        rdel: sec.rdel,
        rprv: sec.rprv,
        openings: BTreeMap::new(),
    })
}

#[cfg(test)]
mod step_batch_tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    #[cfg(feature = "subgroup-audit")]
    fn check_received_slots(
        step: &str,
        wire: &[u8],
        fields: &[(&str, Vec<u8>)],
        audit: &crate::subgroup_audit::Audit,
        decode: impl Fn(&[u8]) -> bool,
    ) {
        let encoded = fields
            .iter()
            .map(|(kind, bytes)| {
                (
                    *kind,
                    bytes.iter().map(|b| format!("{b:02x}")).collect::<String>(),
                )
            })
            .collect::<Vec<_>>();
        let decodes = audit
            .events
            .iter()
            .filter(|event| event.operation == "checked_decode")
            .map(|event| (event.kind.as_str(), event.encoding_hex.clone()))
            .collect::<Vec<_>>();
        assert_eq!(
            decodes, encoded,
            "one checked parser primitive in exact wire slot order"
        );
        assert!(
            !audit
                .events
                .iter()
                .any(|event| event.operation != "checked_decode"
                    && encoded
                        .iter()
                        .any(|(kind, bytes)| *kind == event.kind && *bytes == event.encoding_hex)),
            "received point rechecked by native algorithm"
        );
        for (_, point) in fields {
            let offset = wire
                .windows(point.len())
                .position(|window| window == point)
                .unwrap();
            let mut malformed = wire.to_vec();
            malformed[offset..offset + point.len()].fill(0);
            assert!(!decode(&malformed), "received group slot must be checked");
        }
        println!(
            "R033_RECEIPT_SG {}",
            serde_json::json!({"step":step,"received_slots":fields.len(),"received_membership_checks_after_decode":0,"wire_slot_order_checked":true,"malformed_each_slot_rejected":true,"audit":audit,"formal_samples":0})
        );
    }

    struct Coins {
        rng: StdRng,
        bytes: usize,
    }
    impl Coins {
        fn new() -> Self {
            Self {
                rng: StdRng::seed_from_u64(33_021),
                bytes: 0,
            }
        }
    }
    impl RngCore for Coins {
        fn next_u32(&mut self) -> u32 {
            self.bytes += 4;
            self.rng.next_u32()
        }
        fn next_u64(&mut self) -> u64 {
            self.bytes += 8;
            self.rng.next_u64()
        }
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            self.bytes += dest.len();
            self.rng.fill_bytes(dest);
        }
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> std::result::Result<(), rand::Error> {
            self.bytes += dest.len();
            self.rng.try_fill_bytes(dest)
        }
    }
    #[cfg(feature = "subgroup-audit")]
    #[test]
    fn issuer_and_delegator_received_requests_check_each_group_slot_once() {
        use std::sync::Arc;
        let mut rng = StdRng::seed_from_u64(33_025);
        let pp = Arc::new(
            PublicParameters::setup(16, 4, 8, 3, 2, b"request provenance", &mut rng).unwrap(),
        );
        let (ip, sk) = keygen(&pp, &mut rng).unwrap();
        let ip = Arc::new(ip);
        let (request, sec) =
            prepare_request(&pp, &ip, S::from(7), &[S::ONE; 3], &[S::ONE; 2], &mut rng).unwrap();
        let wire = request.encode();
        let fields = [
            request.pku,
            request.q[0],
            request.q[1],
            request.cdel,
            request.cprv,
        ]
        .map(|point| ("G1", point.to_compressed().to_vec()));
        let mut raw_rng = rng.clone();
        let mut received_rng = rng.clone();
        let reference = issue(&pp, &ip, &sk, &request, 1, &mut raw_rng).unwrap();
        let (response, audit) = crate::subgroup_audit::collect(|| {
            let received = ReceivedIssueRequest::decode(&pp, &wire).unwrap();
            issue_received_installed(&pp, &ip, &sk, &received, 1, &mut received_rng).unwrap()
        });
        assert_eq!(
            response.encode(),
            reference.encode(),
            "original Sigma/FS/random tape unchanged"
        );
        check_received_slots("IssueIssuer", &wire, &fields, &audit, |bad| {
            ReceivedIssueRequest::decode(&pp, bad).is_ok()
        });
        let mut bad_request = request.clone();
        bad_request.proof.z[0] += S::ONE;
        let bad = ReceivedIssueRequest::decode(&pp, &bad_request.encode()).unwrap();
        assert!(issue_received_installed(&pp, &ip, &sk, &bad, 1, &mut rng).is_err());
        let mut wallet = accept(&pp, &ip, &request, &sec, &response, &mut rng).unwrap();
        let context = super::super::context::ProtocolContext::new(pp.clone(), ip.clone()).unwrap();
        // A zero Schnorr nonce produces a legitimate identity first message.
        // pka still has to be nonidentity. Preserve that native format rule.
        let recipient = spseq_fc::request_installed(
            &pp.id,
            &ip.encode(),
            b"recipient nonce zero",
            S::from(11),
            &mut rand::rngs::mock::StepRng::new(0, 0),
        )
        .unwrap();
        assert_eq!(recipient.proof.a, G1::identity());
        let wire = recipient.encode();
        let fields =
            [recipient.pka, recipient.proof.a].map(|point| ("G1", point.to_compressed().to_vec()));
        let mut other_wallet = wallet.clone();
        let mut raw_rng = rng.clone();
        let mut received_rng = rng.clone();
        let reference = context
            .fresh_holder_context()
            .delegate(
                &mut other_wallet,
                &recipient,
                &[0, 1],
                &[true; 3],
                &mut raw_rng,
            )
            .unwrap();
        let (delivery, audit) = crate::subgroup_audit::collect(|| {
            let received = ReceivedRecipientRequest::decode(pp.id, &wire).unwrap();
            context
                .fresh_holder_context()
                .delegate_received(
                    &mut wallet,
                    &received,
                    &[0, 1],
                    &[true; 3],
                    &mut received_rng,
                )
                .unwrap()
        });
        assert_eq!(
            delivery.delivery.encode(),
            reference.delivery.encode(),
            "recipient relation/FS/random tape unchanged"
        );
        check_received_slots("DelegateSend", &wire, &fields, &audit, |bad| {
            ReceivedRecipientRequest::decode(pp.id, bad).is_ok()
        });
        let mut bad_recipient = recipient.clone();
        bad_recipient.proof.z += S::ONE;
        let received = ReceivedRecipientRequest::decode(pp.id, &bad_recipient.encode()).unwrap();
        assert!(context
            .fresh_holder_context()
            .delegate_received(&mut wallet, &received, &[2], &[true; 3], &mut rng)
            .is_err());
    }
    #[test]
    fn issue_receive_batches_signature_and_every_derivation_equation_once() {
        let mut rng = StdRng::seed_from_u64(33_022);
        let pp = PublicParameters::setup(16, 4, 8, 3, 2, b"all issue equations", &mut rng).unwrap();
        let (ip, sk) = keygen(&pp, &mut rng).unwrap();
        let (request, sec) =
            prepare_request(&pp, &ip, S::from(7), &[S::ONE; 3], &[S::ONE; 2], &mut rng).unwrap();
        let response = issue(&pp, &ip, &sk, &request, 1, &mut rng).unwrap();
        let received_response = ReceivedIssueResponse::decode(&pp, &response.encode()).unwrap();
        let mut coins = Coins::new();
        crate::ops::reset();
        let wallet =
            accept_received_installed(&pp, &ip, &request, &sec, &received_response, &mut coins)
                .unwrap();
        let counts = crate::ops::stop();
        let equations = 2 + 2 + pp.k_del + pp.w + 2;
        println!(
            "R033_STEP_BATCH {}",
            serde_json::json!({"step":"IssueReceive","coefficient_bytes_observed":coins.bytes,"coefficients_observed":coins.bytes/16,"counts":counts,"formal_samples":0})
        );
        assert_eq!(coins.bytes, 16 * equations);
        if cfg!(feature = "op-counts") {
            assert_eq!(counts.final_exponentiations, 1);
        }
        #[cfg(feature = "subgroup-audit")]
        {
            let wire = response.encode();
            let mut fields = vec![
                ("G1", response.e.to_compressed().to_vec()),
                ("G1", response.signature.z.to_compressed().to_vec()),
                ("G1", response.signature.y.to_compressed().to_vec()),
                ("G2", response.signature.yhat.to_compressed().to_vec()),
                ("G1", response.dk.base.k0.to_compressed().to_vec()),
                ("G1", response.dk.base.ka.to_compressed().to_vec()),
            ];
            fields.extend(
                response
                    .dk
                    .base
                    .attrs
                    .iter()
                    .chain(&response.dk.base.pools)
                    .chain(&response.dk.kz)
                    .map(|point| ("G1", point.to_compressed().to_vec())),
            );
            let (accepted, audit) = crate::subgroup_audit::collect(|| {
                let received = ReceivedIssueResponse::decode(&pp, &wire).unwrap();
                accept_received_installed(&pp, &ip, &request, &sec, &received, &mut Coins::new())
            });
            assert_eq!(accepted.unwrap().id(), wallet.id());
            check_received_slots("IssueReceive", &wire, &fields, &audit, |bad| {
                ReceivedIssueResponse::decode(&pp, bad).is_ok()
            });
        }
        // Reprove only the unchanged native metadata statement after each
        // malformed issuer algebra. This isolates the pairing check instead of
        // relying on the transcript-binding OR proof to reject first.
        for index in 0..equations {
            let mut bad = response.clone();
            match index {
                0 => bad.signature.z += G1::generator(),
                1 => bad.signature.y += G1::generator(),
                2 => bad.dk.base.k0 += G1::generator(),
                3 => bad.dk.base.ka += G1::generator(),
                n if n < 4 + pp.k_del => bad.dk.base.attrs[n - 4] += G1::generator(),
                n if n < 4 + pp.k_del + pp.w => {
                    bad.dk.base.pools[n - 4 - pp.k_del] += G1::generator()
                }
                n => bad.dk.kz[n - 4 - pp.k_del - pp.w] += G1::generator(),
            }
            let r = wallet.parent[4];
            bad.metadata_proof = metadata::prove(
                &mut rng,
                &response_prefix(&pp, &ip, &request, &bad, &wallet.parent),
                &metadata::MetadataStatement {
                    keys: ip.metadata_keys,
                    r,
                    e: bad.e,
                },
                1,
                sk.metadata_secrets[1],
            )
            .unwrap();
            let mut coins = Coins::new();
            let received = ReceivedIssueResponse::decode(&pp, &bad.encode()).unwrap();
            assert!(
                accept_received_installed(&pp, &ip, &request, &sec, &received, &mut coins).is_err(),
                "equation {index}"
            );
            assert_eq!(coins.bytes, 16 * equations, "equation {index}");
        }
    }

    #[test]
    fn delegate_receive_batches_both_signatures_and_all_pool_columns() {
        let mut rng = StdRng::seed_from_u64(33_023);
        let pp =
            PublicParameters::setup(16, 4, 8, 3, 2, b"all receive equations", &mut rng).unwrap();
        let (ip, sk) = keygen(&pp, &mut rng).unwrap();
        let (request, sec) =
            prepare_request(&pp, &ip, S::from(7), &[S::ONE; 3], &[S::ONE; 2], &mut rng).unwrap();
        let response = issue(&pp, &ip, &sk, &request, 1, &mut rng).unwrap();
        let mut wallet = accept(&pp, &ip, &request, &sec, &response, &mut rng).unwrap();
        for gamma in [1, 2, 4] {
            let pools = (0..gamma).collect::<Vec<_>>();
            let delivery = derive(
                &pp,
                &mut wallet,
                G1::generator() * S::from(11),
                &pools,
                &[true; 3],
                &mut rng,
            )
            .unwrap();
            let mut coins = Coins::new();
            let received_delivery = ReceivedDelivery::decode(&pp, &delivery.encode()).unwrap();
            crate::ops::reset();
            complete_received_installed(
                &pp,
                &ip,
                &received_delivery,
                S::from(11),
                None,
                Mode::Randomized,
                &mut coins,
            )
            .unwrap();
            let counts = crate::ops::stop();
            println!(
                "R033_STEP_BATCH {}",
                serde_json::json!({"step":"DelegateReceive","gamma":gamma,"coefficient_bytes_observed":coins.bytes,"coefficients_observed":coins.bytes/16,"counts":counts,"formal_samples":0})
            );
            assert_eq!(coins.bytes, 16 * (2 + 2 * gamma));
            if cfg!(feature = "op-counts") {
                assert_eq!(counts.final_exponentiations, 1);
            }
            #[cfg(feature = "subgroup-audit")]
            {
                let wire = delivery.encode();
                let mut fields = delivery
                    .parent
                    .iter()
                    .copied()
                    .chain([delivery.c, delivery.v, delivery.w, delivery.y])
                    .map(|point| ("G1", point.to_compressed().to_vec()))
                    .collect::<Vec<_>>();
                fields.push(("G2", delivery.yhat.to_compressed().to_vec()));
                fields.extend(
                    delivery
                        .pools
                        .iter()
                        .flat_map(|pool| pool.openings)
                        .map(|point| ("G2", point.to_compressed().to_vec())),
                );
                let (accepted, audit) = crate::subgroup_audit::collect(|| {
                    let received = ReceivedDelivery::decode(&pp, &wire).unwrap();
                    complete_received_installed(
                        &pp,
                        &ip,
                        &received,
                        S::from(11),
                        None,
                        Mode::Randomized,
                        &mut Coins::new(),
                    )
                });
                assert!(accepted.is_ok());
                check_received_slots(
                    &format!("DelegateReceive/Gamma{gamma}"),
                    &wire,
                    &fields,
                    &audit,
                    |bad| ReceivedDelivery::decode(&pp, bad).is_ok(),
                );
            }
            complete_installed(
                &pp,
                &ip,
                &delivery,
                S::from(11),
                None,
                Mode::Specification,
                &mut rng,
            )
            .unwrap();
            for index in 0..2 + 2 * gamma {
                let mut bad = delivery.clone();
                match index {
                    0 => bad.w += G1::generator(),
                    1 => bad.y += G1::generator(),
                    n => bad.pools[(n - 2) / 2].openings[(n - 2) % 2] += G2::generator(),
                }
                let mut coins = Coins::new();
                let received = ReceivedDelivery::decode(&pp, &bad.encode()).unwrap();
                assert!(
                    complete_received_installed(
                        &pp,
                        &ip,
                        &received,
                        S::from(11),
                        None,
                        Mode::Randomized,
                        &mut coins
                    )
                    .is_err(),
                    "gamma {gamma} equation {index}"
                );
                assert_eq!(coins.bytes, 16 * (2 + 2 * gamma));
            }
        }
    }
}
#[derive(Clone, Debug)]
pub struct OwnerOpening {
    pub mprv: Vec<S>,
    pub rprv: S,
}
#[derive(Clone, Debug)]
pub struct PoolBundle {
    pub pool: usize,
    pub seeds: [S; 2],
    pub openings: [G2; 2],
}
#[derive(Clone, Debug)]
pub struct Delivery {
    pub parent: Vec<G1>,
    pub c: G1,
    pub r: S,
    pub gamma: Vec<usize>,
    pub delta: Vec<bool>,
    pub v: G1,
    pub w: G1,
    pub y: G1,
    pub yhat: G2,
    pub rdel: S,
    pub mdel: Vec<S>,
    pub pools: Vec<PoolBundle>,
}
impl Delivery {
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut b = vec![];
        points1(&mut b, &self.parent);
        for p in [self.c, self.v, self.w, self.y] {
            b.extend(p.to_compressed());
        }
        b.extend(self.yhat.to_compressed());
        b.extend(self.r.to_bytes_be());
        b.extend(self.rdel.to_bytes_be());
        scalars(&mut b, &self.mdel);
        for x in &self.pools {
            b.extend((x.pool as u64).to_be_bytes());
            for z in x.seeds {
                b.extend(z.to_bytes_be());
            }
            for w in x.openings {
                b.extend(w.to_compressed());
            }
        }
        b.extend(self.delta.iter().map(|b| u8::from(*b)));
        b
    }
}
#[derive(Clone, Debug)]
pub struct Holder {
    pub(crate) pp_id: [u8; 32],
    pub(crate) issuer_id: [u8; 32],
    pub(crate) parent: Vec<G1>,
    pub(crate) signature: spseq_fc::Sig,
    pub(crate) c: G1,
    pub(crate) r: S,
    pub(crate) ska: S,
    pub(crate) scope: G1,
    pub(crate) gamma: Vec<usize>,
    pub(crate) delta: Vec<bool>,
    pub(crate) mdel: Vec<S>,
    pub(crate) rdel: S,
    pub(crate) owner: Option<OwnerOpening>,
    pub(crate) pools: Vec<PoolBundle>,
    pub(crate) scope_openings: BTreeMap<usize, G2>,
}
impl Holder {
    pub fn gamma(&self) -> &[usize] {
        &self.gamma
    }
    pub fn scope(&self) -> G1 {
        self.scope
    }
    pub fn signature(&self) -> &spseq_fc::Sig {
        &self.signature
    }
    pub fn scope_opening_cache_len(&self) -> usize {
        self.scope_openings.len()
    }
    pub fn is_owner(&self) -> bool {
        self.owner.is_some()
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn message(&self) -> Vec<G1> {
        let mut b = self.parent.clone();
        b.push(self.c);
        b
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn pool(&self, b: usize) -> Result<&PoolBundle> {
        self.pools
            .iter()
            .find(|p| p.pool == b)
            .ok_or("unit outside child scope".into())
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn scope_opening(&mut self, pp: &PublicParameters, b: usize) -> Result<G2> {
        let _span = crate::darlt::instrumentation::span("scope_opening_cache_and_compute");
        if self.pp_id != pp.id {
            return Err("scope opening parameter binding".into());
        }
        if let Some(w) = self.scope_openings.get(&b) {
            return Ok(*w);
        }
        let w = pp.srs.scope_opening(b, &self.gamma)?;
        self.scope_openings.insert(b, w);
        Ok(w)
    }
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(super) fn scope_check(pp: &PublicParameters, gamma: &[usize], delta: &[bool]) -> Result<()> {
    if gamma.is_empty()
        || gamma.iter().any(|b| *b >= pp.w)
        || gamma.iter().copied().collect::<BTreeSet<_>>().len() != gamma.len()
        || delta.len() != pp.k_del
        || !delta[0]
    {
        return Err("invalid child scope or grant".into());
    }
    Ok(())
}

/// The original authorization relation after fixed bases were installed.
/// Only the chosen scope and recipient require dynamic checks.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn authorization_core(
    pp: &PublicParameters,
    recipient: G1,
    r: S,
    gamma: &[usize],
    delta: &[bool],
    received: Option<&super::spend::ReceivedInputs>,
) -> Result<G1> {
    scope_check(pp, gamma, delta)?;
    if !received.map_or_else(|| valid1(recipient, true), |_| recipient != G1::identity()) {
        return Err("invalid child recipient".into());
    }
    let scope = crate::ops::msm1(
        &gamma.iter().map(|&b| pp.fc.pools[b]).collect::<Vec<_>>(),
        &vec![S::ONE; gamma.len()],
    );
    if scope == G1::identity() {
        return Err("identity child scope".into());
    }
    let mut bases = vec![pp.fc.h0, recipient, scope];
    let mut values = vec![r, S::ONE, S::ONE];
    for (base, selected) in pp.fc.attrs.iter().zip(delta) {
        if *selected {
            bases.push(*base);
            values.push(S::ONE);
        }
    }
    Ok(crate::ops::msm1(&bases, &values))
}
/// Raw cryptographic derivation; the stateful facade must allocate before calling.
/// Crate-only so application callers cannot bypass the allocation table.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn derive(
    pp: &PublicParameters,
    wallet: &mut Wallet,
    recipient: G1,
    gamma: &[usize],
    delta: &[bool],
    rng: &mut impl RngCore,
) -> Result<Delivery> {
    derive_core(pp, wallet, recipient, gamma, delta, rng, None)
}
pub(super) fn derive_received(
    pp: &PublicParameters,
    wallet: &mut Wallet,
    recipient: G1,
    gamma: &[usize],
    delta: &[bool],
    rng: &mut impl RngCore,
    received: &super::spend::ReceivedInputs,
) -> Result<Delivery> {
    if !received.matches_parameters(&pp.id) {
        return Err("recipient parameter binding".into());
    }
    derive_core(pp, wallet, recipient, gamma, delta, rng, Some(received))
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn derive_core(
    pp: &PublicParameters,
    wallet: &mut Wallet,
    recipient: G1,
    gamma: &[usize],
    delta: &[bool],
    rng: &mut impl RngCore,
    received: Option<&super::spend::ReceivedInputs>,
) -> Result<Delivery> {
    if wallet.pp_id != pp.id {
        return Err("wallet parameter binding".into());
    }
    scope_check(pp, gamma, delta)?;
    if !received.map_or_else(|| valid1(recipient, true), |_| recipient != G1::identity()) {
        return Err("invalid recipient".into());
    }
    let mut pools = vec![];
    for &b in gamma {
        let openings = wallet.parent_opening(pp, b)?;
        pools.push(PoolBundle {
            pool: b,
            seeds: [wallet.seeds[0][b], wallet.seeds[1][b]],
            openings,
        });
    }
    let eps = [S::random(&mut *rng), S::random(&mut *rng)];
    let mut parent = wallet.parent.clone();
    for d in 0..2 {
        parent[1 + d] += pp.srs.vanishing * eps[d];
        for p in &mut pools {
            p.openings[d] += pp.srs.k_hat[p.pool] * eps[d];
        }
    }
    let (r, c) = loop {
        let r = S::random(&mut *rng);
        let c = authorization_core(pp, recipient, r, gamma, delta, received)?;
        if c != G1::identity() {
            break (r, c);
        }
    };
    let t = S::random(&mut *rng);
    let theta = nonzero(rng);
    let reciprocal = theta.invert().unwrap();
    let mut points = vec![
        wallet.signature.z,
        wallet.dk.kz[0],
        wallet.dk.kz[1],
        wallet.dk.base.k0,
    ];
    let mut coeff = vec![S::ONE, eps[0], eps[1], r];
    for &b in gamma {
        points.push(wallet.dk.base.pools[b]);
        coeff.push(S::ONE);
    }
    for (p, bit) in wallet.dk.base.attrs.iter().zip(delta) {
        if *bit {
            points.push(*p);
            coeff.push(S::ONE);
        }
    }
    let v = crate::ops::msm1(&[wallet.dk.base.ka, G1::generator()], &[theta, t]);
    let w = crate::ops::msm1(
        &[crate::ops::msm1(&points, &coeff), recipient],
        &[theta, -t],
    );
    Ok(Delivery {
        parent,
        c,
        r,
        gamma: gamma.to_vec(),
        delta: delta.to_vec(),
        v,
        w,
        y: wallet.signature.y * reciprocal,
        yhat: wallet.signature.yhat * reciprocal,
        rdel: wallet.rdel,
        mdel: wallet.mdel.clone(),
        pools,
    })
}
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn complete(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    d: &Delivery,
    ska: S,
    owner: Option<OwnerOpening>,
    mode: Mode,
    rng: &mut impl RngCore,
) -> Result<Holder> {
    if !spseq_fc::validate_instance(&pp.fc, &ip.vk) {
        return Err("signature instance rejected".into());
    }
    install(pp, ip)?;
    complete_installed(pp, ip, d, ska, owner, mode, rng)
}

#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn complete_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    d: &Delivery,
    ska: S,
    owner: Option<OwnerOpening>,
    mode: Mode,
    rng: &mut impl RngCore,
) -> Result<Holder> {
    complete_core(pp, ip, d, ska, owner, mode, rng, None)
}
pub(crate) fn complete_received_installed(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    d: &ReceivedDelivery,
    ska: S,
    owner: Option<OwnerOpening>,
    mode: Mode,
    rng: &mut impl RngCore,
) -> Result<Holder> {
    if !d.inputs.matches_parameters(&pp.id) {
        return Err("received delivery parameter binding".into());
    }
    complete_core(pp, ip, &d.delivery, ska, owner, mode, rng, Some(&d.inputs))
}
#[allow(clippy::too_many_arguments)]
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
fn complete_core(
    pp: &PublicParameters,
    ip: &IssuerPublic,
    d: &Delivery,
    ska: S,
    owner: Option<OwnerOpening>,
    mode: Mode,
    rng: &mut impl RngCore,
    received: Option<&super::spend::ReceivedInputs>,
) -> Result<Holder> {
    scope_check(pp, &d.gamma, &d.delta)?;
    let point1 = |p: G1, nonzero: bool| {
        received.map_or_else(|| valid1(p, nonzero), |_| !nonzero || p != G1::identity())
    };
    let point2 = |p: G2, nonzero: bool| {
        received.map_or_else(|| valid2(p, nonzero), |_| !nonzero || p != G2::identity())
    };
    if ska == S::ZERO
        || d.parent.len() != 8
        || d.mdel.len() != pp.k_del
        || d.pools.len() != d.gamma.len()
        || d.parent.iter().any(|point| !point1(*point, true))
        || !point1(d.c, true)
        || !point1(d.v, false)
        || !point1(d.w, false)
        || !point1(d.y, true)
        || !point2(d.yhat, true)
    {
        return Err("invalid delivery".into());
    }
    // Fix and validate the complete response, including advice that does
    // not occur in the signature equations, before drawing any verifier coins.
    let _fixed = d.encode();
    for (&b, p) in d.gamma.iter().zip(&d.pools) {
        if b != p.pool
            || p.seeds.iter().any(|z| !valid_seed(*z, pp.s))
            || p.openings.iter().any(|w| !point2(*w, false))
        {
            return Err("child advice rejected".into());
        }
    }
    let recipient = G1::generator() * ska;
    if authorization_core(pp, recipient, d.r, &d.gamma, &d.delta, received)? != d.c
        || attribute_commitment(pp.hdel, &pp.adel, d.rdel, &d.mdel)? != d.parent[6]
    {
        return Err("child authorization/opening rejected".into());
    }
    if let Some(o) = &owner {
        if recipient != d.parent[3]
            || attribute_commitment(pp.hprv, &pp.bprv, o.rprv, &o.mprv)? != d.parent[7]
        {
            return Err("owner opening rejected".into());
        }
    }
    let signature = spseq_fc::Sig {
        z: d.w + d.v * ska,
        y: d.y,
        yhat: d.yhat,
    };
    let mut message = d.parent.clone();
    message.push(d.c);
    let mut equations = match received {
        Some(checked) => {
            spseq_fc::signature_equations_received(&ip.vk, &message, &signature, checked)
        }
        None => spseq_fc::signature_equations_installed(&ip.vk, &message, &signature),
    }
    .ok_or("invalid child signature input")?;
    for p in &d.pools {
        for dcol in 0..2 {
            equations.push(vec![
                (d.parent[1 + dcol] - pp.ghat * p.seeds[dcol], pp.srs.g2[&0]),
                (-pp.srs.g1[1], p.openings[dcol]),
                (pp.ghat * pp.srs.domain.elements[p.pool], p.openings[dcol]),
            ]);
        }
    }
    let combine = |weights: &[S]| {
        let mut combined = verification::combine_equations(&equations[..2], &weights[..2]);
        let mut bases = vec![];
        let mut coeff = vec![];
        let mut witnesses = vec![];
        let mut weighted = vec![];
        for (j, p) in d.pools.iter().enumerate() {
            for dcol in 0..2 {
                let a = weights[2 + 2 * j + dcol];
                bases.push(d.parent[1 + dcol] - pp.ghat * p.seeds[dcol]);
                coeff.push(a);
                witnesses.push(p.openings[dcol]);
                weighted.push(a * pp.srs.domain.elements[p.pool]);
            }
        }
        combined.extend([
            (crate::ops::msm1(&bases, &coeff), pp.srs.g2[&0]),
            (-pp.srs.g1[1], crate::ops::msm2(&witnesses, &coeff)),
            (pp.ghat, crate::ops::msm2(&witnesses, &weighted)),
        ]);
        combined
    };
    let checked = match received {
        Some(checked) => {
            verification::check_with_combiner_received(&equations, mode, rng, checked, combine)
        }
        None => verification::check_with_combiner(&equations, mode, rng, combine),
    }?;
    if !checked.accepted {
        return Err("child signature/opening batch rejected".into());
    }
    Ok(Holder {
        pp_id: pp.id,
        issuer_id: Sha256::digest(ip.encode()).into(),
        parent: d.parent.clone(),
        signature,
        c: d.c,
        r: d.r,
        ska,
        scope: d.gamma.iter().map(|b| pp.fc.pools[*b]).sum(),
        gamma: d.gamma.clone(),
        delta: d.delta.clone(),
        mdel: d.mdel.clone(),
        rdel: d.rdel,
        owner,
        pools: d.pools.clone(),
        scope_openings: BTreeMap::new(),
    })
}
/// Local explicit self derivation: no signature verification, pairing, or message.
/// The parent was accepted once; its component-wise algebra constructs the child.
#[cfg(test)]
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(crate) fn self_derive(
    pp: &PublicParameters,
    wallet: &mut Wallet,
    gamma: &[usize],
    rng: &mut impl RngCore,
) -> Result<Holder> {
    let delta = vec![true; pp.k_del];
    let ska = wallet.sku;
    let d = derive(pp, wallet, G1::generator() * ska, gamma, &delta, rng)?;
    Ok(local_child(pp, wallet, &d))
}

/// Complete only our own freshly constructed or locally cached delivery.
/// Remote deliveries always go through `complete` and its full checks.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub(super) fn local_child(pp: &PublicParameters, wallet: &Wallet, d: &Delivery) -> Holder {
    let ska = wallet.sku;
    Holder {
        pp_id: wallet.pp_id,
        issuer_id: wallet.issuer_id,
        parent: d.parent.clone(),
        signature: spseq_fc::Sig {
            z: d.w + d.v * ska,
            y: d.y,
            yhat: d.yhat,
        },
        c: d.c,
        r: d.r,
        ska,
        scope: d.gamma.iter().map(|b| pp.fc.pools[*b]).sum(),
        gamma: d.gamma.clone(),
        delta: d.delta.clone(),
        mdel: d.mdel.clone(),
        rdel: d.rdel,
        owner: Some(OwnerOpening {
            mprv: wallet.mprv.clone(),
            rprv: wallet.rprv,
        }),
        pools: d.pools.clone(),
        scope_openings: BTreeMap::new(),
    }
}

impl Delivery {
    /// Canonical decoding of the existing DARLT delivery encoding. The pool
    /// count follows from the fixed-width pool records and installed schema;
    /// Gamma is exactly the ordered pool indices, not a second implicit input.
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn decode(pp: &PublicParameters, bytes: &[u8]) -> Result<Self> {
        let _span = crate::darlt::instrumentation::span("strict_decoding");
        struct Reader<'a> {
            bytes: &'a [u8],
            offset: usize,
        }
        impl<'a> Reader<'a> {
            #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
            fn take(&mut self, n: usize) -> Result<&'a [u8]> {
                let end = self
                    .offset
                    .checked_add(n)
                    .ok_or("delivery length overflow")?;
                let out = self
                    .bytes
                    .get(self.offset..end)
                    .ok_or("truncated delivery")?;
                self.offset = end;
                Ok(out)
            }
            #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
            fn number(&mut self) -> Result<usize> {
                usize::try_from(u64::from_be_bytes(self.take(8)?.try_into().unwrap()))
                    .map_err(|_| "delivery number overflow".into())
            }
            #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
            fn g1(&mut self) -> Result<G1> {
                let _span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
                let raw: [u8; 48] = self.take(48)?.try_into().unwrap();
                crate::subgroup_audit::decode("G1", &raw, "darlt/delivery/G1");
                Option::<blstrs::G1Affine>::from(blstrs::G1Affine::from_compressed(&raw))
                    .map(G1::from)
                    .ok_or("invalid delivery G1 encoding/subgroup".into())
            }
            #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
            fn g2(&mut self) -> Result<G2> {
                let _span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
                let raw: [u8; 96] = self.take(96)?.try_into().unwrap();
                crate::subgroup_audit::decode("G2", &raw, "darlt/delivery/G2");
                Option::<blstrs::G2Affine>::from(blstrs::G2Affine::from_compressed(&raw))
                    .map(G2::from)
                    .ok_or("invalid delivery G2 encoding/subgroup".into())
            }
            #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
            fn scalar(&mut self) -> Result<S> {
                let raw: [u8; 32] = self.take(32)?.try_into().unwrap();
                Option::<S>::from(S::from_bytes_be(&raw))
                    .ok_or("noncanonical delivery scalar".into())
            }
        }
        let mut reader = Reader { bytes, offset: 0 };
        if reader.number()? != 8 {
            return Err("invalid delivery parent dimension".into());
        }
        let parent = (0..8).map(|_| reader.g1()).collect::<Result<Vec<_>>>()?;
        let c = reader.g1()?;
        let v = reader.g1()?;
        let w = reader.g1()?;
        let y = reader.g1()?;
        let yhat = reader.g2()?;
        let r = reader.scalar()?;
        let rdel = reader.scalar()?;
        if reader.number()? != pp.k_del {
            return Err("invalid delivery attribute dimension".into());
        }
        let mdel = (0..pp.k_del)
            .map(|_| reader.scalar())
            .collect::<Result<Vec<_>>>()?;
        let remaining = bytes.len() - reader.offset;
        let pool_bytes = remaining
            .checked_sub(pp.k_del)
            .ok_or("truncated delivery scope")?;
        if !pool_bytes.is_multiple_of(264) || pool_bytes == 0 || pool_bytes / 264 > pp.w {
            return Err("invalid delivery pool record dimension".into());
        }
        let mut pools = Vec::with_capacity(pool_bytes / 264);
        for _ in 0..pool_bytes / 264 {
            pools.push(PoolBundle {
                pool: reader.number()?,
                seeds: [reader.scalar()?, reader.scalar()?],
                openings: [reader.g2()?, reader.g2()?],
            });
        }
        let delta = reader
            .take(pp.k_del)?
            .iter()
            .map(|byte| match byte {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err("noncanonical delivery grant bit".into()),
            })
            .collect::<Result<Vec<_>>>()?;
        let gamma = pools.iter().map(|p| p.pool).collect();
        let delivery = Self {
            parent,
            c,
            r,
            gamma,
            delta,
            v,
            w,
            y,
            yhat,
            rdel,
            mdel,
            pools,
        };
        scope_check(pp, &delivery.gamma, &delivery.delta)?;
        if reader.offset != bytes.len() || delivery.encode() != bytes {
            return Err("noncanonical delivery".into());
        }
        Ok(delivery)
    }
}
