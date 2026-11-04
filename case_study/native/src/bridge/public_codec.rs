//! Codec for public verifier parameters.
use super::{err, hex, s, unhex, Result, G1, S};
use baseline_core::{sma2rt as sma, sma2rt_proof};
use blstrs::G2Projective as G2;
use darlt_spseq_fc::{
    darlt::{
        context::ProtocolContext,
        params::ReferenceString,
        protocol::{IssuerPublic, PublicParameters},
        sigma,
        state::request_hash,
    },
    polynomial::Domain,
    spseq_fc,
};
use ff::Field;
use serde_json::{json, Value};
use std::{collections::BTreeMap, sync::Arc};

fn n(v: &Value, key: &str) -> Result<usize> {
    v[key]
        .as_u64()
        .and_then(|x| usize::try_from(x).ok())
        .filter(|x| *x <= 16384)
        .ok_or_else(|| format!("public {key} integer"))
}
fn bytes<const N: usize>(v: &Value) -> Result<[u8; N]> {
    unhex(v.as_str().ok_or("public canonical hex missing")?)?
        .try_into()
        .map_err(|_| "public canonical encoding length".into())
}
fn p1(v: &Value) -> Result<G1> {
    Option::<G1>::from(G1::from_compressed(&bytes::<48>(v)?))
        .ok_or("public G1 strict decoding".into())
}
fn p2(v: &Value) -> Result<G2> {
    Option::<G2>::from(G2::from_compressed(&bytes::<96>(v)?))
        .ok_or("public G2 strict decoding".into())
}
fn scalar(v: &Value) -> Result<S> {
    Option::<S>::from(S::from_bytes_be(&bytes::<32>(v)?))
        .ok_or("public scalar strict decoding".into())
}
fn vector<T>(v: &Value, decode: fn(&Value) -> Result<T>) -> Result<Vec<T>> {
    let a = v
        .as_array()
        .filter(|a| a.len() <= 16384)
        .ok_or("public vector bound")?;
    a.iter().map(decode).collect()
}
fn e1(x: G1) -> String {
    hex(&x.to_compressed())
}
fn e2(x: G2) -> String {
    hex(&x.to_compressed())
}
fn es(x: S) -> String {
    hex(&x.to_bytes_be())
}
fn ev1(x: &[G1]) -> Vec<String> {
    x.iter().copied().map(e1).collect()
}
fn ev2(x: &[G2]) -> Vec<String> {
    x.iter().copied().map(e2).collect()
}
fn evs(x: &[S]) -> Vec<String> {
    x.iter().copied().map(es).collect()
}

pub(super) fn digest(material: &Value) -> Result<String> {
    Ok(hex(&request_hash(
        &serde_json::to_vec(material).map_err(err)?,
    )))
}

pub(super) fn darlt_export(pp: &PublicParameters, ip: &IssuerPublic) -> Value {
    let r = &pp.srs;
    json!({
        "public_parameters": {
            "n":pp.n,"s":pp.s,"w":pp.w,"k_max":pp.k_max,"k_del":pp.k_del,"k_prv":pp.k_prv,"id":hex(&pp.id),
            "srs": {"domain_size":r.domain.size,"degree":r.degree,"n":r.n,"w":r.w,"s":r.s,"k_max":r.k_max,"k_padded":r.k_padded,
                "g1":ev1(&r.g1),"g2":r.g2.iter().map(|(i,x)|json!([i,e2(*x)])).collect::<Vec<_>>(),
                "lagrange":ev1(&r.lagrange),"vanishing":e1(r.vanishing),"k_hat":ev2(&r.k_hat),"d_hat":ev2(&r.d_hat),"o_hat":ev2(&r.o_hat),"offset":e1(r.offset)},
            "fc":{"u":e1(pp.fc.u),"h0":e1(pp.fc.h0),"attrs":ev1(&pp.fc.attrs),"pools":ev1(&pp.fc.pools)},
            "ghat":e1(pp.ghat),"h":e1(pp.h),"hdel":e1(pp.hdel),"adel":ev1(&pp.adel),"hprv":e1(pp.hprv),"bprv":ev1(&pp.bprv),"grant_bases":ev1(&pp.grant_bases),
            "query_bases":pp.query_bases.iter().map(|(i,(xs,y))|json!([i,ev1(xs),e1(*y)])).collect::<Vec<_>>()},
        "issuer_public":{"vk":ev2(&ip.vk),"metadata_keys":ev1(&ip.metadata_keys),"key_proof":hex(&ip.key_proof.encode())}
    })
}

pub(super) fn darlt_import(material: &Value) -> Result<ProtocolContext> {
    let p = &material["public_parameters"];
    if (
        n(p, "n")?,
        n(p, "s")?,
        n(p, "w")?,
        n(p, "k_max")?,
        n(p, "k_del")?,
        n(p, "k_prv")?,
    ) != (1024, 16, 64, 64, 6, 4)
    {
        return Err("case study public parameter profile mismatch".into());
    }
    let r = &p["srs"];
    let mut g2 = BTreeMap::new();
    for x in r["g2"]
        .as_array()
        .filter(|a| a.len() <= 64)
        .ok_or("public G2 map")?
    {
        let i = x[0].as_u64().ok_or("public G2 index")? as usize;
        if g2.insert(i, p2(&x[1])?).is_some() {
            return Err("duplicate public G2 index".into());
        }
    }
    let srs = ReferenceString {
        domain: Domain::new(n(r, "domain_size")?)?,
        degree: n(r, "degree")?,
        n: n(r, "n")?,
        w: n(r, "w")?,
        s: n(r, "s")?,
        k_max: n(r, "k_max")?,
        k_padded: n(r, "k_padded")?,
        g1: vector(&r["g1"], p1)?,
        g2,
        lagrange: vector(&r["lagrange"], p1)?,
        vanishing: p1(&r["vanishing"])?,
        k_hat: vector(&r["k_hat"], p2)?,
        d_hat: vector(&r["d_hat"], p2)?,
        o_hat: vector(&r["o_hat"], p2)?,
        offset: p1(&r["offset"])?,
    };
    let f = &p["fc"];
    let fc = spseq_fc::Params::new(
        p1(&f["u"])?,
        p1(&f["h0"])?,
        vector(&f["attrs"], p1)?,
        vector(&f["pools"], p1)?,
    )?;
    let mut query_bases = BTreeMap::new();
    for x in p["query_bases"]
        .as_array()
        .filter(|a| a.len() <= 64)
        .ok_or("public query map")?
    {
        let i = x[0].as_u64().ok_or("public query index")? as usize;
        if query_bases
            .insert(i, (vector(&x[1], p1)?, p1(&x[2])?))
            .is_some()
        {
            return Err("duplicate public query index".into());
        }
    }
    let pp = PublicParameters {
        n: n(p, "n")?,
        s: n(p, "s")?,
        w: n(p, "w")?,
        k_max: n(p, "k_max")?,
        k_del: n(p, "k_del")?,
        k_prv: n(p, "k_prv")?,
        srs,
        fc,
        ghat: p1(&p["ghat"])?,
        h: p1(&p["h"])?,
        hdel: p1(&p["hdel"])?,
        adel: vector(&p["adel"], p1)?,
        hprv: p1(&p["hprv"])?,
        bprv: vector(&p["bprv"], p1)?,
        grant_bases: vector(&p["grant_bases"], p1)?,
        query_bases,
        id: bytes::<32>(&p["id"])?,
    };
    if pp.id != request_hash(&pp.encode()) {
        return Err("public parameter identity mismatch".into());
    }
    let i = &material["issuer_public"];
    let ip = IssuerPublic {
        vk: vector(&i["vk"], p2)?,
        metadata_keys: vector(&i["metadata_keys"], p1)?
            .try_into()
            .map_err(|_| "metadata key count")?,
        key_proof: sigma::Proof::decode(&unhex(s(i, "key_proof")?)?, 11, 0)?,
    };
    ProtocolContext::new(Arc::new(pp), Arc::new(ip))
}

pub(super) fn sma_export(pp: &sma::Params, issuer: &sma::Issuer, meta: &sma::MetadataKey) -> Value {
    json!({"parameters":{"k":pp.k,"n":pp.n,"anchor":e1(pp.anchor),"u":e1(pp.u),"h":e1(pp.h),"y":ev1(&pp.y),"bit_h":e1(pp.bit_h)},
        "issuer_public":{"vk":ev2(&issuer.vk),"proof":{"c":es(issuer.proof.c),"z":evs(&issuer.proof.z)}},
        "metadata_public":{"pk":ev1(&meta.pk),"proof":{"c":es(meta.proof.c),"z":evs(&meta.proof.z),"orz":meta.proof.orz.iter().map(|x|evs(x)).collect::<Vec<_>>()}}})
}

pub(super) fn sma_import(material: &Value) -> Result<sma::InstalledInstance> {
    let p = &material["parameters"];
    if n(p, "k")? != 10 || n(p, "n")? != 1024 {
        return Err("case study SMA public profile mismatch".into());
    }
    let pp = sma::Params {
        k: 10,
        n: 1024,
        anchor: p1(&p["anchor"])?,
        u: p1(&p["u"])?,
        h: p1(&p["h"])?,
        y: vector(&p["y"], p1)?,
        bit_h: p1(&p["bit_h"])?,
    };
    let i = &material["issuer_public"];
    // Unused local fields are zero; install_instance consumes public fields.
    let issuer = sma::Issuer {
        sk: [S::ZERO; 4],
        vk: vector(&i["vk"], p2)?
            .try_into()
            .map_err(|_| "issuer key count")?,
        proof: sma::G2Proof {
            c: scalar(&i["proof"]["c"])?,
            z: vector(&i["proof"]["z"], scalar)?,
        },
    };
    let m = &material["metadata_public"];
    let mut orz = vec![];
    for x in m["proof"]["orz"]
        .as_array()
        .filter(|a| a.len() <= 64)
        .ok_or("metadata public proof branches")?
    {
        orz.push(
            vector(x, scalar)?
                .try_into()
                .map_err(|_| "metadata proof branch size")?,
        );
    }
    let meta = sma::MetadataKey {
        sk: [S::ZERO; 2],
        pk: vector(&m["pk"], p1)?
            .try_into()
            .map_err(|_| "metadata key count")?,
        proof: sma2rt_proof::Proof {
            c: scalar(&m["proof"]["c"])?,
            z: vector(&m["proof"]["z"], scalar)?,
            orz,
        },
    };
    sma::install_instance(&pp, &issuer, &meta).map_err(err)
}
