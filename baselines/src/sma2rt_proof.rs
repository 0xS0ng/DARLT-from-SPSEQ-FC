//! Versioned full-statement Sigma/OR compiler for SMA profile-2 issuance,
//! and canonical raw-transcript hashing used by its eight token relations.
use crate::arithmetic::*;
use rand::RngCore;

#[derive(Clone, Debug)]
pub struct Eq1 {
    pub target: G1,
    pub terms: Vec<(usize, G1)>,
}
#[derive(Clone, Debug)]
pub struct Or1 {
    pub branches: [Vec<(G1, G1)>; 2],
}
#[derive(Clone, Debug)]
pub struct Statement {
    pub vars: usize,
    pub eqs: Vec<Eq1>,
    pub ors: Vec<Or1>,
}
#[derive(Clone, Debug)]
pub struct Proof {
    pub c: S,
    pub z: Vec<S>,
    pub orz: Vec<[S; 3]>,
}
impl Proof {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = encs(self.c);
        b.extend((self.z.len() as u64).to_be_bytes());
        for &z in &self.z {
            b.extend(encs(z));
        }
        b.extend((self.orz.len() as u64).to_be_bytes());
        for triple in &self.orz {
            for &z in triple {
                b.extend(encs(z));
            }
        }
        b
    }
}
/// Version is fixed in the hash domain and transcript; all inputs are framed.
pub fn raw_challenge(tag: &[u8], raw: &[u8], firsts: &[G1]) -> S {
    let mut b = b"SMA2RT-profile-2/RAW-STMT-v2".to_vec();
    frame(&mut b, raw);
    b.extend((firsts.len() as u64).to_be_bytes());
    for &a in firsts {
        b.extend(enc1(a));
    }
    hash_scalar(tag, &b)
}
/// Prover-only equivalent transcript construction using prepared canonical bytes.
pub(crate) fn raw_challenge_cached(
    tag: &[u8],
    raw: &[u8],
    firsts: &[G1],
    cache: &CanonicalPointCache,
) -> S {
    let mut b = b"SMA2RT-profile-2/RAW-STMT-v2".to_vec();
    frame(&mut b, raw);
    b.extend((firsts.len() as u64).to_be_bytes());
    for &a in firsts {
        b.extend(cache.enc1(a));
    }
    hash_scalar(tag, &b)
}
/// Exact-length public-prefix capability. A differing valid shape uses the
/// original full transcript, never a digest substituted for public bytes.
#[derive(Clone)]
pub(crate) struct InstalledRawChallenge {
    tag: Vec<u8>,
    raw_prefix: Vec<u8>,
    raw_len: usize,
    firsts_len: usize,
    cached: CachedScalarHashPrefix,
}
impl InstalledRawChallenge {
    pub(crate) fn new(tag: &[u8], raw_prefix: Vec<u8>, raw_len: usize, firsts_len: usize) -> Self {
        assert!(raw_prefix.len() <= raw_len);
        let mut prefix = b"SMA2RT-profile-2/RAW-STMT-v2".to_vec();
        prefix.extend((raw_len as u64).to_be_bytes());
        prefix.extend(&raw_prefix);
        let suffix_len = raw_len - raw_prefix.len() + 8 + 48 * firsts_len;
        Self {
            tag: tag.to_vec(),
            raw_prefix,
            raw_len,
            firsts_len,
            cached: CachedScalarHashPrefix::new(tag, &prefix, &[suffix_len]),
        }
    }
    pub(crate) fn challenge(&self, raw: &[u8], firsts: &[G1]) -> S {
        if raw.len() != self.raw_len
            || firsts.len() != self.firsts_len
            || !raw.starts_with(&self.raw_prefix)
        {
            return raw_challenge(&self.tag, raw, firsts);
        }
        let mut suffix = raw[self.raw_prefix.len()..].to_vec();
        suffix.extend((firsts.len() as u64).to_be_bytes());
        for &a in firsts {
            suffix.extend(enc1(a));
        }
        self.cached.finish(&suffix)
    }
    pub(crate) fn challenge_cached(
        &self,
        raw: &[u8],
        firsts: &[G1],
        cache: &CanonicalPointCache,
    ) -> S {
        if raw.len() != self.raw_len
            || firsts.len() != self.firsts_len
            || !raw.starts_with(&self.raw_prefix)
        {
            return raw_challenge_cached(&self.tag, raw, firsts, cache);
        }
        let mut suffix = raw[self.raw_prefix.len()..].to_vec();
        suffix.extend((firsts.len() as u64).to_be_bytes());
        for &a in firsts {
            suffix.extend(cache.enc1(a));
        }
        self.cached.finish(&suffix)
    }
}
pub(crate) struct OrPrepared {
    real: usize,
    witness: S,
    cs: S,
    zs: S,
    nonce: S,
    pub firsts: Vec<G1>,
}
impl OrPrepared {
    pub fn new(relation: &Or1, real: usize, witness: S, rng: &mut impl RngCore) -> Self {
        assert!(real < 2);
        let cs = random_scalar(rng);
        let zs = random_scalar(rng);
        let nonce = random_scalar(rng);
        let mut firsts = vec![];
        for j in 0..2 {
            for &(base, target) in &relation.branches[j] {
                firsts.push(if j == real {
                    g1_mul(base, nonce)
                } else {
                    sum1(&[(base, zs), (target, -cs)])
                });
            }
        }
        Self {
            real,
            witness,
            cs,
            zs,
            nonce,
            firsts,
        }
    }
    pub fn finish(self, c: S) -> [S; 3] {
        let cr = c - self.cs;
        let zr = self.nonce + cr * self.witness;
        if self.real == 0 {
            [cr, zr, self.zs]
        } else {
            [self.cs, self.zs, zr]
        }
    }
}
impl Statement {
    // Native proof construction uses the explicit new constructor; no default protocol state is promised.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            vars: 0,
            eqs: vec![],
            ors: vec![],
        }
    }
    pub fn var(&mut self) -> usize {
        let id = self.vars;
        self.vars += 1;
        id
    }
    pub fn eq(&mut self, target: G1, terms: Vec<(usize, G1)>) {
        self.eqs.push(Eq1 { target, terms });
    }
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = (self.vars as u64).to_be_bytes().to_vec();
        b.extend((self.eqs.len() as u64).to_be_bytes());
        for eq in &self.eqs {
            b.extend(enc1(eq.target));
            b.extend((eq.terms.len() as u64).to_be_bytes());
            for &(i, g) in &eq.terms {
                b.extend((i as u64).to_be_bytes());
                b.extend(enc1(g));
            }
        }
        b.extend((self.ors.len() as u64).to_be_bytes());
        for or in &self.ors {
            for branch in &or.branches {
                b.extend((branch.len() as u64).to_be_bytes());
                for &(g, y) in branch {
                    b.extend(enc1(g));
                    b.extend(enc1(y));
                }
            }
        }
        b
    }
    fn raw(&self, external: &[u8]) -> Vec<u8> {
        let mut b = vec![];
        frame(&mut b, external);
        frame(&mut b, &self.bytes());
        b
    }
    pub fn prove(
        &self,
        tag: &[u8],
        external: &[u8],
        w: &[S],
        ow: &[(usize, S)],
        rng: &mut impl RngCore,
    ) -> Proof {
        self.prove_cached(tag, external, w, ow, rng, None)
    }
    pub(crate) fn prove_cached(
        &self,
        tag: &[u8],
        external: &[u8],
        w: &[S],
        ow: &[(usize, S)],
        rng: &mut impl RngCore,
        cached: Option<&InstalledRawChallenge>,
    ) -> Proof {
        assert_eq!(w.len(), self.vars);
        assert_eq!(ow.len(), self.ors.len());
        let rr: Vec<_> = (0..self.vars).map(|_| random_scalar(rng)).collect();
        let mut firsts: Vec<_> = self
            .eqs
            .iter()
            .map(|e| sum1(&e.terms.iter().map(|&(i, g)| (g, rr[i])).collect::<Vec<_>>()))
            .collect();
        let states: Vec<_> = self
            .ors
            .iter()
            .zip(ow)
            .map(|(o, &(real, w))| OrPrepared::new(o, real, w, rng))
            .collect();
        for s in &states {
            firsts.extend(&s.firsts);
        }
        let raw = self.raw(external);
        let c = cached.map_or_else(
            || raw_challenge(tag, &raw, &firsts),
            |p| p.challenge(&raw, &firsts),
        );
        Proof {
            c,
            z: rr.iter().zip(w).map(|(&r, &x)| r + c * x).collect(),
            orz: states.into_iter().map(|s| s.finish(c)).collect(),
        }
    }
    pub fn verify(&self, tag: &[u8], external: &[u8], proof: &Proof) -> bool {
        self.verify_cached(tag, external, proof, None)
    }
    pub(crate) fn verify_cached(
        &self,
        tag: &[u8],
        external: &[u8],
        proof: &Proof,
        cached: Option<&InstalledRawChallenge>,
    ) -> bool {
        if proof.z.len() != self.vars
            || proof.orz.len() != self.ors.len()
            || self
                .eqs
                .iter()
                .any(|e| e.terms.iter().any(|&(i, _)| i >= self.vars))
        {
            return false;
        }
        let mut firsts: Vec<_> = self
            .eqs
            .iter()
            .map(|e| {
                let mut terms: Vec<_> = e.terms.iter().map(|&(i, g)| (g, proof.z[i])).collect();
                terms.push((e.target, -proof.c));
                sum1(&terms)
            })
            .collect();
        for (o, z) in self.ors.iter().zip(&proof.orz) {
            for j in 0..2 {
                let c = if j == 0 { z[0] } else { proof.c - z[0] };
                for &(g, y) in &o.branches[j] {
                    firsts.push(sum1(&[(g, z[j + 1]), (y, -c)]));
                }
            }
        }
        {
            let raw = self.raw(external);
            cached.map_or_else(
                || raw_challenge(tag, &raw, &firsts),
                |p| p.challenge(&raw, &firsts),
            ) == proof.c
        }
    }
}
