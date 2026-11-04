//! SMA²RT Cheshire (ePrint 2026/518, full PDF 2026-06-05, Figs.6–8).
//! Experimental SMA2RT-profile-2: explicit pkU', distinct hash domains,
//! complete Sigma/OR proofs, including ctr range; SMA-INV-1 raw transcript, no delegation.
use crate::{
    arithmetic::*,
    sma2rt_proof::{self, InstalledRawChallenge, Or1, OrPrepared, Proof, Statement},
};
use ff::Field;
use group::Group;
use rand::RngCore;
pub type Result<T> = std::result::Result<T, &'static str>;
#[derive(Clone, Debug)]
pub struct Params {
    pub k: usize,
    pub n: u64,
    pub anchor: G1,
    pub u: G1,
    pub h: G1,
    pub y: Vec<G1>,
    pub bit_h: G1,
}
#[derive(Clone, Debug)]
pub struct G2Proof {
    pub c: S,
    pub z: Vec<S>,
}
#[derive(Clone, Debug)]
pub struct Issuer {
    pub sk: [S; 4],
    pub vk: [G2; 4],
    pub proof: G2Proof,
}
#[derive(Clone, Debug)]
pub struct MetadataKey {
    pub sk: [S; 2],
    pub pk: [G1; 2],
    pub proof: Proof,
}
#[derive(Clone, Debug)]
pub struct UserKey {
    sk: S,
    pk: G1,
}
#[derive(Clone, Debug)]
pub struct Signature {
    pub z: G1,
    pub y: G1,
    pub yhat: G2,
}
#[derive(Clone, Debug)]
pub enum Atom {
    Reveal(usize, S),
    Equal(usize, S),
    Linear(Vec<(usize, S)>, S),
}
#[derive(Clone, Debug, Default)]
pub struct Policy {
    pub atoms: Vec<Atom>,
}
#[derive(Clone, Debug)]
pub struct Request {
    pub pk: G1,
    pub ca: G1,
    pub proof: Proof,
}
#[derive(Clone, Debug)]
pub struct RequestState {
    pub request: Request,
    pub key: UserKey,
    pub attrs: Vec<S>,
    pub zu: [S; 2],
    pub r: S,
    // Public request fields can be replaced. Only an actual point equality
    // with this privately captured local derivation carries membership.
    local_ca: G1,
}
#[derive(Clone, Debug)]
pub struct Credential {
    pub sig: Signature,
    pub e: G1,
    pub ca: G1,
    pub cf: G1,
    pub zi: [S; 2],
    pub encryption: Proof,
}
/// Created only after successful full credential acceptance.
#[derive(Clone, Debug)]
pub struct Wallet {
    key: UserKey,
    attrs: Vec<S>,
    z: [S; 2],
    r: S,
    m: [G1; 4],
    sig: Signature,
    profile: Vec<u8>,
    installation_binding: Vec<u8>,
}
#[derive(Clone, Debug)]
pub struct Token {
    pub sig: Signature,
    pub m: [G1; 4],
    pub serial: G1,
    pub d: G1,
    pub pk_prime: G1,
    pub q: G1,
    pub bits: Vec<G1>,
    pub proof: Proof,
}
/// Immutable evidence of exact-shape canonical subgroup decoding. Acceptance
/// still requires the original signature, policy, range and full FS relations.
/// ```compile_fail
/// use baseline_core::sma2rt::{CheckedToken, Token};
/// fn forge(token:Token) { let _ = CheckedToken { token }; }
/// ```
/// ```compile_fail
/// use baseline_core::sma2rt::CheckedToken;
/// fn mutate(t:&CheckedToken) { t.as_token().bits.clear(); }
/// ```
#[derive(Clone)]
pub struct CheckedToken {
    token: Token,
}
impl CheckedToken {
    pub fn decode_received_installed(
        h: &InstalledInstance,
        bytes: &[u8],
        policy: &Policy,
    ) -> Result<Self> {
        Ok(Self {
            token: Token::from_received_installed(h, bytes, policy)?,
        })
    }
    pub fn decode_installed(h: &InstalledInstance, bytes: &[u8]) -> Result<Self> {
        Ok(Self {
            token: Token::from_bytes_internal(&h.pp, bytes, true)?,
        })
    }
    pub fn as_token(&self) -> &Token {
        &self.token
    }
}
#[derive(Clone, Debug)]
pub struct Record {
    pub context: Vec<u8>,
    pub policy: Policy,
    pub token: Token,
}
/// Installed issuer key binds the fixed anchor pairing to the complete pp/vk.
/// Constructed only through successful key-PoK verification.
#[derive(Clone)]
pub struct InstalledIssuer {
    vk: [G2; 4],
    anchor_pair: GT,
    binding: Vec<u8>,
}
/// Owned, immutable public instance. Safe Rust cannot construct a forged
/// capability or mutate its public objects; replacement requires installation.
/// ```compile_fail
/// use baseline_core::sma2rt::InstalledInstance;
/// let forged = InstalledInstance {};
/// ```
/// ```compile_fail
/// use baseline_core::sma2rt::InstalledInstance;
/// fn mutate(h: &InstalledInstance) { h.parameters().k = 99; }
/// ```
#[derive(Clone)]
pub struct InstalledInstance {
    pp: Params,
    issuer: InstalledIssuer,
    metadata_pk: [G1; 2],
    pp_bytes: Vec<u8>,
    instance: Vec<u8>,
    installation_binding: Vec<u8>,
    request_hash: InstalledRawChallenge,
    encryption_hash: InstalledRawChallenge,
    token_hash: InstalledRawChallenge,
}
impl InstalledInstance {
    pub fn parameters(&self) -> &Params {
        &self.pp
    }
    pub fn issuer_vk(&self) -> &[G2; 4] {
        &self.issuer.vk
    }
    pub fn matches_public_instance(
        &self,
        pp: &Params,
        vk: &[G2; 4],
        metadata_pk: &[G1; 2],
    ) -> bool {
        // Compressed bytes alone do not authenticate an in-memory point:
        // safe from_raw_unchecked can preserve its encoding while going off curve.
        pp.k == self.pp.k
            && pp.n == self.pp.n
            && [pp.anchor, pp.u, pp.h, pp.bit_h]
                == [self.pp.anchor, self.pp.u, self.pp.h, self.pp.bit_h]
            && pp.y == self.pp.y
            && vk == &self.issuer.vk
            && metadata_pk == &self.metadata_pk
    }
}
/// Private one-use nonce state. Every candidate is bound to one wallet and ctr.
/// ```compile_fail
/// use baseline_core::sma2rt::*;
/// fn replay(p: &Params, vk: &[baseline_core::arithmetic::G2;4], state: Prepared, pol: &Policy) {
///     let _ = show_online(p,vk,state,b"first",pol);
///     let _ = show_online(p,vk,state,b"second",pol);
/// }
/// ```
pub struct Prepared {
    encodings: CanonicalPointCache,
    token: Token,
    witnesses: Vec<S>,
    nonces: Vec<S>,
    firsts: Vec<G1>,
    attribute_firsts: Vec<G1>,
    ors: Vec<OrPrepared>,
    attrs: Vec<S>,
    pk: G1,
    profile: Vec<u8>,
    installation_binding: Vec<u8>,
    prepared_policy: Option<(Vec<u8>, Vec<Option<S>>)>,
}
fn empty() -> Proof {
    Proof {
        c: S::ZERO,
        z: vec![],
        orz: vec![],
    }
}
fn put1s(b: &mut Vec<u8>, xs: &[G1]) {
    b.extend((xs.len() as u64).to_be_bytes());
    for &x in xs {
        b.extend(enc1(x));
    }
}
impl Params {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = b"SMA2RT-profile-2/BLS12-381/v2".to_vec();
        b.extend((self.k as u64).to_be_bytes());
        b.extend(self.n.to_be_bytes());
        for x in [self.anchor, self.u, self.h, self.bit_h] {
            b.extend(enc1(x));
        }
        put1s(&mut b, &self.y);
        b
    }
    pub fn valid(&self) -> bool {
        self.k >= 1
            && self.k <= 1024
            && self.n >= 2
            && self.n.is_power_of_two()
            && self.n <= 1u64 << 32
            && self.y.len() == self.k + 3
            && [self.anchor, self.u, self.h, self.bit_h]
                .iter()
                .chain(&self.y)
                .all(|&x| valid1(x, true))
    }
}
impl Policy {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = vec![];
        b.extend((self.atoms.len() as u64).to_be_bytes());
        for a in &self.atoms {
            match a {
                Atom::Reveal(i, v) | Atom::Equal(i, v) => {
                    b.push(if matches!(a, Atom::Reveal(..)) { 0 } else { 1 });
                    b.extend((*i as u64).to_be_bytes());
                    b.extend(encs(*v));
                }
                Atom::Linear(t, v) => {
                    b.push(2);
                    b.extend((t.len() as u64).to_be_bytes());
                    for &(i, c) in t {
                        b.extend((i as u64).to_be_bytes());
                        b.extend(encs(c));
                    }
                    b.extend(encs(*v));
                }
            }
        }
        b
    }
    pub fn satisfied(&self, a: &[S]) -> bool {
        self.atoms.iter().all(|p| match p {
            Atom::Reveal(i, v) | Atom::Equal(i, v) => a.get(*i) == Some(v),
            Atom::Linear(ts, v) => {
                !ts.is_empty()
                    && ts.iter().all(|(i, _)| *i < a.len())
                    && ts.iter().fold(S::ZERO, |s, (i, c)| s + a[*i] * c) == *v
            }
        })
    }
}
impl Signature {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = enc1(self.z);
        b.extend(enc1(self.y));
        b.extend(enc2(self.yhat));
        b
    }
}
impl Request {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = enc1(self.pk);
        b.extend(enc1(self.ca));
        frame(&mut b, &self.proof.bytes());
        b
    }
}
impl Credential {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = self.sig.bytes();
        for x in [self.e, self.ca, self.cf] {
            b.extend(enc1(x));
        }
        for x in self.zi {
            b.extend(encs(x));
        }
        frame(&mut b, &self.encryption.bytes());
        b
    }
}
/// Opaque evidence of canonical decoding of every issuer-response field.
pub struct ReceivedCredential(Credential);
impl ReceivedCredential {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = crate::canonical::Reader::new(bytes, crate::canonical::DecodeLimits::default())
            .map_err(|_| "credential encoding")?;
        let sig = Signature {
            z: r.g1().map_err(|_| "credential Z")?,
            y: r.g1().map_err(|_| "credential Y")?,
            yhat: r.g2().map_err(|_| "credential Yhat")?,
        };
        let e = r.g1().map_err(|_| "credential E")?;
        let ca = r.g1().map_err(|_| "credential CA")?;
        let cf = r.g1().map_err(|_| "credential CF")?;
        let zi = [
            r.scalar().map_err(|_| "credential scalar")?,
            r.scalar().map_err(|_| "credential scalar")?,
        ];
        let n = r
            .bounded_usize(8 * 1024 * 1024, "proof bytes")
            .map_err(|_| "credential proof length")?;
        let p = crate::canonical::decode_proof(r.take(n).map_err(|_| "credential proof")?)
            .map_err(|_| "credential proof")?;
        r.finish().map_err(|_| "credential trailing bytes")?;
        if sig.y == G1::identity()
            || sig.yhat == G2::identity()
            || [e, ca, cf].iter().any(|p| *p == G1::identity())
        {
            return Err("credential identity");
        }
        Ok(Self(Credential {
            sig,
            e,
            ca,
            cf,
            zi,
            encryption: Proof {
                c: p.c,
                z: p.z,
                orz: p.orz,
            },
        }))
    }
}
impl Token {
    /// Strict received-token input checks, without any signature/Sigma algebra.
    /// Identity is retained for exactly the native identity-allowed fields.
    pub fn from_received_installed(
        h: &InstalledInstance,
        bytes: &[u8],
        policy: &Policy,
    ) -> Result<Self> {
        let token = Self::from_bytes_internal(&h.pp, bytes, true)?;
        let known = disclosed(&h.pp, policy).ok_or("invalid expected disclosure schema")?;
        if token.m.iter().any(|p| *p == G1::identity())
            || token.sig.y == G1::identity()
            || token.sig.yhat == G2::identity()
            || token.serial == G1::identity()
            || token.pk_prime == G1::identity()
            || token.proof.z.len() != FIXED + known.iter().filter(|v| v.is_none()).count()
        {
            return Err("SMA received-token domain or dimension");
        }
        Ok(token)
    }

    fn core_bytes(&self) -> Vec<u8> {
        let mut b = b"SMA2RT-INV1-v2".to_vec();
        b.extend(self.sig.bytes());
        for x in self.m {
            b.extend(enc1(x));
        }
        for x in [self.serial, self.d, self.pk_prime, self.q] {
            b.extend(enc1(x));
        }
        put1s(&mut b, &self.bits);
        b
    }
    fn core_bytes_cached(&self, cache: &CanonicalPointCache) -> Vec<u8> {
        let mut b = b"SMA2RT-INV1-v2".to_vec();
        b.extend(cache.enc1(self.sig.z));
        b.extend(cache.enc1(self.sig.y));
        b.extend(cache.enc2(self.sig.yhat));
        for x in self.m {
            b.extend(cache.enc1(x));
        }
        for x in [self.serial, self.d, self.pk_prime, self.q] {
            b.extend(cache.enc1(x));
        }
        b.extend((self.bits.len() as u64).to_be_bytes());
        for &x in &self.bits {
            b.extend(cache.enc1(x));
        }
        b
    }
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = self.core_bytes();
        frame(&mut b, &self.proof.bytes());
        b
    }
    /// Algebraic payload excludes u64 framing/length words, includes ALL proof scalars.
    pub fn payload_bytes(&self) -> usize {
        192 + 4 * 48
            + 4 * 48
            + self.bits.len() * 48
            + 32 * (1 + self.proof.z.len() + 3 * self.proof.orz.len())
    }
    /// Exact shape, canonical scalar/curve/subgroup decode, bounded length and EOF.
    /// Cryptographic acceptance still requires verify with the expected context/policy.
    pub fn from_bytes(pp: &Params, bytes: &[u8]) -> Result<Self> {
        Self::from_bytes_internal(pp, bytes, false)
    }
    fn from_bytes_internal(pp: &Params, bytes: &[u8], installed: bool) -> Result<Self> {
        if bytes.len() > 8 * 1024 * 1024 || (!installed && !pp.valid()) {
            return Err("invalid SMA wire limits");
        }
        struct Reader<'a> {
            b: &'a [u8],
            p: usize,
        }
        impl<'a> Reader<'a> {
            fn take(&mut self, n: usize) -> Result<&'a [u8]> {
                let end = self.p.checked_add(n).ok_or("overflow")?;
                if end > self.b.len() {
                    return Err("truncated SMA token");
                }
                let out = &self.b[self.p..end];
                self.p = end;
                Ok(out)
            }
            fn len(&mut self) -> Result<usize> {
                let n = u64::from_be_bytes(self.take(8)?.try_into().unwrap());
                usize::try_from(n).map_err(|_| "length overflow")
            }
            fn g1(&mut self) -> Result<G1> {
                crate::canonical::decode_g1(self.take(48)?).map_err(|_| "invalid canonical G1")
            }
            fn g2(&mut self) -> Result<G2> {
                crate::canonical::decode_g2(self.take(96)?).map_err(|_| "invalid canonical G2")
            }
        }
        let mut r = Reader { b: bytes, p: 0 };
        if r.take(14)? != b"SMA2RT-INV1-v2" {
            return Err("wrong token transcript version");
        }
        let sig = Signature {
            z: r.g1()?,
            y: r.g1()?,
            yhat: r.g2()?,
        };
        let m = [r.g1()?, r.g1()?, r.g1()?, r.g1()?];
        let serial = r.g1()?;
        let d = r.g1()?;
        let pk_prime = r.g1()?;
        let q = r.g1()?;
        let count = r.len()?;
        if count != pp.n.trailing_zeros() as usize {
            return Err("wrong ctr proof width");
        }
        let mut bits = Vec::with_capacity(count);
        for _ in 0..count {
            bits.push(r.g1()?);
        }
        let len = r.len()?;
        if len > 48 + (pp.k + 10) * 32 + count * 96 {
            return Err("wrong proof size");
        }
        let proof =
            crate::canonical::decode_proof(r.take(len)?).map_err(|_| "invalid canonical proof")?;
        if proof.z.len() < 10
            || proof.z.len() > pp.k + 10
            || proof.orz.len() != count
            || r.p != bytes.len()
        {
            return Err("noncanonical SMA token shape or trailing bytes");
        }
        Ok(Self {
            sig,
            m,
            serial,
            d,
            pk_prime,
            q,
            bits,
            proof: Proof {
                c: proof.c,
                z: proof.z,
                orz: proof.orz,
            },
        })
    }
}
impl Record {
    pub fn bytes(&self) -> Vec<u8> {
        let mut b = vec![];
        frame(&mut b, &self.context);
        frame(&mut b, &self.policy.bytes());
        frame(&mut b, &self.token.bytes());
        b
    }
}
impl Wallet {
    pub fn public_key(&self) -> G1 {
        self.key.pk
    }
    pub fn attribute_count(&self) -> usize {
        self.attrs.len()
    }
}
#[allow(clippy::manual_range_contains)]
/// Create in-memory public parameters for this native scheme.
pub fn setup(k: usize, n: u64) -> Params {
    assert!(k >= 1 && k <= 1024 && n >= 2 && n.is_power_of_two() && n <= 1u64 << 32);
    let domain = format!("SMA2RT-profile-2/{k}/{n}");
    let h = |s: &str| hash_g1(b"SMA_SETUP", format!("{domain}/{s}").as_bytes());
    Params {
        k,
        n,
        anchor: h("anchor"),
        u: h("offset"),
        h: h("blind"),
        y: (0..k + 3).map(|i| h(&format!("attribute/{i}"))).collect(),
        bit_h: h("bit-blind"),
    }
}
fn instance(pp: &Params, vk: &[G2; 4]) -> Vec<u8> {
    let mut b = pp.bytes();
    for &x in vk {
        b.extend(enc2(x));
    }
    b
}
// Private local capability binding, never added to the published FS transcript.
fn local_instance_binding(instance: &[u8], metadata_pk: &[G1; 2]) -> Vec<u8> {
    let mut b = b"\x45\x56\x41\x30\x30\x36\x2f\x53\x4d\x41\x2f\x6c\x6f\x63\x61\x6c\x20\x69\x6e\x73\x74\x61\x6c\x6c\x65\x64\x20\x69\x6e\x73\x74\x61\x6e\x63\x65\x20\x62\x69\x6e\x64\x69\x6e\x67\x2f\x76\x31".to_vec();
    frame(&mut b, instance);
    for &v in metadata_pk {
        b.extend(enc1(v));
    }
    digest(&b)
}
fn g2challenge(pp: &Params, vk: &[G2; 4], t: &[G2]) -> S {
    let mut b = instance(pp, vk);
    for &x in t {
        b.extend(enc2(x));
    }
    hash_scalar(b"SMA_IKEY", &b)
}
/// IKeyGen: generate the native issuer signing key and its proof.
pub fn ikeygen(pp: &Params, rng: &mut impl RngCore) -> Issuer {
    let sk = std::array::from_fn(|_| random_nonzero(&mut *rng));
    let vk = sk.map(|x| g2_mul(G2::generator(), x));
    let rr: [S; 4] = std::array::from_fn(|_| random_scalar(&mut *rng));
    let ts = rr.map(|x| g2_mul(G2::generator(), x));
    let c = g2challenge(pp, &vk, &ts);
    let proof = G2Proof {
        c,
        z: rr.iter().zip(sk).map(|(r, x)| *r + c * x).collect(),
    };
    Issuer { sk, vk, proof }
}
pub fn verify_issuer_key(pp: &Params, vk: &[G2; 4], p: &G2Proof) -> bool {
    if !pp.valid() || p.z.len() != 4 || vk.iter().any(|&x| !valid2(x, true)) {
        return false;
    }
    let ts: Vec<_> = vk
        .iter()
        .zip(&p.z)
        .map(|(&x, &z)| sum2(&[(G2::generator(), z), (x, -p.c)]))
        .collect();
    g2challenge(pp, vk, &ts) == p.c
}
/// Validate and cache the native issuer key before repeated operations.
pub fn install_issuer(pp: &Params, issuer: &Issuer) -> Result<InstalledIssuer> {
    if !verify_issuer_key(pp, &issuer.vk, &issuer.proof) {
        return Err("issuer key proof rejected");
    }
    Ok(InstalledIssuer {
        vk: issuer.vk,
        anchor_pair: pair(pp.anchor, issuer.vk[0]),
        binding: instance(pp, &issuer.vk),
    })
}
/// Includes parameter/key subgroup checks, both key PoKs, the fixed anchor
/// pairing and exact-length FS prefixes. Installation is measured separately.
/// Bind checked parameters, issuer key, metadata key and disclosure profile.
pub fn install_instance(
    pp: &Params,
    issuer: &Issuer,
    metadata: &MetadataKey,
) -> Result<InstalledInstance> {
    let installed = install_issuer(pp, issuer)?;
    if !verify_metadata_key(pp, &metadata.pk, &metadata.proof) {
        return Err("metadata key proof rejected");
    }
    let pp_bytes = pp.bytes();
    let inst = instance(pp, &issuer.vk);
    let pol = Policy::default();
    let req = Request {
        pk: G1::identity(),
        ca: G1::identity(),
        proof: Proof {
            c: S::ZERO,
            z: vec![S::ZERO; pp.k + 4],
            orz: vec![],
        },
    };
    let st = request_statement(pp, &req, &pol).ok_or("invalid installed request schema")?;
    let request_external_len = pp_bytes.len() + 112;
    let request_raw_len = 16 + request_external_len + st.bytes().len();
    let mut request_prefix = (request_external_len as u64).to_be_bytes().to_vec();
    request_prefix.extend(&pp_bytes);
    let request_hash = InstalledRawChallenge::new(
        b"SMA_REQUEST",
        request_prefix,
        request_raw_len,
        st.eqs.len(),
    );
    let dummy_sig = Signature {
        z: G1::identity(),
        y: G1::identity(),
        yhat: G2::identity(),
    };
    let cred = Credential {
        sig: dummy_sig.clone(),
        e: G1::identity(),
        ca: G1::identity(),
        cf: G1::identity(),
        zi: [S::ZERO; 2],
        encryption: empty(),
    };
    let enc_st = encryption_statement(&metadata.pk, G1::identity(), G1::identity());
    let enc_external_len = encryption_external(pp, &issuer.vk, &metadata.pk, &req, &cred).len();
    let enc_raw_len = 16 + enc_external_len + enc_st.bytes().len();
    let mut enc_prefix = (enc_external_len as u64).to_be_bytes().to_vec();
    enc_prefix.extend(&inst);
    for &v in &metadata.pk {
        enc_prefix.extend(enc1(v));
    }
    let encryption_hash = InstalledRawChallenge::new(b"SMA_ENCRYPT", enc_prefix, enc_raw_len, 6);
    let dummy_token = Token {
        sig: dummy_sig,
        m: [G1::identity(); 4],
        serial: G1::identity(),
        d: G1::identity(),
        pk_prime: G1::identity(),
        q: G1::identity(),
        bits: vec![G1::identity(); pp.n.trailing_zeros() as usize],
        proof: empty(),
    };
    let token_pol = Policy {
        atoms: (0..3.min(pp.k)).map(|j| Atom::Reveal(j, S::ZERO)).collect(),
    };
    let token_raw_len = token_external(pp, &issuer.vk, &dummy_token, &[0; 32], &token_pol).len();
    let token_prefix = token_public_prefix(&inst);
    let token_hash = InstalledRawChallenge::new(
        b"SMA2_TOKEN",
        token_prefix,
        token_raw_len,
        8 + 2 * pp.n.trailing_zeros() as usize,
    );
    let installation_binding = local_instance_binding(&inst, &metadata.pk);
    Ok(InstalledInstance {
        pp: pp.clone(),
        issuer: installed,
        metadata_pk: metadata.pk,
        pp_bytes,
        instance: inst,
        installation_binding,
        request_hash,
        encryption_hash,
        token_hash,
    })
}
fn metadata_statement(pk: &[G1; 2]) -> Statement {
    let mut st = Statement::new();
    for &x in pk {
        let i = st.var();
        st.eq(x, vec![(i, G1::generator())]);
    }
    st
}
/// Generate the native secret metadata-reading key and its public proof.
pub fn vkeygen(pp: &Params, rng: &mut impl RngCore) -> MetadataKey {
    let a = random_nonzero(&mut *rng);
    let mut b = random_nonzero(&mut *rng);
    while b == a {
        b = random_nonzero(&mut *rng);
    }
    let sk = [a, b];
    let pk = sk.map(|x| g1_mul(G1::generator(), x));
    let proof = metadata_statement(&pk).prove(b"SMA_VKEY", &pp.bytes(), &sk, &[], rng);
    MetadataKey { sk, pk, proof }
}
pub fn verify_metadata_key(pp: &Params, pk: &[G1; 2], proof: &Proof) -> bool {
    pp.valid()
        && pk[0] != pk[1]
        && pk.iter().all(|&x| valid1(x, true))
        && metadata_statement(pk).verify(b"SMA_VKEY", &pp.bytes(), proof)
}
/// UKeyGen: generate a native holder key pair.
pub fn ukeygen(rng: &mut impl RngCore) -> UserKey {
    let sk = random_nonzero(rng);
    UserKey {
        sk,
        pk: g1_mul(G1::generator(), sk),
    }
}
impl UserKey {
    pub fn public_key(&self) -> G1 {
        self.pk
    }
    /// Import validates the long-term relation once, rather than every request.
    pub fn from_secret(sk: S) -> Result<Self> {
        if sk == S::ZERO {
            return Err("zero user key");
        }
        Ok(Self {
            sk,
            pk: g1_mul(G1::generator(), sk),
        })
    }
}
fn add_policy(st: &mut Statement, pol: &Policy, offset: usize, k: usize) -> bool {
    for a in &pol.atoms {
        match a {
            Atom::Reveal(i, v) | Atom::Equal(i, v) => {
                if *i >= k {
                    return false;
                }
                st.eq(
                    g1_mul(G1::generator(), *v),
                    vec![(offset + i, G1::generator())],
                );
            }
            Atom::Linear(ts, v) => {
                if ts.is_empty() || ts.iter().any(|(i, _)| *i >= k) {
                    return false;
                }
                st.eq(
                    g1_mul(G1::generator(), *v),
                    ts.iter()
                        .map(|&(i, c)| (offset + i, g1_mul(G1::generator(), c)))
                        .collect(),
                );
            }
        }
    }
    true
}
fn request_statement(pp: &Params, req: &Request, pol: &Policy) -> Option<Statement> {
    let mut st = Statement::new();
    for _ in 0..pp.k + 4 {
        st.var();
    }
    let mut terms = vec![(pp.k + 3, pp.h)];
    terms.extend(pp.y.iter().enumerate().map(|(i, &y)| (i, y)));
    st.eq(g1_add(req.ca, -pp.u), terms);
    st.eq(req.pk, vec![(pp.k + 2, G1::generator())]);
    if !add_policy(&mut st, pol, 0, pp.k) {
        return None;
    }
    Some(st)
}

fn request_external_cached(
    pp: &Params,
    req: &Request,
    pol: &Policy,
    installed: Option<&InstalledInstance>,
) -> Vec<u8> {
    let mut b = installed.map_or_else(|| pp.bytes(), |h| h.pp_bytes.clone());
    b.extend(enc1(req.pk));
    b.extend(enc1(req.ca));
    frame(&mut b, &pol.bytes());
    b
}
/// Create the holder request for native credential or token acquisition.
pub fn request(
    pp: &Params,
    key: &UserKey,
    attrs: &[S],
    pol: &Policy,
    rng: &mut impl RngCore,
) -> Result<(RequestState, Request)> {
    request_internal(pp, key, attrs, pol, rng, None)
}
pub fn request_installed(
    h: &InstalledInstance,
    key: &UserKey,
    attrs: &[S],
    pol: &Policy,
    rng: &mut impl RngCore,
) -> Result<(RequestState, Request)> {
    request_internal(&h.pp, key, attrs, pol, rng, Some(h))
}
fn request_internal(
    pp: &Params,
    key: &UserKey,
    attrs: &[S],
    pol: &Policy,
    rng: &mut impl RngCore,
    installed: Option<&InstalledInstance>,
) -> Result<(RequestState, Request)> {
    if (installed.is_none() && !pp.valid())
        || attrs.len() != pp.k
        || !pol.satisfied(attrs)
        || key.sk == S::ZERO
        // UserKey is immutable outside this module and only constructed as
        // generator * nonzero scalar. Keep the original nonzero rule.
        || key.pk == G1::identity()
    {
        return Err("invalid request input");
    }
    let zu = [random_scalar(&mut *rng), random_scalar(&mut *rng)];
    let r = random_scalar(&mut *rng);
    let mut w = attrs.to_vec();
    w.extend(zu);
    w.push(key.sk);
    w.push(r);
    let mut terms: Vec<_> = pp.y.iter().zip(&w).map(|(&g, &x)| (g, x)).collect();
    terms.push((pp.h, r));
    let mut req = Request {
        pk: key.pk,
        ca: g1_add(pp.u, sum1(&terms)),
        proof: empty(),
    };
    let st = request_statement(pp, &req, pol).ok_or("invalid issue policy")?;
    req.proof = st.prove_cached(
        b"SMA_REQUEST",
        &request_external_cached(pp, &req, pol, installed),
        &w,
        &[],
        rng,
        installed.map(|h| &h.request_hash),
    );
    Ok((
        RequestState {
            request: req.clone(),
            key: key.clone(),
            attrs: attrs.to_vec(),
            zu,
            r,
            local_ca: req.ca,
        },
        req,
    ))
}
pub fn verify_request(pp: &Params, req: &Request, pol: &Policy) -> bool {
    verify_request_internal(pp, req, pol, None, false)
}
pub fn verify_request_installed(h: &InstalledInstance, req: &Request, pol: &Policy) -> bool {
    verify_request_internal(&h.pp, req, pol, Some(h), false)
}
fn verify_request_internal(
    pp: &Params,
    req: &Request,
    pol: &Policy,
    installed: Option<&InstalledInstance>,
    decoded: bool,
) -> bool {
    if (installed.is_none() && !pp.valid())
        || req.pk == G1::identity()
        || req.ca == G1::identity()
        || (!decoded && (!valid1(req.pk, true) || !valid1(req.ca, true)))
    {
        return false;
    }
    request_statement(pp, req, pol).is_some_and(|st| {
        st.verify_cached(
            b"SMA_REQUEST",
            &request_external_cached(pp, req, pol, installed),
            &req.proof,
            installed.map(|h| &h.request_hash),
        )
    })
}
#[cfg(test)]
fn sign(sk: &[S; 4], m: &[G1; 4], rng: &mut impl RngCore) -> Signature {
    let y = random_nonzero(rng);
    let iy = inv(y);
    let terms: Vec<_> = m.iter().zip(sk).map(|(&g, &x)| (g, x * y)).collect();
    Signature {
        z: sum1(&terms),
        y: g1_mul(G1::generator(), iy),
        yhat: g2_mul(G2::generator(), iy),
    }
}

fn verify_signature_internal(
    vk: &[G2; 4],
    m: &[G1; 4],
    sig: &Signature,
    installed: bool,
    decoded: bool,
) -> bool {
    if (!installed && vk.iter().any(|&x| !valid2(x, true)))
        || m.iter().any(|&x| x == G1::identity())
        || sig.y == G1::identity()
        || sig.yhat == G2::identity()
        || (!decoded
            && (m.iter().any(|&x| !valid1(x, true))
                || !valid1(sig.z, false)
                || !valid1(sig.y, true)
                || !valid2(sig.yhat, true)))
    {
        return false;
    }
    let mut terms = vec![(sig.z, sig.yhat)];
    terms.extend(m.iter().zip(vk).map(|(&a, &b)| (-a, b)));
    if multi_pair(&terms) != GT::identity() {
        return false;
    }
    multi_pair(&[(sig.y, G2::generator()), (-G1::generator(), sig.yhat)]) == GT::identity()
}
fn installed_signature_domain(m: &[G1; 4], sig: &Signature) -> bool {
    if m.iter().any(|&x| x == G1::identity())
        || !valid1(m[1], true)
        || !valid1(m[3], true)
        || !valid1(sig.z, false)
        || !valid1(sig.y, true)
        || !valid2(sig.yhat, true)
    {
        return false;
    }
    true
}
fn verify_installed_signature(installed: &InstalledIssuer, m: &[G1; 4], sig: &Signature) -> bool {
    // This private helper is called only by checked_credential_internal with
    // [installed anchor, received Cf, hash_g1(request), received E]. Anchor's
    // membership was checked by installation (or pp.valid on the legacy path);
    // R is a local hash-to-curve output. Preserve all four nonzero rules and
    // authenticate both received message coordinates and every signature point.
    if !installed_signature_domain(m, sig) {
        return false;
    }
    let mut terms = vec![(sig.z, sig.yhat)];
    terms.extend((1..4).map(|j| (-m[j], installed.vk[j])));
    if multi_pair(&terms) != installed.anchor_pair {
        return false;
    }
    multi_pair(&[(sig.y, G2::generator()), (-G1::generator(), sig.yhat)]) == GT::identity()
}

fn verify_installed_signature_set(
    installed: &InstalledIssuer,
    m: &[G1; 4],
    sig: &Signature,
    weights: &mut impl RngCore,
) -> bool {
    if !installed_signature_domain(m, sig) {
        return false;
    }
    verify_installed_signature_set_body(installed, m, sig, weights)
}
fn verify_installed_signature_set_body(
    installed: &InstalledIssuer,
    m: &[G1; 4],
    sig: &Signature,
    weights: &mut impl RngCore,
) -> bool {
    let mut terms = vec![(sig.z, sig.yhat)];
    terms.extend((1..4).map(|j| (-m[j], installed.vk[j])));
    crate::pairing_verify::verify_checked(
        &[
            crate::pairing_verify::Equation {
                terms,
                target: installed.anchor_pair,
            },
            crate::pairing_verify::Equation {
                terms: vec![(sig.y, G2::generator()), (-G1::generator(), sig.yhat)],
                target: GT::identity(),
            },
        ],
        crate::pairing_verify::Mode::Randomized,
        weights,
    )
}
fn encryption_statement(pk: &[G1; 2], r: G1, e: G1) -> Statement {
    let mut st = metadata_statement(pk);
    st.ors.push(Or1 {
        branches: [
            vec![(G1::generator(), pk[0]), (r, e)],
            vec![(G1::generator(), pk[1]), (r, e)],
        ],
    });
    st
}
fn encryption_external(
    pp: &Params,
    vk: &[G2; 4],
    pkv: &[G1; 2],
    req: &Request,
    c: &Credential,
) -> Vec<u8> {
    encryption_external_cached(pp, vk, pkv, req, c, None)
}
fn encryption_external_cached(
    pp: &Params,
    vk: &[G2; 4],
    pkv: &[G1; 2],
    req: &Request,
    c: &Credential,
    installed: Option<&InstalledInstance>,
) -> Vec<u8> {
    let mut b = installed.map_or_else(|| instance(pp, vk), |h| h.instance.clone());
    for &x in pkv {
        b.extend(enc1(x));
    }
    frame(&mut b, &req.bytes());
    b.extend(c.sig.bytes());
    for x in [c.e, c.ca, c.cf] {
        b.extend(enc1(x));
    }
    for x in c.zi {
        b.extend(encs(x));
    }
    b
}
/// Generate the native issuer response with the chosen hidden metadata bit.
pub fn respond(
    pp: &Params,
    issuer: &Issuer,
    metadata: &MetadataKey,
    req: &Request,
    pol: &Policy,
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    respond_internal(pp, issuer, metadata, req, pol, bit, rng, None, false)
}
pub fn respond_installed(
    h: &InstalledInstance,
    issuer: &Issuer,
    metadata: &MetadataKey,
    req: &Request,
    pol: &Policy,
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    if issuer.vk != h.issuer.vk || metadata.pk != h.metadata_pk {
        return Err("installed issuer/metadata mismatch");
    }
    respond_internal(&h.pp, issuer, metadata, req, pol, bit, rng, Some(h), false)
}
/// Canonical incoming request; only checked decoding can create this value.
pub struct ReceivedRequest(Request);
impl ReceivedRequest {
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let mut r = crate::canonical::Reader::new(bytes, crate::canonical::DecodeLimits::default())
            .map_err(|_| "request framing")?;
        let pk = r.g1().map_err(|_| "request pk")?;
        let ca = r.g1().map_err(|_| "request ca")?;
        let n = r
            .bounded_usize(1 << 20, "request proof")
            .map_err(|_| "request proof framing")?;
        let proof = crate::canonical::decode_proof(r.take(n).map_err(|_| "request proof bytes")?)
            .map_err(|_| "request proof")?;
        let proof = Proof {
            c: proof.c,
            z: proof.z,
            orz: proof.orz,
        };
        r.finish().map_err(|_| "request trailing bytes")?;
        if pk == G1::identity() || ca == G1::identity() {
            return Err("request domain");
        }
        Ok(Self(Request { pk, ca, proof }))
    }
}
pub fn respond_received_installed(
    h: &InstalledInstance,
    issuer: &Issuer,
    metadata: &MetadataKey,
    received: ReceivedRequest,
    pol: &Policy,
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<Credential> {
    if issuer.vk != h.issuer.vk || metadata.pk != h.metadata_pk {
        return Err("installed issuer/metadata mismatch");
    }
    respond_internal(
        &h.pp,
        issuer,
        metadata,
        &received.0,
        pol,
        bit,
        rng,
        Some(h),
        true,
    )
}
// The parameter list follows the native multi-party protocol interface; do not regroup its arguments.
#[allow(clippy::too_many_arguments)]
fn respond_internal(
    pp: &Params,
    issuer: &Issuer,
    metadata: &MetadataKey,
    req: &Request,
    pol: &Policy,
    bit: usize,
    rng: &mut impl RngCore,
    installed: Option<&InstalledInstance>,
    decoded_request: bool,
) -> Result<Credential> {
    // Raw public issuer/metadata keys are mutable, so authenticate their
    // actual points before using metadata bases in the encryption proof.
    // Installed callers already require an exact immutable key binding.
    if (installed.is_none()
        && (issuer.vk.iter().any(|&g| !valid2(g, true))
            || metadata.pk[0] == metadata.pk[1]
            || metadata.pk.iter().any(|&g| !valid1(g, true))))
        || bit > 1
        || !verify_request_internal(pp, req, pol, installed, decoded_request)
    {
        return Err("request rejected");
    }
    let r = hash_g1(b"SMA_REQ_G1", &req.bytes());
    let e = g1_mul(r, metadata.sk[bit]);
    let zi = [random_scalar(&mut *rng), random_scalar(&mut *rng)];
    let cf = g1_add(
        req.ca,
        sum1(&[(pp.y[pp.k], zi[0]), (pp.y[pp.k + 1], zi[1])]),
    );
    // E=R^eta is known to the issuer: fuse both message coefficients.
    let y = random_nonzero(rng);
    let iy = inv(y);
    let sig = Signature {
        z: sum1(&[
            (pp.anchor, issuer.sk[0] * y),
            (cf, issuer.sk[1] * y),
            (r, (issuer.sk[2] + metadata.sk[bit] * issuer.sk[3]) * y),
        ]),
        y: g1_mul(G1::generator(), iy),
        yhat: g2_mul(G2::generator(), iy),
    };
    let mut c = Credential {
        sig,
        e,
        ca: req.ca,
        cf,
        zi,
        encryption: empty(),
    };
    c.encryption = encryption_statement(&metadata.pk, r, e).prove_cached(
        b"SMA_ENCRYPT",
        &encryption_external_cached(pp, &issuer.vk, &metadata.pk, req, &c, installed),
        &metadata.sk,
        &[(bit, metadata.sk[bit])],
        rng,
        installed.map(|h| &h.encryption_hash),
    );
    Ok(c)
}
fn checked_credential(
    pp: &Params,
    installed: &InstalledIssuer,
    pkv: &[G1; 2],
    req: &Request,
    c: &Credential,
) -> Option<G1> {
    checked_credential_internal(pp, installed, pkv, req, c, None, None)
}
fn checked_credential_internal(
    pp: &Params,
    installed: &InstalledIssuer,
    pkv: &[G1; 2],
    req: &Request,
    c: &Credential,
    handle: Option<&InstalledInstance>,
    local_ca: Option<G1>,
) -> Option<G1> {
    checked_credential_internal_with_signature(
        pp,
        installed,
        pkv,
        req,
        c,
        handle,
        local_ca,
        verify_installed_signature,
    )
}
#[allow(clippy::too_many_arguments)]
fn checked_credential_internal_with_signature(
    pp: &Params,
    installed: &InstalledIssuer,
    pkv: &[G1; 2],
    req: &Request,
    c: &Credential,
    handle: Option<&InstalledInstance>,
    local_ca: Option<G1>,
    check: impl FnOnce(&InstalledIssuer, &[G1; 4], &Signature) -> bool,
) -> Option<G1> {
    let vk = &installed.vk;
    if (handle.is_none() && !pp.valid())
        || (handle.is_none() && installed.binding != instance(pp, vk))
        || c.ca != req.ca
        || req.ca == G1::identity()
        // Raw wrappers have no local evidence. Mutable RequestState can reuse
        // evidence only for the actual original point, never encoding alone.
        || (local_ca != Some(req.ca) && !valid1(req.ca, true))
        || !valid1(req.pk, true)
        || (handle.is_none() && (pkv[0] == pkv[1] || pkv.iter().any(|&x| !valid1(x, true))))
    {
        return None;
    }
    let r = hash_g1(b"SMA_REQ_G1", &req.bytes());
    if !check(installed, &[pp.anchor, c.cf, r, c.e], &c.sig) {
        return None;
    }
    if !encryption_statement(pkv, r, c.e).verify_cached(
        b"SMA_ENCRYPT",
        &encryption_external_cached(pp, vk, pkv, req, c, handle),
        &c.encryption,
        handle.map(|h| &h.encryption_hash),
    ) {
        return None;
    }
    if c.cf
        != g1_add(
            c.ca,
            sum1(&[(pp.y[pp.k], c.zi[0]), (pp.y[pp.k + 1], c.zi[1])]),
        )
    {
        return None;
    }
    Some(r)
}
pub fn verify_credential(
    pp: &Params,
    installed: &InstalledIssuer,
    pkv: &[G1; 2],
    req: &Request,
    c: &Credential,
) -> bool {
    checked_credential(pp, installed, pkv, req, c).is_some()
}
/// Validate the native issuer response or delivery and obtain holder material.
pub fn receive(
    pp: &Params,
    installed: &InstalledIssuer,
    pkv: &[G1; 2],
    state: RequestState,
    c: &Credential,
) -> Result<Wallet> {
    receive_internal(pp, installed, pkv, state, c, None)
}
pub fn receive_installed(
    h: &InstalledInstance,
    state: RequestState,
    c: &Credential,
) -> Result<Wallet> {
    receive_internal(&h.pp, &h.issuer, &h.metadata_pk, state, c, Some(h))
}
/// Same native acceptance, with its two SPS pairing equations in one SET.
pub fn receive_installed_set(
    h: &InstalledInstance,
    state: RequestState,
    c: &Credential,
    weights: &mut impl RngCore,
) -> Result<Wallet> {
    receive_internal_with_signature(
        &h.pp,
        &h.issuer,
        &h.metadata_pk,
        state,
        c,
        Some(h),
        |vk, m, sig| verify_installed_signature_set(vk, m, sig, weights),
    )
}
/// Decode provenance is private: no received-group membership is repeated.
pub fn receive_received_set(
    h: &InstalledInstance,
    state: RequestState,
    received: ReceivedCredential,
    weights: &mut impl RngCore,
) -> Result<Wallet> {
    receive_internal_with_signature(
        &h.pp,
        &h.issuer,
        &h.metadata_pk,
        state,
        &received.0,
        Some(h),
        |vk, m, sig| {
            m.iter().all(|p| *p != G1::identity())
                && sig.y != G1::identity()
                && sig.yhat != G2::identity()
                && verify_installed_signature_set_body(vk, m, sig, weights)
        },
    )
}
pub fn verify_credential_installed(h: &InstalledInstance, req: &Request, c: &Credential) -> bool {
    checked_credential_internal(&h.pp, &h.issuer, &h.metadata_pk, req, c, Some(h), None).is_some()
}
fn receive_internal(
    pp: &Params,
    installed: &InstalledIssuer,
    pkv: &[G1; 2],
    state: RequestState,
    c: &Credential,
    handle: Option<&InstalledInstance>,
) -> Result<Wallet> {
    receive_internal_with_signature(
        pp,
        installed,
        pkv,
        state,
        c,
        handle,
        verify_installed_signature,
    )
}
#[allow(clippy::too_many_arguments)]
fn receive_internal_with_signature(
    pp: &Params,
    installed: &InstalledIssuer,
    pkv: &[G1; 2],
    state: RequestState,
    c: &Credential,
    handle: Option<&InstalledInstance>,
    check: impl FnOnce(&InstalledIssuer, &[G1; 4], &Signature) -> bool,
) -> Result<Wallet> {
    if state.attrs.len() != pp.k {
        return Err("credential rejected");
    }
    let r = checked_credential_internal_with_signature(
        pp,
        installed,
        pkv,
        &state.request,
        c,
        handle,
        Some(state.local_ca),
        check,
    )
    .ok_or("credential rejected")?;
    Ok(Wallet {
        key: state.key,
        attrs: state.attrs,
        z: [state.zu[0] + c.zi[0], state.zu[1] + c.zi[1]],
        r: state.r,
        m: [pp.anchor, c.cf, r, c.e],
        sig: c.sig.clone(),
        profile: handle.map_or_else(|| instance(pp, &installed.vk), |h| h.instance.clone()),
        installation_binding: handle.map_or_else(
            || local_instance_binding(&instance(pp, &installed.vk), pkv),
            |h| h.installation_binding.clone(),
        ),
    })
}
/// Full request + issuer response + user acceptance; key generation is Setup.
// The parameter list follows the native multi-party protocol interface; do not regroup its arguments.
#[allow(clippy::too_many_arguments)]
/// Execute the native issuer response or complete issuance interface.
pub fn issue(
    pp: &Params,
    issuer: &Issuer,
    metadata: &MetadataKey,
    key: &UserKey,
    attrs: &[S],
    pol: &Policy,
    bit: usize,
    rng: &mut impl RngCore,
) -> Result<(Wallet, Request, Credential)> {
    let (state, req) = request(pp, key, attrs, pol, &mut *rng)?;
    let c = respond(pp, issuer, metadata, &req, pol, bit, &mut *rng)?;
    let installed = install_issuer(pp, issuer)?;
    let wallet = receive(pp, &installed, &metadata.pk, state, &c)?;
    Ok((wallet, req, c))
}

// Fixed shared witnesses: beta,r,z0,z1,x,i,t,gamma,omega,nu; attributes follow.
const FIXED: usize = 10;
fn disclosed(pp: &Params, policy: &Policy) -> Option<Vec<Option<S>>> {
    let mut values = vec![None; pp.k];
    for atom in &policy.atoms {
        match atom {
            Atom::Reveal(i, v) | Atom::Equal(i, v) if *i < pp.k => {
                if values[*i].is_some_and(|x| x != *v) {
                    return None;
                }
                values[*i] = Some(*v);
            }
            // Profile-2's unknown-policy candidate class is Reveal/Equal.
            // Profile-1 remains available for general Linear relations.
            _ => return None,
        }
    }
    // The schema's period coordinate is always disclosed, but its value need
    // not be one and is not supplied to precompute as a future policy.
    values[0]?;
    Some(values)
}
fn bit_relation(pp: &Params, q: G1) -> Or1 {
    Or1 {
        branches: [
            vec![(pp.bit_h, q)],
            vec![(pp.bit_h, g1_add(q, -G1::generator()))],
        ],
    }
}
fn token_external(pp: &Params, vk: &[G2; 4], t: &Token, ctx: &[u8], policy: &Policy) -> Vec<u8> {
    token_external_cached(pp, vk, t, ctx, policy, None)
}
fn token_public_prefix(inst: &[u8]) -> Vec<u8> {
    let mut b = inst.to_vec();
    frame(
        &mut b,
        b"SMA-INV-1/eight-shared-relations/period-index-0/RAW-v2",
    );
    b
}
fn token_external_cached(
    pp: &Params,
    vk: &[G2; 4],
    t: &Token,
    ctx: &[u8],
    policy: &Policy,
    installed: Option<&InstalledInstance>,
) -> Vec<u8> {
    let mut b =
        token_public_prefix(&installed.map_or_else(|| instance(pp, vk), |h| h.instance.clone()));
    frame(&mut b, ctx);
    frame(&mut b, &policy.bytes());
    frame(&mut b, &t.core_bytes());
    // Relation order and witness numbering are fixed by this version identifier.
    // No materialized U_J, K, B or other omitted value replaces these raw fields.
    b
}
fn token_external_prepared(
    pp: &Params,
    vk: &[G2; 4],
    t: &Token,
    ctx: &[u8],
    policy: &Policy,
    installed: Option<&InstalledInstance>,
    cache: &CanonicalPointCache,
) -> Vec<u8> {
    let mut b =
        token_public_prefix(&installed.map_or_else(|| instance(pp, vk), |h| h.instance.clone()));
    frame(&mut b, ctx);
    frame(&mut b, &policy.bytes());
    frame(&mut b, &t.core_bytes_cached(cache));
    b
}
/// No future context/policy is accepted; every nonperiod attribute is prepared.
/// Prepare fresh one-use native token material before presentation context is known.
pub fn precompute(
    pp: &Params,
    vk: &[G2; 4],
    wallet: &Wallet,
    ctr: u64,
    rng: &mut impl RngCore,
) -> Result<Prepared> {
    precompute_internal(pp, vk, wallet, ctr, rng, None)
}
pub fn precompute_installed(
    h: &InstalledInstance,
    wallet: &Wallet,
    ctr: u64,
    rng: &mut impl RngCore,
) -> Result<Prepared> {
    precompute_internal(&h.pp, &h.issuer.vk, wallet, ctr, rng, Some(h))
}
/// Complete the native fixed-policy first-message work before context arrives.
/// The ordinary precompute_installed entry retains the late-policy boundary.
pub fn precompute_policy_installed(
    h: &InstalledInstance,
    wallet: &Wallet,
    ctr: u64,
    policy: &Policy,
    rng: &mut impl RngCore,
) -> Result<Prepared> {
    let mut p = precompute_installed(h, wallet, ctr, rng)?;
    if !policy.satisfied(&p.attrs) {
        return Err("wrong policy");
    }
    let known = disclosed(&h.pp, policy).ok_or("unsupported or missing-period policy")?;
    for (j, value) in known.iter().enumerate() {
        if value.is_none() {
            p.firsts[1] = g1_add(p.firsts[1], p.attribute_firsts[j]);
        }
    }
    p.encodings.insert1(p.firsts[1]);
    for state in &p.ors {
        p.firsts.extend(&state.firsts);
    }
    p.prepared_policy = Some((policy.bytes(), known));
    Ok(p)
}
fn precompute_internal(
    pp: &Params,
    vk: &[G2; 4],
    wallet: &Wallet,
    ctr: u64,
    rng: &mut impl RngCore,
    installed: Option<&InstalledInstance>,
) -> Result<Prepared> {
    let profile = installed.map_or_else(|| instance(pp, vk), |h| h.instance.clone());
    if (installed.is_none() && !pp.valid())
        || (installed.is_none() && vk.iter().any(|&g| !valid2(g, true)))
        || wallet.profile != profile
        || installed.is_some_and(|h| wallet.installation_binding != h.installation_binding)
        || wallet.attrs.len() != pp.k
        || ctr >= pp.n
    {
        return Err("invalid preparation input");
    }
    let i = S::from(ctr);
    let d0 = wallet.z[0] + i;
    let d1 = wallet.z[1] + i;
    if d0 == S::ZERO || d1 == S::ZERO {
        return Err("DY seed pole");
    }
    let gamma = inv(d1);
    let alpha = random_nonzero(rng);
    let psi = random_nonzero(rng);
    let ipsi = inv(psi);
    let serial = g1_mul(G1::generator(), inv(d0));
    let m = wallet.m.map(|x| g1_mul(x, alpha));
    let sig = Signature {
        z: g1_mul(wallet.sig.z, alpha * psi),
        y: g1_mul(wallet.sig.y, ipsi),
        yhat: g2_mul(wallet.sig.yhat, ipsi),
    };
    let pk_prime = g1_mul(wallet.key.pk, alpha);
    let t = random_scalar(rng);
    let q = sum1(&[(G1::generator(), d1), (pp.bit_h, t)]);
    let mut bits = vec![];
    let mut ors = vec![];
    let mut nu = S::ZERO;
    for j in 0..pp.n.trailing_zeros() {
        let bit = ((ctr >> j) & 1) as usize;
        let kappa = random_scalar(rng);
        let ci = g1_add(
            if bit == 0 {
                G1::identity()
            } else {
                G1::generator()
            },
            g1_mul(pp.bit_h, kappa),
        );
        nu += S::from(1u64 << j) * kappa;
        bits.push(ci);
        ors.push(OrPrepared::new(&bit_relation(pp, ci), bit, kappa, rng));
    }
    let token = Token {
        sig,
        m,
        serial,
        d: G1::identity(),
        pk_prime,
        q,
        bits,
        proof: empty(),
    };
    let mut witnesses = vec![
        inv(alpha),
        wallet.r,
        wallet.z[0],
        wallet.z[1],
        wallet.key.sk,
        i,
        t,
        gamma,
        -t * gamma,
        nu,
    ];
    witnesses.extend(&wallet.attrs);
    let nonces: Vec<_> = (0..witnesses.len()).map(|_| random_scalar(rng)).collect();
    let firsts = prepare_firsts(pp, &token, &nonces);
    let mut attribute_firsts = vec![G1::identity(); pp.k];
    for j in 1..pp.k {
        attribute_firsts[j] = g1_mul(pp.y[j], -nonces[FIXED + j]);
    }
    let mut encodings = CanonicalPointCache::new();
    for g in token
        .m
        .into_iter()
        .chain([
            token.sig.z,
            token.sig.y,
            token.serial,
            token.pk_prime,
            token.q,
        ])
        .chain(token.bits.iter().copied())
        .chain(firsts.iter().copied())
        .chain(attribute_firsts.iter().copied())
    {
        encodings.insert1(g);
    }
    encodings.insert2(token.sig.yhat);
    for state in &ors {
        for &g in &state.firsts {
            encodings.insert1(g);
        }
    }
    Ok(Prepared {
        encodings,
        token,
        witnesses,
        nonces,
        firsts,
        attribute_firsts,
        ors,
        attrs: wallet.attrs.clone(),
        pk: wallet.key.pk,
        profile,
        installation_binding: wallet.installation_binding.clone(),
        prepared_policy: None,
    })
}
/// The eight first messages excluding policy-selected attribute factors and D.
/// Equal bases are fused in scalar arithmetic, without leaking any nonce.
fn prepare_firsts(pp: &Params, t: &Token, r: &[S]) -> Vec<G1> {
    let g = G1::generator();
    vec![
        g1_mul(t.m[0], r[0]),
        sum1(&[
            (t.m[1], r[0]),
            (pp.h, -r[1]),
            (pp.y[pp.k], -r[2]),
            (pp.y[pp.k + 1], -r[3]),
            (pp.y[pp.k + 2], -r[4]),
        ]),
        sum1(&[(t.pk_prime, r[0]), (g, -r[4])]),
        g1_mul(t.serial, r[2] + r[5]),
        G1::identity(),
        sum1(&[(g, r[3] + r[5]), (pp.bit_h, r[6])]),
        sum1(&[(t.q, r[7]), (pp.bit_h, r[8])]),
        sum1(&[(g, r[5]), (pp.bit_h, r[9])]),
    ]
}
/// Consume native token preparation while binding its online statement.
pub fn show_online(
    pp: &Params,
    vk: &[G2; 4],
    p: Prepared,
    ctx: &[u8],
    policy: &Policy,
) -> Result<Token> {
    show_online_internal(pp, vk, p, ctx, policy, None)
}
pub fn show_online_installed(
    h: &InstalledInstance,
    p: Prepared,
    ctx: &[u8],
    policy: &Policy,
) -> Result<Token> {
    show_online_internal(&h.pp, &h.issuer.vk, p, ctx, policy, Some(h))
}
pub fn show_installed(
    h: &InstalledInstance,
    wallet: &Wallet,
    ctr: u64,
    ctx: &[u8],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> Result<Token> {
    show_online_installed(h, precompute_installed(h, wallet, ctr, rng)?, ctx, policy)
}
fn show_online_internal(
    pp: &Params,
    vk: &[G2; 4],
    p: Prepared,
    ctx: &[u8],
    policy: &Policy,
    installed: Option<&InstalledInstance>,
) -> Result<Token> {
    // A byte binding alone cannot authenticate public mutable pp/vk: safe
    // unchecked raw points can share a valid point's compressed encoding.
    if (installed.is_none() && (!pp.valid() || vk.iter().any(|&g| !valid2(g, true))))
        || p.profile != installed.map_or_else(|| instance(pp, vk), |h| h.instance.clone())
        || installed.is_some_and(|h| p.installation_binding != h.installation_binding)
        || ctx.is_empty()
        || p.prepared_policy.as_ref().map_or_else(
            || !policy.satisfied(&p.attrs),
            |(binding, _)| *binding != policy.bytes(),
        )
    {
        return Err("wrong profile or policy");
    }
    let policy_prepared = p.prepared_policy.is_some();
    let Prepared {
        encodings,
        mut token,
        witnesses,
        nonces,
        mut firsts,
        attribute_firsts,
        ors,
        pk,
        prepared_policy,
        ..
    } = p;
    let known = match prepared_policy {
        Some((_, known)) => known,
        None => disclosed(pp, policy).ok_or("unsupported or missing-period policy")?,
    };
    let n = hash_scalar(b"SMA2_CTX_FR", ctx);
    // Do not construct B=g^gamma just to immediately raise it to n.
    token.d = g1_add(pk, g1_mul(G1::generator(), n * witnesses[7]));
    firsts[4] = g1_mul(G1::generator(), nonces[4] + n * nonces[7]);
    if !policy_prepared {
        for (j, value) in known.iter().enumerate() {
            if value.is_none() {
                firsts[1] = g1_add(firsts[1], attribute_firsts[j]);
            }
        }
        for state in &ors {
            firsts.extend(&state.firsts);
        }
    }
    let raw = token_external_prepared(pp, vk, &token, ctx, policy, installed, &encodings);
    let c = installed.map_or_else(
        || sma2rt_proof::raw_challenge_cached(b"SMA2_TOKEN", &raw, &firsts, &encodings),
        |h| h.token_hash.challenge_cached(&raw, &firsts, &encodings),
    );

    let mut z: Vec<_> = (0..FIXED).map(|j| nonces[j] + c * witnesses[j]).collect();
    for (j, value) in known.iter().enumerate() {
        if value.is_none() {
            z.push(nonces[FIXED + j] + c * witnesses[FIXED + j]);
        }
    }
    token.proof = Proof {
        c,
        z,
        orz: ors.into_iter().map(|o| o.finish(c)).collect(),
    };
    Ok(token)
}
/// Run native token preparation and online generation.
pub fn show(
    pp: &Params,
    vk: &[G2; 4],
    wallet: &Wallet,
    ctr: u64,
    ctx: &[u8],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> Result<Token> {
    let p = precompute(pp, vk, wallet, ctr, rng)?;
    show_online(pp, vk, p, ctx, policy)
}
fn verification_firsts(
    pp: &Params,
    t: &Token,
    n: S,
    known: &[Option<S>],
    shared_public: Option<G1>,
) -> Option<Vec<G1>> {
    let proof = &t.proof;
    let z = &proof.z;
    let c = proof.c;
    if z.len() != FIXED + known.iter().filter(|v| v.is_none()).count()
        || proof.orz.len() != t.bits.len()
    {
        return None;
    }
    let g = G1::generator();
    let gc = g1_mul(g, c);
    let gx = g1_mul(g, z[4]);
    let mut commitment = vec![
        (t.m[1], z[0]),
        (pp.h, -z[1]),
        (pp.y[pp.k], -z[2]),
        (pp.y[pp.k + 1], -z[3]),
        (pp.y[pp.k + 2], -z[4]),
    ];
    if shared_public.is_none() {
        commitment.push((pp.u, -c));
    }
    let mut offset = FIXED;
    for (j, value) in known.iter().enumerate() {
        if let Some(a) = value {
            if shared_public.is_none() {
                commitment.push((pp.y[j], -*a * c));
            }
        } else {
            commitment.push((pp.y[j], -z[offset]));
            offset += 1;
        }
    }
    let mut commitment_first = sum1(&commitment);
    if let Some(shared) = shared_public {
        commitment_first = g1_add(commitment_first, -g1_mul(shared, c));
    }
    let mut range = vec![(g, z[5]), (pp.bit_h, z[9])];
    range.extend(
        t.bits
            .iter()
            .enumerate()
            .map(|(j, &q)| (q, -S::from(1u64 << j) * c)),
    );
    let mut firsts = vec![
        sum1(&[(t.m[0], z[0]), (pp.anchor, -c)]),
        commitment_first,
        g1_add(g1_mul(t.pk_prime, z[0]), -gx),
        g1_add(g1_mul(t.serial, z[2] + z[5]), -gc),
        sum1(&[(g, z[4] + n * z[7]), (t.d, -c)]),
        sum1(&[(g, z[3] + z[5]), (pp.bit_h, z[6]), (t.q, -c)]),
        g1_add(sum1(&[(t.q, z[7]), (pp.bit_h, z[8])]), -gc),
        sum1(&range),
    ];
    for (&q, z) in t.bits.iter().zip(&proof.orz) {
        firsts.push(sum1(&[(pp.bit_h, z[1]), (q, -z[0])]));
        firsts.push(sum1(&[(pp.bit_h, z[2]), (g1_add(q, -g), -(c - z[0]))]));
    }
    Some(firsts)
}
/// Verify the native complete signature or token equations against the declared statement.
pub fn verify(pp: &Params, vk: &[G2; 4], t: &Token, ctx: &[u8], policy: &Policy) -> bool {
    verify_internal(pp, vk, t, ctx, policy, None, None, None, false)
}
pub fn verify_installed(h: &InstalledInstance, t: &Token, ctx: &[u8], policy: &Policy) -> bool {
    verify_internal(
        &h.pp,
        &h.issuer.vk,
        t,
        ctx,
        policy,
        None,
        None,
        Some(h),
        false,
    )
}
/// Verify a canonically checked token using the installed native public instance.
pub fn verify_checked(
    h: &InstalledInstance,
    t: &CheckedToken,
    ctx: &[u8],
    policy: &Policy,
) -> bool {
    verify_internal(
        &h.pp,
        &h.issuer.vk,
        &t.token,
        ctx,
        policy,
        None,
        None,
        Some(h),
        true,
    )
}
// The parameter list follows the native multi-party protocol interface; do not regroup its arguments.
#[allow(clippy::too_many_arguments)]
fn verify_internal(
    pp: &Params,
    vk: &[G2; 4],
    t: &Token,
    ctx: &[u8],
    policy: &Policy,
    shared: Option<G1>,
    context_hash: Option<S>,
    installed: Option<&InstalledInstance>,
    decoded: bool,
) -> bool {
    verify_relations_internal(
        pp,
        vk,
        t,
        ctx,
        policy,
        shared,
        context_hash,
        installed,
        decoded,
        true,
    )
}
#[allow(clippy::too_many_arguments)]
fn verify_relations_internal(
    pp: &Params,
    vk: &[G2; 4],
    t: &Token,
    ctx: &[u8],
    policy: &Policy,
    shared: Option<G1>,
    context_hash: Option<S>,
    installed: Option<&InstalledInstance>,
    decoded: bool,
    check_signature: bool,
) -> bool {
    if (installed.is_none() && !pp.valid())
        || ctx.is_empty()
        || t.bits.len() != pp.n.trailing_zeros() as usize
        || t.serial == G1::identity()
        || t.pk_prime == G1::identity()
        || (!decoded
            && (!valid1(t.serial, true)
                || !valid1(t.pk_prime, true)
                || ![t.d, t.q].iter().all(|&x| valid1(x, false))
                || t.bits.iter().any(|&x| !valid1(x, false))))
    {
        return false;
    }
    let Some(known) = disclosed(pp, policy) else {
        return false;
    };
    if (check_signature
        && !verify_signature_internal(vk, &t.m, &t.sig, installed.is_some(), decoded))
        || (!check_signature
            && (t.m.iter().any(|&m| m == G1::identity())
                || t.sig.y == G1::identity()
                || t.sig.yhat == G2::identity()
                || (!decoded
                    && (t.m.iter().any(|&m| !valid1(m, true))
                        || !valid1(t.sig.z, false)
                        || !valid1(t.sig.y, true)
                        || !valid2(t.sig.yhat, true)))))
    {
        return false;
    }
    let n = context_hash.unwrap_or_else(|| hash_scalar(b"SMA2_CTX_FR", ctx));
    let Some(firsts) = verification_firsts(pp, t, n, &known, shared) else {
        return false;
    };
    let raw = token_external_cached(pp, vk, t, ctx, policy, installed);
    installed.map_or_else(
        || sma2rt_proof::raw_challenge(b"SMA2_TOKEN", &raw, &firsts),
        |h| h.token_hash.challenge(&raw, &firsts),
    ) == t.proof.c
}
/// Single-token Verify with verifier-random combination of its native pairing equations.
pub fn verify_random_installed(
    h: &InstalledInstance,
    t: &Token,
    ctx: &[u8],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> bool {
    verify_random_many_inner(h, std::slice::from_ref(t), ctx, policy, rng)
}
/// Common-issuer/context native tokens with individual Sigma, FS, policy and
/// counter checks, and independent full-field random FHS pairing aggregation.
pub fn verify_random_batch_installed(
    h: &InstalledInstance,
    tokens: &[Token],
    ctx: &[u8],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> bool {
    if tokens.len() == 1 {
        return verify_random_installed(h, &tokens[0], ctx, policy, rng);
    }
    verify_random_many_inner(h, tokens, ctx, policy, rng)
}
pub fn verify_random_batch_checked(
    h: &InstalledInstance,
    tokens: &[CheckedToken],
    ctx: &[u8],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> bool {
    verify_random_frozen(
        h,
        tokens.iter().map(|t| t.token.clone()).collect(),
        ctx,
        policy,
        true,
        rng,
    )
}
fn verify_random_many_inner(
    h: &InstalledInstance,
    tokens: &[Token],
    ctx: &[u8],
    policy: &Policy,
    rng: &mut impl RngCore,
) -> bool {
    verify_random_frozen(h, tokens.to_vec(), ctx, policy, false, rng)
}
fn verify_random_frozen(
    h: &InstalledInstance,
    frozen: Vec<Token>,
    ctx: &[u8],
    policy: &Policy,
    decoded: bool,
    rng: &mut impl RngCore,
) -> bool {
    if frozen.is_empty() {
        return false;
    }
    if frozen.iter().any(|t| {
        !verify_relations_internal(
            &h.pp,
            &h.issuer.vk,
            t,
            ctx,
            policy,
            None,
            None,
            Some(h),
            decoded,
            false,
        )
    }) {
        return false;
    }
    let mut serials = std::collections::BTreeSet::new();
    if frozen.iter().any(|t| !serials.insert(enc1(t.serial))) {
        return false;
    }
    let statements: Vec<_> = frozen
        .iter()
        .map(|t| crate::batch::FhsStatement {
            message: t.m.to_vec(),
            z: t.sig.z,
            y: t.sig.y,
            yh: t.sig.yhat,
        })
        .collect();
    if decoded {
        crate::batch::fhs_random_checked(&h.issuer.vk, &statements, rng)
    } else {
        crate::batch::fhs_random(&h.issuer.vk, &statements, rng)
    }
}
/// Original ordered recovery: first match returns; full validity is separate.
/// Read native secret metadata after token verification; this function does not repeat full Verify.
pub fn recover_metadata(key: &MetadataKey, t: &Token) -> Option<usize> {
    (0..2).find(|&j| g1_mul(t.m[2], key.sk[j]) == t.m[3])
}
pub fn identify_valid_records(a: &Record, b: &Record) -> Option<G1> {
    if a.token.serial != b.token.serial || a.context == b.context {
        return None;
    }
    let n1 = hash_scalar(b"SMA2_CTX_FR", &a.context);
    let n2 = hash_scalar(b"SMA2_CTX_FR", &b.context);
    identify_with_hashes(a, b, n1, n2)
}
fn identify_with_hashes(a: &Record, b: &Record, n1: S, n2: S) -> Option<G1> {
    if n1 == n2 || a.token.serial != b.token.serial || a.context == b.context {
        return None;
    }
    let inverse = inv(n2 - n1);
    Some(sum1(&[
        (a.token.d, n2 * inverse),
        (b.token.d, -n1 * inverse),
    ]))
}
/// Full public Judge. Equal disclosed values share one public product only
/// within this execution; both signature and all proof checks still execute.
/// Validate the native record pair before extracting its responsibility key.
pub fn judge(pp: &Params, vk: &[G2; 4], a: &Record, b: &Record) -> Option<G1> {
    judge_internal(pp, vk, a, b, None)
}
pub fn judge_installed(h: &InstalledInstance, a: &Record, b: &Record) -> Option<G1> {
    judge_internal(&h.pp, &h.issuer.vk, a, b, Some(h))
}
fn judge_internal(
    pp: &Params,
    vk: &[G2; 4],
    a: &Record,
    b: &Record,
    installed: Option<&InstalledInstance>,
) -> Option<G1> {
    if installed.is_none() && !pp.valid() {
        return None;
    }
    let left = disclosed(pp, &a.policy)?;
    let right = disclosed(pp, &b.policy)?;
    let shared = if left == right {
        Some(g1_add(
            pp.u,
            sum1(
                &left
                    .iter()
                    .enumerate()
                    .filter_map(|(j, v)| v.map(|x| (pp.y[j], x)))
                    .collect::<Vec<_>>(),
            ),
        ))
    } else {
        None
    };
    let n1 = hash_scalar(b"SMA2_CTX_FR", &a.context);
    let n2 = hash_scalar(b"SMA2_CTX_FR", &b.context);
    if !verify_internal(
        pp,
        vk,
        &a.token,
        &a.context,
        &a.policy,
        shared,
        Some(n1),
        installed,
        false,
    ) || !verify_internal(
        pp,
        vk,
        &b.token,
        &b.context,
        &b.policy,
        shared,
        Some(n2),
        installed,
        false,
    ) {
        return None;
    }
    identify_with_hashes(a, b, n1, n2)
}

#[cfg(test)]
mod adversarial_shared_witnesses {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn issuer_known_metadata_fusion_preserves_signature_at_same_random_tape() {
        let mut rng = StdRng::seed_from_u64(112514);
        let pp = setup(10, 1024);
        let issuer = ikeygen(&pp, &mut rng);
        let metadata = vkeygen(&pp, &mut rng);
        let key = ukeygen(&mut rng);
        let attrs: Vec<_> = (0..10).map(|j| S::from(7 + j)).collect();
        let pol = Policy::default();
        let (_, request) = request(&pp, &key, &attrs, &pol, &mut rng).unwrap();
        for bit in 0..2 {
            let mut reference = rng.clone();
            let r = hash_g1(b"SMA_REQ_G1", &request.bytes());
            let zi = [random_scalar(&mut reference), random_scalar(&mut reference)];
            let cf = g1_add(
                request.ca,
                sum1(&[(pp.y[pp.k], zi[0]), (pp.y[pp.k + 1], zi[1])]),
            );
            let e = g1_mul(r, metadata.sk[bit]);
            let sig = sign(&issuer.sk, &[pp.anchor, cf, r, e], &mut reference);
            let fused = respond(&pp, &issuer, &metadata, &request, &pol, bit, &mut rng).unwrap();
            assert_eq!(fused.zi, zi);
            assert_eq!(fused.cf, cf);
            assert_eq!(fused.e, e);
            assert_eq!(fused.sig.bytes(), sig.bytes());
        }
    }
    fn rebind_points(pp: &Params, p: &mut Prepared) {
        let w = &mut p.witnesses;
        p.token.serial = g1_mul(G1::generator(), inv(w[2] + w[5]));
        let denominator = w[3] + w[5];
        w[7] = if denominator == S::ZERO {
            S::from(3)
        } else {
            inv(denominator)
        };
        w[8] = -w[6] * w[7];
        p.token.q = sum1(&[(G1::generator(), denominator), (pp.bit_h, w[6])]);
        p.firsts = prepare_firsts(pp, &p.token, &p.nonces);
    }
    #[test]
    fn recomputed_fs_does_not_hide_inconsistent_secrets_ctr_or_opening() {
        let mut rng = StdRng::seed_from_u64(0xBAD514);
        let pp = setup(10, 1024);
        let issuer = ikeygen(&pp, &mut rng);
        let metadata = vkeygen(&pp, &mut rng);
        let key = ukeygen(&mut rng);
        let attrs: Vec<_> = (0..10).map(|j| S::from(7 + j)).collect();
        let (wallet, _, _) = issue(
            &pp,
            &issuer,
            &metadata,
            &key,
            &attrs,
            &Policy::default(),
            0,
            &mut rng,
        )
        .unwrap();
        let policy = Policy {
            atoms: (0..3).map(|j| Atom::Reveal(j, attrs[j])).collect(),
        };
        for case in 0..7 {
            let mut prepared = precompute(&pp, &issuer.vk, &wallet, 0, &mut rng).unwrap();
            match case {
                0 => {}                              // full honest control
                1 => prepared.pk += G1::generator(), // D uses x+1; CF/pk' use x
                2 => {
                    // pk' uses x+1; CF/D use x
                    prepared.token.pk_prime += g1_mul(G1::generator(), inv(prepared.witnesses[0]));
                    prepared.firsts = prepare_firsts(&pp, &prepared.token, &prepared.nonces);
                }
                3 => {
                    prepared.witnesses[2] += S::ONE;
                    rebind_points(&pp, &mut prepared);
                } // S seed differs from CF
                4 => {
                    prepared.witnesses[3] += S::ONE;
                    rebind_points(&pp, &mut prepared);
                } // inverse seed differs from CF
                5 => {
                    prepared.witnesses[5] = S::from(1024);
                    rebind_points(&pp, &mut prepared);
                } // same i in S/Q but ten-bit ORs still represent zero
                6 => prepared.witnesses[9] += S::ONE, // wrong aggregate opening, valid individual ORs
                _ => unreachable!(),
            }
            let token =
                show_online(&pp, &issuer.vk, prepared, b"malicious fresh FS", &policy).unwrap();
            assert_eq!(
                verify(&pp, &issuer.vk, &token, b"malicious fresh FS", &policy),
                case == 0,
                "case {case}"
            );
        }
        // A fully issuer-signed credential with z1=0 is not enough to make an
        // inverse proof at ctr=0. Unlike byte mutation, CF/signature are valid.
        let mut pole = wallet.clone();
        pole.m[1] = g1_add(pole.m[1], g1_mul(pp.y[pp.k + 1], -pole.z[1]));
        pole.z[1] = S::ZERO;
        pole.sig = sign(&issuer.sk, &pole.m, &mut rng);
        assert!(precompute(&pp, &issuer.vk, &pole, 0, &mut rng).is_err());
        let mut forged = precompute(&pp, &issuer.vk, &pole, 1, &mut rng).unwrap();
        forged.witnesses[5] = S::ZERO;
        forged.witnesses[9] = S::ZERO;
        forged.token.bits.clear();
        forged.ors.clear();
        for j in 0..pp.n.ilog2() {
            let kappa = random_scalar(&mut rng);
            let point = g1_mul(pp.bit_h, kappa);
            forged.witnesses[9] += S::from(1u64 << j) * kappa;
            forged.token.bits.push(point);
            forged.ors.push(OrPrepared::new(
                &bit_relation(&pp, point),
                0,
                kappa,
                &mut rng,
            ));
        }
        rebind_points(&pp, &mut forged);
        let forged = show_online(&pp, &issuer.vk, forged, b"pole", &policy).unwrap();
        assert!(!verify(&pp, &issuer.vk, &forged, b"pole", &policy));
        let mut pole0 = wallet.clone();
        pole0.z[0] = S::ZERO;
        assert!(precompute(&pp, &issuer.vk, &pole0, 0, &mut rng).is_err());
    }
}
