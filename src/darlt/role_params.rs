//! Role-specific parameter distribution, with an authenticated Setup manifest.
//!
//! The full Setup digest remains the protocol identifier. Each role receives
//! only its algorithm's points; the separate trusted manifest authenticates
//! that projection without sending the complete Setup encoding to that role.
//! Issuer keys and their knowledge proof are separate from these parameters.
use super::{
    params::{Dimensions, ReferenceString},
    protocol::{
        self, Holder, IssueRequest, IssueResponse, IssuerPublic, IssuerSecret, PublicParameters,
    },
    spend::{self, Policy, PreparedSpend, Token},
    verification::Mode,
};
use crate::{
    polynomial::{Domain, S},
    spseq_fc,
};
use blstrs::{G1Projective as G1, G2Projective as G2};
use group::Group;
use rand::RngCore;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

const HEADER: &[u8] = b"DARLT/role-parameters/encoding";
type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Role {
    User,
    Issuer,
    Agent,
    Verifier,
}
impl Role {
    pub fn name(self) -> &'static str {
        match self {
            Self::User => "user",
            Self::Issuer => "issuer",
            Self::Agent => "agent",
            Self::Verifier => "verifier",
        }
    }
    fn tag(self) -> u8 {
        match self {
            Self::User => 1,
            Self::Issuer => 2,
            Self::Agent => 3,
            Self::Verifier => 4,
        }
    }
    fn proves(self) -> bool {
        matches!(self, Self::User | Self::Agent)
    }
}

/// This small record is authenticated by the same honest Setup distribution
/// as the full public-parameter identifier. A role never accepts an untrusted
/// packet merely because it carries its own self-chosen hash.
#[derive(Clone, Debug)]
pub struct RoleManifest {
    pub role: Role,
    pub pp_id: [u8; 32],
    pub package_sha256: [u8; 32],
}

impl RoleManifest {
    /// Role byte, full Setup identifier and projection hash. This descriptor
    /// is distributed through the trusted Setup channel, outside the packet.
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        let mut bytes = vec![self.role.tag()];
        bytes.extend(self.pp_id);
        bytes.extend(self.package_sha256);
        bytes
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ParameterField {
    pub name: &'static str,
    pub object_type: &'static str,
    pub objects: usize,
    pub point_bytes: usize,
    pub framing_bytes: usize,
    pub derived_cache: bool,
}

/// Contains a real reduced runtime view, not a count of hypothetical points.
/// The underlying full-role facade is left unchanged; these narrow wrappers
/// call the same installed algorithms using the decoded reduced view.
pub struct RoleParameters {
    role: Role,
    pp: PublicParameters,
    manifest: RoleManifest,
}
impl RoleParameters {
    /// Internal role dispatch uses this decoded reduced view, so an agent
    /// does not silently fall back to the full Setup package in experiments.
    pub(crate) fn runtime_view(&self) -> &PublicParameters {
        &self.pp
    }
    /// Project an honest Setup result. User includes local self-spending;
    /// agent excludes owner-only private-attribute opening bases.
    pub fn from_setup(pp: &PublicParameters, role: Role) -> Result<Self> {
        if pp.id != <[u8; 32]>::from(Sha256::digest(pp.encode())) {
            return Err("Setup parameter digest rejected".into());
        }
        let projected = project(pp, role)?;
        let bytes = encode(&projected, role);
        let manifest = RoleManifest {
            role,
            pp_id: pp.id,
            package_sha256: Sha256::digest(&bytes).into(),
        };
        Self::decode(&bytes, &manifest)
    }

    /// Strict decoding against an externally trusted role manifest. The
    /// complete full-Setup encoding is not part of this packet or decoder.
    pub fn decode(bytes: &[u8], trusted: &RoleManifest) -> Result<Self> {
        let _span = crate::darlt::instrumentation::span("strict_decoding");
        let _parameter_span = crate::darlt::instrumentation::span("parameter_installation");
        if trusted.package_sha256 != <[u8; 32]>::from(Sha256::digest(bytes)) {
            return Err("role parameter package fingerprint rejected".into());
        }
        let mut r = Reader { bytes, offset: 0 };
        if r.take(HEADER.len())? != HEADER || r.take(1)?[0] != trusted.role.tag() {
            return Err("role parameter version/role rejected".into());
        }
        if r.take(32)? != trusted.pp_id {
            return Err("role parameter Setup identifier rejected".into());
        }
        let dims = (0..9).map(|_| r.usize()).collect::<Result<Vec<_>>>()?;
        let [n, s, w, k_max, k_del, k_prv, table_size, table_n, degree]: [usize; 9] =
            dims.try_into().map_err(|_| "role parameter dimensions")?;
        let dim = Dimensions::new(w, s, k_max)?;
        if w.checked_mul(s) != Some(n)
            || k_del == 0
            || k_del > 128
            || k_prv > 128
            || (table_size, table_n, degree) != (dim.table_size, dim.n, dim.degree)
        {
            return Err("role parameter dimensions rejected".into());
        }
        let mut pp = empty_parameters(n, s, w, k_max, k_del, k_prv, trusted.pp_id)?;
        let specs = g1_specs(trusted.role, &pp);
        if r.usize()? != specs.len() {
            return Err("role G1 field count rejected".into());
        }
        for (tag, _, count) in specs {
            if r.take(1)?[0] != tag || r.usize()? != count {
                return Err("role G1 field shape rejected".into());
            }
            let points = (0..count).map(|_| r.g1()).collect::<Result<Vec<_>>>()?;
            set_g1(&mut pp, tag, points)?;
        }
        let sparse_count = if trusted.role == Role::Issuer { 0 } else { 7 };
        if r.usize()? != sparse_count {
            return Err("role sparse G2 count rejected".into());
        }
        if sparse_count != 0 {
            for index in sparse_indices(&pp) {
                if r.usize()? != index {
                    return Err("role sparse G2 index rejected".into());
                }
                pp.srs.g2.insert(index, r.g2()?);
            }
        }
        for tag in 14..=16 {
            let expected = if trusted.role.proves() {
                match tag {
                    14 => w.max(s),
                    15 => w,
                    _ => s,
                }
            } else {
                0
            };
            if r.usize()? != expected {
                return Err("role advice G2 count rejected".into());
            }
            let points = (0..expected).map(|_| r.g2()).collect::<Result<Vec<_>>>()?;
            match tag {
                14 => pp.srs.k_hat = points,
                15 => pp.srs.d_hat = points,
                _ => pp.srs.o_hat = points,
            }
        }
        let query_sizes = if trusted.role == Role::Issuer {
            vec![]
        } else {
            query_sizes(&pp)
        };
        if r.usize()? != query_sizes.len() {
            return Err("role query cache count rejected".into());
        }
        for size in query_sizes {
            if r.usize()? != size || r.usize()? != size {
                return Err("role query cache shape rejected".into());
            }
            let bases = (0..size).map(|_| r.g1()).collect::<Result<Vec<_>>>()?;
            let z = r.g1()?;
            pp.query_bases.insert(size, (bases, z));
        }
        pp.ghat = pp.srs.g1.first().copied().unwrap_or(G1::identity());
        // The pool bases are one transmitted field shared by both names.
        pp.srs.lagrange = pp.fc.pools.clone();
        let package = Self {
            role: trusted.role,
            pp,
            manifest: trusted.clone(),
        };
        if r.offset != bytes.len() || package.encode() != bytes {
            return Err("noncanonical/trailing role parameter bytes".into());
        }
        Ok(package)
    }
    pub fn role(&self) -> Role {
        self.role
    }
    pub fn manifest(&self) -> RoleManifest {
        self.manifest.clone()
    }
    pub fn encode(&self) -> Vec<u8> {
        let _span = crate::darlt::instrumentation::span("encoding");
        encode(&self.pp, self.role)
    }
    pub fn fields(&self) -> Vec<ParameterField> {
        fields(&self.pp, self.role)
    }
    pub fn header_bytes(&self) -> usize {
        HEADER.len() + 1 + 32 + 9 * 8
    }
    pub fn dimensions(&self) -> [usize; 9] {
        [
            self.pp.n,
            self.pp.s,
            self.pp.w,
            self.pp.k_max,
            self.pp.k_del,
            self.pp.k_prv,
            self.pp.srs.domain.size,
            self.pp.srs.n,
            self.pp.srs.degree,
        ]
    }

    /// Validate the issuer PoK once and bind the key to this installed role.
    pub fn install_issuer<'a>(
        &'a self,
        ip: &'a IssuerPublic,
    ) -> Result<InstalledRoleParameters<'a>> {
        protocol::install(&self.pp, ip)?;
        Ok(InstalledRoleParameters {
            parameters: self,
            issuer: ip,
        })
    }
}

/// Both the reduced Setup view and the issuer key have been accepted once.
/// The issuer key cannot be substituted at a hot algorithm entry point.
pub struct InstalledRoleParameters<'a> {
    parameters: &'a RoleParameters,
    issuer: &'a IssuerPublic,
}
impl InstalledRoleParameters<'_> {
    pub fn issue(
        &self,
        secret: &IssuerSecret,
        request: &IssueRequest,
        bit: usize,
        rng: &mut impl RngCore,
    ) -> Result<IssueResponse> {
        if self.parameters.role != Role::Issuer {
            return Err("issuance requires issuer parameters".into());
        }
        protocol::issue(&self.parameters.pp, self.issuer, secret, request, bit, rng)
    }
    pub fn prepare_spend<'a>(
        &self,
        holder: &'a mut Holder,
        positions: &[usize],
        policy: &Policy,
        rng: &mut impl RngCore,
    ) -> Result<PreparedSpend<'a>> {
        if !self.parameters.role.proves() {
            return Err("spending requires prover parameters".into());
        }
        if self.parameters.role == Role::Agent && holder.is_owner() {
            return Err("owner spending requires user parameters".into());
        }
        spend::prepare_spend_installed(
            &self.parameters.pp,
            self.issuer,
            holder,
            positions,
            policy,
            rng,
        )
    }
    pub fn finish_spend(
        &self,
        prepared: PreparedSpend<'_>,
        context: &[u8],
        rng: &mut impl RngCore,
    ) -> Result<Token> {
        if !self.parameters.role.proves() {
            return Err("spending requires prover parameters".into());
        }
        spend::finish_spend(&self.parameters.pp, self.issuer, prepared, context, rng)
    }
    pub fn valid(&self, token: &Token, mode: Mode, rng: &mut impl RngCore) -> bool {
        self.parameters.role == Role::Verifier
            && spend::valid_installed(&self.parameters.pp, self.issuer, token, mode, rng)
    }
    #[allow(clippy::too_many_arguments)]
    pub fn judge(
        &self,
        a: &Token,
        ai: usize,
        b: &Token,
        bi: usize,
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Option<(spend::Responsibility, G1)> {
        if !self.valid(a, mode, rng) || !self.valid(b, mode, rng) {
            return None;
        }
        spend::identify_validated(&self.parameters.pp, self.issuer, a, ai, b, bi)
    }
    #[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
    pub fn read_bit(
        &self,
        token: &Token,
        secrets: &[S; 2],
        mode: Mode,
        rng: &mut impl RngCore,
    ) -> Option<usize> {
        if !self.valid(token, mode, rng)
            || secrets.map(|x| G1::generator() * x) != self.issuer.metadata_keys
        {
            return None;
        }
        let found: Vec<_> = (0..2)
            .filter(|i| token.auth.message[4] * secrets[*i] == token.auth.message[5])
            .collect();
        (found.len() == 1).then(|| found[0])
    }
    pub fn decode_token(&self, bytes: &[u8]) -> Result<Token> {
        if self.parameters.role != Role::Verifier {
            return Err("token decoding requires verifier parameters".into());
        }
        Token::wire_decode(&self.parameters.pp, bytes)
    }
}

fn query_sizes(pp: &PublicParameters) -> Vec<usize> {
    (0..=pp.srs.k_padded.trailing_zeros())
        .map(|j| 1usize << j)
        .collect()
}
fn sparse_indices(pp: &PublicParameters) -> [usize; 7] {
    [
        0,
        1,
        2,
        3,
        pp.srs.n,
        pp.srs.degree - pp.srs.n + 2,
        pp.srs.degree - pp.srs.n + 4,
    ]
}
fn g1_specs(role: Role, pp: &PublicParameters) -> Vec<(u8, &'static str, usize)> {
    let mut fields = Vec::new();
    let mut add = |tag, name, count| {
        if count != 0 {
            fields.push((tag, name, count));
        }
    };
    add(
        1,
        "G1 monomial SRS",
        match role {
            Role::Issuer => 0,
            Role::Verifier => 3,
            _ => pp.srs.degree + 1,
        },
    );
    add(2, "SPSEQ-FC u", 1);
    add(3, "authorization h0", 1);
    add(4, "grant-bit bases", pp.k_del);
    add(
        5,
        "pool Lagrange bases",
        if role == Role::Verifier { 0 } else { pp.w },
    );
    add(6, "table vanishing Z_H", 1);
    add(7, "offset table Theta", usize::from(role != Role::Issuer));
    add(8, "range blinding h", usize::from(role != Role::Issuer));
    add(9, "delegatable blinding h_del", 1);
    add(10, "delegatable attribute bases", pp.k_del);
    add(
        11,
        "private blinding h_prv",
        usize::from(role != Role::Agent),
    );
    add(
        12,
        "private attribute bases",
        if role == Role::Agent { 0 } else { pp.k_prv },
    );
    add(
        13,
        "accountability authorization bases",
        if role == Role::Issuer { 0 } else { pp.k_del },
    );
    fields
}
fn get_g1(pp: &PublicParameters, tag: u8) -> Vec<G1> {
    match tag {
        1 => pp.srs.g1.clone(),
        2 => vec![pp.fc.u],
        3 => vec![pp.fc.h0],
        4 => pp.fc.attrs.clone(),
        5 => pp.fc.pools.clone(),
        6 => vec![pp.srs.vanishing],
        7 => vec![pp.srs.offset],
        8 => vec![pp.h],
        9 => vec![pp.hdel],
        10 => pp.adel.clone(),
        11 => vec![pp.hprv],
        12 => pp.bprv.clone(),
        13 => pp.grant_bases.clone(),
        _ => unreachable!(),
    }
}
fn set_g1(pp: &mut PublicParameters, tag: u8, points: Vec<G1>) -> Result<()> {
    match tag {
        1 => pp.srs.g1 = points,
        2 => pp.fc.u = points[0],
        3 => pp.fc.h0 = points[0],
        4 => pp.fc.attrs = points,
        5 => pp.fc.pools = points,
        6 => pp.srs.vanishing = points[0],
        7 => pp.srs.offset = points[0],
        8 => pp.h = points[0],
        9 => pp.hdel = points[0],
        10 => pp.adel = points,
        11 => pp.hprv = points[0],
        12 => pp.bprv = points,
        13 => pp.grant_bases = points,
        _ => return Err("unknown parameter field".into()),
    }
    Ok(())
}
#[allow(clippy::too_many_arguments)]
fn empty_parameters(
    n: usize,
    s: usize,
    w: usize,
    k_max: usize,
    k_del: usize,
    k_prv: usize,
    id: [u8; 32],
) -> Result<PublicParameters> {
    let dim = Dimensions::new(w, s, k_max)?;
    Ok(PublicParameters {
        n,
        s,
        w,
        k_max,
        k_del,
        k_prv,
        srs: ReferenceString {
            domain: Domain::new(dim.table_size)?,
            degree: dim.degree,
            n: dim.n,
            w,
            s,
            k_max,
            k_padded: dim.k_padded,
            g1: vec![],
            g2: BTreeMap::new(),
            lagrange: vec![],
            vanishing: G1::identity(),
            k_hat: vec![],
            d_hat: vec![],
            o_hat: vec![],
            offset: G1::identity(),
        },
        fc: spseq_fc::Params {
            u: G1::identity(),
            h0: G1::identity(),
            attrs: vec![],
            pools: vec![],
        },
        ghat: G1::identity(),
        h: G1::identity(),
        hdel: G1::identity(),
        adel: vec![],
        hprv: G1::identity(),
        bprv: vec![],
        grant_bases: vec![],
        query_bases: BTreeMap::new(),
        id,
    })
}
fn project(pp: &PublicParameters, role: Role) -> Result<PublicParameters> {
    let mut projected = empty_parameters(pp.n, pp.s, pp.w, pp.k_max, pp.k_del, pp.k_prv, pp.id)?;
    for (tag, _, count) in g1_specs(role, pp) {
        let mut points = get_g1(pp, tag);
        if tag == 1 {
            points.truncate(count);
        }
        if points.len() != count {
            return Err("Setup field dimensions rejected".into());
        }
        set_g1(&mut projected, tag, points)?;
    }
    projected.ghat = projected.srs.g1.first().copied().unwrap_or(G1::identity());
    projected.srs.lagrange = projected.fc.pools.clone();
    if role != Role::Issuer {
        projected.srs.g2 = pp.srs.g2.clone();
        projected.query_bases = pp.query_bases.clone();
    }
    if role.proves() {
        projected.srs.k_hat = pp.srs.k_hat.clone();
        projected.srs.d_hat = pp.srs.d_hat.clone();
        projected.srs.o_hat = pp.srs.o_hat.clone();
    }
    Ok(projected)
}
fn encode(pp: &PublicParameters, role: Role) -> Vec<u8> {
    let _span = crate::darlt::instrumentation::span("encoding");
    let mut bytes = HEADER.to_vec();
    bytes.push(role.tag());
    bytes.extend(pp.id);
    for value in [
        pp.n,
        pp.s,
        pp.w,
        pp.k_max,
        pp.k_del,
        pp.k_prv,
        pp.srs.domain.size,
        pp.srs.n,
        pp.srs.degree,
    ] {
        bytes.extend((value as u64).to_be_bytes());
    }
    let specs = g1_specs(role, pp);
    bytes.extend((specs.len() as u64).to_be_bytes());
    for (tag, _, _) in specs {
        let points = get_g1(pp, tag);
        bytes.push(tag);
        bytes.extend((points.len() as u64).to_be_bytes());
        for point in points {
            bytes.extend(point.to_compressed());
        }
    }
    bytes.extend((pp.srs.g2.len() as u64).to_be_bytes());
    for (index, point) in &pp.srs.g2 {
        bytes.extend((*index as u64).to_be_bytes());
        bytes.extend(point.to_compressed());
    }
    for points in [&pp.srs.k_hat, &pp.srs.d_hat, &pp.srs.o_hat] {
        bytes.extend((points.len() as u64).to_be_bytes());
        for point in points {
            bytes.extend(point.to_compressed());
        }
    }
    bytes.extend((pp.query_bases.len() as u64).to_be_bytes());
    for (size, (bases, vanishing)) in &pp.query_bases {
        bytes.extend((*size as u64).to_be_bytes());
        bytes.extend((bases.len() as u64).to_be_bytes());
        for base in bases {
            bytes.extend(base.to_compressed());
        }
        bytes.extend(vanishing.to_compressed());
    }
    bytes
}
fn fields(pp: &PublicParameters, role: Role) -> Vec<ParameterField> {
    let mut fields = vec![ParameterField {
        name: "G1 field-count frame",
        object_type: "frame",
        objects: 0,
        point_bytes: 0,
        framing_bytes: 8,
        derived_cache: false,
    }];
    for (_, name, count) in g1_specs(role, pp) {
        fields.push(ParameterField {
            name,
            object_type: "G1",
            objects: count,
            point_bytes: count * 48,
            framing_bytes: 9,
            derived_cache: false,
        });
    }
    fields.push(ParameterField {
        name: "sparse G2 SRS",
        object_type: "G2",
        objects: pp.srs.g2.len(),
        point_bytes: pp.srs.g2.len() * 96,
        framing_bytes: 8 + pp.srs.g2.len() * 8,
        derived_cache: false,
    });
    for (name, points) in [
        ("K_hat", &pp.srs.k_hat),
        ("D_hat", &pp.srs.d_hat),
        ("O_hat", &pp.srs.o_hat),
    ] {
        fields.push(ParameterField {
            name,
            object_type: "G2",
            objects: points.len(),
            point_bytes: points.len() * 96,
            framing_bytes: 8,
            derived_cache: false,
        });
    }
    let cache_g1: usize = pp
        .query_bases
        .values()
        .map(|(bases, _)| bases.len() + 1)
        .sum();
    fields.push(ParameterField {
        name: "query bases and vanishing cache",
        object_type: "G1",
        objects: cache_g1,
        point_bytes: cache_g1 * 48,
        framing_bytes: 8 + pp.query_bases.len() * 16,
        derived_cache: true,
    });
    fields
}
struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}
impl<'a> Reader<'a> {
    fn take(&mut self, size: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(size)
            .ok_or("role packet length overflow")?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or("truncated role packet")?;
        self.offset = end;
        Ok(bytes)
    }
    fn usize(&mut self) -> Result<usize> {
        usize::try_from(u64::from_be_bytes(
            self.take(8)?.try_into().map_err(|_| "integer frame")?,
        ))
        .map_err(|_| "role packet integer overflow".into())
    }
    fn g1(&mut self) -> Result<G1> {
        let _span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
        let bytes: [u8; 48] = self.take(48)?.try_into().map_err(|_| "G1 frame")?;
        Option::from(G1::from_compressed(&bytes)).ok_or("invalid role G1 encoding/subgroup".into())
    }
    fn g2(&mut self) -> Result<G2> {
        let _span = crate::darlt::instrumentation::span("point_decode_and_subgroup");
        let bytes: [u8; 96] = self.take(96)?.try_into().map_err(|_| "G2 frame")?;
        Option::from(G2::from_compressed(&bytes)).ok_or("invalid role G2 encoding/subgroup".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        darlt::{context::ProtocolContext, spend::Atom},
        polynomial::S,
    };
    use ff::Field;
    use rand::{rngs::StdRng, SeedableRng};
    use std::sync::Arc;

    #[test]
    fn reduced_packages_round_trip_and_are_executed_by_their_roles() {
        let mut rng = StdRng::seed_from_u64(2_071);
        let full =
            Arc::new(PublicParameters::setup(16, 4, 8, 2, 1, b"role-test", &mut rng).unwrap());
        let (ip, sk) = protocol::keygen(&full, &mut rng).unwrap();
        let ctx = ProtocolContext::new(full.clone(), Arc::new(ip.clone())).unwrap();
        let user = RoleParameters::from_setup(&full, Role::User).unwrap();
        let issuer = RoleParameters::from_setup(&full, Role::Issuer).unwrap();
        let agent = RoleParameters::from_setup(&full, Role::Agent).unwrap();
        let verifier = RoleParameters::from_setup(&full, Role::Verifier).unwrap();
        for p in [&user, &issuer, &agent, &verifier] {
            p.install_issuer(&ip).unwrap();
            let encoded = p.encode();
            assert_eq!(
                p.header_bytes()
                    + p.fields()
                        .iter()
                        .map(|f| f.point_bytes + f.framing_bytes)
                        .sum::<usize>(),
                encoded.len()
            );
            assert_eq!(
                RoleParameters::decode(&encoded, &p.manifest())
                    .unwrap()
                    .encode(),
                encoded
            );
            assert!(encoded.len() < full.encode().len());
        }
        assert!(issuer.pp.srs.g1.is_empty() && issuer.pp.srs.g2.is_empty());
        assert_eq!(verifier.pp.srs.g1.len(), 3);
        assert!(verifier.pp.fc.pools.is_empty() && verifier.pp.srs.k_hat.is_empty());
        assert!(agent.pp.bprv.is_empty());
        let (request, secret) = protocol::prepare_request(
            &user.pp,
            &ip,
            S::from(19),
            &[S::ONE, S::from(21)],
            &[S::from(7)],
            &mut rng,
        )
        .unwrap();
        let issuer_installed = issuer.install_issuer(&ip).unwrap();
        let user_installed = user.install_issuer(&ip).unwrap();
        let agent_installed = agent.install_issuer(&ip).unwrap();
        let verifier_installed = verifier.install_issuer(&ip).unwrap();
        let response = issuer_installed.issue(&sk, &request, 1, &mut rng).unwrap();
        let mut wallet =
            protocol::accept(&user.pp, &ip, &request, &secret, &response, &mut rng).unwrap();
        ctx.register_wallet(&wallet).unwrap();
        let mut child = ctx
            .self_derive(&mut wallet, b"self-role", &[0, 1], &mut rng)
            .unwrap()
            .holder;
        let policy = Policy {
            period: 1,
            atoms: vec![Atom::Equal(0, S::ONE), Atom::Equal(2, S::from(7))],
        };
        let preparation = user_installed
            .prepare_spend(&mut child, &[0, 1], &policy, &mut rng)
            .unwrap();
        let token = user_installed
            .finish_spend(preparation, b"role-ctx", &mut rng)
            .unwrap();
        let parsed = verifier_installed
            .decode_token(&token.wire_encode())
            .unwrap();
        assert!(verifier_installed.valid(&parsed, Mode::Specification, &mut rng));
        assert!(verifier_installed.valid(&parsed, Mode::Randomized, &mut rng));
        assert!(ctx.valid(&parsed, Mode::Specification, &mut rng));
        assert_eq!(
            verifier_installed.read_bit(
                &parsed,
                &sk.metadata_secrets,
                Mode::Specification,
                &mut rng
            ),
            Some(1)
        );
        let preparation = user_installed
            .prepare_spend(&mut child, &[0, 1], &policy, &mut rng)
            .unwrap();
        let second = user_installed
            .finish_spend(preparation, b"role-ctx-B", &mut rng)
            .unwrap();
        assert_eq!(
            verifier_installed.judge(&parsed, 0, &second, 0, Mode::Specification, &mut rng),
            Some((
                spend::Responsibility::DoubleUse,
                G1::generator() * S::from(19)
            ))
        );

        let delivery = protocol::derive(
            &user.pp,
            &mut wallet,
            G1::generator() * S::from(31),
            &[2],
            &[true, true],
            &mut rng,
        )
        .unwrap();
        let mut remote = protocol::complete(
            &agent.pp,
            &ip,
            &delivery,
            S::from(31),
            None,
            Mode::Specification,
            &mut rng,
        )
        .unwrap();
        let policy = Policy {
            period: 1,
            atoms: vec![Atom::Equal(0, S::ONE)],
        };
        let preparation = agent_installed
            .prepare_spend(&mut remote, &[8], &policy, &mut rng)
            .unwrap();
        let token = agent_installed
            .finish_spend(preparation, b"agent-role-ctx", &mut rng)
            .unwrap();
        assert!(verifier_installed.valid(&token, Mode::Specification, &mut rng));
        let mut invalid = token.clone();
        invalid.units[0].ta += G1::generator();
        assert!(!verifier_installed.valid(&invalid, Mode::Randomized, &mut rng));
    }
    #[test]
    fn default_role_packet_bytes_match_the_independent_point_ledger() {
        let full = PublicParameters::setup(
            1024,
            16,
            64,
            6,
            4,
            b"default-role-ledger",
            &mut StdRng::seed_from_u64(2_073),
        )
        .unwrap();
        for (role, expected_g1, expected_g2, expected_bytes) in [
            (Role::User, 4520, 151, 231924),
            (Role::Issuer, 85, 0, 4344),
            (Role::Agent, 4515, 151, 231666),
            (Role::Verifier, 166, 7, 9099),
        ] {
            let reduced = RoleParameters::from_setup(&full, role).unwrap();
            let fields = reduced.fields();
            assert_eq!(
                fields
                    .iter()
                    .filter(|f| f.object_type == "G1")
                    .map(|f| f.objects)
                    .sum::<usize>(),
                expected_g1
            );
            assert_eq!(
                fields
                    .iter()
                    .filter(|f| f.object_type == "G2")
                    .map(|f| f.objects)
                    .sum::<usize>(),
                expected_g2
            );
            assert_eq!(reduced.encode().len(), expected_bytes);
            assert_eq!(reduced.manifest().encode().len(), 65);
        }
    }

    #[test]
    fn role_manifest_prevents_substitution_and_codec_checks_frames() {
        let mut rng = StdRng::seed_from_u64(2_072);
        let full = PublicParameters::setup(16, 4, 8, 2, 1, b"role-test", &mut rng).unwrap();
        let p = RoleParameters::from_setup(&full, Role::Verifier).unwrap();
        let original = p.encode();
        let mut mutated = original.clone();
        *mutated.last_mut().unwrap() ^= 1;
        assert!(RoleParameters::decode(&mutated, &p.manifest()).is_err());
        let mut other_role = p.manifest();
        other_role.role = Role::Agent;
        assert!(RoleParameters::decode(&original, &other_role).is_err());
        let mut wrong_id = p.manifest();
        wrong_id.pp_id[0] ^= 1;
        assert!(RoleParameters::decode(&original, &wrong_id).is_err());
        // A malformed/trailing packet is rejected even if its transport hash is known.
        for bytes in [
            &original[..original.len() - 1],
            &[original.as_slice(), &[0]].concat(),
        ] {
            let mut transport_manifest = p.manifest();
            transport_manifest.package_sha256 = Sha256::digest(bytes).into();
            assert!(RoleParameters::decode(bytes, &transport_manifest).is_err());
        }
    }
}
