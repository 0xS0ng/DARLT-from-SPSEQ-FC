//! Native payment lifecycle. A wallet's counter advances only through its native Spend call.
use crate::{
    backend::{self as b, GtCompat, ScalarCompat, VerificationMode},
    compact as c, divisible as d,
};
use rand::{CryptoRng, RngCore};

pub type Result<T> = std::result::Result<T, String>;
/// Native 32-byte payinfo: fixed merchant identifier followed by its fresh request nonce.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PayInfo(pub [u8; 32]);
impl PayInfo {
    pub fn new(merchant: [u8; 16], nonce: [u8; 16]) -> Self {
        let mut p = [0; 32];
        p[..16].copy_from_slice(&merchant);
        p[16..].copy_from_slice(&nonce);
        Self(p)
    }
    /// Parse the complete native public input; no bytes are ignored.
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        Ok(Self(bytes.try_into().map_err(|_| {
            "native payinfo must contain exactly32bytes"
        })?))
    }
    pub fn matches(&self, m: &[u8; 16]) -> bool {
        self.0[..16] == m[..]
    }
}

/// The native payment response and its actual public request bytes. Neither
/// field is replaced by a pre-parsed object in a received-message boundary.
#[derive(Clone, Copy)]
pub struct ReceivedPayment<'a> {
    pub payment_bytes: &'a [u8],
    pub payinfo_bytes: &'a [u8],
}

pub struct Compact {
    pub(crate) parameters: std::rc::Rc<c::setup::Parameters>,
    pub(crate) verification_key: c::VerificationKeyAuth,
    authorities: Vec<c::scheme::keygen::KeyPairAuth>,
}
pub struct CompactWallet {
    wallet: c::scheme::Wallet,
    user: c::SecretKeyUser,
}
#[derive(Clone, Debug)]
pub struct CompactPayment {
    pub native: c::scheme::Payment,
    pub payinfo: PayInfo,
}
/// Immutable provenance: every point was checked once by strict decode or typed validation.
#[derive(Clone, Debug)]
pub struct CheckedCompactPayment(CompactPayment);
impl std::ops::Deref for CheckedCompactPayment {
    type Target = CompactPayment;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
/// Private capability for native equation evaluation after complete input validation.
pub(crate) struct CheckedGroups {
    _private: (),
}
impl Compact {
    pub(crate) fn serialized_public_component_lengths(&self) -> serde_json::Value {
        serde_json::json!({"native_public_parameter_package":self.public_parameter_bytes().len(),"native_issuer_verification_key":self.issuer_scope_material().len(),"package_scope":"existing codecs; issuer key is also included in the public package"})
    }

    pub fn new(capacity: u64) -> Result<Self> {
        if !(1..=1024).contains(&capacity) {
            return Err("wallet capacity".into());
        }
        Self::from_parameters(c::setup::setup(capacity))
    }
    pub fn from_parameters(parameters: c::setup::Parameters) -> Result<Self> {
        if !(1..=1024).contains(&parameters.L()) {
            return Err("wallet capacity".into());
        }
        let authorities = c::ttp_keygen(parameters.grp(), 2, 3).map_err(|e| e.to_string())?;
        let verification_key = c::aggregate_verification_keys(
            &authorities[..2]
                .iter()
                .map(|a| a.verification_key())
                .collect::<Vec<_>>(),
            Some(&[1, 2]),
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            parameters: std::rc::Rc::new(parameters),
            authorities,
            verification_key,
        })
    }
    /// Preserve the exact native keygen output for downstream experiment roles.
    pub(crate) fn rekey(&self) -> Result<Self> {
        let authorities = c::ttp_keygen(self.parameters.grp(), 2, 3).map_err(|e| e.to_string())?;
        let verification_key = c::aggregate_verification_keys(
            &authorities[..2]
                .iter()
                .map(|a| a.verification_key())
                .collect::<Vec<_>>(),
            Some(&[1, 2]),
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            parameters: self.parameters.clone(),
            verification_key,
            authorities,
        })
    }
    pub fn issue(&self) -> Result<CompactWallet> {
        let (pending, request) = self.client_request()?;
        let response = self.issuer_responses(&request)?;
        self.client_receive(pending, response)
    }

    pub fn spend(&self, w: &CompactWallet, k: u64, payinfo: PayInfo) -> Result<CompactPayment> {
        let (native, _) = w
            .wallet
            .spend(
                &self.parameters,
                &self.verification_key,
                &w.user,
                &c::PayInfo { info: payinfo.0 },
                false,
                k,
            )
            .map_err(|e| e.to_string())?;
        Ok(CompactPayment { native, payinfo })
    }
    /// Safe typed entry: validate all received point fields once before native equations.
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        p: &[CompactPayment],
        merchant: &[u8; 16],
        mode: VerificationMode,
        rng: &mut R,
    ) -> bool {
        if p.is_empty()
            || p.iter()
                .any(|p| !p.payinfo.matches(merchant) || !p.valid_shape(self.parameters.L()))
        {
            return false;
        }
        self.verify_math(p.iter(), mode, rng, &CheckedGroups { _private: () })
    }
    /// Seal a typed payment after its one complete point/format validation.
    pub fn check_payment(&self, p: CompactPayment) -> Result<CheckedCompactPayment> {
        if !p.valid_shape(self.parameters.L()) {
            return Err("native payment shape/group".into());
        }
        Ok(CheckedCompactPayment(p))
    }
    pub fn verify_checked<R: RngCore + CryptoRng>(
        &self,
        p: &[CheckedCompactPayment],
        merchant: &[u8; 16],
        mode: VerificationMode,
        rng: &mut R,
    ) -> bool {
        if p.is_empty()
            || p.iter()
                .any(|p| !p.payinfo.matches(merchant) || !p.valid_format(self.parameters.L()))
        {
            return false;
        }
        self.verify_math(
            p.iter().map(|p| &p.0),
            mode,
            rng,
            &CheckedGroups { _private: () },
        )
    }
    fn verify_math<'a, R: RngCore + CryptoRng>(
        &self,
        mut p: impl Iterator<Item = &'a CompactPayment>,
        mode: VerificationMode,
        rng: &mut R,
        checked: &CheckedGroups,
    ) -> bool {
        b::verify_captured_checked(mode, rng, checked, || {
            p.all(|p| {
                p.native
                    .spend_verify(
                        &self.parameters,
                        &self.verification_key,
                        &c::PayInfo { info: p.payinfo.0 },
                    )
                    .unwrap_or(false)
            })
        })
    }
    /// Decode the entire batch before native verification may draw weights.
    pub fn decode_received(
        &self,
        messages: &[ReceivedPayment<'_>],
        merchant: &[u8; 16],
    ) -> Result<Vec<CheckedCompactPayment>> {
        if messages.is_empty() {
            return Err("empty received native payment batch".into());
        }
        messages
            .iter()
            .map(|m| {
                let info = PayInfo::decode(m.payinfo_bytes)?;
                if !info.matches(merchant) {
                    return Err("native payinfo merchant/config mismatch".into());
                }
                CompactPayment::decode(m.payment_bytes, info, self.parameters.L())
                    .map(CheckedCompactPayment)
            })
            .collect()
    }
    pub fn verify_received<R: RngCore + CryptoRng>(
        &self,
        messages: &[ReceivedPayment<'_>],
        merchant: &[u8; 16],
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<()> {
        let decoded = self.decode_received(messages, merchant)?;
        if self.verify_checked(&decoded, merchant, mode, rng) {
            Ok(())
        } else {
            Err("native received payment verification rejected".into())
        }
    }
    pub fn deposit_serials_after_verification(&self, p: &[CompactPayment]) -> Result<Vec<Vec<u8>>> {
        let mut ids = vec![];
        for p in p {
            if !p.valid_shape(self.parameters.L()) {
                return Err("native payment shape".into());
            }
            ids.extend(p.native.ss.iter().map(|p| p.to_compressed().to_vec()));
        }
        Ok(ids)
    }
    pub fn deposit_serials_checked(&self, p: &[CheckedCompactPayment]) -> Result<Vec<Vec<u8>>> {
        let mut ids = vec![];
        for p in p {
            if !p.valid_format(self.parameters.L()) {
                return Err("native payment shape".into());
            }
            ids.extend(p.native.ss.iter().map(|p| p.to_compressed().to_vec()));
        }
        Ok(ids)
    }
    pub fn issuer_scope_material(&self) -> Vec<u8> {
        self.verification_key.to_bytes()
    }
}
impl CompactWallet {
    /// Lengths of existing native component encodings, not a new wallet codec.
    pub(crate) fn serialized_component_lengths(&self) -> serde_json::Value {
        serde_json::json!({"native_signature":self.wallet.signature().to_bytes().len(),"native_wallet_scalar_v":self.wallet.v().to_bytes().len(),"native_user_secret_scalar":self.user.sk.to_bytes().len(),"unified_wallet_codec":serde_json::Value::Null})
    }

    pub(crate) fn fixture_branch(&self) -> Self {
        Self {
            wallet: self.wallet.fixture_branch(),
            user: self.user.clone(),
        }
    }

    pub fn next_index(&self) -> u64 {
        self.wallet.l()
    }
}
impl CompactPayment {
    pub fn amount(&self) -> u64 {
        self.native.vv
    }
    fn valid_format(&self, capacity: u64) -> bool {
        let p = &self.native;
        let k = p.vv as usize;
        p.vv > 0
            && p.vv <= capacity
            && [
                p.ss.len(),
                p.tt.len(),
                p.aa.len(),
                p.rr.len(),
                p.kappa_k.len(),
                p.sig_lk.len(),
            ]
            .iter()
            .all(|n| *n == k)
            && p.zk_proof.valid_shape(k)
            && !bool::from(p.sig.0.is_identity())
            && p.sig_lk.iter().all(|s| !bool::from(s.0.is_identity()))
    }
    pub fn valid_shape(&self, capacity: u64) -> bool {
        let p = &self.native;
        self.valid_format(capacity)
            && p.kappa.checked()
            && p.cc.checked()
            && p.sig.0.checked()
            && p.sig.1.checked()
            && p.ss.iter().chain(&p.tt).chain(&p.aa).all(|p| p.checked())
            && p.kappa_k.iter().all(|p| p.checked())
            && p.sig_lk.iter().all(|p| p.0.checked() && p.1.checked())
    }
    pub fn encode(&self) -> Vec<u8> {
        let p = &self.native;
        let mut out = vec![1];
        out.extend(p.vv.to_le_bytes());
        out.extend(p.kappa.to_bytes());
        out.extend(p.sig.to_bytes());
        for v in [&p.ss, &p.tt, &p.aa] {
            for p in v {
                out.extend(p.to_bytes());
            }
        }
        for r in &p.rr {
            out.extend(r.to_bytes());
        }
        for p in &p.kappa_k {
            out.extend(p.to_bytes());
        }
        for p in &p.sig_lk {
            out.extend(p.to_bytes());
        }
        out.extend(p.cc.to_bytes());
        p.zk_proof.encode(&mut out);
        out
    }
    pub fn decode(bytes: &[u8], payinfo: PayInfo, capacity: u64) -> Result<Self> {
        let mut r = b::Reader::new(bytes);
        if r.u8()? != 1 {
            return Err("native payment version".into());
        }
        let vv = r.u64()?;
        if vv == 0 || vv > capacity || vv > 1024 {
            return Err("native payment amount".into());
        }
        let k = vv as usize;
        let kappa = r.g2()?;
        let sig = c::utils::Signature(r.g1()?, r.g1()?);
        let mut points = || -> Result<Vec<_>> { (0..k).map(|_| r.g1()).collect() };
        let ss = points()?;
        let tt = points()?;
        let aa = points()?;
        let rr = (0..k).map(|_| r.scalar()).collect::<Result<_>>()?;
        let kappa_k = (0..k).map(|_| r.g2()).collect::<Result<_>>()?;
        let sig_lk = (0..k)
            .map(|_| Ok(c::utils::Signature(r.g1()?, r.g1()?)))
            .collect::<Result<_>>()?;
        let cc = r.g1()?;
        let zk_proof = c::proofs::proof_spend::SpendProof::decode(&mut r, k)?;
        r.finish()?;
        let p = Self {
            payinfo,
            native: c::scheme::Payment {
                kappa,
                sig,
                ss,
                tt,
                aa,
                rr,
                kappa_k,
                sig_lk,
                cc,
                zk_proof,
                vv,
            },
        };
        if bool::from(p.native.sig.0.is_identity())
            || p.native
                .sig_lk
                .iter()
                .any(|s| bool::from(s.0.is_identity()))
        {
            return Err("native signature h must not be the identity".into());
        }
        if !p.valid_format(capacity) {
            return Err("native payment shape".into());
        }
        Ok(p)
    }
}

pub struct Divisible {
    pub(crate) parameters: std::rc::Rc<d::setup::Parameters>,
    pub(crate) verification_key: d::VerificationKeyAuth,
    authorities: Vec<d::scheme::keygen::KeyPairAuth>,
}
pub struct DivisibleWallet {
    wallet: d::scheme::Wallet,
    user: d::SecretKeyUser,
}
#[derive(Clone, Debug)]
pub struct DivisiblePayment {
    pub native: d::scheme::Payment,
    pub payinfo: PayInfo,
}
/// Immutable provenance; no mutable raw reference or unchecked constructor is exposed.
#[derive(Clone, Debug)]
pub struct CheckedDivisiblePayment(DivisiblePayment);
impl std::ops::Deref for CheckedDivisiblePayment {
    type Target = DivisiblePayment;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl Divisible {
    pub(crate) fn serialized_public_component_lengths(&self) -> serde_json::Value {
        serde_json::json!({"native_user_public_parameter_package":self.user_public_parameter_bytes().len(),"native_deposit_public_parameter_package":self.deposit_public_parameter_bytes().len(),"native_issuer_verification_key":self.issuer_scope_material().len(),"package_scope":"existing per-role codecs, with shared contents counted in each role package"})
    }

    pub fn clear_pairing_cache(&self) {
        self.parameters.clear_pairing_cache();
    }
    pub fn install_public_pairing_bases(&self, amounts: &[u64]) {
        for amount in amounts {
            self.parameters.install_pairing_bases(*amount);
        }
    }
    pub fn new(capacity: u64) -> Result<Self> {
        if !(1..=1024).contains(&capacity) {
            return Err("wallet capacity".into());
        }
        let group = d::setup::GroupParameters::new().map_err(|e| e.to_string())?;
        Self::from_parameters(d::setup::Parameters::new_with_capacity(group, capacity))
    }
    pub fn from_parameters(parameters: d::setup::Parameters) -> Result<Self> {
        let authorities =
            d::ttp_keygen_authorities(&parameters, 2, 3).map_err(|e| e.to_string())?;
        let verification_key = d::aggregate_verification_keys(
            &authorities[..2]
                .iter()
                .map(|a| a.verification_key())
                .collect::<Vec<_>>(),
            Some(&[1, 2]),
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            parameters: std::rc::Rc::new(parameters),
            authorities,
            verification_key,
        })
    }
    /// Preserve the exact native keygen output for downstream experiment roles.
    pub(crate) fn rekey(&self) -> Result<Self> {
        let authorities =
            d::ttp_keygen_authorities(&self.parameters, 2, 3).map_err(|e| e.to_string())?;
        let verification_key = d::aggregate_verification_keys(
            &authorities[..2]
                .iter()
                .map(|a| a.verification_key())
                .collect::<Vec<_>>(),
            Some(&[1, 2]),
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            parameters: self.parameters.clone(),
            verification_key,
            authorities,
        })
    }
    pub fn issue(&self) -> Result<DivisibleWallet> {
        let (pending, request) = self.client_request()?;
        let response = self.issuer_responses(&request)?;
        self.client_receive(pending, response)
    }

    pub fn spend(&self, w: &DivisibleWallet, k: u64, payinfo: PayInfo) -> Result<DivisiblePayment> {
        let (native, _) = w
            .wallet
            .spend(
                &self.parameters,
                &self.verification_key,
                &w.user,
                &d::PayInfo { info: payinfo.0 },
                k,
                false,
            )
            .map_err(|e| e.to_string())?;
        Ok(DivisiblePayment { native, payinfo })
    }
    /// Safe typed entry: validate all received point fields once before native equations.
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        p: &[DivisiblePayment],
        merchant: &[u8; 16],
        mode: VerificationMode,
        rng: &mut R,
    ) -> bool {
        if p.is_empty()
            || p.iter()
                .any(|p| !p.payinfo.matches(merchant) || !p.valid_shape(self.parameters.capacity))
        {
            return false;
        }
        self.verify_math(p.iter(), mode, rng, &CheckedGroups { _private: () })
    }
    /// Seal a typed payment after its one complete point/format validation.
    pub fn check_payment(&self, p: DivisiblePayment) -> Result<CheckedDivisiblePayment> {
        if !p.valid_shape(self.parameters.capacity) {
            return Err("native payment shape/group".into());
        }
        Ok(CheckedDivisiblePayment(p))
    }
    pub fn verify_checked<R: RngCore + CryptoRng>(
        &self,
        p: &[CheckedDivisiblePayment],
        merchant: &[u8; 16],
        mode: VerificationMode,
        rng: &mut R,
    ) -> bool {
        if p.is_empty()
            || p.iter()
                .any(|p| !p.payinfo.matches(merchant) || !p.valid_format(self.parameters.capacity))
        {
            return false;
        }
        self.verify_math(
            p.iter().map(|p| &p.0),
            mode,
            rng,
            &CheckedGroups { _private: () },
        )
    }
    fn verify_math<'a, R: RngCore + CryptoRng>(
        &self,
        mut p: impl Iterator<Item = &'a DivisiblePayment>,
        mode: VerificationMode,
        rng: &mut R,
        checked: &CheckedGroups,
    ) -> bool {
        b::verify_captured_checked(mode, rng, checked, || {
            p.all(|p| {
                p.native
                    .spend_verify(
                        &self.parameters,
                        &self.verification_key,
                        &d::PayInfo { info: p.payinfo.0 },
                    )
                    .unwrap_or(false)
            })
        })
    }
    /// Decode the entire batch before native verification may draw weights.
    pub fn decode_received(
        &self,
        messages: &[ReceivedPayment<'_>],
        merchant: &[u8; 16],
    ) -> Result<Vec<CheckedDivisiblePayment>> {
        if messages.is_empty() {
            return Err("empty received native payment batch".into());
        }
        messages
            .iter()
            .map(|m| {
                let info = PayInfo::decode(m.payinfo_bytes)?;
                if !info.matches(merchant) {
                    return Err("native payinfo merchant/config mismatch".into());
                }
                DivisiblePayment::decode(m.payment_bytes, info, self.parameters.capacity)
                    .map(CheckedDivisiblePayment)
            })
            .collect()
    }
    pub fn verify_received<R: RngCore + CryptoRng>(
        &self,
        messages: &[ReceivedPayment<'_>],
        merchant: &[u8; 16],
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<()> {
        let decoded = self.decode_received(messages, merchant)?;
        if self.verify_checked(&decoded, merchant, mode, rng) {
            Ok(())
        } else {
            Err("native received payment verification rejected".into())
        }
    }
    pub fn deposit_serials_after_verification(
        &self,
        payments: &[DivisiblePayment],
    ) -> Result<Vec<Vec<u8>>> {
        let a = self.parameters.get_params_a();
        let mut ids = vec![];
        for p in payments {
            if !p.valid_shape(self.parameters.capacity) {
                return Err("native payment shape".into());
            }
            for j in 0..p.native.vv {
                let sn = b::pairing_product(&[
                    (
                        p.native.phi.1.to_affine(),
                        a.get_ith_delta(j as usize).to_affine(),
                    ),
                    (
                        p.native.phi.0.to_affine(),
                        a.get_etas_ith_jth_elem(p.native.vv as usize, j as usize)
                            .to_affine(),
                    ),
                ]);
                ids.push(sn.to_compressed().to_vec());
            }
        }
        Ok(ids)
    }
    pub fn deposit_serials_checked(
        &self,
        payments: &[CheckedDivisiblePayment],
    ) -> Result<Vec<Vec<u8>>> {
        let a = self.parameters.get_params_a();
        let mut ids = vec![];
        for p in payments {
            if !p.valid_format(self.parameters.capacity) {
                return Err("native payment shape".into());
            }
            for j in 0..p.native.vv {
                let sn = b::pairing_product(&[
                    (
                        p.native.phi.1.to_affine(),
                        a.get_ith_delta(j as usize).to_affine(),
                    ),
                    (
                        p.native.phi.0.to_affine(),
                        a.get_etas_ith_jth_elem(p.native.vv as usize, j as usize)
                            .to_affine(),
                    ),
                ]);
                ids.push(sn.to_compressed().to_vec());
            }
        }
        Ok(ids)
    }
    pub fn issuer_scope_material(&self) -> Vec<u8> {
        self.verification_key.to_bytes()
    }
    pub fn authority_triangular_points(&self) -> usize {
        self.parameters
            .get_params_a()
            .get_etas()
            .iter()
            .map(Vec::len)
            .sum()
    }
}
impl DivisibleWallet {
    /// Lengths of existing native component encodings, not a new wallet codec.
    pub(crate) fn serialized_component_lengths(&self) -> serde_json::Value {
        serde_json::json!({"native_signature":self.wallet.signature().to_bytes().len(),"native_wallet_scalar_v":self.wallet.v().to_bytes().len(),"native_user_secret_scalar":self.user.sk.to_bytes().len(),"unified_wallet_codec":serde_json::Value::Null})
    }

    pub(crate) fn fixture_branch(&self) -> Self {
        Self {
            wallet: self.wallet.fixture_branch(),
            user: self.user.clone(),
        }
    }

    pub fn next_index(&self) -> u64 {
        self.wallet.l()
    }
}
impl DivisiblePayment {
    pub fn amount(&self) -> u64 {
        self.native.vv
    }
    fn valid_format(&self, capacity: u64) -> bool {
        let p = &self.native;
        p.vv > 0
            && p.vv <= capacity
            && p.zk_proof.valid_shape(p.vv as usize)
            && !bool::from(p.sig.0.is_identity())
    }
    pub fn valid_shape(&self, capacity: u64) -> bool {
        let p = &self.native;
        self.valid_format(capacity)
            && [
                p.sig.0,
                p.sig.1,
                p.phi.0,
                p.phi.1,
                p.varphi.0,
                p.varphi.1,
                p.varsig_prime1,
                p.varsig_prime2,
                p.theta_prime1,
                p.theta_prime2,
                p.rr_prime,
                p.ss_prime,
            ]
            .iter()
            .all(|p| p.checked())
            && p.kappa.checked()
            && p.tt_prime.checked()
    }
    pub fn encode(&self) -> Vec<u8> {
        let p = &self.native;
        let mut out = vec![1];
        out.extend(p.vv.to_le_bytes());
        out.extend(p.kappa.to_bytes());
        out.extend(p.sig.to_bytes());
        for p in [
            p.phi.0,
            p.phi.1,
            p.varphi.0,
            p.varphi.1,
            p.varsig_prime1,
            p.varsig_prime2,
            p.theta_prime1,
            p.theta_prime2,
            p.rr_prime,
            p.ss_prime,
        ] {
            out.extend(p.to_bytes());
        }
        out.extend(p.tt_prime.to_bytes());
        out.extend(p.rr.to_bytes());
        p.zk_proof.encode(&mut out);
        out
    }
    pub fn decode(bytes: &[u8], payinfo: PayInfo, capacity: u64) -> Result<Self> {
        let mut r = b::Reader::new(bytes);
        if r.u8()? != 1 {
            return Err("native payment version".into());
        }
        let vv = r.u64()?;
        if vv == 0 || vv > capacity || vv > 1024 {
            return Err("native payment amount".into());
        }
        let kappa = r.g2()?;
        let sig = d::utils::Signature(r.g1()?, r.g1()?);
        let phi = d::scheme::Phi(r.g1()?, r.g1()?);
        let varphi = d::scheme::VarPhi(r.g1()?, r.g1()?);
        let varsig_prime1 = r.g1()?;
        let varsig_prime2 = r.g1()?;
        let theta_prime1 = r.g1()?;
        let theta_prime2 = r.g1()?;
        let rr_prime = r.g1()?;
        let ss_prime = r.g1()?;
        let tt_prime = r.g2()?;
        let rr = r.scalar()?;
        let zk_proof = d::proofs::proof_spend::SpendProof::decode(&mut r, vv as usize)?;
        r.finish()?;
        let p = Self {
            payinfo,
            native: d::scheme::Payment {
                kappa,
                sig,
                phi,
                varphi,
                varsig_prime1,
                varsig_prime2,
                theta_prime1,
                theta_prime2,
                rr_prime,
                ss_prime,
                tt_prime,
                rr,
                zk_proof,
                vv,
            },
        };
        if bool::from(p.native.sig.0.is_identity()) {
            return Err("native signature h must not be the identity".into());
        }
        if !p.valid_format(capacity) {
            return Err("native payment shape".into());
        }
        Ok(p)
    }
}

fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend((bytes.len() as u64).to_le_bytes());
    out.extend(bytes);
}
impl Compact {
    /// Actual public packages; wallet/user secrets and setup exponents are excluded.
    pub fn public_parameter_bytes(&self) -> Vec<u8> {
        let p = &self.parameters;
        let g = p.grp();
        let mut out = vec![1];
        out.extend(p.L().to_le_bytes());
        out.extend(g.gen1().to_compressed());
        out.extend(g.gen2().to_compressed());
        out.extend((g.gammas().len() as u64).to_le_bytes());
        for g in g.gammas() {
            out.extend(g.to_bytes());
        }
        out.extend(g.delta().to_bytes());
        out.extend(p.pk_rp().alpha.to_bytes());
        out.extend(p.pk_rp().beta.to_bytes());
        out.extend((p.signs().len() as u64).to_le_bytes());
        let mut signs: Vec<_> = p.signs().iter().collect();
        signs.sort_by_key(|(i, _)| **i);
        for (i, s) in signs {
            out.extend(i.to_le_bytes());
            out.extend(s.to_bytes());
        }
        frame(&mut out, &self.verification_key.to_bytes());
        out
    }
}
impl Divisible {
    pub fn user_public_parameter_bytes(&self) -> Vec<u8> {
        let p = &self.parameters;
        let g = p.get_grp();
        let u = p.get_params_u();
        let mut out = vec![1];
        out.extend(p.capacity.to_le_bytes());
        out.extend(g.gen1().to_compressed());
        out.extend(g.gen2().to_compressed());
        for g in u.get_gammas() {
            out.extend(g.to_bytes());
        }
        out.extend(u.get_psi_g1().to_bytes());
        out.extend(u.get_psi_g2().to_bytes());
        out.extend(u.get_eta().to_bytes());
        for v in [u.get_etas(), u.get_sigmas(), u.get_thetas()] {
            out.extend((v.len() as u64).to_le_bytes());
            for p in v {
                out.extend(p.to_bytes());
            }
        }
        out.extend((u.get_sps_signs().len() as u64).to_le_bytes());
        for s in u.get_sps_signs() {
            out.extend(s.rr.to_bytes());
            out.extend(s.ss.to_bytes());
            out.extend(s.tt.to_bytes());
        }
        let vk = u.get_sps_pk();
        for g in &vk.uus {
            out.extend(g.to_bytes());
        }
        for g in &vk.wws {
            out.extend(g.to_bytes());
        }
        out.extend(vk.yy.to_bytes());
        out.extend(vk.zz.to_bytes());
        out.extend((p.get_params_a().get_deltas().len() as u64).to_le_bytes());
        for d in p.get_params_a().get_deltas() {
            out.extend(d.to_bytes());
        }
        frame(&mut out, &self.verification_key.to_bytes());
        out
    }
    pub fn deposit_public_parameter_bytes(&self) -> Vec<u8> {
        let a = self.parameters.get_params_a();
        let mut out = vec![1];
        out.extend(self.parameters.capacity.to_le_bytes());
        out.extend((a.get_deltas().len() as u64).to_le_bytes());
        for g in a.get_deltas() {
            out.extend(g.to_bytes());
        }
        out.extend((a.get_etas().len() as u64).to_le_bytes());
        for row in a.get_etas() {
            out.extend((row.len() as u64).to_le_bytes());
            for g in row {
                out.extend(g.to_bytes());
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use darlt_spseq_fc::{
        batch_runtime::{self as rt, Error, Mode},
        common::spent::SpentStore,
        common::state::StateError,
    };
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn native_replayed_wallet_indices_cannot_reset_at_another_merchant_or_nonce() {
        let mut rng = StdRng::seed_from_u64(214);
        let m1 = [1; 16];
        let m2 = [2; 16];
        let c = Compact::new(16).unwrap();
        let w = c.issue().unwrap();
        let p1 = c.spend(&w, 3, PayInfo::new(m1, [0; 16])).unwrap();
        // Malicious holder rollback is a double-spend negative fixture, not a normal allocator.
        w.wallet.l.set(0);
        let p2 = c.spend(&w, 3, PayInfo::new(m2, [1; 16])).unwrap();
        let a = crate::shared_runtime::CompactVerifier::new(&c, m1);
        let other = crate::shared_runtime::CompactVerifier::new(&c, m2);
        let s = SpentStore::new();
        rt::verify_and_record(
            &a,
            &[c.check_payment(p1).unwrap()],
            b"merchant-one",
            b"",
            &s,
            Mode::Randomized,
            &mut rng,
        )
        .unwrap();
        assert!(matches!(
            rt::verify_and_record(
                &other,
                &[c.check_payment(p2).unwrap()],
                b"merchant-two-fresh-nonce",
                b"",
                &s,
                Mode::Randomized,
                &mut rng
            ),
            Err(Error::State(StateError::SerialUsed))
        ));
        assert_eq!(s.counts().unwrap(), (1, 3));
        let d = Divisible::new(16).unwrap();
        let w = d.issue().unwrap();
        let p1 = d.spend(&w, 3, PayInfo::new(m1, [0; 16])).unwrap();
        w.wallet.l.set(1);
        let p2 = d.spend(&w, 3, PayInfo::new(m2, [1; 16])).unwrap();
        let a = crate::shared_runtime::DivisibleVerifier::new(&d, m1);
        let other = crate::shared_runtime::DivisibleVerifier::new(&d, m2);
        let s = SpentStore::new();
        rt::verify_and_record(
            &a,
            &[d.check_payment(p1).unwrap()],
            b"merchant-one",
            b"",
            &s,
            Mode::Randomized,
            &mut rng,
        )
        .unwrap();
        assert!(matches!(
            rt::verify_and_record(
                &other,
                &[d.check_payment(p2).unwrap()],
                b"merchant-two-fresh-nonce",
                b"",
                &s,
                Mode::Randomized,
                &mut rng
            ),
            Err(Error::State(StateError::SerialUsed))
        ));
        assert_eq!(s.counts().unwrap(), (1, 3));
    }
}

/// One-use native preparation bound to an immutable issuer instance and an exclusively borrowed wallet.
pub struct PreparedCompact<'a> {
    context: &'a Compact,
    wallet: &'a mut CompactWallet,
    merchant: [u8; 16],
    native: c::scheme::PreparedSpend,
}
impl Compact {
    pub fn prepare<'a>(
        &'a self,
        wallet: &'a mut CompactWallet,
        amount: u64,
        merchant: [u8; 16],
    ) -> Result<PreparedCompact<'a>> {
        let native = wallet
            .wallet
            .prepare_spend(
                &self.parameters,
                &self.verification_key,
                &wallet.user,
                amount,
            )
            .map_err(|e| e.to_string())?;
        Ok(PreparedCompact {
            context: self,
            wallet,
            merchant,
            native,
        })
    }
}
impl PreparedCompact<'_> {
    pub fn amount(&self) -> u64 {
        self.native.amount()
    }
    pub fn finish(self, payinfo: PayInfo) -> Result<CompactPayment> {
        if !payinfo.matches(&self.merchant) {
            return Err("prepared merchant mismatch".into());
        }
        let start = self.native.start_index();
        let amount = self.native.amount();
        if self.wallet.wallet.l() != start {
            return Err("prepared wallet counter changed".into());
        }
        let native = self
            .native
            .finish(
                &self.context.parameters,
                &self.context.verification_key,
                &c::PayInfo { info: payinfo.0 },
            )
            .map_err(|e| e.to_string())?;
        self.wallet.wallet.l.set(start + amount);
        Ok(CompactPayment { native, payinfo })
    }
}
/// One-use native interval preparation. Fresh merchant nonce is supplied only to finish.
pub struct PreparedDivisible<'a> {
    context: &'a Divisible,
    wallet: &'a mut DivisibleWallet,
    merchant: [u8; 16],
    native: d::scheme::PreparedSpend,
}
impl Divisible {
    pub fn prepare<'a>(
        &'a self,
        wallet: &'a mut DivisibleWallet,
        amount: u64,
        merchant: [u8; 16],
    ) -> Result<PreparedDivisible<'a>> {
        let native = wallet
            .wallet
            .prepare_spend(
                &self.parameters,
                &self.verification_key,
                &wallet.user,
                amount,
            )
            .map_err(|e| e.to_string())?;
        Ok(PreparedDivisible {
            context: self,
            wallet,
            merchant,
            native,
        })
    }
}
impl PreparedDivisible<'_> {
    pub fn amount(&self) -> u64 {
        self.native.amount()
    }
    pub fn finish(self, payinfo: PayInfo) -> Result<DivisiblePayment> {
        if !payinfo.matches(&self.merchant) {
            return Err("prepared merchant mismatch".into());
        }
        let start = self.native.start_index();
        let amount = self.native.amount();
        if self.wallet.wallet.l() != start {
            return Err("prepared wallet counter changed".into());
        }
        let native = self
            .native
            .finish(
                &self.context.parameters,
                &self.context.verification_key,
                &d::PayInfo { info: payinfo.0 },
            )
            .map_err(|e| e.to_string())?;
        self.wallet.wallet.l.set(start + amount);
        Ok(DivisiblePayment { native, payinfo })
    }
}

#[cfg(test)]
mod preparation_tests {
    use super::*;
    use crate::backend::{self as b, VerificationMode as V};
    use rand::{rngs::StdRng, SeedableRng};
    const MERCHANT: [u8; 16] = [7; 16];
    #[test]
    fn native_and_prepared_payment_are_byte_identical_under_same_randomness() {
        let mut rng = StdRng::seed_from_u64(214);
        let c = Compact::new(80).unwrap();
        let d = Divisible::new(80).unwrap();
        for k in [1, 16, 64] {
            let info = PayInfo::new(MERCHANT, [k as u8; 16]);
            let old = b::with_test_seed(100 + k, || c.issue().unwrap());
            let mut fresh = b::with_test_seed(100 + k, || c.issue().unwrap());
            let expected = b::with_test_seed(200 + k, || c.spend(&old, k, info).unwrap());
            b::start_counts();
            let prepared =
                b::with_test_seed(200 + k, || c.prepare(&mut fresh, k, MERCHANT).unwrap());
            let offline = b::stop_counts();
            assert_eq!(prepared.amount(), k);
            b::start_counts();
            let actual = prepared.finish(info).unwrap();
            let online = b::stop_counts();
            assert_eq!(
                actual.encode(),
                expected.encode(),
                "RP23-C same complete native bytes k={k}"
            );
            assert_eq!(fresh.next_index(), k);
            assert_eq!(online.g1_exp, 2 * k as usize);
            assert_eq!(
                online.g2_exp + online.gt_exp + online.miller_terms + online.final_exponentiations,
                0
            );
            assert!(online.g1_msm_sizes.is_empty() && online.g2_msm_sizes.is_empty());
            assert!(!offline.g1_msm_sizes.is_empty());
            assert!(c.verify(&[actual], &MERCHANT, V::Randomized, &mut rng));
            let old = b::with_test_seed(300 + k, || d.issue().unwrap());
            let mut fresh = b::with_test_seed(300 + k, || d.issue().unwrap());
            let expected = b::with_test_seed(400 + k, || d.spend(&old, k, info).unwrap());
            b::start_counts();
            let prepared =
                b::with_test_seed(400 + k, || d.prepare(&mut fresh, k, MERCHANT).unwrap());
            let offline = b::stop_counts();
            assert_eq!(prepared.amount(), k);
            b::start_counts();
            let actual = prepared.finish(info).unwrap();
            let online = b::stop_counts();
            assert_eq!(
                actual.encode(),
                expected.encode(),
                "RP23-D same complete native bytes k={k}"
            );
            assert_eq!(fresh.next_index(), 1 + k);
            assert_eq!(online.g1_exp, 2);
            assert_eq!(
                online.g2_exp + online.gt_exp + online.miller_terms + online.final_exponentiations,
                0
            );
            assert!(online.g1_msm_sizes.is_empty() && online.g2_msm_sizes.is_empty());
            assert!(!offline.g1_msm_sizes.is_empty());
            assert!(d.verify(&[actual], &MERCHANT, V::Randomized, &mut rng));
        }
    }
    #[test]
    fn failed_or_abandoned_preparation_preserves_native_counter() {
        let c = Compact::new(16).unwrap();
        let d = Divisible::new(16).unwrap();
        let mut cwallet = c.issue().unwrap();
        let mut dwallet = d.issue().unwrap();
        {
            let _prepared = c.prepare(&mut cwallet, 3, MERCHANT).unwrap();
        }
        assert_eq!(cwallet.next_index(), 0);
        assert!(c
            .prepare(&mut cwallet, 3, MERCHANT)
            .unwrap()
            .finish(PayInfo::new([8; 16], [0; 16]))
            .is_err());
        assert_eq!(cwallet.next_index(), 0);
        assert!(c.prepare(&mut cwallet, 0, MERCHANT).is_err());
        assert_eq!(cwallet.next_index(), 0);
        {
            let _prepared = d.prepare(&mut dwallet, 3, MERCHANT).unwrap();
        }
        assert_eq!(dwallet.next_index(), 1);
        assert!(d
            .prepare(&mut dwallet, 3, MERCHANT)
            .unwrap()
            .finish(PayInfo::new([8; 16], [0; 16]))
            .is_err());
        assert_eq!(dwallet.next_index(), 1);
        assert!(d.prepare(&mut dwallet, 0, MERCHANT).is_err());
        assert_eq!(dwallet.next_index(), 1);
    }
}

/// Client-only withdrawal state. Issuer callbacks receive only the separate public request.
pub struct CompactPendingUser {
    user: c::SecretKeyUser,
    info: c::scheme::withdrawal::RequestInfo,
}
pub struct CompactIssueRequest {
    public_key: c::PublicKeyUser,
    request: c::scheme::withdrawal::WithdrawalRequest,
}
/// Sealed group provenance: only native issuance and the strict group decoder
/// construct this type; no mutable raw shares are exposed by the public API.
pub struct CompactIssuerResponses {
    signatures: Vec<c::utils::BlindedSignature>,
}
impl Compact {
    pub fn client_request(&self) -> Result<(CompactPendingUser, CompactIssueRequest)> {
        let user = c::generate_keypair_user(self.parameters.grp());
        let (request, info) = c::withdrawal_request(self.parameters.grp(), &user.secret_key())
            .map_err(|e| e.to_string())?;
        Ok((
            CompactPendingUser {
                user: user.secret_key(),
                info,
            },
            CompactIssueRequest {
                public_key: user.public_key(),
                request,
            },
        ))
    }
    pub fn issuer_responses(
        &self,
        request: &CompactIssueRequest,
    ) -> Result<CompactIssuerResponses> {
        let signatures = self.authorities[..2]
            .iter()
            .map(|a| {
                c::issue_wallet(
                    self.parameters.grp(),
                    a.secret_key(),
                    request.public_key.clone(),
                    &request.request,
                )
            })
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(|e| e.to_string())?;
        Ok(CompactIssuerResponses { signatures })
    }
    pub fn client_receive(
        &self,
        pending: CompactPendingUser,
        response: CompactIssuerResponses,
    ) -> Result<CompactWallet> {
        self.client_receive_with_verification(
            pending,
            response,
            VerificationMode::Randomized,
            &mut rand::thread_rng(),
        )
    }
    /// One receiving step checks both authority shares and the aggregate
    /// signature together, after their complete original native processing.
    pub fn client_receive_with_verification<R: RngCore + CryptoRng>(
        &self,
        pending: CompactPendingUser,
        response: CompactIssuerResponses,
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<CompactWallet> {
        let mut output = None;
        let accepted =
            b::verify_captured_checked(mode, rng, &CheckedGroups { _private: () }, || {
                output = Some(self.client_receive_native(pending, response));
                output.as_ref().unwrap().is_ok()
            });
        let wallet = output.expect("native receiving closure executed")?;
        if !accepted {
            return Err("native wallet receiving pairing equations rejected".into());
        }
        Ok(wallet)
    }
    fn client_receive_native(
        &self,
        pending: CompactPendingUser,
        response: CompactIssuerResponses,
    ) -> Result<CompactWallet> {
        if response.signatures.len() != 2 {
            return Err("withdrawal needs exactly the contacted two authority shares".into());
        }
        let g = self.parameters.grp();
        let shares = response
            .signatures
            .iter()
            .zip(&self.authorities[..2])
            .map(|(s, a)| {
                c::issue_verify(g, &a.verification_key(), &pending.user, s, &pending.info)
            })
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(|e| e.to_string())?;
        let wallet = c::aggregate_wallets(
            g,
            &self.verification_key,
            &pending.user,
            &shares,
            &pending.info,
        )
        .map_err(|e| e.to_string())?;
        Ok(CompactWallet {
            wallet,
            user: pending.user,
        })
    }
}
pub struct DivisiblePendingUser {
    user: d::SecretKeyUser,
    info: d::scheme::withdrawal::RequestInfo,
}
pub struct DivisibleIssueRequest {
    public_key: d::PublicKeyUser,
    request: d::scheme::withdrawal::WithdrawalRequest,
}
/// Sealed native/strict-codec group provenance, with no mutable raw access.
pub struct DivisibleIssuerResponses {
    signatures: Vec<d::utils::BlindedSignature>,
}
impl Divisible {
    pub fn client_request(&self) -> Result<(DivisiblePendingUser, DivisibleIssueRequest)> {
        let user = d::ttp_keygen_users(&self.parameters);
        let (request, info) = d::withdrawal_request(&self.parameters, &user.secret_key())
            .map_err(|e| e.to_string())?;
        Ok((
            DivisiblePendingUser {
                user: user.secret_key(),
                info,
            },
            DivisibleIssueRequest {
                public_key: user.public_key(),
                request,
            },
        ))
    }
    pub fn issuer_responses(
        &self,
        request: &DivisibleIssueRequest,
    ) -> Result<DivisibleIssuerResponses> {
        let signatures = self.authorities[..2]
            .iter()
            .map(|a| {
                d::issue(
                    &self.parameters,
                    &request.request,
                    request.public_key.clone(),
                    &a.secret_key(),
                )
            })
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(|e| e.to_string())?;
        Ok(DivisibleIssuerResponses { signatures })
    }
    pub fn client_receive(
        &self,
        pending: DivisiblePendingUser,
        response: DivisibleIssuerResponses,
    ) -> Result<DivisibleWallet> {
        self.client_receive_with_verification(
            pending,
            response,
            VerificationMode::Randomized,
            &mut rand::thread_rng(),
        )
    }
    /// The two share equations and aggregate equation belong to this same
    /// receiving step and use independent verifier coefficients together.
    pub fn client_receive_with_verification<R: RngCore + CryptoRng>(
        &self,
        pending: DivisiblePendingUser,
        response: DivisibleIssuerResponses,
        mode: VerificationMode,
        rng: &mut R,
    ) -> Result<DivisibleWallet> {
        let mut output = None;
        let accepted =
            b::verify_captured_checked(mode, rng, &CheckedGroups { _private: () }, || {
                output = Some(self.client_receive_native(pending, response));
                output.as_ref().unwrap().is_ok()
            });
        let wallet = output.expect("native receiving closure executed")?;
        if !accepted {
            return Err("native wallet receiving pairing equations rejected".into());
        }
        Ok(wallet)
    }
    fn client_receive_native(
        &self,
        pending: DivisiblePendingUser,
        response: DivisibleIssuerResponses,
    ) -> Result<DivisibleWallet> {
        if response.signatures.len() != 2 {
            return Err("withdrawal needs exactly the contacted two authority shares".into());
        }
        let g = self.parameters.get_grp();
        let shares = response
            .signatures
            .iter()
            .zip(&self.authorities[..2])
            .map(|(s, a)| {
                d::issue_verify(g, &a.verification_key(), &pending.user, s, &pending.info)
            })
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(|e| e.to_string())?;
        let wallet = d::aggregate_wallets(g, &self.verification_key, &pending.user, &shares)
            .map_err(|e| e.to_string())?;
        Ok(DivisibleWallet {
            wallet,
            user: pending.user,
        })
    }
}

#[cfg(test)]
mod issuance_role_tests {
    use super::*;
    use crate::backend::G1Projective;
    #[derive(Default)]
    struct ReceivingCoins(usize);
    impl RngCore for ReceivingCoins {
        fn next_u32(&mut self) -> u32 {
            panic!("batch draw is16bytes")
        }
        fn next_u64(&mut self) -> u64 {
            panic!("batch draw is16bytes")
        }
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            assert_eq!(dest.len(), 16);
            self.0 += 1;
            dest.copy_from_slice(&(self.0 as u128).to_le_bytes());
        }
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> std::result::Result<(), rand::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }
    impl CryptoRng for ReceivingCoins {}
    #[test]
    fn native_spend_batches_every_compact_ppe_and_divisible_single_ppe_degenerates_exactly() {
        let merchant = [19; 16];
        let c = Compact::new(4).unwrap();
        let wallet = c.issue().unwrap();
        let payment = c
            .spend(&wallet, 3, PayInfo::new(merchant, [1; 16]))
            .unwrap();
        for corrupted in [None, Some(0usize), Some(1), Some(2), Some(3)] {
            let mut p = payment.clone();
            if let Some(i) = corrupted {
                if i == 0 {
                    p.native.sig.1 += G1Projective::generator();
                } else {
                    p.native.sig_lk[i - 1].1 += G1Projective::generator();
                }
            }
            let mut coins = ReceivingCoins::default();
            assert_eq!(
                c.verify(&[p], &merchant, VerificationMode::Randomized, &mut coins),
                corrupted.is_none()
            );
            assert_eq!(coins.0, 4);
        }
        assert_eq!(
            c.deposit_serials_after_verification(&[payment])
                .unwrap()
                .len(),
            3
        );
        let d = Divisible::new(4).unwrap();
        let wallet = d.issue().unwrap();
        let payment = d
            .spend(&wallet, 3, PayInfo::new(merchant, [2; 16]))
            .unwrap();
        for corrupted in [false, true] {
            let mut p = payment.clone();
            if corrupted {
                p.native.sig.1 += G1Projective::generator();
            }
            let mut coins = ReceivingCoins::default();
            assert_eq!(
                d.verify(&[p], &merchant, VerificationMode::Randomized, &mut coins),
                !corrupted
            );
            assert_eq!(coins.0, 0);
        }
        assert_eq!(
            d.deposit_serials_after_verification(&[payment])
                .unwrap()
                .len(),
            3
        );
    }
    #[test]
    fn receiving_batches_two_authority_shares_and_aggregate_in_one_step() {
        let c = Compact::new(4).unwrap();
        let d = Divisible::new(4).unwrap();
        for corrupt in [None, Some(0usize), Some(1usize)] {
            let (pending, request) = c.client_request().unwrap();
            let mut response = c.issuer_responses(&request).unwrap();
            if let Some(i) = corrupt {
                response.signatures[i].1 += G1Projective::generator();
            }
            let mut coins = ReceivingCoins::default();
            b::start_counts();
            let received = c.client_receive_with_verification(
                pending,
                response,
                VerificationMode::Randomized,
                &mut coins,
            );
            let counts = b::stop_counts();
            assert_eq!(received.is_ok(), corrupt.is_none());
            assert_eq!(coins.0, 3);
            assert_eq!(counts.final_exponentiations, 1);
            let (pending, request) = d.client_request().unwrap();
            let mut response = d.issuer_responses(&request).unwrap();
            if let Some(i) = corrupt {
                response.signatures[i].1 += G1Projective::generator();
            }
            let mut coins = ReceivingCoins::default();
            b::start_counts();
            let received = d.client_receive_with_verification(
                pending,
                response,
                VerificationMode::Randomized,
                &mut coins,
            );
            let counts = b::stop_counts();
            assert_eq!(received.is_ok(), corrupt.is_none());
            assert_eq!(coins.0, 3);
            assert_eq!(counts.final_exponentiations, 1);
        }
    }
    #[test]
    fn native_issue_roles_accept_valid_and_reject_wrong_user_or_authority_share() {
        let c = Compact::new(16).unwrap();
        let (pending, request) = c.client_request().unwrap();
        let response = c.issuer_responses(&request).unwrap();
        let w = c.client_receive(pending, response).unwrap();
        assert_eq!(w.next_index(), 0);
        let (_, mut request) = c.client_request().unwrap();
        request.public_key.pk = G1Projective::generator();
        assert!(c.issuer_responses(&request).is_err());
        let (pending, request) = c.client_request().unwrap();
        let mut response = c.issuer_responses(&request).unwrap();
        response.signatures[0].1 += G1Projective::generator();
        assert!(c.client_receive(pending, response).is_err());
        let (pending, request) = c.client_request().unwrap();
        let mut response = c.issuer_responses(&request).unwrap();
        response.signatures.pop();
        assert!(c.client_receive(pending, response).is_err());
        let d = Divisible::new(16).unwrap();
        let (pending, request) = d.client_request().unwrap();
        let response = d.issuer_responses(&request).unwrap();
        let w = d.client_receive(pending, response).unwrap();
        assert_eq!(w.next_index(), 1);
        let (_, mut request) = d.client_request().unwrap();
        request.public_key.pk = G1Projective::generator();
        assert!(d.issuer_responses(&request).is_err());
        let (pending, request) = d.client_request().unwrap();
        let mut response = d.issuer_responses(&request).unwrap();
        response.signatures[0].1 += G1Projective::generator();
        assert!(d.client_receive(pending, response).is_err());
        let (pending, request) = d.client_request().unwrap();
        let mut response = d.issuer_responses(&request).unwrap();
        response.signatures.pop();
        assert!(d.client_receive(pending, response).is_err());
    }
}

impl Divisible {
    /// Read the actual end entries and verify the terminal native SPS range signature.
    pub fn end_parameter_coverage(&self) -> serde_json::Value {
        let p = &self.parameters;
        let n = p.capacity as usize;
        let u = p.get_params_u();
        let a = p.get_params_a();
        assert_eq!(u.get_sigmas().len(), n);
        assert_eq!(u.get_thetas().len(), n);
        assert_eq!(u.get_sps_signs().len(), n);
        assert_eq!(u.get_etas().len(), n);
        assert_eq!(a.get_deltas().len(), n);
        assert_eq!(a.get_etas().len(), n);
        assert_eq!(a.get_eta_ith_row(n - 1).len(), n);
        assert!(
            u.get_ith_sigma(n).checked()
                && u.get_ith_theta(n).checked()
                && u.get_ith_eta(n).checked()
                && a.get_ith_delta(n - 1).checked()
                && a.get_etas_ith_jth_elem(n, n - 1).checked()
        );
        let tau = u.get_ith_sps_sign(n).clone();
        assert!(u.get_sps_pk().verify(
            p.get_grp(),
            tau,
            &[*u.get_ith_sigma(n), *u.get_ith_theta(n)],
            None
        ));
        serde_json::json!({"capacity":n,"sigma_last_index_1based":n,"theta_last_index_1based":n,"SPS_last_index_1based":n,"tau_L_verified":true,"eta_amount_last_index_1based":n,"delta_last_index_0based":n-1,"eta_L_row_len":a.get_eta_ith_row(n-1).len(),"eta_L_last_j_0based":n-1,"all_terminal_points_curve_and_subgroup_checked":true})
    }
}
#[cfg(test)]
mod capacity_boundary_tests {
    use super::*;
    use crate::backend::{self as b, VerificationMode as V};
    use rand::{rngs::StdRng, SeedableRng};
    #[test]
    fn full_capacity_and_split_last_coin_match_the_same_native_serial_set() {
        let merchant = [7; 16];
        let mut rng = StdRng::seed_from_u64(21416);
        for capacity in [1, 16] {
            let d = Divisible::new(capacity).unwrap();
            let coverage = d.end_parameter_coverage();
            assert_eq!(coverage["eta_L_row_len"], capacity);
            for prepared in [false, true] {
                let mut full = b::with_test_seed(600 + capacity, || d.issue().unwrap());
                let mut split = b::with_test_seed(600 + capacity, || d.issue().unwrap());
                let info = PayInfo::new(merchant, [1; 16]);
                let pfull = if prepared {
                    d.prepare(&mut full, capacity, merchant)
                        .unwrap()
                        .finish(info)
                        .unwrap()
                } else {
                    d.spend(&full, capacity, info).unwrap()
                };
                assert_eq!(full.next_index(), capacity + 1);
                let mut payments = vec![];
                if capacity > 1 {
                    let info = PayInfo::new(merchant, [2; 16]);
                    let p = if prepared {
                        d.prepare(&mut split, capacity - 1, merchant)
                            .unwrap()
                            .finish(info)
                            .unwrap()
                    } else {
                        d.spend(&split, capacity - 1, info).unwrap()
                    };
                    payments.push(p);
                    assert_eq!(split.next_index(), capacity);
                }
                let info = PayInfo::new(merchant, [3; 16]);
                let last = if prepared {
                    d.prepare(&mut split, 1, merchant)
                        .unwrap()
                        .finish(info)
                        .unwrap()
                } else {
                    d.spend(&split, 1, info).unwrap()
                };
                payments.push(last);
                assert_eq!(split.next_index(), capacity + 1);
                for mode in [V::Specification, V::Randomized] {
                    assert!(d.verify(std::slice::from_ref(&pfull), &merchant, mode, &mut rng));
                    assert!(d.verify(&payments, &merchant, mode, &mut rng));
                }
                let a = d
                    .deposit_serials_after_verification(&[pfull])
                    .unwrap()
                    .into_iter()
                    .collect::<std::collections::BTreeSet<_>>();
                let all = d.deposit_serials_after_verification(&payments).unwrap();
                let z = all
                    .iter()
                    .cloned()
                    .collect::<std::collections::BTreeSet<_>>();
                assert_eq!(all.len(), capacity as usize);
                assert_eq!(a.len(), capacity as usize);
                assert_eq!(z.len(), capacity as usize);
                assert_eq!(
                    a, z,
                    "amount=L and (L-1)+last1 recover the same absolute indices"
                );
                assert!(d.spend(&full, 1, PayInfo::new(merchant, [4; 16])).is_err());
                assert!(d.prepare(&mut full, 1, merchant).is_err());
                assert_eq!(full.next_index(), capacity + 1);
                assert!(d.spend(&split, 1, PayInfo::new(merchant, [4; 16])).is_err());
                assert!(d.prepare(&mut split, 1, merchant).is_err());
                assert_eq!(split.next_index(), capacity + 1);
            }
        }
    }
}

// Canonical public withdrawal transport. Client-only pending state is never encoded.
macro_rules! withdrawal_codec {
    ($request:ident, $responses:ident, $scheme:ident) => {
        impl $request {
            pub fn encode(&self) -> Vec<u8> {
                let mut o = vec![1];
                for p in [self.public_key.pk, self.request.com_hash, self.request.com] {
                    o.extend(p.to_compressed());
                }
                o.extend((self.request.pc_coms.len() as u64).to_le_bytes());
                for p in &self.request.pc_coms {
                    o.extend(p.to_compressed());
                }
                let z = &self.request.zk_proof;
                o.extend(z.challenge.to_bytes_le());
                o.extend(z.response_opening.to_bytes_le());
                for v in [&z.response_openings, &z.response_attributes] {
                    o.extend((v.len() as u64).to_le_bytes());
                    for x in v {
                        o.extend(x.to_bytes_le());
                    }
                }
                o
            }
            pub fn decode(bytes: &[u8]) -> Result<Self> {
                let mut r = b::Reader::new(bytes);
                if r.u8()? != 1 {
                    return Err("withdrawal codec version".into());
                }
                let public_key = $scheme::PublicKeyUser { pk: r.g1()? };
                let com_hash = r.g1()?;
                let com = r.g1()?;
                if r.u64()? != 2 {
                    return Err("withdrawal expects two attributes".into());
                }
                let pc_coms = vec![r.g1()?, r.g1()?];
                let challenge = r.scalar()?;
                let response_opening = r.scalar()?;
                if r.u64()? != 2 {
                    return Err("withdrawal opening response count".into());
                }
                let response_openings = vec![r.scalar()?, r.scalar()?];
                if r.u64()? != 2 {
                    return Err("withdrawal attribute response count".into());
                }
                let response_attributes = vec![r.scalar()?, r.scalar()?];
                r.finish()?;
                Ok(Self {
                    public_key,
                    request: $scheme::scheme::withdrawal::WithdrawalRequest {
                        com_hash,
                        com,
                        pc_coms,
                        zk_proof: $scheme::proofs::proof_withdrawal::WithdrawalReqProof {
                            challenge,
                            response_opening,
                            response_openings,
                            response_attributes,
                        },
                    },
                })
            }
        }
        impl $responses {
            pub fn encode(&self) -> Vec<u8> {
                let mut o = vec![1];
                o.extend((self.signatures.len() as u64).to_le_bytes());
                for s in &self.signatures {
                    o.extend(s.0.to_compressed());
                    o.extend(s.1.to_compressed());
                }
                o
            }
            pub fn decode(bytes: &[u8]) -> Result<Self> {
                let mut r = b::Reader::new(bytes);
                if r.u8()? != 1 || r.u64()? != 2 {
                    return Err("withdrawal response needs two shares".into());
                }
                let signatures = (0..2)
                    .map(|_| Ok($scheme::utils::BlindedSignature(r.g1()?, r.g1()?)))
                    .collect::<Result<Vec<_>>>()?;
                r.finish()?;
                Ok(Self { signatures })
            }
        }
    };
}
withdrawal_codec!(CompactIssueRequest, CompactIssuerResponses, c);
withdrawal_codec!(DivisibleIssueRequest, DivisibleIssuerResponses, d);

#[cfg(test)]
mod withdrawal_codec_tests {
    use super::*;
    #[test]
    fn full_public_withdrawal_transport_is_canonical_and_role_complete() {
        macro_rules! check {
            ($ctx:expr,$req:ident,$resp:ident) => {{
                let c = $ctx;
                let (pending, request) = c.client_request().unwrap();
                let raw = request.encode();
                let request = $req::decode(&raw).unwrap();
                assert_eq!(request.encode(), raw);
                let response = c.issuer_responses(&request).unwrap();
                let bytes = response.encode();
                assert_eq!(raw.len(), 457);
                assert_eq!(bytes.len(), 201);
                let response = $resp::decode(&bytes).unwrap();
                assert_eq!(response.encode(), bytes);
                c.client_receive(pending, response).unwrap();
                assert!($req::decode(&raw[..raw.len() - 1]).is_err());
                let mut trailing = raw.clone();
                trailing.push(0);
                assert!($req::decode(&trailing).is_err());
                let mut invalid = raw;
                invalid[1..49].fill(255);
                assert!($req::decode(&invalid).is_err());
                let mut bad = bytes;
                bad.push(0);
                assert!($resp::decode(&bad).is_err());
            }};
        }
        check!(
            Compact::new(2).unwrap(),
            CompactIssueRequest,
            CompactIssuerResponses
        );
        check!(
            Divisible::new(2).unwrap(),
            DivisibleIssueRequest,
            DivisibleIssuerResponses
        );
    }
}
