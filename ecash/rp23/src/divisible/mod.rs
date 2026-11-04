use crate::backend::Scalar;
use crate::backend::{GtCompat, IntoMsm, NativeMsm, ScalarCompat};
use ff::Field;
use std::ops::*;

pub use scheme::aggregation::aggregate_verification_keys;
pub use scheme::aggregation::aggregate_wallets;
pub use scheme::keygen::ttp_keygen_authorities;
pub use scheme::keygen::ttp_keygen_users;
pub use scheme::keygen::{PublicKeyUser, SecretKeyUser, VerificationKeyAuth};
pub use scheme::setup;
pub use scheme::withdrawal::issue;
pub use scheme::withdrawal::issue_verify;
pub use scheme::withdrawal::withdrawal_request;
pub use scheme::PartialWallet;
pub use scheme::PayInfo;
pub use traits::Base58;

mod error;
pub(crate) mod proofs;
pub mod scheme;

mod constants;
mod traits;
pub(crate) mod utils;

pub type Attribute = Scalar;
