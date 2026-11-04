//! Recover keys from authenticated pairs of conflicting unit tags.
use blstrs::{G1Projective as G1, Scalar as S};
use ff::Field;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlgebraError {
    ZeroZeta,
    ZeroEta,
    ZeroMu,
    ZeroDenominator,
}

/// Evaluate the DU recovery expression, without authenticating its inputs.
///
/// This does not check matching serials, authorizations, contexts, or proofs.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn raw_du_recover(ta1: G1, ta2: G1, v1: S, v2: S) -> Result<G1, AlgebraError> {
    let inverse = Option::<S>::from((v2 - v1).invert()).ok_or(AlgebraError::ZeroDenominator)?;
    Ok(crate::ops::msm1(
        &[ta1, ta2],
        &[v2 * inverse, -v1 * inverse],
    ))
}

/// Evaluate the DA recovery expression, without authenticating its inputs.
///
/// This does not check matching serials, distinct authorizations, or proofs.
#[cfg_attr(feature = "op-counts", instrument_ops::count_ops)]
pub fn raw_da_recover(tu1: G1, tu2: G1, c1: S, c2: S) -> Result<G1, AlgebraError> {
    let inverse = Option::<S>::from((c2 - c1).invert()).ok_or(AlgebraError::ZeroDenominator)?;
    Ok(crate::ops::msm1(
        &[tu1, tu2],
        &[c2 * inverse, -c1 * inverse],
    ))
}
