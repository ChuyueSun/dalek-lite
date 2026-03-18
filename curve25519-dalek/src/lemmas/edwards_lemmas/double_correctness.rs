//! Correctness of the projective doubling formula for twisted Edwards curves.
//!
//! Proves that `ProjectivePoint::double()` correctly computes the Edwards
//! group doubling and produces a valid `CompletedPoint`.
//!
//! Given a projective point P = (X:Y:Z) with affine (x,y) = (X/Z, Y/Z):
//!
//!   XX = X²,  YY = Y²,  ZZ2 = 2·Z²
//!   XpY_sq = (X+Y)²,  YYpXX = YY+XX,  YYmXX = YY-XX
//!   result.X = XpY_sq - YYpXX = 2XY
//!   result.Y = YYpXX = Y²+X²
//!   result.Z = YYmXX = Y²-X²
//!   result.T = ZZ2 - YYmXX = 2Z²-(Y²-X²)
//!
//! Proof strategy:
//!   1. Factor: all result components share the projective factor Z²
//!   2. Curve eq: use y²-x² = 1+d·x²y² to identify result.Z, result.T as Z²·(1±t)
//!   3. Nonzero: axiom_edwards_add_complete(x,y,x,y) gives 1+t ≠ 0, 1-t ≠ 0
//!   4. Cancel: divide out Z² to get affine ratios matching edwards_add(x,y,x,y)
#[allow(unused_imports)]
use crate::backend::serial::curve_models::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::niels_addition_correctness::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Bridge lemma: the projective doubling formulas produce a valid CompletedPoint
/// whose affine projection equals `edwards_double(x, y)`.
pub proof fn lemma_double_projective_completed_valid(
    self_point: ProjectivePoint,
    result: CompletedPoint,
    xx_val: nat,
    yy_val: nat,
    zz2_val: nat,
    xpy_sq_val: nat,
)
    requires
        is_valid_projective_point(self_point),
        xx_val == field_square(fe51_as_canonical_nat(&self_point.X)),
        yy_val == field_square(fe51_as_canonical_nat(&self_point.Y)),
        zz2_val == field_mul(2, field_square(fe51_as_canonical_nat(&self_point.Z))),
        xpy_sq_val == field_square(
            field_add(fe51_as_canonical_nat(&self_point.X), fe51_as_canonical_nat(&self_point.Y)),
        ),
        fe51_as_canonical_nat(&result.X) == field_sub(xpy_sq_val, field_add(yy_val, xx_val)),
        fe51_as_canonical_nat(&result.Y) == field_add(yy_val, xx_val),
        fe51_as_canonical_nat(&result.Z) == field_sub(yy_val, xx_val),
        fe51_as_canonical_nat(&result.T) == field_sub(zz2_val, field_sub(yy_val, xx_val)),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == edwards_double(
            projective_point_as_affine_edwards(self_point).0,
            projective_point_as_affine_edwards(self_point).1,
        ),
{
    admit(); // HOLE R5
}

} // verus!
