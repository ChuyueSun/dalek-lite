//! Experiment 15: Mode B feasibility test sub-lemmas
//!
//! This file contains isolated sub-lemma tests extracted from
//! lemma_double_projective_completed_valid (double_correctness.rs).

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

// ==========================================================================
// PART A (completed)
// ==========================================================================

// Part A Step 4 sibling (completed)
pub proof fn lemma_step4_result_Z(
    result_Z: nat,
    xx_val: nat, yy_val: nat,
    z2: nat, x2: nat, y2: nat, t: nat,
)
    requires
        result_Z == field_sub(yy_val, xx_val),
        xx_val == field_mul(x2, z2),
        yy_val == field_mul(y2, z2),
        field_sub(y2, x2) == field_add(1, t),
    ensures
        result_Z == field_mul(z2, field_add(1, t)),
{
    lemma_factor_result_component_sub(y2, x2, z2);
}

// Part A Step 5 target (completed)
pub proof fn lemma_step5_result_T(
    result_T: nat,
    zz2_val: nat, xx_val: nat, yy_val: nat,
    z2: nat, x2: nat, y2: nat, t: nat,
)
    requires
        result_T == field_sub(zz2_val, field_sub(yy_val, xx_val)),
        zz2_val == field_mul(2, z2),
        xx_val == field_mul(x2, z2),
        yy_val == field_mul(y2, z2),
        field_sub(y2, x2) == field_add(1, t),
        x2 < p(),
        y2 < p(),
        z2 < p(),
        t < p(),
    ensures
        result_T == field_mul(z2, field_sub(1, t)),
{
    lemma_factor_result_component_sub(y2, x2, z2);
    lemma_field_mul_comm(2, z2);
    lemma_factor_result_component_sub(2, field_sub(y2, x2), z2);
    p_gt_2();
    lemma_small_mod(2, p());
    assert(field_add(1, 1) == 2nat);
    lemma_field_add_comm(1, t);
    lemma_field_sub_add_common_right(1, t, 1);
}

// ==========================================================================
// PART B: Steps 1-5 combined (68 LOC in GT)
// ==========================================================================

// SIBLING TEMPLATE (Step 2 completed): result.X = Z²·(2·xy)
//
// This shows the proof style for component expressions:
//   1. Factor projective products through Z²
//   2. Apply algebraic identity
//   3. Reassociate to get Z²·(affine expression)
pub proof fn lemma_step2_result_X(
    pX: nat, pY: nat, pZ: nat,
    x: nat, y: nat,
    z2: nat, xy: nat,
    xx_val: nat, yy_val: nat, xpy_sq_val: nat,
    result_X: nat,
)
    requires
        pX < p(), pY < p(), pZ < p(),
        pZ % p() != 0,
        x == field_mul(pX, field_inv(pZ)),
        y == field_mul(pY, field_inv(pZ)),
        z2 == field_square(pZ),
        xy == field_mul(x, y),
        xx_val == field_square(pX),
        yy_val == field_square(pY),
        xpy_sq_val == field_square(field_add(pX, pY)),
        result_X == field_sub(xpy_sq_val, field_add(yy_val, xx_val)),
    ensures
        result_X == field_mul(z2, field_mul(2, xy)),
{
    // Step 1 (partial): X·Y = xy·Z²  (projective product factoring)
    assert(field_mul(pX, pY) == field_mul(xy, z2)) by {
        lemma_projective_product_factor(pX, pZ, pY, pZ);
    };

    // Step 2a: (X+Y)² - (Y²+X²) = 2·X·Y  (binomial expansion)
    assert(result_X == field_mul(2, field_mul(pX, pY))) by {
        lemma_square_sum_expansion(pX, pY);
    };

    // Step 2b: 2·(xy·Z²) = Z²·(2·xy)  (reassociation)
    lemma_reassociate_2_z_num(z2, xy);
}

// TARGET: Steps 1-5 combined — factor all 4 result components through Z²
//
// Given:
//   - Projective point (pX:pY:pZ) with affine (x,y) = (pX/pZ, pY/pZ)
//   - Doubling formula intermediate values xx_val, yy_val, zz2_val, xpy_sq_val
//   - Result component values result_X, result_Y, result_Z, result_T
//   - Curve equation: y² - x² = 1 + t
//
// Prove all 4 result components equal Z² times their affine equivalents.
pub proof fn lemma_all_component_expressions(
    // Projective coordinates
    pX: nat, pY: nat, pZ: nat,
    // Affine coordinates (= projective / Z)
    x: nat, y: nat,
    // Affine derived values
    z2: nat, x2: nat, y2: nat, xy: nat, t: nat,
    // Doubling formula intermediate values
    xx_val: nat, yy_val: nat, zz2_val: nat, xpy_sq_val: nat,
    // Result component values
    result_X: nat, result_Y: nat, result_Z: nat, result_T: nat,
)
    requires
        // Projective coordinates are field elements
        pX < p(), pY < p(), pZ < p(),
        pZ % p() != 0,
        // Affine coordinates via division
        x == field_mul(pX, field_inv(pZ)),
        y == field_mul(pY, field_inv(pZ)),
        // Derived values
        z2 == field_square(pZ),
        x2 == field_square(x),
        y2 == field_square(y),
        xy == field_mul(x, y),
        t < p(),
        // Bounds on derived values
        x < p(), y < p(), z2 < p(), x2 < p(), y2 < p(), xy < p(),
        // Curve equation: y² - x² = 1 + d·x²·y²
        field_sub(y2, x2) == field_add(1, t),
        // Doubling formula intermediate values
        xx_val == field_square(pX),
        yy_val == field_square(pY),
        zz2_val == field_mul(2, field_square(pZ)),
        xpy_sq_val == field_square(field_add(pX, pY)),
        // Result component definitions
        result_X == field_sub(xpy_sq_val, field_add(yy_val, xx_val)),
        result_Y == field_add(yy_val, xx_val),
        result_Z == field_sub(yy_val, xx_val),
        result_T == field_sub(zz2_val, field_sub(yy_val, xx_val)),
    ensures
        result_X == field_mul(z2, field_mul(2, xy)),
        result_Y == field_mul(z2, field_add(y2, x2)),
        result_Z == field_mul(z2, field_add(1, t)),
        result_T == field_mul(z2, field_sub(1, t)),
{
    // Step 1: Factor projective squares/products through Z²
    // field_square(pX) = field_mul(x2, z2)
    assert(xx_val == field_mul(x2, z2)) by {
        lemma_projective_product_factor(pX, pZ, pX, pZ);
    };
    // field_square(pY) = field_mul(y2, z2)
    assert(yy_val == field_mul(y2, z2)) by {
        lemma_projective_product_factor(pY, pZ, pY, pZ);
    };
    // field_mul(pX, pY) = field_mul(xy, z2)
    assert(field_mul(pX, pY) == field_mul(xy, z2)) by {
        lemma_projective_product_factor(pX, pZ, pY, pZ);
    };

    // Step 2: result_X = Z²·(2·xy)
    // (X+Y)² - (Y²+X²) = 2·X·Y
    assert(result_X == field_mul(2, field_mul(pX, pY))) by {
        lemma_square_sum_expansion(pX, pY);
    };
    // 2·(xy·Z²) = Z²·(2·xy)
    lemma_reassociate_2_z_num(z2, xy);

    // Step 3: result_Y = Z²·(y²+x²)
    // yy_val + xx_val = y2·z2 + x2·z2 = z2·(y2+x2)
    lemma_factor_result_component_add(y2, x2, z2);

    // Step 4: result_Z = Z²·(1+t)
    // yy_val - xx_val = y2·z2 - x2·z2 = z2·(y2-x2) = z2·(1+t)
    lemma_factor_result_component_sub(y2, x2, z2);

    // Step 5: result_T = Z²·(1-t)
    // zz2_val = field_mul(2, z2) since field_square(pZ) = z2
    // result_T = zz2_val - (yy_val - xx_val)
    //          = field_mul(2, z2) - z2·(y2-x2)
    //          = field_mul(2, z2) - z2·field_sub(y2,x2)
    // Need: field_mul(2, z2) = z2·2
    lemma_field_mul_comm(2, z2);
    // Now: z2·2 - z2·field_sub(y2,x2) = z2·(2 - field_sub(y2,x2))
    lemma_factor_result_component_sub(2, field_sub(y2, x2), z2);
    // Now need: 2 - (1+t) = 1-t
    // 2 = 1+1
    p_gt_2();
    lemma_small_mod(2, p());
    assert(field_add(1, 1) == 2nat);
    // (1+1) - (1+t) = cancel common right addend 1: 1 - t
    lemma_field_add_comm(1, t);
    lemma_field_sub_add_common_right(1, t, 1);
}

// ==========================================================================
// PART C: Full proof with decomposition plan + preamble given
// ==========================================================================

/// Bridge lemma: the projective doubling formulas produce a valid CompletedPoint
/// whose affine projection equals `edwards_double(x, y)`.
///
/// This is the ORIGINAL R5 function (same requires/ensures as the GT).
pub proof fn lemma_double_projective_completed_valid_part_c(
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
    // ===== PREAMBLE (given for free) =====
    let pX = fe51_as_canonical_nat(&self_point.X);
    let pY = fe51_as_canonical_nat(&self_point.Y);
    let pZ = fe51_as_canonical_nat(&self_point.Z);
    let p = p();
    let p_i = p as int;

    assert(p > 2) by {
        p_gt_2();
    };

    assert(pX < p) by {
        lemma_mod_bound(u64_5_as_nat(self_point.X.limbs) as int, p_i);
    }
    assert(pY < p) by {
        lemma_mod_bound(u64_5_as_nat(self_point.Y.limbs) as int, p_i);
    }
    assert(pZ < p) by {
        lemma_mod_bound(u64_5_as_nat(self_point.Z.limbs) as int, p_i);
    }

    assert(pZ != 0);
    assert(pZ % p != 0) by {
        lemma_field_element_reduced(pZ);
    };

    let z_inv = field_inv(pZ);
    let x = field_mul(pX, z_inv);
    let y = field_mul(pY, z_inv);

    assert(is_on_edwards_curve(x, y)) by {
        lemma_projective_implies_affine_on_curve(pX, pY, pZ);
    };

    let z2 = field_square(pZ);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let xy = field_mul(x, y);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let t = field_mul(d, field_mul(x2, y2));

    assert(x < p) by {
        lemma_mod_bound((pX * z_inv) as int, p_i);
    }
    assert(y < p) by {
        lemma_mod_bound((pY * z_inv) as int, p_i);
    }
    assert(z2 < p) by {
        lemma_mod_bound((pZ * pZ) as int, p_i);
    }
    assert(x2 < p) by {
        lemma_mod_bound((x * x) as int, p_i);
    }
    assert(y2 < p) by {
        lemma_mod_bound((y * y) as int, p_i);
    }
    assert(xy < p) by {
        lemma_mod_bound((x * y) as int, p_i);
    }
    // ===== END PREAMBLE =====

    // ===== TARGET: Steps 1-8 + conclusion =====

    // --- Step 1: Factor projective squares through Z² ---
    assert(xx_val == field_mul(x2, z2)) by {
        lemma_projective_product_factor(pX, pZ, pX, pZ);
    };
    assert(yy_val == field_mul(y2, z2)) by {
        lemma_projective_product_factor(pY, pZ, pY, pZ);
    };
    assert(field_mul(pX, pY) == field_mul(xy, z2)) by {
        lemma_projective_product_factor(pX, pZ, pY, pZ);
    };

    // --- Step 2: result.X = Z²·(2·xy) ---
    assert(fe51_as_canonical_nat(&result.X) == field_mul(2, field_mul(pX, pY))) by {
        lemma_square_sum_expansion(pX, pY);
    };
    lemma_reassociate_2_z_num(z2, xy);

    // --- Step 3: result.Y = Z²·(y²+x²) ---
    lemma_factor_result_component_add(y2, x2, z2);

    // --- Step 4: result.Z = Z²·(1+t) ---
    lemma_factor_result_component_sub(y2, x2, z2);

    // --- Step 5: result.T = Z²·(1-t) ---
    lemma_field_mul_comm(2, z2);
    lemma_factor_result_component_sub(2, field_sub(y2, x2), z2);
    p_gt_2();
    lemma_small_mod(2, p);
    assert(field_add(1, 1) == 2nat);
    lemma_field_add_comm(1, t);
    lemma_field_sub_add_common_right(1, t, 1);

    // --- Step 6: Nonzero denominators ---
    axiom_edwards_add_complete(x, y, x, y);
    // Connect the t from axiom to our local t:
    // axiom uses field_mul(d, field_mul(field_mul(x, x), field_mul(y, y)))
    // we have t = field_mul(d, field_mul(x2, y2))
    // field_mul(x, x) = field_square(x) = x2, field_mul(y, y) = field_square(y) = y2
    // So they should be equal. Assert to help SMT:
    assert(field_mul(x, x) == x2);
    assert(field_mul(y, y) == y2);
    let t_axiom = field_mul(d, field_mul(field_mul(x, x), field_mul(y, y)));
    assert(t_axiom == t);

    assert(field_add(1, t) != 0);
    assert(field_sub(1, t) != 0);

    // z2 != 0
    lemma_nonzero_product(pZ, pZ);
    assert(z2 % p != 0) by {
        lemma_field_element_reduced(z2);
    };

    // field_add(1, t) reduced
    let one_plus_t = field_add(1, t);
    assert(one_plus_t < p) by {
        lemma_mod_bound((1 + t) as int, p_i);
    };
    assert(one_plus_t % p != 0) by {
        lemma_field_element_reduced(one_plus_t);
    };

    // field_sub(1, t) reduced
    let one_minus_t = field_sub(1, t);
    assert(one_minus_t < p) by {
        lemma_mod_bound((1nat + p - field_canonical(t)) as int, p_i);
    };
    assert(one_minus_t % p != 0) by {
        lemma_field_element_reduced(one_minus_t);
    };

    // result.Z = z2 * (1+t), both nonzero => result.Z != 0
    lemma_nonzero_product(z2, one_plus_t);
    assert(fe51_as_canonical_nat(&result.Z) == field_mul(z2, one_plus_t));
    assert(fe51_as_canonical_nat(&result.Z) != 0);

    // result.T = z2 * (1-t), both nonzero => result.T != 0
    lemma_nonzero_product(z2, one_minus_t);
    assert(fe51_as_canonical_nat(&result.T) == field_mul(z2, one_minus_t));
    assert(fe51_as_canonical_nat(&result.T) != 0);

    // --- Step 7: Cancel Z² from ratios ---
    // cancel_common_factor gives: (a*c) * inv(b*c) = a * inv(b)
    // For X/Z: need field_mul(z2, field_mul(2, xy)) * inv(field_mul(z2, one_plus_t))
    //        = field_mul(2, xy) * inv(one_plus_t)
    // But cancel takes (a, b, c) and gives (a*c)*inv(b*c) = a*inv(b)
    // So we need a=field_mul(2,xy), b=one_plus_t, c=z2
    // Gives: field_mul(field_mul(field_mul(2,xy), z2), field_inv(field_mul(one_plus_t, z2)))
    //      = field_mul(field_mul(2,xy), field_inv(one_plus_t))
    lemma_cancel_common_factor(field_mul(2, xy), one_plus_t, z2);
    // But result.X = field_mul(z2, field_mul(2,xy)), need commutativity
    lemma_field_mul_comm(field_mul(2, xy), z2);
    assert(fe51_as_canonical_nat(&result.X) == field_mul(field_mul(2, xy), z2));
    // And result.Z = field_mul(z2, one_plus_t), need commutativity
    lemma_field_mul_comm(one_plus_t, z2);
    assert(fe51_as_canonical_nat(&result.Z) == field_mul(one_plus_t, z2));

    // So X/Z = field_mul(field_mul(2,xy), z2) * inv(field_mul(one_plus_t, z2))
    //        = field_mul(2,xy) * inv(one_plus_t)
    let x_over_z = field_mul(fe51_as_canonical_nat(&result.X), field_inv(fe51_as_canonical_nat(&result.Z)));
    assert(x_over_z == field_mul(field_mul(2, xy), field_inv(one_plus_t)));

    // For Y/T: a=field_add(y2,x2), b=one_minus_t, c=z2
    lemma_cancel_common_factor(field_add(y2, x2), one_minus_t, z2);
    lemma_field_mul_comm(field_add(y2, x2), z2);
    assert(fe51_as_canonical_nat(&result.Y) == field_mul(field_add(y2, x2), z2));
    lemma_field_mul_comm(one_minus_t, z2);
    assert(fe51_as_canonical_nat(&result.T) == field_mul(one_minus_t, z2));

    let y_over_t = field_mul(fe51_as_canonical_nat(&result.Y), field_inv(fe51_as_canonical_nat(&result.T)));
    assert(y_over_t == field_mul(field_add(y2, x2), field_inv(one_minus_t)));

    // --- Step 8: Connect to edwards_add(x, y, x, y) ---
    // For doubling: x1=x2=x, y1=y2=y
    // num_x of edwards_add = x*y + y*x = xy + xy = 2*xy
    lemma_field_mul_comm(y, x);
    assert(field_mul(y, x) == xy);
    lemma_add_self_eq_double(xy);
    assert(field_add(xy, xy) == field_mul(2, xy));

    // num_y = y*y + x*x = y2 + x2
    assert(field_mul(y, y) == y2);
    assert(field_mul(x, x) == x2);

    // axiom_edwards_add_complete already called, gives on-curve result
    // edwards_add(x,y,x,y):
    //   t_add = field_mul(d, field_mul(field_mul(x,x), field_mul(y,y)))
    //         = field_mul(d, field_mul(x2, y2)) = t
    //   x3 = field_mul(field_add(xy, xy), field_inv(field_add(1, t)))
    //      = field_mul(field_mul(2, xy), field_inv(one_plus_t))
    //   y3 = field_mul(field_add(y2, x2), field_inv(field_sub(1, t)))
    //      = field_mul(field_add(y2, x2), field_inv(one_minus_t))

    // Show completed_point_as_affine_edwards matches edwards_double
    assert(x_over_z == field_mul(field_mul(2, xy), field_inv(one_plus_t)));
    assert(y_over_t == field_mul(field_add(y2, x2), field_inv(one_minus_t)));

    // The on-curve result from axiom
    assert(is_on_edwards_curve(edwards_add(x, y, x, y).0, edwards_add(x, y, x, y).1));

    // Show the completed point's affine coords are on the curve
    assert(x_over_z == edwards_add(x, y, x, y).0);
    assert(y_over_t == edwards_add(x, y, x, y).1);
    assert(is_on_edwards_curve(x_over_z, y_over_t));

    // --- Conclusion ---
    assert(is_valid_completed_point(result));
    assert(completed_point_as_affine_edwards(result) == edwards_double(x, y));
}

} // verus!
