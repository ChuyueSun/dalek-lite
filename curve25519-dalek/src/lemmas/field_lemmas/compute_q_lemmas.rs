#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::load8_lemmas::*;
use super::pow2_51_lemmas::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// ============================================================================
// LEMMA 1: Computing q (the quotient when dividing by p)
// ============================================================================
pub proof fn lemma_bounded_shr_51(x: u64)
    requires
        x < 3 * pow2(51),
    ensures
        (x >> 51) < 3,
{
    // x >> 51 == x / pow2(51)
    lemma_u64_shr_is_div(x, 51);
    // x < 3 * pow2(51), so x / pow2(51) < 3
    lemma_pow2_pos(51nat);
    lemma_div_strictly_bounded(x as int, pow2(51) as int, 3int);
}

/// Helper lemma: Proves the algebraic expansion and cancellation of intermediate terms
/// Shows that when expanding the substituted limbs, q0, q1, q2, q3 all cancel out
proof fn lemma_radix51_telescoping_expansion(
    q0: int,
    q1: int,
    q2: int,
    q3: int,
    q4: int,
    r0: int,
    r1: int,
    r2: int,
    r3: int,
    r4: int,
)
    requires
        true,
    ensures
        (q0 * pow2(51) as int + r0 - 19) + (q1 * pow2(51) as int + r1 - q0) * pow2(51) as int + (q2
            * pow2(51) as int + r2 - q1) * pow2(102) as int + (q3 * pow2(51) as int + r3 - q2)
            * pow2(153) as int + (q4 * pow2(51) as int + r4 - q3) * pow2(204) as int + 19 == q4
            * pow2(51) as int * pow2(204) as int + r0 + r1 * pow2(51) as int + r2 * pow2(102) as int
            + r3 * pow2(153) as int + r4 * pow2(204) as int,
{
    // Establish pow2 products for telescoping
    let p51 = pow2(51) as int;
    let p102 = pow2(102) as int;
    let p153 = pow2(153) as int;
    let p204 = pow2(204) as int;

    lemma_pow2_adds(51, 51);   // pow2(102) = pow2(51) * pow2(51)
    lemma_pow2_adds(51, 102);  // pow2(153) = pow2(51) * pow2(102)
    lemma_pow2_adds(51, 153);  // pow2(204) = pow2(51) * pow2(153)
    lemma_pow2_adds(51, 204);  // pow2(255) = pow2(51) * pow2(204)

    assert(p51 * p51 == p102);
    assert(p51 * p102 == p153);
    assert(p51 * p153 == p204);
    let p255 = pow2(255) as int;
    assert(p51 * p204 == p255);

    // Use nonlinear arithmetic with the pow2 facts to verify the algebraic identity
    assert((q0 * p51 + r0 - 19) + (q1 * p51 + r1 - q0) * p51 + (q2
            * p51 + r2 - q1) * p102 + (q3 * p51 + r3 - q2)
            * p153 + (q4 * p51 + r4 - q3) * p204 + 19 == q4
            * p51 * p204 + r0 + r1 * p51 + r2 * p102
            + r3 * p153 + r4 * p204) by (nonlinear_arith)
        requires
            p51 * p51 == p102,
            p51 * p102 == p153,
            p51 * p153 == p204,
            p51 * p204 == p255,
    ;
}

/// Direct proof of telescoping division for radix-51 representation
/// Uses repeated substitution to show q4 = (u64_5_as_nat(limbs) + 19) / 2^255
///
/// Proof strategy:
/// 1. Express u64_5_as_nat(limbs) + 19 as a sum using radix-51: Σ limbs[i] * 2^(51*i) + 19
/// 2. Substitute each limb using the division theorem equations (from requires clause)
/// 3. Expand and observe that intermediate q_i terms telescope (cancel out):
///    - q0 appears as: +q0*2^51 - q0*2^51 = 0
///    - q1 appears as: +q1*2^102 - q1*2^102 = 0  (and so on)
/// 4. After cancellation: value = q4 * 2^255 + remainder, where remainder < 2^255
/// 5. By uniqueness of division, q4 = value / 2^255
pub proof fn lemma_radix51_telescoping_direct(
    limbs: [u64; 5],
    q0: int,
    q1: int,
    q2: int,
    q3: int,
    q4: int,
    r0: int,
    r1: int,
    r2: int,
    r3: int,
    r4: int,
)
    requires
        limbs[0] as int + 19 == q0 * pow2(51) as int + r0,
        limbs[1] as int + q0 == q1 * pow2(51) as int + r1,
        limbs[2] as int + q1 == q2 * pow2(51) as int + r2,
        limbs[3] as int + q2 == q3 * pow2(51) as int + r3,
        limbs[4] as int + q3 == q4 * pow2(51) as int + r4,
        0 <= r0 < pow2(51) as int,
        0 <= r1 < pow2(51) as int,
        0 <= r2 < pow2(51) as int,
        0 <= r3 < pow2(51) as int,
        0 <= r4 < pow2(51) as int,
    ensures
        q4 == (u64_5_as_nat(limbs) as int + 19) / pow2(255) as int,
{
    // Step 1: Use the telescoping expansion to show the algebraic identity
    lemma_radix51_telescoping_expansion(q0, q1, q2, q3, q4, r0, r1, r2, r3, r4);
    // This gives us:
    // (q0*pow2(51) + r0 - 19) + (q1*pow2(51) + r1 - q0)*pow2(51) + ...
    //   + (q4*pow2(51) + r4 - q3)*pow2(204) + 19
    //   == q4*pow2(51)*pow2(204) + r0 + r1*pow2(51) + r2*pow2(102) + r3*pow2(153) + r4*pow2(204)

    // Step 2: The LHS equals u64_5_as_nat(limbs) + 19
    // From the requires:
    //   limbs[0] + 19 == q0*pow2(51) + r0  =>  q0*pow2(51) + r0 - 19 == limbs[0]
    //   limbs[1] + q0 == q1*pow2(51) + r1  =>  q1*pow2(51) + r1 - q0 == limbs[1]
    //   etc.
    // So the LHS = limbs[0] + limbs[1]*pow2(51) + ... + limbs[4]*pow2(204) + 19
    //            = u64_5_as_nat(limbs) + 19

    // Establish commutativity for u64_5_as_nat matching
    lemma_mul_is_commutative(pow2(51) as int, limbs[1] as int);
    lemma_mul_is_commutative(pow2(102) as int, limbs[2] as int);
    lemma_mul_is_commutative(pow2(153) as int, limbs[3] as int);
    lemma_mul_is_commutative(pow2(204) as int, limbs[4] as int);

    // Step 3: pow2(51) * pow2(204) = pow2(255)
    lemma_pow2_adds(51, 204);
    assert(q4 * pow2(51) as int * pow2(204) as int == q4 * pow2(255) as int) by {
        lemma_mul_is_associative(q4, pow2(51) as int, pow2(204) as int);
    };

    // Step 4: The remainder is bounded by pow2(255)
    let rem = r0 + r1 * pow2(51) as int + r2 * pow2(102) as int + r3 * pow2(153) as int + r4 * pow2(204) as int;
    lemma_radix51_remainder_bound(r0, r1, r2, r3, r4);
    assert(0 <= rem);
    assert(rem < pow2(255) as int);

    // Step 5: So u64_5_as_nat(limbs) + 19 = q4 * pow2(255) + rem
    // with 0 <= rem < pow2(255)
    // By uniqueness of division, q4 == (u64_5_as_nat(limbs) + 19) / pow2(255)
    lemma_pow2_pos(255nat);
    let val = u64_5_as_nat(limbs) as int + 19;
    assert(val == q4 * pow2(255) as int + rem);
    lemma_fundamental_div_mod_converse(val, pow2(255) as int, q4, rem);
}

/// Helper: Proves the remainder from radix-51 representation is bounded by 2^255
pub proof fn lemma_radix51_remainder_bound(r0: int, r1: int, r2: int, r3: int, r4: int)
    requires
        0 <= r0 < (pow2(51) as int),
        0 <= r1 < (pow2(51) as int),
        0 <= r2 < (pow2(51) as int),
        0 <= r3 < (pow2(51) as int),
        0 <= r4 < (pow2(51) as int),
    ensures
        r0 + r1 * (pow2(51) as int) + r2 * (pow2(102) as int) + r3 * (pow2(153) as int) + r4 * (
        pow2(204) as int) < (pow2(255) as int),
{
    // Each ri < pow2(51), so ri * pow2(51*i) < pow2(51) * pow2(51*i) = pow2(51*(i+1))
    // The sum is bounded by pow2(51) - 1 + (pow2(51)-1)*pow2(51) + ... + (pow2(51)-1)*pow2(204)
    // = pow2(51) - 1 + pow2(102) - pow2(51) + pow2(153) - pow2(102) + pow2(204) - pow2(153) + pow2(255) - pow2(204)
    // = pow2(255) - 1

    // Bound each term
    // r4 * pow2(204) <= (pow2(51)-1) * pow2(204) = pow2(255) - pow2(204)
    lemma_pow2_adds(51, 204);
    lemma_mul_inequality(r4, pow2(51) as int - 1, pow2(204) as int);
    lemma_mul_is_distributive_sub(pow2(204) as int, pow2(51) as int, 1int);
    assert(r4 * pow2(204) as int <= pow2(255) as int - pow2(204) as int);

    // r3 * pow2(153) <= (pow2(51)-1) * pow2(153) = pow2(204) - pow2(153)
    lemma_pow2_adds(51, 153);
    lemma_mul_inequality(r3, pow2(51) as int - 1, pow2(153) as int);
    lemma_mul_is_distributive_sub(pow2(153) as int, pow2(51) as int, 1int);
    assert(r3 * pow2(153) as int <= pow2(204) as int - pow2(153) as int);

    // r2 * pow2(102) <= (pow2(51)-1) * pow2(102) = pow2(153) - pow2(102)
    lemma_pow2_adds(51, 102);
    lemma_mul_inequality(r2, pow2(51) as int - 1, pow2(102) as int);
    lemma_mul_is_distributive_sub(pow2(102) as int, pow2(51) as int, 1int);
    assert(r2 * pow2(102) as int <= pow2(153) as int - pow2(102) as int);

    // r1 * pow2(51) <= (pow2(51)-1) * pow2(51) = pow2(102) - pow2(51)
    lemma_pow2_adds(51, 51);
    lemma_mul_inequality(r1, pow2(51) as int - 1, pow2(51) as int);
    lemma_mul_is_distributive_sub(pow2(51) as int, pow2(51) as int, 1int);
    assert(r1 * pow2(51) as int <= pow2(102) as int - pow2(51) as int);

    // r0 <= pow2(51) - 1
    // Sum: all terms telescope to <= pow2(255) - 1 < pow2(255)
}

/// Helper: Establishes basic power-of-2 facts needed for carry propagation
pub proof fn lemma_carry_propagation_setup()
    ensures
        (1u64 << 51) == pow2(51),
        (1u64 << 52) == pow2(52),
        pow2(52) == 2 * pow2(51),
        19 < pow2(51),
        3 * pow2(51) <= u64::MAX,
{
    lemma_u64_shift_is_pow2(51);
    lemma_u64_shift_is_pow2(52);
    lemma_pow2_adds(1, 51);
    lemma2_to64();
    assert(pow2(52) == pow2(1) * pow2(51) == 2 * pow2(51));

    // 19 < pow2(51): pow2(51) > pow2(5) = 32 > 19
    lemma_pow2_strictly_increases(5, 51);

    // 3 * pow2(51) <= u64::MAX
    // pow2(51) = 2251799813685248
    // 3 * pow2(51) = 6755399441055744, which is much less than u64::MAX = 18446744073709551615
    assert(3 * pow2(51) <= u64::MAX) by {
        lemma_u64_pow2_le_max(51);
        // pow2(51) <= u64::MAX, and 3*pow2(51) < pow2(53) <= u64::MAX since 53 < 64
        lemma_pow2_adds(51, 2);
        lemma_u64_pow2_le_max(53);
        assert(3 * pow2(51) < pow2(53)) by {
            assert(pow2(2) == 4) by (compute);
            lemma_mul_strict_inequality(3, pow2(2) as int, pow2(51) as int);
        };
    };
}

/// Helper: Proves the division relationship for a single carry propagation stage
/// Given limb_i and carry_in q_{i-1}, computes q_i = (limb_i + q_{i-1}) >> 51
/// and establishes the division theorem relationship
///
/// Note: carry_in is typically < 3 for stages 1-4, but equals 19 for stage 0
pub proof fn lemma_single_stage_division(limb: u64, carry_in: u64, stage_input: u64, carry_out: u64)
    requires
        limb < (1u64 << 52),
        limb + carry_in <= u64::MAX,  // No overflow
        stage_input == (limb + carry_in) as u64,
        stage_input < 3 * pow2(51),
        carry_out == (stage_input >> 51) as u64,
    ensures
        carry_out < 3,
        carry_out as int == (limb as int + carry_in as int) / pow2(51) as int,
{
    // carry_out = stage_input >> 51
    // stage_input < 3 * pow2(51)
    // So carry_out < 3 by lemma_bounded_shr_51
    lemma_bounded_shr_51(stage_input);

    // carry_out >> 51 is stage_input / pow2(51)
    lemma_u64_shr_is_div(stage_input, 51);
    // stage_input == limb + carry_in (no overflow by precondition)
    assert(stage_input as int == limb as int + carry_in as int);
}

/// Helper: Establishes division theorem for a single stage
/// Given the inputs and outputs of a stage, proves the division/modulo relationship
///
/// Note: carry_in is typically < 3 for stages 1-4, but equals 19 for stage 0
pub proof fn lemma_stage_division_theorem(limb: u64, carry_in: int, carry_out: int) -> (r: int)
    requires
        limb < (1u64 << 52),
        carry_out == (limb as int + carry_in) / pow2(51) as int,
    ensures
        (limb as int + carry_in) == carry_out * pow2(51) as int + r,
        0 <= r < pow2(51) as int,
{
    let val = limb as int + carry_in;
    let p51 = pow2(51) as int;
    lemma_pow2_pos(51nat);
    // By fundamental div/mod theorem
    lemma_fundamental_div_mod(val, p51);
    // val == (val / p51) * p51 + val % p51
    // carry_out == val / p51
    let r = val % p51;
    // 0 <= r < p51 by definition of modulo
    lemma_mod_bound(val, p51);
    r
}

/// Helper lemma: proves that the carry propagation computes the division by 2^255
/// This shows that q represents (u64_5_as_nat(limbs) + 19) / 2^255
///
/// Refactored into smaller pieces for better readability and maintainability.
pub proof fn lemma_carry_propagation_is_division(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        q == compute_q_spec(limbs),
    ensures
        q as nat == (u64_5_as_nat(limbs) + 19) / pow2(255),
{
    // Setup: establish basic facts
    lemma_carry_propagation_setup();

    // Extract the carry chain from compute_q_spec
    let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
    let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
    let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
    let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
    let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
    assert(q == q4);

    // Stage 0: limbs[0] + 19, carry_in = 19
    // limbs[0] < 2^52, 19 < 2^51, so limbs[0] + 19 < 2^52 + 2^51 = 3 * 2^51
    let s0 = (limbs[0] + 19) as u64;
    assert(s0 < 3 * pow2(51)) by {
        assert(limbs[0] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[0], 19u64, s0, q0);
    assert(q0 < 3);
    assert(q0 as int == (limbs[0] as int + 19) / pow2(51) as int);

    // Stage 1: limbs[1] + q0, carry_in = q0 < 3
    let s1 = (limbs[1] + q0) as u64;
    assert(s1 < 3 * pow2(51)) by {
        assert(limbs[1] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[1], q0, s1, q1);
    assert(q1 < 3);
    assert(q1 as int == (limbs[1] as int + q0 as int) / pow2(51) as int);

    // Stage 2: limbs[2] + q1
    let s2 = (limbs[2] + q1) as u64;
    assert(s2 < 3 * pow2(51)) by {
        assert(limbs[2] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[2], q1, s2, q2);
    assert(q2 < 3);
    assert(q2 as int == (limbs[2] as int + q1 as int) / pow2(51) as int);

    // Stage 3: limbs[3] + q2
    let s3 = (limbs[3] + q2) as u64;
    assert(s3 < 3 * pow2(51)) by {
        assert(limbs[3] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[3], q2, s3, q3);
    assert(q3 < 3);
    assert(q3 as int == (limbs[3] as int + q2 as int) / pow2(51) as int);

    // Stage 4: limbs[4] + q3
    let s4 = (limbs[4] + q3) as u64;
    assert(s4 < 3 * pow2(51)) by {
        assert(limbs[4] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[4], q3, s4, q4);
    assert(q4 < 3);
    assert(q4 as int == (limbs[4] as int + q3 as int) / pow2(51) as int);

    // Now get the division theorem remainders
    let r0 = lemma_stage_division_theorem(limbs[0], 19, q0 as int);
    let r1 = lemma_stage_division_theorem(limbs[1], q0 as int, q1 as int);
    let r2 = lemma_stage_division_theorem(limbs[2], q1 as int, q2 as int);
    let r3 = lemma_stage_division_theorem(limbs[3], q2 as int, q3 as int);
    let r4 = lemma_stage_division_theorem(limbs[4], q3 as int, q4 as int);

    // Now we have:
    // limbs[0] + 19 == q0 * pow2(51) + r0
    // limbs[1] + q0 == q1 * pow2(51) + r1
    // limbs[2] + q1 == q2 * pow2(51) + r2
    // limbs[3] + q2 == q3 * pow2(51) + r3
    // limbs[4] + q3 == q4 * pow2(51) + r4

    // Use telescoping to conclude
    lemma_radix51_telescoping_direct(limbs, q0 as int, q1 as int, q2 as int, q3 as int, q4 as int, r0, r1, r2, r3, r4);
}

// lemma_radix_51_geometric_sum: MOVED to unused_helper_lemmas.rs (superseded by lemma_radix_51_partial_geometric_sum)
/// Helper: Proves all intermediate carries are bounded by 3
pub proof fn lemma_all_carries_bounded_by_3(limbs: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
    ensures
        ({
            let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
            let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
            let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
            let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
            let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
            q0 < 3 && q1 < 3 && q2 < 3 && q3 < 3 && q4 < 3
        }),
{
    lemma_carry_propagation_setup();

    let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
    let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
    let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
    let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
    let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;

    // Stage 0
    let s0 = (limbs[0] + 19) as u64;
    assert(s0 < 3 * pow2(51)) by {
        assert(limbs[0] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[0], 19u64, s0, q0);

    // Stage 1
    let s1 = (limbs[1] + q0) as u64;
    assert(s1 < 3 * pow2(51)) by {
        assert(limbs[1] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[1], q0, s1, q1);

    // Stage 2
    let s2 = (limbs[2] + q1) as u64;
    assert(s2 < 3 * pow2(51)) by {
        assert(limbs[2] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[2], q1, s2, q2);

    // Stage 3
    let s3 = (limbs[3] + q2) as u64;
    assert(s3 < 3 * pow2(51)) by {
        assert(limbs[3] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[3], q2, s3, q3);

    // Stage 4
    let s4 = (limbs[4] + q3) as u64;
    assert(s4 < 3 * pow2(51)) by {
        assert(limbs[4] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(limbs[4], q3, s4, q4);
}

/// Helper: Proves q can only be 0 or 1 (not 2)
/// Also establishes the division relationship for reuse
pub proof fn lemma_q_is_binary(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        u64_5_as_nat(limbs) < 2 * p(),  // From reduce()'s postcondition
        q == compute_q_spec(limbs),
        q < 3,
    ensures
        q == 0 || q == 1,
        q as nat == (u64_5_as_nat(limbs) + 19) / pow2(255),  // Export for reuse
{
    // First establish the division relationship
    lemma_carry_propagation_is_division(limbs, q);
    assert(q as nat == (u64_5_as_nat(limbs) + 19) / pow2(255));

    // Now show q < 2 (i.e., q == 0 || q == 1)
    // val = u64_5_as_nat(limbs) < 2 * p() = 2 * (2^255 - 19) = 2^256 - 38
    // val + 19 < 2^256 - 38 + 19 = 2^256 - 19 < 2^256 = 2 * 2^255
    // So (val + 19) / 2^255 < 2, meaning q < 2

    let val = u64_5_as_nat(limbs);
    assert(val < 2 * p());
    // p() = pow2(255) - 19
    pow255_gt_19();
    assert(p() == (pow2(255) - 19) as nat);
    assert(val + 19 < 2 * pow2(255)) by {
        // 2 * p() = 2 * (pow2(255) - 19) = 2 * pow2(255) - 38
        // val < 2 * pow2(255) - 38
        // val + 19 < 2 * pow2(255) - 38 + 19 = 2 * pow2(255) - 19 < 2 * pow2(255)
        assert(2 * p() == 2 * pow2(255) - 38) by {
            lemma_mul_is_distributive_sub(2int, pow2(255) as int, 19int);
        };
    };

    // (val + 19) / pow2(255) < 2
    lemma_pow2_pos(255nat);
    lemma_div_strictly_bounded((val + 19) as int, pow2(255) as int, 2int);
    assert(q < 2);
}

/// Unified helper: Proves the biconditional relationship between u64_5_as_nat and q
///
/// With the tight bound u64_5_as_nat(limbs) < 2*p(), the value is either in [0, p) or [p, 2*p),
/// which maps directly to q=0 or q=1. This makes the biconditional proofs straightforward.
pub proof fn lemma_q_biconditional(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        u64_5_as_nat(limbs) < 2 * p(),  // Tight bound from reduce()
        q == compute_q_spec(limbs),
        q as nat == (u64_5_as_nat(limbs) + 19) / pow2(255),
        q == 0 || q == 1,
    ensures
        u64_5_as_nat(limbs) >= p() <==> q == 1,
        u64_5_as_nat(limbs) < p() <==> q == 0,
{
    let val = u64_5_as_nat(limbs);
    let p255 = pow2(255);
    pow255_gt_19();
    lemma_pow2_pos(255nat);
    assert(p() == (p255 - 19) as nat);

    // Case 1: val >= p() implies q == 1
    // val >= p() = 2^255 - 19 means val + 19 >= 2^255
    // So (val + 19) / 2^255 >= 1
    // Since q <= 1, we get q == 1
    if val >= p() {
        assert(val + 19 >= p255);
        // (val + 19) / pow2(255) >= pow2(255) / pow2(255) = 1
        lemma_div_is_ordered(p255 as int, (val + 19) as int, p255 as int);
        lemma_div_by_self(p255 as int);
        assert(q as nat >= 1);
        assert(q == 1);
    }

    // Case 2: val < p() implies q == 0
    // val < p() = 2^255 - 19 means val + 19 < 2^255
    // So (val + 19) / 2^255 == 0
    if val < p() {
        assert(val + 19 < p255);
        lemma_div_is_ordered(0int, (val + 19) as int, p255 as int);
        lemma_div_by_self(p255 as int);
        assert((val + 19) / p255 < 1) by {
            lemma_div_strictly_bounded((val + 19) as int, p255 as int, 1int);
        };
        assert(q as nat == 0);
        assert(q == 0);
    }
}

/// Proves that q computed via successive carry propagation equals 1 iff h >= p, 0 otherwise
/// where h = u64_5_as_nat(limbs) and limbs[i] < 2^52 for all i
///
/// The precondition `u64_5_as_nat(limbs) < 2 * p()` is satisfied when limbs come from
/// `reduce()` output, which now ensures this property in its postcondition.
pub proof fn lemma_compute_q(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        u64_5_as_nat(limbs) < 2 * p(),  // From reduce()'s postcondition
        q == compute_q_spec(limbs),
    ensures
        q == 0 || q == 1,
        u64_5_as_nat(limbs) >= p() <==> q == 1,
        u64_5_as_nat(limbs) < p() <==> q == 0,
{
    // Step 1: All carries are bounded by 3
    lemma_all_carries_bounded_by_3(limbs);
    assert(q < 3);

    // Step 2: q is binary (0 or 1)
    lemma_q_is_binary(limbs, q);

    // Step 3: Biconditional
    lemma_q_biconditional(limbs, q);
}

} // verus!
