#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::calc;
use vstd::prelude::*;

use super::compute_q_lemmas::*;
use super::load8_lemmas::*;
use super::pow2_51_lemmas::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// ============================================================================
// LEMMA 2: Value preservation through modular reduction
// ============================================================================
/// Telescoping lemma for reduction: expands u64_5_as_nat through the carry propagation
/// This is analogous to lemma_radix51_telescoping_direct but for the reduction case
pub proof fn lemma_reduction_telescoping(
    input_limbs: [u64; 5],
    final_limbs: [u64; 5],
    q: u64,
    c0: int,
    c1: int,
    c2: int,
    c3: int,
    c4: int,
)
    requires
// The carry propagation relationships

        input_limbs[0] as int + 19 * q as int == c0 * pow2(51) as int + final_limbs[0] as int,
        input_limbs[1] as int + c0 == c1 * pow2(51) as int + final_limbs[1] as int,
        input_limbs[2] as int + c1 == c2 * pow2(51) as int + final_limbs[2] as int,
        input_limbs[3] as int + c2 == c3 * pow2(51) as int + final_limbs[3] as int,
        input_limbs[4] as int + c3 == c4 * pow2(51) as int + final_limbs[4] as int,
        // final_limbs are bounded by 2^51
        final_limbs[0] < (1u64 << 51),
        final_limbs[1] < (1u64 << 51),
        final_limbs[2] < (1u64 << 51),
        final_limbs[3] < (1u64 << 51),
        final_limbs[4] < (1u64 << 51),
    ensures
        u64_5_as_nat(input_limbs) as int + 19 * q as int == u64_5_as_nat(final_limbs) as int + c4
            * pow2(255) as int,
{
    // From requires, rearrange each carry equation:
    // input_limbs[0] + 19*q = c0*pow2(51) + final_limbs[0]
    //   => input_limbs[0] = c0*pow2(51) + final_limbs[0] - 19*q
    // input_limbs[1] + c0 = c1*pow2(51) + final_limbs[1]
    //   => input_limbs[1] = c1*pow2(51) + final_limbs[1] - c0
    // etc.

    let p51 = pow2(51) as int;
    let p102 = pow2(102) as int;
    let p153 = pow2(153) as int;
    let p204 = pow2(204) as int;

    // Establish pow2 products
    lemma_pow2_adds(51, 51);   // pow2(102) = pow2(51) * pow2(51)
    lemma_pow2_adds(51, 102);  // pow2(153) = pow2(51) * pow2(102)
    lemma_pow2_adds(51, 153);  // pow2(204) = pow2(51) * pow2(153)
    lemma_pow2_adds(51, 204);  // pow2(255) = pow2(51) * pow2(204)

    assert(p51 * p51 == p102);
    assert(p51 * p102 == p153);
    assert(p51 * p153 == p204);
    let p255 = pow2(255) as int;
    assert(p51 * p204 == p255);

    // u64_5_as_nat(input) + 19*q
    // = (input[0] + p51*input[1] + p102*input[2] + p153*input[3] + p204*input[4]) + 19*q
    // = (input[0] + 19*q) + p51*input[1] + p102*input[2] + p153*input[3] + p204*input[4]
    // Substitute using carry equations:
    //   input[0] + 19*q = c0*p51 + final[0]
    //   input[1] + c0 = c1*p51 + final[1]  => input[1] = c1*p51 + final[1] - c0
    //   etc.
    // After substitution, intermediate carries cancel (telescoping):
    //   = final[0] + c0*p51 + p51*(c1*p51 + final[1] - c0) + ...
    //   = final[0] + p51*final[1] + p102*final[2] + p153*final[3] + p204*final[4] + c4*p255

    // Use nonlinear_arith with pow2 facts to verify the algebraic identity
    assert(
        (input_limbs[0] as int + 19 * q as int)
        + p51 * input_limbs[1] as int
        + p102 * input_limbs[2] as int
        + p153 * input_limbs[3] as int
        + p204 * input_limbs[4] as int
        ==
        final_limbs[0] as int
        + p51 * final_limbs[1] as int
        + p102 * final_limbs[2] as int
        + p153 * final_limbs[3] as int
        + p204 * final_limbs[4] as int
        + c4 * p255
    ) by (nonlinear_arith)
        requires
            input_limbs[0] as int + 19 * q as int == c0 * p51 + final_limbs[0] as int,
            input_limbs[1] as int + c0 == c1 * p51 + final_limbs[1] as int,
            input_limbs[2] as int + c1 == c2 * p51 + final_limbs[2] as int,
            input_limbs[3] as int + c2 == c3 * p51 + final_limbs[3] as int,
            input_limbs[4] as int + c3 == c4 * p51 + final_limbs[4] as int,
            p51 * p51 == p102,
            p51 * p102 == p153,
            p51 * p153 == p204,
            p51 * p204 == p255,
    ;

    // Commute multiplications to match u64_5_as_nat definition
    lemma_mul_is_commutative(p51, input_limbs[1] as int);
    lemma_mul_is_commutative(p102, input_limbs[2] as int);
    lemma_mul_is_commutative(p153, input_limbs[3] as int);
    lemma_mul_is_commutative(p204, input_limbs[4] as int);

    lemma_mul_is_commutative(p51, final_limbs[1] as int);
    lemma_mul_is_commutative(p102, final_limbs[2] as int);
    lemma_mul_is_commutative(p153, final_limbs[3] as int);
    lemma_mul_is_commutative(p204, final_limbs[4] as int);
}

/// Helper lemma: Multiplication preserves upper bounds
proof fn lemma_mul_upper_bound(a: nat, x: nat, b: nat)
    requires
        x <= b,
    ensures
        a * x <= a * b,
{
    lemma_mul_inequality(x as int, b as int, a as int);
    lemma_mul_is_commutative(a as int, x as int);
    lemma_mul_is_commutative(a as int, b as int);
}

/// Helper lemma: Proves the geometric series identity for 5 terms with base 2^51
/// (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204) = 2^255 - 1
proof fn lemma_geometric_sum_5_terms()
    ensures
        (pow2(51) - 1) * (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204)) == pow2(255) - 1,
{
    // Use repeated application of the geometric identity:
    // (2^a - 1) * 2^b + (2^b - 1) == 2^(a+b) - 1

    // Step 1: (2^51 - 1) * 2^51 + (2^51 - 1) = 2^102 - 1
    lemma_pow2_geometric(51, 51);
    // Step 2: (2^102 - 1) * 2^51 + (2^51 - 1) = 2^153 - 1
    lemma_pow2_geometric(102, 51);
    // Step 3: (2^153 - 1) * 2^51 + (2^51 - 1) = 2^204 - 1
    lemma_pow2_geometric(153, 51);
    // Step 4: (2^204 - 1) * 2^51 + (2^51 - 1) = 2^255 - 1
    lemma_pow2_geometric(204, 51);

    let p51 = pow2(51) as int;
    let p102 = pow2(102) as int;
    let p153 = pow2(153) as int;
    let p204 = pow2(204) as int;

    lemma_pow2_pos(51nat);

    // Now we need to show that
    // (p51 - 1) * (1 + p51 + p102 + p153 + p204) = p255 - 1
    // Distribute:
    lemma_mul_distributive_5_terms(p51 - 1, 1, p51, p102, p153, p204);
    // (p51-1)*1 + (p51-1)*p51 + (p51-1)*p102 + (p51-1)*p153 + (p51-1)*p204

    // (p51-1)*1 = p51 - 1
    lemma_mul_basics_3(p51 - 1);

    // Each term (p51-1)*p(k) uses the geometric identity already established
    // (p51-1)*p51 = p102 - p51 (from step 1 rearranged)
    lemma_mul_is_distributive_sub(p51, p51, 1);
    lemma_pow2_adds(51, 51);

    // (p51-1)*p102 = p153 - p102
    lemma_mul_is_distributive_sub(p102, p51, 1);
    lemma_pow2_adds(51, 102);

    // (p51-1)*p153 = p204 - p153
    lemma_mul_is_distributive_sub(p153, p51, 1);
    lemma_pow2_adds(51, 153);

    // (p51-1)*p204 = p255 - p204
    lemma_mul_is_distributive_sub(p204, p51, 1);
    lemma_pow2_adds(51, 204);

    // Sum telescopes: (p51-1) + (p102-p51) + (p153-p102) + (p204-p153) + (p255-p204) = p255-1
}

/// Helper lemma: u64_5_as_nat bound for 51-bit limbs
/// If each limb < 2^51, then u64_5_as_nat < 2^255
pub proof fn lemma_as_nat_bound_from_51bit_limbs(limbs: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        u64_5_as_nat(limbs) < pow2(255),
{
    // (1u64 << 51) == pow2(51)
    lemma_u64_shift_is_pow2(51);

    // Use the remainder bound from compute_q_lemmas
    lemma_radix51_remainder_bound(
        limbs[0] as int,
        limbs[1] as int,
        limbs[2] as int,
        limbs[3] as int,
        limbs[4] as int,
    );

    // The lemma gives us exactly what we need since u64_5_as_nat matches the sum form
    lemma_mul_is_commutative(pow2(51) as int, limbs[1] as int);
    lemma_mul_is_commutative(pow2(102) as int, limbs[2] as int);
    lemma_mul_is_commutative(pow2(153) as int, limbs[3] as int);
    lemma_mul_is_commutative(pow2(204) as int, limbs[4] as int);
}

/// Helper lemma: Proves that the carry propagation in reduction computes the division by 2^255
/// This is analogous to lemma_carry_propagation_is_division but for the reduction step
pub proof fn lemma_reduction_carry_propagation_is_division(input_limbs: [u64; 5], q: u64, c4: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        c4 == ({
            let l0 = (input_limbs[0] + 19 * q) as u64;
            let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
            let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
            let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
            let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
            l4 >> 51
        }),
    ensures
        c4 as int == (u64_5_as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int),
{
    // Setup basic pow2 facts
    lemma_carry_propagation_setup();

    // Extract carry chain
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;

    // Each carry c_i = l_i >> 51 = l_i / pow2(51)
    // Each masked r_i = l_i & mask51 = l_i % pow2(51)
    // Division theorem: l_i = c_i * pow2(51) + r_i

    // Stage 0: input[0] + 19*q
    // 19*q <= 19 (since q <= 1) and input[0] < 2^52
    // So l0 < 2^52 + 19 < 3 * pow2(51)
    let carry0 = (l0 >> 51) as u64;
    assert(l0 < 3 * pow2(51)) by {
        assert(input_limbs[0] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(input_limbs[0], (19 * q) as u64, l0, carry0);
    assert(carry0 < 3);

    // Get division theorem relationship for stage 0
    lemma_u64_shr_is_div(l0, 51);
    assert(carry0 as int == (input_limbs[0] as int + 19 * q as int) / pow2(51) as int);
    let r0 = lemma_stage_division_theorem(input_limbs[0], 19 * q as int, carry0 as int);

    // Stage 1
    let carry1 = (l1 >> 51) as u64;
    assert(l1 < 3 * pow2(51)) by {
        assert(input_limbs[1] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(input_limbs[1], carry0, l1, carry1);
    let r1 = lemma_stage_division_theorem(input_limbs[1], carry0 as int, carry1 as int);

    // Stage 2
    let carry2 = (l2 >> 51) as u64;
    assert(l2 < 3 * pow2(51)) by {
        assert(input_limbs[2] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(input_limbs[2], carry1, l2, carry2);
    let r2 = lemma_stage_division_theorem(input_limbs[2], carry1 as int, carry2 as int);

    // Stage 3
    let carry3 = (l3 >> 51) as u64;
    assert(l3 < 3 * pow2(51)) by {
        assert(input_limbs[3] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(input_limbs[3], carry2, l3, carry3);
    let r3 = lemma_stage_division_theorem(input_limbs[3], carry2 as int, carry3 as int);

    // Stage 4
    assert(l4 < 3 * pow2(51)) by {
        assert(input_limbs[4] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_single_stage_division(input_limbs[4], carry3, l4, c4);
    let r4 = lemma_stage_division_theorem(input_limbs[4], carry3 as int, c4 as int);

    // Now we have:
    // input[0] + 19*q = carry0 * pow2(51) + r0
    // input[1] + carry0 = carry1 * pow2(51) + r1
    // input[2] + carry1 = carry2 * pow2(51) + r2
    // input[3] + carry2 = carry3 * pow2(51) + r3
    // input[4] + carry3 = c4 * pow2(51) + r4

    // Establish pow2 products for telescoping
    let p51 = pow2(51) as int;
    let p102 = pow2(102) as int;
    let p153 = pow2(153) as int;
    let p204 = pow2(204) as int;

    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);

    assert(p51 * p51 == p102);
    assert(p51 * p102 == p153);
    assert(p51 * p153 == p204);
    let p255 = pow2(255) as int;
    assert(p51 * p204 == p255);

    // Telescoping: inline the algebraic expansion and cancellation
    assert(
        (carry0 as int * p51 + r0 - 19 * q as int)
        + (carry1 as int * p51 + r1 - carry0 as int) * p51
        + (carry2 as int * p51 + r2 - carry1 as int) * p102
        + (carry3 as int * p51 + r3 - carry2 as int) * p153
        + (c4 as int * p51 + r4 - carry3 as int) * p204
        + 19 * q as int
        == c4 as int * p51 * p204
        + r0 + r1 * p51 + r2 * p102 + r3 * p153 + r4 * p204
    ) by (nonlinear_arith)
        requires
            p51 * p51 == p102,
            p51 * p102 == p153,
            p51 * p153 == p204,
            p51 * p204 == p255,
    ;

    // LHS equals u64_5_as_nat(input_limbs) + 19*q because:
    //   carry0*p51 + r0 - 19*q = input[0]  (from requires)
    //   carry1*p51 + r1 - carry0 = input[1]
    //   etc.

    // Establish commutativity for u64_5_as_nat matching
    lemma_mul_is_commutative(pow2(51) as int, input_limbs[1] as int);
    lemma_mul_is_commutative(pow2(102) as int, input_limbs[2] as int);
    lemma_mul_is_commutative(pow2(153) as int, input_limbs[3] as int);
    lemma_mul_is_commutative(pow2(204) as int, input_limbs[4] as int);

    // c4 * p51 * p204 = c4 * p255
    assert(c4 as int * p51 * p204 == c4 as int * p255) by {
        lemma_mul_is_associative(c4 as int, p51, p204);
    };

    // Remainder is bounded by pow2(255)
    let rem = r0 + r1 * p51 + r2 * p102 + r3 * p153 + r4 * p204;
    lemma_radix51_remainder_bound(r0, r1, r2, r3, r4);
    assert(0 <= rem);
    assert(rem < p255);

    // u64_5_as_nat(input_limbs) + 19*q = c4 * pow2(255) + rem
    let val = u64_5_as_nat(input_limbs) as int + 19 * q as int;
    assert(val == c4 as int * p255 + rem);

    // By uniqueness of division
    lemma_pow2_pos(255nat);
    lemma_fundamental_div_mod_converse(val, p255, c4 as int, rem);
}

/// Helper lemma: Show that the carry out of l4 equals q
pub proof fn lemma_carry_out_equals_q(input_limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        u64_5_as_nat(input_limbs) >= p() <==> q == 1,
        u64_5_as_nat(input_limbs) < 2 * p(),  // From reduce()'s postcondition

    ensures
        ({
            let l0 = (input_limbs[0] + 19 * q) as u64;
            let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
            let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
            let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
            let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
            (l4 >> 51) == q
        }),
{
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
    let c4 = (l4 >> 51) as u64;

    // First, establish c4 = (u64_5_as_nat(input_limbs) + 19*q) / pow2(255)
    lemma_reduction_carry_propagation_is_division(input_limbs, q, c4);
    assert(c4 as int == (u64_5_as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int));

    let val = u64_5_as_nat(input_limbs);
    pow255_gt_19();
    lemma_pow2_pos(255nat);

    if q == 0 {
        // q = 0 means val < p() = pow2(255) - 19
        // So val + 0 = val < pow2(255) - 19 < pow2(255)
        // Therefore c4 = val / pow2(255) = 0 = q
        assert(val < p());
        assert(val + 19 * 0 == val) by {
            assert(19 * 0 == 0) by (nonlinear_arith);
        };
        assert(val < pow2(255));
        lemma_div_strictly_bounded(val as int, pow2(255) as int, 1int);
        assert(c4 == 0);
    } else {
        // q = 1 means val >= p() = pow2(255) - 19
        // So val + 19 >= pow2(255)
        // Also val < 2*p() = 2*pow2(255) - 38
        // So val + 19 < 2*pow2(255) - 38 + 19 = 2*pow2(255) - 19 < 2*pow2(255)
        // Therefore c4 = (val + 19) / pow2(255) = 1 = q
        assert(q == 1);
        assert(val >= p());
        assert(val as int + 19 >= pow2(255) as int);

        // val + 19 < 2*pow2(255)
        assert(val as int + 19 < 2 * pow2(255) as int) by {
            assert(2 * p() == 2 * pow2(255) - 38) by {
                lemma_mul_is_distributive_sub(2int, pow2(255) as int, 19int);
            };
        };

        // 1 = pow2(255) / pow2(255)
        lemma_div_by_self(pow2(255) as int);
        // val + 19 >= pow2(255) => (val+19)/pow2(255) >= 1
        lemma_div_is_ordered(pow2(255) as int, (val as int + 19), pow2(255) as int);
        assert(c4 as int >= 1);

        // val + 19 < 2*pow2(255) => (val+19)/pow2(255) < 2
        lemma_div_strictly_bounded(val as int + 19, pow2(255) as int, 2 as int);
        assert(c4 < 2);

        assert(c4 == 1);
    }
}

/// Proves that after adding 19*q and propagating carries while masking to 51 bits,
/// the result equals u64_5_as_nat(input_limbs) mod p
pub proof fn lemma_to_bytes_reduction(input_limbs: [u64; 5], final_limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        u64_5_as_nat(input_limbs) >= p() <==> q == 1,
        u64_5_as_nat(input_limbs) < 2 * p(),  // From reduce()'s postcondition
        final_limbs == reduce_with_q_spec(input_limbs, q),
    ensures
        forall|i: int| 0 <= i < 5 ==> final_limbs[i] < (1u64 << 51),
        u64_5_as_nat(final_limbs) == u64_5_as_nat(input_limbs) % p(),
{
    // Expand reduce_with_q_spec
    let ul = compute_unmasked_limbs(input_limbs, q);
    let l0 = ul[0];
    let l1 = ul[1];
    let l2 = ul[2];
    let l3 = ul[3];
    let l4 = ul[4];

    // Part 1: Show each final limb is < 2^51 (from masking)
    lemma_masked_lt_51(l0);
    lemma_masked_lt_51(l1);
    lemma_masked_lt_51(l2);
    lemma_masked_lt_51(l3);
    lemma_masked_lt_51(l4);

    assert(final_limbs[0] == (l0 & mask51) as u64);
    assert(final_limbs[1] == (l1 & mask51) as u64);
    assert(final_limbs[2] == (l2 & mask51) as u64);
    assert(final_limbs[3] == (l3 & mask51) as u64);
    assert(final_limbs[4] == (l4 & mask51) as u64);

    assert(final_limbs[0] < (1u64 << 51));
    assert(final_limbs[1] < (1u64 << 51));
    assert(final_limbs[2] < (1u64 << 51));
    assert(final_limbs[3] < (1u64 << 51));
    assert(final_limbs[4] < (1u64 << 51));

    // Part 2: Show u64_5_as_nat(final_limbs) == u64_5_as_nat(input_limbs) % p()
    // First establish carry relationships
    // l0 = input[0] + 19*q, so l0 >> 51 is the carry, l0 & mask51 is the remainder
    // l1 = input[1] + carry0, etc.

    // Get the carries
    let c0 = (l0 >> 51) as int;
    let c1 = (l1 >> 51) as int;
    let c2 = (l2 >> 51) as int;
    let c3 = (l3 >> 51) as int;
    let c4 = (l4 >> 51) as int;

    // Establish division theorem for each stage:
    // l_i = c_i * pow2(51) + (l_i & mask51)
    l51_bit_mask_lt();
    lemma_u64_div_and_mod_51((l0 >> 51) as u64, (l0 & mask51) as u64, l0);
    lemma_u64_div_and_mod_51((l1 >> 51) as u64, (l1 & mask51) as u64, l1);
    lemma_u64_div_and_mod_51((l2 >> 51) as u64, (l2 & mask51) as u64, l2);
    lemma_u64_div_and_mod_51((l3 >> 51) as u64, (l3 & mask51) as u64, l3);
    lemma_u64_div_and_mod_51((l4 >> 51) as u64, (l4 & mask51) as u64, l4);

    // Now we have from div_and_mod_51:
    // l_i = c_i * pow2(51) + (l_i & mask51)
    // which gives the carry relationships needed by lemma_reduction_telescoping

    // Establish carry bounds and that l_i as int == input[i] as int + carry_in
    // Each carry (l_i >> 51) is bounded:
    // l0 < 2^52 + 19, l0 >> 51 <= 1 (actually < 2 since l0 < 2^52+19 < 2*pow2(51)+19 < 3*pow2(51))
    lemma_carry_propagation_setup();

    // Stage 0
    assert(l0 as int == input_limbs[0] as int + 19 * q as int);
    assert(l0 < 3 * pow2(51)) by {
        assert(input_limbs[0] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_bounded_shr_51(l0);
    assert((l0 >> 51) < 3);

    // Stage 1
    assert(l1 as int == input_limbs[1] as int + (l0 >> 51) as int);
    assert(c0 == (l0 >> 51) as int);
    assert(l1 < 3 * pow2(51)) by {
        assert(input_limbs[1] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_bounded_shr_51(l1);

    // Stage 2
    assert(l2 as int == input_limbs[2] as int + (l1 >> 51) as int);
    assert(c1 == (l1 >> 51) as int);
    assert(l2 < 3 * pow2(51)) by {
        assert(input_limbs[2] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_bounded_shr_51(l2);

    // Stage 3
    assert(l3 as int == input_limbs[3] as int + (l2 >> 51) as int);
    assert(c2 == (l2 >> 51) as int);
    assert(l3 < 3 * pow2(51)) by {
        assert(input_limbs[3] < (1u64 << 52));
        assert((1u64 << 52) == pow2(52)) by { lemma_u64_shift_is_pow2(52); };
    };
    lemma_bounded_shr_51(l3);

    // Stage 4
    assert(l4 as int == input_limbs[4] as int + (l3 >> 51) as int);
    assert(c3 == (l3 >> 51) as int);

    // Use telescoping
    lemma_reduction_telescoping(
        input_limbs, final_limbs, q,
        c0, c1, c2, c3, c4,
    );
    // This gives: u64_5_as_nat(input) + 19*q == u64_5_as_nat(final) + c4*pow2(255)

    // Show c4 == q using lemma_carry_out_equals_q
    lemma_carry_out_equals_q(input_limbs, q);

    // So: u64_5_as_nat(input) + 19*q == u64_5_as_nat(final) + q*pow2(255)
    // Rearranging: u64_5_as_nat(final) == u64_5_as_nat(input) + 19*q - q*pow2(255)
    //            == u64_5_as_nat(input) - q*(pow2(255) - 19)
    //            == u64_5_as_nat(input) - q*p()

    let val = u64_5_as_nat(input_limbs);
    let final_val = u64_5_as_nat(final_limbs);
    pow255_gt_19();

    assert(final_val as int == val as int - q as int * p() as int) by {
        assert(final_val as int == val as int + 19 * q as int - c4 * pow2(255) as int);
        assert(c4 == q as int);
        // q*(pow2(255) - 19) = q*pow2(255) - 19*q
        assert(q as int * p() as int == q as int * pow2(255) as int - 19 * q as int) by {
            lemma_mul_is_distributive_sub(q as int, pow2(255) as int, 19int);
        };
    };

    // Now show final_val == val % p()
    lemma_pow2_pos(255nat);
    p_gt_2();

    if q == 0 {
        // val < p() and final_val = val - 0 = val
        assert(val < p());
        assert(final_val == val);
        assert(val % p() == val) by {
            lemma_small_mod(val, p());
        };
    } else {
        // q == 1, val >= p() and val < 2*p()
        // final_val = val - p()
        assert(val >= p());
        assert(val < 2 * p());
        assert(final_val as int == val as int - p() as int);
        // val % p() = val - p() because p <= val < 2p
        assert(val % p() == (val - p()) as nat) by {
            // val = 1 * p() + (val - p())
            // 0 <= val - p() < p() (since val < 2*p())
            lemma_fundamental_div_mod_converse(val as int, p() as int, 1int, (val - p()) as int);
        };
    }
}

/// Proves that the subtraction constants expand to 16 * p() in radix-2^51 form.
pub proof fn lemma_sub_constants_equal_16p()
    ensures
        (36028797018963664u64 as nat + pow2(51) * (36028797018963952u64 as nat) + pow2(102) * (
        36028797018963952u64 as nat) + pow2(153) * (36028797018963952u64 as nat) + pow2(204) * (
        36028797018963952u64 as nat)) == (16 as nat) * p(),
{
    // p() = pow2(255) - 19
    // 16 * p() = 16 * (pow2(255) - 19) = 16 * pow2(255) - 304
    // In radix-2^51:
    //   16*(2^51 - 19) = 36028797018963664
    //   16*(2^51 - 1) = 36028797018963952

    // First establish pow2 values and p()
    pow255_gt_19();

    // Use lemma_p_radix_representation to get p() in radix-2^51, then multiply by 16
    // Actually, let's just prove it directly using the algebraic structure

    // The constants are:
    // c0 = 16 * (pow2(51) - 19) = 16*pow2(51) - 304
    // c1 = c2 = c3 = c4 = 16 * (pow2(51) - 1) = 16*pow2(51) - 16

    // LHS = c0 + pow2(51)*c1 + pow2(102)*c1 + pow2(153)*c1 + pow2(204)*c1

    // Expand: 16*(pow2(51) - 19) + pow2(51)*16*(pow2(51)-1) + ... + pow2(204)*16*(pow2(51)-1)
    // = 16 * [(pow2(51)-19) + pow2(51)*(pow2(51)-1) + pow2(102)*(pow2(51)-1) + pow2(153)*(pow2(51)-1) + pow2(204)*(pow2(51)-1)]
    // = 16 * p()   (by lemma_p_radix_representation)

    // But we can't call lemma_p_radix_representation because it hasn't been proven yet.
    // Let's use a different approach.

    // Verify constants
    assert(36028797018963664u64 == 16 * (pow2(51) - 19)) by {
        lemma2_to64_rest();
        assert(pow2(51) == 2251799813685248) by (compute);
        assert(16 * (2251799813685248 - 19) == 36028797018963664) by (compute);
    };

    assert(36028797018963952u64 == 16 * (pow2(51) - 1)) by {
        lemma2_to64_rest();
        assert(pow2(51) == 2251799813685248) by (compute);
        assert(16 * (2251799813685248 - 1) == 36028797018963952) by (compute);
    };

    // Now: LHS = 16*(pow2(51)-19) + pow2(51)*16*(pow2(51)-1) + pow2(102)*16*(pow2(51)-1) + pow2(153)*16*(pow2(51)-1) + pow2(204)*16*(pow2(51)-1)
    // Factor out 16:
    // = 16 * [(pow2(51)-19) + pow2(51)*(pow2(51)-1) + pow2(102)*(pow2(51)-1) + pow2(153)*(pow2(51)-1) + pow2(204)*(pow2(51)-1)]

    let p51 = pow2(51) as int;
    let p102 = pow2(102) as int;
    let p153 = pow2(153) as int;
    let p204 = pow2(204) as int;

    // Factor 16 out of each term
    lemma_mul_is_commutative(p51, 16 * (p51 - 1));
    lemma_mul_is_associative(p51, 16, p51 - 1);

    lemma_mul_is_commutative(p102, 16 * (p51 - 1));
    lemma_mul_is_associative(p102, 16, p51 - 1);

    lemma_mul_is_commutative(p153, 16 * (p51 - 1));
    lemma_mul_is_associative(p153, 16, p51 - 1);

    lemma_mul_is_commutative(p204, 16 * (p51 - 1));
    lemma_mul_is_associative(p204, 16, p51 - 1);

    // LHS = 16 * ((p51-19) + p51*(p51-1) + p102*(p51-1) + p153*(p51-1) + p204*(p51-1))
    let inner = (p51 - 19) + p51 * (p51 - 1) + p102 * (p51 - 1) + p153 * (p51 - 1) + p204 * (p51 - 1);

    lemma_mul_distributive_5_terms(16, p51 - 19, p51 * (p51 - 1), p102 * (p51 - 1), p153 * (p51 - 1), p204 * (p51 - 1));

    // Now show inner == p()
    // p() = pow2(255) - 19
    // inner = (p51-19) + p51*(p51-1) + p102*(p51-1) + p153*(p51-1) + p204*(p51-1)

    // Expand: (p51-1)*p51 = p51^2 - p51 = p102 - p51
    lemma_pow2_adds(51, 51);
    lemma_mul_is_distributive_sub(p51, p51, 1);

    // (p51-1)*p102 = p51*p102 - p102 = p153 - p102
    lemma_pow2_adds(51, 102);
    lemma_mul_is_distributive_sub(p102, p51, 1);

    // (p51-1)*p153 = p51*p153 - p153 = p204 - p153
    lemma_pow2_adds(51, 153);
    lemma_mul_is_distributive_sub(p153, p51, 1);

    // (p51-1)*p204 = p51*p204 - p204 = p255 - p204
    lemma_pow2_adds(51, 204);
    lemma_mul_is_distributive_sub(p204, p51, 1);

    let p255 = pow2(255) as int;

    // Commutativity to match
    lemma_mul_is_commutative(p51, p51 - 1);
    lemma_mul_is_commutative(p102, p51 - 1);
    lemma_mul_is_commutative(p153, p51 - 1);
    lemma_mul_is_commutative(p204, p51 - 1);

    // inner = (p51-19) + (p102-p51) + (p153-p102) + (p204-p153) + (p255-p204)
    //       = p255 - 19 = p()
    assert(inner == p255 - 19);
    assert(inner == p() as int);
}

/// Helper lemma establishing the radix-2^51 expansion of p().
pub proof fn lemma_p_radix_representation()
    ensures
        (pow2(51) - 19) + pow2(51) * (pow2(51) - 1) + pow2(102) * (pow2(51) - 1) + pow2(153) * (
        pow2(51) - 1) + pow2(204) * (pow2(51) - 1) == p(),
{
    // p() = pow2(255) - 19
    pow255_gt_19();

    let p51 = pow2(51) as int;
    let p102 = pow2(102) as int;
    let p153 = pow2(153) as int;
    let p204 = pow2(204) as int;
    let p255 = pow2(255) as int;

    // Expand each term (pow2(51)-1)*pow2(k) using distributivity:
    // (pow2(51)-1)*pow2(51) = pow2(51)*pow2(51) - pow2(51) = pow2(102) - pow2(51)
    lemma_pow2_adds(51, 51);
    lemma_mul_is_distributive_sub(p51, p51, 1);
    lemma_mul_is_commutative(p51, p51 - 1);

    // (pow2(51)-1)*pow2(102) = pow2(51)*pow2(102) - pow2(102) = pow2(153) - pow2(102)
    lemma_pow2_adds(51, 102);
    lemma_mul_is_distributive_sub(p102, p51, 1);
    lemma_mul_is_commutative(p102, p51 - 1);

    // (pow2(51)-1)*pow2(153) = pow2(51)*pow2(153) - pow2(153) = pow2(204) - pow2(153)
    lemma_pow2_adds(51, 153);
    lemma_mul_is_distributive_sub(p153, p51, 1);
    lemma_mul_is_commutative(p153, p51 - 1);

    // (pow2(51)-1)*pow2(204) = pow2(51)*pow2(204) - pow2(204) = pow2(255) - pow2(204)
    lemma_pow2_adds(51, 204);
    lemma_mul_is_distributive_sub(p204, p51, 1);
    lemma_mul_is_commutative(p204, p51 - 1);

    // Sum telescopes:
    // (p51-19) + (p102-p51) + (p153-p102) + (p204-p153) + (p255-p204)
    // = p255 - 19 = p()
}

} // verus!
