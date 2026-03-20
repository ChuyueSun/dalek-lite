#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mask_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// Specialization for b = 51
pub proof fn lemma_two_factoring_51(k: nat, ai: u64)
    ensures
        pow2(k + 51) * ai == pow2(k) * (pow2(51) * ai),
{
    lemma_two_factoring(k, 51, ai);
}

pub proof fn lemma_add_then_shift(a: u64, b: u64)
    requires
        a < (1u64 << 52),
        b < (1u64 << 52),
    ensures
        (a + b) < (1u64 << 53),
        ((a + b) as u64 >> 51) < 4,
{
    // a + b < 2^52 + 2^52 = 2^53
    assert((1u64 << 52) + (1u64 << 52) == (1u64 << 53)) by (bit_vector);
    // (a + b) >> 51 = (a + b) / 2^51
    // a + b < 2^53, so (a + b) / 2^51 < 2^53 / 2^51 = 4
    assert(((a + b) as u64 >> 51) < 4) by (bit_vector)
        requires
            a < (1u64 << 52),
            b < (1u64 << 52),
    ;
}

// >> preserves [<=]. Unfortunately, these operations are u128 and
// we need lemma_u128_shr_is_div.
pub proof fn lemma_shr_51_le(a: u128, b: u128)
    requires
        a <= b,
    ensures
        (a >> 51) <= (b >> 51),
{
    lemma_u128_shr_le(a, b, 51);
}

// Corollary of above, using the identity (a << x) >> x == a for u64::MAX
pub proof fn lemma_shr_51_fits_u64(a: u128)
    requires
        a <= (u64::MAX as u128) << 51,
    ensures
        (a >> 51) <= (u64::MAX as u128),
{
    lemma_u128_shr_le(a, (u64::MAX as u128) << 51u128, 51);
    assert(((u64::MAX as u128) << 51u128) >> 51u128 == u64::MAX as u128) by (bit_vector);
}

// Auxiliary datatype lemma
// Should work for any k <= 64, but the proofs are convoluted and we can't use BV
// (x as u64) = x % 2^64, so x = 2^64 * (x / 2^64) + (x as u64). Thus
// (x as u64) % 2^k = (x as u64) % 2^k, because 2^k | 2^64 * (...) for k <= 64
pub proof fn lemma_cast_then_mod_51(x: u128)
    ensures
        (x as u64) % (pow2(51) as u64) == x % (pow2(51) as u128),
{
    let trunc = x as u64;
    let p51 = pow2(51);

    // pow2(51) fits in u64 (it's less than 2^64)
    assert(p51 <= u64::MAX) by {
        lemma_u64_pow2_le_max(51);
    }

    // Step 1: (x as u64) as nat == x as nat % 2^64
    lemma_u128_cast_64_is_mod(x);
    assert(trunc as nat == x as nat % 0x10000000000000000);

    // Establish pow2(64) == 0x10000000000000000
    assert(pow2(64) == 0x10000000000000000nat) by {
        lemma_u128_shift_is_pow2(64);
        assert((1u128 << 64u128) == 0x10000000000000000u128) by (bit_vector);
    }

    // Step 2: 2^64 = 2^51 * 2^13
    lemma_pow2_pos(51nat);
    lemma_pow2_pos(13nat);
    lemma_pow2_adds(51nat, 13nat);
    assert(pow2(51) * pow2(13) == pow2(64));

    // Step 3: (x % 2^64) % 2^51 == x % 2^51 (all at nat level)
    lemma_mod_mod(x as nat as int, pow2(51) as int, pow2(13) as int);

    // Step 4: (trunc as nat) % p51 == (x as nat) % p51
    assert((trunc as nat) % p51 == (x as nat) % p51);

    // Step 5: Connect to the u64/u128 typed postcondition
    // LHS: (x as u64) % (pow2(51) as u64) -- this is a u64 % u64 = u64
    // RHS: x % (pow2(51) as u128)         -- this is a u128 % u128 = u128
    // Both should equal (x as nat) % pow2(51) when lifted to nat

    // pow2(51) > 0
    lemma_pow2_pos(51nat);

    // (x as u64) % (pow2(51) as u64) as nat == (x as u64) as nat % p51
    // Already: (trunc as nat) % p51 == (x as nat) % p51

    // x % (pow2(51) as u128) as nat == (x as nat) % p51
    // This should follow from the fact that % on unsigned integers IS nat %
}

pub proof fn lemma_mul_sub(ci: int, cj: int, cj_0: int, k: nat)
    ensures
        pow2(k) * (ci - pow2(51) * (cj - cj_0)) == pow2(k) * ci - pow2(k + 51) * cj + pow2(k + 51)
            * cj_0,
{
    // pow2(k+51) = pow2(k) * pow2(51)
    lemma_pow2_adds(k, 51);
    assert(pow2(k + 51) == pow2(k) * pow2(51));

    // Distribute pow2(51) * (cj - cj_0) = pow2(51) * cj - pow2(51) * cj_0
    lemma_mul_is_distributive_sub(pow2(51) as int, cj, cj_0);

    // Distribute pow2(k) * (ci - pow2(51)*(cj-cj_0))
    //   = pow2(k) * ci - pow2(k) * (pow2(51)*cj - pow2(51)*cj_0)
    lemma_mul_is_distributive_sub(pow2(k) as int, ci, pow2(51) as int * (cj - cj_0));

    // pow2(k) * (pow2(51) * cj) = pow2(k+51) * cj
    lemma_mul_is_associative(pow2(k) as int, pow2(51) as int, cj);

    // pow2(k) * (pow2(51) * cj_0) = pow2(k+51) * cj_0
    lemma_mul_is_associative(pow2(k) as int, pow2(51) as int, cj_0);

    // Now: pow2(k) * (pow2(51)*cj - pow2(51)*cj_0)
    //   = pow2(k) * pow2(51) * cj - pow2(k) * pow2(51) * cj_0
    lemma_mul_is_distributive_sub(pow2(k) as int, pow2(51) as int * cj, pow2(51) as int * cj_0);
}

// Masking with low_bits_mask(51) gives a value bounded by 2^51
pub proof fn lemma_masked_lt_51(v: u64)
    ensures
        v & mask51 < (1u64 << 51),
{
    // mask51 == low_bits_mask(51)
    l51_bit_mask_lt();
    // Use the generic lemma for u64 masking with k = 51
    lemma_u64_masked_lt(v, 51);
}

// lemma_u64_div_and_mod specialization for k = 51, using mask51 == low_bits_mask(51)
pub proof fn lemma_u64_div_and_mod_51(ai: u64, bi: u64, v: u64)
    requires
        ai == v >> 51,
        bi == v & mask51,
    ensures
        ai == v / (pow2(51) as u64),
        bi == v % (pow2(51) as u64),
        v == ai * pow2(51) + bi,
{
    // mask51 == low_bits_mask(51)
    l51_bit_mask_lt();
    // Delegate to the generic lemma with k = 51
    lemma_u64_div_and_mod(ai, bi, v, 51);
}

pub broadcast proof fn lemma_cast_then_mask_51(x: u128)
    ensures
        #![trigger (x as u64) & mask51]
        (x as u64) & mask51 == x & (mask51 as u128),
{
    assert((x as u64) & mask51 == x & (mask51 as u128)) by (bit_vector);
}

} // verus!
