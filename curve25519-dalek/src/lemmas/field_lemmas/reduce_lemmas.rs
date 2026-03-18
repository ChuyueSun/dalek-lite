#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::pow2_51_lemmas::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mask_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// Each component of spec_reduce is bounded.
// The reason we _don't_ write
// ensures forall |i: int| 0 <= i < 5 ==> spec_reduce(limbs)[i] < (1u64 << 52)
// is that the solver treats `spec_reduce`` above as symbolic and does _not_ instantiate e.g.
// ((limbs[4] & mask51) + (limbs[3] >> 51)) as u64 < (1u64 << 52)
pub proof fn lemma_reduce_boundaries(limbs: [u64; 5])
    ensures
        ((limbs[0] & mask51) + (limbs[4] >> 51) * 19) < (1u64 << 52),
        ((limbs[1] & mask51) + (limbs[0] >> 51)) < (1u64 << 52),
        ((limbs[2] & mask51) + (limbs[1] >> 51)) < (1u64 << 52),
        ((limbs[3] & mask51) + (limbs[2] >> 51)) < (1u64 << 52),
        ((limbs[4] & mask51) + (limbs[3] >> 51)) < (1u64 << 52),
{
    admit(); // HOLE H
}

pub proof fn proof_reduce(limbs: [u64; 5])
    ensures
        forall|i: int| 0 <= i < 5 ==> spec_reduce(limbs)[i] < (1u64 << 52),
        // Suppose l = (l0, l1, l2, l3, l4) are the input limbs.
        // They represent a number
        // e(l) =  l0 + l1 * 2^51 + l2 * 2^102 + l3 * 2^153 + l4 * 2^204
        // in Z_p, for p = 2^255 - 19
        // reduce(l) returns v = (v0, v1, v2, v3, v4), such that
        // v0 = 19 * a4 + b0
        // v1 =      a0 + b1
        // v2 =      a1 + b2
        // v3 =      a2 + b3
        // v4 =      a3 + b4
        // where ai = li >> 51 and bi = li & mask51
        // we can reformulate this as ai = li / 2^51 (flooring division) and bi = li % 2^51
        // Using the following identity connecting integer division and remainder:
        // x = y * (x / y) + x % y
        // we can see that li = ai * 2^51 + bi
        // Plugging the above identities into the equations for v, we can observe that
        // e(v) = e(l) - p * (l4 >> 51)
        // IOW, e(reduce(l)) = e(l) (mod p)
        // additionally, if all limbs are below 2^51, reduce(l) = l
        (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (spec_reduce(limbs) =~= limbs),
        u64_5_as_nat(spec_reduce(limbs)) == u64_5_as_nat(limbs) - p() * (limbs[4] >> 51),
        u64_5_as_nat(spec_reduce(limbs)) % p() == u64_5_as_nat(limbs) % p(),
{
    admit(); // HOLE J
}

/// Proves that reduce() ensures u64_5_as_nat < 2*p()
///
/// This is the key property needed for to_bytes(): after reduce(),
/// the value is bounded by 2*p = 2^256 - 38, not just by the loose
/// bound from individual limb sizes.
pub proof fn lemma_reduce_bound_2p(limbs: [u64; 5])
    ensures
        u64_5_as_nat(spec_reduce(limbs)) < 2 * p(),
{
    lemma2_to64();
    pow255_gt_19();

    let r = spec_reduce(limbs);

    assert(1u64 << 51 == pow2(51)) by {
        lemma_u64_shift_is_pow2(51);
    }

    // For r[i] where i > 0: (limbs[i] & mask51) + (limbs[i-1] >> 51) < 2^51 + 2^13
    assert forall|i: int| 0 <= i <= 4 implies #[trigger] (limbs[i] & mask51) < pow2(51) by {
        lemma_masked_lt_51(limbs[i]);
    }
    // separate foralls, because they trigger on i and i-1
    assert forall|i: int| 0 <= i <= 4 implies #[trigger] limbs[i] >> 51 < pow2(13) by {
        assert(limbs[i] >> 51 <= u64::MAX >> 51) by {
            lemma_u64_shr_le(limbs[i], u64::MAX, 51);
        }
        assert(u64::MAX >> 51 < pow2(13)) by {
            assert(1u64 << 13 == pow2(13)) by {
                lemma_u64_shift_is_pow2(13);
            }
            lemma_u64_max_shifting(51);
        }
    }

    // For r[0] we have the extra factor of 19:
    // r[0] = (limbs[0] & mask51) + (limbs[4] >> 51) * 19
    assert((limbs[4] >> 51) * 19 < pow2(18)) by {
        assert(19 < pow2(5)) by {
            lemma2_to64();
        }
        assert(pow2(18) == pow2(13) * pow2(5)) by {
            lemma_pow2_adds(13, 5);
        }
        lemma_mul_lt((limbs[4] >> 51) as nat, pow2(13), 19, pow2(5));
    }

    assert forall|i: nat| 1 <= i <= 4 implies #[trigger] pow2(i * 51) * r[i as int] < pow2(i * 51)
        * pow2(13) + pow2((i + 1) * 51) by {
        assert(pow2(i * 51) * r[i as int] < pow2(i * 51) * (pow2(51) + pow2(13))) by {
            lemma_pow2_pos(i * 51);
            lemma_mul_strict_inequality(
                r[i as int] as int,
                (pow2(51) + pow2(13)) as int,
                pow2(i * 51) as int,
            );
            lemma_mul_is_commutative(pow2(i * 51) as int, r[i as int] as int);
            lemma_mul_is_commutative(pow2(i * 51) as int, (pow2(51) + pow2(13)) as int);
        }

        assert(pow2(i * 51) * (pow2(51) + pow2(13)) == pow2((i + 1) * 51) + pow2(i * 51) * pow2(13))
            by {
            assert(pow2(i * 51) * (pow2(51) + pow2(13)) == pow2(i * 51) * pow2(51) + pow2(i * 51)
                * pow2(13)) by {
                lemma_mul_is_distributive_add(
                    pow2(i * 51) as int,
                    pow2(51) as int,
                    pow2(13) as int,
                );
            }
            assert(pow2(i * 51) * pow2(51) == pow2((i + 1) * 51)) by {
                assert(i * 51 + 51 == (i + 1) * 51) by {
                    lemma_mul_is_distributive_add_other_way(51, i as int, 1);
                }
                lemma_pow2_adds(i * 51, 51);
            }
        }
    }

    // write out i * 51s explicitly to trigger forall match
    let tail = (pow2(18) + pow2(51) + pow2(64) + pow2(102) + pow2(115) + pow2(153) + pow2(166)
        + pow2(204) + pow2(217));
    assert(u64_5_as_nat(r) == r[0] + pow2(1 * 51) * r[1] + pow2(2 * 51) * r[2] + pow2(3 * 51) * r[3]
        + pow2(4 * 51) * r[4] < tail + pow2(255)) by {
        lemma_pow2_adds(51, 13);
        lemma_pow2_adds(102, 13);
        lemma_pow2_adds(153, 13);
        lemma_pow2_adds(204, 13);
    }

    assert(2 * p() == pow2(255) + pow2(255) - 38) by {
        lemma_pow2_adds(255, 1);
        lemma_pow2_plus_one(255);
    }

    // we'll prove the tail is small
    assert(tail < pow2(255) - 38) by {
        assert forall|i: nat| i <= 204 implies #[trigger] pow2(i) < pow2(217) by {
            lemma_pow2_strictly_increases(i, 217);
        }
        assert(tail < 9 * pow2(217) < pow2(221)) by {
            assert(9 < pow2(4));  // known
            assert(pow2(217) > 0) by {
                lemma_pow2_pos(217);
            }
            lemma_mul_strict_inequality(9, pow2(4) as int, pow2(217) as int);
            lemma_pow2_adds(217, 4);
        }

        assert(pow2(254) < pow2(255) - 38) by {
            assert(38 < pow2(6));  // known
            assert(pow2(255) - 38 > pow2(255) - pow2(6) == pow2(254) + pow2(254) - pow2(6)) by {
                lemma_pow2_plus_one(254);
            }
            assert(pow2(254) - pow2(6) > 0) by {
                lemma_pow2_strictly_increases(6, 254);
            }
        }

        assert(pow2(221) < pow2(254)) by {
            lemma_pow2_strictly_increases(221, 254);
        }
    }
}

} // verus!
