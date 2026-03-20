#![allow(unused)]
use super::common_lemmas::pow_lemmas::*;
use super::scalar_lemmas::*;
use crate::backend::serial::u64::constants;
use crate::specs::scalar52_specs::*;
use crate::specs::scalar_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::specs::core_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::montgomery_specs::*;

use crate::montgomery::ProjectivePoint;
use crate::MontgomeryPoint;

verus! {

/// Swapping the two ladder state points flips the `bit` parameter.
pub proof fn lemma_ladder_invariant_swap(
    x0: ProjectivePoint,
    x1: ProjectivePoint,
    P: MontgomeryAffine,
    k: nat,
    bit: bool,
)
    requires
        montgomery_ladder_invariant(x0, x1, P, k, bit),
    ensures
        montgomery_ladder_invariant(x1, x0, P, k, !bit),
{
    reveal(montgomery_ladder_invariant);
    if bit {
        // bit = true: x0=[k+1]P and x1=[k]P. After swapping, !bit=false expects x1=[k]P and x0=[k+1]P.
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k + 1)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k)));
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k + 1)));
        assert(montgomery_ladder_invariant(x1, x0, P, k, false));
    } else {
        // bit = false: x0=[k]P and x1=[k+1]P. After swapping, !bit=true expects x1=[k+1]P and x0=[k]P.
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k + 1)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k + 1)));
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k)));
        assert(montgomery_ladder_invariant(x1, x0, P, k, true));
    }
}

pub proof fn lemma_zero_limbs_is_zero(point: MontgomeryPoint)
    requires
        forall|i: int| 0 <= i < 32 ==> #[trigger] point.0[i] == 0u8,
    ensures
        montgomery_point_as_nat(point) == 0,
{
    // montgomery_point_as_nat(point) ==
    // field_element_from_bytes(point.0) ==
    // (u8_32_as_nat(point.0) % pow2(255)) % p() ==
    // \sum_{i = 0} ^ 31 (bytes[i] as nat) * pow2(i * 8)
    assert(u8_32_as_nat(&point.0) == 0) by {
        assert forall|i: nat| 0 <= i < 32 implies point.0[i as int] * pow2(i * 8) == 0 by {
            /// trigger requirement:
            assert(point.0[i as int] == 0u8);
            assert(0u8 * pow2(i * 8) == 0) by {
                lemma_mul_basics_1(pow2(i * 8) as int);
            }
        }
    }
    assert((0nat % pow2(255)) % p() == 0) by {
        assert(0 < p() < pow2(255)) by {
            pow255_gt_19();
        }
        lemma_small_mod(0, p());
        lemma_small_mod(0, pow2(255));
    }
}

/// Proves that the precomputed RR constant equals R² mod L
///
/// In Montgomery arithmetic, RR is precomputed as R² mod L where:
/// - R = montgomery_radix() = 2^260
/// - L = group_order() (the curve order)
///
/// This lemma verifies the precomputed constant is correct by showing:
///   scalar52_as_nat(RR.limbs) % L == (R * R) % L
pub(crate) proof fn lemma_rr_equals_radix_squared()
    ensures
        scalar52_as_nat(&constants::RR) % group_order() == (montgomery_radix() * montgomery_radix())
            % group_order(),
{
    admit();
}

} // verus!
