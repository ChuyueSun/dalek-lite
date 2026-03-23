pub proof fn lemma_field_add_16p_no_overflow(lhs: &FieldElement51, rhs: &FieldElement51)
    requires
        fe51_limbs_bounded(lhs, 54),
        fe51_limbs_bounded(rhs, 54),
    ensures
// Adding 16p constants won't overflow

        lhs.limbs[0] <= u64::MAX - 36028797018963664u64,
        lhs.limbs[1] <= u64::MAX - 36028797018963952u64,
        lhs.limbs[2] <= u64::MAX - 36028797018963952u64,
        lhs.limbs[3] <= u64::MAX - 36028797018963952u64,
        lhs.limbs[4] <= u64::MAX - 36028797018963952u64,
        rhs.limbs[0] < 36028797018963664u64,
        rhs.limbs[1] < 36028797018963952u64,
        rhs.limbs[2] < 36028797018963952u64,
        rhs.limbs[3] < 36028797018963952u64,
        rhs.limbs[4] < 36028797018963952u64,
{
    let c0 = 36028797018963664u64;  // 16 * (2^51 - 19)
    let c = 36028797018963952u64;  // 16 * (2^51 - 1)

    // Bound lhs limbs so adding the constants cannot overflow a u64
    assert(lhs.limbs[0] <= u64::MAX - c0) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c0) by (compute);
    }
    assert(lhs.limbs[1] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }
    assert(lhs.limbs[2] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }
    assert(lhs.limbs[3] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }
    assert(lhs.limbs[4] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }

    // Bound rhs limbs to be less than the constants
    assert(rhs.limbs[0] < c0) by {
        assert((1u64 << 54) <= c0) by (compute);
    }
    assert(rhs.limbs[1] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
    assert(rhs.limbs[2] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
    assert(rhs.limbs[3] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
    assert(rhs.limbs[4] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
}
