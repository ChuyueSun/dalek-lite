pub proof fn lemma_fe51_limbs_bounded_weaken(fe: &FieldElement51, a: u64, b: u64)
    requires
        fe51_limbs_bounded(fe, a),
        a < b,
        b <= 63,  // so 1u64 << b doesn't overflow

    ensures
        fe51_limbs_bounded(fe, b),
{
    assert forall|i: int| 0 <= i < 5 implies fe.limbs[i] < (1u64 << b) by {
        assert(fe.limbs[i] < (1u64 << a));
        assert((1u64 << a) < (1u64 << b)) by (bit_vector)
            requires
                a < b,
                b <= 63,
        ;
    }
}
