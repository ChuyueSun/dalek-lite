proof fn lemma_scalar_mod_breakdown_step(scalar_val: nat, pos: nat)
    requires
        pos < 256,
    ensures
        (scalar_val as int) % pow2(pos + 1) as int
            == pow2(pos) as int * (((scalar_val as int) / pow2(pos) as int) % 2)
                + (scalar_val as int) % pow2(pos) as int,
{
    // pow2(pos + 1) == pow2(pos) * pow2(1)  via lemma_pow2_adds
    lemma_pow2_adds(pos, 1);
    // pow2(1) == 2
    lemma2_to64();
    // pow2(pos) > 0
    lemma_pow2_pos(pos);
    // Now pow2(pos + 1) == pow2(pos) * 2
    // Apply lemma_mod_breakdown with x = scalar_val, a = pow2(pos), b = 2:
    //   scalar_val % (pow2(pos) * 2) == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)
    lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
    // The LHS uses pow2(pos + 1); after lemma_pow2_adds we know pow2(pos + 1) == pow2(pos) * pow2(1) == pow2(pos) * 2
    // Verus can close the goal by arithmetic after the above facts are in scope.
}
