    pow255_gt_19();
    let lhs_limbs = lhs.limbs;
    let rhs_limbs = rhs.limbs;
    let sum_limbs = spec_add_fe51_limbs(lhs, rhs).limbs;

    // Establish that pairwise sums don't overflow, as required by lemma_u64_5_as_nat_add
    assert(forall|i: int| 0 <= i < 5 ==> rhs_limbs[i] as nat + lhs_limbs[i] as nat <= u64::MAX) by {
        assert(rhs_limbs[0] as nat + lhs_limbs[0] as nat <= u64::MAX);
        assert(rhs_limbs[1] as nat + lhs_limbs[1] as nat <= u64::MAX);
        assert(rhs_limbs[2] as nat + lhs_limbs[2] as nat <= u64::MAX);
        assert(rhs_limbs[3] as nat + lhs_limbs[3] as nat <= u64::MAX);
        assert(rhs_limbs[4] as nat + lhs_limbs[4] as nat <= u64::MAX);
    }

    // Step 1: nat sum equality
    lemma_u64_5_as_nat_add(lhs_limbs, rhs_limbs);

    // Step 2: canonical nat / field_add equivalence
    lemma_add_mod_noop(u64_5_as_nat(lhs_limbs) as int, u64_5_as_nat(rhs_limbs) as int, p() as int);
