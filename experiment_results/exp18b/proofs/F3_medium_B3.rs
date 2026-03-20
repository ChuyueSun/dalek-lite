    // The precondition sum_of_limbs_bounded ensures each pair of limbs doesn't overflow u64.
    // Use lemma_u64_5_as_nat_add to establish the first ensures clause.
    let lhs_limbs = lhs.limbs;
    let rhs_limbs = rhs.limbs;

    // Establish the limb-wise no-overflow condition required by lemma_u64_5_as_nat_add
    // (this follows directly from sum_of_limbs_bounded(lhs, rhs, u64::MAX))
    lemma_u64_5_as_nat_add(lhs_limbs, rhs_limbs);

    // Now prove the second ensures: canonical nat equality
    // fe51_as_canonical_nat(x) = u64_5_as_nat(x.limbs) % p()
    // field_add(a, b) = (a + b) % p()
    // So we need: u64_5_as_nat(sum_limbs) % p() == (u64_5_as_nat(lhs_limbs) % p() + u64_5_as_nat(rhs_limbs) % p()) % p()
    // which follows from lemma_add_mod_noop and the first ensures.
    pow255_gt_19();
    lemma_add_mod_noop(
        u64_5_as_nat(lhs_limbs) as int,
        u64_5_as_nat(rhs_limbs) as int,
        p() as int,
    );
