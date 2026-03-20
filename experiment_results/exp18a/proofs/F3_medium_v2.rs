    // The precondition sum_of_limbs_bounded(lhs, rhs, u64::MAX) ensures
    // each lhs.limbs[i] + rhs.limbs[i] does not overflow u64.
    //
    // Step 1: Prove the first ensures — limb-wise nat addition is preserved.
    //
    // We need: u64_5_as_nat(spec_add_fe51_limbs(lhs, rhs).limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs)
    //
    // Establish the no-overflow condition that lemma_u64_5_as_nat_add requires.
    assert(forall|i: int| 0 <= i < 5 ==> lhs.limbs[i] as nat + rhs.limbs[i] as nat <= u64::MAX as nat) by {
        assert forall|i: int| 0 <= i < 5 implies lhs.limbs[i] as nat + rhs.limbs[i] as nat <= u64::MAX as nat by {
            // sum_of_limbs_bounded gives us lhs.limbs[i] + rhs.limbs[i] <= u64::MAX
            assert(lhs.limbs[i] + rhs.limbs[i] <= u64::MAX);
        }
    };

    // Apply the key lemma that u64_5_as_nat distributes over limb-wise addition.
    lemma_u64_5_as_nat_add(lhs.limbs, rhs.limbs);

    // Name the result for clarity.
    let result = spec_add_fe51_limbs(lhs, rhs);

    // Confirm the first ensures.
    assert(u64_5_as_nat(result.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs));

    // Step 2: Prove the second ensures — field_add corresponds to modular addition.
    //
    // We need:
    //   fe51_as_canonical_nat(&result) == field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
    //
    // By definition:
    //   fe51_as_canonical_nat(x) = u64_5_as_nat(x.limbs) % p()
    //   field_add(a, b) = (a + b) % p()
    //
    // So we need:
    //   (lhs_nat + rhs_nat) % p() == ((lhs_nat % p()) + (rhs_nat % p())) % p()
    // which is lemma_add_mod_noop.

    // Establish p() > 0 (needed for modular arithmetic lemmas).
    pow255_gt_19();

    let lhs_nat = u64_5_as_nat(lhs.limbs) as int;
    let rhs_nat = u64_5_as_nat(rhs.limbs) as int;

    // The sum of nats equals the nat of the sum (from step 1).
    assert(u64_5_as_nat(result.limbs) as int == lhs_nat + rhs_nat);

    // Apply add_mod_noop: (x + y) % m == ((x % m) + (y % m)) % m
    lemma_add_mod_noop(lhs_nat, rhs_nat, p() as int);

    // Now conclude the field equality.
    assert(fe51_as_canonical_nat(&result) == field_add(
        fe51_as_canonical_nat(lhs),
        fe51_as_canonical_nat(rhs),
    ));
