    // Step 1: Prove the first ensures: u64_5_as_nat of the sum equals the sum of u64_5_as_nat.
    //
    // lemma_u64_5_as_nat_add requires: forall i, b[i] as nat + a[i] as nat <= u64::MAX
    // Our precondition sum_of_limbs_bounded(lhs, rhs, u64::MAX) gives:
    //   forall i, lhs.limbs[i] + rhs.limbs[i] < u64::MAX
    // which implies <= u64::MAX, so we can call the lemma.
    assert(forall|i: int| 0 <= i < 5 ==> rhs.limbs[i] as nat + lhs.limbs[i] as nat <= u64::MAX) by {
        assert forall|i: int| 0 <= i < 5 implies rhs.limbs[i] as nat + lhs.limbs[i] as nat <= u64::MAX by {
            assert(lhs.limbs[i] + rhs.limbs[i] < u64::MAX);
        }
    };
    lemma_u64_5_as_nat_add(lhs.limbs, rhs.limbs);

    // The result limbs are exactly lhs.limbs[i] + rhs.limbs[i] cast back to u64,
    // which is what spec_add_fe51_limbs produces.
    let result = spec_add_fe51_limbs(lhs, rhs);
    assert(result.limbs == [
        (lhs.limbs[0] + rhs.limbs[0]) as u64,
        (lhs.limbs[1] + rhs.limbs[1]) as u64,
        (lhs.limbs[2] + rhs.limbs[2]) as u64,
        (lhs.limbs[3] + rhs.limbs[3]) as u64,
        (lhs.limbs[4] + rhs.limbs[4]) as u64,
    ]);

    // First ensures: confirmed by lemma_u64_5_as_nat_add
    assert(u64_5_as_nat(result.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs));

    // Step 2: Prove the second ensures:
    //   fe51_as_canonical_nat(result) == field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
    //
    // By definition:
    //   fe51_as_canonical_nat(x) = u64_5_as_nat(x.limbs) % p()
    //   field_add(a, b) = field_canonical(a + b) = (a + b) % p()
    //
    // So we need:
    //   u64_5_as_nat(result.limbs) % p() == (u64_5_as_nat(lhs.limbs) % p() + u64_5_as_nat(rhs.limbs) % p()) % p()
    //
    // Using the fact that u64_5_as_nat(result.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs):
    //   (lhs_nat + rhs_nat) % p() == ((lhs_nat % p()) + (rhs_nat % p())) % p()
    // which is exactly lemma_add_mod_noop.
    pow255_gt_19();  // establishes p() > 0

    let lhs_nat = u64_5_as_nat(lhs.limbs);
    let rhs_nat = u64_5_as_nat(rhs.limbs);
    let sum_nat = u64_5_as_nat(result.limbs);

    assert(sum_nat == lhs_nat + rhs_nat);

    lemma_add_mod_noop(lhs_nat as int, rhs_nat as int, p() as int);
    // lemma_add_mod_noop: (x + y) % m == ((x % m) + (y % m)) % m
    assert(sum_nat % p() == (lhs_nat % p() + rhs_nat % p()) % p());

    // Unfolding: fe51_as_canonical_nat(result) = u64_5_as_nat(result.limbs) % p() = sum_nat % p()
    // field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
    //   = (fe51_as_canonical_nat(lhs) + fe51_as_canonical_nat(rhs)) % p()
    //   = (lhs_nat % p() + rhs_nat % p()) % p()
    assert(fe51_as_canonical_nat(&result) == sum_nat % p());
    assert(field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
        == (fe51_as_canonical_nat(lhs) + fe51_as_canonical_nat(rhs)) % p());
    assert(fe51_as_canonical_nat(&result) == field_add(
        fe51_as_canonical_nat(lhs),
        fe51_as_canonical_nat(rhs),
    ));
