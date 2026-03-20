    // Name the result once to avoid repeated calls to spec_add_fe51_limbs.
    let result = spec_add_fe51_limbs(lhs, rhs);

    // -----------------------------------------------------------------------
    // Step 1: Prove the first ensures:
    //   u64_5_as_nat(result.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs)
    //
    // lemma_u64_5_as_nat_add requires: forall i, lhs.limbs[i] as nat + rhs.limbs[i] as nat <= u64::MAX
    // The precondition sum_of_limbs_bounded(lhs, rhs, u64::MAX) ensures
    // lhs.limbs[i] + rhs.limbs[i] <= u64::MAX for each i (no u64 overflow).
    // -----------------------------------------------------------------------
    assert(forall|i: int| 0 <= i < 5 ==>
        lhs.limbs[i] as nat + rhs.limbs[i] as nat <= u64::MAX as nat) by {
        assert forall|i: int| 0 <= i < 5 implies
            lhs.limbs[i] as nat + rhs.limbs[i] as nat <= u64::MAX as nat by {
            assert(lhs.limbs[i] + rhs.limbs[i] <= u64::MAX);
        }
    };

    lemma_u64_5_as_nat_add(lhs.limbs, rhs.limbs);

    // First ensures now follows directly.
    assert(u64_5_as_nat(result.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs));

    // -----------------------------------------------------------------------
    // Step 2: Prove the second ensures:
    //   fe51_as_canonical_nat(&result) == field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
    //
    // By definition:
    //   fe51_as_canonical_nat(x) = u64_5_as_nat(x.limbs) % p()
    //   field_add(a, b)          = (a + b) % p()
    //
    // The goal reduces to:
    //   (lhs_nat + rhs_nat) % p == ((lhs_nat % p) + (rhs_nat % p)) % p
    // which is exactly lemma_add_mod_noop.
    // -----------------------------------------------------------------------

    // Establish p() > 0, required by modular arithmetic lemmas.
    pow255_gt_19();

    let lhs_nat = u64_5_as_nat(lhs.limbs) as int;
    let rhs_nat = u64_5_as_nat(rhs.limbs) as int;
    let p = p() as int;
    assert(p > 0);

    // (lhs_nat + rhs_nat) % p == ((lhs_nat % p) + (rhs_nat % p)) % p
    lemma_add_mod_noop(lhs_nat, rhs_nat, p);

    // Unfold the definition of fe51_as_canonical_nat on the result.
    assert(fe51_as_canonical_nat(&result) == u64_5_as_nat(result.limbs) % p());

    // Unfold the definition of field_add.
    assert(field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
        == (fe51_as_canonical_nat(lhs) + fe51_as_canonical_nat(rhs)) % p());

    // Unfold fe51_as_canonical_nat on lhs and rhs.
    assert(fe51_as_canonical_nat(lhs) == u64_5_as_nat(lhs.limbs) % p());
    assert(fe51_as_canonical_nat(rhs) == u64_5_as_nat(rhs.limbs) % p());

    // Now everything chains together:
    //   fe51_as_canonical_nat(&result)
    //     == u64_5_as_nat(result.limbs) % p
    //     == (lhs_nat + rhs_nat) % p            [by step 1]
    //     == ((lhs_nat % p) + (rhs_nat % p)) % p [by lemma_add_mod_noop]
    //     == (fe51_as_canonical_nat(lhs) + fe51_as_canonical_nat(rhs)) % p
    //     == field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
    assert(fe51_as_canonical_nat(&result) == field_add(
        fe51_as_canonical_nat(lhs),
        fe51_as_canonical_nat(rhs),
    ));
