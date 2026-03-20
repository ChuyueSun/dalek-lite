// STRATEGY: The proof proceeds in two steps. First, use a pointwise no-overflow argument
// derived from the precondition sum_of_limbs_bounded to invoke lemma_u64_5_as_nat_add,
// establishing that u64_5_as_nat is additive over the result limbs. Second, use
// lemma_add_mod_noop from vstd::arithmetic::div_mod to push the modulo through the
// addition, connecting the canonical (mod p) representations to field_add.

    // Introduce the result for clarity
    let result = spec_add_fe51_limbs(lhs, rhs);

    // -----------------------------------------------------------------------
    // Step 1: Prove the first ensures:
    //   u64_5_as_nat(result.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs)
    //
    // lemma_u64_5_as_nat_add needs: forall i, rhs.limbs[i] as nat + lhs.limbs[i] as nat <= u64::MAX
    // The precondition sum_of_limbs_bounded(lhs, rhs, u64::MAX) gives us
    //   forall i, lhs.limbs[i] + rhs.limbs[i] <= u64::MAX (no overflow in u64 arithmetic).
    // -----------------------------------------------------------------------
    assert(forall|i: int| 0 <= i < 5 ==>
        lhs.limbs[i] as nat + rhs.limbs[i] as nat <= u64::MAX as nat) by {
        assert forall|i: int| 0 <= i < 5 implies
            lhs.limbs[i] as nat + rhs.limbs[i] as nat <= u64::MAX as nat by
        {
            // sum_of_limbs_bounded(lhs, rhs, u64::MAX) ensures lhs.limbs[i] + rhs.limbs[i] <= u64::MAX
            assert(lhs.limbs[i] + rhs.limbs[i] <= u64::MAX);
        }
    };

    lemma_u64_5_as_nat_add(lhs.limbs, rhs.limbs);

    // Confirm the additive relationship for u64_5_as_nat
    assert(u64_5_as_nat(result.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs));

    // -----------------------------------------------------------------------
    // Step 2: Prove the second ensures:
    //   fe51_as_canonical_nat(result) == field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
    //
    // By definition:
    //   fe51_as_canonical_nat(x)   = u64_5_as_nat(x.limbs) % p()
    //   field_add(a, b)            = (a + b) % p()
    //
    // Goal reduces to:
    //   (lhs_nat + rhs_nat) % p() == ((lhs_nat % p()) + (rhs_nat % p())) % p()
    //
    // which is exactly lemma_add_mod_noop.
    // -----------------------------------------------------------------------
    let lhs_nat = u64_5_as_nat(lhs.limbs) as int;
    let rhs_nat = u64_5_as_nat(rhs.limbs) as int;
    let p = p() as int;

    // p() > 0 (needed for modular arithmetic lemmas)
    pow255_gt_19();
    assert(p > 0);

    // (lhs_nat + rhs_nat) % p == ((lhs_nat % p) + (rhs_nat % p)) % p
    lemma_add_mod_noop(lhs_nat, rhs_nat, p);

    // Unfold fe51_as_canonical_nat on the result: it equals u64_5_as_nat(result.limbs) % p
    assert(fe51_as_canonical_nat(&result) == u64_5_as_nat(result.limbs) % p());

    // The first ensures gave us u64_5_as_nat(result.limbs) == lhs_nat + rhs_nat (as nats)
    // so fe51_as_canonical_nat(result) == (lhs_nat + rhs_nat) % p
    //                                   == ((lhs_nat % p) + (rhs_nat % p)) % p  [by lemma_add_mod_noop]
    //                                   == field_add(fe51_as_canonical_nat(lhs), fe51_as_canonical_nat(rhs))
    assert(fe51_as_canonical_nat(&result) == field_add(
        fe51_as_canonical_nat(lhs),
        fe51_as_canonical_nat(rhs),
    ));
