    let v = fe51_as_nat(fe_orig);

    // Establish that 0 < p < pow2(255)
    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };

    // Subgoal 1: u8_32_as_nat(bytes) == v % p
    // This follows directly from as_bytes_post
    let bytes_nat = u8_32_as_nat(bytes);
    assert(bytes_nat == v % p());

    // Subgoal 2: v % p < pow2(255)
    // Since v % p < p < pow2(255)
    assert(v % p() < pow2(255)) by {
        lemma_mod_pos_bound(v as int, p() as int);
    };

    // Subgoal 3: (v % p) % pow2(255) == v % p
    // Since v % p < pow2(255), small_mod applies
    assert((v % p()) % pow2(255) == v % p()) by {
        lemma_small_mod(v % p(), pow2(255));
    };

    // Subgoal 4: fe51_as_nat(fe_decoded) == v % p
    // from_bytes_post gives fe51_as_nat(fe_decoded) = bytes_nat % pow2(255)
    // bytes_nat = v % p, and (v % p) % pow2(255) = v % p
    assert(fe51_as_nat(fe_decoded) == v % p());

    // Subgoal 5: fe51_as_canonical_nat(fe_decoded) == v % p
    // fe51_as_canonical_nat = fe51_as_nat % p
    // (v % p) % p = v % p by lemma_mod_twice
    assert(fe51_as_canonical_nat(fe_decoded) == v % p()) by {
        lemma_mod_twice(v as int, p() as int);
    };

    // Subgoal 6: fe51_as_canonical_nat(fe_orig) == v % p
    // fe51_as_canonical_nat(fe_orig) = fe51_as_nat(fe_orig) % p = v % p
    assert(fe51_as_canonical_nat(fe_orig) == v % p());

    // Conclude
    assert(fe51_as_canonical_nat(fe_decoded) == fe51_as_canonical_nat(fe_orig));
