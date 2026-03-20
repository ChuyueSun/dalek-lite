    let v = fe51_as_nat(fe_orig);

    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };

    // Subgoal 1: u8_32_as_nat(bytes) == v % p
    // from as_bytes_post
    assert(u8_32_as_nat(bytes) == v % p());

    // Subgoal 2: (v % p) % pow2(255) == v % p
    // Since v % p < p < pow2(255), by lemma_small_mod
    assert((v % p()) % pow2(255) == v % p()) by {
        lemma_small_mod(v % p(), pow2(255));
    };

    // Subgoal 3: fe51_as_nat(fe_decoded) == v % p
    // from_bytes_post gives: fe51_as_nat(fe_decoded) = u8_32_as_nat(bytes) % pow2(255)
    // = (v % p) % pow2(255) = v % p
    assert(fe51_as_nat(fe_decoded) == v % p());

    // Subgoal 4: fe51_as_canonical_nat(fe_decoded) == (v % p) % p == v % p
    // by lemma_mod_twice
    assert(fe51_as_canonical_nat(fe_decoded) == v % p()) by {
        lemma_mod_twice(v, p());
    };

    // Subgoal 5: fe51_as_canonical_nat(fe_orig) == v % p
    assert(fe51_as_canonical_nat(fe_orig) == v % p());
