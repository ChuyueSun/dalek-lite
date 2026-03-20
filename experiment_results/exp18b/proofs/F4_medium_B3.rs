    let v = fe51_as_nat(fe_orig);

    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };

    // Subgoal 1: u8_32_as_nat(bytes) = v % p
    // This follows directly from as_bytes_post
    let w = u8_32_as_nat(bytes);
    assert(w == v % p());  // from as_bytes_post

    // Subgoal 2: fe51_as_nat(fe_decoded) = w % pow2(255)
    // This follows directly from from_bytes_post
    assert(fe51_as_nat(fe_decoded) == w % pow2(255));  // from from_bytes_post

    // Subgoal 3: w % pow2(255) == w
    // Since w = v % p and p < pow2(255), we have w < pow2(255)
    assert(w < pow2(255)) by {
        lemma_mod_pos_bound(v as int, p() as int);
        // w == v % p < p < pow2(255)
    };
    assert(w % pow2(255) == w) by {
        lemma_small_mod(w, pow2(255) as nat);
    };

    // So fe51_as_nat(fe_decoded) = w = v % p
    assert(fe51_as_nat(fe_decoded) == v % p());

    // Subgoal 4: fe51_as_canonical_nat(fe_decoded) = fe51_as_canonical_nat(fe_orig)
    // fe51_as_canonical_nat(x) = fe51_as_nat(x) % p
    // fe51_as_canonical_nat(fe_decoded) = (v % p) % p = v % p  (by lemma_mod_twice)
    // fe51_as_canonical_nat(fe_orig) = v % p
    assert(fe51_as_canonical_nat(fe_decoded) == v % p()) by {
        lemma_mod_twice(v as int, p() as int);
    };
    assert(fe51_as_canonical_nat(fe_orig) == v % p());
