    let v = fe51_as_nat(fe_orig);

    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };

    // as_bytes_post gives: u8_32_as_nat(bytes) == v % p
    // from_bytes_post gives: fe51_as_nat(fe_decoded) == u8_32_as_nat(bytes) % pow2(255)
    // So: fe51_as_nat(fe_decoded) == (v % p) % pow2(255)

    // Step 1: (v % p) < p < pow2(255), so (v % p) % pow2(255) == v % p
    assert((v % p()) % pow2(255) == v % p()) by {
        assert(v % p() < p()) by {
            lemma_mod_pos_bound(v as int, p() as int);
        };
        lemma_small_mod(v % p(), pow2(255));
    };

    // Step 2: fe51_as_nat(fe_decoded) == v % p
    assert(fe51_as_nat(fe_decoded) == v % p());

    // Step 3: fe51_as_canonical_nat(fe_decoded) == (fe51_as_nat(fe_decoded) % p) % p == (v % p) % p == v % p
    assert(fe51_as_canonical_nat(fe_decoded) == v % p()) by {
        lemma_mod_twice(v % p() as int, p() as int);
    };

    // Step 4: fe51_as_canonical_nat(fe_orig) == v % p
    assert(fe51_as_canonical_nat(fe_orig) == v % p()) by {
        lemma_mod_twice(v as int, p() as int);
    };
