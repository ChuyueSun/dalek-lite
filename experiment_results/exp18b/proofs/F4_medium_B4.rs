    let v = fe51_as_nat(fe_orig);

    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };

    // Step 1: as_bytes_post gives u8_32_as_nat(bytes) = v % p
    // (this follows directly from the precondition as_bytes_post(fe_orig, bytes))
    assert(u8_32_as_nat(bytes) == v % p());

    // Step 2: v % p < p < pow2(255), so (v % p) % pow2(255) = v % p
    assert((v % p()) % pow2(255) == v % p()) by {
        assert(v % p() < p()) by {
            lemma_mod_pos_bound(v as int, p() as int);
        };
        assert(v % p() < pow2(255)) by {
            // v % p < p < pow2(255)
        };
        lemma_small_mod((v % p()) as nat, pow2(255) as nat);
    };

    // Step 3: from_bytes_post gives fe51_as_nat(fe_decoded) = u8_32_as_nat(bytes) % pow2(255)
    //         = (v % p) % pow2(255) = v % p
    assert(fe51_as_nat(fe_decoded) == v % p()) by {
        // from_bytes_post says fe51_as_nat(fe_decoded) == u8_32_as_nat(bytes) % pow2(255)
        // u8_32_as_nat(bytes) == v % p
        // (v % p) % pow2(255) == v % p  (from Step 2)
    };

    // Step 4: fe51_as_canonical_nat(fe_decoded) = (v % p) % p = v % p = fe51_as_canonical_nat(fe_orig)
    assert(fe51_as_canonical_nat(fe_decoded) == fe51_as_canonical_nat(fe_orig)) by {
        // fe51_as_canonical_nat(fe_decoded) = fe51_as_nat(fe_decoded) % p = (v % p) % p
        // By lemma_mod_twice: (v % p) % p = v % p
        // fe51_as_canonical_nat(fe_orig) = fe51_as_nat(fe_orig) % p = v % p
        lemma_mod_twice(v as int, p() as int);
    };
