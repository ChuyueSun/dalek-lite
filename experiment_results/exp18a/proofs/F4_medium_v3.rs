// STRATEGY: Use the postconditions of as_bytes and from_bytes to chain equalities.
// First, as_bytes_post tells us u8_32_as_nat(bytes) = fe51_as_nat(fe_orig) % p.
// Then, since v % p < p < pow2(255), lemma_small_mod collapses the pow2(255) mod from
// from_bytes_post, and lemma_mod_twice collapses the final % p, yielding the canonical equality.

{
    let v = fe51_as_nat(fe_orig);

    // Establish that 0 < p < pow2(255)
    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };

    // Step 1: as_bytes_post gives us: u8_32_as_nat(bytes) == v % p()
    // (this follows directly from the precondition as_bytes_post(fe_orig, bytes))
    let bnat = u8_32_as_nat(bytes);
    assert(bnat == v % p());

    // Step 2: v % p() < p() < pow2(255), so (v % p()) % pow2(255) == v % p()
    assert(bnat % pow2(255) == bnat) by {
        assert(bnat < pow2(255)) by {
            lemma_mod_pos_bound(v as int, p() as int);
            // bnat == v % p() < p() < pow2(255)
            lemma_small_mod(bnat, pow2(255));
        };
        lemma_small_mod(bnat, pow2(255));
    };

    // Step 3: from_bytes_post gives: fe51_as_nat(fe_decoded) == bnat % pow2(255) == bnat
    assert(fe51_as_nat(fe_decoded) == bnat);

    // Step 4: fe51_as_canonical_nat is fe51_as_nat(...) % p()
    // fe51_as_canonical_nat(fe_decoded) == bnat % p() == (v % p()) % p() == v % p()
    assert(fe51_as_canonical_nat(fe_decoded) == fe51_as_canonical_nat(fe_orig)) by {
        // fe51_as_canonical_nat(fe_decoded) == fe51_as_nat(fe_decoded) % p()
        //                                   == bnat % p()
        //                                   == (v % p()) % p()
        //                                   == v % p()    (by lemma_mod_twice)
        //                                   == fe51_as_nat(fe_orig) % p()
        //                                   == fe51_as_canonical_nat(fe_orig)
        lemma_mod_twice(v as int, p() as int);
    };
}
