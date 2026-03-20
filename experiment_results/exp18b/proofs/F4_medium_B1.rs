{
    let v = fe51_as_nat(fe_orig);

    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };

    // Subgoal 1: u8_32_as_nat(bytes) = v % p
    // This follows directly from as_bytes postcondition.
    let w = u8_32_as_nat(bytes);
    assert(w == v % p());  // from as_bytes_post

    // Subgoal 2: fe51_as_nat(fe_decoded) = w % pow2(255)
    // This follows directly from from_bytes postcondition.
    assert(fe51_as_nat(fe_decoded) == w % pow2(255));  // from from_bytes_post

    // Subgoal 3: w % pow2(255) == w
    // Since w = v % p < p < pow2(255), w fits in 255 bits
    assert(w < pow2(255)) by {
        lemma_small_mod(w, p());
        // w = v % p < p < pow2(255)
    };
    assert(w % pow2(255) == w) by {
        lemma_small_mod(w, pow2(255));
    };

    // Subgoal 4: fe51_as_canonical_nat(fe_decoded) = (v % p) % p = v % p
    // And fe51_as_canonical_nat(fe_orig) = v % p
    // So they are equal.
    assert(fe51_as_nat(fe_decoded) == w);
    assert(fe51_as_canonical_nat(fe_decoded) == fe51_as_nat(fe_decoded) % p());
    assert(fe51_as_canonical_nat(fe_orig) == fe51_as_nat(fe_orig) % p());
    assert(fe51_as_canonical_nat(fe_decoded) == w % p()) by {
        lemma_mod_twice(v, p());
    };
    assert(w % p() == v % p()) by {
        lemma_small_mod(w, p());
    };
}
