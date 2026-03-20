{
    let v = fe51_as_nat(fe_orig);
    let p = P25519;

    // Step 1: as_bytes postcondition gives u8_32_as_nat(bytes) == v % p
    // (follows directly from as_bytes_post)

    // Step 2: from_bytes postcondition gives fe51_as_nat(fe_decoded) == u8_32_as_nat(bytes) % pow2(255)
    // Combining: fe51_as_nat(fe_decoded) == (v % p) % pow2(255)

    // Step 3: v % p < p < pow2(255), so (v % p) % pow2(255) == v % p
    // by lemma_small_mod (since v % p < pow2(255))
    lemma_mod_pos_bound(v as int, p as int);
    // now we know 0 <= v % p < p
    // p < pow2(255), so v % p < pow2(255)
    lemma_small_mod((v % p) as nat, pow2(255));

    // Step 4: fe51_as_canonical_nat = fe51_as_nat % p
    // fe51_as_canonical_nat(fe_decoded) == fe51_as_nat(fe_decoded) % p
    //                                   == ((v % p) % pow2(255)) % p
    //                                   == (v % p) % p    (by step 3)
    //                                   == v % p          (by lemma_mod_twice)
    //                                   == fe51_as_canonical_nat(fe_orig)
    lemma_mod_twice(v as int, p as int);
}
