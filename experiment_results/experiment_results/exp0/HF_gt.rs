pub proof fn lemma_from_bytes_as_bytes_roundtrip(
    fe_orig: &FieldElement51,
    bytes: &[u8; 32],
    fe_decoded: &FieldElement51,
)
    requires
        as_bytes_post(fe_orig, bytes),  // bytes = as_bytes(fe_orig)
        from_bytes_post(bytes, fe_decoded),  // fe_decoded = from_bytes(bytes)

    ensures
        fe51_as_canonical_nat(fe_decoded) == fe51_as_canonical_nat(fe_orig),
{
    let v = fe51_as_nat(fe_orig);

    assert(fe51_as_canonical_nat(fe_decoded) == fe51_as_canonical_nat(fe_orig)) by {
        assert(0 < p() < pow2(255)) by {
            pow255_gt_19();
        };
        // Subgoal 1: (v % p) % pow2(255) == v % p
        // The canonical value fits in 255 bits, so from_bytes preserves it
        assert((v % p()) % pow2(255) == v % p()) by {
            assert(v % p() < p()) by {
                lemma_mod_bound(v as int, p() as int);
            };
            lemma_small_mod((v % p()) as nat, pow2(255));
        };

        // Subgoal 2: (v % p) % p == v % p (mod idempotence)
        // Taking mod p again doesn't change the canonical value
        assert((v % p()) % p() == v % p()) by {
            lemma_mod_twice(v as int, p() as int);
        };
    };
}
