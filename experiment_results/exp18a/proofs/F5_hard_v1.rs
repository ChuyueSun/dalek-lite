    // Step 1: Show pow2(pos+1) == 2 * pow2(pos)
    assert(pow2((pos + 1) as nat) == 2 * pow2(pos)) by {
        lemma_pow2_plus_one(pos);
    };

    // Step 2: Decompose scalar_val % pow2(pos+1) into low part and bit-at-pos
    // lemma_mod_breakdown: x % (a * b) == a * ((x / a) % b) + x % a
    // With a = pow2(pos), b = 2: scalar_val % pow2(pos+1) == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)
    assert((scalar_val as int) % pow2((pos + 1) as nat) as int
        == pow2(pos) as int * (((scalar_val as int) / pow2(pos) as int) % 2)
            + (scalar_val as int) % pow2(pos) as int) by {
        lemma_pow2_pos(pos);
        lemma_pow2_pos((pos + 1) as nat);
        assert(pow2((pos + 1) as nat) as int == pow2(pos) as int * 2) by {
            lemma_pow2_adds(pos, 1nat);
            assert(pow2(1nat) == 2) by { lemma2_to64(); };
            lemma_mul_is_commutative(pow2(pos) as int, pow2(1nat) as int);
        };
        lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2int);
    };

    // Step 3: Establish that the bit at pos equals carry
    // extracted = (scalar_val / pow2(pos)) % pow2(w)
    // (carry + extracted) % 2 == 0 means carry and extracted have same parity
    // bit_at_pos = (scalar_val / pow2(pos)) % 2 = extracted % 2
    // Since carry <= 1 and carry % 2 == extracted % 2, we get carry == extracted % 2 == bit_at_pos
    let bit_at_pos = ((scalar_val as int) / pow2(pos) as int) % 2;
    assert(bit_at_pos == carry as int) by {
        // extracted % 2 == (scalar_val / pow2(pos)) % pow2(w) % 2
        // Since pow2(w) is divisible by 2 (w >= 2 >= 1), (x % pow2(w)) % 2 == x % 2
        assert(extracted % 2 == (scalar_val / pow2(pos)) % 2) by {
            lemma_pow2_pos(w);
            lemma_pow2_even(w);
            // (x % (2 * k)) % 2 == x % 2 for any k
            // extracted = (scalar_val / pow2(pos)) % pow2(w)
            // and pow2(w) % 2 == 0 (w >= 2 >= 1)
            // so extracted % 2 == (scalar_val / pow2(pos)) % 2
            assert(pow2(w) % 2 == 0) by { lemma_pow2_even(w); };
            // pow2(w) == 2 * pow2((w-1) as nat)
            assert(pow2(w) == 2 * pow2((w - 1) as nat)) by {
                lemma_pow2_plus_one((w - 1) as nat);
            };
            // (x % (2 * k)) % 2 == x % 2 follows from lemma_mod_mod with a=2, b=pow2(w-1)
            // actually lemma_mod_mod: (x % (a * b)) % a == x % a
            // with a=2, b=pow2(w-1): ((scalar_val/pow2(pos)) % (2 * pow2(w-1))) % 2 == (scalar_val/pow2(pos)) % 2
            lemma_mod_mod((scalar_val / pow2(pos)) as int, 2int, pow2((w - 1) as nat) as int);
        };
        // (carry + extracted) % 2 == 0 and carry <= 1 and extracted % 2 == bit_at_pos
        // carry % 2 == extracted % 2 (since their sum is even)
        // since carry in {0,1}: carry == carry % 2 == extracted % 2 == bit_at_pos
        assert((carry + extracted) % 2 == 0);
        assert(carry % 2 == extracted % 2) by {
            // (carry + extracted) % 2 == (carry % 2 + extracted % 2) % 2 == 0
            // so carry % 2 == extracted % 2 (they are both 0 or both 1)
            assert((carry % 2 + extracted % 2) % 2 == 0) by {
                lemma_add_mod_noop(carry as int, extracted as int, 2int);
            };
        };
        // carry <= 1 so carry == carry % 2
        assert(carry % 2 == carry) by {
            lemma_small_mod(carry, 2nat);
        };
        // bit_at_pos in {0, 1} since it's x % 2
        assert(0 <= bit_at_pos < 2) by {
            lemma_mod_pos_bound((scalar_val as int) / pow2(pos) as int, 2int);
        };
        // So bit_at_pos == extracted % 2 == carry % 2 == carry
        assert(extracted % 2 == bit_at_pos);
        assert(carry == bit_at_pos) by {
            assert(carry as int == extracted % 2 as int);
            assert(extracted % 2 == bit_at_pos);
        };
    };

    // Step 4: So scalar_val % pow2(pos+1) == scalar_val % pow2(pos) + carry * pow2(pos)
    assert((scalar_val as int) % pow2((pos + 1) as nat) as int
        == (scalar_val as int) % pow2(pos) as int + (carry as int) * pow2(pos) as int) by {
        assert(bit_at_pos == carry as int);
        // scalar_val % pow2(pos+1) == pow2(pos) * bit_at_pos + scalar_val % pow2(pos)
        //                          == pow2(pos) * carry + scalar_val % pow2(pos)
        lemma_mul_is_commutative(pow2(pos) as int, bit_at_pos);
    };

    // Step 5: Show reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)) since naf[pos] == 0
    assert(reconstruct(naf.take((pos + 1) as int)) == reconstruct(naf.take(pos as int))) by {
        // Use lemma_reconstruct_split to split at pos
        lemma_reconstruct_split(naf.take((pos + 1) as int), pos);
        // naf.take(pos+1).take(pos) == naf.take(pos)
        assert(naf.take((pos + 1) as int).take(pos as int) =~= naf.take(pos as int));
        // The suffix is a single element: naf[pos] == 0
        let suffix = naf.take((pos + 1) as int).skip(pos as int);
        assert(suffix.len() == 1);
        assert(suffix[0] == naf[pos as int]);
        assert(naf[pos as int] == 0i8);
        // reconstruct(suffix) == 0
        assert(reconstruct(suffix) == 0) by {
            assert(suffix.skip(1).len() == 0);
            assert(reconstruct(suffix.skip(1)) == 0);
        };
        // pow2(pos) * 0 == 0
        assert(pow2(pos) as int * reconstruct(suffix) == 0) by {
            lemma_mul_basics(pow2(pos) as int);
        };
    };

    // Step 6: Show carry * pow2(pos+1) == carry * 2 * pow2(pos)
    assert((carry as int) * pow2((pos + 1) as nat) as int == (carry as int) * 2 * pow2(pos) as int)
        by {
        assert(pow2((pos + 1) as nat) as int == 2 * pow2(pos) as int) by {
            lemma_pow2_plus_one(pos);
        };
        lemma_mul_is_associative(carry as int, 2int, pow2(pos) as int);
    };

    // Step 7: Combine everything
    // reconstruct(naf.take(pos+1)) + carry * pow2(pos+1)
    // == reconstruct(naf.take(pos)) + carry * 2 * pow2(pos)
    // == reconstruct(naf.take(pos)) + carry * pow2(pos) + carry * pow2(pos)
    // == scalar_val % pow2(pos) + carry * pow2(pos)  [by old invariant]
    // == scalar_val % pow2(pos+1)                    [by step 4]
    assert(reconstruct(naf.take((pos + 1) as int)) + (carry as int) * pow2(
        (pos + 1) as nat,
    ) as int == (scalar_val as int) % pow2((pos + 1) as nat) as int) by {
        // LHS == reconstruct(naf.take(pos)) + carry * 2 * pow2(pos)
        //     == reconstruct(naf.take(pos)) + carry * pow2(pos) + carry * pow2(pos)
        // old invariant: reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
        // so LHS == scalar_val % pow2(pos) + carry * pow2(pos) == RHS
        lemma_mul_is_distributive_add(carry as int, pow2(pos) as int, pow2(pos) as int);
    };
