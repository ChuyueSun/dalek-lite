    // Step 1: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)) since naf[pos]=0
    assert(reconstruct(naf.take((pos + 1) as int)) == reconstruct(naf.take(pos as int))) by {
        lemma_reconstruct_zero_extend(naf, pos, (pos + 1) as nat);
    };

    // Step 2: extracted % 2 == scalar_val / pow2(pos) % 2
    // extracted = (scalar_val / pow2(pos)) % pow2(w)
    // extracted % 2 = ((scalar_val / pow2(pos)) % pow2(w)) % 2
    //              = (scalar_val / pow2(pos)) % 2   (since w >= 2, pow2(w) = pow2(1) * pow2(w-1) = 2 * pow2(w-1))
    let bit_at_pos: nat = (scalar_val / pow2(pos)) % 2;
    assert(extracted % 2 == bit_at_pos) by {
        // pow2(w) = 2 * pow2(w-1) via lemma_pow2_adds(1, w-1)
        lemma_pow2_adds(1, (w - 1) as nat);
        lemma2_to64();
        // extracted % 2 = ((scalar_val / pow2(pos)) % pow2(w)) % 2
        // = (scalar_val / pow2(pos)) % 2 by lemma_mod_mod(a, 2, pow2(w-1))
        lemma_mod_mod((scalar_val / pow2(pos)) as int, 2, pow2((w - 1) as nat) as int);
    };

    // Step 3: carry == bit_at_pos (from (carry + extracted) % 2 == 0)
    // (carry + extracted) % 2 == 0 means carry % 2 == extracted % 2
    // but carry <= 1, so carry == carry % 2
    // and bit_at_pos = extracted % 2
    // combined: carry == extracted % 2 == bit_at_pos
    // But wait: (carry + extracted) % 2 == 0 means they have the same parity
    // carry is 0 or 1, extracted % 2 is 0 or 1
    // So carry == bit_at_pos
    assert(carry == bit_at_pos) by {
        // (carry + extracted) % 2 == 0, so carry % 2 == -(extracted % 2) % 2
        // which means carry % 2 == extracted % 2 (since -(x%2)%2 == x%2 for x in {0,1})
        // Actually: (carry + extracted) % 2 == 0 => carry % 2 == (2 - extracted % 2) % 2 == extracted % 2
        // We know carry <= 1 so carry == carry % 2
        assert((carry as int + extracted as int) % 2 == 0);
        assert(carry as int % 2 == extracted as int % 2) by {
            assert((carry as int + extracted as int) % 2 == 0);
            assert((carry as int % 2 + extracted as int % 2) % 2 == 0) by {
                lemma_mod_add_sub_cancel(carry as int + extracted as int, 2);
            };
        };
        assert(bit_at_pos == extracted % 2);
        assert(carry as int % 2 == bit_at_pos as int);
        assert(carry <= 1);
        assert(carry as int == carry as int % 2) by {
            if carry == 0 {
                assert(0int % 2 == 0);
            } else {
                assert(carry == 1);
                assert(1int % 2 == 1);
            }
        };
    };

    // Step 4: scalar_val % pow2(pos+1) decomposition
    // scalar_val % pow2(pos+1) = scalar_val % (2 * pow2(pos))
    //   = (scalar_val % pow2(pos)) + pow2(pos) * ((scalar_val / pow2(pos)) % 2)
    //   = (scalar_val % pow2(pos)) + pow2(pos) * bit_at_pos
    assert(scalar_val as int % pow2((pos + 1) as nat) as int
        == scalar_val as int % pow2(pos) as int + pow2(pos) as int * bit_at_pos as int) by {
        // pow2(pos+1) = 2 * pow2(pos)
        lemma_pow2_adds(1, pos);
        lemma2_to64();
        assert(pow2((pos + 1) as nat) as int == 2 * pow2(pos) as int);
        // scalar_val % (2 * pow2(pos)) decomposition
        lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
        assert(scalar_val as int % (2 * pow2(pos) as int)
            == scalar_val as int % pow2(pos) as int
                + pow2(pos) as int * (scalar_val as int / pow2(pos) as int % 2));
        assert((scalar_val as int / pow2(pos) as int % 2) == bit_at_pos as int);
    };

    // Step 5: Combine everything
    // We have:
    //   reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))   [Step 1]
    //   carry == bit_at_pos                                           [Step 3]
    //   scalar_val % pow2(pos) == reconstruct(naf.take(pos)) + carry * pow2(pos) [old invariant, rearranged]
    //   scalar_val % pow2(pos+1) == scalar_val % pow2(pos) + pow2(pos) * bit_at_pos [Step 4]
    //
    // Therefore:
    //   reconstruct(naf.take(pos+1)) + carry * pow2(pos+1)
    //   == reconstruct(naf.take(pos)) + carry * (2 * pow2(pos))
    //   == reconstruct(naf.take(pos)) + carry * pow2(pos) + carry * pow2(pos)
    //   == scalar_val % pow2(pos) + carry * pow2(pos)     [by old invariant, noting carry = bit_at_pos]
    //   Wait, let me redo this carefully.
    //
    // Old invariant: reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
    // So: scalar_val % pow2(pos) == reconstruct(naf.take(pos)) + carry * pow2(pos)
    //
    // scalar_val % pow2(pos+1)
    //   == scalar_val % pow2(pos) + pow2(pos) * bit_at_pos
    //   == (reconstruct(naf.take(pos)) + carry * pow2(pos)) + pow2(pos) * carry   [since bit_at_pos == carry]
    //   == reconstruct(naf.take(pos)) + 2 * carry * pow2(pos)
    //   == reconstruct(naf.take(pos+1)) + carry * (2 * pow2(pos))
    //   == reconstruct(naf.take(pos+1)) + carry * pow2(pos+1)

    lemma_pow2_adds(1, pos);
    lemma2_to64();
    assert(pow2((pos + 1) as nat) as int == 2 * pow2(pos) as int);
    assert(reconstruct(naf.take((pos + 1) as int)) + carry as int * pow2((pos + 1) as nat) as int
        == scalar_val as int % pow2((pos + 1) as nat) as int) by {
        // Restate old invariant rearranged
        assert(scalar_val as int % pow2(pos) as int
            == reconstruct(naf.take(pos as int)) + carry as int * pow2(pos) as int);
        // reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))
        assert(reconstruct(naf.take((pos + 1) as int)) == reconstruct(naf.take(pos as int)));
        // carry == bit_at_pos
        assert(carry as int == bit_at_pos as int);
        // scalar_val % pow2(pos+1) == scalar_val % pow2(pos) + pow2(pos) * bit_at_pos
        assert(scalar_val as int % pow2((pos + 1) as nat) as int
            == scalar_val as int % pow2(pos) as int + pow2(pos) as int * bit_at_pos as int);
        // Now arithmetic:
        // LHS = reconstruct(naf.take(pos+1)) + carry * pow2(pos+1)
        //     = reconstruct(naf.take(pos)) + carry * (2 * pow2(pos))
        // RHS = scalar_val % pow2(pos) + pow2(pos) * carry
        //     = (reconstruct(naf.take(pos)) + carry * pow2(pos)) + pow2(pos) * carry
        //     = reconstruct(naf.take(pos)) + 2 * carry * pow2(pos)
        assert(carry as int * (2 * pow2(pos) as int)
            == 2 * carry as int * pow2(pos) as int) by {
            lemma_mul_is_commutative(carry as int, 2 * pow2(pos) as int);
            lemma_mul_is_associative(2, carry as int, pow2(pos) as int);
        };
        assert(scalar_val as int % pow2(pos) as int + pow2(pos) as int * bit_at_pos as int
            == reconstruct(naf.take(pos as int)) + carry as int * pow2(pos) as int
                + pow2(pos) as int * carry as int);
        assert(carry as int * pow2(pos) as int + pow2(pos) as int * carry as int
            == 2 * carry as int * pow2(pos) as int) by {
            lemma_mul_is_commutative(pow2(pos) as int, carry as int);
        };
    };
