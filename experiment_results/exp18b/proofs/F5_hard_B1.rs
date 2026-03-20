    // Step 1: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))
    // because naf[pos] == 0, so the extra element contributes nothing.
    let pos1 = (pos + 1) as nat;
    let suffix = naf.take(pos1 as int).skip(pos as int);

    assert(reconstruct(suffix) == 0) by {
        assert(suffix.len() == 1);
        assert(suffix[0] == naf[pos as int]);
        assert(naf[pos as int] == 0i8);
        assert(suffix.skip(1).len() == 0);
        assert(reconstruct(suffix.skip(1)) == 0);
    };

    assert(reconstruct(naf.take(pos1 as int)) == reconstruct(naf.take(pos as int))) by {
        lemma_reconstruct_split(naf.take(pos1 as int), pos);
        assert(naf.take(pos1 as int).take(pos as int) =~= naf.take(pos as int));
        assert(pow2(pos) * reconstruct(suffix) == 0) by {
            lemma_mul_basics(pow2(pos) as int);
        };
    };

    // Step 2: pow2(pos+1) == 2 * pow2(pos)
    lemma_pow2_adds(1nat, pos);
    lemma2_to64();
    // Now pow2(1) == 2 and pow2(1) * pow2(pos) == pow2(pos+1)
    assert(pow2(pos1) == 2 * pow2(pos)) by {
        assert(pow2(pos1) == pow2(1nat) * pow2(pos));
        assert(pow2(1nat) == 2);
    };

    // Step 3: extracted % 2 == (scalar_val / pow2(pos)) % 2
    // extracted == (scalar_val / pow2(pos)) % pow2(w)
    // pow2(w) == 2 * pow2(w-1), so (x % (2 * pow2(w-1))) % 2 == x % 2
    let wm1 = (w - 1) as nat;
    lemma_pow2_adds(1nat, wm1);
    assert(pow2(w) == 2 * pow2(wm1)) by {
        assert(pow2(w) == pow2(1nat) * pow2(wm1));
        assert(pow2(1nat) == 2);
    };
    assert(extracted % 2 == (scalar_val as int / pow2(pos) as int) % 2) by {
        let base = scalar_val as int / pow2(pos) as int;
        lemma_mod_mod(base, 2, pow2(wm1) as int);
        assert(pow2(wm1) > 0) by { lemma_pow2_pos(wm1); };
        assert((base % (2 * pow2(wm1) as int)) % 2 == base % 2);
        assert(extracted as int % 2 == base % 2);
    };

    // Step 4: parity argument: carry == (scalar_val / pow2(pos)) % 2
    // We know (carry + extracted) % 2 == 0 and carry <= 1.
    // extracted % 2 == (scalar_val / pow2(pos)) % 2.
    // Also: old invariant gives us:
    //   reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
    // The low bit of (scalar_val / pow2(pos)) equals carry:
    //   (carry + extracted) % 2 == 0 means carry % 2 == (-(extracted % 2)) % 2
    //   so carry == extracted % 2 (since carry in {0,1}).
    //   But we need carry == (scalar_val / pow2(pos)) % 2, which equals extracted % 2.
    assert(carry as int == (scalar_val as int / pow2(pos) as int) % 2) by {
        let bit = (scalar_val as int / pow2(pos) as int) % 2;
        // extracted % 2 == bit (from step 3)
        assert(extracted as int % 2 == bit);
        // (carry + extracted) % 2 == 0, so carry % 2 == extracted % 2 % 2? No:
        // carry + extracted ≡ 0 (mod 2), so carry ≡ -extracted ≡ extracted (mod 2) (since -1≡1 mod 2)
        // carry ∈ {0,1}, bit ∈ {0,1}, both equal extracted % 2 (which is 0 or 1)
        // If extracted % 2 == 0: carry must be 0 (since (carry + 0) % 2 == 0 => carry % 2 == 0 => carry == 0)
        // If extracted % 2 == 1: carry must be 1 (since (carry + 1) % 2 == 0 => carry % 2 == 1 => carry == 1)
        assert((carry as int + extracted as int) % 2 == 0);
        assert(carry as int % 2 == extracted as int % 2) by {
            // (carry + extracted) % 2 == 0 means carry % 2 == (2 - extracted % 2) % 2 == extracted % 2
            // Because if extracted % 2 == 0, then carry % 2 == 0; if extracted % 2 == 1, then carry % 2 == 1
        };
        // carry in {0,1} and carry % 2 == bit in {0,1}, so carry == bit
        assert(carry as int <= 1);
        assert(bit >= 0);
        assert(bit < 2);
    };

    // Step 5: decompose scalar_val % pow2(pos+1) using lemma_mod_breakdown
    // scalar_val % pow2(pos+1) == scalar_val % (2 * pow2(pos))
    //   == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)
    assert(scalar_val as int % pow2(pos1) as int
        == pow2(pos) as int * ((scalar_val as int / pow2(pos) as int) % 2)
            + scalar_val as int % pow2(pos) as int) by {
        assert(pow2(pos1) == 2 * pow2(pos));
        lemma_pow2_pos(pos);
        lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
        lemma_mul_is_commutative(pow2(pos) as int, (scalar_val as int / pow2(pos) as int) % 2);
    };

    // Step 6: Combine everything
    // reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))
    // carry == (scalar_val / pow2(pos)) % 2
    // old invariant: reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
    // pow2(pos+1) == 2 * pow2(pos)
    // scalar_val % pow2(pos+1) == pow2(pos) * carry + scalar_val % pow2(pos)
    //   == pow2(pos) * carry + reconstruct(naf.take(pos)) + carry * pow2(pos) - carry * pow2(pos)
    // Wait, let's be more direct:
    // LHS = reconstruct(naf.take(pos+1)) + carry * pow2(pos+1)
    //     = reconstruct(naf.take(pos)) + carry * (2 * pow2(pos))
    // RHS = scalar_val % pow2(pos+1)
    //     = pow2(pos) * carry + scalar_val % pow2(pos)
    //     = pow2(pos) * carry + (reconstruct(naf.take(pos)) + carry * pow2(pos))
    //     = pow2(pos) * carry + reconstruct(naf.take(pos)) + carry * pow2(pos)
    //     = reconstruct(naf.take(pos)) + 2 * carry * pow2(pos)
    //     = reconstruct(naf.take(pos)) + carry * (2 * pow2(pos))  ✓
    assert(
        reconstruct(naf.take(pos1 as int)) + carry as int * pow2(pos1) as int
            == scalar_val as int % pow2(pos1) as int
    ) by {
        assert(reconstruct(naf.take(pos1 as int)) == reconstruct(naf.take(pos as int)));
        assert(pow2(pos1) == 2 * pow2(pos));
        assert(carry as int == (scalar_val as int / pow2(pos) as int) % 2);
        assert(scalar_val as int % pow2(pos1) as int
            == pow2(pos) as int * carry as int + scalar_val as int % pow2(pos) as int);
        lemma_mul_is_distributive_add(carry as int, pow2(pos) as int, pow2(pos) as int);
        // carry * pow2(pos+1) == carry * (2 * pow2(pos)) == carry * pow2(pos) + carry * pow2(pos)
        // reconstruct(naf.take(pos)) + carry * 2 * pow2(pos)
        // == reconstruct(naf.take(pos)) + carry * pow2(pos) + carry * pow2(pos)
        // == scalar_val % pow2(pos) + carry * pow2(pos)
        // == pow2(pos) * carry + scalar_val % pow2(pos)
        // == scalar_val % pow2(pos+1)
    };
