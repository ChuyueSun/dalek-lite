    // We need to show:
    //   reconstruct(naf.take(pos+1)) + carry * pow2(pos+1) == scalar_val % pow2(pos+1)
    //
    // Step 1: Since naf[pos] == 0, reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)).
    //         (The definition of reconstruct adds naf[pos] * pow2(pos) = 0 * pow2(pos) = 0.)
    assert(naf.take((pos + 1) as int) =~= naf.take(pos as int).push(0i8));
    // reconstruct(seq.push(0)) == reconstruct(seq) + 0 * pow2(len) == reconstruct(seq)
    // This should follow from the definition of reconstruct over sequences ending with 0.
    // We assert the key equality about reconstruct:
    assert(reconstruct(naf.take((pos + 1) as int)) == reconstruct(naf.take(pos as int))) by {
        // naf[pos] == 0i8, so the last term contributes 0
        let s = naf.take(pos as int);
        let s1 = naf.take((pos + 1) as int);
        assert(s1 == s.push(0i8));
        // reconstruct is defined recursively; the extra term is 0i8 * pow2(pos) = 0
        assert(reconstruct(s1) == reconstruct(s) + 0i8 as int * pow2(pos) as int) by {
            // By definition of reconstruct on s.push(v): reconstruct(s.push(v)) == reconstruct(s) + v * pow2(s.len())
        };
        assert(0i8 as int * pow2(pos) as int == 0) by {
            lemma_mul_basics(pow2(pos) as int);
        };
    };

    // Step 2: pow2(pos+1) == 2 * pow2(pos)
    lemma_pow2_plus_one(pos);

    // Step 3: We need to show that carry * pow2(pos+1) = carry * 2 * pow2(pos)
    // and use the old invariant to relate to scalar_val % pow2(pos+1).
    //
    // Old invariant: reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
    //
    // We want: reconstruct(naf.take(pos)) + carry * pow2(pos+1) == scalar_val % pow2(pos+1)
    //
    // scalar_val % pow2(pos+1) = scalar_val % (2 * pow2(pos))
    // By lemma_mod_breakdown: scalar_val % (2 * pow2(pos)) = 2 * ((scalar_val / 2) % pow2(pos)) + scalar_val % 2
    // But more directly, we can write:
    // scalar_val % pow2(pos+1) = (scalar_val % pow2(pos)) + (scalar_val / pow2(pos)) % 2 * pow2(pos)
    //
    // Since (carry + extracted) % 2 == 0, and extracted = (scalar_val / pow2(pos)) % pow2(w),
    // the low bit of extracted = (scalar_val / pow2(pos)) % 2.
    // So carry % 2 == (scalar_val / pow2(pos)) % 2 (both have the same parity).
    // Since carry <= 1, carry == (scalar_val / pow2(pos)) % 2.

    // The bit at position pos in scalar_val:
    let bit_pos = (scalar_val / pow2(pos)) % 2;

    // From (carry + extracted) % 2 == 0 and extracted == (scalar_val / pow2(pos)) % pow2(w):
    // low bit of extracted == (scalar_val / pow2(pos)) % 2 = bit_pos
    // carry + bit_pos ≡ 0 (mod 2), so carry ≡ bit_pos (mod 2)
    // Since carry <= 1 and bit_pos is 0 or 1, carry == bit_pos
    assert(extracted % 2 == bit_pos) by {
        // extracted = (scalar_val / pow2(pos)) % pow2(w)
        // (scalar_val / pow2(pos)) % pow2(w) % 2 == (scalar_val / pow2(pos)) % 2
        // because 2 divides pow2(w) when w >= 1
        lemma_mod_mod(
            (scalar_val / pow2(pos)) as int,
            2,
            pow2((w - 1) as nat) as int,
        );
        // pow2(w) = 2 * pow2(w-1), so (x % pow2(w)) % 2 == x % 2
        lemma_pow2_adds(1, (w - 1) as nat);
        assert(pow2(w) == 2 * pow2((w - 1) as nat));
        assert(extracted % 2 == (scalar_val / pow2(pos)) % 2) by {
            lemma_mod_mod(
                (scalar_val / pow2(pos)) as int,
                2,
                pow2((w - 1) as nat) as int,
            );
        };
    };
    assert(carry == bit_pos) by {
        // (carry + extracted) % 2 == 0, extracted % 2 == bit_pos
        // carry % 2 + bit_pos % 2 == 0 mod 2  => carry % 2 == bit_pos % 2
        // carry <= 1 and bit_pos <= 1, so carry == bit_pos
        assert((carry + bit_pos) % 2 == 0) by {
            assert((carry + extracted) % 2 == 0);
            assert(extracted % 2 == bit_pos);
            lemma_mod_add_eq(extracted as int, bit_pos as int, carry as int, 2);
        };
        assert(carry % 2 == carry) by {
            lemma_small_mod(carry, 2);
        };
        assert(bit_pos % 2 == bit_pos) by {
            lemma_small_mod(bit_pos, 2);
        };
    };

    // Step 4: Now use lemma_mod_breakdown to split scalar_val % pow2(pos+1)
    // scalar_val % (2 * pow2(pos)) == 2 * ((scalar_val / 2) % pow2(pos)) + scalar_val % 2
    // Better: use the partition:
    // scalar_val % pow2(pos+1) == scalar_val % pow2(pos) + bit_pos * pow2(pos)
    assert((scalar_val as int) % pow2((pos + 1) as nat) as int
        == (scalar_val as int) % pow2(pos) as int + bit_pos as int * pow2(pos) as int) by {
        // pow2(pos+1) = 2 * pow2(pos)
        lemma_pow2_plus_one(pos);
        assert(pow2((pos + 1) as nat) == 2 * pow2(pos));
        // By lemma_mod_breakdown with a=pow2(pos), b=2:
        // scalar_val % (pow2(pos) * 2) == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)
        lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
        // scalar_val % (pow2(pos) * 2) == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)
        assert(pow2(pos) as int * 2 == pow2((pos + 1) as nat) as int);
        assert((scalar_val as int) % (pow2(pos) as int * 2)
            == pow2(pos) as int * ((scalar_val as int / pow2(pos) as int) % 2) + (scalar_val as int) % pow2(pos) as int);
        // bit_pos = (scalar_val / pow2(pos)) % 2 as nat
        assert(bit_pos as int == (scalar_val as int / pow2(pos) as int) % 2) by {
            // Both are the same value, just int vs nat
            lemma_int_nat_mod_equiv((scalar_val / pow2(pos)) as int, 2);
        };
        lemma_mul_is_commutative(pow2(pos) as int, bit_pos as int);
    };

    // Step 5: Combine everything
    // reconstruct(naf.take(pos)) + carry * pow2(pos+1)
    // = reconstruct(naf.take(pos)) + bit_pos * (2 * pow2(pos))
    // = reconstruct(naf.take(pos)) + bit_pos * pow2(pos) + bit_pos * pow2(pos)
    // Hmm, that's not right. Let me reconsider.
    //
    // carry * pow2(pos+1) = bit_pos * 2 * pow2(pos)
    // But we want: reconstruct(naf.take(pos)) + carry * pow2(pos+1) == scalar_val % pow2(pos+1)
    //            = (scalar_val % pow2(pos)) + bit_pos * pow2(pos)
    //
    // From old invariant: reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
    // So: reconstruct(naf.take(pos)) = scalar_val % pow2(pos) - carry * pow2(pos)
    //                                 = scalar_val % pow2(pos) - bit_pos * pow2(pos)
    //
    // Then: reconstruct(naf.take(pos)) + carry * pow2(pos+1)
    //     = scalar_val % pow2(pos) - bit_pos * pow2(pos) + bit_pos * 2 * pow2(pos)
    //     = scalar_val % pow2(pos) + bit_pos * pow2(pos)
    //     = scalar_val % pow2(pos+1)  ✓

    // Let's verify this algebraically
    assert(reconstruct(naf.take((pos + 1) as int)) + (carry as int) * pow2((pos + 1) as nat) as int
        == (scalar_val as int) % pow2((pos + 1) as nat) as int) by {
        // Restate known facts
        let r_pos = reconstruct(naf.take(pos as int));
        let r_pos1 = reconstruct(naf.take((pos + 1) as int));
        let p = pow2(pos) as int;
        let p1 = pow2((pos + 1) as nat) as int;
        let c = carry as int;
        let sv = scalar_val as int;
        let bp = bit_pos as int;

        assert(r_pos1 == r_pos);
        assert(p1 == 2 * p) by {
            lemma_pow2_plus_one(pos);
        };
        assert(c == bp);
        // Old invariant: r_pos + c * p == sv % p
        assert(r_pos + c * p == sv % p);
        // Target: sv % p + bp * p
        assert(sv % p1 == sv % p + bp * p);
        // Compute LHS: r_pos1 + c * p1 = r_pos + bp * 2 * p
        assert(r_pos1 + c * p1 == r_pos + bp * (2 * p)) by {
            lemma_mul_is_distributive_add(bp, p, p);
            lemma_mul_is_associative(bp, 2, p);
        };
        // = (r_pos + c * p) + bp * p  (since c == bp, so bp * 2 * p = bp * p + bp * p = bp * p + c * p)
        // r_pos + bp * 2 * p = r_pos + bp * p + bp * p = (r_pos + c*p) + bp * p = sv % p + bp * p = sv % p1
        assert(r_pos + bp * (2 * p) == r_pos + bp * p + bp * p) by {
            lemma_mul_is_distributive_add(bp, p, p);
        };
        assert(r_pos + bp * p + bp * p == (r_pos + c * p) + bp * p);
        assert(sv % p + bp * p == sv % p1);
    };
