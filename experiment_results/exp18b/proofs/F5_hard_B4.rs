    // Step 1: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)) since naf[pos] == 0
    // Note: lemma_reconstruct_zero_extend requires pos < naf.len(), new_len <= naf.len(), pos < new_len
    // Here pos < 256 == naf.len(), and pos+1 <= 256 == naf.len(), and pos < pos+1.
    lemma_reconstruct_zero_extend(naf, pos, (pos + 1) as nat);
    // Now: reconstruct(naf.take((pos+1) as int)) == reconstruct(naf.take(pos as int))

    // Step 2: Show pow2(pos+1) == 2 * pow2(pos)
    lemma_pow2_adds(1, pos);
    // pow2(1) * pow2(pos) == pow2(pos + 1)
    lemma2_to64();
    // pow2(1) == 2, so pow2(pos+1) == 2 * pow2(pos)
    assert(pow2((pos + 1) as nat) as int == 2 * pow2(pos) as int) by {
        lemma_pow2_adds(1, pos);
        lemma2_to64();
        assert(pow2(1usize as nat) == 2usize as nat);
        // lemma_pow2_adds(1, pos) gives pow2(1) * pow2(pos) == pow2(1 + pos)
        // Since 1 + pos == pos + 1 and pow2(1) == 2:
        assert(pow2(1) * pow2(pos) == pow2(1 + pos));
        assert((1 + pos) == (pos + 1) as nat);
    };

    // Step 3: Use lemma_mod_breakdown to decompose scalar_val % pow2(pos+1)
    // lemma_mod_breakdown(x, a, b): x % (a * b) == a * ((x / a) % b) + x % a
    // We want: scalar_val % pow2(pos+1) == scalar_val % (2 * pow2(pos))
    //        == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)
    // But let's use: pow2(pos+1) == 2 * pow2(pos)
    // So scalar_val % pow2(pos+1) == scalar_val % (2 * pow2(pos))
    // Using lemma_mod_breakdown(scalar_val, pow2(pos), 2):
    //   scalar_val % (pow2(pos) * 2) == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)
    lemma_pow2_pos(pos);
    lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
    // scalar_val % (pow2(pos) * 2) == pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)

    // Step 4: Show (carry + extracted) % 2 == 0 implies carry % 2 == extracted % 2
    // More precisely: carry == (scalar_val / pow2(pos)) % 2
    // We know extracted == (scalar_val / pow2(pos)) % pow2(w)
    // extracted % 2 == ((scalar_val / pow2(pos)) % pow2(w)) % 2
    // By lemma_mod_mod with a=2, b=pow2(w-1): (x % (2 * pow2(w-1))) % 2 == x % 2
    // pow2(w) == 2 * pow2(w-1) via lemma_pow2_adds(1, w-1)
    // So extracted % 2 == (scalar_val / pow2(pos)) % 2

    // Establish pow2(w) == 2 * pow2(w - 1)
    assert(w >= 2);
    let wm1 = (w - 1) as nat;
    lemma_pow2_adds(1, wm1);
    // pow2(1) * pow2(wm1) == pow2(1 + wm1) == pow2(w)
    assert(pow2(1) * pow2(wm1) == pow2(w));
    assert(pow2(1) == 2) by { lemma2_to64(); };
    assert(pow2(w) as int == 2 * pow2(wm1) as int);

    // extracted % 2 == (scalar_val / pow2(pos)) % 2
    // extracted == (scalar_val / pow2(pos)) % pow2(w)
    // Using lemma_mod_mod(scalar_val / pow2(pos), 2, pow2(wm1)):
    //   (x % (2 * pow2(wm1))) % 2 == x % 2  where x = scalar_val / pow2(pos)
    lemma_pow2_pos(wm1);
    lemma_mod_mod((scalar_val / pow2(pos)) as int, 2, pow2(wm1) as int);
    // ((scalar_val / pow2(pos)) % (2 * pow2(wm1))) % 2 == (scalar_val / pow2(pos)) % 2
    // Since 2 * pow2(wm1) == pow2(w):
    assert(extracted % 2 == (scalar_val / pow2(pos)) % 2) by {
        assert(extracted == (scalar_val / pow2(pos)) % pow2(w));
        assert(pow2(w) as int == 2 * pow2(wm1) as int);
        // extracted % 2 == ((scalar_val / pow2(pos)) % (2 * pow2(wm1))) % 2
        //               == (scalar_val / pow2(pos)) % 2   by lemma_mod_mod
        lemma_mul_is_commutative(2, pow2(wm1) as int);
        // lemma_mod_mod gives: (x % (a * b)) % a == x % a, with a=2, b=pow2(wm1)
        // So (x % (2 * pow2(wm1))) % 2 == x % 2
        assert(((scalar_val / pow2(pos)) % (2 * pow2(wm1) as int)) % 2
            == (scalar_val / pow2(pos)) % 2);
    };

    // Step 5: Show carry == (scalar_val / pow2(pos)) % 2
    // We know (carry + extracted) % 2 == 0, so carry % 2 == extracted % 2
    // carry <= 1, so carry == carry % 2
    // extracted % 2 == (scalar_val / pow2(pos)) % 2
    // So carry == (scalar_val / pow2(pos)) % 2
    assert(carry as int == (scalar_val / pow2(pos)) % 2) by {
        // (carry + extracted) % 2 == 0 means carry % 2 == (2 - extracted % 2) % 2 == extracted % 2
        // Since both carry and extracted % 2 are in {0, 1} and they sum to even:
        // Either both 0 or both 1 (but actually if sum is even and both in {0,1}, they must be equal)
        assert((carry + extracted) % 2 == 0);
        // carry <= 1
        assert(carry as int % 2 == carry as int) by {
            if carry == 0 { assert(0int % 2 == 0); }
            else { assert(1int % 2 == 1); }
        };
        // extracted % 2 == (scalar_val / pow2(pos)) % 2
        // carry % 2 == extracted % 2 (since sum is even)
        assert(carry as int % 2 == extracted % 2) by {
            // (carry + extracted) % 2 == 0 means carry % 2 + extracted % 2 is even
            // carry % 2 in {0,1}, extracted % 2 in {0,1}
            // their sum is even iff they're equal
            let c = carry as int % 2;
            let e = extracted % 2;
            assert(c == carry as int);  // carry <= 1
            assert(e == 0 || e == 1);
            assert(c == 0 || c == 1);
            assert((c + extracted) % 2 == 0) by {
                lemma_add_mod_noop(carry as int, extracted as int, 2);
            };
            assert((extracted % 2 + carry as int % 2) % 2 == 0) by {
                lemma_add_mod_noop(extracted as int, carry as int, 2);
                assert((extracted + carry as int) % 2 == (carry + extracted as nat) % 2 as int) by {
                    lemma_mul_is_commutative(carry as int, 1);
                };
            };
        };
        assert(carry as int == extracted % 2);
        assert(carry as int == (scalar_val / pow2(pos)) % 2);
    };

    // Step 6: Now combine to prove the goal
    // reconstruct(naf.take((pos+1) as int)) + carry * pow2(pos+1) == scalar_val % pow2(pos+1)
    //
    // LHS = reconstruct(naf.take(pos as int)) + carry * (2 * pow2(pos))   [step 1 + step 2]
    //     = reconstruct(naf.take(pos as int)) + (carry * 2) * pow2(pos)   [assoc]
    //
    // From old invariant:
    //   reconstruct(naf.take(pos as int)) + carry * pow2(pos) == scalar_val % pow2(pos)
    //
    // RHS = scalar_val % pow2(pos+1)
    //     = scalar_val % (2 * pow2(pos))
    //     = pow2(pos) * ((scalar_val / pow2(pos)) % 2) + scalar_val % pow2(pos)   [mod_breakdown]
    //     = pow2(pos) * carry + scalar_val % pow2(pos)                              [step 5]
    //     = carry * pow2(pos) + scalar_val % pow2(pos)                             [comm]
    //
    // But wait, LHS = reconstruct(naf.take(pos)) + carry * 2 * pow2(pos)
    //              = (scalar_val % pow2(pos) - carry * pow2(pos)) + 2 * carry * pow2(pos)
    //              = scalar_val % pow2(pos) + carry * pow2(pos)
    //              = RHS  ✓

    assert(reconstruct(naf.take((pos + 1) as int)) + (carry as int) * pow2((pos + 1) as nat) as int
        == (scalar_val as int) % pow2((pos + 1) as nat) as int) by {
        // Alias
        let rec_pos = reconstruct(naf.take(pos as int));
        let rec_pos1 = reconstruct(naf.take((pos + 1) as int));
        let p = pow2(pos) as int;
        let p1 = pow2((pos + 1) as nat) as int;
        let sv = scalar_val as int;
        let c = carry as int;

        // From step 1:
        assert(rec_pos1 == rec_pos);

        // From step 2:
        assert(p1 == 2 * p);

        // From old invariant:
        assert(rec_pos + c * p == sv % p);

        // From mod_breakdown (step 3):
        // sv % (p * 2) == p * ((sv / p) % 2) + sv % p
        assert(sv % (p * 2) == p * ((sv / p) % 2) + sv % p) by {
            lemma_mod_breakdown(sv, p, 2);
        };

        // carry == (scalar_val / pow2(pos)) % 2 (step 5):
        assert(c == (sv / p) % 2);

        // So sv % (p * 2) == p * c + sv % p
        // And sv % (2 * p) == sv % (p * 2) (commutativity of multiplication)
        assert(p * 2 == 2 * p) by { lemma_mul_is_commutative(p, 2); };
        assert(sv % (2 * p) == p * c + sv % p);

        // LHS = rec_pos1 + c * (2 * p) = rec_pos + 2 * c * p
        // RHS = sv % (2 * p) = p * c + sv % p = p * c + rec_pos + c * p - c * p + sv % p
        // Wait, from old invariant: sv % p == rec_pos + c * p
        // So RHS = p * c + rec_pos + c * p

        // LHS = rec_pos + c * 2 * p
        assert(c * (2 * p) == 2 * c * p) by {
            lemma_mul_is_associative(c, 2, p);
            lemma_mul_is_commutative(c, 2);
        };

        // RHS = p * c + rec_pos + c * p
        //     = c * p + rec_pos + c * p   (p*c = c*p)
        //     = rec_pos + 2 * c * p
        assert(p * c == c * p) by { lemma_mul_is_commutative(p, c); };
        assert(sv % (2 * p) == c * p + (rec_pos + c * p));
        assert(sv % (2 * p) == c * p + rec_pos + c * p);
        assert(c * p + rec_pos + c * p == rec_pos + 2 * c * p) by {
            // arithmetic
        };
        // So rec_pos + 2 * c * p == sv % (2 * p)
        assert(rec_pos + c * (2 * p) == sv % (2 * p));
        assert(rec_pos1 + c * p1 == sv % p1);
    };
