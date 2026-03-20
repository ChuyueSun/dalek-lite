    // Step 1: Split the reconstruction at pos.
    // reconstruct(naf.take(pos+1)) = reconstruct(naf.take(pos)) + pow2(pos) * naf[pos]
    // Since naf[pos] == 0, we get reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)).
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

    // Step 2: We need to show:
    //   reconstruct(naf.take(pos+1)) + carry * pow2(pos+1) == scalar_val % pow2(pos+1)
    //
    // From above: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))
    // From old invariant: reconstruct(naf.take(pos)) == scalar_val % pow2(pos) - carry * pow2(pos)
    //
    // So LHS = scalar_val % pow2(pos) - carry * pow2(pos) + carry * pow2(pos+1)
    //        = scalar_val % pow2(pos) + carry * (pow2(pos+1) - pow2(pos))
    //        = scalar_val % pow2(pos) + carry * pow2(pos)
    //
    // We need LHS == scalar_val % pow2(pos+1).
    // By lemma_mod_breakdown: scalar_val % pow2(pos+1) = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
    //
    // Key: we need to show carry == (scalar_val / pow2(pos)) % 2.
    // Since (carry + extracted) % 2 == 0, we have carry % 2 == extracted % 2 == (scalar_val/pow2(pos)) % 2.
    // More specifically: carry + extracted is even, and extracted == (scalar_val/pow2(pos)) % pow2(w).
    // So extracted % 2 == (scalar_val/pow2(pos)) % 2 (since w >= 2).
    // And carry % 2 == extracted % 2 (since their sum is even, and carry <= 1).
    // Since carry <= 1, carry == carry % 2 == (scalar_val/pow2(pos)) % 2.

    // Show pow2(pos+1) == 2 * pow2(pos)
    assert(pow2(pos1) == pow2(pos) + pow2(pos)) by {
        lemma_pow2_plus_one(pos);
    };

    // Show extracted % 2 == (scalar_val / pow2(pos)) % 2
    assert(extracted % 2 == (scalar_val / pow2(pos)) % 2) by {
        // extracted == (scalar_val / pow2(pos)) % pow2(w)
        // pow2(w) % 2 == 0 for w >= 1
        // So (scalar_val/pow2(pos)) % pow2(w) ≡ (scalar_val/pow2(pos)) mod 2
        // because pow2(w) is a multiple of 2 when w >= 1.
        assert(pow2(w) % 2 == 0) by {
            lemma_pow2_even(w);
        };
        // (x % (2*k)) % 2 == x % 2  when k > 0
        assert(pow2(w) >= 2) by {
            assert(pow2(w) % 2 == 0);
            lemma_pow2_pos(w);
        };
        // extracted == (scalar_val / pow2(pos)) % pow2(w)
        // extracted % 2 == ((scalar_val/pow2(pos)) % pow2(w)) % 2
        //               == (scalar_val/pow2(pos)) % 2   [since 2 divides pow2(w)]
        lemma_mod_mod(scalar_val / pow2(pos) as int, 2, pow2(w) as int / 2);
        // Alternatively use that pow2(w) == 2 * pow2(w-1) and mod collapses
        assert((extracted as int) % 2 == ((scalar_val as int) / pow2(pos) as int) % 2) by {
            let sv_div = (scalar_val / pow2(pos)) as int;
            assert(extracted as int == sv_div % pow2(w) as int);
            // (sv_div % pow2(w)) % 2 == sv_div % 2  since 2 | pow2(w)
            // pow2(w) = 2 * pow2(w-1), so pow2(w) is a multiple of 2
            // lemma_mod_mod: (x % (a*b)) % a == x % a
            let wm1 = (w - 1) as nat;
            assert(pow2(w) == 2 * pow2(wm1)) by {
                lemma_pow2_adds(1nat, wm1);
                assert(pow2(1nat) == 2) by { lemma2_to64(); };
            };
            lemma_mod_mod(sv_div, 2, pow2(wm1) as int);
            assert((sv_div % (pow2(w) as int)) % 2 == sv_div % 2);
        };
    };

    // Show carry == (scalar_val / pow2(pos)) % 2
    assert(carry as int == (scalar_val as int / pow2(pos) as int) % 2) by {
        // carry <= 1 and extracted % 2 == (scalar_val/pow2(pos)) % 2
        // (carry + extracted) % 2 == 0 means carry % 2 == extracted % 2 (they have same parity)
        // carry % 2 == carry (since carry <= 1)
        // extracted % 2 == (scalar_val/pow2(pos)) % 2
        let sv_bit = (scalar_val as int / pow2(pos) as int) % 2;
        assert(extracted as int % 2 == sv_bit);
        assert((carry as int + extracted as int) % 2 == 0);
        // carry % 2 == extracted % 2 mod 2
        assert(carry as int % 2 == extracted as int % 2) by {
            assert((carry as int + extracted as int) % 2 == 0);
            // If (a + b) % 2 == 0 then a % 2 == b % 2
            assert(carry as int % 2 == (0 - extracted as int) % 2) by {
                assert((carry as int + extracted as int) % 2 == 0);
            };
            assert((0 - extracted as int) % 2 == (2 - extracted as int % 2) % 2) by {
                lemma_add_mod_noop(0, -extracted as int, 2);
            };
            // simplified: (2 - x%2) % 2 == (2 - x%2) % 2; if x%2 == 0, res=0; if x%2==1, res=1
            assert((2 - extracted as int % 2) % 2 == extracted as int % 2) by {
                if extracted as int % 2 == 0 {
                    assert((2 - 0) % 2 == 0);
                } else {
                    assert(extracted as int % 2 == 1);
                    assert((2 - 1) % 2 == 1);
                }
            };
        };
        // carry <= 1, so carry == carry % 2
        assert(carry as int == carry as int % 2) by {
            if carry == 0 {
                assert(0int % 2 == 0);
            } else {
                assert(carry == 1);
                assert(1int % 2 == 1);
            }
        };
        assert(carry as int == sv_bit);
    };

    // Step 3: Apply lemma_mod_breakdown to expand scalar_val % pow2(pos+1)
    // scalar_val % pow2(pos+1) = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
    assert((scalar_val as int) % pow2(pos1) as int
        == pow2(pos) as int * ((scalar_val as int / pow2(pos) as int) % 2)
        + (scalar_val as int) % pow2(pos) as int) by {
        lemma_pow2_pos(pos);
        assert(pow2(pos1) == 2 * pow2(pos));
        lemma_mod_breakdown(scalar_val as int, 2, pow2(pos) as int);
        assert((scalar_val as int) % (2 * pow2(pos) as int)
            == 2 * ((scalar_val as int / 2) % pow2(pos) as int) + (scalar_val as int) % 2);
        // Alternative: use the form with divisor pow2(pos)
        lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
        // scalar_val % (pow2(pos) * 2) = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
        assert(pow2(pos) as int * 2 == pow2(pos1) as int);
    };

    // Step 4: Combine everything
    // LHS = reconstruct(naf.take(pos+1)) + carry * pow2(pos+1)
    //     = reconstruct(naf.take(pos)) + carry * (2 * pow2(pos))
    //     = (scalar_val % pow2(pos) - carry * pow2(pos)) + carry * 2 * pow2(pos)
    //     = scalar_val % pow2(pos) + carry * pow2(pos)
    //
    // RHS = scalar_val % pow2(pos+1)
    //     = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
    //     = pow2(pos) * carry + scalar_val % pow2(pos)   [since carry == (scalar_val/pow2(pos))%2]
    //
    // LHS == RHS. QED.
    assert(reconstruct(naf.take(pos1 as int)) + (carry as int) * pow2(pos1) as int
        == (scalar_val as int) % pow2(pos1) as int) by {
        // We know:
        // (A) reconstruct(naf.take(pos1)) == reconstruct(naf.take(pos))
        // (B) reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
        // (C) carry == (scalar_val / pow2(pos)) % 2
        // (D) scalar_val % pow2(pos1) = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
        // (E) pow2(pos1) == 2 * pow2(pos)
        let rec_pos = reconstruct(naf.take(pos as int));
        let rec_pos1 = reconstruct(naf.take(pos1 as int));
        assert(rec_pos1 == rec_pos);
        assert(rec_pos + (carry as int) * pow2(pos) as int == (scalar_val as int) % pow2(pos) as int);
        assert(carry as int == (scalar_val as int / pow2(pos) as int) % 2);
        assert((scalar_val as int) % pow2(pos1) as int
            == pow2(pos) as int * ((scalar_val as int / pow2(pos) as int) % 2)
            + (scalar_val as int) % pow2(pos) as int);
        assert(pow2(pos1) as int == 2 * pow2(pos) as int);
        // LHS = rec_pos1 + carry * pow2(pos1)
        //     = rec_pos + carry * (2 * pow2(pos))
        // From (B): rec_pos = scalar_val%pow2(pos) - carry*pow2(pos)
        // LHS = scalar_val%pow2(pos) - carry*pow2(pos) + carry*2*pow2(pos)
        //     = scalar_val%pow2(pos) + carry*pow2(pos)
        // RHS = pow2(pos)*carry + scalar_val%pow2(pos)
        // So LHS == RHS.
        assert(rec_pos1 + (carry as int) * pow2(pos1) as int
            == (scalar_val as int) % pow2(pos) as int + (carry as int) * pow2(pos) as int) by {
            lemma_mul_is_distributive_add(carry as int, pow2(pos1) as int - pow2(pos) as int, pow2(pos) as int);
            assert((carry as int) * pow2(pos1) as int
                == (carry as int) * (pow2(pos1) as int - pow2(pos) as int) + (carry as int) * pow2(pos) as int);
            assert((carry as int) * (pow2(pos1) as int - pow2(pos) as int)
                == (carry as int) * pow2(pos) as int) by {
                assert(pow2(pos1) as int - pow2(pos) as int == pow2(pos) as int);
            };
            assert(rec_pos1 + (carry as int) * pow2(pos1) as int
                == rec_pos + (carry as int) * pow2(pos) as int + (carry as int) * pow2(pos) as int);
            assert(rec_pos + (carry as int) * pow2(pos) as int == (scalar_val as int) % pow2(pos) as int);
        };
        assert((scalar_val as int) % pow2(pos) as int + (carry as int) * pow2(pos) as int
            == (scalar_val as int) % pow2(pos1) as int) by {
            assert((scalar_val as int) % pow2(pos1) as int
                == pow2(pos) as int * (carry as int) + (scalar_val as int) % pow2(pos) as int);
            lemma_mul_is_commutative(carry as int, pow2(pos) as int);
        };
    };
