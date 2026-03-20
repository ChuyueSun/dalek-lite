    // Step 1: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))
    // because naf[pos] == 0.
    // NOTE: The registry signature for lemma_reconstruct_zero_extend differs from the sibling.
    // The registry version requires: pos < naf.len(), new_len <= naf.len(), pos < new_len,
    // naf[pos as int] == 0i8. Here pos < 256 == naf.len(), pos+1 <= 256, pos < pos+1.
    lemma_reconstruct_zero_extend(naf, pos, (pos + 1) as nat);
    // Now reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))

    // Step 2: Relate pow2(pos+1) to 2 * pow2(pos)
    lemma_pow2_adds(1, pos);
    // pow2(1) * pow2(pos) == pow2(pos+1)
    // From lemma2_to64: pow2(1) == 2
    lemma2_to64();
    // So pow2(pos+1) == 2 * pow2(pos)

    // Step 3: Expand scalar_val % pow2(pos+1) using lemma_mod_breakdown
    // lemma_mod_breakdown(x, a, b): x % (a*b) == a * ((x/a) % b) + x % a
    // With x = scalar_val as int, a = pow2(pos) as int, b = 2
    lemma_pow2_pos(pos);
    lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
    // scalar_val % (pow2(pos)*2) == pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)

    // Step 4: The bit at position pos of scalar_val equals carry.
    // (carry + extracted) % 2 == 0 means carry % 2 == extracted % 2
    // extracted == (scalar_val / pow2(pos)) % pow2(w)
    // (scalar_val / pow2(pos)) % 2 == extracted % 2 (since pow2(w) >= 4, taking mod 2 of a mod pow2(w) = mod 2)
    // So (scalar_val / pow2(pos)) % 2 == carry % 2 == carry (since carry <= 1)
    assert((scalar_val as int / pow2(pos) as int) % 2 == carry as int) by {
        // extracted % 2 == carry % 2 (from (carry + extracted) % 2 == 0)
        // (scalar_val / pow2(pos)) % 2 == extracted % 2
        // because extracted = (scalar_val / pow2(pos)) % pow2(w) and pow2(w) is divisible by 2 (w>=2)
        assert(extracted % 2 == (scalar_val / pow2(pos)) % pow2(w) % 2) by {
            // trivial since extracted == (scalar_val / pow2(pos)) % pow2(w)
        };
        // pow2(w) = 2 * pow2(w-1), so (x % pow2(w)) % 2 == x % 2
        // Use lemma_mod_mod: (x % (a*b)) % a == x % a with a=2, b=pow2(w-1)
        // But we need to compute pow2(w-1)... Instead use lemma_pow2_adds(1, w-1)
        // Actually: (scalar_val/pow2(pos)) % pow2(w) % 2
        //        == (scalar_val/pow2(pos)) % (2 * pow2(w-1)) % 2
        //        == (scalar_val/pow2(pos)) % 2  [by lemma_mod_mod with a=2, b=pow2(w-1)]
        let sv_shifted = scalar_val as int / pow2(pos) as int;
        lemma_pow2_adds(1, (w - 1) as nat);
        lemma_pow2_pos((w - 1) as nat);
        lemma2_to64();
        // pow2(1) * pow2(w-1) == pow2(w), pow2(1)==2
        assert(pow2(w) as int == 2 * pow2((w - 1) as nat) as int);
        lemma_mod_mod(sv_shifted, 2, pow2((w - 1) as nat) as int);
        // (sv_shifted % (2 * pow2(w-1))) % 2 == sv_shifted % 2
        assert(sv_shifted % pow2(w) as int % 2 == sv_shifted % 2);
        // extracted == sv_shifted % pow2(w)
        assert(extracted as int % 2 == sv_shifted % 2);
        // (carry + extracted) % 2 == 0 means carry % 2 == extracted % 2 (mod 2)
        assert((carry as int + extracted as int) % 2 == 0);
        assert(carry as int % 2 == extracted as int % 2) by {
            assert((carry as int + extracted as int) % 2 == (carry as int % 2 + extracted as int % 2) % 2);
            // carry <= 1 so carry % 2 == carry
            assert(carry as int % 2 == carry as int);
        };
        assert(carry as int == sv_shifted % 2);
    };

    // Step 5: Assemble the final equality
    // LHS = reconstruct(naf.take(pos+1)) + carry * pow2(pos+1)
    //      = reconstruct(naf.take(pos)) + carry * (2 * pow2(pos))  [steps 1, 2]
    // RHS = scalar_val % pow2(pos+1)
    //      = scalar_val % (2 * pow2(pos))
    //      = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)  [step 3]
    //      = pow2(pos) * carry + scalar_val % pow2(pos)  [step 4]
    // From old invariant: reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)
    // So scalar_val % pow2(pos) == reconstruct(naf.take(pos)) + carry * pow2(pos)
    // RHS = pow2(pos) * carry + reconstruct(naf.take(pos)) + carry * pow2(pos)
    //      = reconstruct(naf.take(pos)) + 2 * carry * pow2(pos)
    //      = LHS  ✓
    assert(reconstruct(naf.take((pos + 1) as int)) + carry as int * pow2((pos + 1) as nat) as int
        == scalar_val as int % pow2((pos + 1) as nat) as int) by {
        // reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))
        // pow2(pos+1) == 2 * pow2(pos)
        assert(pow2((pos + 1) as nat) as int == 2 * pow2(pos) as int);
        // scalar_val % pow2(pos+1) == pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
        assert(scalar_val as int % (pow2((pos + 1) as nat) as int)
            == pow2(pos) as int * ((scalar_val as int / pow2(pos) as int) % 2)
                + scalar_val as int % pow2(pos) as int);
        // (scalar_val/pow2(pos)) % 2 == carry
        assert((scalar_val as int / pow2(pos) as int) % 2 == carry as int);
        // So RHS == pow2(pos)*carry + scalar_val%pow2(pos)
        //        == pow2(pos)*carry + reconstruct(naf.take(pos)) + carry*pow2(pos)  [old invariant reversed]
        //   Wait: old invariant says reconstruct(naf.take(pos)) + carry*pow2(pos) == scalar_val%pow2(pos)
        //   So scalar_val%pow2(pos) == reconstruct(naf.take(pos)) + carry*pow2(pos)
        // RHS = pow2(pos)*carry + reconstruct(naf.take(pos)) + carry*pow2(pos)
        //     = reconstruct(naf.take(pos)) + 2*carry*pow2(pos)
        // LHS = reconstruct(naf.take(pos)) + carry * (2*pow2(pos))
        //     = reconstruct(naf.take(pos)) + 2*carry*pow2(pos)
        lemma_mul_is_commutative(pow2(pos) as int, carry as int);
        lemma_mul_is_distributive_add(carry as int, pow2(pos) as int, pow2(pos) as int);
    };
