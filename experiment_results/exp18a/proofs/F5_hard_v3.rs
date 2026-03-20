// STRATEGY:
// We need to advance the invariant from pos to pos+1 when naf[pos]==0 and the window is even.
// The core calculation expands scalar_val % pow2(pos+1) into scalar_val % pow2(pos) + bit_at(pos)*pow2(pos),
// where bit_at(pos) = (scalar_val / pow2(pos)) % 2. Since extracted == (scalar_val/pow2(pos)) % pow2(w)
// and (carry + extracted) % 2 == 0, we get (carry + bit_at(pos)) % 2 == 0, so carry == bit_at(pos) (both 0 or 1).
// We then show reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)) (because naf[pos]==0),
// and combine with the old invariant and the pow2(pos+1) = 2*pow2(pos) doubling to close the goal.

{
    // Step 1: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))
    // because naf[pos] == 0.
    let pos_int = pos as int;
    let pos1_int = (pos + 1) as int;

    // Split naf.take(pos+1) at pos
    lemma_reconstruct_split(naf.take(pos1_int), pos);
    assert(naf.take(pos1_int).take(pos_int) =~= naf.take(pos_int));

    // The suffix of naf.take(pos+1) starting at pos is exactly [naf[pos]] == [0]
    let suffix = naf.take(pos1_int).skip(pos_int);
    assert(suffix.len() == 1);
    assert(suffix[0] == naf[pos_int]);
    assert(suffix[0] == 0i8);
    assert(suffix.skip(1).len() == 0);
    assert(reconstruct(suffix.skip(1)) == 0);
    // reconstruct(suffix) == naf[pos] as int * pow2(0) + pow2(1) * reconstruct([]) = 0
    assert(reconstruct(suffix) == 0) by {
        // reconstruct([x]) = x * pow2(0) + pow2(1) * reconstruct([])
        // = 0 * 1 + 2 * 0 = 0
        lemma_mul_basics(pow2(pos) as int);
    };
    // So reconstruct(naf.take(pos+1)) = reconstruct(naf.take(pos)) + pow2(pos) * 0
    assert(pow2(pos) as int * reconstruct(suffix) == 0) by {
        lemma_mul_basics(pow2(pos) as int);
    };
    assert(reconstruct(naf.take(pos1_int)) == reconstruct(naf.take(pos_int)));

    // Step 2: Compute bit_at(pos) = (scalar_val / pow2(pos)) % 2
    let bit_at_pos: nat = (scalar_val / pow2(pos)) % 2;

    // Since extracted == (scalar_val / pow2(pos)) % pow2(w) and w >= 2,
    // extracted % 2 == bit_at_pos
    assert(extracted % 2 == bit_at_pos) by {
        // pow2(w) is divisible by 2 since w >= 2
        lemma_pow2_even(w);
        // extracted % pow2(w) % 2 == extracted % 2
        // and extracted % 2 == (scalar_val/pow2(pos)) % 2 = bit_at_pos
        lemma_mod_mod(extracted as int, 2, pow2(w) as int / 2);
        // more directly: extracted = (scalar_val/pow2(pos)) % pow2(w)
        // so extracted % 2 = ((scalar_val/pow2(pos)) % pow2(w)) % 2
        //                  = (scalar_val/pow2(pos)) % 2 (since 2 | pow2(w))
        lemma_mod_mod(scalar_val as int / pow2(pos) as int, 2, pow2(w) as int / 2);
    };

    // From (carry + extracted) % 2 == 0 and extracted % 2 == bit_at_pos:
    // carry % 2 == bit_at_pos % 2, and since carry <= 1 and bit_at_pos < 2,
    // carry == bit_at_pos.
    assert(carry == bit_at_pos) by {
        assert((carry + extracted) % 2 == 0);
        assert(extracted % 2 == bit_at_pos);
        // (carry + bit_at_pos) % 2 == 0 => carry == bit_at_pos (both 0 or 1)
        assert(carry + bit_at_pos < 4);
        assert((carry + bit_at_pos) % 2 == 0);
        // carry <= 1 and bit_at_pos <= 1 => if sum is even, they're equal
        if carry == 0 {
            assert(bit_at_pos % 2 == 0);
            assert(bit_at_pos < 2);
            assert(bit_at_pos == 0);
        } else {
            assert(carry == 1);
            assert((1 + bit_at_pos) % 2 == 0);
            assert(bit_at_pos < 2);
            assert(bit_at_pos == 1);
        }
    };

    // Step 3: Expand scalar_val % pow2(pos+1)
    // scalar_val % pow2(pos+1) = scalar_val % pow2(pos) + bit_at_pos * pow2(pos)
    // This follows from lemma_mod_breakdown with (pos+1) = pos + 1
    let p = pow2(pos) as int;
    let p1 = pow2((pos + 1) as nat) as int;

    assert(p1 == 2 * p) by {
        lemma_pow2_plus_one(pos);
    };

    // scalar_val % pow2(pos+1) = scalar_val % (2 * pow2(pos))
    //   = 2 * ((scalar_val / 2) % pow2(pos)) + scalar_val % 2  ... no, use lemma_mod_breakdown
    // lemma_mod_breakdown(x, a, b): x % (a*b) == a * ((x/a) % b) + x % a
    // Use a=pow2(pos), b=2:
    //   scalar_val % (pow2(pos)*2) = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
    //                              = pow2(pos) * bit_at_pos + scalar_val % pow2(pos)
    assert(scalar_val as int % p1 == p * bit_at_pos as int + scalar_val as int % p) by {
        lemma_mod_breakdown(scalar_val as int, p, 2);
        assert(p1 == p * 2);
        assert(scalar_val as int % (p * 2) == p * ((scalar_val as int / p) % 2) + scalar_val as int % p);
        assert((scalar_val as int / p) % 2 == bit_at_pos as int) by {
            lemma_int_nat_mod_equiv(scalar_val as int / p, 2);
        };
    };

    // Step 4: Assemble the final equality
    // We have:
    //   reconstruct(naf.take(pos)) + carry * pow2(pos) == scalar_val % pow2(pos)   [old inv]
    //   reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos))                  [naf[pos]==0]
    //   carry == bit_at_pos
    //   scalar_val % pow2(pos+1) == bit_at_pos * pow2(pos) + scalar_val % pow2(pos)
    //   pow2(pos+1) == 2 * pow2(pos)
    //
    // Goal: reconstruct(naf.take(pos+1)) + carry * pow2(pos+1) == scalar_val % pow2(pos+1)
    //
    // LHS = reconstruct(naf.take(pos)) + carry * 2 * pow2(pos)
    //     = (scalar_val % pow2(pos) - carry * pow2(pos)) + carry * 2 * pow2(pos)
    //     = scalar_val % pow2(pos) + carry * pow2(pos)
    //     = scalar_val % pow2(pos) + bit_at_pos * pow2(pos)
    //     = scalar_val % pow2(pos+1)  = RHS

    assert(reconstruct(naf.take(pos1_int)) + carry as int * p1 == scalar_val as int % p1) by {
        // reconstruct(naf.take(pos+1)) = reconstruct(naf.take(pos))
        // old inv: reconstruct(naf.take(pos)) = scalar_val % pow2(pos) - carry * pow2(pos)
        // carry * pow2(pos+1) = carry * 2 * pow2(pos)
        // total = scalar_val % pow2(pos) - carry * pow2(pos) + carry * 2 * pow2(pos)
        //       = scalar_val % pow2(pos) + carry * pow2(pos)
        //       = scalar_val % pow2(pos) + bit_at_pos * pow2(pos)
        //       = scalar_val % pow2(pos+1)
        let old_inv = scalar_val as int % p - carry as int * p;
        assert(reconstruct(naf.take(pos_int)) == old_inv);
        assert(carry as int * p1 == carry as int * (2 * p)) by {
            lemma_mul_is_distributive_add(carry as int, p, p);
        };
        assert(carry as int * (2 * p) == 2 * (carry as int * p)) by {
            lemma_mul_is_associative(2, carry as int, p);
            lemma_mul_is_commutative(carry as int, 2);
        };
        // total = old_inv + carry * 2 * pow2(pos)
        //       = (scalar_val%p - carry*p) + 2*carry*p
        //       = scalar_val%p + carry*p
        //       = scalar_val%p + bit_at_pos*p
        //       = scalar_val % p1
        assert(old_inv + carry as int * p1 == scalar_val as int % p + carry as int * p);
        assert(carry as int == bit_at_pos as int);
        assert(scalar_val as int % p + bit_at_pos as int * p == scalar_val as int % p1);
    };
}
