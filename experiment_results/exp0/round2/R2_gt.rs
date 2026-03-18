    let p_pos = pow2(pos) as int;
    let c = carry as int;
    let sv_mod_pos = (scalar_val as int) % pow2(pos) as int;
    let bit_at_pos: nat = (scalar_val / pow2(pos)) % 2;

    // Step 1: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)) since naf[pos] == 0
    assert(reconstruct(naf.take((pos + 1) as int)) == reconstruct(naf.take(pos as int))) by {
        lemma_reconstruct_zero_extend(naf, pos, (pos + 1) as nat);
    };

    // Step 2: extracted % 2 == bit_at_pos (mod-of-mod)
    assert(extracted % 2 == bit_at_pos) by {
        let sv_shifted = (scalar_val / pow2(pos)) as int;
        assert(pow2(w) == 2 * pow2((w - 1) as nat)) by {
            assert(pow2(1) == 2) by {
                lemma2_to64();
            };
            lemma_pow2_adds(1, (w - 1) as nat);
        };
        lemma_pow2_pos((w - 1) as nat);
        lemma_mod_mod(sv_shifted, 2, pow2((w - 1) as nat) as int);
    };

    // Step 3: carry == bit_at_pos (parity argument)
    assert(carry == bit_at_pos) by {
        if carry != bit_at_pos {
            assert((carry + extracted) % 2 != 0);
        }
    };

    // Step 4: scalar_val % pow2(pos+1) == carry * pow2(pos) + scalar_val % pow2(pos)
    assert((scalar_val as int) % pow2((pos + 1) as nat) as int == c * p_pos + sv_mod_pos) by {
        lemma_pow2_pos(pos);
        assert(pow2(pos) * 2 == pow2(pos + 1)) by {
            assert(pow2(1) == 2) by {
                lemma2_to64();
            };
            lemma_pow2_adds(pos, 1);
        };
        lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
        lemma_mul_is_commutative(p_pos, bit_at_pos as int);
    };

    // Step 5: Combine
    assert(pow2((pos + 1) as nat) == 2 * pow2(pos)) by {
        assert(pow2(1) == 2) by {
            lemma2_to64();
        };
        lemma_pow2_adds(1, pos);
        lemma_mul_is_commutative(pow2(1) as int, pow2(pos) as int);
    };
    assert(c * pow2((pos + 1) as nat) as int == c * 2 * p_pos) by {
        lemma_mul_is_associative(c, 2, p_pos);
    };
