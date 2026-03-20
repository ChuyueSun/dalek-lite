proof fn lemma_carry_bit_from_window_parity(
    scalar_val: nat,
    pos: nat,
    carry: nat,
    w: nat,
    extracted: nat,
)
    requires
        w >= 2,
        carry <= 1,
        extracted == (scalar_val / pow2(pos)) % pow2(w),
        (carry + extracted) % 2 == 0,
    ensures
        (((scalar_val as int) / pow2(pos) as int) % 2) == carry as int,
{
    // Establish: pow2(w) == 2 * pow2(w-1)
    let wm1: nat = (w - 1) as nat;
    lemma_pow2_adds(1, wm1);
    lemma2_to64();
    // Now pow2(1) * pow2(wm1) == pow2(w) and pow2(1) == 2
    // => pow2(w) == 2 * pow2(wm1)
    assert(pow2(w) as int == 2 * pow2(wm1) as int) by {
        lemma_pow2_adds(1, wm1);
        lemma2_to64();
        assert(pow2(1) * pow2(wm1) == pow2(1 + wm1));
        assert(1 + wm1 == w);
        assert(pow2(1) == 2);
    };

    // The integer quotient of scalar_val divided by pow2(pos)
    let quot: int = (scalar_val as int) / (pow2(pos) as int);

    // pow2(pos) > 0 and pow2(wm1) > 0
    lemma_pow2_pos(pos);
    lemma_pow2_pos(wm1);

    // Nat division coincides with int division (both operands non-negative,
    // divisor positive): (scalar_val / pow2(pos)) as int == quot
    // This is an axiom of Verus nat/int coercion with positive divisor.
    assert((scalar_val / pow2(pos)) as int == quot);

    // Therefore extracted as int == quot % pow2(w) as int
    assert(extracted as int == quot % (pow2(w) as int));

    // Apply lemma_mod_mod(quot, 2, pow2(wm1)):
    // requires 2 > 0, pow2(wm1) > 0 — both hold
    // ensures (quot % (2 * pow2(wm1))) % 2 == quot % 2
    lemma_mod_mod(quot, 2, pow2(wm1) as int);

    // Since pow2(w) == 2 * pow2(wm1), we get extracted % 2 == quot % 2
    assert(extracted as int % 2 == quot % 2) by {
        assert(pow2(w) as int == 2 * pow2(wm1) as int);
        assert((quot % (2 * pow2(wm1) as int)) % 2 == quot % 2);
        assert(extracted as int == quot % (pow2(w) as int));
    };

    // lemma_add_mod_noop: (carry + extracted) % 2 == ((carry%2) + (extracted%2)) % 2
    lemma_add_mod_noop(carry as int, extracted as int, 2);
    // The precondition gives (carry + extracted) % 2 == 0 (as nat), which as int:
    assert(((carry as int) + (extracted as int)) % 2 == 0);
    // So ((carry%2) + (extracted%2)) % 2 == 0
    assert(((carry as int % 2) + (extracted as int % 2)) % 2 == 0);

    // carry <= 1 implies carry % 2 == carry as int
    assert(carry as int % 2 == carry as int) by {
        if carry == 0 {
            lemma_small_mod(0nat, 2);
        } else {
            // carry == 1 since carry <= 1 and carry != 0
            assert(carry == 1);
            lemma_small_mod(1nat, 2);
        }
    };

    // quot % 2 is in {0, 1}
    lemma_mod_pos_bound(quot, 2);
    assert(0 <= quot % 2 < 2);

    // Conclude: carry == quot % 2
    // We have: (carry + (quot % 2)) % 2 == 0
    // carry in {0,1}, quot%2 in {0,1}
    // => carry + quot%2 in {0,1,2}, and must be even => in {0,2}
    // => carry == quot % 2
    assert(carry as int == quot % 2) by {
        assert(extracted as int % 2 == quot % 2);
        assert(carry as int % 2 == carry as int);
        assert(((carry as int) + (extracted as int % 2)) % 2 == 0);
        assert(((carry as int) + (quot % 2)) % 2 == 0);
        assert(0 <= quot % 2 < 2);
        assert(carry as int == 0 || carry as int == 1);
        // Z3 can close this: two values in {0,1} summing to even must be equal
    };
}
