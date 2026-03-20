{
    // Step 1: naf[pos] == 0 means the (pos+1)-prefix reconstruction equals the pos-prefix reconstruction.
    lemma_take_pos_plus_one_zero(naf, pos);
    // Now: reconstruct(naf.take((pos+1) as int)) == reconstruct(naf.take(pos as int))

    // Step 2: pow2(pos+1) == 2 * pow2(pos)
    lemma_pow2_step(pos);
    // Now: pow2((pos+1) as nat) == 2 * pow2(pos)

    // Step 3: scalar_val % pow2(pos+1) == pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)
    lemma_scalar_mod_breakdown_step(scalar_val, pos);

    // Step 4: (scalar_val/pow2(pos)) % 2 == carry
    // Precondition: (carry + extracted) % 2 == 0, extracted == (scalar_val/pow2(pos)) % pow2(w)
    // This means (scalar_val/pow2(pos)) % 2 == carry % 2 == carry (since carry <= 1)
    lemma_carry_bit_from_window_parity(scalar_val, pos, carry, w, extracted);
    // Now: (scalar_val/pow2(pos)) % 2 == carry

    // Combine:
    // RHS goal = scalar_val % pow2(pos+1)
    //          = pow2(pos) * ((scalar_val/pow2(pos)) % 2) + scalar_val % pow2(pos)   [step 3]
    //          = pow2(pos) * carry + scalar_val % pow2(pos)                          [step 4]
    //
    // LHS goal = reconstruct(naf.take((pos+1) as int)) + carry * pow2(pos+1)
    //          = reconstruct(naf.take(pos as int)) + carry * (2 * pow2(pos))         [steps 1, 2]
    //
    // From the inductive hypothesis (requires clause):
    //   reconstruct(naf.take(pos as int)) + carry * pow2(pos) == scalar_val % pow2(pos)
    // So:
    //   reconstruct(naf.take(pos as int)) == scalar_val % pow2(pos) - carry * pow2(pos)
    //
    // Substituting into LHS:
    //   LHS = (scalar_val % pow2(pos) - carry * pow2(pos)) + carry * 2 * pow2(pos)
    //       = scalar_val % pow2(pos) + carry * pow2(pos)
    //       = RHS  ✓
    //
    // We now assert the arithmetic identity that Verus/Z3 should close automatically
    // given the equalities established above.

    // Unfold carry * pow2(pos+1) == 2 * carry * pow2(pos) using distributivity and commutativity.
    lemma_mul_is_commutative(carry as int, pow2((pos + 1) as nat) as int);
    // pow2(pos+1) * carry == carry * pow2(pos+1)
    lemma_mul_is_distributive_add(pow2(pos) as int, 1int, 1int);
    // just warming up the SMT with mul lemmas; Z3 should now close the goal via linear arithmetic
    assert(
        reconstruct(naf.take((pos + 1) as int)) + (carry as int) * pow2((pos + 1) as nat) as int
            == (scalar_val as int) % pow2((pos + 1) as nat) as int
    ) by {
        // All needed equalities are now in context; rely on Z3 linear arithmetic.
    };
}
