// STRATEGY: Split the reconstruction into three parts — prefix [0..i], the pair
// at [i, i+1], and the tail [i+2..] — using lemma_reconstruct_radix_2w_split twice.
// The prefix and tail are identical between old and new. For the pair, expand
// reconstruct_radix_2w via its definition and use distributivity to show that
// the carry terms (−carry·pow2(w) in digit i, +carry in digit i+1) cancel
// algebraically because pow2(w)·(old[i+1] + carry) − carry·pow2(w) = pow2(w)·old[i+1].

{
    let n = old_digits.len();
    let i_int = i as int;

    // ------------------------------------------------------------------
    // Step 1: Split both reconstructions at position i
    // reconstruct(digits, w) = reconstruct(digits[0..i], w)
    //                        + pow2(w*i) * reconstruct(digits[i..], w)
    // ------------------------------------------------------------------
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    lemma_reconstruct_radix_2w_split(new_digits, i, w);

    // The prefix [0..i] is identical
    assert(old_digits.take(i_int) =~= new_digits.take(i_int)) by {
        assert forall|j: int| 0 <= j < i_int implies old_digits[j] == new_digits[j] by {
            // j < i, so j != i and j != i+1; by the forall precondition digits agree
        }
    }

    // ------------------------------------------------------------------
    // Step 2: Split the suffix [i..] at position 2 to isolate the pair
    // reconstruct(digits[i..], w) = reconstruct(digits[i..][0..2], w)
    //                             + pow2(w*2) * reconstruct(digits[i..][2..], w)
    // ------------------------------------------------------------------
    let old_suffix = old_digits.skip(i_int);
    let new_suffix = new_digits.skip(i_int);

    lemma_reconstruct_radix_2w_split(old_suffix, 2, w);
    lemma_reconstruct_radix_2w_split(new_suffix, 2, w);

    let old_pair = old_suffix.take(2);
    let new_pair = new_suffix.take(2);
    let old_rest = old_suffix.skip(2);
    let new_rest = new_suffix.skip(2);

    // The tail [i+2..] is identical
    assert(old_rest =~= new_rest) by {
        assert forall|j: int| 0 <= j < old_rest.len() implies old_rest[j] == new_rest[j] by {
            // old_rest[j] == old_digits[i + 2 + j]
            // i + 2 + j >= i + 2, so it is != i and != i+1 => digits agree
        }
    }

    // ------------------------------------------------------------------
    // Step 3: Expand reconstruct_radix_2w for the 2-element pair sequences
    // reconstruct([a, b], w) = a + pow2(w) * b
    // ------------------------------------------------------------------
    assert(old_pair[0] == old_digits[i_int]);
    assert(old_pair[1] == old_digits[i_int + 1]);
    assert(new_pair[0] == new_digits[i_int]);
    assert(new_pair[1] == new_digits[i_int + 1]);

    // Unroll old_pair reconstruction
    let old_pair_tail = old_pair.skip(1);
    assert(old_pair_tail.len() == 1);
    assert(old_pair_tail[0] == old_pair[1]);
    assert(reconstruct_radix_2w(old_pair_tail.skip(1), w) == 0);
    assert(reconstruct_radix_2w(old_pair_tail, w) == (old_pair[1] as int) + pow2(w) * 0);
    assert(reconstruct_radix_2w(old_pair_tail, w) == (old_pair[1] as int)) by {
        lemma_mul_basics(pow2(w) as int);
    }
    assert(reconstruct_radix_2w(old_pair, w)
        == (old_pair[0] as int) + pow2(w) * reconstruct_radix_2w(old_pair_tail, w));
    let old_pair_val: int = (old_digits[i_int] as int) + pow2(w) * (old_digits[i_int + 1] as int);
    assert(reconstruct_radix_2w(old_pair, w) == old_pair_val);

    // Unroll new_pair reconstruction
    let new_pair_tail = new_pair.skip(1);
    assert(new_pair_tail.len() == 1);
    assert(new_pair_tail[0] == new_pair[1]);
    assert(reconstruct_radix_2w(new_pair_tail.skip(1), w) == 0);
    assert(reconstruct_radix_2w(new_pair_tail, w) == (new_pair[1] as int) + pow2(w) * 0);
    assert(reconstruct_radix_2w(new_pair_tail, w) == (new_pair[1] as int)) by {
        lemma_mul_basics(pow2(w) as int);
    }
    assert(reconstruct_radix_2w(new_pair, w)
        == (new_pair[0] as int) + pow2(w) * reconstruct_radix_2w(new_pair_tail, w));
    let new_pair_val: int = (new_digits[i_int] as int) + pow2(w) * (new_digits[i_int + 1] as int);
    assert(reconstruct_radix_2w(new_pair, w) == new_pair_val);

    // ------------------------------------------------------------------
    // Step 4: Show the pair reconstructions are equal
    // new_pair_val = (old[i] - carry*pow2(w)) + pow2(w) * (old[i+1] + carry)
    //             = old[i] - carry*pow2(w) + pow2(w)*old[i+1] + pow2(w)*carry
    //             = old[i] + pow2(w)*old[i+1]
    //             = old_pair_val
    // ------------------------------------------------------------------
    assert(new_digits[i_int] == old_digits[i_int] - carry * (pow2(w) as int));
    assert(new_digits[i_int + 1] == old_digits[i_int + 1] + carry);

    assert(reconstruct_radix_2w(new_pair, w) == reconstruct_radix_2w(old_pair, w)) by {
        // Expand pow2(w) * (old[i+1] + carry) = pow2(w)*old[i+1] + pow2(w)*carry
        lemma_mul_is_distributive_add(pow2(w) as int, old_digits[i_int + 1] as int, carry);
        // The carry terms: -carry*pow2(w) + pow2(w)*carry = 0
        // So new_pair_val = old_pair_val
    }

    // ------------------------------------------------------------------
    // Step 5: Assemble the full equality
    // All three parts agree => overall reconstructions agree
    // ------------------------------------------------------------------
    assert(reconstruct_radix_2w(new_digits, w) == reconstruct_radix_2w(old_digits, w));
}
