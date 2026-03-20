    let n = old_digits.len();
    let pw = pow2(w) as int;

    // Step 1: Split both reconstructions at position i
    lemma_reconstruct_radix_2w_split(old_digits, i as int, w);
    lemma_reconstruct_radix_2w_split(new_digits, i as int, w);

    // Prefixes before position i are identical (digits unchanged)
    assert(old_digits.take(i as int) =~= new_digits.take(i as int)) by {
        assert forall|j: int| 0 <= j < i implies old_digits[j] == new_digits[j] by {
            assert(old_digits[j] == new_digits[j]);
        }
        assert(old_digits.take(i as int) =~= new_digits.take(i as int));
    }

    // So prefix reconstructions are equal
    assert(reconstruct_radix_2w(old_digits.take(i as int), w)
        == reconstruct_radix_2w(new_digits.take(i as int), w));

    // Step 2: Work on the suffix from position i
    let old_suffix = old_digits.skip(i as int);
    let new_suffix = new_digits.skip(i as int);

    // Step 3: Split suffix at position 1 to isolate digit i
    lemma_reconstruct_radix_2w_split(old_suffix, 1, w);
    lemma_reconstruct_radix_2w_split(new_suffix, 1, w);

    // Single-element reconstruct at position 0 of suffix == digit value
    let old_suffix_take1 = old_suffix.take(1);
    let new_suffix_take1 = new_suffix.take(1);

    assert(old_suffix_take1[0] == old_digits[i as int]);
    assert(new_suffix_take1[0] == new_digits[i as int]);

    // Reconstruct of a single element: d + pw * reconstruct([]) = d + pw * 0 = d
    assert(reconstruct_radix_2w(old_suffix_take1, w)
        == (old_digits[i as int] as int) + pw * reconstruct_radix_2w(old_suffix_take1.skip(1), w)) by {
        assert(old_suffix_take1.len() == 1);
    }
    assert(reconstruct_radix_2w(old_suffix_take1.skip(1), w) == 0) by {
        assert(old_suffix_take1.skip(1).len() == 0);
    }
    assert(reconstruct_radix_2w(old_suffix_take1, w) == old_digits[i as int] as int) by {
        lemma_mul_basics(pw);
    }

    assert(reconstruct_radix_2w(new_suffix_take1, w)
        == (new_digits[i as int] as int) + pw * reconstruct_radix_2w(new_suffix_take1.skip(1), w)) by {
        assert(new_suffix_take1.len() == 1);
    }
    assert(reconstruct_radix_2w(new_suffix_take1.skip(1), w) == 0) by {
        assert(new_suffix_take1.skip(1).len() == 0);
    }
    assert(reconstruct_radix_2w(new_suffix_take1, w) == new_digits[i as int] as int) by {
        lemma_mul_basics(pw);
    }

    // Step 4: Work on tail of suffix (from position 1 onward = from i+1 onward)
    let old_tail = old_suffix.skip(1);
    let new_tail = new_digits.skip((i + 1) as int);

    assert(old_tail =~= old_digits.skip((i + 1) as int));
    assert(new_tail =~= new_digits.skip((i + 1) as int));
    assert(old_suffix.skip(1) =~= old_tail);
    assert(new_suffix.skip(1) =~= new_tail);

    // Step 5: Split the tails at position 1 to isolate digit i+1
    lemma_reconstruct_radix_2w_split(old_tail, 1, w);
    lemma_reconstruct_radix_2w_split(new_tail, 1, w);

    let old_tail_take1 = old_tail.take(1);
    let new_tail_take1 = new_tail.take(1);

    assert(old_tail_take1[0] == old_digits[(i + 1) as int]);
    assert(new_tail_take1[0] == new_digits[(i + 1) as int]);

    // Reconstruct of single element at i+1
    assert(reconstruct_radix_2w(old_tail_take1, w) == old_digits[(i + 1) as int] as int) by {
        assert(old_tail_take1.len() == 1);
        assert(reconstruct_radix_2w(old_tail_take1.skip(1), w) == 0) by {
            assert(old_tail_take1.skip(1).len() == 0);
        }
        lemma_mul_basics(pw);
    }
    assert(reconstruct_radix_2w(new_tail_take1, w) == new_digits[(i + 1) as int] as int) by {
        assert(new_tail_take1.len() == 1);
        assert(reconstruct_radix_2w(new_tail_take1.skip(1), w) == 0) by {
            assert(new_tail_take1.skip(1).len() == 0);
        }
        lemma_mul_basics(pw);
    }

    // Step 6: Show tails beyond i+1 are equal
    let old_beyond = old_tail.skip(1);
    let new_beyond = new_tail.skip(1);

    assert(old_beyond =~= old_digits.skip((i + 2) as int));
    assert(new_beyond =~= new_digits.skip((i + 2) as int));

    assert(old_beyond =~= new_beyond) by {
        assert forall|j: int| 0 <= j < old_beyond.len() implies old_beyond[j] == new_beyond[j] by {
            assert(old_beyond[j] == old_digits[(i + 2 + j) as int]);
            assert(new_beyond[j] == new_digits[(i + 2 + j) as int]);
            assert(old_digits[(i + 2 + j) as int] == new_digits[(i + 2 + j) as int]);
        }
        assert(old_beyond =~= new_beyond);
    }

    assert(reconstruct_radix_2w(old_beyond, w) == reconstruct_radix_2w(new_beyond, w));

    // Step 7: Algebraic cancellation at positions i and i+1
    // new_di + pw * new_di1 == old_di + pw * old_di1
    // new_di = old_di - carry * pw
    // new_di1 = old_di1 + carry
    // new_di + pw * new_di1
    //   = (old_di - carry * pw) + pw * (old_di1 + carry)
    //   = old_di - carry * pw + pw * old_di1 + pw * carry
    //   = old_di + pw * old_di1
    let old_di = old_digits[i as int] as int;
    let new_di = new_digits[i as int] as int;
    let old_di1 = old_digits[(i + 1) as int] as int;
    let new_di1 = new_digits[(i + 1) as int] as int;

    assert(new_di == old_di - carry * pw);
    assert(new_di1 == old_di1 + carry);

    assert(new_di + pw * new_di1 == old_di + pw * old_di1) by {
        // new_di + pw * new_di1
        // = (old_di - carry * pw) + pw * (old_di1 + carry)
        // = old_di - carry * pw + pw * old_di1 + pw * carry
        lemma_mul_is_distributive_add(pw, old_di1, carry);
        // pw * (old_di1 + carry) = pw * old_di1 + pw * carry
        // carry * pw = pw * carry  (commutativity)
        lemma_mul_is_commutative(carry, pw);
        // So: old_di - pw * carry + pw * old_di1 + pw * carry = old_di + pw * old_di1
    }

    // Now combine everything:
    // reconstruct(new) = reconstruct(new_prefix) + pow2(w*i) * (new_di + pw * (new_di1 + pw * reconstruct(new_beyond)))
    // == reconstruct(old_prefix) + pow2(w*i) * (old_di + pw * (old_di1 + pw * reconstruct(old_beyond)))
    // == reconstruct(old)

    // The split lemmas tell us:
    // reconstruct(old) = reconstruct(old_prefix) + pow2(w*i) * reconstruct(old_suffix)
    // reconstruct(old_suffix) = reconstruct([old_di]) + pow2(w*1) * reconstruct(old_tail)
    //                        = old_di + pw * reconstruct(old_tail)
    // reconstruct(old_tail) = old_di1 + pw * reconstruct(old_beyond)

    // Similarly for new.
    // Since new_di + pw * new_di1 = old_di + pw * old_di1,
    // we get reconstruct(old_suffix) == reconstruct(new_suffix), hence equality.

    let pow_wi = pow2(w * i);

    // Expand old_tail reconstruction
    assert(reconstruct_radix_2w(old_tail, w)
        == old_di1 + pw * reconstruct_radix_2w(old_beyond, w)) by {
        // from split at position 1
        assert(reconstruct_radix_2w(old_tail_take1, w) == old_di1);
    }

    assert(reconstruct_radix_2w(new_tail, w)
        == new_di1 + pw * reconstruct_radix_2w(new_beyond, w)) by {
        assert(reconstruct_radix_2w(new_tail_take1, w) == new_di1);
    }

    // Since old_beyond =~= new_beyond, their reconstructions are equal
    assert(reconstruct_radix_2w(old_tail, w) == reconstruct_radix_2w(new_tail, w)) by {
        assert(reconstruct_radix_2w(old_beyond, w) == reconstruct_radix_2w(new_beyond, w));
        // new_di1 + pw * reconstruct(new_beyond) == old_di1 + pw * (reconstruct(old_beyond))
        // but we need new_di + pw*new_di1 == old_di + pw*old_di1
        // Actually need: new_di1 + pw * R == old_di1 + pw * R?  No, new_di1 != old_di1 in general.
        // We need to work at the suffix level.
        // old_tail recon = old_di1 + pw * R
        // new_tail recon = new_di1 + pw * R  where R = reconstruct(old_beyond)
        // These are NOT equal in general. The equality is at the suffix level combining di and di1.
    }

    // Let R_beyond = reconstruct_radix_2w(old_beyond, w) = reconstruct_radix_2w(new_beyond, w)
    let r_beyond = reconstruct_radix_2w(old_beyond, w);

    assert(reconstruct_radix_2w(old_tail, w) == old_di1 + pw * r_beyond);
    assert(reconstruct_radix_2w(new_tail, w) == new_di1 + pw * r_beyond);

    assert(reconstruct_radix_2w(old_suffix, w)
        == old_di + pw * reconstruct_radix_2w(old_tail, w));
    assert(reconstruct_radix_2w(new_suffix, w)
        == new_di + pw * reconstruct_radix_2w(new_tail, w));

    assert(reconstruct_radix_2w(old_suffix, w)
        == old_di + pw * (old_di1 + pw * r_beyond));
    assert(reconstruct_radix_2w(new_suffix, w)
        == new_di + pw * (new_di1 + pw * r_beyond));

    // Now show old_di + pw*(old_di1 + pw*R) == new_di + pw*(new_di1 + pw*R)
    // LHS = old_di + pw*old_di1 + pw*pw*R
    // RHS = new_di + pw*new_di1 + pw*pw*R
    // Equal iff old_di + pw*old_di1 == new_di + pw*new_di1  (which we proved above)
    assert(reconstruct_radix_2w(old_suffix, w) == reconstruct_radix_2w(new_suffix, w)) by {
        lemma_mul_is_distributive_add(pw, old_di1, pw * r_beyond);
        lemma_mul_is_distributive_add(pw, new_di1, pw * r_beyond);
        // old_di + pw*old_di1 + pw*(pw*R) == new_di + pw*new_di1 + pw*(pw*R)
        // follows from new_di + pw*new_di1 == old_di + pw*old_di1
    }

    // Finally, the full reconstructions are equal
    assert(reconstruct_radix_2w(new_digits, w) == reconstruct_radix_2w(old_digits, w)) by {
        // Both equal reconstruct(prefix) + pow2(w*i) * reconstruct(suffix)
        // and the suffix reconstructions are equal
    }
