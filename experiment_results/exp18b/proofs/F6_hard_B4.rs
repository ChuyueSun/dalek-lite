    let n = old_digits.len();
    let pw = pow2(w) as int;

    // Step 1: Split both reconstructions at position i
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    lemma_reconstruct_radix_2w_split(new_digits, i, w);
    // reconstruct(old) == reconstruct(old.take(i)) + pow2(w*i) * reconstruct(old.skip(i))
    // reconstruct(new) == reconstruct(new.take(i)) + pow2(w*i) * reconstruct(new.skip(i))

    // Step 2: Show prefixes are equal (digits before i are unchanged)
    let old_prefix = old_digits.take(i as int);
    let new_prefix = new_digits.take(i as int);
    assert(old_prefix =~= new_prefix) by {
        assert forall|j: int| 0 <= j < i implies old_prefix[j] == new_prefix[j] by {
            assert(old_digits[j] == new_digits[j]);
        }
    }

    // Step 3: Split suffixes at position 1 to isolate digit i
    let old_suffix = old_digits.skip(i as int);
    let new_suffix = new_digits.skip(i as int);

    lemma_reconstruct_radix_2w_split(old_suffix, 1, w);
    lemma_reconstruct_radix_2w_split(new_suffix, 1, w);
    // reconstruct(old_suffix) == reconstruct(old_suffix.take(1)) + pow2(w) * reconstruct(old_suffix.skip(1))
    // reconstruct(new_suffix) == reconstruct(new_suffix.take(1)) + pow2(w) * reconstruct(new_suffix.skip(1))

    // Step 4: Single-element reconstruct == digit value
    let old_suffix_take1 = old_suffix.take(1);
    let new_suffix_take1 = new_suffix.take(1);
    assert(old_suffix_take1.len() == 1);
    assert(new_suffix_take1.len() == 1);
    assert(old_suffix_take1[0] == old_digits[i as int]);
    assert(new_suffix_take1[0] == new_digits[i as int]);

    // Unroll single-element reconstruct
    let old_take1_skip1 = old_suffix_take1.skip(1);
    let new_take1_skip1 = new_suffix_take1.skip(1);
    assert(old_take1_skip1.len() == 0);
    assert(new_take1_skip1.len() == 0);
    assert(reconstruct_radix_2w(old_take1_skip1, w) == 0);
    assert(reconstruct_radix_2w(new_take1_skip1, w) == 0);
    assert(reconstruct_radix_2w(old_suffix_take1, w) == old_digits[i as int] as int + pw * 0);
    assert(reconstruct_radix_2w(new_suffix_take1, w) == new_digits[i as int] as int + pw * 0);
    assert(reconstruct_radix_2w(old_suffix_take1, w) == old_digits[i as int] as int) by {
        lemma_mul_basics(pw);
    }
    assert(reconstruct_radix_2w(new_suffix_take1, w) == new_digits[i as int] as int) by {
        lemma_mul_basics(pw);
    }

    // Step 5: Split suffixes again at position i+1 to get the tail beyond i+1
    let old_suffix2 = old_suffix.skip(1);
    let new_suffix2 = new_suffix.skip(1);
    // old_suffix2[0] == old_digits[i+1], new_suffix2[0] == new_digits[i+1]

    lemma_reconstruct_radix_2w_split(old_suffix2, 1, w);
    lemma_reconstruct_radix_2w_split(new_suffix2, 1, w);

    let old_suffix2_take1 = old_suffix2.take(1);
    let new_suffix2_take1 = new_suffix2.take(1);
    assert(old_suffix2_take1[0] == old_digits[(i + 1) as int]);
    assert(new_suffix2_take1[0] == new_digits[(i + 1) as int]);

    let old_take2_skip1 = old_suffix2_take1.skip(1);
    let new_take2_skip1 = new_suffix2_take1.skip(1);
    assert(old_take2_skip1.len() == 0);
    assert(new_take2_skip1.len() == 0);
    assert(reconstruct_radix_2w(old_take2_skip1, w) == 0);
    assert(reconstruct_radix_2w(new_take2_skip1, w) == 0);
    assert(reconstruct_radix_2w(old_suffix2_take1, w) == old_digits[(i + 1) as int] as int) by {
        lemma_mul_basics(pw);
    }
    assert(reconstruct_radix_2w(new_suffix2_take1, w) == new_digits[(i + 1) as int] as int) by {
        lemma_mul_basics(pw);
    }

    // Step 6: Show tails beyond i+1 are equal
    let old_tail = old_suffix2.skip(1);
    let new_tail = new_suffix2.skip(1);
    assert(old_tail =~= new_tail) by {
        assert forall|j: int| 0 <= j < old_tail.len() implies old_tail[j] == new_tail[j] by {
            let idx = i + 2 + j;
            assert(old_digits[idx as int] == new_digits[idx as int]);
        }
    }

    // Step 7: Algebraic cancellation
    // reconstruct(old_suffix) == old_di + pw * (old_di1 + pw * reconstruct(old_tail))
    // reconstruct(new_suffix) == new_di + pw * (new_di1 + pw * reconstruct(new_tail))
    // new_di + pw * new_di1 == old_di - carry*pw + pw*(old_di1 + carry)
    //                       == old_di + pw*old_di1 + (-carry*pw + pw*carry)
    //                       == old_di + pw*old_di1
    let old_di = old_digits[i as int] as int;
    let new_di = new_digits[i as int] as int;
    let old_di1 = old_digits[(i + 1) as int] as int;
    let new_di1 = new_digits[(i + 1) as int] as int;
    let tail_rec = reconstruct_radix_2w(old_tail, w);

    assert(new_di + pw * new_di1 == old_di + pw * old_di1) by {
        // new_di == old_di - carry * pw
        // new_di1 == old_di1 + carry
        // new_di + pw * new_di1
        //   == (old_di - carry*pw) + pw*(old_di1 + carry)
        //   == old_di - carry*pw + pw*old_di1 + pw*carry
        //   == old_di + pw*old_di1 + pw*carry - carry*pw
        //   == old_di + pw*old_di1
        lemma_mul_is_distributive_add(pw, old_di1, carry);
        lemma_mul_is_commutative(carry, pw);
    }

    // Now assemble the full equality
    // reconstruct(old_suffix) == old_di + pw * (old_di1 + pw * tail_rec)
    // reconstruct(new_suffix) == new_di + pw * (new_di1 + pw * tail_rec)
    // Since new_di + pw * new_di1 == old_di + pw * old_di1, the two are equal.
    assert(reconstruct_radix_2w(old_suffix2, w) == old_di1 + pw * tail_rec) by {
        assert(reconstruct_radix_2w(old_suffix2, w) ==
            reconstruct_radix_2w(old_suffix2_take1, w) + pow2(w * 1) * reconstruct_radix_2w(old_tail, w));
        assert(pow2(w * 1) == pw) by {
            assert(w * 1 == w) by { lemma_mul_basics(w as int); }
        }
    }
    assert(reconstruct_radix_2w(new_suffix2, w) == new_di1 + pw * tail_rec) by {
        assert(reconstruct_radix_2w(new_suffix2, w) ==
            reconstruct_radix_2w(new_suffix2_take1, w) + pow2(w * 1) * reconstruct_radix_2w(new_tail, w));
        assert(pow2(w * 1) == pw) by {
            assert(w * 1 == w) by { lemma_mul_basics(w as int); }
        }
        assert(reconstruct_radix_2w(new_tail, w) == tail_rec);
    }

    assert(reconstruct_radix_2w(old_suffix, w) == old_di + pw * (old_di1 + pw * tail_rec)) by {
        assert(reconstruct_radix_2w(old_suffix, w) ==
            reconstruct_radix_2w(old_suffix_take1, w) + pow2(w * 1) * reconstruct_radix_2w(old_suffix2, w));
        assert(pow2(w * 1) == pw) by {
            assert(w * 1 == w) by { lemma_mul_basics(w as int); }
        }
    }
    assert(reconstruct_radix_2w(new_suffix, w) == new_di + pw * (new_di1 + pw * tail_rec)) by {
        assert(reconstruct_radix_2w(new_suffix, w) ==
            reconstruct_radix_2w(new_suffix_take1, w) + pow2(w * 1) * reconstruct_radix_2w(new_suffix2, w));
        assert(pow2(w * 1) == pw) by {
            assert(w * 1 == w) by { lemma_mul_basics(w as int); }
        }
    }

    assert(old_di + pw * (old_di1 + pw * tail_rec) == new_di + pw * (new_di1 + pw * tail_rec)) by {
        lemma_mul_is_distributive_add(pw, old_di1, pw * tail_rec);
        lemma_mul_is_distributive_add(pw, new_di1, pw * tail_rec);
    }

    assert(reconstruct_radix_2w(new_suffix, w) == reconstruct_radix_2w(old_suffix, w));
