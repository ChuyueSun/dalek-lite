    // Strategy: split reconstruction at position i, then at i+1, and show the
    // contribution changes cancel algebraically.
    let n = old_digits.len();

    // Split both reconstructions at position i
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    lemma_reconstruct_radix_2w_split(new_digits, i, w);

    // old: rec(old) = rec(old.take(i)) + pow2(w*i) * rec(old.skip(i))
    // new: rec(new) = rec(new.take(i)) + pow2(w*i) * rec(new.skip(i))

    // The prefixes are identical (all j < i are unchanged)
    assert(old_digits.take(i as int) =~= new_digits.take(i as int)) by {
        assert forall|j: int| 0 <= j < i ==> old_digits.take(i as int)[j] == new_digits.take(i as int)[j] by {
            assert(old_digits[j] == new_digits[j]);
        }
    }

    // Now split the suffixes (skip(i)) at position 1, to isolate digit i
    let old_skip_i = old_digits.skip(i as int);
    let new_skip_i = new_digits.skip(i as int);

    assert(old_skip_i.len() == n - i);
    assert(new_skip_i.len() == n - i);
    assert(1 <= old_skip_i.len());

    lemma_reconstruct_radix_2w_split(old_skip_i, 1, w);
    lemma_reconstruct_radix_2w_split(new_skip_i, 1, w);

    // old_skip_i.take(1) = [old_digits[i]], new_skip_i.take(1) = [new_digits[i]]
    assert(old_skip_i[0] == old_digits[i as int]);
    assert(new_skip_i[0] == new_digits[i as int]);

    // reconstruct_radix_2w of a single element [x] = x + pow2(w) * 0 = x
    // old_skip_i.take(1) reconstructs to old_digits[i]
    // new_skip_i.take(1) reconstructs to new_digits[i]
    // (Verus should handle these via definition unrolling, but we can assert)

    // The tails old_skip_i.skip(1) and new_skip_i.skip(1) split further at position 1
    // to isolate digit i+1
    let old_skip_i1 = old_skip_i.skip(1);
    let new_skip_i1 = new_skip_i.skip(1);

    assert(old_skip_i1.len() == n - i - 1);
    assert(new_skip_i1.len() == n - i - 1);
    assert(1 <= old_skip_i1.len());

    lemma_reconstruct_radix_2w_split(old_skip_i1, 1, w);
    lemma_reconstruct_radix_2w_split(new_skip_i1, 1, w);

    assert(old_skip_i1[0] == old_digits[(i + 1) as int]);
    assert(new_skip_i1[0] == new_digits[(i + 1) as int]);

    // The tails beyond i+1 are identical
    let old_tail = old_skip_i1.skip(1);
    let new_tail = new_skip_i1.skip(1);

    assert(old_tail =~= new_tail) by {
        assert forall|j: int| 0 <= j < old_tail.len() ==> old_tail[j] == new_tail[j] by {
            // old_tail[j] = old_digits[i + 2 + j], new_tail[j] = new_digits[i + 2 + j]
            assert(old_tail[j] == old_digits[(i + 2 + j) as int]);
            assert(new_tail[j] == new_digits[(i + 2 + j) as int]);
            // i + 2 + j != i and != i+1, so they are equal
            assert(old_digits[(i + 2 + j) as int] == new_digits[(i + 2 + j) as int]);
        }
    }

    // Now reason about the algebraic cancellation.
    // Let:
    //   P = rec(old.take(i)) = rec(new.take(i))
    //   A = rec(old_skip_i.take(1)) = old_digits[i]
    //   A' = rec(new_skip_i.take(1)) = new_digits[i] = old_digits[i] - carry * pow2(w)
    //   B = rec(old_skip_i1.take(1)) = old_digits[i+1]
    //   B' = rec(new_skip_i1.take(1)) = new_digits[i+1] = old_digits[i+1] + carry
    //   T = rec(old_tail) = rec(new_tail)
    //
    // rec(old_skip_i1) = B + pow2(w*1) * (rec(old_tail))
    // rec(new_skip_i1) = B' + pow2(w*1) * (rec(new_tail))
    //
    // B' - B = carry
    // A' - A = -carry * pow2(w)
    //
    // rec(old) = P + pow2(w*i) * (A + pow2(w) * rec(old_skip_i1))
    // rec(new) = P + pow2(w*i) * (A' + pow2(w) * rec(new_skip_i1))
    //
    // Difference = pow2(w*i) * ((A' - A) + pow2(w) * (rec(new_skip_i1) - rec(old_skip_i1)))
    //            = pow2(w*i) * (-carry * pow2(w) + pow2(w) * carry)
    //            = 0

    // Concretize:
    let wi = w * i;
    let p2wi = pow2(wi);
    let p2w = pow2(w);

    // pow2(w * 1) == pow2(w)
    assert(pow2(w * 1) == pow2(w)) by {
        lemma_mul_basics(w as int);
    }

    // pow2(w) * pow2(w * i) == pow2(w * (i + 1))
    assert(p2w * p2wi == pow2(w * (i + 1))) by {
        lemma_pow2_adds(w, wi);
        assert(w + w * i == w * (i + 1)) by {
            lemma_mul_is_distributive_add(w as int, 1, i as int);
            lemma_mul_basics(w as int);
        }
    }

    // Expand rec(old_skip_i1) and rec(new_skip_i1) using split at 1
    // (already called lemma_reconstruct_radix_2w_split above)
    // rec(old_skip_i1) = old_digits[i+1] + pow2(w*1) * rec(old_tail)
    //                  = old_digits[i+1] + pow2(w) * rec(old_tail)
    // rec(new_skip_i1) = new_digits[i+1] + pow2(w*1) * rec(new_tail)
    //                  = new_digits[i+1] + pow2(w) * rec(old_tail)  [tails equal]

    // rec(new_skip_i1) - rec(old_skip_i1) = new_digits[i+1] - old_digits[i+1] = carry
    assert(reconstruct_radix_2w(new_skip_i1, w) - reconstruct_radix_2w(old_skip_i1, w) == carry) by {
        // Both are: digit[i+1] + pow2(w) * rec(tail)
        // The tails are equal, and new_digits[i+1] = old_digits[i+1] + carry
        assert(reconstruct_radix_2w(old_skip_i1, w) ==
            old_digits[(i + 1) as int] as int + pow2(w * 1) * reconstruct_radix_2w(old_tail, w));
        assert(reconstruct_radix_2w(new_skip_i1, w) ==
            new_digits[(i + 1) as int] as int + pow2(w * 1) * reconstruct_radix_2w(new_tail, w));
        assert(reconstruct_radix_2w(old_tail, w) == reconstruct_radix_2w(new_tail, w));
        assert(new_digits[(i + 1) as int] as int == old_digits[(i + 1) as int] as int + carry);
    }

    // Expand rec(old_skip_i) and rec(new_skip_i) using split at 1
    assert(reconstruct_radix_2w(old_skip_i, w) ==
        old_digits[i as int] as int + pow2(w * 1) * reconstruct_radix_2w(old_skip_i1, w));
    assert(reconstruct_radix_2w(new_skip_i, w) ==
        new_digits[i as int] as int + pow2(w * 1) * reconstruct_radix_2w(new_skip_i1, w));

    // Now show the full reconstructions are equal
    // rec(new) = P + pow2(w*i) * rec(new_skip_i)
    //          = P + pow2(w*i) * (new_digits[i] + pow2(w) * rec(new_skip_i1))
    //          = P + pow2(w*i) * ((old_digits[i] - carry*pow2(w)) + pow2(w) * (rec(old_skip_i1) + carry))
    //          = P + pow2(w*i) * (old_digits[i] + pow2(w) * rec(old_skip_i1))  [cancellation]
    //          = P + pow2(w*i) * rec(old_skip_i)
    //          = rec(old)

    assert(new_digits[i as int] as int == old_digits[i as int] as int - carry * (pow2(w) as int));
    assert(pow2(w * 1) == pow2(w));

    // The net change in rec(new_skip_i) vs rec(old_skip_i):
    // delta = (new_digits[i] - old_digits[i]) + pow2(w) * (rec(new_skip_i1) - rec(old_skip_i1))
    //       = -carry * pow2(w) + pow2(w) * carry = 0
    assert(reconstruct_radix_2w(new_skip_i, w) == reconstruct_radix_2w(old_skip_i, w)) by {
        let r_old_1 = reconstruct_radix_2w(old_skip_i1, w);
        let r_new_1 = reconstruct_radix_2w(new_skip_i1, w);
        assert(r_new_1 == r_old_1 + carry);
        let d_old = old_digits[i as int] as int;
        let d_new = new_digits[i as int] as int;
        assert(d_new == d_old - carry * (pow2(w) as int));
        // rec(new_skip_i) = d_new + pow2(w) * r_new_1
        //                 = (d_old - carry * pow2(w)) + pow2(w) * (r_old_1 + carry)
        //                 = d_old - carry * pow2(w) + pow2(w) * r_old_1 + pow2(w) * carry
        //                 = d_old + pow2(w) * r_old_1  [the carry*pow2(w) terms cancel]
        //                 = rec(old_skip_i)
        assert(reconstruct_radix_2w(new_skip_i, w) ==
            d_new + (pow2(w) as int) * r_new_1) by {
            assert(pow2(w * 1) == pow2(w));
        }
        assert(reconstruct_radix_2w(old_skip_i, w) ==
            d_old + (pow2(w) as int) * r_old_1) by {
            assert(pow2(w * 1) == pow2(w));
        }
        assert(d_new + (pow2(w) as int) * r_new_1
            == d_old + (pow2(w) as int) * r_old_1) by {
            lemma_mul_is_distributive_add(pow2(w) as int, r_old_1, carry);
            lemma_mul_is_commutative(carry, pow2(w) as int);
        }
    }
