{
    let n = old_digits.len();
    let pw = pow2(w) as int;

    // Step 1: Split both reconstructions at position i
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    lemma_reconstruct_radix_2w_split(new_digits, i, w);

    // Step 2: Show prefixes are equal (all digits before i are unchanged)
    assert(old_digits.take(i as int) =~= new_digits.take(i as int)) by {
        assert forall|j: int| 0 <= j < i implies old_digits[j] == new_digits[j] by {
            assert(0 <= j < old_digits.len() as int && j != i as int && j != (i + 1) as int);
        }
    };

    // Step 3: Focus on the suffixes starting at position i
    let old_suffix = old_digits.skip(i as int);
    let new_suffix = new_digits.skip(i as int);

    // Step 4: Split the suffixes at position 1 to isolate digit i
    lemma_reconstruct_radix_2w_split(old_suffix, 1, w);
    lemma_reconstruct_radix_2w_split(new_suffix, 1, w);

    // old_suffix[0] == old_digits[i], new_suffix[0] == new_digits[i]
    assert(old_suffix[0] == old_digits[i as int]);
    assert(new_suffix[0] == new_digits[i as int]);

    // reconstruct of a single-element prefix
    assert(reconstruct_radix_2w(old_suffix.take(1), w) == old_digits[i as int] as int) by {
        let s = old_suffix.take(1);
        assert(s.len() == 1);
        assert(s[0] == old_digits[i as int]);
        assert(s.skip(1).len() == 0);
        assert(reconstruct_radix_2w(s.skip(1), w) == 0);
        assert(reconstruct_radix_2w(s, w) == s[0] as int + pw * 0);
        lemma_mul_basics(pw);
    };
    assert(reconstruct_radix_2w(new_suffix.take(1), w) == new_digits[i as int] as int) by {
        let s = new_suffix.take(1);
        assert(s.len() == 1);
        assert(s[0] == new_digits[i as int]);
        assert(s.skip(1).len() == 0);
        assert(reconstruct_radix_2w(s.skip(1), w) == 0);
        assert(reconstruct_radix_2w(s, w) == s[0] as int + pw * 0);
        lemma_mul_basics(pw);
    };

    // Step 5: Look at the tails after position i: old_suffix.skip(1) and new_suffix.skip(1)
    let old_tail1 = old_suffix.skip(1);
    let new_tail1 = new_suffix.skip(1);
    // These are old_digits.skip(i+1) and new_digits.skip(i+1)
    assert(old_tail1 =~= old_digits.skip((i + 1) as int));
    assert(new_tail1 =~= new_digits.skip((i + 1) as int));

    // Step 6: Split the tail1 sequences at position 1 to isolate digit i+1
    lemma_reconstruct_radix_2w_split(old_tail1, 1, w);
    lemma_reconstruct_radix_2w_split(new_tail1, 1, w);

    assert(old_tail1[0] == old_digits[(i + 1) as int]);
    assert(new_tail1[0] == new_digits[(i + 1) as int]);

    assert(reconstruct_radix_2w(old_tail1.take(1), w) == old_digits[(i + 1) as int] as int) by {
        let s = old_tail1.take(1);
        assert(s.len() == 1);
        assert(s[0] == old_digits[(i + 1) as int]);
        assert(s.skip(1).len() == 0);
        assert(reconstruct_radix_2w(s.skip(1), w) == 0);
        assert(reconstruct_radix_2w(s, w) == s[0] as int + pw * 0);
        lemma_mul_basics(pw);
    };
    assert(reconstruct_radix_2w(new_tail1.take(1), w) == new_digits[(i + 1) as int] as int) by {
        let s = new_tail1.take(1);
        assert(s.len() == 1);
        assert(s[0] == new_digits[(i + 1) as int]);
        assert(s.skip(1).len() == 0);
        assert(reconstruct_radix_2w(s.skip(1), w) == 0);
        assert(reconstruct_radix_2w(s, w) == s[0] as int + pw * 0);
        lemma_mul_basics(pw);
    };

    // Step 7: Show tails beyond i+1 are equal
    let old_tail2 = old_tail1.skip(1);
    let new_tail2 = new_tail1.skip(1);
    assert(old_tail2 =~= old_digits.skip((i + 2) as int));
    assert(new_tail2 =~= new_digits.skip((i + 2) as int));

    assert(old_tail2 =~= new_tail2) by {
        assert forall|j: int| 0 <= j < old_tail2.len() implies old_tail2[j] == new_tail2[j] by {
            // old_tail2[j] == old_digits[i + 2 + j], new_tail2[j] == new_digits[i + 2 + j]
            let k = i + 2 + j;
            assert(old_tail2[j] == old_digits[k as int]);
            assert(new_tail2[j] == new_digits[k as int]);
            assert(0 <= k < old_digits.len() as int && k != i as int && k != (i + 1) as int);
        }
    };

    // Step 8: Now expand the reconstruct expressions and do algebraic cancellation
    // reconstruct(old_suffix, w) == old_digits[i] + pw * (old_digits[i+1] + pw * reconstruct(old_tail2))
    // reconstruct(new_suffix, w) == new_digits[i] + pw * (new_digits[i+1] + pw * reconstruct(new_tail2))
    // Since old_tail2 == new_tail2, reconstruct tails are equal.
    // new_digits[i] + pw * new_digits[i+1]
    //   == (old_digits[i] - carry * pw) + pw * (old_digits[i+1] + carry)
    //   == old_digits[i] - carry*pw + pw*old_digits[i+1] + pw*carry
    //   == old_digits[i] + pw*old_digits[i+1]
    // So the suffixes reconstruct to the same value.

    let rec_tail2 = reconstruct_radix_2w(old_tail2, w);

    // Expand reconstruct(old_tail1, w) using split at 1:
    // = reconstruct(old_tail1.take(1)) + pow2(w*1) * reconstruct(old_tail1.skip(1))
    // = old_digits[i+1] + pw * rec_tail2
    assert(pow2(w * 1) == pw) by {
        lemma_mul_basics(w as int);
    };
    assert(reconstruct_radix_2w(old_tail1, w) == old_digits[(i + 1) as int] as int + pw * rec_tail2);
    assert(reconstruct_radix_2w(new_tail1, w) == new_digits[(i + 1) as int] as int + pw * rec_tail2);

    // Expand reconstruct(old_suffix, w) using split at 1:
    // = old_digits[i] + pow2(w*1) * reconstruct(old_tail1)
    assert(reconstruct_radix_2w(old_suffix, w)
        == old_digits[i as int] as int + pw * reconstruct_radix_2w(old_tail1, w));
    assert(reconstruct_radix_2w(new_suffix, w)
        == new_digits[i as int] as int + pw * reconstruct_radix_2w(new_tail1, w));

    // Step 9: Algebraic cancellation
    // new_digits[i] + pw * new_digits[i+1] == old_digits[i] + pw * old_digits[i+1]
    assert(new_digits[i as int] as int + pw * new_digits[(i + 1) as int] as int
        == old_digits[i as int] as int + pw * old_digits[(i + 1) as int] as int) by {
        // new_digits[i] = old_digits[i] - carry * pw
        // new_digits[i+1] = old_digits[i+1] + carry
        // pw * new_digits[i+1] = pw * (old_digits[i+1] + carry) = pw*old_digits[i+1] + pw*carry
        lemma_mul_is_distributive_add(pw, old_digits[(i + 1) as int] as int, carry);
        // carry * pw == pw * carry
        lemma_mul_is_commutative(carry, pw);
    };

    // Now show new_suffix and old_suffix reconstruct to the same value
    assert(reconstruct_radix_2w(new_suffix, w) == reconstruct_radix_2w(old_suffix, w)) by {
        // new_suffix recon = new_di + pw*(new_di1 + pw*rec_tail2)
        //                  = new_di + pw*new_di1 + pw*pw*rec_tail2
        // old_suffix recon = old_di + pw*(old_di1 + pw*rec_tail2)
        //                  = old_di + pw*old_di1 + pw*pw*rec_tail2
        // These are equal since new_di + pw*new_di1 == old_di + pw*old_di1
        lemma_mul_is_distributive_add(pw, old_digits[(i + 1) as int] as int, pw * rec_tail2);
        lemma_mul_is_distributive_add(pw, new_digits[(i + 1) as int] as int, pw * rec_tail2);
    };

    // Step 10: The full reconstruction equality follows from equal prefixes and equal suffixes
    assert(pow2(w * i) == pow2(w * i));  // trivially
    // reconstruct(old_digits) = reconstruct(prefix) + pow2(w*i) * reconstruct(old_suffix)
    // reconstruct(new_digits) = reconstruct(prefix) + pow2(w*i) * reconstruct(new_suffix)
    // Since old_suffix recon == new_suffix recon and prefix recon is shared, we're done.
}
