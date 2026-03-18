    // Split both at position i
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    lemma_reconstruct_radix_2w_split(new_digits, i, w);

    // Prefixes are identical
    assert(old_digits.take(i as int) =~= new_digits.take(i as int));

    let old_suffix = old_digits.skip(i as int);
    let new_suffix = new_digits.skip(i as int);
    assert(old_suffix.len() >= 2);

    // Split suffixes to isolate positions i and i+1
    lemma_reconstruct_radix_2w_split(old_suffix, 1, w);
    lemma_reconstruct_radix_2w_split(new_suffix, 1, w);

    // Reconstruct of single-element prefix == digit value
    assert(reconstruct_radix_2w(old_suffix.take(1), w) == old_digits[i as int] as int) by {
        assert(old_suffix.take(1)[0] == old_digits[i as int]);
        assert(old_suffix.take(1).skip(1).len() == 0);
    }
    assert(reconstruct_radix_2w(new_suffix.take(1), w) == new_digits[i as int] as int) by {
        assert(new_suffix.take(1)[0] == new_digits[i as int]);
        assert(new_suffix.take(1).skip(1).len() == 0);
    }

    let old_rest = old_suffix.skip(1);
    let new_rest = new_suffix.skip(1);

    // Split rest to isolate position i+1
    lemma_reconstruct_radix_2w_split(old_rest, 1, w);
    lemma_reconstruct_radix_2w_split(new_rest, 1, w);

    assert(reconstruct_radix_2w(old_rest.take(1), w) == old_digits[(i + 1) as int] as int) by {
        assert(old_rest.take(1)[0] == old_digits[(i + 1) as int]);
        assert(old_rest.take(1).skip(1).len() == 0);
    }
    assert(reconstruct_radix_2w(new_rest.take(1), w) == new_digits[(i + 1) as int] as int) by {
        assert(new_rest.take(1)[0] == new_digits[(i + 1) as int]);
        assert(new_rest.take(1).skip(1).len() == 0);
    }

    // Tail after position i+1 is identical
    assert(old_rest.skip(1) =~= new_rest.skip(1));

    // Core algebraic identity: carry preserves d[i] + pw * d[i+1]
    let old_di = old_digits[i as int] as int;
    let old_di1 = old_digits[(i + 1) as int] as int;
    let new_di = new_digits[i as int] as int;
    let new_di1 = new_digits[(i + 1) as int] as int;
    let pw = pow2(w) as int;
    let tail_recon = reconstruct_radix_2w(old_rest.skip(1), w);

    assert(new_di + pw * new_di1 == old_di + pw * old_di1) by {
        lemma_mul_is_distributive_add(pw, old_di1, carry);
        lemma_mul_is_commutative(carry, pw);
    }

    assert(new_di + pw * (new_di1 + pw * tail_recon) == old_di + pw * (old_di1 + pw * tail_recon))
        by {
        lemma_mul_is_distributive_add(pw, new_di1, pw * tail_recon);
        lemma_mul_is_distributive_add(pw, old_di1, pw * tail_recon);
    }

    assert(w * 1 == w) by {
        lemma_mul_basics(w as int);
    }
