    // Split old_digits reconstruction at position i
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    // Gives: reconstruct(old_digits) == reconstruct(old_digits.take(i)) + pow2(w*i) * reconstruct(old_digits.skip(i))

    // Split old_digits.skip(i) at position 1 to isolate digit i
    lemma_reconstruct_radix_2w_split(old_digits.skip(i as int), 1, w);
    // Gives: reconstruct(old_digits.skip(i)) == reconstruct(old_digits.skip(i).take(1)) + pow2(w) * reconstruct(old_digits.skip(i).skip(1))

    // Split old_digits.skip(i+1) at position 1 to isolate digit i+1
    lemma_reconstruct_radix_2w_split(old_digits.skip((i + 1) as int), 1, w);

    // Split new_digits reconstruction at position i
    lemma_reconstruct_radix_2w_split(new_digits, i, w);

    // Split new_digits.skip(i) at position 1 to isolate digit i
    lemma_reconstruct_radix_2w_split(new_digits.skip(i as int), 1, w);

    // Split new_digits.skip(i+1) at position 1 to isolate digit i+1
    lemma_reconstruct_radix_2w_split(new_digits.skip((i + 1) as int), 1, w);

    // The prefixes up to i are identical (all those digits are unchanged)
    assert(old_digits.take(i as int) =~= new_digits.take(i as int)) by {
        assert forall|j: int| 0 <= j < i ==> old_digits.take(i as int)[j] == new_digits.take(i as int)[j] by {
            // j < i, so j != i and j != i+1
            assert(j < old_digits.len() as int);
            assert(old_digits[j] == new_digits[j]);
        }
    };

    // The suffixes beyond i+1 are identical (digits j > i+1 are unchanged)
    assert(old_digits.skip((i + 1) as int).skip(1) =~= new_digits.skip((i + 1) as int).skip(1)) by {
        assert forall|j: int| 0 <= j < old_digits.skip((i + 1) as int).skip(1).len()
            ==> old_digits.skip((i + 1) as int).skip(1)[j] == new_digits.skip((i + 1) as int).skip(1)[j] by {
            let orig = j + (i as int) + 2;
            assert(0 <= orig < old_digits.len() && orig != i && orig != i + 1);
            assert(old_digits[orig] == new_digits[orig]);
        }
    };

    // Note: old_digits.skip(i).skip(1) == old_digits.skip(i+1)
    assert(old_digits.skip(i as int).skip(1) =~= old_digits.skip((i + 1) as int));
    assert(new_digits.skip(i as int).skip(1) =~= new_digits.skip((i + 1) as int));

    // The single-element reconstruction of a sequence s with s[0] == d is just d as int
    // reconstruct_radix_2w([d], w) == d * pow2(0) == d
    // We need: old digit i contribution at offset i: old_digits[i] * pow2(w*i)
    // and new digit i contribution: new_digits[i] * pow2(w*i)
    // Their difference is: (new_digits[i] - old_digits[i]) * pow2(w*i)
    //   = -carry * pow2(w) * pow2(w*i) = -carry * pow2(w + w*i) = -carry * pow2(w*(i+1))
    // old digit i+1 contribution at offset i+1: old_digits[i+1] * pow2(w*(i+1))
    // new digit i+1 contribution: new_digits[i+1] * pow2(w*(i+1))
    // Their difference: carry * pow2(w*(i+1))
    // Total difference: 0 -- proves the lemma.

    // Key: pow2(w) * pow2(w*i) == pow2(w + w*i) == pow2(w*(i+1))
    lemma_pow2_adds(w, w * i);
    assert(w + w * i == w * (i + 1)) by {
        lemma_mul_is_distributive_add(w, 1nat, i);
    };

    // The carry cancels algebraically between positions i and i+1
    // new_digits[i] * pow2(w*i) + new_digits[i+1] * pow2(w*(i+1))
    // = (old_digits[i] - carry*pow2(w)) * pow2(w*i) + (old_digits[i+1] + carry) * pow2(w*(i+1))
    // = old_digits[i]*pow2(w*i) - carry*pow2(w)*pow2(w*i) + old_digits[i+1]*pow2(w*(i+1)) + carry*pow2(w*(i+1))
    // = old_digits[i]*pow2(w*i) + old_digits[i+1]*pow2(w*(i+1))   [since pow2(w)*pow2(w*i) == pow2(w*(i+1))]
    assert((new_digits[i as int] as int) * (pow2(w * i) as int)
        + (new_digits[(i + 1) as int] as int) * (pow2(w * (i + 1)) as int)
        == (old_digits[i as int] as int) * (pow2(w * i) as int)
        + (old_digits[(i + 1) as int] as int) * (pow2(w * (i + 1)) as int)) by {
        lemma_mul_is_distributive_add(pow2(w * i) as int, old_digits[i as int] as int, -(carry * (pow2(w) as int)));
        lemma_mul_is_distributive_add(pow2(w * (i + 1)) as int, old_digits[(i + 1) as int] as int, carry);
        assert(pow2(w) as int * pow2(w * i) as int == pow2(w * (i + 1)) as int) by {
            lemma_pow2_adds(w, w * i);
        };
        lemma_mul_is_associative(carry, pow2(w) as int, pow2(w * i) as int);
        lemma_mul_is_commutative(pow2(w) as int, pow2(w * i) as int);
    };
