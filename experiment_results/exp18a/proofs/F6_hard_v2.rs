    let n = old_digits.len();

    // Split reconstruction of old_digits at position i: prefix [0..i] + suffix [i..]
    lemma_reconstruct_radix_2w_split(old_digits, i as nat, w);
    // old = reconstruct(old[0..i], w) + pow2(w*i) * reconstruct(old[i..], w)

    // Split the suffix old[i..] at position 1: element i + rest [i+1..]
    lemma_reconstruct_radix_2w_split(old_digits.skip(i as int), 1, w);
    // reconstruct(old[i..], w) = old[i] + pow2(w*1) * reconstruct(old[i+1..], w)

    // Split old[i+1..] at position 1: element i+1 + rest [i+2..]
    lemma_reconstruct_radix_2w_split(old_digits.skip((i + 1) as int), 1, w);
    // reconstruct(old[i+1..], w) = old[i+1] + pow2(w) * reconstruct(old[i+2..], w)

    // Same splits for new_digits
    lemma_reconstruct_radix_2w_split(new_digits, i as nat, w);
    lemma_reconstruct_radix_2w_split(new_digits.skip(i as int), 1, w);
    lemma_reconstruct_radix_2w_split(new_digits.skip((i + 1) as int), 1, w);

    // The prefix [0..i] is unchanged between old and new
    assert(old_digits.take(i as int) =~= new_digits.take(i as int)) by {
        assert forall|j: int| 0 <= j < i ==> old_digits[j] == new_digits[j] by {
            assert(0 <= j < old_digits.len() as int);
            assert(j != i as int);
            assert(j != (i + 1) as int);
        }
    }

    // The suffix [i+2..] is unchanged between old and new
    assert(old_digits.skip((i + 1) as int).skip(1) =~= new_digits.skip((i + 1) as int).skip(1)) by {
        assert forall|j: int| 0 <= j < old_digits.skip((i + 1) as int).skip(1).len() ==>
            old_digits.skip((i + 1) as int).skip(1)[j] == new_digits.skip((i + 1) as int).skip(1)[j] by {
            let orig_j = j + i as int + 2;
            assert(orig_j != i as int);
            assert(orig_j != (i + 1) as int);
            assert(0 <= orig_j < old_digits.len() as int);
            assert(old_digits[orig_j] == new_digits[orig_j]);
        }
    }

    // The single-element sequences at positions i and i+1
    assert(old_digits.skip(i as int).take(1)[0] == old_digits[i as int]);
    assert(new_digits.skip(i as int).take(1)[0] == new_digits[i as int]);
    assert(old_digits.skip((i + 1) as int).take(1)[0] == old_digits[(i + 1) as int]);
    assert(new_digits.skip((i + 1) as int).take(1)[0] == new_digits[(i + 1) as int]);

    // pow2(w * 1) == pow2(w)
    assert(w * 1 == w) by {
        lemma_mul_basics(w as int);
    }

    // pow2(w * i + w) == pow2(w * i) * pow2(w)
    assert(pow2(w * i + w) == pow2(w * i as nat) * pow2(w)) by {
        lemma_pow2_adds(w * i as nat, w);
    }

    // pow2(w * (i + 1)) == pow2(w * i + w)
    assert(w * (i + 1) == w * i + w) by {
        lemma_mul_is_distributive_add(w as int, i as int, 1);
        lemma_mul_basics(w as int);
    }

    // The algebraic cancellation:
    // new[i] * pow2(w*i) + pow2(w*i) * pow2(w) * new[i+1]
    // = (old[i] - carry*pow2(w)) * pow2(w*i) + pow2(w*i)*pow2(w) * (old[i+1] + carry)
    // = old[i]*pow2(w*i) - carry*pow2(w)*pow2(w*i) + pow2(w*i)*pow2(w)*old[i+1] + carry*pow2(w*i)*pow2(w)
    // = old[i]*pow2(w*i) + pow2(w*i)*pow2(w)*old[i+1]
    // which equals the old contribution
    assert(
        new_digits[i as int] as int * pow2(w * i as nat) as int
            + pow2(w * i as nat) as int * pow2(w) as int * new_digits[(i + 1) as int] as int
        == old_digits[i as int] as int * pow2(w * i as nat) as int
            + pow2(w * i as nat) as int * pow2(w) as int * old_digits[(i + 1) as int] as int
    ) by {
        lemma_mul_is_distributive_add(pow2(w * i as nat) as int, old_digits[i as int] as int, -(carry * pow2(w) as int));
        lemma_mul_is_distributive_add(pow2(w * i as nat) as int * pow2(w) as int, old_digits[(i + 1) as int] as int, carry);
        lemma_mul_is_associative(pow2(w * i as nat) as int, pow2(w) as int, carry);
    }
