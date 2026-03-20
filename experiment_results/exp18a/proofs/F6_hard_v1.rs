    // We use lemma_reconstruct_radix_2w_split to split at position i, then at i+1.
    // This lets us isolate the two changed digits and show the carry cancels out.

    let n = old_digits.len();

    // Split both reconstructions at i
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    lemma_reconstruct_radix_2w_split(new_digits, i, w);
    // old: recon(old, w) == recon(old.take(i), w) + pow2(w*i) * recon(old.skip(i), w)
    // new: recon(new, w) == recon(new.take(i), w) + pow2(w*i) * recon(new.skip(i), w)

    // The prefixes up to i are the same (all digits before i are unchanged)
    assert(old_digits.take(i as int) =~= new_digits.take(i as int)) by {
        assert forall|j: int| 0 <= j < i implies old_digits.take(i as int)[j] == new_digits.take(i as int)[j] by {
            assert(old_digits[j] == new_digits[j]);
        }
    };

    // Now split the suffixes (skip(i)) at position 1 (i.e., split off digit i)
    let old_suf = old_digits.skip(i as int);
    let new_suf = new_digits.skip(i as int);

    lemma_reconstruct_radix_2w_split(old_suf, 1, w);
    lemma_reconstruct_radix_2w_split(new_suf, 1, w);
    // old_suf: recon(old_suf, w) == recon(old_suf.take(1), w) + pow2(w*1) * recon(old_suf.skip(1), w)
    // new_suf: recon(new_suf, w) == recon(new_suf.take(1), w) + pow2(w*1) * recon(new_suf.skip(1), w)

    // The take(1) reconstructions: just digit i
    assert(old_suf.take(1)[0] == old_digits[i as int]);
    assert(new_suf.take(1)[0] == new_digits[i as int]);
    assert(reconstruct_radix_2w(old_suf.take(1), w) == old_digits[i as int] as int + pow2(w) * 0) by {
        // old_suf.take(1) has length 1, so reconstruction = digit[0] + pow2(w) * recon(skip(1))
        // and skip(1) is empty so recon = 0
        lemma_reconstruct_radix_2w_split(old_suf.take(1), 1, w);
        assert(old_suf.take(1).skip(1).len() == 0);
        assert(reconstruct_radix_2w(old_suf.take(1).skip(1), w) == 0);
    };
    assert(reconstruct_radix_2w(new_suf.take(1), w) == new_digits[i as int] as int + pow2(w) * 0) by {
        lemma_reconstruct_radix_2w_split(new_suf.take(1), 1, w);
        assert(new_suf.take(1).skip(1).len() == 0);
        assert(reconstruct_radix_2w(new_suf.take(1).skip(1), w) == 0);
    };
    assert(reconstruct_radix_2w(old_suf.take(1), w) == old_digits[i as int] as int) by {
        lemma_mul_basics(pow2(w) as int);
    };
    assert(reconstruct_radix_2w(new_suf.take(1), w) == new_digits[i as int] as int) by {
        lemma_mul_basics(pow2(w) as int);
    };

    // The skipped suffixes: old_suf.skip(1) == old_digits.skip(i+1), similar for new
    assert(old_suf.skip(1) =~= old_digits.skip((i + 1) as int));
    assert(new_suf.skip(1) =~= new_digits.skip((i + 1) as int));

    // Split old_suf.skip(1) at position 1 (to isolate digit i+1)
    let old_tail = old_digits.skip((i + 1) as int);
    let new_tail = new_digits.skip((i + 1) as int);

    lemma_reconstruct_radix_2w_split(old_tail, 1, w);
    lemma_reconstruct_radix_2w_split(new_tail, 1, w);

    assert(old_tail.take(1)[0] == old_digits[(i + 1) as int]);
    assert(new_tail.take(1)[0] == new_digits[(i + 1) as int]);

    assert(reconstruct_radix_2w(old_tail.take(1), w) == old_digits[(i + 1) as int] as int) by {
        lemma_reconstruct_radix_2w_split(old_tail.take(1), 1, w);
        assert(old_tail.take(1).skip(1).len() == 0);
        assert(reconstruct_radix_2w(old_tail.take(1).skip(1), w) == 0);
        lemma_mul_basics(pow2(w) as int);
    };
    assert(reconstruct_radix_2w(new_tail.take(1), w) == new_digits[(i + 1) as int] as int) by {
        lemma_reconstruct_radix_2w_split(new_tail.take(1), 1, w);
        assert(new_tail.take(1).skip(1).len() == 0);
        assert(reconstruct_radix_2w(new_tail.take(1).skip(1), w) == 0);
        lemma_mul_basics(pow2(w) as int);
    };

    // The remaining tails (skip(i+2)) are identical
    let old_tail2 = old_digits.skip((i + 2) as int);
    let new_tail2 = new_digits.skip((i + 2) as int);

    assert(old_tail.skip(1) =~= old_tail2);
    assert(new_tail.skip(1) =~= new_tail2);
    assert(old_tail2 =~= new_tail2) by {
        assert forall|j: int| 0 <= j < old_tail2.len() implies old_tail2[j] == new_tail2[j] by {
            let k = i + 2 + j;
            assert(k != i as int && k != (i + 1) as int);
            assert(old_digits[k as int] == new_digits[k as int]);
        }
    };

    // Now put it all together: the carry cancels because
    // new_digits[i] - old_digits[i] = - carry * pow2(w)
    // new_digits[i+1] - old_digits[i+1] = carry
    // so the contribution at position i changes by -carry * pow2(w) * pow2(w*i)
    // and at position i+1 by +carry * pow2(w*(i+1))
    // these cancel because pow2(w*(i+1)) == pow2(w) * pow2(w*i)

    assert(pow2(w * (i + 1)) == pow2(w) * pow2(w * i)) by {
        assert(w * (i + 1) == w + w * i) by {
            lemma_mul_is_distributive_add(w as int, i as int, 1);
        };
        lemma_pow2_adds(w, w * i);
        lemma_mul_is_commutative(pow2(w) as int, pow2(w * i) as int);
    };

    // The two suffix reconstructions (from i) differ by:
    // recon(new_suf) - recon(old_suf)
    // = (new_digits[i] - old_digits[i]) + pow2(w) * (recon(new_tail) - recon(old_tail))
    // = (-carry * pow2(w)) + pow2(w) * (carry + 0)
    // = 0
    assert(reconstruct_radix_2w(old_suf, w) == reconstruct_radix_2w(new_suf, w)) by {
        // recon(old_suf) = old_digits[i] + pow2(w) * recon(old_tail)
        // recon(new_suf) = new_digits[i] + pow2(w) * recon(new_tail)
        // recon(old_tail) = old_digits[i+1] + pow2(w) * recon(old_tail2)
        // recon(new_tail) = new_digits[i+1] + pow2(w) * recon(new_tail2)
        // old_tail2 == new_tail2

        let r_old_tail2 = reconstruct_radix_2w(old_tail2, w);
        let r_new_tail2 = reconstruct_radix_2w(new_tail2, w);
        assert(r_old_tail2 == r_new_tail2) by {
            assert(old_tail2 =~= new_tail2);
        };

        let r_old_tail = reconstruct_radix_2w(old_tail, w);
        let r_new_tail = reconstruct_radix_2w(new_tail, w);
        assert(r_old_tail == old_digits[(i + 1) as int] as int + pow2(w) * r_old_tail2);
        assert(r_new_tail == new_digits[(i + 1) as int] as int + pow2(w) * r_new_tail2);
        assert(r_new_tail == r_old_tail + carry) by {
            assert(new_digits[(i + 1) as int] as int == old_digits[(i + 1) as int] as int + carry);
            lemma_mul_is_distributive_add(pow2(w) as int, r_old_tail2, 0);
        };

        let r_old_suf = reconstruct_radix_2w(old_suf, w);
        let r_new_suf = reconstruct_radix_2w(new_suf, w);
        assert(r_old_suf == old_digits[i as int] as int + pow2(w) * r_old_tail);
        assert(r_new_suf == new_digits[i as int] as int + pow2(w) * r_new_tail);
        assert(new_digits[i as int] as int == old_digits[i as int] as int - carry * (pow2(w) as int));
        assert(r_new_suf == r_old_suf) by {
            // r_new_suf = (old[i] - carry*pow2(w)) + pow2(w) * (r_old_tail + carry)
            //           = old[i] - carry*pow2(w) + pow2(w)*r_old_tail + pow2(w)*carry
            //           = old[i] + pow2(w)*r_old_tail
            //           = r_old_suf
            lemma_mul_is_distributive_add(pow2(w) as int, r_old_tail, carry);
            lemma_mul_is_commutative(pow2(w) as int, carry);
        };
    };
