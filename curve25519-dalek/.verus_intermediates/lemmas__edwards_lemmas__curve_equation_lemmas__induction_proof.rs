pub proof fn axiom_edwards_scalar_mul_distributive(a: (nat, nat), b: (nat, nat), n: nat)
    ensures
        edwards_scalar_mul(edwards_add(a.0, a.1, b.0, b.1), n) == ({
            let na = edwards_scalar_mul(a, n);
            let nb = edwards_scalar_mul(b, n);
            edwards_add(na.0, na.1, nb.0, nb.1)
        }),
    decreases n,
{
    let sum_ab = edwards_add(a.0, a.1, b.0, b.1);

    if n == 0 {
        reveal_with_fuel(edwards_scalar_mul, 1);
        // LHS: (0, 1);  RHS: edwards_add(0, 1, 0, 1)
        lemma_edwards_add_identity_left(0, 1);
        // edwards_add(0, 1, 0, 1) == (0 % p(), 1 % p())
        assert(0nat % p() == 0nat) by {
            p_gt_2();
            lemma_small_mod(0nat, p());
        };
        assert(1nat % p() == 1nat) by {
            p_gt_2();
            lemma_small_mod(1nat, p());
        };
    } else if n == 1 {
        reveal_with_fuel(edwards_scalar_mul, 1);
        // Both sides equal edwards_add(a.0, a.1, b.0, b.1)
    } else {
        let prev_n = (n - 1) as nat;

        let prev_a = edwards_scalar_mul(a, prev_n);
        let prev_b = edwards_scalar_mul(b, prev_n);
        let prev_sum = edwards_scalar_mul(sum_ab, prev_n);

        // Step 1: Induction hypothesis for n-1
        axiom_edwards_scalar_mul_distributive(a, b, prev_n);
        let ih_rhs = edwards_add(prev_a.0, prev_a.1, prev_b.0, prev_b.1);
        assert(prev_sum == ih_rhs);
        assert(prev_sum.0 == ih_rhs.0);
        assert(prev_sum.1 == ih_rhs.1);

        // Step 2: Unfold f(P, n) = add(f(P, n-1), P) via succ with (n-1)
        lemma_edwards_scalar_mul_succ(sum_ab, prev_n);
        assert(edwards_scalar_mul(sum_ab, n) == edwards_add(prev_sum.0, prev_sum.1, sum_ab.0, sum_ab.1));

        lemma_edwards_scalar_mul_succ(a, prev_n);
        assert(edwards_scalar_mul(a, n) == edwards_add(prev_a.0, prev_a.1, a.0, a.1));

        lemma_edwards_scalar_mul_succ(b, prev_n);
        assert(edwards_scalar_mul(b, n) == edwards_add(prev_b.0, prev_b.1, b.0, b.1));

        // Step 3: Substitute IH into LHS
        assert(edwards_add(prev_sum.0, prev_sum.1, sum_ab.0, sum_ab.1)
            == edwards_add(ih_rhs.0, ih_rhs.1, sum_ab.0, sum_ab.1));

        // Step 4: Four-way swap: (prev_a + prev_b) + (a + b) == (prev_a + a) + (prev_b + b)
        lemma_edwards_add_four_way_swap(prev_a, prev_b, a, b);

        let ab_result = edwards_add(prev_a.0, prev_a.1, prev_b.0, prev_b.1);
        let cd_result = edwards_add(a.0, a.1, b.0, b.1);
        let ac_result = edwards_add(prev_a.0, prev_a.1, a.0, a.1);
        let bd_result = edwards_add(prev_b.0, prev_b.1, b.0, b.1);

        assert(edwards_add(ab_result.0, ab_result.1, cd_result.0, cd_result.1)
            == edwards_add(ac_result.0, ac_result.1, bd_result.0, bd_result.1));

        // Connect ih_rhs == ab_result, sum_ab == cd_result
        assert(ih_rhs.0 == ab_result.0);
        assert(ih_rhs.1 == ab_result.1);
        assert(sum_ab.0 == cd_result.0);
        assert(sum_ab.1 == cd_result.1);

        // Connect ac_result/bd_result to scalar muls of a,b at n
        let na = edwards_scalar_mul(a, n);
        let nb = edwards_scalar_mul(b, n);
        assert(na == ac_result);
        assert(nb == bd_result);
        assert(na.0 == ac_result.0);
        assert(na.1 == ac_result.1);
        assert(nb.0 == bd_result.0);
        assert(nb.1 == bd_result.1);

        // Final chain
        assert(edwards_scalar_mul(sum_ab, n) == edwards_add(na.0, na.1, nb.0, nb.1));
    }
}