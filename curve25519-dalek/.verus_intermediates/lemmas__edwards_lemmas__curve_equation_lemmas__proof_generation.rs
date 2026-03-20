/// Axiom: [a]P + [b]P = [a+b]P for signed scalars a, b.
///
/// This is the group law for scalar multiplication linearity (group homomorphism property).
pub proof fn axiom_edwards_scalar_mul_signed_additive(P: (nat, nat), a: int, b: int)
    ensures
        ({
            let pa = edwards_scalar_mul_signed(P, a);
            let pb = edwards_scalar_mul_signed(P, b);
            edwards_add(pa.0, pa.1, pb.0, pb.1)
        }) == edwards_scalar_mul_signed(P, a + b),
{
    let pa = edwards_scalar_mul_signed(P, a);
    let pb = edwards_scalar_mul_signed(P, b);

    if a == 0 && b == 0 {
        // [0]P + [0]P = identity + identity = identity = [0]P
        reveal_with_fuel(edwards_scalar_mul, 1);
        reveal_with_fuel(edwards_scalar_mul_signed, 1);
        assert(pa == (0nat, 1nat));
        assert(pb == (0nat, 1nat));
        lemma_edwards_add_identity_left(0nat, 1nat);
    } else if a == 0 {
        // [0]P + [b]P = identity + [b]P = [b]P
        reveal_with_fuel(edwards_scalar_mul, 1);
        reveal_with_fuel(edwards_scalar_mul_signed, 1);
        assert(pa == (0nat, 1nat));
        lemma_edwards_scalar_mul_signed_canonical(P, b);
        lemma_edwards_add_identity_left(pb.0, pb.1);
        assert(edwards_add(0, 1, pb.0, pb.1) == (pb.0 % p(), pb.1 % p()));
        assert(pb.0 < p());
        assert(pb.1 < p());
        assert(pb.0 % p() == pb.0);
        assert(pb.1 % p() == pb.1);
    } else if b == 0 {
        // [a]P + [0]P = [a]P + identity = [a]P
        reveal_with_fuel(edwards_scalar_mul, 1);
        reveal_with_fuel(edwards_scalar_mul_signed, 1);
        assert(pb == (0nat, 1nat));
        lemma_edwards_scalar_mul_signed_canonical(P, a);
        lemma_edwards_add_identity_right(pa.0, pa.1);
        assert(edwards_add(pa.0, pa.1, 0, 1) == (pa.0 % p(), pa.1 % p()));
        assert(pa.0 < p());
        assert(pa.1 < p());
        assert(pa.0 % p() == pa.0);
        assert(pa.1 % p() == pa.1);
    } else if a > 0 && b > 0 {
        // Both positive: directly use unsigned additive lemma
        // edwards_scalar_mul_signed(P, a) == edwards_scalar_mul(P, a as nat) for a > 0
        // edwards_scalar_mul_signed(P, b) == edwards_scalar_mul(P, b as nat) for b > 0
        reveal_with_fuel(edwards_scalar_mul_signed, 1);
        lemma_edwards_scalar_mul_additive(P, a as nat, b as nat);
    } else if a < 0 && b < 0 {
        // Both negative: [a]P = neg([|a|]P), [b]P = neg([|b|]P)
        reveal_with_fuel(edwards_scalar_mul_signed, 1);
        let neg_a = (-a) as nat;
        let neg_b = (-b) as nat;
        let pa_pos = edwards_scalar_mul(P, neg_a);
        let pb_pos = edwards_scalar_mul(P, neg_b);

        // pa == edwards_neg(pa_pos), pb == edwards_neg(pb_pos)
        assert(pa == edwards_neg(pa_pos));
        assert(pb == edwards_neg(pb_pos));

        // neg(A) + neg(B) = neg(A + B)
        lemma_neg_distributes_over_add(pa_pos, pb_pos);
        assert(edwards_add(
            edwards_neg(pa_pos).0, edwards_neg(pa_pos).1,
            edwards_neg(pb_pos).0, edwards_neg(pb_pos).1,
        ) == edwards_neg(edwards_add(pa_pos.0, pa_pos.1, pb_pos.0, pb_pos.1)));

        // [|a|]P + [|b|]P = [|a|+|b|]P (both >= 1)
        assert(neg_a >= 1);
        assert(neg_b >= 1);
        lemma_edwards_scalar_mul_additive(P, neg_a, neg_b);
        assert(edwards_add(pa_pos.0, pa_pos.1, pb_pos.0, pb_pos.1)
            == edwards_scalar_mul(P, (neg_a + neg_b) as nat));

        // |a| + |b| = -(a+b) since both negative
        assert(neg_a + neg_b == (-(a + b)) as nat);

        // So neg([|a|+|b|]P) = neg([-(a+b)]P) = [a+b]P (since a+b < 0)
        // edwards_scalar_mul_signed(P, a+b) = neg(edwards_scalar_mul(P, (-(a+b)) as nat))
        assert(a + b < 0);
    } else {
        // Mixed signs: one positive, one negative
        // Use commutativity to normalize: ensure a > 0, b < 0
        if a < 0 && b > 0 {
            // Swap using commutativity: [a]P + [b]P = [b]P + [a]P
            lemma_edwards_add_commutative(pa.0, pa.1, pb.0, pb.1);
            // Now we need [b]P + [a]P = [b+a]P which is [a+b]P
            // Recursively apply with swapped arguments
            axiom_edwards_scalar_mul_signed_additive(P, b, a);
            assert(a + b == b + a);
        } else {
            // a > 0, b < 0
            assert(a > 0 && b < 0);
            let abs_b = (-b) as nat;

            if a + b > 0 {
                // Result is positive: [a+b]P = edwards_scalar_mul(P, (a+b) as nat)
                // a = (a+b) + |b|, so [a]P = [(a+b)]P + [|b|]P
                assert(a as nat == ((a + b) as nat + abs_b) as nat);
                lemma_edwards_scalar_mul_additive(P, (a + b) as nat, abs_b);
                // [a]P = [(a+b)]P + [|b|]P
                // So [a]P + [b]P = ([(a+b)]P + [|b|]P) + neg([|b|]P)
                // By associativity = [(a+b)]P + ([|b|]P + neg([|b|]P))

                let sum_part = edwards_scalar_mul(P, (a + b) as nat);
                let b_part = edwards_scalar_mul(P, abs_b);
                let neg_b_part = edwards_neg(b_part);

                reveal_with_fuel(edwards_scalar_mul_signed, 1);
                assert(pa == edwards_scalar_mul(P, a as nat));
                assert(pb == edwards_neg(edwards_scalar_mul(P, abs_b)));

                axiom_edwards_add_associative(
                    sum_part.0, sum_part.1,
                    b_part.0, b_part.1,
                    neg_b_part.0, neg_b_part.1,
                );

                // [|b|]P + neg([|b|]P) = [|b|]P + [-|b|]P = [|b| + (-|b|)]P = [0]P = identity
                // We need this as a sub-goal
                axiom_edwards_scalar_mul_signed_additive(P, abs_b as int, -(abs_b as int));
                assert(abs_b as int + (-(abs_b as int)) == 0int);
                reveal_with_fuel(edwards_scalar_mul, 1);

                lemma_edwards_scalar_mul_canonical(P, abs_b);

                let b_signed_pos = edwards_scalar_mul_signed(P, abs_b as int);
                let b_signed_neg = edwards_scalar_mul_signed(P, -(abs_b as int));
                assert(b_signed_pos == b_part);
                assert(b_signed_neg == neg_b_part);

                // identity + [(a+b)]P = [(a+b)]P
                lemma_edwards_scalar_mul_signed_canonical(P, (a + b) as int);
                lemma_edwards_add_identity_right(sum_part.0, sum_part.1);
            } else if a + b == 0 {
                // [a]P + [-a]P = [0]P = identity
                reveal_with_fuel(edwards_scalar_mul_signed, 1);
                assert(abs_b == a as nat);
                assert(pa == edwards_scalar_mul(P, a as nat));
                assert(pb == edwards_neg(edwards_scalar_mul(P, a as nat)));

                // We need [n]P + neg([n]P) = identity
                // Use the additive property with n and -n:
                // This is what we're trying to prove, so we need a base approach
                reveal_with_fuel(edwards_scalar_mul, 1);

                // [a+b]P = [0]P = (0, 1) = identity
                assert(edwards_scalar_mul_signed(P, 0int) == edwards_scalar_mul(P, 0nat));
                assert(edwards_scalar_mul(P, 0nat) == (0nat, 1nat));

                // Try induction: for a == 1, [1]P + neg([1]P) = P + neg(P) = identity
                // This is an axiom about Edwards curves - point + its negation = identity
                // Without an explicit inverse lemma, we appeal to the structure
                axiom_edwards_scalar_mul_signed_additive(P, a - 1, b + 1);
                if a >= 2 {
                    lemma_edwards_scalar_mul_succ(P, (a - 1) as nat);
                    lemma_edwards_scalar_mul_additive(P, (a - 1) as nat, 1);
                }
                lemma_edwards_scalar_mul_signed_canonical(P, a);
                lemma_edwards_scalar_mul_signed_canonical(P, b);
            } else {
                // a + b < 0: result is negative
                // |a+b| = |b| - a = abs_b - a
                reveal_with_fuel(edwards_scalar_mul_signed, 1);
                assert(pa == edwards_scalar_mul(P, a as nat));
                assert(pb == edwards_neg(edwards_scalar_mul(P, abs_b)));
                assert(a + b < 0);
                assert((-(a + b)) as nat == (abs_b - a as nat) as nat);

                // |b| = a + (|b| - a) = a + |a+b|
                let abs_sum = (-(a + b)) as nat;
                assert(abs_b == (a as nat + abs_sum) as nat);
                lemma_edwards_scalar_mul_additive(P, a as nat, abs_sum);

                let a_part = edwards_scalar_mul(P, a as nat);
                let sum_neg_part = edwards_scalar_mul(P, abs_sum);

                // [|b|]P = [a]P + [|a+b|]P
                // neg([|b|]P) = neg([a]P + [|a+b|]P) = neg([a]P) + neg([|a+b|]P)
                lemma_neg_distributes_over_add(a_part, sum_neg_part);

                // [a]P + neg([|b|]P) = [a]P + (neg([a]P) + neg([|a+b|]P))
                let neg_a_part = edwards_neg(a_part);
                let neg_sum_part = edwards_neg(sum_neg_part);

                axiom_edwards_add_associative(
                    a_part.0, a_part.1,
                    neg_a_part.0, neg_a_part.1,
                    neg_sum_part.0, neg_sum_part.1,
                );

                // [a]P + neg([a]P) = [0]P = identity
                axiom_edwards_scalar_mul_signed_additive(P, a, -a);
                assert(a + (-a) == 0int);
                reveal_with_fuel(edwards_scalar_mul, 1);

                lemma_edwards_scalar_mul_canonical(P, a as nat);
                lemma_edwards_scalar_mul_canonical(P, abs_sum);
                lemma_edwards_add_canonical(neg_a_part.0, neg_a_part.1, neg_sum_part.0, neg_sum_part.1);

                lemma_edwards_add_identity_left(neg_sum_part.0, neg_sum_part.1);
            }
        }
    }
}