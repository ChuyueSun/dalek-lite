/// Lemma: [a]P + [b]P = [a+b]P for signed scalars a, b.
///
/// This is the group law for scalar multiplication linearity (group homomorphism property).
pub proof fn axiom_edwards_scalar_mul_signed_additive(P: (nat, nat), a: int, b: int)
    requires
        P.0 < p(),
        P.1 < p(),
    ensures
        ({
            let pa = edwards_scalar_mul_signed(P, a);
            let pb = edwards_scalar_mul_signed(P, b);
            edwards_add(pa.0, pa.1, pb.0, pb.1)
        }) == edwards_scalar_mul_signed(P, a + b),
{
    reveal(edwards_scalar_mul_signed);

    if a == 0 && b == 0 {
        // Both zero: add(identity, identity) = identity = [0]P
        reveal_with_fuel(edwards_scalar_mul, 1);
        // edwards_scalar_mul(P, 0) == (0, 1) == edwards_identity()
        lemma_edwards_double_identity();
        // edwards_double(0, 1) == (0, 1), i.e., edwards_add(0, 1, 0, 1) == (0, 1)
    } else if a == 0 {
        // a == 0, b != 0: add(identity, [b]P) = [b]P = [a+b]P
        reveal_with_fuel(edwards_scalar_mul, 1);
        // edwards_scalar_mul(P, 0) == (0, 1), so edwards_scalar_mul_signed(P, 0) == (0, 1)

        // Get canonical bounds on [b]P
        lemma_edwards_scalar_mul_signed_canonical(P, b);
        let pb = edwards_scalar_mul_signed(P, b);
        assert(pb.0 < p());
        assert(pb.1 < p());

        // add(0, 1, pb.0, pb.1) == (pb.0 % p(), pb.1 % p())
        lemma_edwards_add_identity_left(pb.0, pb.1);

        // Since pb.0 < p() and pb.1 < p(), reduce mod p is identity
        lemma_field_element_reduced(pb.0);
        assert(pb.0 % p() == pb.0);
        lemma_field_element_reduced(pb.1);
        assert(pb.1 % p() == pb.1);

        // So edwards_add(0, 1, pb.0, pb.1) == (pb.0, pb.1) == pb
        assert(edwards_add(0, 1, pb.0, pb.1) == pb);
    } else if b == 0 {
        // b == 0, a != 0: add([a]P, identity) = [a]P = [a+b]P
        reveal_with_fuel(edwards_scalar_mul, 1);

        lemma_edwards_scalar_mul_signed_canonical(P, a);
        let pa = edwards_scalar_mul_signed(P, a);
        assert(pa.0 < p());
        assert(pa.1 < p());

        // add(pa.0, pa.1, 0, 1) == (pa.0 % p(), pa.1 % p())
        lemma_edwards_add_identity_right(pa.0, pa.1);

        lemma_field_element_reduced(pa.0);
        assert(pa.0 % p() == pa.0);
        lemma_field_element_reduced(pa.1);
        assert(pa.1 % p() == pa.1);

        assert(edwards_add(pa.0, pa.1, 0, 1) == pa);
    } else if a > 0 && b > 0 {
        // Both positive: directly use unsigned additive lemma
        // [a]P + [b]P = [a+b]P for nat
        lemma_edwards_scalar_mul_additive(P, a as nat, b as nat);
    } else if a < 0 && b < 0 {
        // Both negative:
        // [a]P = neg([|a|]P), [b]P = neg([|b|]P)
        // add(neg(A), neg(B)) = neg(add(A, B))
        // add(A, B) = [|a|+|b|]P
        // neg([|a|+|b|]P) = [a+b]_signed P since a+b < 0 and |a+b| = |a|+|b|
        let abs_a = (-a) as nat;
        let abs_b = (-b) as nat;
        let qa = edwards_scalar_mul(P, abs_a);
        let qb = edwards_scalar_mul(P, abs_b);

        // Step 1: add(neg(qa), neg(qb)) == neg(add(qa, qb))
        lemma_neg_distributes_over_add(qa, qb);
        assert(edwards_add(
            edwards_neg(qa).0, edwards_neg(qa).1,
            edwards_neg(qb).0, edwards_neg(qb).1
        ) == edwards_neg(edwards_add(qa.0, qa.1, qb.0, qb.1)));

        // Step 2: add(qa, qb) == [|a|+|b|]P
        lemma_edwards_scalar_mul_additive(P, abs_a, abs_b);
        assert(edwards_add(qa.0, qa.1, qb.0, qb.1) == edwards_scalar_mul(P, abs_a + abs_b));

        // Step 3: |a+b| == |a| + |b| when both negative
        assert((-(a + b)) as nat == abs_a + abs_b) by {
            assert(-(a + b) == -a + -b);
        };

        // So neg([|a|+|b|]P) == neg([|a+b|]P) == edwards_scalar_mul_signed(P, a+b)
    } else if a < 0 && b > 0 {
        // Mixed: a < 0, b > 0
        // Use commutativity to swap, then use pos_neg helper with (b, a)
        let pa = edwards_scalar_mul_signed(P, a);
        let pb = edwards_scalar_mul_signed(P, b);

        // Step 1: add(pa, pb) == add(pb, pa)
        lemma_edwards_add_commutative(pa.0, pa.1, pb.0, pb.1);
        assert(edwards_add(pa.0, pa.1, pb.0, pb.1) == edwards_add(pb.0, pb.1, pa.0, pa.1));

        // Step 2: add([b]P, [a]P) == [b+a]P via pos_neg helper (b > 0, a < 0)
        lemma_signed_additive_pos_neg(P, b, a);
        assert(edwards_add(pb.0, pb.1, pa.0, pa.1) == edwards_scalar_mul_signed(P, b + a));

        // Step 3: a + b == b + a
        assert(a + b == b + a);
    } else {
        // a > 0, b < 0: directly use pos_neg helper
        assert(a > 0 && b < 0);
        lemma_signed_additive_pos_neg(P, a, b);
    }
}