pub proof fn lemma_field_mul_distributes_over_add(a: nat, b: nat, c: nat)
    ensures
        field_mul(a, field_add(b, c)) == field_add(field_mul(a, b), field_mul(a, c)),
{
    let p = p();
    p_gt_2();

    // Goal: a · (b + c) = a·b + a·c in the field
    assert(field_mul(a, field_add(b, c)) == field_add(field_mul(a, b), field_mul(a, c))) by {
        // Step 1: a * ((b+c) % p) ≡ a * (b+c) (mod p)
        lemma_mul_mod_noop_right(a as int, (b + c) as int, p as int);

        // Step 2: a * (b+c) = a*b + a*c (integer distributivity)
        lemma_mul_is_distributive_add(a as int, b as int, c as int);

        // Step 3: (a*b + a*c) % p = ((a*b)%p + (a*c)%p) % p
        lemma_add_mod_noop((a * b) as int, (a * c) as int, p as int);
    };
}
