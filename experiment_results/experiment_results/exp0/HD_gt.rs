pub proof fn lemma_field_mul_assoc(a: nat, b: nat, c: nat)
    ensures
        field_mul(field_mul(a, b), c) == field_mul(a, field_mul(b, c)),
{
    let p = p();
    p_gt_2();

    let ab = field_mul(a, b);
    let bc = field_mul(b, c);

    // LHS = ((a*b) % p * c) % p
    // RHS = (a * (b*c) % p) % p

    // By mod absorption, both equal (a * b * c) % p
    assert(field_mul(ab, c) == field_mul(a, bc)) by {
        lemma_mul_mod_noop_left((a * b) as int, c as int, p as int);
        lemma_mul_mod_noop_right(a as int, (b * c) as int, p as int);
        lemma_mul_is_associative(a as int, b as int, c as int);
    };
}
