{
    let p = p();
    p_gt_2();
    let bc = field_add(b, c);
    // field_add(b, c) = (b + c) % p
    // field_mul(a, bc) = (a * bc) % p = (a * ((b + c) % p)) % p
    // Step 1: absorb inner mod: a * ((b+c) % p) % p == a * (b+c) % p
    lemma_mul_mod_noop_right(a as int, (b + c) as int, p as int);
    // Step 2: integer distributivity: a * (b+c) == a*b + a*c
    lemma_mul_is_distributive_add(a as int, b as int, c as int);
    // Step 3: split outer mod: (a*b + a*c) % p == ((a*b)%p + (a*c)%p) % p
    lemma_add_mod_noop((a * b) as int, (a * c) as int, p as int);
}
