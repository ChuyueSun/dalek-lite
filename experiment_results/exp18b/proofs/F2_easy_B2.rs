{
    let p = p();
    p_gt_2();
    let bc = field_add(b, c);
    assert(bc == (b + c) % p);
    assert(field_mul(a, bc) == (a * bc) % p);
    lemma_mul_mod_noop_right(a as int, (b + c) as int, p as int);
    assert((a * bc) % p == (a * (b + c)) % p);
    lemma_mul_is_distributive_add(a as int, b as int, c as int);
    assert(a * (b + c) == a * b + a * c);
    lemma_add_mod_noop(a as int * b as int, a as int * c as int, p as int);
    assert((a * (b + c)) % p == ((a * b) % p + (a * c) % p) % p);
    assert(field_mul(a, b) == (a * b) % p);
    assert(field_mul(a, c) == (a * c) % p);
    assert(field_add(field_mul(a, b), field_mul(a, c)) == ((a * b) % p + (a * c) % p) % p);
}
