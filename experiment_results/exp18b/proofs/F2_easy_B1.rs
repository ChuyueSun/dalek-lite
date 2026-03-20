{
    let p = p();
    p_gt_2();
    let bc = field_add(b, c);
    assert(bc == (b + c) % p);
    assert(field_mul(a, bc) == (a * bc) % p);
    assert(field_mul(a, b) == (a * b) % p);
    assert(field_mul(a, c) == (a * c) % p);
    assert(field_add(field_mul(a, b), field_mul(a, c)) == ((a * b) % p + (a * c) % p) % p);
    assert((a * bc) % p == (a * ((b + c) % p)) % p);
    assert((a * ((b + c) % p)) % p == (a * (b + c)) % p) by {
        lemma_mul_mod_right(a as int, (b + c) as int, p as int);
    };
    assert((a * (b + c)) % p == (a * b + a * c) % p) by {
        assert((a * (b + c)) as int == (a * b + a * c) as int);
    };
    assert((a * b + a * c) % p == ((a * b) % p + (a * c) % p) % p) by {
        lemma_mod_add_mod(a * b, a * c, p);
    };
}
