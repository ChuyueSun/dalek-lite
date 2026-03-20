    let p = p() as int;
    p_gt_2();
    // field_add(b, c) = (b + c) % p
    // field_mul(a, field_add(b, c)) = (a * ((b + c) % p)) % p
    // By lemma_mul_mod_noop_right: (a * ((b+c) % p)) % p == (a * (b+c)) % p
    lemma_mul_mod_noop_right(a as int, (b + c) as int, p);
    // By lemma_mul_is_distributive_add: a * (b + c) == a*b + a*c
    lemma_mul_is_distributive_add(a as int, b as int, c as int);
    // So (a * (b+c)) % p == (a*b + a*c) % p
    // By lemma_add_mod_noop: (a*b + a*c) % p == ((a*b % p) + (a*c % p)) % p
    lemma_add_mod_noop(a as int * b as int, a as int * c as int, p);
    // field_add(field_mul(a,b), field_mul(a,c)) = ((a*b)%p + (a*c)%p) % p
