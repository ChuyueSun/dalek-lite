    // field_mul(a, field_add(b, c)) == field_add(field_mul(a, b), field_mul(a, c))
    // Expanding definitions:
    //   LHS = (a * ((b + c) % p())) % p()
    //   RHS = ((a * b % p()) + (a * c % p())) % p()

    // Step 1: (a * ((b + c) % p())) % p() == (a * (b + c)) % p()
    //         by lemma_mul_mod_noop_right
    lemma_mul_mod_noop_right(a as int, (b + c) as int, p() as int);

    // Step 2: a * (b + c) == a * b + a * c
    //         by lemma_mul_is_distributive_add
    lemma_mul_is_distributive_add(a as int, b as int, c as int);

    // Step 3: (a * b + a * c) % p() == ((a * b % p()) + (a * c % p())) % p()
    //         by lemma_add_mod_noop
    lemma_add_mod_noop(a as int * b as int, a as int * c as int, p() as int);
