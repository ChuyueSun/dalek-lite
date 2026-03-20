    let p = p() as int;
    p_gt_2();
    // Unfold definitions:
    //   field_add(b, c) = (b + c) % p
    //   field_mul(a, field_add(b, c)) = (a * ((b + c) % p)) % p
    // Step 1: absorb inner mod on right factor
    //   (a * ((b+c) % p)) % p == (a * (b+c)) % p
    lemma_mul_mod_noop_right(a as int, (b + c) as int, p);
    // Step 2: integer distributivity a*(b+c) == a*b + a*c
    lemma_mul_is_distributive_add(a as int, b as int, c as int);
    // Now (a * (b+c)) % p == (a*b + a*c) % p
    // Step 3: split mod over addition
    //   (a*b + a*c) % p == ((a*b % p) + (a*c % p)) % p
    lemma_add_mod_noop(a as int * b as int, a as int * c as int, p);
    // The right-hand side is field_add(field_mul(a,b), field_mul(a,c))
    //   = ((a*b % p) + (a*c % p)) % p
    // All steps chain to give the equality.
