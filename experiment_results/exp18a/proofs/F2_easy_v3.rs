// STRATEGY: Unfold field_mul and field_add to their modular arithmetic definitions, then use
// vstd's lemma_mul_mod_noop_right to absorb the inner (b+c)%p into the outer multiplication
// (making the left side equal to (a*(b+c))%p), then use lemma_mul_is_distributive_add for
// integer distributivity to get (a*b + a*c)%p, and finally use lemma_add_mod_noop to show
// that equals ((a*b)%p + (a*c)%p)%p, matching the right-hand side exactly.

{
    let prime = p();
    p_gt_2();

    // Unfold definitions:
    //   LHS = field_mul(a, field_add(b, c))
    //       = (a * ((b + c) % prime)) % prime
    //   RHS = field_add(field_mul(a, b), field_mul(a, c))
    //       = ((a * b) % prime + (a * c) % prime) % prime

    // Step 1: absorb inner mod on LHS
    //   (a * ((b + c) % prime)) % prime == (a * (b + c)) % prime
    lemma_mul_mod_noop_right(a as int, (b + c) as int, prime as int);

    // Step 2: integer distributivity
    //   a * (b + c) == a * b + a * c
    lemma_mul_is_distributive_add(a as int, b as int, c as int);

    // Step 3: mod distributes over add on RHS
    //   (a * b + a * c) % prime == ((a * b) % prime + (a * c) % prime) % prime
    lemma_add_mod_noop(a as int * b as int, a as int * c as int, prime as int);
}
