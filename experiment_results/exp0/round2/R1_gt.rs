    let neg_x = field_neg(x);

    assert(is_on_edwards_curve(neg_x, y)) by {
        // Key insight: (-x)² = x²
        assert(field_square(neg_x) == field_square(x)) by {
            lemma_neg_square_eq(x);  // (-x)² = (x % p)²
            lemma_square_mod_noop(x);  // (x % p)² = x²
        };
        // With (-x)² = x², the curve equations are identical
    };
