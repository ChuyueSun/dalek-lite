    let p = p();
    p_gt_2();
    let neg_x = field_neg(x);

    // From precondition: (x, y) is on the Edwards curve, i.e., is_on_edwards_curve(x, y)

    // Key insight: (-x)² = x²
    assert(field_square(neg_x) == field_square(x)) by {
        lemma_neg_square_eq(x);
        lemma_square_mod_noop(x);
    };

    // With (-x)² = x², the curve equation for (-x, y) is identical to that for (x, y)
    // since is_on_edwards_curve only uses x² (not x itself)
    assert(is_on_edwards_curve(neg_x, y));
