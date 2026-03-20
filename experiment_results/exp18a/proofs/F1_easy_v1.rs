    let p = p();
    p_gt_2();
    let neg_x = field_neg(x);

    // Key insight: (-x)² = x²
    assert(field_square(neg_x) == field_square(x)) by {
        lemma_neg_square_eq(x);
        lemma_square_mod_noop(x);
    };
    // With (-x)² = x², the affine curve equation is unchanged
