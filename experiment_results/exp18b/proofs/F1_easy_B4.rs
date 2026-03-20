{
    let p = p();
    p_gt_2();
    let neg_x = field_neg(x);

    // Key insight: (-x)² = x²
    assert(field_square(neg_x) == field_square(x)) by {
        lemma_neg_square_eq(x);
        lemma_square_mod_noop(x);
    };

    // With field_square(neg_x) == field_square(x), the curve equation for (neg_x, y)
    // is identical to the curve equation for (x, y), which holds by precondition.
}
