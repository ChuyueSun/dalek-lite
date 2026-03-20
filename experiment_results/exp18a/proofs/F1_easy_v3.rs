// STRATEGY: The curve equation involves x², and since (-x)² = x² in any field,
// replacing x with field_neg(x) leaves the squared term unchanged. We first establish
// that field_square(field_neg(x)) == field_square(x) using lemma_neg_square_eq and
// lemma_square_mod_noop, then unfold is_on_edwards_curve to show the equation still holds.

{
    let p = p();
    p_gt_2();
    let neg_x = field_neg(x);

    // Key insight: (-x)² = x² in the field
    assert(field_square(neg_x) == field_square(x)) by {
        lemma_neg_square_eq(x);
        lemma_square_mod_noop(x);
    };

    // With (-x)² = x², the curve equation is unchanged:
    // -(-x)² + y² = 1 + d·(-x)²·y²  iff  -x² + y² = 1 + d·x²·y²
    // which holds by the precondition is_on_edwards_curve(x, y).
}
