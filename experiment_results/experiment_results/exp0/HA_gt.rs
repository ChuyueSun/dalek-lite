pub proof fn lemma_field_add_comm(a: nat, b: nat)
    ensures
        field_add(a, b) == field_add(b, a),
{
    let p = p();
    p_gt_2();
    assert(field_add(a, b) == (a + b) % p);
    assert(field_add(b, a) == (b + a) % p);
    assert((a + b) as int == (b + a) as int);
}
