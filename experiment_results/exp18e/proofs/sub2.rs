proof fn lemma_pow2_step(pos: nat)
    ensures
        pow2(pos + 1) == 2 * pow2(pos),
{
    lemma_pow2_adds(1, pos);
    // Now we have: pow2(1) * pow2(pos) == pow2(1 + pos)
    // Note: 1 + pos == pos + 1 (nat addition is commutative)
    assert(1 + pos == pos + 1) by {}; // trivial arithmetic
    // pow2(1) == 2 from lemma2_to64
    lemma2_to64();
    // pow2(1) * pow2(pos) == 2 * pow2(pos) by commutativity
    lemma_mul_is_commutative(pow2(1) as int, pow2(pos) as int);
}
