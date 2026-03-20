proof fn lemma_take_pos_plus_one_zero(naf: Seq<i8>, pos: nat)
    requires
        pos < 256,
        naf.len() == 256,
        naf[pos as int] == 0i8,
    ensures
        reconstruct(naf.take((pos + 1) as int)) == reconstruct(naf.take(pos as int)),
{
    lemma_reconstruct_zero_extend(naf, pos, (pos + 1) as nat);
}
