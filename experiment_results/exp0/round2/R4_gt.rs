    match P_aff {
        MontgomeryAffine::Infinity => {
            assert(fe51_as_canonical_nat(&P_proj.W) == 0);
            assert(projective_u_coordinate(P_proj) == 0);
            assert(u_coordinate(P_aff) == 0);
            assert(u_coordinate(P_aff) % p() == 0) by {
                p_gt_2();
                lemma_small_mod(0, p());
            }
        },
        MontgomeryAffine::Finite { u, v: _ } => {
            let U = fe51_as_canonical_nat(&P_proj.U);
            let W = fe51_as_canonical_nat(&P_proj.W);
            assert(W != 0);
            assert(U == field_mul(u, W));
            assert(W % p() != 0) by {
                let W_raw = fe51_as_nat(&P_proj.W);
                assert(W == W_raw % p());
                assert(W_raw % p() < p()) by {
                    p_gt_2();
                    lemma_mod_division_less_than_divisor(W_raw as int, p() as int);
                }
                assert(W % p() == W) by {
                    lemma_small_mod(W, p());
                }
            }

            assert(projective_u_coordinate(P_proj) == field_mul(U, field_inv(W)));
            assert(projective_u_coordinate(P_proj) == field_mul(field_mul(u, W), field_inv(W)));

            assert(projective_u_coordinate(P_proj) == field_mul(u, field_mul(W, field_inv(W)))) by {
                lemma_field_mul_assoc(u, W, field_inv(W));
            }

            assert(field_mul(W, field_inv(W)) == 1) by {
                lemma_inv_mul_cancel(W);
                lemma_field_mul_comm(field_inv(W), W);
            }

            assert(field_mul(u, 1) == u % p()) by {
                lemma_field_mul_one_right(u);
            }
            assert(projective_u_coordinate(P_proj) == u % p());
        },
    }
