        proof {
            lemma_unfold_edwards(*self);
            // is_valid_edwards_point gives z % p() != 0; since z = fe51_as_canonical_nat < p,
            // z % p = z, so z != 0 — which is what is_valid_projective_point needs
            let z = fe51_as_canonical_nat(&self.Z);
            assert(z % p() != 0);
            p_gt_2();
            assert(z < p()) by {
                lemma_mod_bound(fe51_as_nat(&self.Z) as int, p() as int);
            };
            assert(z != 0) by {
                lemma_small_mod(z, p());
            };
            assert(is_valid_projective_point(proj));
            // ProjectivePoint invariant: 52-bounded (from as_projective postcondition)
            assert(fe51_limbs_bounded(&proj.X, 52) && fe51_limbs_bounded(&proj.Y, 52)
                && fe51_limbs_bounded(&proj.Z, 52));
            // sum_of_limbs_bounded follows from 52-bounded: 2^52 + 2^52 = 2^53 < u64::MAX
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&proj.X, &proj.Y, 52);
        }
