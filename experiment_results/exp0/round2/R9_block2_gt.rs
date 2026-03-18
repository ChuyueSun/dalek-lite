            proof {
                lemma_unfold_edwards(point);
                // Extract values for lemma
                let x_orig = fe51_as_canonical_nat(&X);

                // Establish step_2 postconditions needed by lemma
                // step_2 ensures Y and Z are preserved by reference equality
                assert(&point.Y == &Y);
                assert(&point.Z == &Z);
                assert(fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(&self.0));
                assert(fe51_as_canonical_nat(&point.Z) == 1);

                // x_orig < p() is trivially true since x_orig = fe51_as_canonical_nat(&X) = ...%p()
                pow255_gt_19();
                assert(x_orig < p()) by {
                    lemma_mod_bound(fe51_as_nat(&X) as int, p() as int);
                };

                // Use the unified lemma to prove all postconditions
                lemma_decompress_valid_branch(&self.0, x_orig, &point);

                // Strengthen to well-formedness: bounds + sum bounds.
                assert(fe51_limbs_bounded(&point.Y, 51));
                assert(fe51_limbs_bounded(&point.Z, 51));
                assert((1u64 << 51) < (1u64 << 52)) by (bit_vector);
                lemma_fe51_limbs_bounded_weaken(&point.Y, 51, 52);
                lemma_fe51_limbs_bounded_weaken(&point.Z, 51, 52);

                assert(edwards_point_limbs_bounded(point));
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&point.Y, &point.X, 52);
                assert(is_well_formed_edwards_point(point));
            }
