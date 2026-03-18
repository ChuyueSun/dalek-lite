        proof {
            lemma_unfold_edwards(r);
            let new_x = fe51_as_canonical_nat(&r.X);
            let new_y = fe51_as_canonical_nat(&r.Y);
            let new_z = fe51_as_canonical_nat(&r.Z);
            let new_t = fe51_as_canonical_nat(&r.T);

            assert(new_x == field_neg(old_x));
            assert(new_t == field_neg(old_t));
            assert(new_y == old_y);
            assert(new_z == old_z);

            assert(fe51_limbs_bounded(&r.X, 52));
            assert(fe51_limbs_bounded(&r.T, 52));
            assert(fe51_limbs_bounded(&r.Y, 52));
            assert(fe51_limbs_bounded(&r.Z, 52));

            lemma_sum_of_limbs_bounded_from_fe51_bounded(&r.Y, &r.X, 52);
            assert(is_valid_edwards_point(r));

            // 4. Prove affine semantics: edwards_point_as_affine(r) == edwards_neg(edwards_point_as_affine(*self))
            let z_inv = field_inv(old_z);

            // Key algebraic fact: (-x) * z_inv = -(x * z_inv)
            assert(field_mul(new_x, z_inv) == field_neg(field_mul(old_x, z_inv))) by {
                // new_x = field_neg(old_x)
                // field_mul(neg(a), b) = neg(field_mul(a, b)) by field algebra
                lemma_field_mul_comm(new_x, z_inv);
                lemma_field_mul_neg(z_inv, old_x);
                lemma_field_mul_comm(z_inv, old_x);
            };

            // The affine coords match: (neg(x/z), y/z) = edwards_neg((x/z, y/z))
            assert(edwards_point_as_affine(r) == edwards_neg(edwards_point_as_affine(*self)));
        }
