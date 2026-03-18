        proof {
            // Helps solver: maps opaque (1u64 << 52) to literal
            assert((1u64 << 52u64) == 4503599627370496u64) by (bit_vector);
            use_type_invariant(*self);
            lemma_negation_preserves_extended_validity(old_x, old_y, old_z, old_t);
            assert(fe51_as_canonical_nat(&neg_x) == field_neg(old_x));
            assert(fe51_as_canonical_nat(&neg_t) == field_neg(old_t));
        }
