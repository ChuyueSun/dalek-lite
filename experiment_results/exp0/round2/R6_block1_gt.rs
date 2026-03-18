        proof {
            // Trigger the forall invariant
            assert(output.limbs == [
                (original_limbs[0] + _rhs.limbs[0]) as u64,
                (original_limbs[1] + _rhs.limbs[1]) as u64,
                (original_limbs[2] + _rhs.limbs[2]) as u64,
                (original_limbs[3] + _rhs.limbs[3]) as u64,
                (original_limbs[4] + _rhs.limbs[4]) as u64,
            ]);

            lemma_field51_add(self, _rhs);

            // Prove bound propagation: n-bit inputs → (n+1)-bit output
            // If a < 2^n and b < 2^n, then a + b < 2^(n+1)
            assert((1u64 << 51) + (1u64 << 51) == (1u64 << 52)) by (bit_vector);
            assert((1u64 << 52) + (1u64 << 52) == (1u64 << 53)) by (bit_vector);
        }
