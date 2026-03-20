    // First, establish that the pointwise sum of limbs equals the element-wise addition.
    // The precondition ensures no u64 overflow when adding corresponding limbs.
    let sum = spec_add_fe51_limbs(lhs, rhs);

    // Step 1: Prove u64_5_as_nat of the sum equals the sum of the two u64_5_as_nats.
    // u64_5_as_nat unpacks to: l[0] + 2^51*l[1] + 2^102*l[2] + 2^153*l[3] + 2^204*l[4]
    // Since addition is done limb-wise and there is no overflow (by precondition),
    // the nat values distribute.
    assert(u64_5_as_nat(sum.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs)) by {
        // Each limb of sum equals lhs.limbs[i] + rhs.limbs[i] (no overflow by precondition).
        // Expanding the definition of u64_5_as_nat and using linearity of addition:
        assert(sum.limbs[0] == lhs.limbs[0] + rhs.limbs[0]);
        assert(sum.limbs[1] == lhs.limbs[1] + rhs.limbs[1]);
        assert(sum.limbs[2] == lhs.limbs[2] + rhs.limbs[2]);
        assert(sum.limbs[3] == lhs.limbs[3] + rhs.limbs[3]);
        assert(sum.limbs[4] == lhs.limbs[4] + rhs.limbs[4]);
        assert(u64_5_as_nat(sum.limbs)
            == sum.limbs[0] as nat
                + sum.limbs[1] as nat * (1u64 << 51) as nat
                + sum.limbs[2] as nat * (1u64 << 102) as nat
                + sum.limbs[3] as nat * (1u64 << 153) as nat
                + sum.limbs[4] as nat * (1u64 << 204) as nat) by {
            reveal(u64_5_as_nat);
        }
        assert(u64_5_as_nat(lhs.limbs)
            == lhs.limbs[0] as nat
                + lhs.limbs[1] as nat * (1u64 << 51) as nat
                + lhs.limbs[2] as nat * (1u64 << 102) as nat
                + lhs.limbs[3] as nat * (1u64 << 153) as nat
                + lhs.limbs[4] as nat * (1u64 << 204) as nat) by {
            reveal(u64_5_as_nat);
        }
        assert(u64_5_as_nat(rhs.limbs)
            == rhs.limbs[0] as nat
                + rhs.limbs[1] as nat * (1u64 << 51) as nat
                + rhs.limbs[2] as nat * (1u64 << 102) as nat
                + rhs.limbs[3] as nat * (1u64 << 153) as nat
                + rhs.limbs[4] as nat * (1u64 << 204) as nat) by {
            reveal(u64_5_as_nat);
        }
    }

    // Step 2: Prove the canonical nat (mod p) interpretation is preserved.
    // fe51_as_canonical_nat(x) = u64_5_as_nat(x.limbs) % p
    // field_add(a, b) = (a + b) % p
    // So we need: (u64_5_as_nat(sum.limbs)) % p == (u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs)) % p
    // which follows directly from the first part.
    assert(fe51_as_canonical_nat(&sum) == field_add(
        fe51_as_canonical_nat(lhs),
        fe51_as_canonical_nat(rhs),
    )) by {
        reveal(fe51_as_canonical_nat);
        reveal(field_add);
        assert(u64_5_as_nat(sum.limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs));
    }
