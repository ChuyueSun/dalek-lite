pub proof fn lemma_as_nat_32_mod_255(bytes: &[u8; 32])
    ensures
        u8_32_as_nat(bytes) % pow2(255) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (
        bytes[2] * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5]
            * pow2(5 * 8)) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(
            8 * 8,
        )) + (bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + (
        bytes[12] * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (
        bytes[15] * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (
        bytes[18] * pow2(18 * 8)) + (bytes[19] * pow2(19 * 8)) + (bytes[20] * pow2(20 * 8)) + (
        bytes[21] * pow2(21 * 8)) + (bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (
        bytes[24] * pow2(24 * 8)) + (bytes[25] * pow2(25 * 8)) + (bytes[26] * pow2(26 * 8)) + (
        bytes[27] * pow2(27 * 8)) + (bytes[28] * pow2(28 * 8)) + (bytes[29] * pow2(29 * 8)) + (
        bytes[30] * pow2(30 * 8)) + ((bytes[31] as nat % pow2(7)) * pow2(31 * 8)),
{
    assert(u8_32_as_nat(bytes) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2]
        * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(
        5 * 8,
    )) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (bytes[9]
        * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + (bytes[12]
        * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (bytes[15]
        * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (bytes[18]
        * pow2(18 * 8)) + (bytes[19] * pow2(19 * 8)) + (bytes[20] * pow2(20 * 8)) + (bytes[21]
        * pow2(21 * 8)) + (bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (bytes[24]
        * pow2(24 * 8)) + (bytes[25] * pow2(25 * 8)) + (bytes[26] * pow2(26 * 8)) + (bytes[27]
        * pow2(27 * 8)) + (bytes[28] * pow2(28 * 8)) + (bytes[29] * pow2(29 * 8)) + (bytes[30]
        * pow2(30 * 8)) + (bytes[31] * pow2(31 * 8)) == pow2_sum_u8(bytes, 0, 8, 30) + (bytes[31]
        * pow2(31 * 8))) by {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(bytes[0] == bytes[0] * pow2(0)) by {
            lemma_mul_basics_3(bytes[0] as int);
        }
        reveal_with_fuel(pow2_sum_u8, 31);
    }
    assert(u8_32_as_nat(bytes) % pow2(255) == (pow2_sum_u8(bytes, 0, 8, 30) + bytes[31] * pow2(
        31 * 8,
    )) as nat % pow2(255));

    assert((pow2_sum_u8(bytes, 0, 8, 30) + bytes[31] * pow2(31 * 8)) as nat % pow2(255)
        == pow2_sum_u8(bytes, 0, 8, 30) + (bytes[31] * pow2(31 * 8)) as nat % pow2(255)) by {
        assert(pow2_sum_u8(bytes, 0, 8, 30) < pow2(31 * 8)) by {
            assert forall|i: nat| 0 <= i <= 30 implies bytes[i as int] < pow2(8) by {
                lemma_u8_lt_pow2_8(bytes[i as int]);
            }
            lemma_pow2_sum_u8_bounds(bytes, 0, 8, 30);
        }
        assert((pow2_sum_u8(bytes, 0, 8, 30) + bytes[31] * pow2(31 * 8)) as nat % pow2(255)
            == pow2_sum_u8(bytes, 0, 8, 30) % pow2(255) + (bytes[31] * pow2(31 * 8)) as nat % pow2(
            255,
        )) by {
            lemma_binary_sum_mod_decomposition(
                pow2_sum_u8(bytes, 0, 8, 30),
                bytes[31] as nat,
                31 * 8,
                255,
            );
        }

        assert(pow2_sum_u8(bytes, 0, 8, 30) % pow2(255) == pow2_sum_u8(bytes, 0, 8, 30)) by {
            assert(pow2(31 * 8) < pow2(255)) by {
                lemma_pow2_strictly_increases(31 * 8, 255);
            }
            lemma_small_mod(pow2_sum_u8(bytes, 0, 8, 30), pow2(255));
        }
    }

    assert((bytes[31] as nat * pow2(31 * 8)) % pow2(255) == ((bytes[31] as nat % pow2(7)) * pow2(
        31 * 8,
    ))) by {
        lemma_pow2_mul_mod(bytes[31] as nat, 31 * 8, 255);
    }
}
