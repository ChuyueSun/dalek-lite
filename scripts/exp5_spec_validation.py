#!/usr/bin/env python3
"""
Experiment 5: Spec Validation Retroactive Test

For known spec bugs from the dalek-lite Verus codebase git history, this script
simulates the arithmetic in Python to check whether random property tests
(proptests) would have caught the bugs, and how many samples are needed.

Bug 1: from_bytes wrong postcondition
  - Wrong ensures: to_nat(&s.limbs) < group_order()
  - Reality: from_bytes of arbitrary bytes can produce scalars >= group_order
  - from_bytes faithfully represents 256-bit values (no mod reduction)

Bug 3: spec_scalar vs scalar_to_nat confusion
  - spec_scalar(s) = bytes_to_nat(s.bytes) % L  (canonical)
  - scalar_to_nat(s) = bytes_to_nat(s.bytes)     (raw, without mod)
  - For non-canonical scalars (>= L), they differ
"""

import json
import os
import random
import sys

# Group order L = 2^252 + 27742317777372353535851937790883648493
L = 2**252 + 27742317777372353535851937790883648493


def from_bytes_to_limbs(b: bytes) -> list:
    """
    Simulate Scalar52::from_bytes: unpack 32 bytes into 5 u64 limbs with radix 2^52.

    From the Rust source:
      words[i] = little-endian u64 from bytes[i*8..(i+1)*8]  (4 words)
      mask = (1 << 52) - 1
      top_mask = (1 << 48) - 1
      limbs[0] =  words[0]                           & mask
      limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask
      limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask
      limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask
      limbs[4] =  (words[3] >> 16)                    & top_mask
    """
    assert len(b) == 32

    # Pack into 4 little-endian u64 words
    words = []
    for i in range(4):
        w = int.from_bytes(b[i*8:(i+1)*8], byteorder='little')
        words.append(w)

    mask = (1 << 52) - 1
    top_mask = (1 << 48) - 1

    limbs = [0] * 5
    limbs[0] = words[0] & mask
    limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask
    limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask
    limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask
    limbs[4] = (words[3] >> 16) & top_mask

    return limbs


def to_nat(limbs: list) -> int:
    """
    Compute the natural number from 5 limbs in radix 2^52:
      limbs[0] + limbs[1] * 2^52 + limbs[2] * 2^104 + limbs[3] * 2^156 + limbs[4] * 2^208
    """
    result = 0
    for i, limb in enumerate(limbs):
        result += limb * (2 ** (52 * i))
    return result


def bytes_to_nat(b: bytes) -> int:
    """
    Interpret 32 bytes as a little-endian 256-bit integer.
    This is u8_32_as_nat / bytes_seq_as_nat.
    """
    return int.from_bytes(b, byteorder='little')


def verify_from_bytes_roundtrip():
    """
    Sanity check: from_bytes should produce limbs whose to_nat equals bytes_to_nat.
    This is the *correct* postcondition.
    """
    for _ in range(1000):
        b = bytes(random.randint(0, 255) for _ in range(32))
        limbs = from_bytes_to_limbs(b)
        assert to_nat(limbs) == bytes_to_nat(b), \
            f"Roundtrip failed for {b.hex()}: to_nat={to_nat(limbs)}, bytes_to_nat={bytes_to_nat(b)}"
    print("Sanity check passed: from_bytes roundtrip is correct for 1000 samples.")


def test_bug1(sample_sizes):
    """
    Bug 1: Test the wrong postcondition 'to_nat(&s.limbs) < group_order()'.
    Generate random 32-byte arrays, compute from_bytes then to_nat, check if < L.
    """
    results = {}
    for n in sample_sizes:
        random.seed(42)  # Deterministic for reproducibility
        first_counterexample_idx = None
        first_counterexample_bytes = None
        counterexample_count = 0

        for i in range(n):
            b = bytes(random.randint(0, 255) for _ in range(32))
            limbs = from_bytes_to_limbs(b)
            val = to_nat(limbs)

            if val >= L:
                counterexample_count += 1
                if first_counterexample_idx is None:
                    first_counterexample_idx = i + 1  # 1-indexed
                    first_counterexample_bytes = b.hex()

        results[n] = {
            "counterexample_count": counterexample_count,
            "first_counterexample_at_sample": first_counterexample_idx,
            "first_counterexample_bytes": first_counterexample_bytes,
            "rate_per_10000": round(counterexample_count / n * 10000, 1) if n > 0 else 0,
        }

    return results


def test_bug3(sample_sizes):
    """
    Bug 3: Test spec_scalar vs scalar_to_nat confusion.
    spec_scalar(s) = bytes_to_nat(s.bytes) % L
    scalar_to_nat(s) = bytes_to_nat(s.bytes)
    They differ iff bytes_to_nat(s.bytes) >= L.
    """
    results = {}
    for n in sample_sizes:
        random.seed(42)  # Deterministic
        first_counterexample_idx = None
        first_counterexample_bytes = None
        counterexample_count = 0

        for i in range(n):
            b = bytes(random.randint(0, 255) for _ in range(32))
            val = bytes_to_nat(b)

            if val >= L:
                counterexample_count += 1
                if first_counterexample_idx is None:
                    first_counterexample_idx = i + 1
                    first_counterexample_bytes = b.hex()

        results[n] = {
            "counterexample_count": counterexample_count,
            "first_counterexample_at_sample": first_counterexample_idx,
            "first_counterexample_bytes": first_counterexample_bytes,
            "rate_per_10000": round(counterexample_count / n * 10000, 1) if n > 0 else 0,
        }

    return results


def compute_theoretical_probability():
    """
    Compute the theoretical probability that a random 256-bit value >= L.

    L = 2^252 + 27742317777372353535851937790883648493
    The range [0, 2^256) has 2^256 values.
    Values >= L: 2^256 - L
    Probability = (2^256 - L) / 2^256

    Since L ~ 2^252, approximately (2^256 - 2^252) / 2^256 = 1 - 1/16 = 15/16 ~ 93.75%
    """
    total = 2**256
    prob = (total - L) / total
    return prob


def main():
    print("=" * 70)
    print("Experiment 5: Spec Validation Retroactive Test")
    print("=" * 70)
    print()

    # Sanity check
    verify_from_bytes_roundtrip()
    print()

    # Theoretical probability
    theoretical_prob = compute_theoretical_probability()
    print(f"Theoretical probability of counterexample:")
    print(f"  L = 2^252 + 27742317777372353535851937790883648493")
    print(f"  P(random 256-bit value >= L) = {theoretical_prob:.10f}")
    print(f"  = {theoretical_prob * 100:.6f}%")
    print(f"  ~ 15/16 = {15/16:.6f} (since L ~ 2^252 and 2^256/2^252 = 16)")
    print()

    sample_sizes = [100, 1000, 10000]

    # Bug 1
    print("-" * 70)
    print("Bug 1: from_bytes wrong postcondition (to_nat < group_order)")
    print("-" * 70)
    bug1_results = test_bug1(sample_sizes)
    for n, r in bug1_results.items():
        print(f"  n={n:>5}: counterexamples={r['counterexample_count']:>5}, "
              f"first_at_sample={r['first_counterexample_at_sample']}, "
              f"rate_per_10000={r['rate_per_10000']}")
    print()

    # Bug 3
    print("-" * 70)
    print("Bug 3: spec_scalar vs scalar_to_nat (bytes_to_nat >= L)")
    print("-" * 70)
    bug3_results = test_bug3(sample_sizes)
    for n, r in bug3_results.items():
        print(f"  n={n:>5}: counterexamples={r['counterexample_count']:>5}, "
              f"first_at_sample={r['first_counterexample_at_sample']}, "
              f"rate_per_10000={r['rate_per_10000']}")
    print()

    # Build output JSON
    # Use the largest sample size results for the top-level summary
    bug1_summary = bug1_results[10000]
    bug3_summary = bug3_results[10000]

    output = {
        "experiment": "Experiment 5: Spec Validation Retroactive Test",
        "description": (
            "Test whether random property tests (proptests) would catch known spec bugs "
            "from git history, by simulating the arithmetic in Python."
        ),
        "theoretical_probability_counterexample": round(theoretical_prob, 10),
        "bug1_from_bytes_postcondition": {
            "description": (
                "Wrong postcondition: to_nat(&s.limbs) < group_order(). "
                "from_bytes faithfully represents all 256 bits without mod reduction, "
                "so any 256-bit value >= L (about 93.75% of inputs) is a counterexample."
            ),
            "counterexample_found": bug1_summary["first_counterexample_at_sample"] is not None,
            "samples_to_first_counterexample": bug1_summary["first_counterexample_at_sample"],
            "counterexample_rate_per_10000": bug1_summary["rate_per_10000"],
            "counterexample_bytes": bug1_summary["first_counterexample_bytes"],
            "results_by_sample_size": bug1_results,
        },
        "bug3_spec_scalar_vs_scalar_to_nat": {
            "description": (
                "Confusion between spec_scalar(s) = bytes_to_nat(s.bytes) % L and "
                "scalar_to_nat(s) = bytes_to_nat(s.bytes). They differ when bytes_to_nat >= L, "
                "which is about 93.75% of random 256-bit inputs."
            ),
            "counterexample_found": bug3_summary["first_counterexample_at_sample"] is not None,
            "samples_to_first_counterexample": bug3_summary["first_counterexample_at_sample"],
            "counterexample_rate_per_10000": bug3_summary["rate_per_10000"],
            "counterexample_bytes": bug3_summary["first_counterexample_bytes"],
            "results_by_sample_size": bug3_results,
        },
        "conclusion": (
            "Both bugs are trivially caught by random testing. With ~93.75% of random 256-bit "
            "values exceeding the group order L (since L ~ 2^252 << 2^256), the very first "
            "random sample almost certainly provides a counterexample. Bug 1 (wrong postcondition "
            "claiming to_nat < L after from_bytes) and Bug 3 (confusing spec_scalar with "
            "scalar_to_nat) are both exposed on the first random input. A single random proptest "
            "has >93% chance of catching either bug. Formal verification is not needed for these "
            "particular bugs -- simple random testing suffices."
        ),
    }

    # Save results
    output_path = "/root/experiment_results/exp5_spec_validation.json"
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)

    print(f"Results saved to {output_path}")
    print()
    print("Conclusion:")
    print(output["conclusion"])


if __name__ == "__main__":
    main()
