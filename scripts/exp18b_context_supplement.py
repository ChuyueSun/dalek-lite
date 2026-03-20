#!/usr/bin/env python3
"""
Exp 18b: Context Supplement Testing

Tests whether additional context beyond siblings improves proof generation.
All variants include siblings (18a-proven baseline).

B1: Sibling + imports (baseline — equivalent to 18a best)
B2: + strategy catalog hint
B3: + proven lemma registry (exact names with correct signatures)
B4: + strategy + registry + resolved spec definitions
"""

import json
import os
import sys

DALEK_SRC = "/root/dalek-lite/curve25519-dalek/src"
RESULTS_DIR = "/root/dalek-lite/experiment_results/exp18b"

# Strategy hints — targeted advice for each function's proof pattern
STRATEGY_HINTS = {
    "F1_easy": """STRATEGY HINT:
This is a negation-preserves-curve lemma. The curve equation uses x², and (-x)² = x².
Pattern: establish field_square(neg_x) == field_square(x) using neg-square lemmas,
then the curve equation follows identically.""",

    "F2_easy": """STRATEGY HINT:
This is a field distributivity lemma: a·(b+c) = a·b + a·c mod p.
Pattern: chain 3 vstd modular arithmetic lemmas:
1. lemma_mul_mod_noop_right to absorb inner mod
2. lemma_mul_is_distributive_add for integer distributivity
3. lemma_add_mod_noop to split outer mod over addition
IMPORTANT: call p_gt_2() first to establish p > 0 for mod lemma preconditions.""",

    "F3_medium": """STRATEGY HINT:
This proves limb-wise addition preserves nat representation and field semantics.
Pattern: two-step proof:
1. Call lemma_u64_5_as_nat_add for the nat sum equality
2. Call lemma_add_mod_noop for the canonical nat / field_add equivalence
IMPORTANT: call pow255_gt_19() or p_gt_2() first to establish p() > 0.""",

    "F4_medium": """STRATEGY HINT:
This is a serialization roundtrip: from_bytes(as_bytes(fe)) == fe canonically.
Pattern: chain through intermediate values:
1. as_bytes_post gives bytes = v % p
2. from_bytes_post gives decoded = bytes % pow2(255)
3. lemma_small_mod: since v%p < p < pow2(255), the pow2(255) mod is identity
4. lemma_mod_twice: (v%p)%p = v%p, so canonical values match
IMPORTANT: establish p < pow2(255) via pow255_gt_19().""",

    "F5_hard": """STRATEGY HINT:
This proves the NAF even-step invariant: when naf[pos]=0 and window is even,
the reconstruction invariant advances from pos to pos+1.
Pattern: 5-step proof:
1. reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)) since naf[pos]=0
   → use lemma_reconstruct_zero_extend
2. extracted % 2 == bit_at_pos (mod-of-mod)
   → use lemma_mod_mod with a=2, b=pow2(w-1)
   → IMPORTANT: pow2(w) = 2 * pow2(w-1) via lemma_pow2_adds(1, (w-1))
   → IMPORTANT: pow2(1) = 2 via lemma2_to64()
3. carry == bit_at_pos (parity argument from (carry+extracted)%2==0)
4. scalar_val % pow2(pos+1) decomposition
   → use lemma_mod_breakdown(scalar_val, pow2(pos), 2)
5. Combine using pow2(pos+1) = 2 * pow2(pos) via lemma_pow2_adds(1, pos)
WARNING: Do NOT use lemma_pow2_plus_one — it does not exist.
Use lemma_pow2_adds(1, pos) + lemma2_to64() instead.""",

    "F6_hard": """STRATEGY HINT:
This proves carry preserves radix-2^w reconstruction.
Pattern: split-and-cancel:
1. Split both reconstructions at position i using lemma_reconstruct_radix_2w_split
2. Show prefixes equal (digits before i unchanged)
3. Split suffixes at position 1 to isolate digit i
4. Show single-element reconstruct == digit value (recursive unfolding)
5. Split again at position i+1
6. Show tails beyond i+1 are equal
7. Algebraic cancellation: new_di + pw * new_di1 == old_di + pw * old_di1
   → use lemma_mul_is_distributive_add and lemma_mul_is_commutative""",
}

# Proven lemma registry — exact signatures of lemmas available to call
# These are the REAL lemmas in the codebase (not hallucinated)
PROVEN_LEMMA_REGISTRY = {
    "F1_easy": """PROVEN LEMMA REGISTRY (exact signatures — use these names):
  lemma_neg_square_eq(x: nat)
    ensures field_square(field_neg(x)) == field_square(x % p())
  lemma_square_mod_noop(x: nat)
    ensures field_square(x % p()) == field_square(x)
  lemma_field_mul_comm(a: nat, b: nat)
    ensures field_mul(a, b) == field_mul(b, a)
  p_gt_2()
    ensures p() > 2
  lemma_small_mod(x: nat, m: nat)
    requires x < m
    ensures x % m == x""",

    "F2_easy": """PROVEN LEMMA REGISTRY (exact signatures — use these names):
  p_gt_2()
    ensures p() > 2
  lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires m > 0
    ensures x * (y % m) % m == x * y % m
  lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  lemma_add_mod_noop(x: int, y: int, m: int)
    requires m > 0
    ensures (x + y) % m == ((x % m) + (y % m)) % m""",

    "F3_medium": """PROVEN LEMMA REGISTRY (exact signatures — use these names):
  lemma_u64_5_as_nat_add(a: [u64; 5], b: [u64; 5])
    requires forall|i: int| 0 <= i < 5 ==> b[i] as nat + a[i] as nat <= u64::MAX
    ensures u64_5_as_nat([a[0]+b[0], a[1]+b[1], a[2]+b[2], a[3]+b[3], a[4]+b[4]])
            == u64_5_as_nat(a) + u64_5_as_nat(b)
  lemma_add_mod_noop(x: int, y: int, m: int)
    requires m > 0
    ensures (x + y) % m == ((x % m) + (y % m)) % m
  pow255_gt_19()
    ensures p() == pow2(255) - 19, p() > 0, pow2(255) > 19""",

    "F4_medium": """PROVEN LEMMA REGISTRY (exact signatures — use these names):
  pow255_gt_19()
    ensures p() == pow2(255) - 19, p() > 0, pow2(255) > 19
  lemma_mod_pos_bound(x: int, m: int)
    requires m > 0
    ensures 0 <= x % m < m
  lemma_mod_bound(x: int, m: int)
    requires m > 0
    ensures x % m < m
  lemma_small_mod(x: nat, m: nat)
    requires x < m
    ensures x % m == x
  lemma_mod_twice(x: int, m: int)
    requires m > 0
    ensures (x % m) % m == x % m""",

    "F5_hard": """PROVEN LEMMA REGISTRY (exact signatures — use these names):
  lemma_reconstruct_zero_extend(naf: Seq<i8>, pos: nat, new_len: nat)
    requires pos < naf.len(), new_len <= naf.len(), pos < new_len,
             naf[pos as int] == 0i8
    ensures reconstruct(naf.take(new_len as int)) == reconstruct(naf.take(pos as int))
  lemma_reconstruct_split(naf: Seq<i8>, k: nat)
    requires k <= naf.len()
    ensures reconstruct(naf) == reconstruct(naf.take(k)) + pow2(k) * reconstruct(naf.skip(k))
  lemma_pow2_adds(e1: nat, e2: nat)
    ensures pow2(e1) * pow2(e2) == pow2(e1 + e2)
  lemma_pow2_pos(e: nat)
    ensures pow2(e) > 0
  lemma2_to64()
    ensures pow2(0)==1, pow2(1)==2, pow2(2)==4, ..., pow2(64)==0x10000000000000000
  lemma_mod_mod(x: int, a: int, b: int)
    requires a > 0, b > 0
    ensures (x % (a * b)) % a == x % a
  lemma_mod_breakdown(x: int, a: int, b: int)
    requires a > 0, b > 0
    ensures x % (a * b) == a * ((x / a) % b) + x % a
  lemma_mul_is_commutative(x: int, y: int)
    ensures x * y == y * x
  lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
  lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  lemma_small_mod(x: nat, m: nat)
    requires x < m
    ensures x % m == x
  lemma_add_mod_noop(x: int, y: int, m: int)
    requires m > 0
    ensures (x + y) % m == ((x % m) + (y % m)) % m
  lemma_mul_basics(x: int)
    ensures x * 0 == 0, 0 * x == 0, x * 1 == x
  NOTE: lemma_pow2_plus_one does NOT exist. Use lemma_pow2_adds(1, n) instead.
  NOTE: '2int' is NOT valid Verus syntax. Use '2 as int' or just '2'.""",

    "F6_hard": """PROVEN LEMMA REGISTRY (exact signatures — use these names):
  lemma_reconstruct_radix_2w_split(digits: Seq<i8>, k: nat, w: nat)
    requires k <= digits.len(), w > 0
    ensures reconstruct_radix_2w(digits, w) ==
            reconstruct_radix_2w(digits.take(k), w) + pow2(w*k) * reconstruct_radix_2w(digits.skip(k), w)
  lemma_pow2_adds(e1: nat, e2: nat)
    ensures pow2(e1) * pow2(e2) == pow2(e1 + e2)
  lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  lemma_mul_is_commutative(x: int, y: int)
    ensures x * y == y * x
  lemma_mul_basics(x: int)
    ensures x * 0 == 0, 0 * x == 0, x * 1 == x""",
}

# Spec definitions — resolved definitions of spec fns in ensures
SPEC_DEFINITIONS = {
    "F1_easy": """SPEC DEFINITIONS:
  spec fn is_on_edwards_curve(x: nat, y: nat) -> bool {
    let p = p();
    field_sub(field_square(y), field_square(x)) ==
      field_add(1, field_mul(fe51_as_canonical_nat(&EDWARDS_D), field_mul(field_square(x), field_square(y))))
  }
  spec fn field_neg(x: nat) -> nat { (p() - (x % p())) % p() }
  spec fn field_square(x: nat) -> nat { (x * x) % p() }""",

    "F2_easy": """SPEC DEFINITIONS:
  spec fn field_mul(a: nat, b: nat) -> nat { (a * b) % p() }
  spec fn field_add(a: nat, b: nat) -> nat { (a + b) % p() }
  spec fn p() -> nat { pow2(255) - 19 }""",

    "F3_medium": """SPEC DEFINITIONS:
  spec fn fe51_as_canonical_nat(f: &FieldElement51) -> nat { u64_5_as_nat(f.limbs) % p() }
  spec fn field_add(a: nat, b: nat) -> nat { (a + b) % p() }
  spec fn u64_5_as_nat(limbs: [u64; 5]) -> nat {
    limbs[0] as nat + limbs[1] as nat * pow2(51) + limbs[2] as nat * pow2(102)
    + limbs[3] as nat * pow2(153) + limbs[4] as nat * pow2(204)
  }""",

    "F4_medium": """SPEC DEFINITIONS:
  spec fn fe51_as_canonical_nat(f: &FieldElement51) -> nat { fe51_as_nat(f) % p() }
  spec fn fe51_as_nat(f: &FieldElement51) -> nat { u64_5_as_nat(f.limbs) }
  spec fn as_bytes_post(fe: &FieldElement51, bytes: &[u8; 32]) -> bool {
    u8_32_as_nat(bytes) == fe51_as_nat(fe) % p()
  }
  spec fn from_bytes_post(bytes: &[u8; 32], fe: &FieldElement51) -> bool {
    fe51_as_nat(fe) == u8_32_as_nat(bytes) % pow2(255)
  }""",

    "F5_hard": """SPEC DEFINITIONS:
  spec fn reconstruct(naf: Seq<i8>) -> int
    decreases naf.len()
  {
    if naf.len() == 0 { 0 }
    else { naf[0] as int + 2 * reconstruct(naf.skip(1)) }
  }
  spec fn pow2(e: nat) -> nat  // standard power of 2""",

    "F6_hard": """SPEC DEFINITIONS:
  spec fn reconstruct_radix_2w(digits: Seq<i8>, w: nat) -> int
    decreases digits.len()
  {
    if digits.len() == 0 { 0 }
    else { digits[0] as int + pow2(w) * reconstruct_radix_2w(digits.skip(1), w) }
  }""",
}


def build_b1_prompt(fid, obligation, sibling, imports):
    """B1: Sibling + imports (baseline)."""
    return f"""You are writing a Verus proof body.

== SIBLING PROOF (adapt this approach) ==
{sibling}

== OBLIGATION ==
{obligation}

== FILE IMPORTS ==
{imports}

Write the proof body. Follow the structure of the sibling proof where applicable.
Return ONLY the proof body content (between {{ and }}).
"""


def build_b2_prompt(fid, obligation, sibling, imports):
    """B2: Sibling + imports + strategy hint."""
    hint = STRATEGY_HINTS.get(fid, "No specific strategy hint available.")
    return f"""{hint}

== SIBLING PROOF (adapt this approach) ==
{sibling}

== OBLIGATION ==
{obligation}

== FILE IMPORTS ==
{imports}

Follow the strategy hint. Adapt the sibling's approach.
Return ONLY the proof body content (between {{ and }}).
"""


def build_b3_prompt(fid, obligation, sibling, imports):
    """B3: Sibling + imports + proven lemma registry."""
    registry = PROVEN_LEMMA_REGISTRY.get(fid, "No registry available.")
    return f"""== SIBLING PROOF (adapt this approach) ==
{sibling}

== OBLIGATION ==
{obligation}

{registry}

== FILE IMPORTS ==
{imports}

Use ONLY lemmas from the proven registry above. Their names and signatures are exact.
Return ONLY the proof body content (between {{ and }}).
"""


def build_b4_prompt(fid, obligation, sibling, imports):
    """B4: Sibling + imports + strategy + registry + spec definitions."""
    hint = STRATEGY_HINTS.get(fid, "")
    registry = PROVEN_LEMMA_REGISTRY.get(fid, "")
    specs = SPEC_DEFINITIONS.get(fid, "")
    return f"""{hint}

== SIBLING PROOF (adapt this approach) ==
{sibling}

== OBLIGATION ==
{obligation}

{registry}

{specs}

== FILE IMPORTS ==
{imports}

Follow the strategy hint. Use ONLY lemmas from the proven registry.
Return ONLY the proof body content (between {{ and }}).
"""


VARIANT_BUILDERS = {
    "B1": build_b1_prompt,
    "B2": build_b2_prompt,
    "B3": build_b3_prompt,
    "B4": build_b4_prompt,
}


if __name__ == "__main__":
    # Load the 18a extracted context (obligations, siblings, imports)
    with open("/root/dalek-lite/experiment_results/exp18a/prompts.json") as f:
        context_18a = json.load(f)

    # Extract obligations and siblings from 18a V2 (sibling-first) prompts
    # We need to parse them out
    func_ids = ["F1_easy", "F2_easy", "F3_medium", "F4_medium", "F5_hard", "F6_hard"]

    for fid in func_ids:
        # Use the v1 prompt from 18a and extract sections
        v1_prompt = context_18a[fid]["prompts"]["v1_obligation_first"]

        # Parse out obligation (between [OBLIGATION] and [CONTEXT])
        parts = v1_prompt.split("[CONTEXT]")
        obligation_part = parts[0].replace("[OBLIGATION]\nProve this Verus proof function:\n\n", "").strip()

        # Parse out sibling (between [SIBLING] and [INSTRUCTION])
        if "[SIBLING]" in v1_prompt:
            sibling_part = v1_prompt.split("[SIBLING]")[1].split("[INSTRUCTION]")[0].strip()
            sibling_part = sibling_part.replace("Here are nearby proof functions from the same file:\n\n", "").strip()
        else:
            sibling_part = "No sibling available."

        # Parse out imports — just use the file imports from context
        imports_part = "// See file imports in context above"

        # Build all 4 variant prompts
        for vname, builder in VARIANT_BUILDERS.items():
            prompt = builder(fid, obligation_part, sibling_part, imports_part)
            path = f"{RESULTS_DIR}/prompts/{fid}_{vname}.txt"
            with open(path, 'w') as f:
                f.write(prompt)

    # Print summary
    for fid in func_ids:
        for v in ["B1", "B2", "B3", "B4"]:
            path = f"{RESULTS_DIR}/prompts/{fid}_{v}.txt"
            size = os.path.getsize(path)
            print(f"{fid}_{v}: {size} bytes")

    print(f"\nTotal: {len(func_ids) * 4} prompts generated")
