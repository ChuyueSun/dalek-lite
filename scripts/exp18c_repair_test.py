#!/usr/bin/env python3
"""
Exp 18c: Repair Prompt Testing

Tests 4 repair prompt variants against 10 Exp 13 error scenarios.
Groups:
  A (direct, 7 tests): C1 vs C2 vs C3
  B (misleading, 2 tests): C1 vs C2 vs C4
  C (vague, 1 test): C1 vs C2 vs C3 vs C4
"""

import json
import os
import re
import subprocess
import sys

DALEK_SRC = "/root/dalek-lite/curve25519-dalek/src"
RESULTS_DIR = "/root/dalek-lite/experiment_results/exp18c"

# ============================================================================
# The 10 test scenarios from Exp 13
# Each has: the mutation to apply, the error message, the correct fix
# ============================================================================
TESTS = {
    "T1": {
        "group": "A",
        "error_type": "missing_lemma",
        "file": "backend/serial/u64/field.rs",
        "mutation": "comment out lemma_field51_add(self, _rhs) at line 278",
        "mutation_pattern": "            lemma_field51_add(self, _rhs);",
        "mutation_replacement": "            // lemma_field51_add(self, _rhs); // MUTATION: removed",
        "error_msg": "error: postcondition not satisfied\n   --> curve25519-dalek/src/backend/serial/u64/field.rs:234:13\n    |\n234 |             fe51_as_nat(&output) == fe51_as_nat(self) + fe51_as_nat(_rhs),\n    |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition",
        "verify_module": "backend::serial::u64::field",
        "correct_fix": "uncomment lemma_field51_add(self, _rhs)",
        "dispatch_hint": "postcondition not satisfied → a lemma call is missing. Search for lemmas whose ensures match the failing postcondition (fe51_as_nat equality).",
    },
    "T2": {
        "group": "A",
        "error_type": "missing_lemma",
        "file": "backend/serial/u64/field.rs",
        "mutation": "comment out lemma_neg(self) at line 666",
        "mutation_pattern": "            lemma_neg(self);",
        "mutation_replacement": "            // lemma_neg(self); // MUTATION: removed",
        "error_msg": "error: postcondition not satisfied\n   --> curve25519-dalek/src/backend/serial/u64/field.rs:659:13\n    |\n659 |             fe51_as_canonical_nat(&output) == field_neg(fe51_as_canonical_nat(self)),\n    |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition",
        "verify_module": "backend::serial::u64::field",
        "correct_fix": "uncomment lemma_neg(self)",
        "dispatch_hint": "postcondition not satisfied → a lemma call is missing. Search for lemmas about field_neg or negation.",
    },
    "T3": {
        "group": "A",
        "error_type": "wrong_lemma_arguments",
        "file": "backend/serial/u64/field.rs",
        "mutation": "swap args in lemma_mul_le at line 169",
        "mutation_pattern": "        lemma_mul_le(x as nat, u64::MAX as nat, y as nat, u64::MAX as nat);",
        "mutation_replacement": "        lemma_mul_le(u64::MAX as nat, x as nat, u64::MAX as nat, y as nat);",
        "error_msg": "error: precondition not satisfied\n   --> curve25519-dalek/src/backend/serial/u64/field.rs:169:9\n    |\n169 |         lemma_mul_le(u64::MAX as nat, x as nat, u64::MAX as nat, y as nat);\n    |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n    |         -------- failed precondition",
        "verify_module": "backend::serial::u64::field",
        "correct_fix": "swap args back to (x, u64::MAX, y, u64::MAX)",
        "dispatch_hint": "precondition not satisfied → check argument order. lemma_mul_le requires a <= b and c <= d. Currently passing (u64::MAX, x, u64::MAX, y) but need (x, u64::MAX, y, u64::MAX).",
    },
    "T4": {
        "group": "B",
        "error_type": "wrong_args_type_compatible",
        "file": "backend/serial/u64/field.rs",
        "mutation": "swap first two args of lemma_mod_sum_factor at line 409: (16, x-y, modulus) -> (x-y, 16, modulus)",
        "mutation_pattern": "            lemma_mod_sum_factor(16 as int, x - y, modulus);",
        "mutation_replacement": "            lemma_mod_sum_factor(x - y, 16 as int, modulus);",
        "error_msg": "error: assertion failed\n   --> curve25519-dalek/src/backend/serial/u64/field.rs:432:20\n    |\n432 |               assert(fe51_as_canonical_nat(&output) == field_sub(\n    |  ____________________^\n433 | |                 fe51_as_canonical_nat(self),\n    | |_____________^ assertion failed",
        "verify_module": "backend::serial::u64::field",
        "correct_fix": "swap args back to (16, x-y, modulus)",
        "dispatch_hint": "assertion failed downstream (line 432) but the bug is on line 409. When a lemma proves the wrong fact (type-compatible arg swap), the error appears later.",
    },
    "T5": {
        "group": "B",
        "error_type": "missing_intermediate_assert",
        "file": "backend/serial/u64/field.rs",
        "mutation": "remove assert(output.limbs == [...]) at lines 270-276",
        "mutation_pattern": "            // Trigger the forall invariant\n            assert(output.limbs == [\n                (original_limbs[0] + _rhs.limbs[0]) as u64,\n                (original_limbs[1] + _rhs.limbs[1]) as u64,\n                (original_limbs[2] + _rhs.limbs[2]) as u64,\n                (original_limbs[3] + _rhs.limbs[3]) as u64,\n                (original_limbs[4] + _rhs.limbs[4]) as u64,\n            ]);",
        "mutation_replacement": "            // MUTATION: extensional equality assertion removed",
        "error_msg": "error: postcondition not satisfied\n   --> /root/.cargo/git/checkouts/verus-e4ebf515fa1de14c/88f7396/source/vstd/std_specs/ops.rs:70:25\n    |\n 70 |                         Self::$obeys() ==> ret == self.$spec(rhs);\n    |                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition\n\nerror: postcondition not satisfied\n   --> curve25519-dalek/src/backend/serial/u64/field.rs:233:13\n    |\n233 |             output == spec_add_fe51_limbs(self, _rhs),\n    |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition",
        "verify_module": "backend::serial::u64::field",
        "correct_fix": "re-add the extensional equality assertion for output.limbs",
        "dispatch_hint": "postcondition not satisfied + vstd trait error → an intermediate assertion bridging loop output to struct equality is missing. Add assert(output.limbs == [...]) with explicit limb values.",
    },
    "T6": {
        "group": "A",
        "error_type": "missing_reveal",
        "file": "montgomery.rs",
        "mutation": "comment out reveal(montgomery_ladder_invariant) at line 673",
        "mutation_pattern": "                reveal(montgomery_ladder_invariant);",
        "mutation_replacement": "                // reveal(montgomery_ladder_invariant); // MUTATION: removed",
        "error_msg": "error: assertion failed\n   --> curve25519-dalek/src/montgomery.rs:674:24\n    |\n674 |                 assert(montgomery_ladder_invariant(x0, x1, P, 0, false));\n    |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed",
        "verify_module": "montgomery",
        "correct_fix": "uncomment reveal(montgomery_ladder_invariant)",
        "dispatch_hint": "assertion failed on opaque/closed spec function → add reveal() before the assert. Pattern: assert(opaque_fn(...)) fails → needs reveal(opaque_fn).",
    },
    "T7": {
        "group": "A",
        "error_type": "off_by_one_bounds",
        "file": "backend/serial/u64/field.rs",
        "mutation": "change postcondition from 'fe51_as_nat(&r) < 2 * p()' to 'fe51_as_nat(&r) <= p()'",
        "mutation_pattern": "            fe51_as_nat(&r) < 2 * p(),",
        "mutation_replacement": "            fe51_as_nat(&r) <= p(),",
        "error_msg": "error: postcondition not satisfied\n   --> curve25519-dalek/src/backend/serial/u64/field.rs:871:13\n    |\n871 |               fe51_as_nat(&r) <= p(),\n    |               ^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition",
        "verify_module": "backend::serial::u64::field",
        "correct_fix": "change back to fe51_as_nat(&r) < 2 * p()",
        "dispatch_hint": "postcondition not satisfied on a bounds clause → the bound is too tight. Check if '<=' should be '<' or if the constant needs adjustment (e.g., p() vs 2*p()).",
    },
    "T8": {
        "group": "A",
        "error_type": "wrong_by_strategy",
        "file": "window.rs",
        "mutation": "change by(bit_vector) to by(nonlinear_arith)",
        "mutation_pattern": "            assert((x as i16 >> 7u32) == 0i16 || (x as i16 >> 7u32) == -1i16) by (bit_vector)",
        "mutation_replacement": "            assert((x as i16 >> 7u32) == 0i16 || (x as i16 >> 7u32) == -1i16) by (nonlinear_arith)",
        "error_msg": "error: assertion failed\n   --> curve25519-dalek/src/window.rs:150:20\n    |\n150 |             assert((x as i16 >> 7u32) == 0i16 || (x as i16 >> 7u32) == -1i16) by (nonlinear_arith)\n    |                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed",
        "verify_module": "window",
        "correct_fix": "change by(nonlinear_arith) back to by(bit_vector)",
        "dispatch_hint": "assertion failed with by(nonlinear_arith) on expression with >> (bit shift) → use by(bit_vector) instead. Nonlinear arithmetic cannot reason about bitwise operations.",
    },
    "T9": {
        "group": "A",
        "error_type": "arithmetic_overflow",
        "file": "backend/serial/u64/field.rs",
        "mutation": "comment out lemma_mul_boundary(*a, *b) at line 507",
        "mutation_pattern": "            lemma_mul_boundary(*a, *b);",
        "mutation_replacement": "            // lemma_mul_boundary(*a, *b); // MUTATION: removed",
        "error_msg": "error: possible arithmetic underflow/overflow\n   --> curve25519-dalek/src/backend/serial/u64/field.rs:511:21\n    |\n511 |         let b1_19 = b[1] * 19;\n    |                     ^^^^^^^^^",
        "verify_module": "backend::serial::u64::field",
        "correct_fix": "uncomment lemma_mul_boundary(*a, *b)",
        "dispatch_hint": "possible arithmetic overflow → a bounds-establishing lemma is missing before this line. Search for lemma_*_boundary or lemma_*_bounded that establishes operand bounds.",
    },
    "T10": {
        "group": "C",
        "error_type": "precondition_not_satisfied_vstd",
        "file": "edwards.rs",
        "mutation": "comment out lemma_edwards_d_limbs_bounded() at line 412",
        "mutation_pattern": "            lemma_edwards_d_limbs_bounded();",
        "mutation_replacement": "            // lemma_edwards_d_limbs_bounded(); // MUTATION: removed",
        "error_msg": "error: precondition not satisfied\n   --> curve25519-dalek/src/edwards.rs:416:26\n    |\n416 |         let yy_times_d = &YY * &constants::EDWARDS_D;\n    |                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^\n    |\n   ::: /root/.cargo/git/checkouts/verus-e4ebf515fa1de14c/88f7396/source/vstd/std_specs/ops.rs:68:25\n    |\n 68 |                         self.$req(rhs),\n    |                         -------------- failed precondition",
        "verify_module": "edwards",
        "correct_fix": "uncomment lemma_edwards_d_limbs_bounded()",
        "dispatch_hint": "precondition not satisfied on multiplication → the operand's limb bounds aren't established. For constants like EDWARDS_D, search for a lemma_*_limbs_bounded() that establishes the constant's bounds.",
    },
}

# Sibling fix patterns (for variant C3)
SIBLING_FIXES = {
    "T1": "// Before (failed): postcondition about fe51_as_nat not satisfied\n// Missing lemma call after the loop\n// After (passed):\n//   lemma_field51_add(self, _rhs);  // establishes nat and canonical nat postconditions",
    "T2": "// Before (failed): postcondition about field_neg not satisfied\n// Missing lemma call in proof block\n// After (passed):\n//   lemma_neg(self);  // establishes canonical nat == field_neg",
    "T3": "// Before (failed): precondition of lemma_mul_le not satisfied\n//   lemma_mul_le(u64::MAX, x, u64::MAX, y)  -- WRONG order\n// After (passed):\n//   lemma_mul_le(x, u64::MAX, y, u64::MAX)  -- requires a<=b, c<=d",
    "T6": "// Before (failed): assert(opaque_fn(...)) failed\n// Missing reveal() for opaque spec function\n// After (passed):\n//   reveal(montgomery_ladder_invariant);  // unfold opaque definition before assert",
    "T7": "// Before (failed): postcondition fe51_as_nat(&r) <= p() not satisfied\n// Bound too tight\n// After (passed):\n//   fe51_as_nat(&r) < 2 * p()  // correct bound is 2*p, not p",
    "T8": "// Before (failed): assert with >> using by(nonlinear_arith)\n// Wrong proof strategy for bitwise operations\n// After (passed):\n//   assert(...) by (bit_vector)  // bit shifts need bit_vector, not nonlinear_arith",
    "T9": "// Before (failed): arithmetic overflow on b[1] * 19\n// Missing bounds lemma\n// After (passed):\n//   lemma_mul_boundary(*a, *b);  // establishes that limb values fit in u64",
    "T10": "// Before (failed): precondition of Mul not satisfied for EDWARDS_D\n// Constant's limb bounds not established\n// After (passed):\n//   lemma_edwards_d_limbs_bounded();  // establishes EDWARDS_D has 51-bit limbs",
}


def get_test_variants(test_id):
    """Return which variants to test for a given test."""
    t = TESTS[test_id]
    if t["group"] == "A":
        return ["C1", "C2", "C3"]
    elif t["group"] == "B":
        return ["C1", "C2", "C4"]
    elif t["group"] == "C":
        return ["C1", "C2", "C3", "C4"]


def build_repair_prompt(test_id, variant):
    """Build the repair prompt for a given test × variant."""
    t = TESTS[test_id]

    # Read the relevant source file to get surrounding context
    filepath = os.path.join(DALEK_SRC, t["file"])
    with open(filepath) as f:
        content = f.read()

    # Find the mutation site - handle both single-line and multi-line patterns
    lines = content.split('\n')
    pattern_first_line = t["mutation_pattern"].split('\n')[0].strip()
    mutation_line = None
    for i, line in enumerate(lines):
        if pattern_first_line in line.strip():
            mutation_line = i
            break

    if mutation_line is None:
        # Try the replacement pattern (if already mutated)
        repl_first_line = t["mutation_replacement"].split('\n')[0].strip()
        for i, line in enumerate(lines):
            if repl_first_line in line.strip():
                mutation_line = i
                break

    if mutation_line is None:
        return f"ERROR: Could not find mutation site for {test_id}"

    # Apply mutation to create the mutated version for the prompt
    mutated_content = content.replace(t["mutation_pattern"], t["mutation_replacement"], 1)
    mutated_lines = mutated_content.split('\n')

    # Extract context window around mutation site
    start = max(0, mutation_line - 25)
    end = min(len(mutated_lines), mutation_line + 25)
    mutated_context = '\n'.join(f"{start+i+1:4d}: {mutated_lines[start+i]}" for i in range(end - start))

    prompt = ""

    if variant == "C1":
        prompt = f"""Your proof has an error. Fix it.

== CURRENT CODE (around the error) ==
{mutated_context}

== ERROR ==
{t["error_msg"]}

Fix the error. Return the corrected code for the relevant section."""

    elif variant == "C2":
        prompt = f"""Your proof has an error. Fix it.

== CURRENT CODE (around the error) ==
{mutated_context}

== ERROR ==
{t["error_msg"]}

== ERROR CLASSIFICATION ==
Error type: {t["error_type"]}
Repair hint: {t["dispatch_hint"]}

Fix the error. Return the corrected code for the relevant section."""

    elif variant == "C3":
        sibling = SIBLING_FIXES.get(test_id, "No sibling fix pattern available.")
        prompt = f"""Your proof has an error. Fix it.

== CURRENT CODE (around the error) ==
{mutated_context}

== ERROR ==
{t["error_msg"]}

== SIMILAR FIX PATTERN ==
{sibling}

Apply a similar fix. Return the corrected code for the relevant section."""

    elif variant == "C4":
        prompt = f"""Your proof has an error. Fix it.

== CURRENT CODE (around the error) ==
{mutated_context}

== ERROR ==
{t["error_msg"]}

== IMPORTANT WARNING ==
This error may appear DOWNSTREAM of the actual problem.
The failing line may be correct — the real issue could be:
  1. A lemma call ABOVE the error line with swapped arguments (proving wrong fact)
  2. A missing intermediate assertion BEFORE the failing line
  3. A missing extensional equality (=~=) bridging step

Check ALL lemma calls and assertions ABOVE the error line for correctness.
Fix the proof. Return the corrected code for the relevant section."""

    return prompt


def apply_mutation(test_id):
    """Apply the mutation. Returns True if successful."""
    t = TESTS[test_id]
    filepath = os.path.join(DALEK_SRC, t["file"])
    with open(filepath) as f:
        content = f.read()
    if t["mutation_pattern"] not in content:
        return False
    content = content.replace(t["mutation_pattern"], t["mutation_replacement"], 1)
    with open(filepath, 'w') as f:
        f.write(content)
    return True


def revert_mutation(test_id):
    """Revert the mutation."""
    t = TESTS[test_id]
    filepath = os.path.join(DALEK_SRC, t["file"])
    with open(filepath) as f:
        content = f.read()
    if t["mutation_replacement"] not in content:
        return False
    content = content.replace(t["mutation_replacement"], t["mutation_pattern"], 1)
    with open(filepath, 'w') as f:
        f.write(content)
    return True


if __name__ == "__main__":
    os.makedirs(RESULTS_DIR, exist_ok=True)
    os.makedirs(f"{RESULTS_DIR}/prompts", exist_ok=True)
    os.makedirs(f"{RESULTS_DIR}/fixes", exist_ok=True)

    if len(sys.argv) < 2:
        print("Usage:")
        print("  python exp18c_repair_test.py prepare        # Generate all prompts")
        print("  python exp18c_repair_test.py mutate <test>   # Apply mutation")
        print("  python exp18c_repair_test.py revert <test>   # Revert mutation")
        print("  python exp18c_repair_test.py verify <test>   # Verify module")
        print("  python exp18c_repair_test.py summary         # Show results")
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "prepare":
        all_runs = []
        for tid in sorted(TESTS.keys()):
            variants = get_test_variants(tid)
            for v in variants:
                prompt = build_repair_prompt(tid, v)
                fname = f"{tid}_{v}.txt"
                with open(f"{RESULTS_DIR}/prompts/{fname}", 'w') as f:
                    f.write(prompt)
                all_runs.append(f"{tid}_{v}")
                print(f"  {fname}: {len(prompt)} chars")
        print(f"\nTotal runs: {len(all_runs)}")
        print(f"Prompts saved to {RESULTS_DIR}/prompts/")

    elif cmd == "mutate":
        tid = sys.argv[2]
        if apply_mutation(tid):
            print(f"Mutation applied for {tid}")
        else:
            print(f"ERROR: Could not apply mutation for {tid}")

    elif cmd == "revert":
        tid = sys.argv[2]
        if revert_mutation(tid):
            print(f"Mutation reverted for {tid}")
        else:
            print(f"ERROR: Could not revert mutation for {tid}")

    elif cmd == "verify":
        tid = sys.argv[2]
        t = TESTS[tid]
        cmd_str = f"cargo verus verify -p curve25519-dalek -- --verify-module {t['verify_module']}"
        result = subprocess.run(cmd_str, shell=True, capture_output=True, text=True,
                              timeout=180, cwd="/root/dalek-lite")
        output = result.stdout + result.stderr
        m = re.search(r'(\d+) verified, (\d+) errors', output)
        if m and int(m.group(2)) == 0:
            print(f"PASS: {tid}")
        else:
            print(f"FAIL: {tid}")
            for line in output.split('\n'):
                if 'error' in line.lower() and 'warning' not in line.lower():
                    print(f"  {line.strip()}")

    elif cmd == "summary":
        results_file = f"{RESULTS_DIR}/results.json"
        if os.path.exists(results_file):
            with open(results_file) as f:
                results = json.load(f)

            # Print matrix
            tests_a = ["T1", "T2", "T3", "T6", "T7", "T8", "T9"]
            tests_b = ["T4", "T5"]
            tests_c = ["T10"]

            print("Group A (direct errors):")
            print(f"{'Test':<6} {'C1':<8} {'C2':<8} {'C3':<8}")
            for tid in tests_a:
                row = f"{tid:<6}"
                for v in ["C1", "C2", "C3"]:
                    key = f"{tid}_{v}"
                    r = results.get(key, {}).get("result", "---")
                    row += f" {r:<8}"
                print(row)

            print("\nGroup B (misleading errors):")
            print(f"{'Test':<6} {'C1':<8} {'C2':<8} {'C4':<8}")
            for tid in tests_b:
                row = f"{tid:<6}"
                for v in ["C1", "C2", "C4"]:
                    key = f"{tid}_{v}"
                    r = results.get(key, {}).get("result", "---")
                    row += f" {r:<8}"
                print(row)

            print("\nGroup C (vague errors):")
            print(f"{'Test':<6} {'C1':<8} {'C2':<8} {'C3':<8} {'C4':<8}")
            for tid in tests_c:
                row = f"{tid:<6}"
                for v in ["C1", "C2", "C3", "C4"]:
                    key = f"{tid}_{v}"
                    r = results.get(key, {}).get("result", "---")
                    row += f" {r:<8}"
                print(row)
        else:
            print("No results yet.")
