#!/usr/bin/env python3
"""
Exp 18a: Verify generated proofs and record results.

Usage:
    python3 exp18a_verify_and_record.py insert_and_verify <func_id> <proof_file>
    python3 exp18a_verify_and_record.py record <func_id> <variant> <pass/fail> <loc> <notes>
    python3 exp18a_verify_and_record.py restore <func_id>
    python3 exp18a_verify_and_record.py summary
"""

import json
import os
import re
import subprocess
import sys

DALEK_SRC = "/root/dalek-lite/curve25519-dalek/src"
RESULTS_FILE = "/root/dalek-lite/experiment_results/exp18a/results.json"

TEST_FUNCTIONS = {
    "F1_easy": {
        "function": "lemma_negation_preserves_curve",
        "file": "lemmas/edwards_lemmas/curve_equation_lemmas.rs",
        "verify_module": "lemmas::edwards_lemmas::curve_equation_lemmas",
    },
    "F2_easy": {
        "function": "lemma_field_mul_distributes_over_add",
        "file": "lemmas/field_lemmas/field_algebra_lemmas.rs",
        "verify_module": "lemmas::field_lemmas::field_algebra_lemmas",
    },
    "F3_medium": {
        "function": "lemma_field51_add",
        "file": "lemmas/field_lemmas/add_lemmas.rs",
        "verify_module": "lemmas::field_lemmas::add_lemmas",
    },
    "F4_medium": {
        "function": "lemma_from_bytes_as_bytes_roundtrip",
        "file": "lemmas/field_lemmas/as_bytes_lemmas.rs",
        "verify_module": "lemmas::field_lemmas::as_bytes_lemmas",
    },
    "F5_hard": {
        "function": "lemma_naf_even_step",
        "file": "lemmas/scalar_lemmas_/naf_lemmas.rs",
        "verify_module": "lemmas::scalar_lemmas_::naf_lemmas",
    },
    "F6_hard": {
        "function": "lemma_carry_preserves_reconstruction",
        "file": "lemmas/scalar_lemmas_/radix16_lemmas.rs",
        "verify_module": "lemmas::scalar_lemmas_::radix16_lemmas",
    },
}


def find_function_range(filepath, fn_name):
    with open(filepath) as f:
        lines = f.readlines()
    fn_line = None
    for i, line in enumerate(lines):
        if f"fn {fn_name}(" in line or f"fn {fn_name} (" in line:
            fn_line = i
            break
    if fn_line is None:
        raise ValueError(f"Function {fn_name} not found in {filepath}")
    brace_depth = 0
    body_start = None
    for i in range(fn_line, len(lines)):
        for ch in lines[i]:
            if ch == '{':
                brace_depth += 1
                if brace_depth == 1:
                    body_start = i
            elif ch == '}':
                brace_depth -= 1
                if brace_depth == 0 and body_start is not None:
                    return fn_line, body_start, i
    raise ValueError(f"Could not find body bounds for {fn_name}")


def insert_proof(func_id, proof_file):
    """Insert a proof body from a file, replacing the current body."""
    tf = TEST_FUNCTIONS[func_id]
    filepath = os.path.join(DALEK_SRC, tf["file"])
    fn_name = tf["function"]

    with open(proof_file) as f:
        proof_body = f.read()

    with open(filepath) as f:
        lines = f.readlines()

    _, body_start, body_end = find_function_range(filepath, fn_name)

    proof_lines = proof_body.strip().split('\n')

    # Check if the proof already has indentation (first non-empty line starts with spaces)
    first_nonempty = next((l for l in proof_lines if l.strip()), '')
    already_indented = first_nonempty.startswith('    ') or first_nonempty.startswith('\t')

    if already_indented:
        formatted_body = '\n'.join(proof_lines)
    else:
        formatted_body = '\n'.join('    ' + line if line.strip() else line for line in proof_lines)

    new_lines = lines[:body_start] + ['{\n', formatted_body + '\n', '}\n'] + lines[body_end + 1:]

    with open(filepath, 'w') as f:
        f.writelines(new_lines)

    # Count non-empty lines
    loc = len([l for l in proof_lines if l.strip()])
    return loc


def verify(func_id, timeout=180):
    """Run Verus verification. Returns (success, error_summary)."""
    tf = TEST_FUNCTIONS[func_id]
    cmd = f"cargo verus verify -p curve25519-dalek -- --verify-module {tf['verify_module']}"
    try:
        result = subprocess.run(
            cmd, shell=True, capture_output=True, text=True,
            timeout=timeout, cwd="/root/dalek-lite"
        )
        output = result.stdout + result.stderr
        m = re.search(r'(\d+) verified, (\d+) errors', output)
        if m:
            success = int(m.group(2)) == 0
        else:
            success = False

        # Extract error summary
        error_lines = []
        for line in output.split('\n'):
            if 'error' in line.lower() and 'warning' not in line.lower():
                error_lines.append(line.strip())
            if 'failed this' in line.lower():
                error_lines.append(line.strip())
        error_summary = '\n'.join(error_lines[:5]) if error_lines else ""

        return success, error_summary
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"


def restore_hole(func_id):
    """Restore the function to admit() state."""
    tf = TEST_FUNCTIONS[func_id]
    filepath = os.path.join(DALEK_SRC, tf["file"])
    fn_name = tf["function"]

    with open(filepath) as f:
        lines = f.readlines()

    _, body_start, body_end = find_function_range(filepath, fn_name)
    new_lines = lines[:body_start] + ['{\n', '    admit();\n', '}\n'] + lines[body_end + 1:]

    with open(filepath, 'w') as f:
        f.writelines(new_lines)


def load_results():
    if os.path.exists(RESULTS_FILE):
        with open(RESULTS_FILE) as f:
            return json.load(f)
    return {}


def save_results(results):
    with open(RESULTS_FILE, 'w') as f:
        json.dump(results, f, indent=2)


if __name__ == "__main__":
    cmd = sys.argv[1]

    if cmd == "insert_and_verify":
        func_id = sys.argv[2]
        proof_file = sys.argv[3]
        loc = insert_proof(func_id, proof_file)
        print(f"Inserted {loc} LOC proof for {func_id}")
        success, errors = verify(func_id)
        print(f"Result: {'PASS' if success else 'FAIL'}")
        if errors:
            print(f"Errors:\n{errors}")
        # Restore hole
        restore_hole(func_id)
        print(f"Restored hole for {func_id}")
        # Output machine-readable result
        print(f"RESULT:{func_id}:{'pass' if success else 'fail'}:{loc}")

    elif cmd == "record":
        func_id = sys.argv[2]
        variant = sys.argv[3]
        result = sys.argv[4]
        loc = int(sys.argv[5]) if len(sys.argv) > 5 else 0
        notes = sys.argv[6] if len(sys.argv) > 6 else ""

        results = load_results()
        key = f"{func_id}_{variant}"
        results[key] = {
            "func_id": func_id,
            "variant": variant,
            "result": result,
            "loc": loc,
            "notes": notes,
        }
        save_results(results)
        print(f"Recorded: {key} = {result}")

    elif cmd == "restore":
        func_id = sys.argv[2]
        restore_hole(func_id)
        print(f"Restored hole for {func_id}")

    elif cmd == "summary":
        results = load_results()
        if not results:
            print("No results yet.")
            sys.exit(0)

        variants = ["v1_obligation_first", "v2_sibling_first", "v3_strategy_first", "v4_minimal"]
        func_ids = ["F1_easy", "F2_easy", "F3_medium", "F4_medium", "F5_hard", "F6_hard"]

        print(f"{'Function':<15} {'v1_oblg':<10} {'v2_sibl':<10} {'v3_strt':<10} {'v4_mini':<10}")
        print("-" * 55)
        for fid in func_ids:
            row = f"{fid:<15}"
            for v in variants:
                key = f"{fid}_{v}"
                if key in results:
                    r = results[key]
                    row += f" {r['result']:<10}"
                else:
                    row += f" {'---':<10}"
            print(row)

        # Per-variant stats
        print("\n--- Per-variant stats ---")
        for v in variants:
            passes = sum(1 for fid in func_ids if f"{fid}_{v}" in results and results[f"{fid}_{v}"]["result"] == "pass")
            total = sum(1 for fid in func_ids if f"{fid}_{v}" in results)
            avg_loc = 0
            if total > 0:
                locs = [results[f"{fid}_{v}"]["loc"] for fid in func_ids if f"{fid}_{v}" in results and results[f"{fid}_{v}"]["result"] == "pass"]
                avg_loc = sum(locs) / len(locs) if locs else 0
            print(f"{v}: {passes}/{total} pass, avg_loc={avg_loc:.0f}")

    else:
        print(f"Unknown command: {cmd}")
