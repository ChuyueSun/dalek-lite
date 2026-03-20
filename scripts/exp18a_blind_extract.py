#!/usr/bin/env python3
"""
Exp 18a: Blind context extraction for prompt structure testing.

This script MECHANICALLY extracts context for proof generation prompts.
No human curation of lemma lists or sibling selection.

Protocol:
1. Given a function name + file, extract the signature (requires/ensures)
2. Replace the proof body with admit() to create a hole
3. Extract ALL pub proof/spec fn signatures from imported modules
4. Select siblings by file proximity (nearest 2 proof fns)
5. Output structured context for prompt assembly
"""

import re
import os
import json
import subprocess
import sys

DALEK_SRC = "/root/dalek-lite/curve25519-dalek/src"

# ============================================================================
# Test functions - just names and files, NO GT knowledge encoded
# ============================================================================
TEST_FUNCTIONS = [
    {
        "id": "F1_easy",
        "function": "lemma_negation_preserves_curve",
        "file": "lemmas/edwards_lemmas/curve_equation_lemmas.rs",
        "difficulty": "easy",
        "verify_module": "lemmas::edwards_lemmas::curve_equation_lemmas",
    },
    {
        "id": "F2_easy",
        "function": "lemma_field_mul_distributes_over_add",
        "file": "lemmas/field_lemmas/field_algebra_lemmas.rs",
        "difficulty": "easy",
        "verify_module": "lemmas::field_lemmas::field_algebra_lemmas",
    },
    {
        "id": "F3_medium",
        "function": "lemma_field51_add",
        "file": "lemmas/field_lemmas/add_lemmas.rs",
        "difficulty": "medium",
        "verify_module": "lemmas::field_lemmas::add_lemmas",
    },
    {
        "id": "F4_medium",
        "function": "lemma_from_bytes_as_bytes_roundtrip",
        "file": "lemmas/field_lemmas/as_bytes_lemmas.rs",
        "difficulty": "medium",
        "verify_module": "lemmas::field_lemmas::as_bytes_lemmas",
    },
    {
        "id": "F5_hard",
        "function": "lemma_naf_even_step",
        "file": "lemmas/scalar_lemmas_/naf_lemmas.rs",
        "difficulty": "hard",
        "verify_module": "lemmas::scalar_lemmas_::naf_lemmas",
    },
    {
        "id": "F6_hard",
        "function": "lemma_carry_preserves_reconstruction",
        "file": "lemmas/scalar_lemmas_/radix16_lemmas.rs",
        "difficulty": "hard",
        "verify_module": "lemmas::scalar_lemmas_::radix16_lemmas",
    },
]


def find_function_range(filepath, fn_name):
    """Find the line range of a proof function (signature start to closing brace).

    Returns (sig_start, body_start, body_end) as 0-indexed line numbers.
    sig_start: first line of the function (pub proof fn ...)
    body_start: the line with the opening { of the body
    body_end: the line with the closing } of the body
    """
    with open(filepath) as f:
        lines = f.readlines()

    # Find the function declaration
    fn_line = None
    for i, line in enumerate(lines):
        if f"fn {fn_name}(" in line or f"fn {fn_name} (" in line:
            fn_line = i
            break

    if fn_line is None:
        raise ValueError(f"Function {fn_name} not found in {filepath}")

    # Find the opening { of the body (after requires/ensures)
    # We need to find the { that starts the body, not one inside requires/ensures
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


def extract_signature(filepath, fn_name):
    """Extract function signature (everything from fn declaration to opening {, exclusive)."""
    with open(filepath) as f:
        lines = f.readlines()

    fn_line, body_start, _ = find_function_range(filepath, fn_name)

    # Collect lines from fn_line to body_start (inclusive of body_start line, up to {)
    sig_lines = []
    for i in range(fn_line, body_start + 1):
        line = lines[i]
        # For the body_start line, only include up to (but not including) the {
        if i == body_start:
            brace_pos = line.index('{')
            if brace_pos > 0 and line[:brace_pos].strip():
                sig_lines.append(line[:brace_pos].rstrip())
        else:
            sig_lines.append(line.rstrip())

    return '\n'.join(sig_lines)


def extract_body(filepath, fn_name):
    """Extract the proof body (between { and })."""
    with open(filepath) as f:
        lines = f.readlines()

    _, body_start, body_end = find_function_range(filepath, fn_name)

    # Body is lines between body_start and body_end (exclusive of the braces themselves)
    body_lines = []
    for i in range(body_start + 1, body_end):
        body_lines.append(lines[i].rstrip())

    return '\n'.join(body_lines)


def extract_doc_comments(filepath, fn_name):
    """Extract doc comments (///) immediately before the function."""
    with open(filepath) as f:
        lines = f.readlines()

    fn_line, _, _ = find_function_range(filepath, fn_name)

    doc_lines = []
    i = fn_line - 1
    while i >= 0 and (lines[i].strip().startswith('///') or lines[i].strip().startswith('// ')):
        doc_lines.insert(0, lines[i].rstrip())
        i -= 1

    return '\n'.join(doc_lines)


def find_all_proof_fns(filepath):
    """Find all pub proof fn declarations in a file. Returns [(name, line_num)]."""
    with open(filepath) as f:
        lines = f.readlines()

    fns = []
    for i, line in enumerate(lines):
        m = re.match(r'\s*pub\s+proof\s+fn\s+(\w+)', line)
        if m:
            fns.append((m.group(1), i))

    # Also catch `proof fn` without pub
    for i, line in enumerate(lines):
        m = re.match(r'\s*proof\s+fn\s+(\w+)', line)
        if m and m.group(1) not in [f[0] for f in fns]:
            fns.append((m.group(1), i))

    return sorted(fns, key=lambda x: x[1])


def get_nearest_siblings(filepath, fn_name, n=2):
    """Get the N nearest proof functions (by line number) as siblings.

    Returns full function bodies (signature + body) for the nearest N.
    """
    all_fns = find_all_proof_fns(filepath)

    # Find our function's position
    target_line = None
    for name, line in all_fns:
        if name == fn_name:
            target_line = line
            break

    if target_line is None:
        return []

    # Sort by distance from target
    candidates = [(name, line) for name, line in all_fns if name != fn_name]
    candidates.sort(key=lambda x: abs(x[1] - target_line))

    siblings = []
    with open(filepath) as f:
        content = f.read()
        lines = content.split('\n')

    for name, _ in candidates[:n]:
        try:
            sig_start, body_start, body_end = find_function_range(filepath, name)
            # Also grab doc comments
            doc_start = sig_start
            i = sig_start - 1
            while i >= 0 and (lines[i].strip().startswith('///') or lines[i].strip().startswith('// ')):
                doc_start = i
                i -= 1

            sibling_text = '\n'.join(lines[doc_start:body_end + 1])
            siblings.append({"name": name, "text": sibling_text})
        except (ValueError, IndexError):
            continue

    return siblings


def extract_imports(filepath):
    """Extract all use/import lines from a file."""
    with open(filepath) as f:
        lines = f.readlines()

    imports = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith('use ') or stripped.startswith('pub use '):
            imports.append(stripped)

    return imports


def resolve_import_path(import_line):
    """Convert a use statement to a file path."""
    # Extract the module path from use statement
    # e.g., "use crate::lemmas::field_lemmas::field_algebra_lemmas::*;"
    # -> "lemmas/field_lemmas/field_algebra_lemmas.rs"

    m = re.match(r'(?:pub\s+)?use\s+(?:crate::)?(.+?)(?:::\*|::\{.*?\});', import_line)
    if not m:
        return None

    path = m.group(1)

    # Skip vstd imports
    if path.startswith('vstd::'):
        return None

    # Convert :: to /
    file_path = path.replace('::', '/')

    # Try as a file
    candidate = os.path.join(DALEK_SRC, file_path + '.rs')
    if os.path.exists(candidate):
        return candidate

    # Try as a module directory
    candidate = os.path.join(DALEK_SRC, file_path, 'mod.rs')
    if os.path.exists(candidate):
        return candidate

    return None


def gather_available_lemmas(filepath):
    """Gather ALL pub proof fn and pub spec fn signatures from imported modules.

    This is MECHANICAL - includes everything from imports, no filtering.
    """
    imports = extract_imports(filepath)

    all_sigs = []
    seen_files = set()

    for imp in imports:
        resolved = resolve_import_path(imp)
        if resolved and resolved not in seen_files and resolved != filepath:
            seen_files.add(resolved)
            try:
                with open(resolved) as f:
                    content = f.read()

                # Find all pub proof fn and pub spec fn signatures
                # Match from "pub proof fn" or "pub spec fn" or "pub open spec fn"
                # to the opening {
                pattern = r'(pub\s+(?:proof|(?:open\s+)?spec)\s+fn\s+\w+[^{]*)'
                matches = re.findall(pattern, content, re.DOTALL)

                for match in matches:
                    # Clean up - just get signature (name + params + requires + ensures)
                    # Truncate at reasonable length
                    sig = match.strip()
                    if len(sig) > 500:
                        sig = sig[:500] + '...'
                    all_sigs.append(sig)
            except Exception:
                continue

    # Also include vstd lemma hints (common ones the solver needs)
    vstd_hints = [
        "// From vstd::arithmetic::div_mod:",
        "//   lemma_mod_multiples_vanish(b: int, a: int, n: int) requires n > 0 ensures a % n == (a + b * n) % n",
        "//   lemma_small_mod(x: nat, m: nat) requires x < m ensures x % m == x",
        "//   lemma_mod_twice(x: int, m: int) requires m > 0 ensures (x % m) % m == x % m",
        "//   lemma_add_mod_noop(x: int, y: int, m: int) requires m > 0 ensures (x + y) % m == ((x % m) + (y % m)) % m",
        "//   lemma_mod_pos_bound(x: int, m: int) requires m > 0 ensures 0 <= x % m < m",
        "//   lemma_mod_bound(x: int, m: int) requires m > 0 ensures x % m < m",
        "//   lemma_mod_mod(x: int, a: int, b: int) requires a > 0, b > 0 ensures (x % (a * b)) % a == x % a",
        "//   lemma_mod_breakdown(x: int, a: int, b: int) requires a > 0, b > 0 ensures x % (a * b) == a * ((x / a) % b) + x % a",
        "//   lemma_mod_division_less_than_divisor(x: int, m: int) requires m > 0 ensures x % m < m",
        "",
        "// From vstd::arithmetic::mul:",
        "//   lemma_mul_basics(x: int) ensures x * 0 == 0, 0 * x == 0, x * 1 == x",
        "//   lemma_mul_is_commutative(x: int, y: int) ensures x * y == y * x",
        "//   lemma_mul_is_associative(x: int, y: int, z: int) ensures x * (y * z) == (x * y) * z",
        "//   lemma_mul_is_distributive_add(x: int, y: int, z: int) ensures x * (y + z) == x * y + x * z",
        "//   lemma_mul_mod_noop_left(x: int, y: int, m: int) requires m > 0 ensures (x % m) * y % m == x * y % m",
        "//   lemma_mul_mod_noop_right(x: int, y: int, m: int) requires m > 0 ensures x * (y % m) % m == x * y % m",
        "//   lemma_mul_strict_inequality(x: int, y: int, z: int) requires x < y, z > 0 ensures x * z < y * z",
        "//   lemma_mul_by_zero_is_zero(x: int) ensures x * 0 == 0 && 0 * x == 0",
        "",
        "// From vstd::arithmetic::power2:",
        "//   lemma_pow2_pos(e: nat) ensures pow2(e) > 0",
        "//   lemma_pow2_adds(e1: nat, e2: nat) ensures pow2(e1) * pow2(e2) == pow2(e1 + e2)",
        "//   lemma2_to64() ensures pow2(0)==1, pow2(1)==2, pow2(2)==4, ..., pow2(64)==0x10000000000000000",
    ]

    return all_sigs, vstd_hints


def create_hole(filepath, fn_name):
    """Replace the proof body with admit(). Returns the original body for restoration."""
    with open(filepath) as f:
        lines = f.readlines()

    _, body_start, body_end = find_function_range(filepath, fn_name)

    # Save original
    original_body = lines[body_start:body_end + 1]

    # Get the indentation from body_start line
    indent = '    '  # Default 4 spaces

    # Replace body with admit()
    new_lines = lines[:body_start] + [f'{{\n', f'{indent}admit();\n', f'}}\n'] + lines[body_end + 1:]

    with open(filepath, 'w') as f:
        f.writelines(new_lines)

    return original_body


def restore_body(filepath, fn_name, original_body):
    """Restore the original proof body."""
    with open(filepath) as f:
        lines = f.readlines()

    _, body_start, body_end = find_function_range(filepath, fn_name)

    new_lines = lines[:body_start] + original_body + lines[body_end + 1:]

    with open(filepath, 'w') as f:
        f.writelines(new_lines)


def insert_proof(filepath, fn_name, proof_body):
    """Insert a generated proof body into the function."""
    with open(filepath) as f:
        lines = f.readlines()

    _, body_start, body_end = find_function_range(filepath, fn_name)

    # Create the new body
    new_body = [f'{{\n', proof_body.rstrip() + '\n', f'}}\n']

    new_lines = lines[:body_start] + new_body + lines[body_end + 1:]

    with open(filepath, 'w') as f:
        f.writelines(new_lines)


def verify_function(module_path, timeout=120):
    """Run targeted Verus verification. Returns (success, output)."""
    cmd = f"cargo verus verify -p curve25519-dalek -- --verify-module {module_path}"
    try:
        result = subprocess.run(
            cmd, shell=True, capture_output=True, text=True,
            timeout=timeout, cwd="/root/dalek-lite"
        )
        output = result.stdout + result.stderr
        success = "0 errors" in output and "error" not in output.split("verification results")[-1].lower().split("0 errors")[0]
        # More reliable check
        m = re.search(r'(\d+) verified, (\d+) errors', output)
        if m:
            success = int(m.group(2)) == 0
        else:
            success = False
        return success, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"


def build_prompt_variant1(obligation, doc_comments, available_lemmas, vstd_hints, siblings):
    """Variant 1: Obligation-first"""
    prompt = "[OBLIGATION]\nProve this Verus proof function:\n\n"
    if doc_comments:
        prompt += doc_comments + "\n"
    prompt += obligation + "\n\n"

    prompt += "[CONTEXT]\nAvailable lemmas from imported modules:\n\n"
    for sig in available_lemmas[:60]:  # Cap at 60 to avoid token overflow
        prompt += sig + "\n\n"
    prompt += "\n".join(vstd_hints) + "\n\n"

    if siblings:
        prompt += "[SIBLING]\nHere are nearby proof functions from the same file:\n\n"
        for sib in siblings:
            prompt += sib["text"] + "\n\n"

    prompt += "[INSTRUCTION]\n"
    prompt += "Write the proof body for the function in [OBLIGATION]. "
    prompt += "Use only lemmas from the available list or from the sibling proofs. "
    prompt += "Return ONLY the proof body content (what goes between { and }), no function signature.\n"

    return prompt


def build_prompt_variant2(obligation, doc_comments, available_lemmas, vstd_hints, siblings):
    """Variant 2: Sibling-first"""
    prompt = ""

    if siblings:
        prompt += "[SIBLING]\nHere are proven proof functions from the same file:\n\n"
        for sib in siblings:
            prompt += sib["text"] + "\n\n"

    prompt += "[OBLIGATION]\nNow prove this similar function:\n\n"
    if doc_comments:
        prompt += doc_comments + "\n"
    prompt += obligation + "\n\n"

    prompt += "[CONTEXT]\nAvailable lemmas from imported modules:\n\n"
    for sig in available_lemmas[:60]:
        prompt += sig + "\n\n"
    prompt += "\n".join(vstd_hints) + "\n\n"

    prompt += "[INSTRUCTION]\n"
    prompt += "Adapt the sibling's approach for this function. "
    prompt += "Return ONLY the proof body content (what goes between { and }), no function signature.\n"

    return prompt


def build_prompt_variant3(obligation, doc_comments, available_lemmas, vstd_hints, siblings):
    """Variant 3: Strategy-first (chain of thought)"""
    prompt = "[OBLIGATION]\n"
    if doc_comments:
        prompt += doc_comments + "\n"
    prompt += obligation + "\n\n"

    prompt += "[CONTEXT]\nAvailable lemmas from imported modules:\n\n"
    for sig in available_lemmas[:60]:
        prompt += sig + "\n\n"
    prompt += "\n".join(vstd_hints) + "\n\n"

    if siblings:
        prompt += "[SIBLING]\nHere are nearby proof functions from the same file:\n\n"
        for sib in siblings:
            prompt += sib["text"] + "\n\n"

    prompt += "[INSTRUCTION]\n"
    prompt += "First, describe your proof strategy in 2-3 sentences.\n"
    prompt += "Then write the proof body.\n"
    prompt += "Format your response as:\nSTRATEGY: <your strategy>\n\nPROOF:\n<proof body code>\n"

    return prompt


def build_prompt_variant4(obligation, doc_comments, available_lemmas, vstd_hints, siblings):
    """Variant 4: Minimal (no siblings)"""
    prompt = "[OBLIGATION]\n"
    if doc_comments:
        prompt += doc_comments + "\n"
    prompt += obligation + "\n\n"

    prompt += "[CONTEXT]\nAvailable lemmas from imported modules:\n\n"
    for sig in available_lemmas[:60]:
        prompt += sig + "\n\n"
    prompt += "\n".join(vstd_hints) + "\n\n"

    prompt += "[INSTRUCTION]\n"
    prompt += "Write the proof body for the function in [OBLIGATION]. "
    prompt += "Use only lemmas from the available list. "
    prompt += "Return ONLY the proof body content (what goes between { and }), no function signature.\n"

    return prompt


VARIANT_BUILDERS = {
    "v1_obligation_first": build_prompt_variant1,
    "v2_sibling_first": build_prompt_variant2,
    "v3_strategy_first": build_prompt_variant3,
    "v4_minimal": build_prompt_variant4,
}


def extract_all_context():
    """Extract context for all test functions. MECHANICAL, no curation."""
    results = {}

    for tf in TEST_FUNCTIONS:
        filepath = os.path.join(DALEK_SRC, tf["file"])
        fn_name = tf["function"]

        print(f"Extracting context for {tf['id']}: {fn_name}")

        # Extract signature
        sig = extract_signature(filepath, fn_name)

        # Extract doc comments
        docs = extract_doc_comments(filepath, fn_name)

        # Extract body (GT - stored for restoration, NOT shown to agents)
        body = extract_body(filepath, fn_name)

        # Find nearest siblings
        siblings = get_nearest_siblings(filepath, fn_name, n=2)

        # Gather available lemmas from imports
        available, vstd = gather_available_lemmas(filepath)

        results[tf["id"]] = {
            "id": tf["id"],
            "function": fn_name,
            "file": tf["file"],
            "filepath": filepath,
            "verify_module": tf["verify_module"],
            "difficulty": tf["difficulty"],
            "signature": sig,
            "doc_comments": docs,
            "gt_body": body,
            "gt_body_loc": len([l for l in body.split('\n') if l.strip()]),
            "siblings": siblings,
            "available_lemmas": available,
            "vstd_hints": vstd,
            "sibling_names": [s["name"] for s in siblings],
            "num_available_lemmas": len(available),
        }

        # Build prompts for all 4 variants
        prompts = {}
        for vname, builder in VARIANT_BUILDERS.items():
            prompts[vname] = builder(sig, docs, available, vstd, siblings)
        results[tf["id"]]["prompts"] = prompts

    return results


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python exp18a_blind_extract.py extract     # Extract all context")
        print("  python exp18a_blind_extract.py hole <id>   # Create hole for function")
        print("  python exp18a_blind_extract.py restore <id> # Restore original")
        print("  python exp18a_blind_extract.py verify <id> # Verify module")
        print("  python exp18a_blind_extract.py prompt <id> <variant> # Print prompt")
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "extract":
        ctx = extract_all_context()

        # Save context (without GT bodies) to file
        output = {}
        for k, v in ctx.items():
            output[k] = {
                "id": v["id"],
                "function": v["function"],
                "file": v["file"],
                "difficulty": v["difficulty"],
                "gt_body_loc": v["gt_body_loc"],
                "sibling_names": v["sibling_names"],
                "num_available_lemmas": v["num_available_lemmas"],
            }

        print(json.dumps(output, indent=2))

        # Save full context (including prompts) for experiment use
        # Strip GT bodies from saved prompts file
        prompt_output = {}
        for k, v in ctx.items():
            prompt_output[k] = {
                "id": v["id"],
                "function": v["function"],
                "verify_module": v["verify_module"],
                "filepath": v["filepath"],
                "prompts": v["prompts"],
            }

        with open("/root/dalek-lite/experiment_results/exp18a/prompts.json", 'w') as f:
            json.dump(prompt_output, f, indent=2)

        print(f"\nPrompts saved to experiment_results/exp18a/prompts.json")

    elif cmd == "hole":
        func_id = sys.argv[2]
        tf = next(t for t in TEST_FUNCTIONS if t["id"] == func_id)
        filepath = os.path.join(DALEK_SRC, tf["file"])
        original = create_hole(filepath, tf["function"])
        # Save original for restoration
        backup_path = f"/root/dalek-lite/experiment_results/exp18a/{func_id}_backup.txt"
        with open(backup_path, 'w') as f:
            f.writelines(original)
        print(f"Hole created for {func_id}. Backup at {backup_path}")

    elif cmd == "restore":
        func_id = sys.argv[2]
        tf = next(t for t in TEST_FUNCTIONS if t["id"] == func_id)
        filepath = os.path.join(DALEK_SRC, tf["file"])
        backup_path = f"/root/dalek-lite/experiment_results/exp18a/{func_id}_backup.txt"
        with open(backup_path) as f:
            original = f.readlines()
        restore_body(filepath, tf["function"], original)
        print(f"Restored {func_id}")

    elif cmd == "verify":
        func_id = sys.argv[2]
        tf = next(t for t in TEST_FUNCTIONS if t["id"] == func_id)
        success, output = verify_function(tf["verify_module"])
        print(f"{'PASS' if success else 'FAIL'}: {func_id}")
        if not success:
            # Print relevant error lines
            for line in output.split('\n'):
                if 'error' in line.lower() or 'failed' in line.lower() or 'verification results' in line:
                    print(f"  {line.strip()}")

    elif cmd == "prompt":
        func_id = sys.argv[2]
        variant = sys.argv[3]

        # Load from saved prompts
        with open("/root/dalek-lite/experiment_results/exp18a/prompts.json") as f:
            prompts = json.load(f)

        if func_id in prompts and variant in prompts[func_id]["prompts"]:
            print(prompts[func_id]["prompts"][variant])
        else:
            print(f"Not found: {func_id} / {variant}")

    elif cmd == "insert":
        # Insert a proof body from a file
        func_id = sys.argv[2]
        proof_file = sys.argv[3]
        tf = next(t for t in TEST_FUNCTIONS if t["id"] == func_id)
        filepath = os.path.join(DALEK_SRC, tf["file"])
        with open(proof_file) as f:
            proof_body = f.read()
        insert_proof(filepath, tf["function"], proof_body)
        print(f"Inserted proof for {func_id}")

    else:
        print(f"Unknown command: {cmd}")
