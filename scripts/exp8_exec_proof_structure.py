#!/usr/bin/env python3
"""Experiment 8: Exec Function Proof Structure Analysis

Parses exec functions with ensures clauses and classifies their proof structure.
"""

import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path

# Source files to analyze
BASE = Path("/root/dalek-lite/curve25519-dalek/src")
SOURCE_FILES = [
    BASE / "backend/serial/u64/field.rs",
    BASE / "backend/serial/u64/scalar.rs",
    BASE / "edwards.rs",
    BASE / "ristretto.rs",
    BASE / "montgomery.rs",
    BASE / "backend/serial/curve_models/mod.rs",
    BASE / "window.rs",
    BASE / "backend/serial/scalar_mul/straus.rs",
    BASE / "backend/serial/scalar_mul/variable_base.rs",
    BASE / "backend/serial/scalar_mul/vartime_double_base.rs",
    BASE / "backend/serial/scalar_mul/pippenger.rs",
    BASE / "backend/serial/scalar_mul/precomputed_straus.rs",
]


def read_file(path):
    if not path.exists():
        return ""
    return path.read_text()


def find_balanced_braces(text, start):
    """Find the end of a balanced brace block starting at `start` (which should point to '{')."""
    depth = 0
    i = start
    while i < len(text):
        if text[i] == '{':
            depth += 1
        elif text[i] == '}':
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return len(text) - 1


def extract_exec_functions(text, filename):
    """Extract exec functions that have ensures clauses."""
    functions = []

    lines = text.split('\n')

    # Find function signatures - look for `fn name(` patterns that are NOT `proof fn` or `spec fn`
    # We need to find exec fns with ensures clauses
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Skip proof fn, spec fn, spec(checked) fn
        if re.match(r'\s*(pub\s+)?(proof|spec(\(checked\))?)\s+fn\s+', line):
            i += 1
            continue

        # Look for fn declarations (exec functions)
        fn_match = re.match(r'\s*(pub(\s*\(crate\))?\s+)?fn\s+(\w+)', line)
        if fn_match:
            fn_name = fn_match.group(3)
            fn_start_line = i

            # Scan forward to find ensures, requires, and the opening brace of the body
            j = i
            has_ensures = False
            has_requires = False
            ensures_lines = []
            ensures_spec_fns = set()
            requires_end = -1
            ensures_start = -1
            ensures_end = -1
            body_start = -1

            # Scan for ensures/requires between fn signature and body
            while j < len(lines):
                sline = lines[j].strip()

                if sline.startswith('requires'):
                    has_requires = True
                elif sline.startswith('ensures'):
                    has_ensures = True
                    ensures_start = j

                # Collect ensures spec function references
                if has_ensures and ensures_start >= 0:
                    ensures_lines.append(sline)
                    # Extract function-like calls in ensures
                    for m in re.finditer(r'(\w+)\s*[\(&\[]', sline):
                        name = m.group(1)
                        if name not in ('self', 'output', 'old', 'true', 'false', 'Some', 'None',
                                       'forall', 'exists', 'implies', 'if', 'else', 'match',
                                       'let', 'fn', 'pub', 'u64', 'u128', 'i64', 'bool', 'usize'):
                            ensures_spec_fns.add(name)

                # Look for the body opening brace - it's the '{' at the right nesting depth
                # after ensures
                if sline == '{' or (sline.endswith('{') and not sline.startswith('//')):
                    # Check if this could be the function body start
                    # Count the depth - we need to be at the function's body brace
                    # Simple heuristic: if we've seen ensures and hit a line that is just '{'
                    # or has `{` after ensures block ends
                    if has_ensures:
                        body_start = j
                        break
                    elif j > i + 1:
                        # No ensures yet but found brace - no ensures clause
                        break

                j += 1

            if not has_ensures or body_start < 0:
                i += 1
                continue

            ensures_loc = body_start - ensures_start if ensures_start >= 0 else 0

            # Now parse the function body to find proof blocks, loops, ghost variables
            # Find the end of the function body
            body_text_start = sum(len(l) + 1 for l in lines[:body_start])
            body_end_idx = find_balanced_braces(text, body_text_start)
            body_end_line = text[:body_end_idx].count('\n')

            body_lines = lines[body_start:body_end_line + 1]
            exec_body_loc = len(body_lines)

            # Extract proof blocks
            proof_blocks = []
            total_proof_loc = 0
            total_lemma_calls = 0
            all_lemma_calls = []
            has_loop = False
            has_loop_invariant = False
            has_ghost_variables = False

            # Simple parser for proof blocks, loops, ghost vars
            k = 0
            in_proof_block = False
            proof_block_start = -1
            proof_depth = 0
            current_proof_lines = []

            for k, bline in enumerate(body_lines):
                bs = bline.strip()

                # Detect loops
                if re.match(r'(for|while|loop)\b', bs):
                    has_loop = True

                # Detect loop invariants
                if 'invariant' in bs and not bs.startswith('//'):
                    has_loop_invariant = True

                # Detect ghost variables
                if re.match(r'(let\s+ghost|ghost\s+let)', bs) or 'Ghost::' in bs:
                    has_ghost_variables = True

                # Detect proof blocks
                if bs.startswith('proof {') or bs == 'proof {' or re.match(r'proof\s*\{', bs):
                    in_proof_block = True
                    proof_depth = 1
                    proof_block_start = k
                    current_proof_lines = [bs]
                    continue

                if in_proof_block:
                    current_proof_lines.append(bs)
                    proof_depth += bs.count('{') - bs.count('}')
                    if proof_depth <= 0:
                        # End of proof block
                        in_proof_block = False
                        block_loc = len(current_proof_lines)
                        total_proof_loc += block_loc

                        # Extract lemma calls from this proof block
                        block_lemma_calls = []
                        block_assertions = 0
                        for pl in current_proof_lines:
                            # Lemma calls: lemma_xxx(...) or reveal(xxx)
                            for lm in re.finditer(r'(lemma_\w+|reveal\w*)\s*[\(<]', pl):
                                call_name = lm.group(1)
                                block_lemma_calls.append(call_name)
                                all_lemma_calls.append(call_name)
                                total_lemma_calls += 1
                            # Also catch reveal() calls
                            for lm in re.finditer(r'reveal\s*\(', pl):
                                if 'reveal' not in [c for c in block_lemma_calls if c == 'reveal']:
                                    block_lemma_calls.append('reveal')
                                    all_lemma_calls.append('reveal')
                                    total_lemma_calls += 1
                            if 'assert' in pl and 'assert_by' not in pl:
                                block_assertions += 1

                        # Determine position
                        position = "inline"
                        if proof_block_start < 5:
                            position = "function_start"
                        elif k > len(body_lines) - 5:
                            position = "function_end"

                        proof_blocks.append({
                            "position": position,
                            "loc": block_loc,
                            "lemma_calls": block_lemma_calls,
                            "assertions": block_assertions,
                        })

            # Classify lemma sources
            lemma_sources = defaultdict(list)
            for lc in set(all_lemma_calls):
                if lc.startswith('reveal'):
                    lemma_sources["reveal_calls"].append(lc)
                elif 'fe51' in lc or 'field' in lc or 'add_lemma' in lc or 'mul_lemma' in lc or 'negate' in lc or 'reduce' in lc or 'pow2k' in lc:
                    lemma_sources["field_lemmas"].append(lc)
                elif 'edwards' in lc or 'decompress' in lc or 'niels' in lc or 'double' in lc:
                    lemma_sources["edwards_lemmas"].append(lc)
                elif 'scalar' in lc or 'montgomery_reduce' in lc or 'radix' in lc:
                    lemma_sources["scalar_lemmas"].append(lc)
                elif 'ristretto' in lc or 'elligator' in lc or 'compress' in lc:
                    lemma_sources["ristretto_lemmas"].append(lc)
                elif 'mod' in lc or 'div' in lc or 'mul' in lc or 'pow' in lc or 'bit' in lc:
                    lemma_sources["common_lemmas"].append(lc)
                elif lc.startswith('lemma_'):
                    # vstd or other
                    lemma_sources["vstd_or_other"].append(lc)
                else:
                    lemma_sources["other"].append(lc)

            unique_lemmas = set(all_lemma_calls)

            fn_info = {
                "function": fn_name,
                "file": str(Path(filename).name),
                "exec_body_loc": exec_body_loc,
                "ensures_loc": ensures_loc,
                "ensures_spec_fns": sorted(ensures_spec_fns),
                "proof_blocks": proof_blocks,
                "has_loop": has_loop,
                "has_loop_invariant": has_loop_invariant,
                "has_ghost_variables": has_ghost_variables,
                "total_proof_loc": total_proof_loc,
                "total_lemma_calls": total_lemma_calls,
                "unique_lemmas_used": len(unique_lemmas),
                "lemma_sources": {k: sorted(v) for k, v in lemma_sources.items()},
            }

            functions.append(fn_info)

        i += 1

    return functions


def classify_structure(fn_info):
    """Classify a function's proof structure."""
    pb = fn_info["proof_blocks"]
    total_proof_loc = fn_info["total_proof_loc"]
    total_lemma_calls = fn_info["total_lemma_calls"]

    if fn_info["has_loop"] and fn_info["has_loop_invariant"]:
        if len(pb) > 3 or total_proof_loc > 100:
            return "complex_loop"
        return "loop_with_invariant"

    if len(pb) == 0:
        return "trivial"

    if len(pb) == 1 and total_proof_loc <= 5 and total_lemma_calls <= 1:
        return "trivial"

    if len(pb) == 1 and total_lemma_calls <= 2:
        return "single_block"

    if len(pb) == 2 and pb[0]["loc"] <= 5:
        return "setup_then_delegate"

    if len(pb) >= 3:
        return "multi_phase"

    if fn_info["has_loop"]:
        return "loop_with_invariant"

    # Check if different proof blocks suggest branching
    if len(pb) >= 2:
        return "branching"

    return "single_block"


def main():
    all_functions = []

    for src_file in SOURCE_FILES:
        if not src_file.exists():
            print(f"  Skipping {src_file} (not found)")
            continue

        text = read_file(src_file)
        fns = extract_exec_functions(text, str(src_file))
        print(f"  {src_file.name}: {len(fns)} exec fns with ensures")
        all_functions.extend(fns)

    # Classify structures
    structure_counts = defaultdict(lambda: {"count": 0, "total_proof_loc": 0, "functions": []})
    lemma_counts = defaultdict(int)

    for fn in all_functions:
        structure = classify_structure(fn)
        fn["structure"] = structure
        structure_counts[structure]["count"] += 1
        structure_counts[structure]["total_proof_loc"] += fn["total_proof_loc"]
        structure_counts[structure]["functions"].append(fn["function"])

        # Lemma distribution
        ul = fn["unique_lemmas_used"]
        if ul == 0:
            lemma_counts["0_lemmas"] += 1
        elif ul <= 2:
            lemma_counts["1_2_lemmas"] += 1
        elif ul <= 5:
            lemma_counts["3_5_lemmas"] += 1
        elif ul <= 10:
            lemma_counts["6_10_lemmas"] += 1
        else:
            lemma_counts["10_plus_lemmas"] += 1

    total = len(all_functions)

    # Build structure distribution
    structure_distribution = {}
    for st, data in sorted(structure_counts.items()):
        avg_loc = data["total_proof_loc"] / data["count"] if data["count"] > 0 else 0
        structure_distribution[st] = {
            "count": data["count"],
            "pct": round(data["count"] / total * 100, 1) if total > 0 else 0,
            "avg_proof_loc": round(avg_loc, 1),
            "functions": data["functions"][:10],  # First 10 examples
        }

    # Lemma discovery budget
    unique_lemma_counts = [fn["unique_lemmas_used"] for fn in all_functions]
    if unique_lemma_counts:
        avg_lemmas = sum(unique_lemma_counts) / len(unique_lemma_counts)
        sorted_counts = sorted(unique_lemma_counts)
        median_lemmas = sorted_counts[len(sorted_counts) // 2]
        max_lemmas = max(unique_lemma_counts)
    else:
        avg_lemmas = median_lemmas = max_lemmas = 0

    # Loop functions
    loop_functions = []
    for fn in all_functions:
        if fn["has_loop_invariant"]:
            complexity = "simple"
            if fn["total_proof_loc"] > 50:
                complexity = "hard"
            elif fn["total_proof_loc"] > 20:
                complexity = "medium"
            loop_functions.append({
                "function": fn["function"],
                "file": fn["file"],
                "total_proof_loc": fn["total_proof_loc"],
                "invariant_complexity": complexity,
            })

    # Proof LOC vs exec LOC
    ratios = []
    proof_exceeds_exec = 0
    for fn in all_functions:
        if fn["exec_body_loc"] > 0:
            ratio = fn["total_proof_loc"] / fn["exec_body_loc"]
            ratios.append(ratio)
            if fn["total_proof_loc"] > fn["exec_body_loc"]:
                proof_exceeds_exec += 1

    avg_ratio = sum(ratios) / len(ratios) if ratios else 0

    result = {
        "total_exec_fns_with_ensures": total,
        "structure_distribution": structure_distribution,
        "lemma_discovery_budget": {
            "avg_unique_lemmas_per_fn": round(avg_lemmas, 1),
            "median_unique_lemmas_per_fn": median_lemmas,
            "max_unique_lemmas_per_fn": max_lemmas,
            "distribution": dict(sorted(lemma_counts.items())),
        },
        "loop_functions": loop_functions,
        "proof_loc_vs_exec_loc": {
            "avg_ratio": round(avg_ratio, 3),
            "functions_where_proof_exceeds_exec": proof_exceeds_exec,
        },
        "all_functions": all_functions,
    }

    out_path = "/root/dalek-lite/experiment_results/exp8_exec_proof_structure.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    print(f"\nResults written to {out_path}")
    print(f"Total exec fns with ensures: {total}")
    print(f"\nStructure distribution:")
    for st, data in sorted(structure_distribution.items()):
        print(f"  {st}: {data['count']} ({data['pct']}%) avg_proof_loc={data['avg_proof_loc']}")
    print(f"\nLemma discovery budget:")
    print(f"  avg={avg_lemmas:.1f}, median={median_lemmas}, max={max_lemmas}")
    print(f"  distribution: {dict(sorted(lemma_counts.items()))}")
    print(f"\nLoop functions: {len(loop_functions)}")
    print(f"Avg proof/exec ratio: {avg_ratio:.3f}")
    print(f"Functions where proof > exec: {proof_exceeds_exec}")


if __name__ == "__main__":
    main()
