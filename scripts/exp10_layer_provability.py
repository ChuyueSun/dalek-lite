#!/usr/bin/env python3
"""Experiment 10: Incremental Layer Provability

Validates that proofs at layer N only use lemmas from layers 0..N-1 (plus vstd).
Checks actual function calls in proof bodies, not just file-level imports.
"""

import json
import os
import re
from collections import defaultdict
from pathlib import Path

BASE = Path("/root/dalek-lite/curve25519-dalek/src")
LEMMA_DIR = BASE / "lemmas"

# Define layers by domain directory
# Layer 0: vstd (external)
# Layer 1: common_lemmas
# Layer 2: field_lemmas
# Layer 3: scalar_byte_lemmas, scalar_lemmas_ (scalar support)
# Layer 4: scalar_lemmas (top-level scalar files)
# Layer 5: edwards_lemmas
# Layer 6: ristretto_lemmas
# Layer 7: montgomery_lemmas, montgomery_curve_lemmas, montgomery_pow_chain_lemmas

LAYER_MAP = {
    "common_lemmas": 1,
    "field_lemmas": 2,
    "scalar_byte_lemmas": 3,
    "scalar_lemmas_": 3,
    "scalar_lemmas": 4,  # top-level scalar files
    "scalar_lemmas_extra": 4,
    "scalar_montgomery_lemmas": 4,
    "scalar_batch_invert_lemmas": 4,
    "edwards_lemmas": 5,
    "ristretto_lemmas": 6,
    "montgomery_lemmas": 7,
    "montgomery_curve_lemmas": 7,
    "montgomery_pow_chain_lemmas": 7,
}


def get_layer_for_file(filepath):
    """Determine which layer a file belongs to."""
    filepath = str(filepath)

    # Check directory-based layers
    for key, layer in LAYER_MAP.items():
        if f"/{key}/" in filepath or f"/{key}.rs" in filepath:
            return layer

    # Top-level lemma files
    fname = Path(filepath).stem
    if fname in LAYER_MAP:
        return LAYER_MAP[fname]

    return -1  # Unknown


def get_layer_name(layer_num):
    names = {
        0: "vstd",
        1: "common_lemmas",
        2: "field_lemmas",
        3: "scalar_byte/support_lemmas",
        4: "scalar_lemmas",
        5: "edwards_lemmas",
        6: "ristretto_lemmas",
        7: "montgomery_lemmas",
    }
    return names.get(layer_num, f"layer_{layer_num}")


def find_all_lemma_files():
    """Find all .rs files in src/lemmas/ (excluding mod.rs)."""
    files = []
    for p in LEMMA_DIR.rglob("*.rs"):
        if p.name == "mod.rs":
            continue
        files.append(p)
    return sorted(files)


def build_lemma_index(lemma_files):
    """Build an index: lemma_name -> (file, layer)."""
    index = {}
    for f in lemma_files:
        text = f.read_text()
        layer = get_layer_for_file(f)

        # Find all proof fn declarations
        for m in re.finditer(r'(?:pub\s+)?proof\s+fn\s+(\w+)', text):
            fn_name = m.group(1)
            index[fn_name] = {
                "file": str(f.relative_to(BASE)),
                "layer": layer,
                "layer_name": get_layer_name(layer),
            }

    return index


def extract_proof_fns_with_calls(lemma_files):
    """Extract proof functions and their lemma calls from bodies."""
    results = []

    for f in lemma_files:
        text = f.read_text()
        lines = text.split('\n')
        layer = get_layer_for_file(f)

        # Find proof fn declarations and their bodies
        i = 0
        while i < len(lines):
            line = lines[i]
            match = re.match(r'\s*(?:pub\s+)?proof\s+fn\s+(\w+)', line)
            if match:
                fn_name = match.group(1)
                fn_start = i

                # Find the body opening brace
                j = i
                brace_depth = 0
                body_start = -1
                while j < len(lines):
                    for ch in lines[j]:
                        if ch == '{':
                            brace_depth += 1
                            if brace_depth == 1 and body_start < 0:
                                body_start = j
                        elif ch == '}':
                            brace_depth -= 1
                            if brace_depth == 0 and body_start >= 0:
                                # End of function
                                body_lines = lines[body_start:j + 1]
                                body_text = '\n'.join(body_lines)

                                # Extract lemma calls
                                lemma_calls = set()
                                for bl in body_lines:
                                    bs = bl.strip()
                                    if bs.startswith('//'):
                                        continue
                                    # Match lemma_xxx( calls
                                    for lm in re.finditer(r'(lemma_\w+)\s*[\(<:]', bs):
                                        lemma_calls.add(lm.group(1))
                                    # Match reveal(xxx) calls
                                    for lm in re.finditer(r'reveal\s*\(\s*(\w+)', bs):
                                        lemma_calls.add(f"reveal_{lm.group(1)}")
                                    # Match other proof fn calls (not starting with lemma_)
                                    for lm in re.finditer(r'(p_gt_\d+|assert_bit_vector|assert_bitvector)\s*\(', bs):
                                        lemma_calls.add(lm.group(1))

                                results.append({
                                    "name": fn_name,
                                    "file": str(f.relative_to(BASE)),
                                    "layer": layer,
                                    "layer_name": get_layer_name(layer),
                                    "lemma_calls": sorted(lemma_calls),
                                })
                                i = j
                                break
                    else:
                        j += 1
                        continue
                    break

            i += 1

    return results


def main():
    lemma_files = find_all_lemma_files()
    print(f"Found {len(lemma_files)} lemma files")

    # Build index of all known lemmas
    lemma_index = build_lemma_index(lemma_files)
    print(f"Indexed {len(lemma_index)} proof functions")

    # Extract proof fns with their calls
    proof_fns = extract_proof_fns_with_calls(lemma_files)
    print(f"Extracted {len(proof_fns)} proof functions with call info")

    # Analyze layer dependencies
    total_lemma_calls = 0
    calls_same_layer = 0
    calls_lower_layer = 0
    calls_higher_layer = 0
    calls_vstd = 0
    calls_unknown = 0
    violations = []

    layer_stats = defaultdict(lambda: {"proof_fns": 0, "all_deps_satisfied": True, "violations": []})

    for pfn in proof_fns:
        caller_layer = pfn["layer"]
        layer_stats[caller_layer]["proof_fns"] += 1

        for call in pfn["lemma_calls"]:
            total_lemma_calls += 1

            # Skip reveal calls
            if call.startswith("reveal_"):
                calls_vstd += 1  # Treat reveals as neutral
                continue

            # Look up the callee
            if call in lemma_index:
                callee_info = lemma_index[call]
                callee_layer = callee_info["layer"]

                if callee_layer == caller_layer:
                    calls_same_layer += 1
                elif callee_layer < caller_layer:
                    calls_lower_layer += 1
                else:
                    calls_higher_layer += 1
                    violation = {
                        "caller": pfn["name"],
                        "caller_file": pfn["file"],
                        "caller_layer": caller_layer,
                        "caller_layer_name": pfn["layer_name"],
                        "callee": call,
                        "callee_file": callee_info["file"],
                        "callee_layer": callee_layer,
                        "callee_layer_name": callee_info["layer_name"],
                        "severity": "hard_violation",
                    }
                    violations.append(violation)
                    layer_stats[caller_layer]["all_deps_satisfied"] = False
                    layer_stats[caller_layer]["violations"].append(f"{pfn['name']} -> {call}")
            else:
                # Not in our index - likely vstd or utility
                calls_vstd += 1

    # Build layer self-sufficiency report
    layer_self_sufficiency = {}
    for layer_num in sorted(set(pfn["layer"] for pfn in proof_fns)):
        stats = layer_stats[layer_num]
        layer_self_sufficiency[get_layer_name(layer_num)] = {
            "layer_number": layer_num,
            "proof_fns": stats["proof_fns"],
            "all_deps_satisfied_by_lower_or_same": stats["all_deps_satisfied"],
            "violation_count": len(stats["violations"]),
            "violations": stats["violations"][:5],  # First 5
        }

    result = {
        "total_proof_fns": len(proof_fns),
        "total_lemma_calls": total_lemma_calls,
        "calls_to_same_layer": calls_same_layer,
        "calls_to_lower_layer": calls_lower_layer,
        "calls_to_higher_layer": calls_higher_layer,
        "calls_to_vstd_or_unknown": calls_vstd,
        "violations": violations[:50],  # First 50
        "total_violations": len(violations),
        "layer_self_sufficiency": layer_self_sufficiency,
    }

    out_path = "/root/dalek-lite/experiment_results/exp10_layer_provability.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    print(f"\nResults written to {out_path}")
    print(f"\nTotal proof fns: {len(proof_fns)}")
    print(f"Total lemma calls: {total_lemma_calls}")
    print(f"  Same layer: {calls_same_layer}")
    print(f"  Lower layer: {calls_lower_layer}")
    print(f"  Higher layer (VIOLATIONS): {calls_higher_layer}")
    print(f"  vstd/unknown: {calls_vstd}")
    print(f"\nTotal violations: {len(violations)}")
    if violations:
        print("Sample violations:")
        for v in violations[:5]:
            print(f"  {v['caller']} (L{v['caller_layer']}) -> {v['callee']} (L{v['callee_layer']})")

    print(f"\nLayer self-sufficiency:")
    for name, data in sorted(layer_self_sufficiency.items(), key=lambda x: x[1]["layer_number"]):
        status = "OK" if data["all_deps_satisfied_by_lower_or_same"] else f"VIOLATIONS ({data['violation_count']})"
        print(f"  {name}: {data['proof_fns']} proof fns - {status}")


if __name__ == "__main__":
    main()
