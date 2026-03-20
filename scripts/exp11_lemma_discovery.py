#!/usr/bin/env python3
"""Experiment 11: Lemma Discovery from Exec Functions

Validates: can the needed lemmas be predicted from the exec function's ensures clause?
Tests the analogue search hypothesis applied to exec→lemma discovery.
"""

import json
import os
import re
from collections import defaultdict
from pathlib import Path

BASE = Path("/root/dalek-lite/curve25519-dalek/src")

# Source files with exec functions
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

LEMMA_DIR = BASE / "lemmas"


def extract_spec_fns_from_text(text):
    """Extract all function-like identifiers from a text block."""
    spec_fns = set()
    # Match identifiers followed by ( or <
    for m in re.finditer(r'(\w+)\s*[\(<]', text):
        name = m.group(1)
        # Filter out keywords and built-in types
        if name not in ('self', 'output', 'old', 'true', 'false', 'Some', 'None',
                       'forall', 'exists', 'implies', 'if', 'else', 'match', 'let',
                       'fn', 'pub', 'u64', 'u128', 'i64', 'bool', 'usize', 'i32',
                       'as', 'mut', 'return', 'assert', 'proof', 'ensures', 'requires',
                       'invariant', 'Ghost', 'Tracked', 'spec', 'exec', 'open',
                       'for', 'while', 'loop', 'break', 'continue', 'where',
                       'struct', 'enum', 'impl', 'trait', 'type', 'const',
                       'Int', 'Seq', 'Map', 'Set', 'Vec', 'Option', 'Result',
                       'u8', 'u16', 'u32', 'i8', 'i16', 'i128', 'nat', 'int'):
            spec_fns.add(name)
    return spec_fns


def extract_exec_ensures_and_proof_calls(text, filename):
    """For each exec fn with ensures, extract the ensures spec fns and proof block lemma calls."""
    results = []
    lines = text.split('\n')
    i = 0

    while i < len(lines):
        line = lines[i]

        # Skip proof fn, spec fn
        if re.match(r'\s*(pub\s+)?(proof|spec(\(checked\))?)\s+fn\s+', line):
            i += 1
            continue

        fn_match = re.match(r'\s*(pub(\s*\(crate\))?\s+)?fn\s+(\w+)', line)
        if fn_match:
            fn_name = fn_match.group(3)
            fn_start = i

            # Scan for ensures clause
            j = i
            ensures_text = []
            in_ensures = False
            has_ensures = False
            body_start = -1
            brace_depth_header = 0

            while j < min(len(lines), i + 100):
                sline = lines[j].strip()

                if sline.startswith('ensures'):
                    in_ensures = True
                    has_ensures = True
                    ensures_text.append(sline)
                    j += 1
                    continue

                if in_ensures:
                    # ensures block ends at the body opening brace
                    if sline == '{' or (sline.endswith('{') and not sline.startswith('//')):
                        body_start = j
                        in_ensures = False
                        break
                    ensures_text.append(sline)

                if not in_ensures and not has_ensures:
                    if sline == '{' or (sline.endswith('{') and not sline.startswith('//')):
                        body_start = j
                        break

                j += 1

            if not has_ensures or body_start < 0:
                i += 1
                continue

            # Extract spec fns from ensures
            ensures_spec_fns = extract_spec_fns_from_text('\n'.join(ensures_text))

            # Find body end and extract proof block lemma calls
            depth = 0
            k = body_start
            all_lemma_calls = set()
            in_proof = False
            proof_depth = 0

            while k < len(lines):
                for ch_idx, ch in enumerate(lines[k]):
                    if ch == '{':
                        depth += 1
                    elif ch == '}':
                        depth -= 1
                        if depth == 0:
                            k_end = k
                            break

                sline = lines[k].strip()
                if not sline.startswith('//'):
                    # Extract lemma calls from proof blocks
                    if re.match(r'proof\s*\{', sline) or sline == 'proof {':
                        in_proof = True
                        proof_depth = 1

                    if in_proof:
                        for lm in re.finditer(r'(lemma_\w+)\s*[\(<:]', sline):
                            all_lemma_calls.add(lm.group(1))
                        for lm in re.finditer(r'reveal\s*\(\s*(\w+)', sline):
                            all_lemma_calls.add(f"reveal({lm.group(1)})")

                if depth == 0:
                    break
                k += 1

            if all_lemma_calls:
                results.append({
                    "function": fn_name,
                    "file": Path(filename).name,
                    "ensures_spec_fns": sorted(ensures_spec_fns),
                    "lemma_calls": sorted(all_lemma_calls),
                })

        i += 1

    return results


def build_lemma_ensures_index():
    """Build index: lemma_name -> set of spec fns in its ensures clause."""
    index = {}

    for f in LEMMA_DIR.rglob("*.rs"):
        if f.name == "mod.rs":
            continue

        text = f.read_text()
        lines = text.split('\n')
        i = 0

        while i < len(lines):
            match = re.match(r'\s*(?:pub\s+)?proof\s+fn\s+(\w+)', lines[i])
            if match:
                fn_name = match.group(1)

                # Find ensures clause
                j = i + 1
                in_ensures = False
                ensures_text = []
                while j < min(len(lines), i + 50):
                    sline = lines[j].strip()
                    if sline.startswith('ensures'):
                        in_ensures = True
                        ensures_text.append(sline)
                    elif in_ensures:
                        if sline == '{' or (sline.endswith('{') and not sline.startswith('//')):
                            break
                        ensures_text.append(sline)
                    elif sline.startswith('decreases') or sline == '{' or sline.endswith('{'):
                        break
                    j += 1

                spec_fns = extract_spec_fns_from_text('\n'.join(ensures_text))
                index[fn_name] = {
                    "spec_fns": spec_fns,
                    "file": str(f.relative_to(BASE)),
                }

            i += 1

    return index


def main():
    # Build lemma ensures index
    print("Building lemma ensures index...")
    lemma_index = build_lemma_ensures_index()
    print(f"  Indexed {len(lemma_index)} lemmas with ensures spec fns")

    # Extract exec fn data
    print("\nExtracting exec function data...")
    all_exec_fns = []
    for src_file in SOURCE_FILES:
        if not src_file.exists():
            continue
        text = src_file.read_text()
        fns = extract_exec_ensures_and_proof_calls(text, str(src_file))
        print(f"  {src_file.name}: {len(fns)} exec fns with ensures + proof blocks")
        all_exec_fns.extend(fns)

    # Analyze discoverability
    total_lemma_calls = 0
    discoverable = 0
    not_discoverable = 0
    not_discoverable_reasons = defaultdict(int)
    examples_not_discoverable = []

    for fn in all_exec_fns:
        exec_spec_fns = set(fn["ensures_spec_fns"])

        for lemma_call in fn["lemma_calls"]:
            total_lemma_calls += 1

            # Handle reveal() calls
            if lemma_call.startswith("reveal("):
                not_discoverable += 1
                not_discoverable_reasons["reveal_call"] += 1
                continue

            # Look up the lemma's ensures spec fns
            if lemma_call in lemma_index:
                lemma_spec_fns = lemma_index[lemma_call]["spec_fns"]

                # Check overlap
                overlap = exec_spec_fns & lemma_spec_fns
                if overlap:
                    discoverable += 1
                else:
                    not_discoverable += 1
                    # Classify reason
                    if any(kw in lemma_call for kw in ['bounded', 'bound', 'limb', 'range', 'small']):
                        not_discoverable_reasons["utility_lemma_no_spec_overlap"] += 1
                    elif not lemma_spec_fns:
                        not_discoverable_reasons["lemma_has_no_ensures_spec_fns"] += 1
                    else:
                        not_discoverable_reasons["spec_vocabulary_mismatch"] += 1

                    if len(examples_not_discoverable) < 20:
                        examples_not_discoverable.append({
                            "exec_fn": fn["function"],
                            "lemma": lemma_call,
                            "exec_spec_fns": sorted(exec_spec_fns)[:5],
                            "lemma_spec_fns": sorted(lemma_spec_fns)[:5],
                            "reason": "No overlap between exec ensures spec fns and lemma ensures spec fns",
                        })
            else:
                # Not in our index - could be vstd
                not_discoverable += 1
                if lemma_call.startswith('lemma_'):
                    not_discoverable_reasons["vstd_lemma"] += 1
                else:
                    not_discoverable_reasons["other"] += 1

    discoverable_pct = (discoverable / total_lemma_calls * 100) if total_lemma_calls > 0 else 0

    result = {
        "total_exec_fns": len(all_exec_fns),
        "total_lemma_calls_in_exec_proofs": total_lemma_calls,
        "discoverable_by_spec_fn_overlap": discoverable,
        "discoverable_pct": round(discoverable_pct, 1),
        "not_discoverable": not_discoverable,
        "not_discoverable_reasons": dict(sorted(not_discoverable_reasons.items())),
        "examples_not_discoverable": examples_not_discoverable,
        "exec_functions_detail": all_exec_fns,
    }

    out_path = "/root/dalek-lite/experiment_results/exp11_lemma_discovery.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    print(f"\nResults written to {out_path}")
    print(f"\nTotal exec fns with ensures + proof blocks: {len(all_exec_fns)}")
    print(f"Total lemma calls in exec proofs: {total_lemma_calls}")
    print(f"Discoverable by spec fn overlap: {discoverable} ({discoverable_pct:.1f}%)")
    print(f"Not discoverable: {not_discoverable}")
    print(f"Reasons:")
    for reason, count in sorted(not_discoverable_reasons.items()):
        print(f"  {reason}: {count}")


if __name__ == "__main__":
    main()
