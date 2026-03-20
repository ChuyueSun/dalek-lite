#!/usr/bin/env python3
"""
Experiment 7: Admit/Axiom Boundary Analysis for dalek-lite Verus codebase.

For every remaining `admit()` in the codebase, classifies it as:
- mathematical_axiom: Well-known math fact impractical to prove in SMT
- trusted_constant: Specific computed constant values accepted as correct
- external_verification: Verified by external tool/system
- algebraic_deep: Requires deep algebraic reasoning beyond current lemma library
- incomplete_proof: Could likely be proved with more effort
- computational: Could be verified by by(compute) if Verus supported the size
- unknown: Can't classify
"""

import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path

SRC_DIR = Path("/root/dalek-lite/curve25519-dalek/src")


def find_all_admits():
    """Find every admit() in .rs files under src/, with context."""
    admits = []
    for rs_file in sorted(SRC_DIR.rglob("*.rs")):
        rel = str(rs_file.relative_to(SRC_DIR))
        lines = rs_file.read_text().splitlines()
        for i, line in enumerate(lines):
            # Match admit() as a standalone call or inside an assert block
            if "admit()" in line and "//!" not in line and line.strip().startswith("//") is False:
                # Skip comment-only lines (but keep lines where admit() is in code, possibly with trailing comment)
                stripped = line.strip()
                if stripped.startswith("//"):
                    continue
                # Get context: 150 lines before, 10 after
                ctx_before = lines[max(0, i - 150):i]
                ctx_after = lines[i + 1:min(len(lines), i + 11)]
                admits.append({
                    "file": rel,
                    "abs_path": str(rs_file),
                    "line": i + 1,  # 1-indexed
                    "line_text": line,
                    "context_before": ctx_before,
                    "context_after": ctx_after,
                })
    return admits


def find_enclosing_function(context_before, admit_line_text):
    """Look backwards through context to find the enclosing fn declaration."""
    # Search backwards for fn declaration
    for line in reversed(context_before):
        m = re.search(r'(?:pub\s+)?(?:proof\s+)?(?:pub\(\w+\)\s+)?(?:proof\s+)?fn\s+(\w+)', line)
        if m:
            return m.group(1)
    return "unknown"


def extract_ensures(context_before, context_after, all_lines_around):
    """Extract the ensures clause from context."""
    in_ensures = False
    ensures_lines = []
    combined = context_before + [all_lines_around] + context_after
    for line in combined:
        stripped = line.strip()
        if stripped.startswith("ensures"):
            in_ensures = True
            rest = stripped[len("ensures"):].strip()
            if rest:
                ensures_lines.append(rest)
            continue
        if in_ensures:
            if stripped.startswith("{") or stripped.startswith("admit") or stripped.startswith("//"):
                break
            if stripped.startswith("requires"):
                break
            ensures_lines.append(stripped)
    return " ".join(ensures_lines).strip() if ensures_lines else ""


def extract_comment(context_before, admit_line_text):
    """Extract inline comment from admit line and nearby comments."""
    comments = []
    # Inline comment on the admit line itself
    m = re.search(r'admit\(\);\s*//\s*(.*)', admit_line_text)
    if m:
        comments.append(m.group(1).strip())
    # Look for doc comments (///) or regular comments (//) in the few lines before
    for line in context_before[-5:]:
        stripped = line.strip()
        if stripped.startswith("///") or stripped.startswith("//"):
            comment_text = re.sub(r'^///?!?\s*', '', stripped).strip()
            if comment_text and "admit" not in comment_text.lower():
                comments.append(comment_text)
    return " | ".join(comments) if comments else ""


def determine_layer(file_path):
    """Determine which architectural layer a file belongs to."""
    if "specs/" in file_path:
        if "primality" in file_path:
            return "specs/primality"
        elif "proba" in file_path:
            return "specs/probabilistic"
        elif "window" in file_path:
            return "specs/window"
        elif "field" in file_path:
            return "specs/field"
        elif "edwards" in file_path:
            return "specs/edwards"
        return "specs/other"
    elif "lemmas/ristretto" in file_path:
        return "lemmas/ristretto"
    elif "lemmas/edwards" in file_path:
        return "lemmas/edwards"
    elif "lemmas/field" in file_path:
        return "lemmas/field"
    elif "lemmas/montgomery" in file_path:
        return "lemmas/montgomery"
    elif "lemmas/" in file_path:
        return "lemmas/other"
    elif "lizard/" in file_path:
        return "exec/lizard"
    elif "core_assumes" in file_path:
        return "core_assumes"
    return "other"


def classify_admit(admit_info):
    """Classify a single admit() into one of the categories."""
    fn_name = admit_info["function"]
    ensures = admit_info["ensures_summary"]
    comment = admit_info["comment"]
    file_path = admit_info["file"]
    layer = admit_info["layer"]
    line_text = admit_info["line_text"]
    ctx_before_text = "\n".join(admit_info.get("_ctx_before", []))

    # --- mathematical_axiom ---
    # Primality, group theory axioms, probabilistic axioms
    if "axiom" in fn_name.lower():
        # Probabilistic axioms (cryptographic properties)
        if "proba" in file_path or "uniform" in fn_name.lower():
            return "mathematical_axiom", False, \
                "Cryptographic/probabilistic axiom (uniform distribution, independence) - not provable in program logic"

        # Primality axioms
        if "prime" in fn_name.lower() or "prime" in ensures.lower() or "primality" in file_path:
            return "mathematical_axiom", False, \
                "Primality of large constants (2^255-19 or group order) - requires big-number computation"

        # Group structure axioms (associativity, identity, etc.)
        if "associat" in fn_name.lower():
            return "algebraic_deep", False, \
                "Group associativity requires degree-6 polynomial identity over F_p"

        # Edwards add completeness
        if "complete" in fn_name.lower():
            return "algebraic_deep", False, \
                "Completeness of Edwards addition law - deep algebraic geometry result"

        # Ristretto decode axioms
        if "ristretto_decode" in fn_name.lower():
            return "mathematical_axiom", False, \
                "Ristretto decode property - follows from Decaf/Ristretto construction"

        # Elligator axioms
        if "elligator" in fn_name.lower():
            if "nonzero" in fn_name.lower() or "intermediates" in fn_name.lower():
                return "algebraic_deep", False, \
                    "Elligator intermediate nonzero - algebraic property of the map"
            if "on_curve" in fn_name.lower():
                return "mathematical_axiom", False, \
                    "Elligator map produces on-curve points - standard Elligator result"
            if "even_subgroup" in fn_name.lower():
                return "mathematical_axiom", False, \
                    "Elligator map produces even subgroup points - Decaf construction"
            if "encode" in fn_name.lower() and "valid" in fn_name.lower():
                return "mathematical_axiom", False, \
                    "Elligator encode outputs valid u-coordinate - standard map property"
            return "mathematical_axiom", False, \
                "Elligator map property - standard cryptographic construction"

        # Even subgroup closure
        if "even_subgroup" in fn_name.lower():
            return "mathematical_axiom", False, \
                "Even subgroup closed under addition - standard group theory"

        # Cross-multiplication equivalence
        if "cross_mul" in fn_name.lower():
            return "mathematical_axiom", False, \
                "Ristretto equivalence via cross-multiplication - Decaf/Ristretto construction"

        # Basepoint table axioms
        if "basepoint_table" in fn_name.lower() or "basepoint" in fn_name.lower():
            return "trusted_constant", False, \
                "Precomputed basepoint table validity - verified by construction/test"

        # Hash axioms
        if "hash" in fn_name.lower():
            return "mathematical_axiom", False, \
                "Hash function property (deterministic, canonical)"

        # SHA-512/SHA-256 output length
        if "sha512" in fn_name.lower() or "sha256" in fn_name.lower():
            return "external_verification", False, \
                "Hash function output length - property of the external hash implementation"

        # xDBL / xADD correctness
        if "xdbl" in fn_name.lower() or "xadd" in fn_name.lower():
            return "algebraic_deep", False, \
                "Montgomery ladder formula correctness - requires algebraic verification"

        # Montgomery-Edwards map commutativity
        if "commutes" in fn_name.lower() or "edwards_to_montgomery" in fn_name.lower():
            return "algebraic_deep", False, \
                "Edwards-Montgomery map commutativity - deep birational correspondence"

        # Montgomery validity preservation
        if "montgomery" in fn_name.lower() and "valid" in fn_name.lower():
            return "algebraic_deep", False, \
                "Montgomery u-coordinate validity under birational map"

        # Inverse square root factoring
        if "invsqrt" in fn_name.lower():
            if "a_minus_d" in fn_name.lower():
                return "trusted_constant", False, \
                    "Specific numerical value of invsqrt(-1-d) - concrete constant"
            if "factors" in fn_name.lower():
                return "algebraic_deep", False, \
                    "Inverse square root factoring property - field arithmetic identity"
            return "algebraic_deep", False, \
                "Inverse square root property - field arithmetic identity"

        # Quadratic residue axioms
        if "not_quadratic" in fn_name.lower() or "not_qr" in fn_name.lower():
            return "computational", False, \
                "Quadratic residuosity of specific constants - verifiable by Euler criterion computation"

        # Add-neg-is-identity
        if "add_neg" in fn_name.lower():
            return "algebraic_deep", False, \
                "Point + negation = identity - requires algebraic simplification"

        # sqrt_m1 properties - these are computational facts about a specific constant
        if "sqrt_m1" in fn_name.lower():
            if "squared" in fn_name.lower():
                return "computational", False, \
                    "sqrt(-1)^2 = -1 mod p - verifiable by 252-bit modular multiplication"
            if "not_square" in fn_name.lower():
                return "computational", False, \
                    "sqrt(-1) or -sqrt(-1) not a QR - verifiable by Euler criterion computation"

        # Catch-all for axioms
        return "mathematical_axiom", False, \
            "Named axiom - mathematical fact accepted without proof"

    # --- trusted_constant ---
    if "hardcoded" in comment.lower() or "table" in fn_name.lower():
        return "trusted_constant", False, \
            "Hardcoded table/constant data verified by construction"

    # --- computational ---
    if "sqrt_m1" in fn_name.lower():
        if "squared" in fn_name.lower():
            return "computational", False, \
                "sqrt(-1)^2 = -1 mod p - verifiable by 252-bit modular multiplication"
        if "not_square" in fn_name.lower():
            return "computational", False, \
                "sqrt(-1) not a QR - verifiable by Euler criterion computation"
        if "neg_sqrt_m1" in fn_name.lower():
            return "computational", False, \
                "-sqrt(-1) not a QR - verifiable by Euler criterion computation"

    # --- incomplete_proof ---
    # Look for PROOF BYPASS comments or TODO markers
    if "PROOF BYPASS" in comment or "PROOF BYPASS" in ctx_before_text or "PROOF BYPASS" in line_text:
        return "incomplete_proof", True, \
            "Proof bypass - could be completed with more proof effort"

    # Lizard/exec code with admits
    if "lizard" in file_path:
        if "limbs_bounded" in line_text or "limbs_bounded" in ensures:
            return "incomplete_proof", True, \
                "Limb bound tracking in loop - could be proven with invariant strengthening"
        if "elligator" in ensures.lower() or "coset" in ensures.lower():
            return "incomplete_proof", True, \
                "Elligator roundtrip correctness - could be proven with algebraic lemmas"
        return "incomplete_proof", True, \
            "Exec-level proof incomplete - could be completed with more effort"

    # core_assumes hash/sha axioms
    if "core_assumes" in file_path:
        if "sha512" in fn_name.lower() or "sha256" in fn_name.lower():
            return "external_verification", False, \
                "SHA output length - property of external crypto library"
        if "hash" in fn_name.lower():
            return "mathematical_axiom", False, \
                "Hashing canonical form property"

    # Edwards curve equation lemmas
    if "curve_equation" in file_path:
        if "associat" in fn_name.lower():
            return "algebraic_deep", False, \
                "Edwards addition associativity - degree-6 polynomial identity"
        if "add_neg" in fn_name.lower() or "neg_is_identity" in fn_name.lower():
            return "algebraic_deep", False, \
                "Point + negation = identity - algebraic simplification in F_p"
        if "complete" in fn_name.lower():
            return "algebraic_deep", False, \
                "Completeness of Edwards addition - algebraic geometry"
        return "algebraic_deep", False, \
            "Edwards curve equation property - algebraic identity"

    # Montgomery curve lemmas
    if "montgomery" in file_path:
        return "algebraic_deep", False, \
            "Montgomery curve property - algebraic identity over F_p"

    # Window specs
    if "window" in file_path:
        return "trusted_constant", False, \
            "Precomputed table data verified by construction"

    # Field specs
    if "field" in file_path:
        return "algebraic_deep", False, \
            "Field arithmetic identity"

    return "unknown", False, "Could not classify"


def analyze():
    """Main analysis: find, extract, classify, and summarize all admits."""
    raw_admits = find_all_admits()

    entries = []
    for adm in raw_admits:
        fn_name = find_enclosing_function(adm["context_before"], adm["line_text"])
        ensures = extract_ensures(adm["context_before"], adm["context_after"], adm["line_text"])
        comment = extract_comment(adm["context_before"], adm["line_text"])
        layer = determine_layer(adm["file"])

        entry = {
            "file": adm["file"],
            "line": adm["line"],
            "function": fn_name,
            "ensures_summary": ensures[:200] if ensures else "(no ensures extracted)",
            "comment": comment[:200] if comment else "",
            "layer": layer,
            "line_text": adm["line_text"].strip(),
            "_ctx_before": adm["context_before"],  # for classification
        }

        category, automatable, reason = classify_admit(entry)
        entry["category"] = category
        entry["automatable"] = automatable
        entry["reason"] = reason

        # Remove internal field
        del entry["_ctx_before"]

        entries.append(entry)

    # --- Build summary ---
    total = len(entries)

    # by_file
    by_file = defaultdict(int)
    for e in entries:
        by_file[e["file"]] += 1

    # by_category
    by_category = defaultdict(lambda: {"count": 0, "examples": []})
    for e in entries:
        cat = e["category"]
        by_category[cat]["count"] += 1
        by_category[cat]["examples"].append({
            "file": e["file"],
            "line": e["line"],
            "function": e["function"],
            "ensures_summary": e["ensures_summary"],
            "comment": e["comment"],
            "automatable": e["automatable"],
            "reason": e["reason"],
        })

    # by_layer
    by_layer = defaultdict(int)
    for e in entries:
        by_layer[e["layer"]] += 1

    # automation_ceiling
    not_automatable_cats = {"mathematical_axiom", "algebraic_deep", "external_verification"}
    possibly_automatable_cats = {"incomplete_proof", "computational", "trusted_constant"}

    not_automatable = sum(1 for e in entries if e["category"] in not_automatable_cats)
    possibly_automatable = sum(1 for e in entries if e["category"] in possibly_automatable_cats)
    unknown_count = sum(1 for e in entries if e["category"] == "unknown")

    pct = (possibly_automatable / total * 100) if total > 0 else 0

    result = {
        "experiment": "exp7_admit_boundary_analysis",
        "date": "2026-03-18",
        "codebase": "dalek-lite/curve25519-dalek",
        "total_admits": total,
        "by_file": dict(sorted(by_file.items())),
        "by_category": {
            cat: {
                "count": info["count"],
                "examples": info["examples"],
            }
            for cat, info in sorted(by_category.items())
        },
        "by_layer": dict(sorted(by_layer.items())),
        "automation_ceiling": {
            "total_admits": total,
            "not_automatable": not_automatable,
            "not_automatable_categories": ["mathematical_axiom", "algebraic_deep", "external_verification"],
            "possibly_automatable": possibly_automatable,
            "possibly_automatable_categories": ["incomplete_proof", "computational", "trusted_constant"],
            "unknown": unknown_count,
            "percentage_possibly_automatable": round(pct, 1),
        },
        "detailed_entries": entries,
    }

    return result


def main():
    result = analyze()

    out_path = Path("/root/experiment_results/exp7_admit_analysis.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)

    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    # Print summary to stdout
    print(f"Total admit() occurrences: {result['total_admits']}")
    print()
    print("By file:")
    for file, count in result["by_file"].items():
        print(f"  {file}: {count}")
    print()
    print("By category:")
    for cat, info in result["by_category"].items():
        print(f"  {cat}: {info['count']}")
        for ex in info["examples"][:3]:
            print(f"    - {ex['function']} ({ex['file']}:{ex.get('line', '?')})")
            print(f"      Reason: {ex['reason']}")
    print()
    print("By layer:")
    for layer, count in result["by_layer"].items():
        print(f"  {layer}: {count}")
    print()
    ac = result["automation_ceiling"]
    print("Automation ceiling:")
    print(f"  Total admits: {ac['total_admits']}")
    print(f"  Not automatable (axioms + deep algebra + external): {ac['not_automatable']}")
    print(f"  Possibly automatable (incomplete + computational + trusted): {ac['possibly_automatable']}")
    print(f"  Unknown: {ac['unknown']}")
    print(f"  Percentage possibly automatable: {ac['percentage_possibly_automatable']}%")
    print()
    print(f"Results saved to: {out_path}")


if __name__ == "__main__":
    main()
