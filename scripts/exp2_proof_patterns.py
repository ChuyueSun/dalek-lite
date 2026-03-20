#!/usr/bin/env python3
"""
Experiment 2: Proof Body Pattern Distribution

Walks all .rs files under src/lemmas/, extracts `pub proof fn` and
`pub broadcast proof fn` declarations, classifies their bodies by
proof strategy, and produces a summary JSON.
"""

import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

LEMMAS_DIR = Path("/root/dalek-lite/curve25519-dalek/src/lemmas")
OUTPUT_PATH = Path("/root/experiment_results/exp2_proof_patterns.json")

# ─── helpers ────────────────────────────────────────────────────────────

def read_all_rs_files(root: Path) -> list[tuple[str, str]]:
    """Return list of (relative_path, content) for every .rs file under root."""
    results = []
    for dirpath, _, filenames in os.walk(root):
        for fn in sorted(filenames):
            if fn.endswith(".rs"):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, root)
                with open(full) as f:
                    results.append((rel, f.read()))
    return results


def derive_layer(rel_path: str) -> str:
    """Derive the layer name from the relative path inside src/lemmas/."""
    parts = rel_path.split("/")
    if len(parts) >= 2:
        return parts[0]  # e.g. "common_lemmas", "field_lemmas", etc.
    # Top-level file
    stem = parts[0].replace(".rs", "")
    return stem  # e.g. "scalar_lemmas", "montgomery_lemmas"


# ─── brace-matching body extractor ─────────────────────────────────────

# Match:  pub proof fn <name>   or   pub broadcast proof fn <name>
PROOF_FN_RE = re.compile(
    r'pub\s+(?:broadcast\s+)?proof\s+fn\s+(\$?\w+)'
)

def extract_proof_fns(source: str) -> list[dict]:
    """
    Find every `pub proof fn` / `pub broadcast proof fn` in source.
    Return list of dicts with keys: name, body, start_line, end_line, is_broadcast.
    Uses brace-matching to get the full body.
    """
    results = []
    for m in PROOF_FN_RE.finditer(source):
        fn_name = m.group(1)
        # Skip macro parameter names like $name
        if fn_name.startswith("$"):
            continue

        is_broadcast = "broadcast" in source[m.start():m.end()]

        # Find the opening brace of the body.
        # The body brace comes AFTER the signature (which may include
        # requires/ensures/decreases blocks).
        # We need to find the first '{' that opens the body.
        # Strategy: from the match position, find the first '{' and then
        # brace-match to get the body.  But the signature itself may contain
        # braces in type parameters or trigger blocks.  However, `requires`,
        # `ensures`, `decreases` do NOT use braces (they use commas and
        # expressions).  The only braces before the body are:
        #   - trigger blocks: #![trigger ...]  -- no braces
        #   - by(strategy)  -- parentheses not braces
        # So the first '{' after `fn name(...)` really does start the body
        # (unless there's a `by (bit_vector)` style function with no body braces
        # other than the outer pair).

        # We need to handle two patterns:
        # Pattern A:  pub proof fn name(...) requires ... ensures ... { BODY }
        # Pattern B:  pub proof fn name(...) by (bit_vector) requires ... ensures ... { BODY }
        # In both cases the first '{' starts the body.

        pos = m.end()
        # Find the first '{' from here
        brace_start = source.find('{', pos)
        if brace_start == -1:
            continue

        # Now brace-match
        depth = 0
        i = brace_start
        while i < len(source):
            ch = source[i]
            if ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
                if depth == 0:
                    break
            # Skip string literals
            elif ch == '"':
                i += 1
                while i < len(source) and source[i] != '"':
                    if source[i] == '\\':
                        i += 1  # skip escaped char
                    i += 1
            # Skip single-line comments
            elif ch == '/' and i + 1 < len(source) and source[i + 1] == '/':
                while i < len(source) and source[i] != '\n':
                    i += 1
            # Skip block comments
            elif ch == '/' and i + 1 < len(source) and source[i + 1] == '*':
                i += 2
                comment_depth = 1
                while i < len(source) and comment_depth > 0:
                    if source[i] == '/' and i + 1 < len(source) and source[i + 1] == '*':
                        comment_depth += 1
                        i += 1
                    elif source[i] == '*' and i + 1 < len(source) and source[i + 1] == '/':
                        comment_depth -= 1
                        i += 1
                    i += 1
                continue
            i += 1

        if depth != 0:
            continue  # unmatched braces, skip

        brace_end = i
        body = source[brace_start:brace_end + 1]

        # Also capture the signature text (from fn decl to opening brace)
        sig_text = source[m.start():brace_start]

        # Line numbers
        start_line = source[:m.start()].count('\n') + 1
        end_line = source[:brace_end + 1].count('\n') + 1

        results.append({
            "name": fn_name,
            "body": body,
            "sig": sig_text,
            "start_line": start_line,
            "end_line": end_line,
            "is_broadcast": is_broadcast,
        })

    return results


# ─── pattern classifiers ───────────────────────────────────────────────

def classify_body(body: str, sig: str) -> dict:
    """
    Classify the proof body (and signature) against known patterns.
    Returns a dict of pattern_name -> bool, plus extracted details.
    """
    combined = sig + "\n" + body  # some strategies are in the signature

    patterns = {}

    # by(compute) / by(compute_only)
    patterns["by_compute"] = bool(re.search(r'by\s*\(\s*compute(_only)?\s*\)', combined))

    # by(bit_vector)
    patterns["by_bit_vector"] = bool(re.search(r'by\s*\(\s*bit_vector\s*\)', combined))

    # by(nonlinear_arith)
    patterns["by_nonlinear_arith"] = bool(re.search(r'by\s*\(\s*nonlinear_arith\s*\)', combined))

    # calc! macro
    patterns["calc_macro"] = "calc!" in body

    # assert forall ... by
    patterns["assert_forall_by"] = bool(re.search(r'assert\s+forall', body))

    # broadcast use
    patterns["broadcast_use"] = bool(re.search(r'broadcast\s+use', body))

    # sub-lemma calls: lemma_* or axiom_*
    sub_lemma_calls = set(re.findall(r'\b(lemma_\w+|axiom_\w+)\s*[\(;]', body))
    # Also catch calls like: lemma_foo(...)
    sub_lemma_calls |= set(re.findall(r'\b(lemma_\w+|axiom_\w+)\s*\(', body))
    # Remove the function being defined itself (recursive calls are still sub-lemma)
    # Actually keep recursive calls - they ARE sub-lemma calls
    patterns["sub_lemma_call"] = len(sub_lemma_calls) > 0

    # vstd lemma calls - functions from vstd:: or known vstd patterns
    vstd_calls = set()
    # Direct vstd function calls
    vstd_calls |= set(re.findall(r'\b(lemma_\w+)\s*\(', body))
    # Filter to only keep known vstd lemmas (those from vstd::arithmetic etc.)
    # Known vstd lemma prefixes
    vstd_prefixes = [
        "lemma_mul_", "lemma_div_", "lemma_mod_", "lemma_pow",
        "lemma_small_mod", "lemma_fundamental_div_mod",
        "lemma_mul_basics", "lemma_mul_is_", "lemma_mul_strict",
        "lemma_mul_inequality", "lemma_mul_increases",
        "lemma_mul_nonneg", "lemma_mul_upper_bound",
        "lemma_mul_ordering", "lemma_mul_induction",
        "lemma_mod_", "lemma2_to64",
        "lemma_seq_", "lemma_len",
        "assert_seqs_equal", "assert_by",
    ]
    vstd_fns = set()
    for call in vstd_calls:
        for prefix in vstd_prefixes:
            if call.startswith(prefix):
                vstd_fns.add(call)
                break
    # Also look for vstd:: qualified calls
    vstd_qualified = set(re.findall(r'vstd::\w+::\w+::(\w+)', body))
    vstd_fns |= vstd_qualified
    # p_gt_2 is from primality_specs not vstd
    vstd_fns.discard("p_gt_2")
    patterns["vstd_lemma_call"] = len(vstd_fns) > 0

    # reveal / reveal_with_fuel
    patterns["reveal_fn"] = bool(re.search(r'reveal\s*\(', body) or
                                 re.search(r'reveal_with_fuel\s*\(', body))

    # extensional equality
    patterns["extensional_eq"] = ("=~=" in body or "ext_equal" in body)

    # admit()
    patterns["admit"] = "admit()" in body

    # trivial: body is essentially empty (only whitespace/comments or a single assert)
    stripped = body.strip()
    if stripped == "{}":
        patterns["trivial"] = True
    else:
        # Remove outer braces
        inner = stripped[1:-1].strip() if stripped.startswith("{") and stripped.endswith("}") else stripped
        # Remove comments
        inner_no_comments = re.sub(r'//[^\n]*', '', inner)
        inner_no_comments = re.sub(r'/\*.*?\*/', '', inner_no_comments, flags=re.DOTALL)
        inner_clean = inner_no_comments.strip()
        # If empty or just a semicolon
        if inner_clean == "" or inner_clean == ";":
            patterns["trivial"] = True
        else:
            patterns["trivial"] = False

    # Count occurrences
    counts = {
        "by_compute_count": len(re.findall(r'by\s*\(\s*compute(_only)?\s*\)', combined)),
        "by_bit_vector_count": len(re.findall(r'by\s*\(\s*bit_vector\s*\)', combined)),
        "assert_forall_count": len(re.findall(r'assert\s+forall', body)),
    }

    return {
        "patterns": patterns,
        "counts": counts,
        "sub_lemma_names": sorted(sub_lemma_calls),
        "vstd_fns": sorted(vstd_fns),
    }


# ─── main analysis ─────────────────────────────────────────────────────

def analyze():
    files = read_all_rs_files(LEMMAS_DIR)
    print(f"Found {len(files)} .rs files under src/lemmas/")

    all_fns = []  # list of dicts with full info

    for rel_path, content in files:
        layer = derive_layer(rel_path)
        proof_fns = extract_proof_fns(content)
        for pf in proof_fns:
            classification = classify_body(pf["body"], pf["sig"])
            all_fns.append({
                "file": rel_path,
                "layer": layer,
                "name": pf["name"],
                "start_line": pf["start_line"],
                "end_line": pf["end_line"],
                "is_broadcast": pf["is_broadcast"],
                "body_lines": pf["body"].count('\n') + 1,
                **classification,
            })

    print(f"Extracted {len(all_fns)} proof functions")

    # ── Summary stats ──

    total = len(all_fns)

    # Pattern frequency
    pattern_names = [
        "by_compute", "by_bit_vector", "by_nonlinear_arith",
        "calc_macro", "assert_forall_by", "broadcast_use",
        "sub_lemma_call", "vstd_lemma_call", "reveal_fn",
        "extensional_eq", "admit", "trivial",
    ]
    pattern_freq = {}
    for pn in pattern_names:
        count = sum(1 for fn in all_fns if fn["patterns"][pn])
        pattern_freq[pn] = {
            "count": count,
            "pct": round(100 * count / total, 1) if total > 0 else 0,
        }

    # Pattern combinations
    combo_counter = Counter()
    for fn in all_fns:
        combo = tuple(sorted(pn for pn in pattern_names if fn["patterns"][pn]))
        if not combo:
            combo = ("none",)
        combo_counter[combo] += 1

    # Top 20 combos
    pattern_combinations = []
    for combo, cnt in combo_counter.most_common(20):
        pattern_combinations.append({
            "patterns": list(combo),
            "count": cnt,
            "pct": round(100 * cnt / total, 1) if total > 0 else 0,
        })

    # Body size distribution
    size_buckets = {"1-5": 0, "6-15": 0, "16-50": 0, "51-100": 0, "100+": 0}
    for fn in all_fns:
        bl = fn["body_lines"]
        if bl <= 5:
            size_buckets["1-5"] += 1
        elif bl <= 15:
            size_buckets["6-15"] += 1
        elif bl <= 50:
            size_buckets["16-50"] += 1
        elif bl <= 100:
            size_buckets["51-100"] += 1
        else:
            size_buckets["100+"] += 1

    body_size_distribution = {
        k: {"count": v, "pct": round(100 * v / total, 1) if total > 0 else 0}
        for k, v in size_buckets.items()
    }

    # Per-layer breakdown
    layer_data = defaultdict(lambda: {
        "total": 0,
        "patterns": Counter(),
    })
    for fn in all_fns:
        layer = fn["layer"]
        layer_data[layer]["total"] += 1
        for pn in pattern_names:
            if fn["patterns"][pn]:
                layer_data[layer]["patterns"][pn] += 1

    per_layer = {}
    for layer, data in sorted(layer_data.items()):
        per_layer[layer] = {
            "total_proof_fns": data["total"],
            "patterns": {
                pn: {
                    "count": data["patterns"].get(pn, 0),
                    "pct": round(100 * data["patterns"].get(pn, 0) / data["total"], 1) if data["total"] > 0 else 0,
                }
                for pn in pattern_names
            },
        }

    # Most-called sub-lemmas
    sub_lemma_counter = Counter()
    sub_lemma_files = defaultdict(set)
    for fn in all_fns:
        for name in fn["sub_lemma_names"]:
            sub_lemma_counter[name] += 1
            sub_lemma_files[name].add(fn["file"])

    most_called_sub_lemmas = []
    for name, call_count in sub_lemma_counter.most_common(30):
        most_called_sub_lemmas.append({
            "name": name,
            "call_count": call_count,
            "called_from_files": len(sub_lemma_files[name]),
        })

    # vstd usage
    vstd_counter = Counter()
    for fn in all_fns:
        for name in fn["vstd_fns"]:
            vstd_counter[name] += 1

    vstd_usage = [
        {"name": name, "call_count": cnt}
        for name, cnt in vstd_counter.most_common(30)
    ]

    # ── Build output ──

    result = {
        "experiment": "exp2_proof_patterns",
        "description": "Proof body pattern distribution for all pub proof fn in src/lemmas/",
        "total_proof_fns": total,
        "total_files": len(files),
        "pattern_frequency": pattern_freq,
        "pattern_combinations": pattern_combinations,
        "body_size_distribution": body_size_distribution,
        "per_layer": per_layer,
        "most_called_sub_lemmas": most_called_sub_lemmas,
        "vstd_usage": vstd_usage,
        "per_function_details": [
            {
                "file": fn["file"],
                "layer": fn["layer"],
                "name": fn["name"],
                "is_broadcast": fn["is_broadcast"],
                "body_lines": fn["body_lines"],
                "patterns": fn["patterns"],
                "counts": fn["counts"],
                "sub_lemma_names": fn["sub_lemma_names"],
                "vstd_fns": fn["vstd_fns"],
            }
            for fn in all_fns
        ],
    }

    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, "w") as f:
        json.dump(result, f, indent=2)

    print(f"\nResults written to {OUTPUT_PATH}")
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"Total proof functions: {total}")
    print(f"Total files scanned:  {len(files)}")
    print()
    print(f"Pattern frequency:")
    for pn in pattern_names:
        pf = pattern_freq[pn]
        bar = "#" * (pf["count"] // 3)
        print(f"  {pn:25s} {pf['count']:4d} ({pf['pct']:5.1f}%)  {bar}")
    print()
    print(f"Body size distribution:")
    for bucket, data in body_size_distribution.items():
        bar = "#" * (data["count"] // 3)
        print(f"  {bucket:8s} {data['count']:4d} ({data['pct']:5.1f}%)  {bar}")
    print()
    print(f"Top 10 pattern combinations:")
    for i, combo in enumerate(pattern_combinations[:10]):
        print(f"  {i+1:2d}. {combo['count']:4d} ({combo['pct']:5.1f}%)  {', '.join(combo['patterns'])}")
    print()
    print(f"Top 15 most-called sub-lemmas:")
    for sl in most_called_sub_lemmas[:15]:
        print(f"  {sl['name']:50s}  calls={sl['call_count']:3d}  files={sl['called_from_files']:2d}")
    print()
    print(f"Top 10 vstd lemma usage:")
    for vl in vstd_usage[:10]:
        print(f"  {vl['name']:50s}  calls={vl['call_count']:3d}")
    print()
    print(f"Per-layer summary:")
    for layer, data in sorted(per_layer.items()):
        top_patterns = sorted(
            [(pn, data["patterns"][pn]["count"]) for pn in pattern_names if data["patterns"][pn]["count"] > 0],
            key=lambda x: -x[1]
        )
        top_str = ", ".join(f"{p}={c}" for p, c in top_patterns[:4])
        print(f"  {layer:45s}  {data['total_proof_fns']:3d} fns  top: {top_str}")


if __name__ == "__main__":
    analyze()
