#!/usr/bin/env python3
"""
Experiment 3: Analogue Search Simulation

For each proof fn at Layers 3+ (field_lemmas and above -- NOT common_lemmas),
extract the spec functions mentioned in its ensures clause, then search for OTHER
proof fns with >=2 overlapping spec functions.
"""

import os
import re
import json
from collections import defaultdict, Counter
from pathlib import Path

LEMMAS_DIR = Path("/root/dalek-lite/curve25519-dalek/src/lemmas")

# Keywords and logical operators to exclude from spec function extraction
EXCLUDE_NAMES = {
    "forall", "exists", "old", "true", "false", "self", "Self",
    "int", "nat", "u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "i128",
    "bool", "usize", "isize",
    "Some", "None", "Ok", "Err",
    "requires", "ensures", "decreases", "recommends",
    "assert", "assume", "admit",
    "let", "if", "else", "match", "return",
    "as", "by",
}


def get_domain(file_path: str) -> str:
    """Extract the domain (subdirectory) from a file path."""
    rel = os.path.relpath(file_path, LEMMAS_DIR)
    parts = rel.split(os.sep)
    if len(parts) > 1:
        return parts[0]  # e.g., "field_lemmas", "edwards_lemmas", etc.
    else:
        return "top_level"  # files directly in src/lemmas/


def get_layer(domain: str) -> int:
    """Assign a layer number based on domain."""
    layer_map = {
        "common_lemmas": 0,
        "field_lemmas": 2,
        "scalar_lemmas_": 2,
        "scalar_byte_lemmas": 2,
        "top_level": 3,  # scalar_lemmas.rs etc.
        "edwards_lemmas": 5,
        "ristretto_lemmas": 6,
    }
    return layer_map.get(domain, 3)


def is_excluded_domain(domain: str) -> bool:
    """Return True if this domain should be excluded (common_lemmas)."""
    return domain == "common_lemmas"


def extract_ensures_block(text: str, fn_start_idx: int) -> str:
    """
    Extract the ensures clause from a proof fn declaration.
    Starts searching from fn_start_idx for 'ensures' keyword,
    stops when we hit the opening '{' of the body (balanced brace tracking).
    """
    # Find 'ensures' after the fn signature
    ensures_match = re.search(r'\bensures\b', text[fn_start_idx:])
    if not ensures_match:
        return ""

    ensures_start = fn_start_idx + ensures_match.end()

    # The ensures block ends at the opening '{' of the function body.
    # We need to find the '{' that is NOT inside parentheses or brackets.
    # The ensures block can contain nested parens/brackets but not braces.
    paren_depth = 0
    bracket_depth = 0
    i = ensures_start
    while i < len(text):
        ch = text[i]
        if ch == '(':
            paren_depth += 1
        elif ch == ')':
            paren_depth -= 1
        elif ch == '[':
            bracket_depth += 1
        elif ch == ']':
            bracket_depth -= 1
        elif ch == '{' and paren_depth == 0 and bracket_depth == 0:
            return text[ensures_start:i]
        i += 1
    return text[ensures_start:]


def extract_body(text: str, fn_header_end: int) -> str:
    """
    Extract the body of a proof fn (everything between the opening '{' and
    matching closing '}').
    """
    # Find the opening brace
    brace_pos = text.find('{', fn_header_end)
    if brace_pos == -1:
        return ""

    depth = 0
    i = brace_pos
    while i < len(text):
        ch = text[i]
        if ch == '{':
            depth += 1
        elif ch == '}':
            depth -= 1
            if depth == 0:
                return text[brace_pos + 1:i]
        i += 1
    return text[brace_pos + 1:]


def extract_spec_fns(ensures_text: str) -> set:
    """
    Extract spec function names from an ensures clause.
    A spec function is an identifier followed by '(' that is not a keyword
    or logical operator.
    """
    # Find all identifiers followed by '('
    # This regex matches word characters (including _) followed by '('
    pattern = r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\('
    matches = re.findall(pattern, ensures_text)

    spec_fns = set()
    for name in matches:
        if name not in EXCLUDE_NAMES:
            spec_fns.add(name)
    return spec_fns


def extract_sub_lemma_calls(body_text: str) -> set:
    """
    Extract sub-lemma calls (lemma_* and axiom_*) from the body of a proof fn.
    """
    pattern = r'\b((?:lemma|axiom)_[a-zA-Z0-9_]*)\s*[\(;]'
    matches = re.findall(pattern, body_text)
    return set(matches)


def find_fn_end(text: str, fn_start: int) -> int:
    """
    Find the end of a proof fn by matching braces from the opening '{'.
    Returns the index after the closing '}'.
    """
    brace_pos = text.find('{', fn_start)
    if brace_pos == -1:
        return len(text)

    depth = 0
    i = brace_pos
    while i < len(text):
        ch = text[i]
        if ch == '{':
            depth += 1
        elif ch == '}':
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return len(text)


def parse_proof_fns(file_path: str) -> list:
    """
    Parse a Rust file and extract all pub proof fn and pub broadcast proof fn declarations.
    Returns a list of dicts with fn info.
    """
    with open(file_path, 'r') as f:
        text = f.read()

    results = []

    # Match 'pub proof fn' and 'pub broadcast proof fn'
    pattern = r'\bpub\s+(?:broadcast\s+)?proof\s+fn\s+([a-zA-Z_][a-zA-Z0-9_]*)'
    for match in re.finditer(pattern, text):
        fn_name = match.group(1)
        fn_start = match.start()

        # Find the end of this function
        fn_end = find_fn_end(text, fn_start)

        fn_text = text[fn_start:fn_end]

        # Extract ensures clause
        ensures_text = extract_ensures_block(text, fn_start)

        # Extract spec functions from ensures
        spec_fns = extract_spec_fns(ensures_text)

        # Extract the body (everything after the ensures block / opening brace)
        body_text = extract_body(text, fn_start)

        # Extract sub-lemma calls from body
        sub_lemma_calls = extract_sub_lemma_calls(body_text)

        domain = get_domain(file_path)
        layer = get_layer(domain)

        results.append({
            "fn_name": fn_name,
            "file_path": str(file_path),
            "domain": domain,
            "layer": layer,
            "ensures_spec_fns": sorted(spec_fns),
            "sub_lemma_calls": sorted(sub_lemma_calls),
            "ensures_text_preview": ensures_text.strip()[:200],
        })

    return results


def main():
    all_fns = []

    # Walk all .rs files under src/lemmas/
    for root, dirs, files in os.walk(LEMMAS_DIR):
        for fname in files:
            if fname.endswith('.rs'):
                fpath = os.path.join(root, fname)
                fns = parse_proof_fns(fpath)
                all_fns.extend(fns)

    print(f"Total proof fns found: {len(all_fns)}")

    # Filter to layers 3+ (excluding common_lemmas which is layer 0)
    # But we also want field_lemmas (layer 2) and scalar_lemmas_ (layer 2)
    # The task says "Layers 3+ (field_lemmas and above -- NOT common_lemmas)"
    # So we include everything EXCEPT common_lemmas
    analyzed_fns = [fn for fn in all_fns if not is_excluded_domain(fn["domain"])]
    print(f"Proof fns analyzed (excluding common_lemmas): {len(analyzed_fns)}")

    # Build spec function frequency
    spec_fn_counter = Counter()
    for fn in analyzed_fns:
        for sf in fn["ensures_spec_fns"]:
            spec_fn_counter[sf] += 1

    # Find analogue pairs: different files, >=2 overlapping spec fns in ensures
    analogue_pairs = []
    fns_with_analogue = set()

    for i in range(len(analyzed_fns)):
        for j in range(i + 1, len(analyzed_fns)):
            fn_a = analyzed_fns[i]
            fn_b = analyzed_fns[j]

            # Must be in different files
            if fn_a["file_path"] == fn_b["file_path"]:
                continue

            spec_overlap = set(fn_a["ensures_spec_fns"]) & set(fn_b["ensures_spec_fns"])
            if len(spec_overlap) >= 2:
                # Check sub-lemma overlap
                sub_lemma_overlap = set(fn_a["sub_lemma_calls"]) & set(fn_b["sub_lemma_calls"])

                pair = {
                    "fn_a": fn_a["fn_name"],
                    "fn_a_file": os.path.relpath(fn_a["file_path"], LEMMAS_DIR),
                    "fn_a_domain": fn_a["domain"],
                    "fn_b": fn_b["fn_name"],
                    "fn_b_file": os.path.relpath(fn_b["file_path"], LEMMAS_DIR),
                    "fn_b_domain": fn_b["domain"],
                    "spec_fn_overlap": sorted(spec_overlap),
                    "overlap_count": len(spec_overlap),
                    "shared_sub_lemma_calls": sorted(sub_lemma_overlap),
                    "sub_lemma_overlap_count": len(sub_lemma_overlap),
                    "is_cross_domain": fn_a["domain"] != fn_b["domain"],
                }
                analogue_pairs.append(pair)
                fns_with_analogue.add(fn_a["fn_name"])
                fns_with_analogue.add(fn_b["fn_name"])

    # Sort by overlap_count descending
    analogue_pairs.sort(key=lambda x: (-x["overlap_count"], -x["sub_lemma_overlap_count"]))

    # Cross-domain analogues
    cross_domain_pairs = [p for p in analogue_pairs if p["is_cross_domain"]]

    # Pairs with shared sub-lemma calls
    pairs_with_shared_sub_lemmas = [p for p in analogue_pairs if p["sub_lemma_overlap_count"] > 0]

    # Compute sub-lemma overlap rate among analogue pairs
    if len(analogue_pairs) > 0:
        sub_lemma_overlap_rate = len(pairs_with_shared_sub_lemmas) / len(analogue_pairs)
    else:
        sub_lemma_overlap_rate = 0.0

    # Hit rate
    total_analyzed = len(analyzed_fns)
    fns_with_at_least_one = len(fns_with_analogue)
    hit_rate = fns_with_at_least_one / total_analyzed if total_analyzed > 0 else 0.0

    # Top 30 spec fn frequency
    top_spec_fns = [
        {"spec_fn": name, "count": count}
        for name, count in spec_fn_counter.most_common(30)
    ]

    # Per-function analogue counts for distribution analysis
    fn_analogue_counts = Counter()
    for pair in analogue_pairs:
        fn_analogue_counts[pair["fn_a"]] += 1
        fn_analogue_counts[pair["fn_b"]] += 1

    analogue_count_distribution = {}
    for fn in analyzed_fns:
        count = fn_analogue_counts.get(fn["fn_name"], 0)
        bucket = str(count)
        analogue_count_distribution[bucket] = analogue_count_distribution.get(bucket, 0) + 1

    # Build per-function detail for export
    fn_details = []
    for fn in analyzed_fns:
        fn_details.append({
            "fn_name": fn["fn_name"],
            "file": os.path.relpath(fn["file_path"], LEMMAS_DIR),
            "domain": fn["domain"],
            "layer": fn["layer"],
            "ensures_spec_fns": fn["ensures_spec_fns"],
            "spec_fn_count": len(fn["ensures_spec_fns"]),
            "sub_lemma_calls": fn["sub_lemma_calls"],
            "analogue_count": fn_analogue_counts.get(fn["fn_name"], 0),
        })

    result = {
        "experiment": "exp3_analogue_search",
        "description": "For each proof fn (excluding common_lemmas), find other proof fns in different files with >=2 overlapping spec functions in their ensures clause.",
        "total_proof_fns_all_layers": len(all_fns),
        "total_proof_fns_analyzed": total_analyzed,
        "fns_with_at_least_one_analogue": fns_with_at_least_one,
        "analogue_hit_rate": round(hit_rate, 4),
        "total_analogue_pairs": len(analogue_pairs),
        "cross_domain_analogue_pairs": len(cross_domain_pairs),
        "pairs_with_shared_sub_lemmas": len(pairs_with_shared_sub_lemmas),
        "sub_lemma_overlap_rate": round(sub_lemma_overlap_rate, 4),
        "analogue_count_distribution": analogue_count_distribution,
        "analogue_pairs_top30": analogue_pairs[:30],
        "cross_domain_analogues_top20": cross_domain_pairs[:20],
        "spec_fn_frequency_top30": top_spec_fns,
        "fn_details": fn_details,
    }

    output_path = "/root/experiment_results/exp3_analogue_search.json"
    with open(output_path, 'w') as f:
        json.dump(result, f, indent=2)

    # Print summary
    print(f"\n{'='*70}")
    print(f"EXPERIMENT 3: ANALOGUE SEARCH SIMULATION RESULTS")
    print(f"{'='*70}")
    print(f"Total proof fns (all layers):        {len(all_fns)}")
    print(f"Total proof fns analyzed (layer 3+):  {total_analyzed}")
    print(f"Fns with >= 1 analogue:               {fns_with_at_least_one}")
    print(f"Analogue hit rate:                    {hit_rate:.1%}")
    print(f"Total analogue pairs:                 {len(analogue_pairs)}")
    print(f"Cross-domain pairs:                   {len(cross_domain_pairs)}")
    print(f"Pairs with shared sub-lemmas:         {len(pairs_with_shared_sub_lemmas)}")
    print(f"Sub-lemma overlap rate:               {sub_lemma_overlap_rate:.1%}")
    print()
    print(f"Top 10 spec functions by frequency in ensures clauses:")
    for item in top_spec_fns[:10]:
        print(f"  {item['spec_fn']:45s} {item['count']:3d}")
    print()
    print(f"Top 10 analogue pairs by overlap count:")
    for pair in analogue_pairs[:10]:
        cross = " [CROSS-DOMAIN]" if pair["is_cross_domain"] else ""
        shared = f" (shared sub-lemmas: {pair['sub_lemma_overlap_count']})" if pair["sub_lemma_overlap_count"] > 0 else ""
        print(f"  {pair['fn_a']:45s} <-> {pair['fn_b']:45s} overlap={pair['overlap_count']}{cross}{shared}")
        print(f"    spec fns: {', '.join(pair['spec_fn_overlap'][:5])}{'...' if len(pair['spec_fn_overlap']) > 5 else ''}")
    print()
    print(f"Cross-domain analogue examples (top 5):")
    for pair in cross_domain_pairs[:5]:
        print(f"  {pair['fn_a']} ({pair['fn_a_domain']}) <-> {pair['fn_b']} ({pair['fn_b_domain']})")
        print(f"    overlap: {', '.join(pair['spec_fn_overlap'][:5])}")
    print()
    print(f"Output saved to: {output_path}")


if __name__ == "__main__":
    main()
