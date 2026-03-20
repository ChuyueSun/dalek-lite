#!/usr/bin/env python3
"""
Experiment 6: vstd Usage Census

Scans all .rs files under curve25519-dalek/src/ to map exactly which vstd
modules are imported, which vstd lemmas/functions are called, how often,
and from which layers.

Output: /root/experiment_results/exp6_vstd_census.json
"""

import os
import re
import json
from collections import defaultdict
from pathlib import Path

SRC_ROOT = Path("/root/dalek-lite/curve25519-dalek/src")
OUTPUT_PATH = Path("/root/experiment_results/exp6_vstd_census.json")


def classify_layer(filepath: str) -> str:
    """Derive the layer from the file path."""
    rel = os.path.relpath(filepath, SRC_ROOT)

    if rel.startswith("lemmas/common_lemmas"):
        return "common_lemmas"
    elif rel.startswith("lemmas/field_lemmas"):
        return "field_lemmas"
    elif rel.startswith("lemmas/edwards_lemmas"):
        return "edwards_lemmas"
    elif rel.startswith("lemmas/scalar_lemmas_/"):
        return "scalar_lemmas_"
    elif rel.startswith("lemmas/scalar_byte_lemmas"):
        return "scalar_byte_lemmas"
    elif rel.startswith("lemmas/ristretto_lemmas"):
        return "ristretto_lemmas"
    elif rel.startswith("lemmas/"):
        return "lemmas_other"
    elif rel.startswith("specs/"):
        return "specs"
    elif rel.startswith("backend/"):
        return "backend"
    elif rel.startswith("lizard/"):
        return "lizard"
    else:
        return "exec_top"


def extract_vstd_module(import_path: str) -> str:
    """Extract the vstd module path from an import statement.
    E.g. 'vstd::arithmetic::div_mod::*' -> 'vstd::arithmetic::div_mod'
         'vstd::prelude::*' -> 'vstd::prelude'
         'vstd::arithmetic::power2::pow2' -> 'vstd::arithmetic::power2'
         'vstd::calc' -> 'vstd::calc'
    """
    # Remove trailing ::* or ::{...} or ::specific_item
    # The module is everything up to the last :: before a specific item or *
    parts = import_path.split("::")
    if not parts:
        return import_path

    # If last part is * or looks like a function/type name (lowercase or contains braces)
    # then module is everything before it
    if parts[-1] == "*":
        return "::".join(parts[:-1])

    # If it contains {, it's a grouped import like {a, b, c}
    if "{" in import_path:
        # Find the part before the brace
        brace_idx = import_path.index("{")
        prefix = import_path[:brace_idx].rstrip(":")
        return prefix

    # If the last part starts with lowercase, it's likely a function import
    # and the module is everything before it
    if len(parts) >= 3 and parts[-1][0].islower():
        return "::".join(parts[:-1])

    # Otherwise treat the whole thing as the module (e.g., vstd::calc)
    return import_path


def parse_use_import(line: str):
    """Parse a 'use vstd::...' line. Returns (module_path, list_of_imported_items)."""
    # Match: use vstd::something::something;
    # or: use vstd::something::{item1, item2};
    # or: use vstd::something::*;
    m = re.match(r'^\s*use\s+(vstd::[^;]+);', line)
    if not m:
        return None, []

    import_path = m.group(1).strip()

    # Extract items from grouped import
    brace_m = re.search(r'\{([^}]+)\}', import_path)
    if brace_m:
        items_str = brace_m.group(1)
        items = [item.strip() for item in items_str.split(",") if item.strip()]
        module = import_path[:import_path.index("{")].rstrip(":")
        return module, items
    elif import_path.endswith("::*"):
        module = import_path[:-3]
        return module, ["*"]
    else:
        # Single item import like: use vstd::arithmetic::power2::pow2;
        parts = import_path.split("::")
        if len(parts) >= 3 and parts[-1][0].islower():
            module = "::".join(parts[:-1])
            return module, [parts[-1]]
        elif len(parts) >= 3 and parts[-1][0].isupper():
            # Type import
            module = "::".join(parts[:-1])
            return module, [parts[-1]]
        else:
            # Module-level import (e.g., vstd::calc)
            return import_path, []

    return None, []


def find_direct_vstd_calls(line: str, line_no: int):
    """Find direct vstd:: function calls in a line (not import lines).
    E.g. vstd::arithmetic::power2::lemma2_to64()
         vstd::arithmetic::div_mod::lemma_small_mod(B.0, p())
    Also handles impl vstd::std_specs::... which is a trait impl, not a call.
    """
    results = []

    # Skip import lines
    stripped = line.strip()
    if stripped.startswith("use "):
        return results
    if stripped.startswith("//"):
        return results

    # Find all vstd:: references that are function calls (followed by '(' eventually)
    # or trait impl references (preceded by 'impl')
    for m in re.finditer(r'(vstd::[a-zA-Z0-9_:]+)', line):
        full_path = m.group(1)
        # Determine if this is a function call or a trait/type reference
        # Check if 'impl' precedes it
        before = line[:m.start()].rstrip()
        if before.endswith("impl") or "impl<" in before:
            # This is a trait impl, record as type usage
            results.append(("type_usage", full_path))
        else:
            # Check if it's followed by ( - it's a function call
            after = line[m.end():].lstrip()
            if after.startswith("("):
                # Extract function name
                parts = full_path.split("::")
                func_name = parts[-1]
                module = "::".join(parts[:-1])
                results.append(("call", full_path, module, func_name))
            elif after.startswith("{"):
                # It's an import-like thing in a block
                results.append(("import_block", full_path))
            else:
                # Could be a function reference without parens, or a module path
                # e.g., "use vstd::arithmetic::power2::lemma_pow2_strictly_increases;"
                # already caught by use parsing. Skip here if starts with comment
                results.append(("reference", full_path))

    return results


def scan_file(filepath: str):
    """Scan a single .rs file for all vstd usage."""
    with open(filepath, 'r') as f:
        lines = f.readlines()

    layer = classify_layer(filepath)
    rel_path = os.path.relpath(filepath, SRC_ROOT)

    imports = []          # (module, items)
    direct_calls = []     # (full_path, module, func_name)
    type_usages = []      # (full_path,)
    broadcast_uses = []   # (func_name, is_vstd_origin)

    # Track what's imported from vstd for resolving unqualified calls
    imported_from_vstd = {}  # item_name -> module

    for line_no, line in enumerate(lines, 1):
        stripped = line.strip()

        # --- Parse use vstd:: imports ---
        if re.match(r'^\s*use\s+vstd::', stripped):
            module, items = parse_use_import(stripped)
            if module:
                imports.append((module, items))
                for item in items:
                    if item != "*":
                        imported_from_vstd[item] = module

        # --- Parse direct vstd:: calls/references ---
        if "vstd::" in line and not stripped.startswith("use ") and not stripped.startswith("//"):
            refs = find_direct_vstd_calls(line, line_no)
            for ref in refs:
                if ref[0] == "call":
                    _, full_path, module, func_name = ref
                    direct_calls.append((full_path, module, func_name))
                elif ref[0] == "type_usage":
                    type_usages.append(ref[1])

        # --- Parse broadcast use statements ---
        bm = re.match(r'^\s*broadcast\s+use\s+(.+);', stripped)
        if bm:
            items_str = bm.group(1)
            items = [item.strip() for item in items_str.split(",")]
            for item in items:
                if item:
                    broadcast_uses.append(item)

    return {
        "file": rel_path,
        "layer": layer,
        "imports": imports,
        "direct_calls": direct_calls,
        "type_usages": type_usages,
        "broadcast_uses": broadcast_uses,
        "imported_from_vstd": imported_from_vstd,
    }


# Known vstd broadcast lemmas (functions that exist in vstd modules and are
# used via broadcast use without full qualification)
KNOWN_VSTD_BROADCAST_LEMMAS = {
    # From vstd::arithmetic::mul
    "lemma_mul_is_commutative": "vstd::arithmetic::mul",
    "lemma_mul_is_associative": "vstd::arithmetic::mul",
    "lemma_mul_is_distributive_add": "vstd::arithmetic::mul",
    "lemma_mul_is_distributive_add_other_way": "vstd::arithmetic::mul",
    "lemma_mul_is_distributive_sub": "vstd::arithmetic::mul",
    "lemma_mul_is_distributive_sub_other_way": "vstd::arithmetic::mul",
    "group_mul_is_commutative_and_distributive": "vstd::arithmetic::mul",
    "group_mul_is_distributive": "vstd::arithmetic::mul",
    "lemma_mul_basics_2": "vstd::arithmetic::mul",
    "lemma_mul_basics_3": "vstd::arithmetic::mul",
    "lemma_mul_basics_4": "vstd::arithmetic::mul",
    "lemma_mul_inequality": "vstd::arithmetic::mul",
    "lemma_mul_unary_negation": "vstd::arithmetic::mul",

    # From vstd::arithmetic::div_mod
    "lemma_small_mod": "vstd::arithmetic::div_mod",
    "lemma_mod_self_0": "vstd::arithmetic::div_mod",
    "lemma_mod_multiples_vanish": "vstd::arithmetic::div_mod",
    "lemma_mod_bound": "vstd::arithmetic::div_mod",
    "lemma_mod_twice": "vstd::arithmetic::div_mod",
    "lemma_div_basics_2": "vstd::arithmetic::div_mod",

    # From vstd::arithmetic::power2
    "lemma2_to64": "vstd::arithmetic::power2",
    "lemma2_to64_rest": "vstd::arithmetic::power2",
    "lemma_pow2_pos": "vstd::arithmetic::power2",
    "lemma_pow2_adds": "vstd::arithmetic::power2",
    "lemma_pow2_strictly_increases": "vstd::arithmetic::power2",
    "lemma_pow2_unfold": "vstd::arithmetic::power2",
    "pow2": "vstd::arithmetic::power2",

    # From vstd::arithmetic::power
    "lemma_pow0": "vstd::arithmetic::power",

    # From vstd::bits
    "lemma_u64_shr_is_div": "vstd::bits",
    "lemma_u64_shl_is_mul": "vstd::bits",
    "lemma_u64_mul_pow2_le_max_iff_max_shr": "vstd::bits",
    "lemma_u128_shl_is_mul": "vstd::bits",
}


def main():
    # Collect all .rs files
    rs_files = []
    for root, dirs, files in os.walk(SRC_ROOT):
        for f in files:
            if f.endswith(".rs"):
                rs_files.append(os.path.join(root, f))

    rs_files.sort()

    # Scan all files
    all_results = []
    for filepath in rs_files:
        result = scan_file(filepath)
        all_results.append(result)

    # === Aggregate: vstd modules imported ===
    module_importers = defaultdict(set)  # module -> set of files
    for r in all_results:
        for module, items in r["imports"]:
            module_importers[module].add(r["file"])

    vstd_modules_imported = sorted(
        [{"module": mod, "imported_by_files": sorted(files), "count": len(files)}
         for mod, files in module_importers.items()],
        key=lambda x: -x["count"]
    )

    # === Aggregate: vstd lemmas/functions called ===
    # Track: direct qualified calls (vstd::foo::bar())
    lemma_calls = defaultdict(lambda: {"call_count": 0, "files": set(), "layers": set()})

    for r in all_results:
        for full_path, module, func_name in r["direct_calls"]:
            key = full_path
            lemma_calls[key]["call_count"] += 1
            lemma_calls[key]["files"].add(r["file"])
            lemma_calls[key]["layers"].add(r["layer"])
            lemma_calls[key]["module"] = module
            lemma_calls[key]["func_name"] = func_name

    # Also track broadcast use of vstd lemmas
    broadcast_vstd_lemmas = defaultdict(lambda: {"broadcast_count": 0, "files": set(), "layers": set()})

    for r in all_results:
        # Check if file imports from vstd (to know which broadcast uses could be vstd)
        vstd_imports_in_file = set()
        for module, items in r["imports"]:
            if items == ["*"]:
                vstd_imports_in_file.add(module)
            else:
                for item in items:
                    vstd_imports_in_file.add(f"{module}::{item}")

        for func_name in r["broadcast_uses"]:
            # Check if this is a known vstd function
            if func_name in KNOWN_VSTD_BROADCAST_LEMMAS:
                vstd_module = KNOWN_VSTD_BROADCAST_LEMMAS[func_name]
                full_path = f"{vstd_module}::{func_name}"
                broadcast_vstd_lemmas[full_path]["broadcast_count"] += 1
                broadcast_vstd_lemmas[full_path]["files"].add(r["file"])
                broadcast_vstd_lemmas[full_path]["layers"].add(r["layer"])
                broadcast_vstd_lemmas[full_path]["module"] = vstd_module
                broadcast_vstd_lemmas[full_path]["func_name"] = func_name

                # Also count in overall lemma_calls
                lemma_calls[full_path]["call_count"] += 1
                lemma_calls[full_path]["files"].add(r["file"])
                lemma_calls[full_path]["layers"].add(r["layer"])
                lemma_calls[full_path]["module"] = vstd_module
                lemma_calls[full_path]["func_name"] = func_name

    # Build final lemma list
    vstd_lemmas_called = sorted(
        [{"name": data.get("func_name", key.split("::")[-1]),
          "full_path": key,
          "module": data.get("module", ""),
          "call_count": data["call_count"],
          "called_from_layers": sorted(data["layers"]),
          "called_from_files": sorted(data["files"])}
         for key, data in lemma_calls.items()],
        key=lambda x: -x["call_count"]
    )

    # === Type usages (impl vstd::std_specs::...) ===
    type_usage_counts = defaultdict(lambda: {"count": 0, "files": set(), "layers": set()})
    for r in all_results:
        for tu in r["type_usages"]:
            type_usage_counts[tu]["count"] += 1
            type_usage_counts[tu]["files"].add(r["file"])
            type_usage_counts[tu]["layers"].add(r["layer"])

    vstd_type_usages = sorted(
        [{"trait_path": key,
          "count": data["count"],
          "files": sorted(data["files"]),
          "layers": sorted(data["layers"])}
         for key, data in type_usage_counts.items()],
        key=lambda x: -x["count"]
    )

    # === Totals ===
    total_unique_vstd_lemmas = len(lemma_calls)
    total_vstd_calls = sum(d["call_count"] for d in lemma_calls.values())

    # Top 20
    top_20 = vstd_lemmas_called[:20]

    # === Usage by layer ===
    layer_stats = defaultdict(lambda: {"unique_vstd_lemmas": set(), "total_calls": 0})
    for key, data in lemma_calls.items():
        for layer in data["layers"]:
            layer_stats[layer]["unique_vstd_lemmas"].add(key)
            # We need to count calls per layer, which requires going back to per-file data
    # Recompute per-layer call counts more accurately
    layer_call_counts = defaultdict(int)
    layer_lemma_sets = defaultdict(set)

    for r in all_results:
        layer = r["layer"]
        for full_path, module, func_name in r["direct_calls"]:
            layer_call_counts[layer] += 1
            layer_lemma_sets[layer].add(full_path)

        for func_name in r["broadcast_uses"]:
            if func_name in KNOWN_VSTD_BROADCAST_LEMMAS:
                vstd_module = KNOWN_VSTD_BROADCAST_LEMMAS[func_name]
                full_path = f"{vstd_module}::{func_name}"
                layer_call_counts[layer] += 1
                layer_lemma_sets[layer].add(full_path)

    vstd_usage_by_layer = {
        layer: {
            "unique_vstd_lemmas": len(layer_lemma_sets[layer]),
            "total_calls": layer_call_counts[layer],
            "lemma_names": sorted([p.split("::")[-1] for p in layer_lemma_sets[layer]])
        }
        for layer in sorted(set(list(layer_call_counts.keys()) + list(layer_lemma_sets.keys())))
    }

    # === Broadcast lemmas from vstd ===
    broadcast_lemmas_from_vstd = sorted(
        [{"name": data.get("func_name", key.split("::")[-1]),
          "full_path": key,
          "broadcast_count": data["broadcast_count"],
          "files": sorted(data["files"]),
          "layers": sorted(data["layers"])}
         for key, data in broadcast_vstd_lemmas.items()],
        key=lambda x: -x["broadcast_count"]
    )

    # === Assemble output ===
    output = {
        "experiment": "Experiment 6: vstd Usage Census",
        "source_root": str(SRC_ROOT),
        "total_rs_files_scanned": len(rs_files),
        "vstd_modules_imported": vstd_modules_imported,
        "vstd_lemmas_called": vstd_lemmas_called,
        "vstd_type_usages": vstd_type_usages,
        "total_unique_vstd_lemmas_used": total_unique_vstd_lemmas,
        "total_vstd_calls": total_vstd_calls,
        "top_20_most_used": top_20,
        "vstd_usage_by_layer": vstd_usage_by_layer,
        "broadcast_lemmas_from_vstd": broadcast_lemmas_from_vstd,
        "summary": {
            "total_vstd_modules_imported": len(vstd_modules_imported),
            "total_unique_vstd_lemmas_called": total_unique_vstd_lemmas,
            "total_vstd_lemma_calls": total_vstd_calls,
            "total_type_trait_impls": len(vstd_type_usages),
            "total_broadcast_vstd_lemmas": len(broadcast_lemmas_from_vstd),
            "layers_using_vstd": sorted(vstd_usage_by_layer.keys()),
        }
    }

    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, 'w') as f:
        json.dump(output, f, indent=2, default=list)

    # Print summary
    print(f"=== Experiment 6: vstd Usage Census ===")
    print(f"Files scanned: {len(rs_files)}")
    print(f"vstd modules imported: {len(vstd_modules_imported)}")
    print(f"Unique vstd lemmas/functions called: {total_unique_vstd_lemmas}")
    print(f"Total vstd call sites: {total_vstd_calls}")
    print(f"Total vstd trait impls: {len(vstd_type_usages)}")
    print(f"Total broadcast use of vstd lemmas: {len(broadcast_lemmas_from_vstd)}")
    print()

    print("--- Top 10 vstd Modules by Import Count ---")
    for m in vstd_modules_imported[:10]:
        print(f"  {m['module']:45s}  ({m['count']} files)")
    print()

    print("--- Top 20 Most Called vstd Lemmas ---")
    for l in top_20:
        print(f"  {l['full_path']:60s}  calls={l['call_count']:3d}  layers={l['called_from_layers']}")
    print()

    print("--- vstd Usage by Layer ---")
    for layer, stats in sorted(vstd_usage_by_layer.items()):
        print(f"  {layer:25s}  unique={stats['unique_vstd_lemmas']:3d}  total_calls={stats['total_calls']:3d}")
    print()

    print("--- Broadcast Use of vstd Lemmas ---")
    for bl in broadcast_lemmas_from_vstd:
        print(f"  {bl['full_path']:60s}  count={bl['broadcast_count']:3d}")
    print()

    print("--- vstd Trait Impls (impl vstd::std_specs::...) ---")
    for tu in vstd_type_usages[:15]:
        print(f"  {tu['trait_path']:60s}  count={tu['count']:3d}")

    print(f"\nOutput saved to: {OUTPUT_PATH}")


if __name__ == "__main__":
    main()
