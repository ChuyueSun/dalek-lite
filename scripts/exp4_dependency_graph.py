#!/usr/bin/env python3
"""
Experiment 4: Cross-Layer Dependency Graph for dalek-lite Verus codebase.

Builds the actual dependency DAG between lemma files based on `use` imports
and function calls to lemma_* functions. Assigns layers, detects cycles,
computes topological order, and identifies layer violations.
"""

import os
import re
import json
from collections import defaultdict, deque
from pathlib import Path

LEMMAS_DIR = Path("/root/dalek-lite/curve25519-dalek/src/lemmas")
SPECS_DIR = Path("/root/dalek-lite/curve25519-dalek/src/specs")
SRC_DIR = Path("/root/dalek-lite/curve25519-dalek/src")
OUTPUT = Path("/root/experiment_results/exp4_dependency_graph.json")


def get_all_lemma_files():
    """Get all .rs files under src/lemmas/, excluding mod.rs files."""
    files = []
    for root, dirs, filenames in os.walk(LEMMAS_DIR):
        for f in filenames:
            if f.endswith('.rs') and f != 'mod.rs':
                files.append(Path(root) / f)
    return sorted(files)


def get_all_spec_files():
    """Get all .rs files under src/specs/, excluding mod.rs."""
    files = []
    for root, dirs, filenames in os.walk(SPECS_DIR):
        for f in filenames:
            if f.endswith('.rs') and f != 'mod.rs':
                files.append(Path(root) / f)
    return sorted(files)


def file_to_key(filepath):
    """Convert a filepath to a short key relative to src/."""
    return str(filepath.relative_to(SRC_DIR))


def resolve_use_path(use_path, source_file):
    """
    Resolve a Rust `use` path to a target file key.

    Handles:
    - crate::lemmas::... paths
    - crate::specs::... paths
    - super::... paths
    - super::super::... paths
    """
    parts = use_path.split('::')

    if parts[0] == 'crate':
        # Absolute path from crate root
        # e.g., crate::lemmas::common_lemmas::pow_lemmas::*
        # e.g., crate::specs::field_specs::*
        if len(parts) < 3:
            return None

        if parts[1] == 'lemmas':
            return resolve_crate_lemma_path(parts[2:])
        elif parts[1] == 'specs':
            return resolve_crate_spec_path(parts[2:])
        return None

    elif parts[0] == 'super':
        return resolve_super_path(parts, source_file)

    return None


def resolve_crate_lemma_path(parts):
    """
    Resolve lemma path parts after crate::lemmas::
    e.g., ['common_lemmas', 'pow_lemmas', '*'] -> lemmas/common_lemmas/pow_lemmas.rs
    e.g., ['scalar_lemmas', '*'] -> lemmas/scalar_lemmas.rs
    """
    if not parts:
        return None

    # Try different interpretations
    # Case 1: parts = [dir, file, item...] -> lemmas/dir/file.rs
    # Case 2: parts = [file, item...] -> lemmas/file.rs

    # First, check if parts[0] is a directory
    candidate_dir = LEMMAS_DIR / parts[0]

    if candidate_dir.is_dir() and len(parts) >= 2:
        # It's a subdirectory, next part should be the file
        candidate_file = candidate_dir / f"{parts[1]}.rs"
        if candidate_file.exists():
            return file_to_key(candidate_file)
        # Maybe parts[1] is a function name, and the import is from mod.rs / the dir itself
        # This happens with `use crate::lemmas::common_lemmas::*;`
        # which imports everything from the common_lemmas module (mod.rs re-exports)
        # We treat this as a dependency on the entire module, but since we skip mod.rs,
        # we'll return None here (it's a glob re-export)
        return None

    # It's a file directly under lemmas/
    candidate_file = LEMMAS_DIR / f"{parts[0]}.rs"
    if candidate_file.exists():
        return file_to_key(candidate_file)

    return None


def resolve_crate_spec_path(parts):
    """
    Resolve spec path parts after crate::specs::
    e.g., ['field_specs', '*'] -> specs/field_specs.rs
    """
    if not parts:
        return None

    candidate_file = SPECS_DIR / f"{parts[0]}.rs"
    if candidate_file.exists():
        return file_to_key(candidate_file)

    return None


def resolve_super_path(parts, source_file):
    """
    Resolve super:: paths relative to the source file.

    super:: goes up one level from the current file's module.
    super::super:: goes up two levels, etc.
    """
    # Start from the directory containing the source file
    current_dir = source_file.parent

    idx = 0
    while idx < len(parts) and parts[idx] == 'super':
        current_dir = current_dir.parent
        idx += 1

    if idx >= len(parts):
        return None

    remaining = parts[idx:]

    if not remaining:
        return None

    # Now resolve the remaining parts from current_dir
    # Check if remaining[0] is a subdir
    candidate_dir = current_dir / remaining[0]
    if candidate_dir.is_dir() and len(remaining) >= 2:
        candidate_file = candidate_dir / f"{remaining[1]}.rs"
        if candidate_file.exists():
            return file_to_key(candidate_file)
        return None

    # Check if it's a file
    candidate_file = current_dir / f"{remaining[0]}.rs"
    if candidate_file.exists():
        return file_to_key(candidate_file)

    return None


def is_lemma_file(key):
    """Check if a key refers to a lemma file."""
    return key.startswith('lemmas/')


def is_spec_file(key):
    """Check if a key refers to a spec file."""
    return key.startswith('specs/')


def extract_imports(filepath):
    """
    Extract all use imports from a .rs file.
    Returns list of (use_path, is_specific_item) tuples.
    """
    imports = []
    try:
        content = filepath.read_text(encoding='utf-8')
    except Exception:
        return imports

    # Match `use some::path::*;` and `use some::path::item;`
    # Also handle `use some::path::{item1, item2};`
    # Handle multi-line use statements

    # Pattern for simple use: use path::to::thing;
    # Pattern for glob use: use path::to::*;
    # Pattern for specific items: use path::to::{item1, item2};
    # Pattern for single item: use path::to::item;

    # Remove block comments
    content_no_comments = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
    # Remove line comments
    content_no_comments = re.sub(r'//.*', '', content_no_comments)

    # Find all use statements - handle multi-line by joining
    # Pattern: use <path>;
    use_pattern = re.compile(
        r'use\s+((?:crate|super)(?:::\w+)+)(?:::\{[^}]*\}|::\*|::\w+)?\s*;',
        re.MULTILINE
    )

    # More comprehensive: find all use statements
    # First, let's find complete use statements (may span multiple lines)
    use_stmt_pattern = re.compile(r'use\s+((?:crate|super)[^;]+);', re.MULTILINE)

    for m in use_stmt_pattern.finditer(content_no_comments):
        use_body = m.group(1).strip()
        # Clean up whitespace
        use_body = re.sub(r'\s+', '', use_body)

        # Handle brace groups: use path::{a, b, c};
        brace_match = re.match(r'(.+)::\{(.+)\}', use_body)
        if brace_match:
            base_path = brace_match.group(1)
            items = brace_match.group(2).split(',')
            for item in items:
                item = item.strip()
                if item:
                    imports.append(f"{base_path}::{item}")
        else:
            imports.append(use_body)

    return imports


def extract_lemma_function_calls(filepath, all_lemma_functions):
    """
    Extract calls to lemma_* functions from other files.
    Returns set of function names called.
    """
    try:
        content = filepath.read_text(encoding='utf-8')
    except Exception:
        return set()

    called = set()
    # Find all lemma_* function calls
    call_pattern = re.compile(r'\b(lemma_\w+)\s*[(<]')
    for m in call_pattern.finditer(content):
        fname = m.group(1)
        if fname in all_lemma_functions:
            called.add(fname)

    # Also find proof_* and axiom_* calls
    for prefix in ['proof_', 'axiom_']:
        pat = re.compile(rf'\b({prefix}\w+)\s*[(<]')
        for m in pat.finditer(content):
            fname = m.group(1)
            if fname in all_lemma_functions:
                called.add(fname)

    return called


def build_function_index(lemma_files):
    """
    Build an index mapping function names to their defining file.
    Only indexes lemma_*, proof_*, axiom_* functions.
    """
    func_to_file = {}

    for filepath in lemma_files:
        key = file_to_key(filepath)
        try:
            content = filepath.read_text(encoding='utf-8')
        except Exception:
            continue

        # Match function definitions (pub proof fn, proof fn, pub fn, etc.)
        fn_pattern = re.compile(
            r'(?:pub\s+)?(?:broadcast\s+)?(?:proof\s+)?fn\s+((?:lemma|proof|axiom)_\w+)\s*[(<]'
        )
        for m in fn_pattern.finditer(content):
            fname = m.group(1)
            func_to_file[fname] = key

    return func_to_file


def assign_layer(file_key):
    """
    Assign a layer number to a file based on its path.

    Layer assignments:
    - 0: common_lemmas (bit, arithmetic, general utilities)
    - 1: field_lemmas/u64_5_as_nat_lemmas, field_lemmas/pow2_51_lemmas (field repr fundamentals)
    - 2: field_lemmas (arithmetic: add, mul, negate, reduce, from_bytes, load8, limbs_to_bytes, to_bytes, as_bytes)
    - 3: field_lemmas (algebraic: field_algebra, constants, compute_q, pow_chain, pow2k, pow22501, pow_p58, sqrt_m1)
    - 4: field_lemmas (high-level: invert, batch_invert, sqrt_ratio)
    - 5: scalar_lemmas, scalar_byte_lemmas, scalar_lemmas_, scalar_montgomery, scalar_batch_invert, montgomery_pow_chain
    - 6: edwards_lemmas (foundational: constants, curve_equation, step1, decompress)
    - 7: edwards_lemmas (operations: double, niels_addition, mul_base, pippenger, straus, vartime)
    - 8: montgomery_lemmas, montgomery_curve_lemmas
    - 9: ristretto_lemmas
    """

    if 'common_lemmas/' in file_key:
        return 0

    if 'field_lemmas/' in file_key:
        basename = os.path.basename(file_key).replace('.rs', '')
        if basename in ('u64_5_as_nat_lemmas', 'pow2_51_lemmas'):
            return 1
        if basename in ('add_lemmas', 'mul_lemmas', 'negate_lemmas', 'reduce_lemmas',
                        'from_bytes_lemmas', 'load8_lemmas', 'limbs_to_bytes_lemmas',
                        'to_bytes_reduction_lemmas', 'as_bytes_lemmas'):
            return 2
        if basename in ('field_algebra_lemmas', 'constants_lemmas', 'compute_q_lemmas',
                        'pow_chain_lemmas', 'pow2k_lemmas', 'pow22501_t3_lemma',
                        'pow22501_t19_lemma', 'pow_p58_lemma', 'sqrt_m1_lemmas'):
            return 3
        if basename in ('invert_lemmas', 'batch_invert_lemmas', 'sqrt_ratio_lemmas'):
            return 4
        # Fallback for any unclassified field lemma
        return 3

    if ('scalar_lemmas' in file_key or 'scalar_byte_lemmas/' in file_key or
        'scalar_lemmas_/' in file_key or 'scalar_montgomery' in file_key or
        'scalar_batch_invert' in file_key or 'montgomery_pow_chain' in file_key):
        return 5

    if 'edwards_lemmas/' in file_key:
        basename = os.path.basename(file_key).replace('.rs', '')
        if basename in ('constants_lemmas', 'curve_equation_lemmas', 'step1_lemmas',
                        'decompress_lemmas'):
            return 6
        # Operations: double, niels_addition, mul_base, pippenger, straus, vartime
        return 7

    if 'montgomery_lemmas' in file_key or 'montgomery_curve_lemmas' in file_key:
        return 8

    if 'ristretto_lemmas/' in file_key:
        return 9

    # Fallback
    return 5


def detect_cycles(graph, nodes):
    """
    DFS-based cycle detection.
    Returns list of cycles found (each cycle is a list of nodes).
    """
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {n: WHITE for n in nodes}
    parent = {n: None for n in nodes}
    cycles = []

    def dfs(u, path):
        color[u] = GRAY
        path.append(u)
        for v in graph.get(u, []):
            if v not in color:
                continue
            if color[v] == GRAY:
                # Found a cycle: extract it from path
                cycle_start = path.index(v)
                cycle = path[cycle_start:] + [v]
                cycles.append(cycle)
            elif color[v] == WHITE:
                dfs(v, path)
        path.pop()
        color[u] = BLACK

    for n in nodes:
        if color[n] == WHITE:
            dfs(n, [])

    return cycles


def topological_sort(graph, nodes):
    """
    Kahn's algorithm for topological sort.
    Returns (order, has_cycle).
    """
    in_degree = defaultdict(int)
    for n in nodes:
        if n not in in_degree:
            in_degree[n] = 0

    for u in graph:
        for v in graph[u]:
            if v in nodes:
                in_degree[v] += 1

    queue = deque([n for n in nodes if in_degree[n] == 0])
    order = []

    while queue:
        u = queue.popleft()
        order.append(u)
        for v in graph.get(u, []):
            if v in nodes:
                in_degree[v] -= 1
                if in_degree[v] == 0:
                    queue.append(v)

    has_cycle = len(order) != len(nodes)
    return order, has_cycle


def layer_name(layer_num):
    """Human-readable layer name."""
    names = {
        0: "common_lemmas",
        1: "field_repr_fundamentals",
        2: "field_arithmetic",
        3: "field_algebraic",
        4: "field_high_level",
        5: "scalar_lemmas",
        6: "edwards_foundational",
        7: "edwards_operations",
        8: "montgomery_lemmas",
        9: "ristretto_lemmas",
    }
    return names.get(layer_num, f"layer_{layer_num}")


def main():
    # 1. Discover all files
    lemma_files = get_all_lemma_files()
    spec_files = get_all_spec_files()

    lemma_keys = set()
    spec_keys = set()

    for f in lemma_files:
        lemma_keys.add(file_to_key(f))
    for f in spec_files:
        spec_keys.add(file_to_key(f))

    print(f"Found {len(lemma_keys)} lemma files, {len(spec_keys)} spec files")

    # 2. Build function index for cross-file call detection
    func_to_file = build_function_index(lemma_files)
    print(f"Indexed {len(func_to_file)} lemma/proof/axiom functions")

    # 3. Extract dependencies
    # graph: source -> set of targets (lemma files only)
    graph = defaultdict(set)
    spec_deps = defaultdict(set)  # lemma_file -> set of spec files

    for filepath in lemma_files:
        src_key = file_to_key(filepath)
        imports = extract_imports(filepath)

        for use_path in imports:
            target = resolve_use_path(use_path, filepath)
            if target is None:
                continue
            if target == src_key:
                continue  # skip self-imports

            if is_lemma_file(target) and target in lemma_keys:
                graph[src_key].add(target)
            elif is_spec_file(target) and target in spec_keys:
                spec_deps[src_key].add(target)

        # Also detect cross-file function calls
        called_funcs = extract_lemma_function_calls(filepath, func_to_file)
        for fname in called_funcs:
            target_key = func_to_file[fname]
            if target_key != src_key and target_key in lemma_keys:
                graph[src_key].add(target_key)

    # Convert sets to sorted lists for JSON serialization
    edges = []
    for src in sorted(graph.keys()):
        for tgt in sorted(graph[src]):
            edges.append({"from": src, "to": tgt})

    print(f"Found {len(edges)} edges between lemma files")

    # 4. Assign layers
    file_layers = {}
    for key in lemma_keys:
        file_layers[key] = assign_layer(key)

    # 5. Detect cycles
    cycles = detect_cycles(dict(graph), lemma_keys)
    print(f"Found {len(cycles)} cycles")

    # 6. Topological order
    topo_order, has_cycle = topological_sort(dict(graph), lemma_keys)
    print(f"Topological sort: {'has cycle' if has_cycle else 'clean'}, {len(topo_order)} nodes ordered")

    # 7. Layer violations
    layer_violations = []
    for src in graph:
        src_layer = file_layers.get(src, -1)
        for tgt in graph[src]:
            tgt_layer = file_layers.get(tgt, -1)
            if tgt_layer > src_layer:
                layer_violations.append({
                    "from": src,
                    "from_layer": src_layer,
                    "to": tgt,
                    "to_layer": tgt_layer,
                    "violation": f"layer {src_layer} depends on layer {tgt_layer}"
                })

    print(f"Found {len(layer_violations)} layer violations")

    # 8. Compute fanin / fanout
    fanin = defaultdict(int)   # how many files depend on this file
    fanout = defaultdict(int)  # how many files this file depends on

    for key in lemma_keys:
        fanout[key] = len(graph.get(key, set()))

    for src in graph:
        for tgt in graph[src]:
            fanin[tgt] += 1

    # Ensure all keys present
    for key in lemma_keys:
        if key not in fanin:
            fanin[key] = 0

    # Top 10 fanin
    top_fanin = sorted(fanin.items(), key=lambda x: -x[1])[:10]
    # Top 10 fanout
    top_fanout = sorted(fanout.items(), key=lambda x: -x[1])[:10]

    # 9. Layer summary
    layers = defaultdict(lambda: {
        "files": [],
        "internal_edges": 0,
        "edges_to_lower": 0,
        "edges_to_higher": 0,
    })

    for key in sorted(lemma_keys):
        layer = file_layers[key]
        layers[layer]["files"].append(key)

    for src in graph:
        src_layer = file_layers.get(src, -1)
        for tgt in graph[src]:
            tgt_layer = file_layers.get(tgt, -1)
            if src_layer == tgt_layer:
                layers[src_layer]["internal_edges"] += 1
            elif tgt_layer < src_layer:
                layers[src_layer]["edges_to_lower"] += 1
            else:
                layers[src_layer]["edges_to_higher"] += 1

    # Convert layer summary
    layer_summary = {}
    for layer_num in sorted(layers.keys()):
        info = layers[layer_num]
        layer_summary[f"layer_{layer_num}_{layer_name(layer_num)}"] = {
            "layer": layer_num,
            "name": layer_name(layer_num),
            "file_count": len(info["files"]),
            "files": sorted(info["files"]),
            "internal_edges": info["internal_edges"],
            "edges_to_lower": info["edges_to_lower"],
            "edges_to_higher": info["edges_to_higher"],
        }

    # 10. Spec dependencies
    spec_dep_summary = {}
    for lemma_key in sorted(spec_deps.keys()):
        spec_dep_summary[lemma_key] = sorted(spec_deps[lemma_key])

    # Also compute reverse: which spec files are used by how many lemma files
    spec_usage = defaultdict(list)
    for lemma_key, specs in spec_deps.items():
        for s in specs:
            spec_usage[s].append(lemma_key)

    spec_usage_summary = {}
    for spec_key in sorted(spec_usage.keys()):
        spec_usage_summary[spec_key] = {
            "used_by_count": len(spec_usage[spec_key]),
            "used_by": sorted(spec_usage[spec_key]),
        }

    # 11. Build output
    result = {
        "experiment": "exp4_dependency_graph",
        "description": "Cross-layer dependency DAG for lemma files in dalek-lite Verus codebase",
        "summary": {
            "total_lemma_files": len(lemma_keys),
            "total_spec_files": len(spec_keys),
            "total_edges": len(edges),
            "total_cycles": len(cycles),
            "total_layer_violations": len(layer_violations),
            "total_layers": len(layers),
            "indexed_functions": len(func_to_file),
        },
        "cycles": [
            {"cycle": c, "length": len(c) - 1}
            for c in cycles
        ],
        "layer_violations": sorted(layer_violations, key=lambda x: (x["from_layer"], x["to_layer"])),
        "topological_order": topo_order,
        "topological_order_has_cycle": has_cycle,
        "highest_fanin": [
            {"file": k, "fanin": v, "layer": file_layers.get(k, -1)}
            for k, v in top_fanin
        ],
        "highest_fanout": [
            {"file": k, "fanout": v, "layer": file_layers.get(k, -1)}
            for k, v in top_fanout
        ],
        "layer_summary": layer_summary,
        "spec_dependencies": {
            "per_lemma_file": spec_dep_summary,
            "per_spec_file": spec_usage_summary,
        },
        "all_edges": edges,
        "file_layers": {k: {"layer": v, "layer_name": layer_name(v)} for k, v in sorted(file_layers.items())},
    }

    # Write output
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT, 'w') as f:
        json.dump(result, f, indent=2)

    print(f"\nOutput written to {OUTPUT}")

    # Print summary
    print("\n=== SUMMARY ===")
    print(f"Nodes: {len(lemma_keys)}")
    print(f"Edges: {len(edges)}")
    print(f"Cycles: {len(cycles)}")
    print(f"Layer violations: {len(layer_violations)}")

    print("\n=== LAYER SUMMARY ===")
    for lname, info in sorted(layer_summary.items()):
        print(f"  {lname}: {info['file_count']} files, "
              f"{info['internal_edges']} internal, "
              f"{info['edges_to_lower']} to lower, "
              f"{info['edges_to_higher']} to higher")

    print("\n=== TOP 10 FANIN (most depended-upon) ===")
    for k, v in top_fanin:
        print(f"  {k}: {v} (layer {file_layers.get(k, -1)})")

    print("\n=== TOP 10 FANOUT (most dependencies) ===")
    for k, v in top_fanout:
        print(f"  {k}: {v} (layer {file_layers.get(k, -1)})")

    if cycles:
        print("\n=== CYCLES ===")
        for i, c in enumerate(cycles):
            print(f"  Cycle {i+1}: {' -> '.join(c)}")

    if layer_violations:
        print("\n=== LAYER VIOLATIONS ===")
        for v in sorted(layer_violations, key=lambda x: (x['from_layer'], x['to_layer'])):
            print(f"  {v['from']} (L{v['from_layer']}) -> {v['to']} (L{v['to_layer']})")


if __name__ == '__main__':
    main()
