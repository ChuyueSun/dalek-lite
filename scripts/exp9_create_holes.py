#!/usr/bin/env python3
"""Create spec holes for Experiment 9.

For each of the 10 functions, extract the full function context
(requires + body + proof blocks) with the ensures clause removed.
"""

import json
import re
from pathlib import Path

BASE = Path("/root/dalek-lite/curve25519-dalek/src")
OUT = Path("/root/dalek-lite/experiment_results/exp9_holes")

# Load manifest
with open("/root/dalek-lite/experiment_results/exp9_gt/manifest.json") as f:
    manifest = json.load(f)


def extract_function_context(filepath, fn_name, line_hint):
    """Extract a function with its ensures clause removed.

    Returns: (full_context_with_ensures, context_without_ensures, ensures_text)
    """
    text = filepath.read_text()
    lines = text.split('\n')

    # Find the function declaration near line_hint
    fn_start = None
    for i in range(max(0, line_hint - 10), min(len(lines), line_hint + 10)):
        # Match fn declaration
        if re.search(rf'\bfn\s+{re.escape(fn_name)}\b', lines[i]):
            fn_start = i
            break

    if fn_start is None:
        # Broader search
        for i in range(len(lines)):
            if re.search(rf'\bfn\s+{re.escape(fn_name)}\b', lines[i]):
                fn_start = i
                break

    if fn_start is None:
        return None, None, None

    # Find requires, ensures, and body
    j = fn_start
    requires_start = None
    requires_end = None
    ensures_start = None
    ensures_end = None
    body_start = None

    # Scan forward from fn declaration to find requires/ensures/body
    while j < len(lines):
        stripped = lines[j].strip()

        if stripped.startswith('requires') and requires_start is None:
            requires_start = j

        if stripped.startswith('ensures') and ensures_start is None:
            ensures_start = j
            # Find end of ensures - it ends at the body opening brace
            k = j + 1
            while k < len(lines):
                ks = lines[k].strip()
                if ks == '{':
                    ensures_end = k  # exclusive: this line is the body start
                    body_start = k
                    break
                k += 1
            break

        # If we hit a lone '{' before ensures, there's no ensures
        if stripped == '{' and j > fn_start:
            body_start = j
            break

        j += 1

    if body_start is None:
        return None, None, None

    # Find the end of the function body
    depth = 0
    body_end = None
    for k in range(body_start, len(lines)):
        for ch in lines[k]:
            if ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
                if depth == 0:
                    body_end = k
                    break
        if body_end is not None:
            break

    if body_end is None:
        body_end = min(body_start + 200, len(lines) - 1)

    # Build context lines: include some imports context (10 lines before fn)
    context_start = max(0, fn_start - 3)

    # Full context with ensures
    full_lines = lines[context_start:body_end + 1]

    # Context without ensures
    if ensures_start is not None and ensures_end is not None:
        hole_lines = (
            lines[context_start:ensures_start] +
            ["    // SPEC HOLE: Write the ensures clause for this function"] +
            lines[ensures_end:body_end + 1]
        )
        ensures_text = '\n'.join(lines[ensures_start:ensures_end])
    else:
        hole_lines = full_lines
        ensures_text = ""

    return '\n'.join(full_lines), '\n'.join(hole_lines), ensures_text


def get_imports_context(filepath):
    """Extract the use/import lines from the file for spec function context."""
    text = filepath.read_text()
    lines = text.split('\n')
    imports = []
    in_verus = False

    for line in lines[:200]:  # First 200 lines usually have all imports
        stripped = line.strip()
        if 'verus!' in stripped:
            in_verus = True
        if stripped.startswith('use ') or stripped.startswith('pub use '):
            imports.append(line)

    return '\n'.join(imports)


def main():
    results = {}

    for sid, info in sorted(manifest.items()):
        fn_name = info["function"]
        filepath = BASE.parent / info["file"]
        line_hint = info["line_number"] - 1  # 0-indexed

        print(f"Processing {sid}: {fn_name} in {info['file']}...")

        full_ctx, hole_ctx, ensures = extract_function_context(filepath, fn_name, line_hint)

        if hole_ctx is None:
            print(f"  WARNING: Could not find function {fn_name}")
            continue

        # Get imports for spec function context
        imports = get_imports_context(filepath)

        # Write the hole file
        hole_path = OUT / f"{sid}_{fn_name}_hole.rs"
        with open(hole_path, 'w') as f:
            f.write(f"// Experiment 9 Spec Hole: {sid}\n")
            f.write(f"// Function: {fn_name}\n")
            f.write(f"// File: {info['file']}\n")
            f.write(f"// Complexity: {info['complexity']} — {info['description']}\n")
            f.write(f"//\n")
            f.write(f"// TASK: Write the ensures clause for this function.\n")
            f.write(f"// The function body, requires clause, and proof blocks are given.\n")
            f.write(f"// Available spec functions can be inferred from the imports below.\n")
            f.write(f"//\n")
            f.write(f"// === IMPORTS (spec function context) ===\n")
            f.write(imports)
            f.write(f"\n\n// === FUNCTION WITH SPEC HOLE ===\n")
            f.write(hole_ctx)
            f.write("\n")

        # Write the full context (with ensures) for reference
        full_path = OUT / f"{sid}_{fn_name}_full.rs"
        with open(full_path, 'w') as f:
            f.write(f"// Experiment 9 Reference: {sid}\n")
            f.write(f"// Function: {fn_name} (WITH ensures clause)\n")
            f.write(full_ctx)
            f.write("\n")

        results[sid] = {
            "function": fn_name,
            "file": info["file"],
            "hole_file": str(hole_path.name),
            "full_file": str(full_path.name),
            "ensures_removed_lines": ensures.count('\n') + 1 if ensures else 0,
            "hole_body_lines": hole_ctx.count('\n') + 1,
            "complexity": info["complexity"],
        }

        print(f"  Created {hole_path.name} ({hole_ctx.count(chr(10))+1} lines)")

    # Write manifest
    manifest_path = OUT / "manifest.json"
    with open(manifest_path, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nCreated {len(results)} spec holes in {OUT}")
    print(f"Manifest: {manifest_path}")


if __name__ == "__main__":
    main()
