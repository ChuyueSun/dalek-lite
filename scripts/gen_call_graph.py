#!/usr/bin/env python3
"""Generate a DOT call graph from probe-verus atoms JSON."""
import json
import sys

def main():
    with open("curve25519-dalek/.verilib/probes/verus_curve25519-dalek_4.1.3_atoms.json") as f:
        data = json.load(f)["data"]

    # Focus on curve25519-dalek atoms only
    c25519 = {k: v for k, v in data.items() if "curve25519" in k}
    print(f"Total curve25519-dalek functions: {len(c25519)}", file=sys.stderr)

    kind_colors = {
        "exec": "#a8d8ea",
        "proof": "#fcbad3",
        "spec": "#ffffd2",
    }

    # Use top 80 functions by dep count for readability
    top_funcs = sorted(
        c25519.items(),
        key=lambda x: len(x[1].get("dependencies", [])),
        reverse=True,
    )[:80]
    top_keys = {k for k, _ in top_funcs}

    def sanitize(s):
        for ch in "/#:.-()<>, ":
            s = s.replace(ch, "_")
        return s

    nodes = {}
    edges = set()

    for k, v in top_funcs:
        node_id = sanitize(k)
        label = v["display-name"]
        mod_name = v.get("code-module", "")
        if mod_name:
            label = f"{label}\\n({mod_name})"
        kind = v.get("kind", "exec")
        color = kind_colors.get(kind, "#ffffff")
        nodes[node_id] = (label, color)

        for dep in v.get("dependencies", []):
            if isinstance(dep, str) and dep in top_keys:
                dep_id = sanitize(dep)
                dep_v = c25519[dep]
                dep_label = dep_v["display-name"]
                dep_mod = dep_v.get("code-module", "")
                if dep_mod:
                    dep_label = f"{dep_label}\\n({dep_mod})"
                dep_kind = dep_v.get("kind", "exec")
                dep_color = kind_colors.get(dep_kind, "#ffffff")
                nodes[dep_id] = (dep_label, dep_color)
                edges.add((node_id, dep_id))

    lines = [
        "digraph call_graph {",
        "  rankdir=LR;",
        '  node [shape=box, fontsize=9, style=filled, fontname="Helvetica"];',
        "  edge [arrowsize=0.5, color=\"#666666\"];",
        "  overlap=false;",
        "  splines=true;",
        "",
    ]

    for nid, (label, color) in sorted(nodes.items()):
        lines.append(f'  "{nid}" [label="{label}", fillcolor="{color}"];')

    lines.append("")
    for src, dst in sorted(edges):
        lines.append(f'  "{src}" -> "{dst}";')

    lines.append("")
    lines.append("  subgraph cluster_legend {")
    lines.append('    label="Legend";')
    lines.append("    style=dashed;")
    lines.append('    leg_exec [label="exec fn", fillcolor="#a8d8ea", style=filled];')
    lines.append('    leg_proof [label="proof fn", fillcolor="#fcbad3", style=filled];')
    lines.append('    leg_spec [label="spec fn", fillcolor="#ffffd2", style=filled];')
    lines.append("  }")
    lines.append("}")

    with open("outputs/call_graph.dot", "w") as f:
        f.write("\n".join(lines))

    print(f"Nodes: {len(nodes)}, Edges: {len(edges)}", file=sys.stderr)
    print("Written to outputs/call_graph.dot", file=sys.stderr)


if __name__ == "__main__":
    main()
