#!/usr/bin/env python3
"""Experiment 14: Spec Stability Analysis (from Git History)

Measures how much spec churn occurred and what caused it.
"""

import json
import os
import re
import subprocess
from collections import defaultdict
from pathlib import Path
from datetime import datetime

BASE = Path("/root/dalek-lite/curve25519-dalek")
SPEC_DIR = BASE / "src" / "specs"


def run_git(args, cwd=str(BASE)):
    """Run a git command and return stdout."""
    result = subprocess.run(
        ["git"] + args,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=60,
    )
    return result.stdout.strip()


def get_spec_files():
    """List all spec files."""
    files = []
    if SPEC_DIR.exists():
        for f in sorted(SPEC_DIR.glob("*.rs")):
            if f.name != "mod.rs":
                files.append(f)
    return files


def get_file_commits(filepath):
    """Get detailed commit history for a file."""
    rel_path = str(filepath.relative_to(BASE))
    log = run_git(["log", "--format=%H|%ai|%an|%s", "--follow", "--", rel_path])
    commits = []
    for line in log.split('\n'):
        if not line.strip():
            continue
        parts = line.split('|', 3)
        if len(parts) == 4:
            commits.append({
                "hash": parts[0],
                "date": parts[1][:10],
                "author": parts[2],
                "message": parts[3],
            })
    return commits


def get_commit_diff_for_file(commit_hash, filepath):
    """Get the diff for a specific file in a specific commit."""
    rel_path = str(filepath.relative_to(BASE))
    diff = run_git(["show", commit_hash, "--format=", "--", rel_path])
    return diff


def classify_spec_change(diff_text, commit_msg):
    """Classify a spec change based on the diff and commit message."""
    msg_lower = commit_msg.lower()

    # Check commit message for clues
    if 'bugfix' in msg_lower or 'fix spec' in msg_lower or 'correct' in msg_lower:
        return "bugfix"
    if 'refactor' in msg_lower or 'move' in msg_lower or 'reorganize' in msg_lower:
        return "refactored"
    if 'rename' in msg_lower:
        return "renamed"

    # Analyze diff
    added_lines = [l for l in diff_text.split('\n') if l.startswith('+') and not l.startswith('+++')]
    removed_lines = [l for l in diff_text.split('\n') if l.startswith('-') and not l.startswith('---')]

    added_text = '\n'.join(added_lines)
    removed_text = '\n'.join(removed_lines)

    # New spec function added
    if 'spec fn' in added_text or 'spec(checked) fn' in added_text:
        if 'spec fn' not in removed_text and 'spec(checked) fn' not in removed_text:
            return "new_function"

    # Check for ensures changes
    has_ensures_add = 'ensures' in added_text
    has_ensures_remove = 'ensures' in removed_text

    if has_ensures_add and has_ensures_remove:
        # Both added and removed ensures - could be strengthened, weakened, or bugfix
        if len(added_lines) > len(removed_lines):
            return "strengthened"
        elif len(added_lines) < len(removed_lines):
            return "weakened"
        else:
            return "refactored"
    elif has_ensures_add:
        return "strengthened"
    elif has_ensures_remove:
        return "weakened"

    # Formatting/whitespace changes
    if len(added_lines) == len(removed_lines):
        # Check if it's just formatting
        stripped_added = set(l.strip() for l in added_lines)
        stripped_removed = set(l.strip() for l in removed_lines)
        if stripped_added == stripped_removed:
            return "formatting"

    return "refactored"


def count_spec_fns(filepath):
    """Count spec functions in a file."""
    if not filepath.exists():
        return 0
    text = filepath.read_text()
    return len(re.findall(r'(?:pub\s+)?(?:open\s+)?spec\s+fn\s+\w+', text))


def analyze_spec_file(filepath):
    """Analyze a single spec file's history."""
    commits = get_file_commits(filepath)
    if not commits:
        return None

    # Classify each commit's changes
    changes = defaultdict(int)
    commit_details = []

    for c in commits:
        diff = get_commit_diff_for_file(c["hash"], filepath)
        if not diff.strip():
            continue

        change_type = classify_spec_change(diff, c["message"])
        changes[change_type] += 1

        commit_details.append({
            "hash": c["hash"][:8],
            "date": c["date"],
            "author": c["author"],
            "message": c["message"][:100],
            "change_type": change_type,
        })

    # Current spec fn count
    current_spec_fns = count_spec_fns(filepath)

    return {
        "file": filepath.name,
        "total_commits": len(commits),
        "current_spec_fns": current_spec_fns,
        "changes": dict(changes),
        "first_commit": commits[-1]["date"] if commits else None,
        "last_commit": commits[0]["date"] if commits else None,
        "authors": sorted(set(c["author"] for c in commits)),
        "commit_details": commit_details[:20],  # First 20
    }


def find_bugfix_discovery_method(commit_details):
    """Classify how spec bugs were discovered."""
    methods = defaultdict(int)

    for c in commit_details:
        if c.get("change_type") != "bugfix":
            continue

        msg = c.get("message", "").lower()
        if 'proptest' in msg or 'property test' in msg:
            methods["proptest"] += 1
        elif 'claude' in msg or 'ai' in msg or 'aider' in msg:
            methods["ai_found"] += 1
        elif 'review' in msg:
            methods["code_review"] += 1
        else:
            methods["during_proof"] += 1  # Default assumption

    return dict(methods)


def analyze_ripple_effects():
    """When a spec changed, how many other files changed in the same commit?"""
    effects = []

    spec_files = get_spec_files()
    for sf in spec_files:
        commits = get_file_commits(sf)
        for c in commits[:10]:  # Check last 10 commits
            # Get all files changed in this commit
            files_changed = run_git(["show", "--format=", "--name-only", c["hash"]])
            changed_list = [f for f in files_changed.split('\n') if f.strip()]

            # Count proof/lemma files affected
            proof_files = [f for f in changed_list if 'lemma' in f or 'proof' in f]
            if proof_files:
                effects.append({
                    "spec_file": sf.name,
                    "commit": c["hash"][:8],
                    "message": c["message"][:80],
                    "total_files_changed": len(changed_list),
                    "proof_files_affected": len(proof_files),
                })

    return effects


def main():
    print("Analyzing spec stability from git history...")

    spec_files = get_spec_files()
    print(f"Found {len(spec_files)} spec files")

    # Analyze each spec file
    spec_results = {}
    total_changes = defaultdict(int)
    all_commit_details = []

    for sf in spec_files:
        print(f"  Analyzing {sf.name}...")
        result = analyze_spec_file(sf)
        if result:
            spec_results[sf.name] = result
            for change_type, count in result["changes"].items():
                total_changes[change_type] += count
            all_commit_details.extend(result.get("commit_details", []))

    # Bugfix discovery methods
    bugfix_methods = find_bugfix_discovery_method(all_commit_details)

    # Ripple effects
    print("\n  Analyzing ripple effects...")
    ripple_effects = analyze_ripple_effects()

    # Most changed spec files
    most_changed = sorted(spec_results.values(), key=lambda x: x["total_commits"], reverse=True)

    # Compute churn rate
    total_spec_fns = sum(r["current_spec_fns"] for r in spec_results.values())
    total_commits = sum(r["total_commits"] for r in spec_results.values())

    # Date range
    all_dates = []
    for r in spec_results.values():
        if r["first_commit"]:
            all_dates.append(r["first_commit"])
        if r["last_commit"]:
            all_dates.append(r["last_commit"])

    if all_dates:
        first_date = min(all_dates)
        last_date = max(all_dates)
        try:
            d1 = datetime.strptime(first_date, "%Y-%m-%d")
            d2 = datetime.strptime(last_date, "%Y-%m-%d")
            months = max(1, (d2 - d1).days / 30)
            churn_rate = total_commits / total_spec_fns / months if total_spec_fns > 0 else 0
        except:
            churn_rate = 0
    else:
        churn_rate = 0

    result = {
        "spec_files": spec_results,
        "total_spec_changes": sum(total_changes.values()),
        "change_type_totals": dict(total_changes),
        "total_bugfixes": total_changes.get("bugfix", 0),
        "bugfix_discovery_method": bugfix_methods,
        "spec_churn_rate": round(churn_rate, 3),
        "total_spec_fns": total_spec_fns,
        "most_changed_specs": [
            {"file": r["file"], "commits": r["total_commits"], "spec_fns": r["current_spec_fns"]}
            for r in most_changed[:10]
        ],
        "ripple_effects": ripple_effects[:20],
    }

    out_path = "/root/dalek-lite/experiment_results/exp14_spec_stability.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    print(f"\nResults written to {out_path}")
    print(f"\nSummary:")
    print(f"  Total spec files: {len(spec_results)}")
    print(f"  Total spec fns: {total_spec_fns}")
    print(f"  Total spec changes: {sum(total_changes.values())}")
    print(f"  Change types: {dict(total_changes)}")
    print(f"  Churn rate: {churn_rate:.3f} changes/fn/month")
    print(f"\nMost changed specs:")
    for r in most_changed[:5]:
        print(f"  {r['file']}: {r['total_commits']} commits, {r['current_spec_fns']} spec fns")
    print(f"\nRipple effects: {len(ripple_effects)} spec changes affected proof files")


if __name__ == "__main__":
    main()
