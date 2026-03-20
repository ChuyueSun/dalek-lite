#!/usr/bin/env python3
"""Experiment 12: Proof Effort from Git History

Uses git commit timestamps and PR data to measure how long each proof took.
Maps difficulty by human time investment.
"""

import json
import os
import re
import subprocess
from collections import defaultdict
from pathlib import Path
from datetime import datetime

BASE = Path("/root/dalek-lite/curve25519-dalek")


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


def get_all_commits():
    """Get all commits with their dates and messages."""
    log = run_git(["log", "--format=%H|%ai|%an|%s", "--all"])
    commits = []
    for line in log.split('\n'):
        if not line.strip():
            continue
        parts = line.split('|', 3)
        if len(parts) == 4:
            commits.append({
                "hash": parts[0],
                "date": parts[1][:10],  # Just the date
                "author": parts[2],
                "message": parts[3],
            })
    return commits


def get_file_history(filepath):
    """Get commit history for a specific file."""
    log = run_git(["log", "--format=%H|%ai|%an|%s", "--follow", "--", filepath])
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


def get_pr_info_from_commits(commits):
    """Extract PR numbers from commit messages."""
    prs = set()
    for c in commits:
        for m in re.finditer(r'#(\d+)', c["message"]):
            prs.add(int(m.group(1)))
    return sorted(prs)


def get_commit_stats(commit_hash):
    """Get insertions/deletions for a commit."""
    stat = run_git(["show", "--stat", "--format=", commit_hash])
    insertions = 0
    deletions = 0
    files_changed = 0
    for line in stat.split('\n'):
        m = re.search(r'(\d+) files? changed', line)
        if m:
            files_changed = int(m.group(1))
        m = re.search(r'(\d+) insertions?', line)
        if m:
            insertions = int(m.group(1))
        m = re.search(r'(\d+) deletions?', line)
        if m:
            deletions = int(m.group(1))
    return insertions, deletions, files_changed


def analyze_lemma_files():
    """Analyze git history for all lemma files."""
    lemma_dir = BASE / "src" / "lemmas"
    results = []

    for f in sorted(lemma_dir.rglob("*.rs")):
        if f.name == "mod.rs":
            continue

        rel_path = str(f.relative_to(BASE))
        history = get_file_history(rel_path)

        if not history:
            continue

        authors = set(c["author"] for c in history)
        prs = get_pr_info_from_commits(history)

        results.append({
            "file": rel_path,
            "total_commits": len(history),
            "first_commit": history[-1]["date"] if history else None,
            "last_commit": history[0]["date"] if history else None,
            "authors": sorted(authors),
            "pr_numbers": prs,
            "num_revisions": len(history),
        })

    return results


def analyze_proof_prs():
    """Find PRs related to proofs and analyze their effort."""
    all_commits = get_all_commits()

    # Group commits by PR number
    pr_commits = defaultdict(list)
    for c in all_commits:
        for m in re.finditer(r'#(\d+)', c["message"]):
            pr_commits[int(m.group(1))].append(c)

    # Find proof-related PRs
    proof_keywords = ['prove', 'proof', 'verify', 'lemma', 'admit', 'ensures',
                      'invariant', 'spec', 'verus', 'Prove', 'Proof']

    proof_prs = []
    for c in all_commits:
        msg = c["message"]
        # Check for proof keywords
        is_proof = any(kw.lower() in msg.lower() for kw in proof_keywords)
        if is_proof:
            # Extract PR number if present
            pr_match = re.search(r'\(#(\d+)\)', msg)
            pr_num = int(pr_match.group(1)) if pr_match else None

            # Get stats for this commit
            insertions, deletions, files_changed = get_commit_stats(c["hash"])

            proof_prs.append({
                "commit": c["hash"][:8],
                "date": c["date"],
                "author": c["author"],
                "message": msg,
                "pr_number": pr_num,
                "insertions": insertions,
                "deletions": deletions,
                "files_changed": files_changed,
            })

    return proof_prs


def find_ai_contributions(commits):
    """Find commits that mention AI tools."""
    ai_keywords = ['claude', 'Claude', 'aider', 'Aider', 'cursor', 'Cursor',
                    'copilot', 'Copilot', 'AI', 'GPT', 'gpt', 'LLM', 'llm',
                    'auto-generated', 'generated']
    ai_commits = []
    for c in commits:
        msg = c.get("message", "")
        for kw in ai_keywords:
            if kw in msg:
                ai_commits.append({
                    "commit": c.get("commit", c.get("hash", ""))[:8],
                    "date": c["date"],
                    "message": msg,
                    "ai_keyword": kw,
                })
                break
    return ai_commits


def analyze_by_domain():
    """Group proof effort by domain/layer."""
    domains = {
        "field": {"keywords": ["field", "fe51", "limb"], "files": ["field"]},
        "scalar": {"keywords": ["scalar", "montgomery_reduce", "radix"], "files": ["scalar"]},
        "edwards": {"keywords": ["edwards", "decompress", "compress", "niels", "double"], "files": ["edwards"]},
        "ristretto": {"keywords": ["ristretto", "elligator"], "files": ["ristretto"]},
        "montgomery": {"keywords": ["montgomery", "mul_base"], "files": ["montgomery"]},
        "scalar_mul": {"keywords": ["straus", "pippenger", "scalar_mul", "vartime"], "files": ["scalar_mul"]},
    }

    all_commits = get_all_commits()
    domain_stats = {}

    for domain, info in domains.items():
        domain_commits = []
        for c in all_commits:
            msg = c["message"].lower()
            if any(kw in msg for kw in info["keywords"]):
                domain_commits.append(c)

        if domain_commits:
            dates = [c["date"] for c in domain_commits]
            prs = get_pr_info_from_commits(domain_commits)
            authors = set(c["author"] for c in domain_commits)

            total_insertions = 0
            for c in domain_commits[:20]:  # Limit to avoid too many git calls
                ins, _, _ = get_commit_stats(c["hash"])
                total_insertions += ins

            domain_stats[domain] = {
                "total_commits": len(domain_commits),
                "first_date": min(dates),
                "last_date": max(dates),
                "total_prs": len(prs),
                "authors": sorted(authors),
                "sample_insertions": total_insertions,
            }

    return domain_stats


def main():
    print("Analyzing proof effort from git history...")

    # 1. Analyze lemma files
    print("\n1. Analyzing lemma files...")
    lemma_files = analyze_lemma_files()
    print(f"   Found {len(lemma_files)} lemma files with history")

    # 2. Analyze proof PRs
    print("\n2. Analyzing proof-related commits...")
    proof_prs = analyze_proof_prs()
    print(f"   Found {len(proof_prs)} proof-related commits")

    # 3. Find AI contributions
    print("\n3. Finding AI contributions...")
    ai_commits = find_ai_contributions(proof_prs)
    print(f"   Found {len(ai_commits)} AI-related commits")

    # 4. Analyze by domain
    print("\n4. Analyzing by domain...")
    domain_stats = analyze_by_domain()

    # Sort proof PRs by insertions to find hardest
    proof_prs_sorted = sorted(proof_prs, key=lambda x: x["insertions"], reverse=True)
    hardest_proofs = proof_prs_sorted[:15]

    # Sort by date for timeline
    proof_prs_by_date = sorted(proof_prs, key=lambda x: x["date"])

    # Compute summary stats
    total_insertions = sum(p["insertions"] for p in proof_prs)
    total_deletions = sum(p["deletions"] for p in proof_prs)
    unique_authors = set(p["author"] for p in proof_prs)
    unique_prs = set(p["pr_number"] for p in proof_prs if p["pr_number"])

    result = {
        "summary": {
            "total_proof_commits": len(proof_prs),
            "total_unique_prs": len(unique_prs),
            "total_insertions": total_insertions,
            "total_deletions": total_deletions,
            "unique_authors": sorted(unique_authors),
            "date_range": {
                "first": proof_prs_by_date[0]["date"] if proof_prs_by_date else None,
                "last": proof_prs_by_date[-1]["date"] if proof_prs_by_date else None,
            },
        },
        "hardest_proofs_by_insertions": hardest_proofs,
        "by_domain": domain_stats,
        "lemma_files": lemma_files[:30],  # Top 30
        "ai_involved_proofs": ai_commits,
        "all_proof_commits": proof_prs[:100],  # First 100
    }

    out_path = "/root/dalek-lite/experiment_results/exp12_proof_effort.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    print(f"\nResults written to {out_path}")
    print(f"\nSummary:")
    print(f"  Total proof commits: {len(proof_prs)}")
    print(f"  Total unique PRs: {len(unique_prs)}")
    print(f"  Total insertions: {total_insertions}")
    print(f"  Unique authors: {sorted(unique_authors)}")
    print(f"\nHardest proofs (by insertions):")
    for p in hardest_proofs[:5]:
        print(f"  {p['message'][:80]} — {p['insertions']} ins")
    print(f"\nAI contributions: {len(ai_commits)}")
    if ai_commits:
        for ac in ai_commits[:5]:
            print(f"  {ac['message'][:80]} (keyword: {ac['ai_keyword']})")

    print(f"\nBy domain:")
    for domain, stats in sorted(domain_stats.items()):
        print(f"  {domain}: {stats['total_commits']} commits, {stats['total_prs']} PRs")


if __name__ == "__main__":
    main()
