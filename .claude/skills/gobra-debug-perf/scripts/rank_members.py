#!/usr/bin/env python3
"""Rank Gobra members by verification time using the stats.json that Gobra
writes when run with --gobraDirectory <dir>.

Usage:
    rank_members.py gobra-out/stats.json [-n TOP] [--all] [--csv]

Each entry in stats.json is a Gobra member with a list of the Viper members it
was translated into; the time of a Gobra member is the sum of its Viper members'
times (milliseconds). Imported members are excluded by default: they belong to
another package and are only re-checked for well-formedness here.
"""

import argparse
import json
import sys


def load(path):
    with open(path) as f:
        return json.load(f)


def summarize(entry):
    """Return (total_ms, n_viper_members, unfinished, all_cached) for a member."""
    total = 0
    unfinished = []
    cached = True
    counted = 0
    for vm in entry.get("viperMembers", []):
        if vm.get("fromImport"):
            continue
        counted += 1
        if not vm.get("cached", False):
            cached = False
        # `verified` is false for members the backend never got to (e.g. the run
        # was killed or timed out) -- those are the interesting failures.
        if vm.get("hasBody") and not vm.get("verified", False):
            unfinished.append(vm.get("name", "?"))
        total += vm.get("time", 0) or 0
    return total, counted, unfinished, cached


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("stats", help="path to stats.json")
    ap.add_argument("-n", "--top", type=int, default=20, help="how many members to show (default 20)")
    ap.add_argument("--all", action="store_true", help="include imported and abstract members")
    ap.add_argument("--csv", action="store_true", help="emit CSV instead of a table")
    args = ap.parse_args()

    try:
        data = load(args.stats)
    except (OSError, json.JSONDecodeError) as e:
        sys.exit(f"could not read {args.stats}: {e}")

    rows, unfinished_members = [], []
    for entry in data:
        name = entry.get("name") or entry.get("id", "?")
        node_type = entry.get("nodeType", "?")
        is_abstract = entry.get("abstract", False)
        total, counted, unfinished, cached = summarize(entry)
        if unfinished:
            unfinished_members.append((name, unfinished))
        if not args.all and (counted == 0 or is_abstract):
            continue
        rows.append((total, name, node_type, counted, cached))

    rows.sort(reverse=True)
    grand_total = sum(r[0] for r in rows)

    if args.csv:
        print("time_ms,share_pct,name,node_type,viper_members,cached")
        for t, name, nt, c, cached in rows[: args.top]:
            share = 100.0 * t / grand_total if grand_total else 0.0
            print(f"{t},{share:.1f},{name},{nt},{c},{cached}")
        return

    if not rows:
        print("No non-imported members with timing data. "
              "Was the run killed before verification started?")
    else:
        print(f"{'time (s)':>9}  {'share':>6}  {'kind':<24}  member")
        print("-" * 92)
        for t, name, nt, _c, cached in rows[: args.top]:
            share = 100.0 * t / grand_total if grand_total else 0.0
            flag = " [cached]" if cached else ""
            print(f"{t/1000:>9.2f}  {share:>5.1f}%  {nt:<24}  {name}{flag}")
        print("-" * 92)
        print(f"{grand_total/1000:>9.2f}  100.0%  total over {len(rows)} members")

        # A skewed distribution points at individual members; a flat one points
        # at the shared proof context.
        k = min(5, len(rows))
        topk = sum(r[0] for r in rows[:k])
        if grand_total:
            print(f"\ntop {k} member(s) account for {100.0 * topk / grand_total:.0f}% of the time.")

    if unfinished_members:
        print("\nMembers that did not finish verifying (killed, timed out, or diverged):")
        for name, vms in unfinished_members:
            print(f"  - {name}  ({len(vms)} Viper member(s))")


if __name__ == "__main__":
    main()
