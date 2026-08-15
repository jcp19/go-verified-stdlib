#!/usr/bin/env python3
"""Summarize the per-query CSV produced by Silicon's --recordProofQueries
(https://github.com/viperproject/silicon/pull/966).

Usage:
    summarize_queries.py queries.csv [-n TOP] [--member NAME]

Expected columns: kind,member,file,line,column,category,durationMs,succeeded,description
Missing metadata is rendered as '?' by Silicon.

Prints time and count grouped by category and by member, plus the slowest
individual queries with their source positions — enough to tell "many cheap
queries" (path explosion) from "a few expensive ones" (hard proof goals /
quantified permissions) and to see where they come from.
"""

import argparse
import csv
import sys
from collections import defaultdict


def fmt_ms(ms):
    return f"{ms/1000:.2f}s" if ms >= 1000 else f"{ms:.0f}ms"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("csvfile", help="CSV written by --recordProofQueries")
    ap.add_argument("-n", "--top", type=int, default=15,
                    help="slowest individual queries to list (default 15)")
    ap.add_argument("--member", help="restrict to queries of this member (substring match)")
    args = ap.parse_args()

    rows = []
    try:
        with open(args.csvfile, newline="") as f:
            for row in csv.DictReader(f):
                try:
                    row["durationMs"] = float(row.get("durationMs") or 0)
                except ValueError:
                    continue
                if args.member and args.member not in (row.get("member") or ""):
                    continue
                rows.append(row)
    except OSError as e:
        sys.exit(f"could not read {args.csvfile}: {e}")

    if not rows:
        sys.exit("no queries matched (empty file or --member filter too strict)")

    total_ms = sum(r["durationMs"] for r in rows)
    print(f"{len(rows)} recorded solver interactions, {fmt_ms(total_ms)} total prover time\n")

    def group_table(key, title):
        groups = defaultdict(lambda: [0, 0.0, 0])  # count, ms, failures
        for r in rows:
            g = groups[r.get(key) or "?"]
            g[0] += 1
            g[1] += r["durationMs"]
            if (r.get("succeeded") or "").lower() == "false":
                g[2] += 1
        print(f"{title}:")
        print(f"  {'count':>8}  {'time':>9}  {'share':>6}  {'failed':>6}  {key}")
        for name, (cnt, ms, failed) in sorted(groups.items(), key=lambda kv: -kv[1][1]):
            share = 100.0 * ms / total_ms if total_ms else 0.0
            print(f"  {cnt:>8}  {fmt_ms(ms):>9}  {share:>5.1f}%  {failed:>6}  {name}")
        print()

    group_table("category", "By category")
    # Only break down by member when the CSV covers more than one
    if len({r.get("member") or "?" for r in rows}) > 1:
        group_table("member", "By member")

    # Aggregate by source position: repeated slow queries at one position are
    # one bottleneck, not many.
    by_pos = defaultdict(lambda: [0, 0.0])
    for r in rows:
        pos = f"{r.get('file') or '?'}:{r.get('line') or '?'}"
        by_pos[pos][0] += 1
        by_pos[pos][1] += r["durationMs"]
    print("Hottest source positions:")
    for pos, (cnt, ms) in sorted(by_pos.items(), key=lambda kv: -kv[1][1])[:10]:
        print(f"  {fmt_ms(ms):>9}  ({cnt} queries)  {pos}")
    print()

    print(f"Slowest {min(args.top, len(rows))} individual queries:")
    for r in sorted(rows, key=lambda r: -r["durationMs"])[: args.top]:
        pos = f"{r.get('file') or '?'}:{r.get('line') or '?'}"
        desc = (r.get("description") or "").strip()
        desc = f"  # {desc}" if desc and desc != "?" else ""
        ok = "" if (r.get("succeeded") or "").lower() != "false" else "  [FAILED]"
        print(f"  {fmt_ms(r['durationMs']):>9}  {r.get('category') or '?':<22}"
              f"  {r.get('member') or '?':<30}  {pos}{ok}{desc}")


if __name__ == "__main__":
    main()
