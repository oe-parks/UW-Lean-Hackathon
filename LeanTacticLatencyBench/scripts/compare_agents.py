#!/usr/bin/env python3
"""Compare two agent runs on the same corpus.

Reads two `agent_run.json` files (produced by `run_agent.py`) and emits:

  * a per-problem table — who solved, who didn't, paired TTFC delta,
  * aggregate stats — solve-rate diff, median TTFC on the intersected
    solved set, and a McNemar 2×2 table (no p-value — we only need the
    paired counts; downstream tooling can do the test),
  * a CSV side-by-side table for further analysis.

Designed for the agent-evaluation use case:
"My agent A is faster / smarter than agent B at proving problems P".
Run A, run B, point this script at both, read off the numbers.
"""

import argparse
import csv
import json
import statistics
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple


def _index_by_problem(run: dict) -> Dict[str, dict]:
    return {r["problem_name"]: r for r in run.get("results", [])}


def _ttfc(record: dict) -> Optional[float]:
    """Time-to-first-verified for a single problem run.

    For now we use the agent's wall-clock to proof.lean as the proxy —
    the agent's `summary.json.total_wall_s` if present, else the
    orchestrator-measured `agent_wall_s`. Returns None if the problem
    wasn't verified.
    """
    if not record.get("verified"):
        return None
    summary = record.get("agent_summary", {}) or {}
    if "total_wall_s" in summary:
        return float(summary["total_wall_s"])
    return float(record.get("agent_wall_s", 0.0))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--a", type=Path, required=True,
                    help="First agent's `agent_run.json`.")
    ap.add_argument("--b", type=Path, required=True,
                    help="Second agent's `agent_run.json`.")
    ap.add_argument("--label-a", default=None,
                    help="Display name for agent A (default: agent_name from JSON).")
    ap.add_argument("--label-b", default=None)
    ap.add_argument("--out-csv", type=Path, default=None,
                    help="Optional path for a per-problem comparison CSV.")
    args = ap.parse_args()

    run_a = json.loads(args.a.read_text())
    run_b = json.loads(args.b.read_text())
    a = args.label_a or run_a.get("agent_name", "A")
    b = args.label_b or run_b.get("agent_name", "B")

    by_a = _index_by_problem(run_a)
    by_b = _index_by_problem(run_b)
    problems = sorted(set(by_a) | set(by_b))
    if not problems:
        sys.exit("no problems found in either run")

    # Sanity: warn if corpora differ.
    only_a = set(by_a) - set(by_b)
    only_b = set(by_b) - set(by_a)
    if only_a or only_b:
        print(f"# WARNING: corpora differ. only-in-A={sorted(only_a)}, "
              f"only-in-B={sorted(only_b)}", file=sys.stderr)

    # 2×2 McNemar table on the intersection.
    both_solved = a_only = b_only = neither = 0
    paired_ttfc: List[Tuple[str, float, float]] = []

    rows_for_csv = []
    for p in problems:
        ra = by_a.get(p)
        rb = by_b.get(p)
        va = bool(ra and ra.get("verified"))
        vb = bool(rb and rb.get("verified"))
        ta = _ttfc(ra) if ra else None
        tb = _ttfc(rb) if rb else None
        if ra and rb:
            if va and vb:
                both_solved += 1
                paired_ttfc.append((p, ta or 0.0, tb or 0.0))
            elif va:
                a_only += 1
            elif vb:
                b_only += 1
            else:
                neither += 1
        rows_for_csv.append({
            "problem": p,
            f"{a}_verified": va,
            f"{a}_ttfc_s": ta,
            f"{a}_attempts": (ra or {}).get("n_attempts"),
            f"{b}_verified": vb,
            f"{b}_ttfc_s": tb,
            f"{b}_attempts": (rb or {}).get("n_attempts"),
            "ttfc_delta_s_a_minus_b": (ta - tb) if (ta is not None and tb is not None) else None,
        })

    n_a = sum(1 for r in by_a.values() if r.get("verified"))
    n_b = sum(1 for r in by_b.values() if r.get("verified"))
    rate_a = n_a / max(1, len(by_a))
    rate_b = n_b / max(1, len(by_b))

    print(f"# Comparison: {a}  vs  {b}")
    print(f"# Corpus size: A={len(by_a)}  B={len(by_b)}  intersection={len(set(by_a) & set(by_b))}")
    print()
    print(f"## Solve rate")
    print(f"  {a}:  {n_a}/{len(by_a)}  ({rate_a:.0%})")
    print(f"  {b}:  {n_b}/{len(by_b)}  ({rate_b:.0%})")
    print(f"  Δ:   {(rate_a - rate_b)*100:+.1f} percentage points  ({a} - {b})")
    print()
    print(f"## McNemar 2×2 (intersection)")
    print(f"               {b}=PASS  {b}=FAIL")
    print(f"  {a}=PASS      {both_solved:>5}      {a_only:>5}")
    print(f"  {a}=FAIL      {b_only:>5}      {neither:>5}")
    print()

    if paired_ttfc:
        ttfc_a = [t[1] for t in paired_ttfc]
        ttfc_b = [t[2] for t in paired_ttfc]
        deltas = [a_t - b_t for a_t, b_t in zip(ttfc_a, ttfc_b)]
        print(f"## TTFC on jointly solved (n={len(paired_ttfc)})")
        print(f"  median {a}: {statistics.median(ttfc_a):6.3f}s")
        print(f"  median {b}: {statistics.median(ttfc_b):6.3f}s")
        print(f"  median Δ ({a}-{b}): {statistics.median(deltas):+6.3f}s")
        wins_a = sum(1 for d in deltas if d < 0)
        wins_b = sum(1 for d in deltas if d > 0)
        ties = sum(1 for d in deltas if d == 0)
        print(f"  per-problem wins:  {a}={wins_a}  {b}={wins_b}  ties={ties}")
        print()
        print("## Per-problem (jointly solved)")
        print(f"  {'problem':<28}  {a:>10}  {b:>10}  Δ(A-B)")
        for name, ta, tb in sorted(paired_ttfc, key=lambda x: x[1] - x[2]):
            print(f"  {name:<28}  {ta:9.3f}s  {tb:9.3f}s  {ta - tb:+8.3f}s")
        print()

    # Per-problem PASS/FAIL summary (everything, not just intersection).
    print("## Per-problem outcomes")
    print(f"  {'problem':<28}  {a:^9}  {b:^9}")
    for p in problems:
        va = bool(by_a.get(p) and by_a[p].get("verified"))
        vb = bool(by_b.get(p) and by_b[p].get("verified"))
        print(f"  {p:<28}  {'PASS' if va else 'fail':^9}  {'PASS' if vb else 'fail':^9}")

    if args.out_csv:
        args.out_csv.parent.mkdir(parents=True, exist_ok=True)
        if rows_for_csv:
            with args.out_csv.open("w", newline="") as f:
                w = csv.DictWriter(f, fieldnames=list(rows_for_csv[0].keys()))
                w.writeheader()
                for row in rows_for_csv:
                    w.writerow(row)
            print()
            print(f"# Wrote per-problem CSV: {args.out_csv}")


if __name__ == "__main__":
    main()
