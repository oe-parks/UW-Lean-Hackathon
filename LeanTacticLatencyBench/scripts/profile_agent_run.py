#!/usr/bin/env python3
"""Per-attempt profiling of an agent run.

Reads:
  results/agents/<agent>/agent_run.json     orchestrator summary
  results/agents/<agent>/<problem>/attempts.jsonl   per-attempt log

Produces, for the agent run:

  1. Per-problem table — for each problem, a list of every tactic /
     candidate the agent tried, with elapsed time, success/failure
     status, and a *failure-kind* classification (timeout, simp_no_progress,
     decide_stuck, type_error, unsolved_goals, rfl_failed, …).

  2. Per-problem aggregates — number of failed attempts, total seconds
     spent on failed attempts ("waste"), seconds on the winning attempt
     ("productive"), waste/productive ratio.

  3. Cross-problem aggregates — total waste, productive time,
     failure-kind histogram, and a top-K table of the *most expensive*
     failed tactics (tactic string + cumulative time spent on it across
     the whole corpus).

  4. **Cancellation what-if** — for each problem, two costs:
        actual_wall_s = sum of every attempt the agent serially ran
        clairvoyant_wall_s = elapsed of the winning attempt only
     The difference is the time that *would* be saved if a perfect
     cancellation oracle let us skip every losing attempt — a hard
     upper bound on what early cancellation can buy.

Outputs:
  results/agents/<agent>/attempts_detail.csv
      one row per attempt across all problems; convenient for pandas
      or spreadsheet analysis.
  results/agents/<agent>/profile_summary.json
      machine-readable version of the console report.

Usage:
  python3 scripts/profile_agent_run.py \
      --run results/agents/baseline_decide/agent_run.json
  python3 scripts/profile_agent_run.py \
      --run results/agents/baseline_decide/agent_run.json --top 8
"""

import argparse
import csv
import json
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple


def classify_failure(rec: dict) -> str:
    """Bucket a failed attempt by failure mode, from Lean's output.

    Returns a short tag. We try to be specific so a stacked-bar of
    failure-kind tells you *why* the agent struggled, not just that it
    did. New tags can be added below.
    """
    if rec.get("ok"):
        return "success"
    if rec.get("timed_out"):
        return "timeout"
    if rec.get("api_error"):
        return "api_error"
    if rec.get("failure_kind"):
        # Trust the agent's self-label when present.
        return rec["failure_kind"]

    blob = ((rec.get("stdout_head") or "") + "\n" +
            (rec.get("stderr_head") or "")).lower()
    if not blob.strip():
        return "no_output"
    if "type mismatch" in blob:
        return "type_mismatch"
    if "unknown constant" in blob or "unknown identifier" in blob:
        return "unknown_identifier"
    if "reduction got stuck" in blob:
        return "decide_stuck"
    if "simp made no progress" in blob:
        return "simp_no_progress"
    if "unsolved goals" in blob:
        return "unsolved_goals"
    if "rfl' failed" in blob or "tactic `rfl` failed" in blob:
        return "rfl_failed"
    if "decide' proved" in blob and "is false" in blob:
        return "decide_proved_false"
    if "tactic" in blob and "failed" in blob:
        return "tactic_failed"
    if "maximum recursion depth" in blob:
        return "max_recdepth"
    if rec.get("exit_code") not in (0, None):
        return "compile_failed"
    return "unknown_failure"


def _normalize(rec: dict) -> dict:
    """Flatten the two attempt-record shapes (baseline vs llm_claude)
    into one dict with `tactic`, `elapsed_s`, `ok`, `exit_code`,
    `stdout_head`, `stderr_head`, `timed_out`."""
    rec = dict(rec)  # shallow copy
    if "compile" in rec and isinstance(rec["compile"], dict):
        c = rec["compile"]
        rec["ok"] = c.get("ok", False)
        rec["elapsed_s"] = c.get("elapsed_s")
        rec["exit_code"] = c.get("exit_code")
        rec["stdout_head"] = c.get("stdout_head", "")
        rec["stderr_head"] = c.get("stderr_head", "")
        rec["timed_out"] = c.get("timed_out", False)
    if "tactic" not in rec:
        # llm_claude doesn't expose the candidate as a "tactic" string;
        # we synthesise one for reporting.
        rec["tactic"] = f"<llm attempt #{rec.get('index', '?')}>"
    return rec


def _load_attempts(workdir: Path) -> List[dict]:
    p = workdir / "attempts.jsonl"
    if not p.exists():
        return []
    out = []
    for line in p.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        rec = _normalize(rec)
        rec["failure_kind"] = classify_failure(rec)
        out.append(rec)
    return out


def profile_problem(orchestrator_record: dict, agent_outdir: Path) -> dict:
    """Compute the per-problem profile."""
    pname = orchestrator_record["problem_name"]
    workdir = agent_outdir / pname
    attempts = _load_attempts(workdir)

    failed = [a for a in attempts if not a.get("ok")]
    succeeded = [a for a in attempts if a.get("ok")]
    failed_elapsed = [float(a.get("elapsed_s") or 0) for a in failed]
    success_elapsed = [float(a.get("elapsed_s") or 0) for a in succeeded]

    return {
        "problem": pname,
        "verified": bool(orchestrator_record.get("verified")),
        "claimed_solved": bool(orchestrator_record.get("claimed_solved")),
        "n_attempts": len(attempts),
        "n_failed": len(failed),
        "n_succeeded": len(succeeded),
        "waste_s": sum(failed_elapsed),
        "productive_s": sum(success_elapsed),
        "max_failed_s": max(failed_elapsed) if failed_elapsed else 0.0,
        "mean_failed_s": (statistics.mean(failed_elapsed)
                          if failed_elapsed else 0.0),
        "median_failed_s": (statistics.median(failed_elapsed)
                            if failed_elapsed else 0.0),
        "failure_kinds": Counter(a["failure_kind"] for a in failed),
        "agent_wall_s": orchestrator_record.get("agent_wall_s"),
        "attempts": attempts,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", type=Path, required=True,
                    help="Path to agent_run.json (under results/agents/<agent>/).")
    ap.add_argument("--top", type=int, default=10,
                    help="How many of the most expensive failed tactics to list.")
    ap.add_argument("--csv", type=Path, default=None,
                    help="Override CSV output path "
                         "(default: <agent>/attempts_detail.csv).")
    ap.add_argument("--summary-json", type=Path, default=None,
                    help="Override profile JSON path "
                         "(default: <agent>/profile_summary.json).")
    ap.add_argument("--no-csv", action="store_true",
                    help="Skip CSV output.")
    ap.add_argument("--show-attempts", action="store_true",
                    help="Print every attempt to stdout (verbose).")
    args = ap.parse_args()

    run_path = args.run.resolve()
    agent_dir = run_path.parent
    run = json.loads(run_path.read_text())
    agent_name = run.get("agent_name", agent_dir.name)
    results = run.get("results", [])

    csv_path = args.csv or (agent_dir / "attempts_detail.csv")
    sumjson_path = args.summary_json or (agent_dir / "profile_summary.json")

    # ── Per-problem ──────────────────────────────────────────────────
    profiles: List[dict] = []
    for r in results:
        profiles.append(profile_problem(r, agent_dir))

    # ── Console report ───────────────────────────────────────────────
    print(f"# Agent profile: {agent_name}")
    print(f"# corpus:  {len(results)} problem(s)")
    n_verified = sum(1 for p in profiles if p["verified"])
    print(f"# solved:  {n_verified}/{len(results)}")
    print()

    print("## Per-problem")
    print(f"  {'problem':<28}  {'#att':>4} {'#fail':>5} "
          f"{'waste_s':>9} {'prod_s':>8} {'wall_s':>8}  status")
    total_waste = 0.0
    total_productive = 0.0
    total_attempts = 0
    total_failed = 0
    for p in profiles:
        status = "OK " if p["verified"] else "FAIL"
        total_waste += p["waste_s"]
        total_productive += p["productive_s"]
        total_attempts += p["n_attempts"]
        total_failed += p["n_failed"]
        print(f"  {p['problem']:<28}  {p['n_attempts']:>4d} {p['n_failed']:>5d} "
              f"{p['waste_s']:>9.3f} {p['productive_s']:>8.3f} "
              f"{(p['agent_wall_s'] or 0):>8.3f}  {status}")
    print()
    print(f"  totals:                       {total_attempts:>4d} {total_failed:>5d} "
          f"{total_waste:>9.3f} {total_productive:>8.3f}")
    if total_waste + total_productive > 0:
        print(f"  waste / (waste + productive) = "
              f"{total_waste / (total_waste + total_productive) * 100:.1f}%")
    print()

    # ── Failure-kind histogram ───────────────────────────────────────
    kind_counts: Counter = Counter()
    kind_seconds: Counter = Counter()
    for p in profiles:
        for a in p["attempts"]:
            if a.get("ok"):
                continue
            kind = a["failure_kind"]
            kind_counts[kind] += 1
            kind_seconds[kind] += float(a.get("elapsed_s") or 0)
    print("## Failure kinds (across all problems)")
    print(f"  {'kind':<22}  {'count':>5} {'tot_s':>8} {'mean_s':>8}")
    for kind, cnt in kind_counts.most_common():
        tot = kind_seconds[kind]
        mean = tot / cnt if cnt else 0.0
        print(f"  {kind:<22}  {cnt:>5d} {tot:>8.3f} {mean:>8.3f}")
    print()

    # ── Top wasted tactics ───────────────────────────────────────────
    tactic_seconds: Dict[str, float] = defaultdict(float)
    tactic_count: Counter = Counter()
    for p in profiles:
        for a in p["attempts"]:
            if a.get("ok"):
                continue
            t = (a.get("tactic") or "").strip()
            if not t:
                continue
            tactic_seconds[t] += float(a.get("elapsed_s") or 0)
            tactic_count[t] += 1
    top = sorted(tactic_seconds.items(), key=lambda kv: -kv[1])[:args.top]
    if top:
        print(f"## Top {len(top)} most-expensive failed tactics")
        print(f"  {'cum_s':>8} {'count':>5}  tactic")
        for tac, secs in top:
            print(f"  {secs:>8.3f} {tactic_count[tac]:>5d}  {tac}")
        print()

    # ── Cancellation what-if (clairvoyant oracle) ────────────────────
    print("## Cancellation what-if (clairvoyant oracle)")
    print(f"  Without cancellation:  {total_waste + total_productive:>8.3f}s "
          f"(every attempt runs to completion)")
    print(f"  With perfect oracle:   {total_productive:>8.3f}s "
          f"(only the winning attempt runs)")
    print(f"  Upper bound on savings: {total_waste:>8.3f}s "
          f"({(total_waste / (total_waste + total_productive) * 100 if (total_waste + total_productive) > 0 else 0):.1f}%)")
    print()
    print("  This is the *upper bound* — any real cancellation strategy")
    print("  must pay for at least the winner's elapsed time. Anything")
    print("  between 0 and the upper bound is what your scheduling /")
    print("  early-stopping policy is competing for.")
    print()

    # ── Show every attempt (optional, verbose) ───────────────────────
    if args.show_attempts:
        print("## Every attempt")
        for p in profiles:
            print(f"### {p['problem']}")
            for a in p["attempts"]:
                tag = "OK" if a.get("ok") else a.get("failure_kind", "?")
                tac = (a.get("tactic") or "")[:60]
                el = a.get("elapsed_s") or 0
                print(f"   #{a.get('index', '?'):<3}  "
                      f"{el:>6.3f}s  {tag:<22}  {tac}")
            print()

    # ── CSV ──────────────────────────────────────────────────────────
    if not args.no_csv:
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        with csv_path.open("w", newline="") as f:
            w = csv.writer(f)
            w.writerow([
                "agent", "problem", "verified", "attempt_idx", "tactic",
                "elapsed_s", "ok", "failure_kind", "exit_code",
                "t_since_start_s",
            ])
            for p in profiles:
                for a in p["attempts"]:
                    w.writerow([
                        agent_name,
                        p["problem"],
                        p["verified"],
                        a.get("index"),
                        (a.get("tactic") or "")[:200],
                        a.get("elapsed_s"),
                        a.get("ok", False),
                        a.get("failure_kind"),
                        a.get("exit_code"),
                        a.get("t_since_start_s"),
                    ])
        print(f"# Wrote per-attempt CSV: {csv_path}")

    # ── Machine-readable summary ─────────────────────────────────────
    sumjson_path.parent.mkdir(parents=True, exist_ok=True)
    summary = {
        "agent_name": agent_name,
        "n_problems": len(results),
        "n_verified": n_verified,
        "totals": {
            "n_attempts": total_attempts,
            "n_failed": total_failed,
            "waste_s": total_waste,
            "productive_s": total_productive,
            "wall_s": sum(float(p.get("agent_wall_s") or 0) for p in profiles),
            "waste_ratio": (total_waste / (total_waste + total_productive)
                            if (total_waste + total_productive) > 0 else 0.0),
        },
        "cancellation_oracle": {
            "without_cancellation_s": total_waste + total_productive,
            "with_oracle_s": total_productive,
            "upper_bound_savings_s": total_waste,
        },
        "failure_kinds": [
            {"kind": k, "count": kind_counts[k], "total_s": kind_seconds[k]}
            for k, _ in kind_counts.most_common()
        ],
        "top_wasted_tactics": [
            {"tactic": t, "count": tactic_count[t], "total_s": s}
            for t, s in top
        ],
        "per_problem": [
            {
                **{k: v for k, v in p.items()
                   if k not in ("attempts", "failure_kinds")},
                "failure_kinds": dict(p["failure_kinds"]),
            }
            for p in profiles
        ],
    }
    sumjson_path.write_text(json.dumps(summary, indent=2))
    print(f"# Wrote profile JSON: {sumjson_path}")


if __name__ == "__main__":
    main()
