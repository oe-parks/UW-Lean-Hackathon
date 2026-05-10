#!/usr/bin/env python3
"""Baseline reference agent: try a fixed sequence of high-leverage tactics.

This is the "agent contract" reference implementation. Every other agent
in `agents/` follows the same CLI contract:

  python3 baseline_decide.py --problem PROBLEM.json --workdir OUT/

After it exits, OUT/ contains:
  proof.lean         — the proof file the agent wants to submit
  attempts.jsonl     — one JSON line per attempt (timestamped)
  summary.json       — {claimed_solved, attempts, …}

The agent is *not* trusted: the orchestrator independently verifies
proof.lean via verify_proof.py.
"""

import argparse
import json
import os
import shlex
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional


# Tried in order. First success wins.
DEFAULT_TACTICS: List[str] = [
    "decide",
    "rfl",
    "trivial",
    "exact True.intro",
    "intro; rfl",
    "intros; rfl",
    "intro; decide",
    "intros; decide",
    "intro n; rfl",
    "intro; trivial",
    "intro; simp",
    "intros; simp",
    "intros; omega",
    "omega",
    "intros a b; exact Nat.add_comm a b",
    "intro a b; exact Nat.add_comm a b",
    "intros; constructor",
    "constructor",
    "intros; intros; rfl",
    "intro a b c; exact Nat.add_assoc a b c",
    "intro l; induction l <;> simp_all",
    "intro l; induction l <;> simp [*]",
    "intro l; induction l with | nil => rfl | cons h t ih => simp [ih]",
    "intro a b; exact Nat.le_total a b",
    "intro n; intro h; cases h",
    "intro l; simp",
]


def _make_lean(problem: dict, tactic: str) -> str:
    """Construct the per-attempt Lean file the agent compiles."""
    imports = problem.get("imports", [])
    lines: List[str] = []
    for imp in imports:
        lines.append(f"import {imp}")
    if imports:
        lines.append("")
    lines.append(f"{problem['statement'].rstrip()} := by")
    lines.append(f"  {tactic}")
    lines.append("")
    return "\n".join(lines)


def _try_tactic(project_root: Path, problem: dict, tactic: str,
                attempt_path: Path, timeout_s: float) -> dict:
    """Run lake env lean on the attempt; return a dict with the verdict.
    Note: this is the *agent's* internal compile-check, not the
    orchestrator's verification."""
    src = _make_lean(problem, tactic)
    attempt_path.write_text(src)
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(attempt_path)],
            cwd=project_root,
            capture_output=True, text=True,
            timeout=timeout_s,
        )
        elapsed = time.perf_counter() - t0
        ok = (proc.returncode == 0
              and "error:" not in proc.stderr
              and "error:" not in proc.stdout)
        return {
            "tactic": tactic,
            "elapsed_s": elapsed,
            "exit_code": proc.returncode,
            "ok": ok,
            "stdout_head": proc.stdout[:1000],
            "stderr_head": proc.stderr[:1000],
        }
    except subprocess.TimeoutExpired:
        return {
            "tactic": tactic,
            "elapsed_s": time.perf_counter() - t0,
            "exit_code": None,
            "ok": False,
            "timed_out": True,
        }


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--problem", type=Path, required=True)
    ap.add_argument("--workdir", type=Path, required=True)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent,
                    help="LeanTacticLatencyBench root (default: parent of agents/).")
    ap.add_argument("--per-tactic-timeout", type=float, default=15.0,
                    help="Per-tactic timeout in seconds.")
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    workdir = args.workdir.resolve()
    workdir.mkdir(parents=True, exist_ok=True)

    problem = json.loads(args.problem.read_text())
    log_path = workdir / "attempts.jsonl"
    log_f = log_path.open("w")

    started = time.perf_counter()
    winning_tactic: Optional[str] = None
    final_proof: Optional[str] = None

    for i, tactic in enumerate(DEFAULT_TACTICS):
        scratch = workdir / f"attempt_{i:03d}.lean"
        attempt = _try_tactic(project_root, problem, tactic, scratch,
                              args.per_tactic_timeout)
        attempt["index"] = i
        attempt["t_since_start_s"] = time.perf_counter() - started
        log_f.write(json.dumps(attempt) + "\n")
        log_f.flush()
        if attempt["ok"]:
            winning_tactic = tactic
            final_proof = _make_lean(problem, tactic)
            break

    log_f.close()

    if final_proof is not None:
        (workdir / "proof.lean").write_text(final_proof)
        claimed = True
    else:
        claimed = False

    summary = {
        "agent": "baseline_decide",
        "problem_name": problem["name"],
        "claimed_solved": claimed,
        "winning_tactic": winning_tactic,
        "attempts": sum(1 for _ in open(log_path)),
        "total_wall_s": time.perf_counter() - started,
    }
    (workdir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))
    sys.exit(0 if claimed else 1)


if __name__ == "__main__":
    main()
