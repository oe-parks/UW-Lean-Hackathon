#!/usr/bin/env python3
"""Random-search baseline agent.

Same CLI contract as `baseline_decide.py`, but instead of trying tactics
in a hand-tuned order, this agent samples random combinations from a
small pool until either it finds something Lean accepts or it runs out
of attempts. Useful as a "pure noise" baseline against which a real
agentic workflow should easily beat.
"""

import argparse
import json
import random
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional


# A small alphabet of tactic atoms; the agent forms candidates by
# concatenating between 1 and `--depth` of these.
ATOMS = [
    "trivial",
    "rfl",
    "decide",
    "simp",
    "omega",
    "constructor",
    "intro",
    "intros",
    "intro a b",
    "intro n",
    "intro l",
    "intro h",
    "induction l <;> simp_all",
    "induction n <;> simp_all",
    "exact True.intro",
    "exact Nat.add_comm _ _",
    "exact Nat.le_total _ _",
]


def _make_lean(problem: dict, tactic: str) -> str:
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


def _try(project_root: Path, problem: dict, tactic: str,
         scratch: Path, timeout_s: float) -> dict:
    src = _make_lean(problem, tactic)
    scratch.write_text(src)
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(scratch)],
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


def _sample(rng: random.Random, depth: int) -> str:
    n = rng.randint(1, depth)
    parts = [rng.choice(ATOMS) for _ in range(n)]
    return "; ".join(parts)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--problem", type=Path, required=True)
    ap.add_argument("--workdir", type=Path, required=True)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--max-attempts", type=int, default=30)
    ap.add_argument("--per-tactic-timeout", type=float, default=10.0)
    ap.add_argument("--depth", type=int, default=2,
                    help="Maximum number of tactic atoms per candidate.")
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    workdir = args.workdir.resolve()
    workdir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)

    problem = json.loads(args.problem.read_text())
    log_path = workdir / "attempts.jsonl"
    log_f = log_path.open("w")

    started = time.perf_counter()
    winning: Optional[str] = None
    final_proof: Optional[str] = None
    seen = set()
    n_unique_tried = 0

    for i in range(args.max_attempts):
        cand = _sample(rng, args.depth)
        if cand in seen:
            # Resample to avoid duplicate work.
            cand = _sample(rng, args.depth)
        seen.add(cand)
        n_unique_tried += 1
        scratch = workdir / f"attempt_{i:03d}.lean"
        attempt = _try(project_root, problem, cand, scratch,
                       args.per_tactic_timeout)
        attempt["index"] = i
        attempt["t_since_start_s"] = time.perf_counter() - started
        log_f.write(json.dumps(attempt) + "\n")
        log_f.flush()
        if attempt["ok"]:
            winning = cand
            final_proof = _make_lean(problem, cand)
            break

    log_f.close()

    if final_proof is not None:
        (workdir / "proof.lean").write_text(final_proof)
        claimed = True
    else:
        claimed = False

    summary = {
        "agent": "baseline_random",
        "problem_name": problem["name"],
        "claimed_solved": claimed,
        "winning_tactic": winning,
        "attempts": sum(1 for _ in open(log_path)),
        "unique_tactics_tried": n_unique_tried,
        "total_wall_s": time.perf_counter() - started,
        "seed": args.seed,
    }
    (workdir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))
    sys.exit(0 if claimed else 1)


if __name__ == "__main__":
    main()
