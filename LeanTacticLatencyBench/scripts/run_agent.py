#!/usr/bin/env python3
"""Run an agent over a problem corpus and verify each attempt.

This is the headline tool for the agent-evaluation use case:
"My agent A is faster / smarter than agent B at proving problems P".

  python3 scripts/run_agent.py \
      --agent "agents/baseline_decide.py" \
      --corpus Bench/AgentProblems \
      --budget 60 \
      --out-dir results/agents/baseline_decide

For every problem under --corpus, the orchestrator:
  1. Creates a fresh workdir.
  2. Invokes the agent: <agent> --problem PROB.json --workdir WORKDIR.
  3. Times the agent (wall-clock + GNU time -v if available).
  4. Reads workdir/proof.lean (if any) and verifies it independently
     via verify_proof.py — the agent's claimed_solved is logged but
     not trusted.
  5. Writes per-problem metrics + a top-level summary JSON.

The agent contract is the CLI subprocess described in agents/README.md:
the agent must accept --problem and --workdir, and on success write
proof.lean / attempts.jsonl / summary.json into the workdir.
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

# Local import of the verifier
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_proof  # noqa: E402


def _have_gnu_time() -> bool:
    if not Path("/usr/bin/time").exists():
        return False
    try:
        r = subprocess.run(
            ["/usr/bin/time", "-v", "true"],
            capture_output=True, text=True, timeout=5,
        )
        return r.returncode == 0
    except Exception:
        return False


HAVE_GNU_TIME = _have_gnu_time()


def _parse_gnu_time(stderr: str) -> dict:
    out = {}
    for line in stderr.splitlines():
        line = line.strip()
        if line.startswith("User time (seconds):"):
            try: out["user_s"] = float(line.split(":", 1)[1].strip())
            except: pass
        elif line.startswith("System time (seconds):"):
            try: out["system_s"] = float(line.split(":", 1)[1].strip())
            except: pass
        elif line.startswith("Maximum resident set size (kbytes):"):
            try: out["max_rss_kb"] = int(line.split(":", 1)[1].strip())
            except: pass
    return out


def run_agent_on_problem(
    project_root: Path,
    agent_cmd: List[str],
    problem_path: Path,
    workdir: Path,
    budget_s: float,
    verify_timeout_s: float,
    forbidden_tokens,
    allowed_axioms,
) -> dict:
    """Run the agent on one problem; verify; return metrics."""
    workdir.mkdir(parents=True, exist_ok=True)
    problem = json.loads(problem_path.read_text())

    cmd = list(agent_cmd) + [
        "--problem", str(problem_path),
        "--workdir", str(workdir),
    ]
    if HAVE_GNU_TIME:
        cmd = ["/usr/bin/time", "-v"] + cmd

    started = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            cwd=project_root,
            capture_output=True, text=True,
            timeout=budget_s,
        )
        agent_wall_s = time.perf_counter() - started
        agent_stdout = proc.stdout
        agent_stderr = proc.stderr
        agent_exit = proc.returncode
        agent_timed_out = False
    except subprocess.TimeoutExpired as e:
        agent_wall_s = time.perf_counter() - started
        agent_stdout = (e.stdout or b"").decode("utf-8", errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        agent_stderr = (e.stderr or b"").decode("utf-8", errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        agent_exit = None
        agent_timed_out = True

    gnu = _parse_gnu_time(agent_stderr) if HAVE_GNU_TIME else {}

    # Read agent outputs.
    summary_p = workdir / "summary.json"
    proof_p = workdir / "proof.lean"
    attempts_p = workdir / "attempts.jsonl"
    agent_summary = (json.loads(summary_p.read_text())
                     if summary_p.exists() else {})
    claimed = bool(agent_summary.get("claimed_solved", False))

    if proof_p.exists():
        proof_src = proof_p.read_text()
        verdict = verify_proof.verify(
            project_root, problem, proof_src,
            forbidden_tokens=forbidden_tokens,
            allowed_axioms=allowed_axioms,
            timeout_s=verify_timeout_s,
        )
    else:
        verdict = {
            "verified": False,
            "reason": "agent did not produce proof.lean",
            "stage": "no_output",
        }

    # Count attempts and locate first verified-true attempt's relative
    # timestamp (agent self-report).
    n_attempts = 0
    if attempts_p.exists():
        for ln in attempts_p.read_text().splitlines():
            if ln.strip():
                n_attempts += 1

    return {
        "problem_name": problem["name"],
        "problem_path": str(problem_path),
        "workdir": str(workdir),
        "claimed_solved": claimed,
        "verified": bool(verdict.get("verified")),
        "claimed_lying": claimed and not verdict.get("verified"),
        "verdict": verdict,
        "agent_wall_s": agent_wall_s,
        "agent_exit_code": agent_exit,
        "agent_timed_out": agent_timed_out,
        "agent_user_s": gnu.get("user_s"),
        "agent_system_s": gnu.get("system_s"),
        "agent_peak_rss_kb": gnu.get("max_rss_kb"),
        "n_attempts": n_attempts,
        "agent_summary": agent_summary,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--agent", required=True,
                    help="Agent command (path or 'python3 path.py'). "
                         "Will be run with --problem and --workdir appended.")
    ap.add_argument("--agent-name", default=None,
                    help="Tag for reporting (default: basename of agent).")
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--corpus", type=Path,
                    default=None,
                    help="Directory of *.problem.json files "
                         "(default: <project>/Bench/AgentProblems).")
    ap.add_argument("--budget", type=float, default=120.0,
                    help="Per-problem wall-clock budget in seconds.")
    ap.add_argument("--verify-timeout", type=float, default=60.0,
                    help="Timeout for the verifier's own Lean compile.")
    ap.add_argument("--out-dir", type=Path, default=None,
                    help="Where to write results (default: "
                         "<project>/results/agents/<agent_name>).")
    ap.add_argument("--filter", default=None,
                    help="Only run problems whose name contains this substring.")
    ap.add_argument("--forbid-token", action="append", default=[])
    ap.add_argument("--allow-token", action="append", default=[])
    ap.add_argument("--allow-axiom", action="append", default=[])
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    corpus = (args.corpus or (project_root / "Bench" / "AgentProblems")).resolve()
    agent_cmd = shlex.split(args.agent)
    if not agent_cmd:
        sys.exit("--agent must not be empty")
    # Auto-prepend python3 if the agent is a .py file
    first = agent_cmd[0]
    if first.endswith(".py") and not first.startswith("python"):
        agent_cmd = ["python3"] + agent_cmd
    agent_name = (args.agent_name
                  or Path(agent_cmd[-1]).stem.replace(" ", "_"))
    out_dir = (args.out_dir
               or (project_root / "results" / "agents" / agent_name)).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    forbidden = set(verify_proof.DEFAULT_FORBIDDEN_TOKENS)
    forbidden |= set(args.forbid_token)
    forbidden -= set(args.allow_token)
    allowed_axioms = set(verify_proof.DEFAULT_ALLOWED_AXIOMS) | set(args.allow_axiom)

    problems = sorted(corpus.glob("*.problem.json"))
    if args.filter:
        problems = [p for p in problems if args.filter in p.name]
    if not problems:
        sys.exit(f"no problems found under {corpus}")

    print(f"# Agent run")
    print(f"# project:    {project_root}")
    print(f"# corpus:     {corpus}  ({len(problems)} problem(s))")
    print(f"# agent:      {' '.join(agent_cmd)}")
    print(f"# agent_name: {agent_name}")
    print(f"# budget:     {args.budget}s/problem")
    print(f"# out:        {out_dir}")
    print()

    results = []
    n_verified = n_claimed = n_lying = 0
    for p in problems:
        problem_name = json.loads(p.read_text())["name"]
        wd = out_dir / problem_name
        r = run_agent_on_problem(
            project_root, agent_cmd, p, wd,
            budget_s=args.budget,
            verify_timeout_s=args.verify_timeout,
            forbidden_tokens=forbidden,
            allowed_axioms=allowed_axioms,
        )
        results.append(r)
        if r["claimed_solved"]:
            n_claimed += 1
        if r["verified"]:
            n_verified += 1
        if r["claimed_lying"]:
            n_lying += 1
        verdict = (
            "VERIFIED" if r["verified"]
            else ("LIED" if r["claimed_lying"]
                  else ("UNSOLVED" if not r["claimed_solved"]
                        else "REJECTED"))
        )
        agent_secs = r["agent_wall_s"]
        print(f"  {problem_name:<28}  {agent_secs:6.2f}s  "
              f"{r['n_attempts']:>3} attempt(s)  {verdict}"
              + (f"  ({r['verdict'].get('reason', '')[:60]})"
                 if not r["verified"] else ""))

    summary = {
        "kind": "agent_run",
        "agent_name": agent_name,
        "agent_cmd": agent_cmd,
        "project_root": str(project_root),
        "corpus": str(corpus),
        "budget_s": args.budget,
        "n_problems": len(results),
        "n_claimed_solved": n_claimed,
        "n_verified": n_verified,
        "n_lying": n_lying,
        "solve_rate": n_verified / max(1, len(results)),
        "results": results,
        "have_gnu_time": HAVE_GNU_TIME,
    }
    out_path = out_dir / "agent_run.json"
    out_path.write_text(json.dumps(summary, indent=2))
    print()
    print(f"# verified  : {n_verified}/{len(results)}")
    print(f"# claimed   : {n_claimed}/{len(results)}")
    print(f"# lying     : {n_lying}")
    print(f"# wrote     : {out_path}")


if __name__ == "__main__":
    main()
