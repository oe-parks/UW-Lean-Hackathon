#!/usr/bin/env python3
"""Portfolio tactic search benchmark.

For each goal in --goals-json, generate one Lean file per candidate
tactic, launch them all in parallel via `lake env lean`, and watch
which finishes first with exit code 0. Then *immediately* terminate
the losing subprocesses and record:

  * time_to_first_success — wall-clock seconds from when the last
    candidate was spawned to when the winner exited 0,
  * loser_kill_latency_s — for each losing candidate, the wall-clock
    seconds between sending SIGTERM and the process actually exiting,
  * total_cpu_time_s — best-effort sum across all candidates of
    user+system CPU time (via /usr/bin/time -v if available),
  * winner / loser exit codes.

A single goal where *no* candidate succeeds is reported with
`winner: null` and `time_to_first_success: null`.

Output is JSON under --out-dir/raw/.
"""

import argparse
import json
import os
import re
import shlex
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import List, Optional


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


def make_lean_source(preamble: str, goal: str, tactic: str) -> str:
    """Build the contents of a single per-candidate Lean file."""
    body = f"""-- Auto-generated portfolio candidate.
{preamble}

example : {goal} := by
  {tactic}
"""
    return body


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


def race(
    project_root: Path,
    goal_name: str,
    preamble: str,
    goal: str,
    candidates: List[str],
    timeout_s: float,
    kill_grace_s: float = 1.5,
) -> dict:
    """Race a list of candidate tactics against one goal."""
    with tempfile.TemporaryDirectory(prefix="portfolio_") as td:
        td_path = Path(td)
        files: List[Path] = []
        for i, tac in enumerate(candidates):
            fp = td_path / f"cand_{i}.lean"
            fp.write_text(make_lean_source(preamble, goal, tac))
            files.append(fp)

        procs = []
        spawn_t0 = time.perf_counter()
        for i, (tac, fp) in enumerate(zip(candidates, files)):
            cmd = ["lake", "env", "lean", str(fp)]
            if HAVE_GNU_TIME:
                cmd = ["/usr/bin/time", "-v"] + cmd
            p = subprocess.Popen(
                cmd, cwd=project_root,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
            procs.append({
                "idx": i, "tactic": tac, "proc": p,
                "spawn_t": time.perf_counter(),
                "exit_t": None, "exit_code": None,
                "kill_sent_t": None, "killed_t": None,
                "stdout_bytes": 0, "stderr_bytes": 0,
                "gnu_time": {},
            })
        spawn_done_t = time.perf_counter()

        winner_idx: Optional[int] = None
        deadline = spawn_done_t + timeout_s

        # Poll loop.
        while time.perf_counter() < deadline:
            for entry in procs:
                p = entry["proc"]
                if entry["exit_code"] is not None:
                    continue
                rc = p.poll()
                if rc is None:
                    continue
                # Process exited. Drain output.
                try:
                    stdout, stderr = p.communicate(timeout=2)
                except Exception:
                    stdout, stderr = b"", b""
                entry["exit_t"] = time.perf_counter()
                entry["exit_code"] = rc
                entry["stdout_bytes"] = len(stdout or b"")
                entry["stderr_bytes"] = len(stderr or b"")
                if HAVE_GNU_TIME and stderr:
                    try:
                        entry["gnu_time"] = _parse_gnu_time(stderr.decode("utf-8", errors="replace"))
                    except Exception:
                        pass
                if rc == 0 and winner_idx is None:
                    winner_idx = entry["idx"]
                    # Tell every still-running candidate to stop.
                    for other in procs:
                        if other["idx"] == winner_idx:
                            continue
                        op = other["proc"]
                        if other["exit_code"] is None and op.poll() is None:
                            other["kill_sent_t"] = time.perf_counter()
                            try:
                                op.terminate()
                            except ProcessLookupError:
                                pass
            if winner_idx is not None:
                # Wait for losers (they should have been signalled).
                still_running = [e for e in procs if e["exit_code"] is None]
                if not still_running:
                    break
                # Give each up to kill_grace_s to exit, then escalate.
                escalation_deadline = time.perf_counter() + kill_grace_s
                while still_running and time.perf_counter() < escalation_deadline:
                    for entry in still_running:
                        rc = entry["proc"].poll()
                        if rc is not None:
                            entry["killed_t"] = time.perf_counter()
                            entry["exit_t"] = entry["killed_t"]
                            entry["exit_code"] = rc
                            try:
                                stdout, stderr = entry["proc"].communicate(timeout=1)
                                entry["stdout_bytes"] = len(stdout or b"")
                                entry["stderr_bytes"] = len(stderr or b"")
                                if HAVE_GNU_TIME and stderr:
                                    entry["gnu_time"] = _parse_gnu_time(stderr.decode("utf-8", errors="replace"))
                            except Exception:
                                pass
                    still_running = [e for e in procs if e["exit_code"] is None]
                    if still_running:
                        time.sleep(0.05)
                # Anything still up after grace gets SIGKILL.
                for entry in still_running:
                    try:
                        entry["proc"].kill()
                    except Exception:
                        pass
                    try:
                        rc = entry["proc"].wait(timeout=2)
                    except Exception:
                        rc = -9
                    entry["killed_t"] = time.perf_counter()
                    entry["exit_t"] = entry["killed_t"]
                    entry["exit_code"] = rc
                break
            time.sleep(0.02)
        else:
            # Outer loop hit the timeout.
            pass

        # Final clean-up: anything still running has exceeded the timeout.
        for entry in procs:
            if entry["exit_code"] is None:
                try:
                    entry["proc"].kill()
                except Exception:
                    pass
                try:
                    rc = entry["proc"].wait(timeout=2)
                except Exception:
                    rc = -9
                entry["exit_t"] = time.perf_counter()
                entry["exit_code"] = rc
                entry["killed_t"] = entry["exit_t"]

    # Aggregate.
    winner = None
    if winner_idx is not None:
        e = procs[winner_idx]
        winner = {
            "tactic": e["tactic"],
            "elapsed_s": e["exit_t"] - e["spawn_t"],
            "exit_code": e["exit_code"],
        }
    losers = []
    for e in procs:
        if winner_idx is not None and e["idx"] == winner_idx:
            continue
        loser = {
            "tactic": e["tactic"],
            "exit_code": e["exit_code"],
            "elapsed_s": (e["exit_t"] - e["spawn_t"]) if e["exit_t"] else None,
        }
        if e["kill_sent_t"] is not None and e["killed_t"] is not None:
            loser["kill_latency_s"] = e["killed_t"] - e["kill_sent_t"]
        else:
            loser["kill_latency_s"] = None
        loser["gnu_time"] = e["gnu_time"]
        losers.append(loser)

    total_cpu = 0.0
    for e in procs:
        gt = e.get("gnu_time", {})
        total_cpu += float(gt.get("user_s", 0.0)) + float(gt.get("system_s", 0.0))

    # Cancellation accounting: how long each candidate actually ran
    # before being terminated (or finishing on its own).
    actual_compute_s = 0.0
    for e in procs:
        if e["exit_t"] is not None:
            actual_compute_s += (e["exit_t"] - e["spawn_t"])

    return {
        "goal_name": goal_name,
        "goal": goal,
        "candidate_count": len(candidates),
        "time_to_first_success_s": (
            (procs[winner_idx]["exit_t"] - spawn_done_t) if winner_idx is not None else None
        ),
        "winner": winner,
        "losers": losers,
        "actual_compute_s": actual_compute_s,
        "total_cpu_time_s": total_cpu if HAVE_GNU_TIME else None,
        "have_gnu_time": HAVE_GNU_TIME,
    }


def calibrate(
    project_root: Path,
    preamble: str,
    goal: str,
    candidates: List[str],
    timeout_s: float,
) -> List[dict]:
    """Run each candidate alone and record its natural runtime.

    This gives us the denominator for cancellation savings: without
    knowing how long a candidate would have run if uninterrupted, we
    can only report a lower bound. With calibration, we know exactly.
    """
    out = []
    with tempfile.TemporaryDirectory(prefix="portfolio_calib_") as td:
        for i, tac in enumerate(candidates):
            fp = Path(td) / f"calib_{i}.lean"
            fp.write_text(make_lean_source(preamble, goal, tac))
            t0 = time.perf_counter()
            try:
                proc = subprocess.run(
                    ["lake", "env", "lean", str(fp)],
                    cwd=project_root,
                    capture_output=True,
                    timeout=timeout_s,
                )
                elapsed = time.perf_counter() - t0
                exit_code = proc.returncode
                timed_out = False
            except subprocess.TimeoutExpired:
                elapsed = time.perf_counter() - t0
                exit_code = None
                timed_out = True
            out.append({
                "tactic": tac,
                "natural_elapsed_s": elapsed,
                "exit_code": exit_code,
                "timed_out": timed_out,
                "succeeds_solo": (exit_code == 0 and not timed_out),
            })
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--goals-json", type=Path,
                    default=None,
                    help="JSON file describing goals + candidates "
                         "(default: <project>/Bench/PortfolioGoals/goals.json).")
    ap.add_argument("--timeout", type=float, default=60.0,
                    help="Per-goal timeout in seconds (default: 60).")
    ap.add_argument("--kill-grace", type=float, default=1.5,
                    help="Grace period after SIGTERM before SIGKILL (seconds, default: 1.5).")
    ap.add_argument("--out-dir", type=Path, default=None,
                    help="Where to drop the JSON result (default: <project>/results/raw).")
    ap.add_argument("--label", default=None)
    ap.add_argument("--calibrate", action="store_true",
                    help="Before each race, run every candidate alone "
                         "to measure its natural runtime. Adds a "
                         "`cancellation_savings_s` field to each goal's "
                         "result: the exact compute saved by cancellation "
                         "= sum(natural_runtime - actual_runtime) over "
                         "all candidates.")
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    goals_json = (args.goals_json or
                  (project_root / "Bench" / "PortfolioGoals" / "goals.json")).resolve()
    out_dir = (args.out_dir or (project_root / "results" / "raw")).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    goals = json.loads(goals_json.read_text())

    print(f"# Portfolio bench")
    print(f"# project: {project_root}")
    print(f"# goals:   {len(goals)}")
    print(f"# /usr/bin/time -v available: {HAVE_GNU_TIME}")
    print()

    runs = []
    for g in goals:
        print(f"-- {g['name']}: {len(g['candidates'])} candidate(s)")

        calibration = None
        if args.calibrate:
            calibration = calibrate(project_root, g.get("preamble", ""),
                                    g["goal"], g["candidates"],
                                    timeout_s=args.timeout)
            for c in calibration:
                print(f"   calib : {c['tactic']!r:<40}  "
                      f"natural={c['natural_elapsed_s']:.3f}s  "
                      f"solo_exit={c['exit_code']}")

        r = race(project_root, g["name"], g.get("preamble", ""),
                 g["goal"], g["candidates"],
                 timeout_s=args.timeout,
                 kill_grace_s=args.kill_grace)

        # Annotate each candidate with its calibrated natural runtime,
        # and compute the cancellation savings.
        if calibration is not None:
            natural_by_tactic = {c["tactic"]: c["natural_elapsed_s"]
                                 for c in calibration}
            r["calibration"] = calibration

            natural_total = sum(c["natural_elapsed_s"] for c in calibration)
            actual_total = r["actual_compute_s"]
            r["natural_compute_s"] = natural_total
            r["cancellation_savings_s"] = max(0.0, natural_total - actual_total)
            r["cancellation_savings_pct"] = (
                (natural_total - actual_total) / natural_total * 100.0
                if natural_total > 0 else 0.0
            )
            for L in r["losers"]:
                L["natural_elapsed_s"] = natural_by_tactic.get(L["tactic"])
                if (L["natural_elapsed_s"] is not None
                        and L.get("elapsed_s") is not None):
                    L["compute_saved_s"] = max(
                        0.0, L["natural_elapsed_s"] - L["elapsed_s"])

        runs.append(r)

        if r["winner"]:
            print(f"   winner: {r['winner']['tactic']!r} in "
                  f"{r['time_to_first_success_s']:.3f}s")
            for L in r["losers"]:
                kl = (f"{L['kill_latency_s']:.3f}s" if L["kill_latency_s"] is not None else "—")
                extra = ""
                if "compute_saved_s" in L:
                    extra = (f"  natural={L['natural_elapsed_s']:.3f}s "
                             f"saved={L['compute_saved_s']:.3f}s")
                print(f"   loser : {L['tactic']!r:<40}  exit={L['exit_code']}  "
                      f"kill_latency={kl}{extra}")
            if calibration is not None:
                print(f"   ── compute "
                      f"natural={r['natural_compute_s']:.3f}s "
                      f"actual={r['actual_compute_s']:.3f}s "
                      f"saved={r['cancellation_savings_s']:.3f}s "
                      f"({r['cancellation_savings_pct']:.1f}%)")
        else:
            print(f"   no winner (timeout)")

    label = args.label or time.strftime("%Y%m%d_%H%M%S")
    out_path = out_dir / f"portfolio_{label}.json"
    out_path.write_text(json.dumps({
        "kind": "portfolio",
        "project_root": str(project_root),
        "goals_json": str(goals_json),
        "args": {k: str(v) for k, v in vars(args).items()},
        "runs": runs,
        "have_gnu_time": HAVE_GNU_TIME,
    }, indent=2))
    print()
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
