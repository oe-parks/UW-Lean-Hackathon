#!/usr/bin/env python3
"""Failed-proof latency benchmark.

For each *.lean file under --bench-dir, run `lake env lean <file>` and
record:
  * wall-clock elapsed time (seconds, perf_counter),
  * exit code,
  * stdout / stderr byte counts (and a truncated copy),
  * whether Lean's profiler emitted output (when --profiler is set),
  * peak memory and user/system CPU time (via /usr/bin/time -v, when
    available; otherwise these fields are recorded as None).

Output is written as JSON under --out-dir/raw/.
"""

import argparse
import json
import os
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Optional


def _have_gnu_time() -> bool:
    """Return True if /usr/bin/time supports the `-v` (verbose) flag.

    We use that mode to capture max-RSS and CPU time. macOS's BSD `time`
    does not implement `-v`, so the harness silently falls back to
    wall-clock-only measurement.
    """
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
    """Parse the verbose `/usr/bin/time -v` output. Best-effort."""
    keys = {
        "Maximum resident set size (kbytes)": "max_rss_kb",
        "User time (seconds)": "user_s",
        "System time (seconds)": "system_s",
        "Elapsed (wall clock) time (h:mm:ss or m:ss)": "wall_str",
        "Percent of CPU this job got": "cpu_pct",
        "Voluntary context switches": "vol_ctx_switches",
        "Involuntary context switches": "invol_ctx_switches",
    }
    out = {}
    for line in stderr.splitlines():
        line = line.strip()
        for src, dst in keys.items():
            if line.startswith(src):
                _, _, v = line.partition(":")
                out[dst] = v.strip()
    # Numeric coercion where reasonable
    for k in ("max_rss_kb", "vol_ctx_switches", "invol_ctx_switches"):
        if k in out:
            try:
                out[k] = int(out[k])
            except ValueError:
                pass
    for k in ("user_s", "system_s"):
        if k in out:
            try:
                out[k] = float(out[k])
            except ValueError:
                pass
    return out


def run_one(
    project_root: Path,
    lean_file: Path,
    profiler: bool,
    threshold: int,
    profiler_output: Optional[Path],
    timeout_s: float,
) -> dict:
    """Run lake env lean on a single file. Returns a metrics dict."""
    cmd = ["lake", "env", "lean"]
    if profiler:
        cmd += [
            "-Dtrace.profiler=true",
            f"-Dtrace.profiler.threshold={threshold}",
        ]
        if profiler_output is not None:
            cmd += [f"-Dtrace.profiler.output={profiler_output}"]
    cmd.append(str(lean_file.relative_to(project_root)))

    if HAVE_GNU_TIME:
        cmd = ["/usr/bin/time", "-v"] + cmd

    started_at = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            cwd=project_root,
            capture_output=True, text=True,
            timeout=timeout_s,
        )
        elapsed = time.perf_counter() - started_at
        timed_out = False
        stdout = proc.stdout
        stderr = proc.stderr
        exit_code = proc.returncode
    except subprocess.TimeoutExpired as e:
        elapsed = time.perf_counter() - started_at
        timed_out = True
        stdout = (e.stdout or b"").decode("utf-8", errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        stderr = (e.stderr or b"").decode("utf-8", errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        exit_code = None

    # GNU time writes its report on stderr, mixed with Lean's stderr.
    # That report is parseable by line.
    gtime = _parse_gnu_time(stderr) if HAVE_GNU_TIME else {}

    return {
        "file": str(lean_file.relative_to(project_root)),
        "command": " ".join(shlex.quote(p) for p in cmd),
        "elapsed_s": elapsed,
        "exit_code": exit_code,
        "timed_out": timed_out,
        "stdout_bytes": len(stdout.encode("utf-8")),
        "stderr_bytes": len(stderr.encode("utf-8")),
        "stdout_head": stdout[:2000],
        "stderr_head": stderr[:2000],
        "gnu_time": gtime,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent,
                    help="Root of the Lake project (default: parent of scripts/).")
    ap.add_argument("--bench-dir", type=Path,
                    default=None,
                    help="Directory of *.lean files to run (default: <project>/Bench/FailedProofs).")
    ap.add_argument("--repeats", type=int, default=3,
                    help="How many times to run each file (default: 3).")
    ap.add_argument("--profiler", action="store_true",
                    help="Pass -Dtrace.profiler=true.")
    ap.add_argument("--threshold", type=int, default=0,
                    help="Profiler threshold in ms (default: 0).")
    ap.add_argument("--profiler-output", type=Path, default=None,
                    help="If set, also pass -Dtrace.profiler.output=<path>.")
    ap.add_argument("--timeout", type=float, default=120.0,
                    help="Per-run wall-clock timeout in seconds (default: 120).")
    ap.add_argument("--out-dir", type=Path, default=None,
                    help="Where to drop the JSON result (default: <project>/results/raw).")
    ap.add_argument("--label", default=None,
                    help="Tag for the output filename (default: timestamp).")
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    bench_dir = (args.bench_dir or (project_root / "Bench" / "FailedProofs")).resolve()
    out_dir = (args.out_dir or (project_root / "results" / "raw")).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    files = sorted(bench_dir.glob("*.lean"))
    if not files:
        print(f"No *.lean files found under {bench_dir}", file=sys.stderr)
        sys.exit(1)

    print(f"# Failed-proof latency bench")
    print(f"# project: {project_root}")
    print(f"# files:   {len(files)}")
    print(f"# repeats: {args.repeats}")
    print(f"# profiler: {args.profiler}, threshold: {args.threshold}")
    print(f"# /usr/bin/time -v available: {HAVE_GNU_TIME}")
    print()

    runs = []
    for f in files:
        for i in range(args.repeats):
            res = run_one(project_root, f, args.profiler, args.threshold,
                          args.profiler_output, args.timeout)
            res["repeat"] = i
            runs.append(res)
            tag = "TO" if res["timed_out"] else f"x{res['exit_code']}"
            mem = res["gnu_time"].get("max_rss_kb", "?")
            print(f"  {f.name:<25}  run {i+1}/{args.repeats}  "
                  f"{res['elapsed_s']:6.3f}s  {tag}  rss={mem}kB")

    label = args.label or time.strftime("%Y%m%d_%H%M%S")
    out_path = out_dir / f"failed_proofs_{label}.json"
    out_path.write_text(json.dumps({
        "kind": "failed_proofs",
        "project_root": str(project_root),
        "bench_dir": str(bench_dir),
        "args": {k: str(v) for k, v in vars(args).items()},
        "runs": runs,
        "have_gnu_time": HAVE_GNU_TIME,
    }, indent=2))
    print()
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
