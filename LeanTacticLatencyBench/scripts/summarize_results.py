#!/usr/bin/env python3
"""Summarize raw JSON benchmark results into a single CSV.

Reads every `*.json` file under <project>/results/raw/ and emits one
row per data point in <project>/results/summary.csv.

Columns:
  kind, label, file_or_goal, repeat, elapsed_s, exit_code, timed_out,
  max_rss_kb, user_s, system_s, kill_latency_s, time_to_first_success_s,
  total_cpu_time_s

Cells that don't apply for a given row's `kind` are left blank.
"""

import argparse
import csv
import json
import sys
from pathlib import Path


HEADER = [
    "kind", "label", "file_or_goal", "repeat",
    "elapsed_s", "exit_code", "timed_out",
    "max_rss_kb", "user_s", "system_s",
    "kill_latency_s", "time_to_first_success_s", "total_cpu_time_s",
]


def rows_from_failed_proofs(meta: dict, label: str):
    for run in meta.get("runs", []):
        gt = run.get("gnu_time", {}) or {}
        yield {
            "kind": "failed_proof",
            "label": label,
            "file_or_goal": run.get("file"),
            "repeat": run.get("repeat"),
            "elapsed_s": run.get("elapsed_s"),
            "exit_code": run.get("exit_code"),
            "timed_out": run.get("timed_out"),
            "max_rss_kb": gt.get("max_rss_kb"),
            "user_s": gt.get("user_s"),
            "system_s": gt.get("system_s"),
            "kill_latency_s": "",
            "time_to_first_success_s": "",
            "total_cpu_time_s": "",
        }


def rows_from_portfolio(meta: dict, label: str):
    for run in meta.get("runs", []):
        # Winner row
        w = run.get("winner")
        if w:
            yield {
                "kind": "portfolio_winner",
                "label": label,
                "file_or_goal": f"{run['goal_name']} :: {w['tactic']}",
                "repeat": "",
                "elapsed_s": w.get("elapsed_s"),
                "exit_code": w.get("exit_code"),
                "timed_out": "",
                "max_rss_kb": "",
                "user_s": "",
                "system_s": "",
                "kill_latency_s": "",
                "time_to_first_success_s": run.get("time_to_first_success_s"),
                "total_cpu_time_s": run.get("total_cpu_time_s"),
            }
        # Loser rows
        for L in run.get("losers", []):
            gt = L.get("gnu_time", {}) or {}
            yield {
                "kind": "portfolio_loser",
                "label": label,
                "file_or_goal": f"{run['goal_name']} :: {L['tactic']}",
                "repeat": "",
                "elapsed_s": L.get("elapsed_s"),
                "exit_code": L.get("exit_code"),
                "timed_out": "",
                "max_rss_kb": gt.get("max_rss_kb"),
                "user_s": gt.get("user_s"),
                "system_s": gt.get("system_s"),
                "kill_latency_s": L.get("kill_latency_s"),
                "time_to_first_success_s": "",
                "total_cpu_time_s": "",
            }


def rows_from_lsp_stale(meta: dict, label: str):
    yield {
        "kind": "lsp_stale_cancel",
        "label": label,
        "file_or_goal": meta.get("slow_file"),
        "repeat": "",
        "elapsed_s": meta.get("cancel_latency_s"),
        "exit_code": "",
        "timed_out": meta.get("cancel_latency_s") is None,
        "max_rss_kb": "",
        "user_s": "",
        "system_s": "",
        "kill_latency_s": "",
        "time_to_first_success_s": "",
        "total_cpu_time_s": "",
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--out", type=Path, default=None,
                    help="Output CSV path (default: <project>/results/summary.csv).")
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    raw_dir = project_root / "results" / "raw"
    out = (args.out or (project_root / "results" / "summary.csv")).resolve()

    if not raw_dir.exists():
        print(f"No raw directory at {raw_dir}", file=sys.stderr)
        sys.exit(1)

    rows = []
    for fp in sorted(raw_dir.glob("*.json")):
        try:
            meta = json.loads(fp.read_text())
        except Exception as e:
            print(f"  skip {fp.name}: {e}", file=sys.stderr)
            continue
        kind = meta.get("kind", "")
        label = fp.stem
        if kind == "failed_proofs":
            rows.extend(rows_from_failed_proofs(meta, label))
        elif kind == "portfolio":
            rows.extend(rows_from_portfolio(meta, label))
        elif kind == "lsp_stale_cancel":
            rows.extend(rows_from_lsp_stale(meta, label))
        else:
            print(f"  unknown kind in {fp.name}: {kind!r}", file=sys.stderr)

    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=HEADER)
        w.writeheader()
        for r in rows:
            w.writerow(r)

    print(f"Wrote {out}  ({len(rows)} rows)")


if __name__ == "__main__":
    main()
