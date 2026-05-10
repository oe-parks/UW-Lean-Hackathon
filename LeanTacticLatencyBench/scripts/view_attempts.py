#!/usr/bin/env python3
"""Pretty-print an agent's attempts.jsonl — the tactic-by-tactic trail.

Usage:
  ./view_attempts.py results/agents/baseline_decide/nat_add_comm_all/attempts.jsonl
  ./view_attempts.py results/agents/baseline_random --filter nat_add_comm

Two modes:
  * Single file — pretty-print every record from one attempts.jsonl.
  * Directory — walk the agent's run dir and print attempts for every
    matching problem (--filter substring).

For each attempt we print:
  - attempt index + cumulative time-since-start
  - elapsed compile time
  - status: success / failure-kind (timeout, simp_no_progress,
    decide_stuck, type_mismatch, …)
  - tactic / candidate (truncated)
  - first error line from Lean's output (truncated)
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Optional

# Reuse the same classifier as profile_agent_run so labels are consistent.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from profile_agent_run import classify_failure, _normalize  # noqa: E402


_ANSI = {
    "reset": "\x1b[0m",
    "dim": "\x1b[2m",
    "green": "\x1b[32m",
    "red": "\x1b[31m",
    "yellow": "\x1b[33m",
    "cyan": "\x1b[36m",
    "bold": "\x1b[1m",
}


def _color(s: str, name: str, enabled: bool) -> str:
    if not enabled:
        return s
    return f"{_ANSI[name]}{s}{_ANSI['reset']}"


def _pick_error_line(rec: dict) -> str:
    """Find a short, informative error excerpt from Lean's output.

    Strips Lean's `<path>:<line>:<col>: ` prefix so we surface the
    actual message, not the noise."""
    blob = (rec.get("stderr_head") or "") + "\n" + (rec.get("stdout_head") or "")
    if not blob.strip():
        return ""
    # Prefer the first line containing 'error:'.
    for line in blob.splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.search(r"\berror:\s*(.*)$", line)
        if m:
            msg = m.group(1).strip()
            # Many Lean errors are "error: foo\n  details": just take foo.
            return msg if msg else line
    # Otherwise the first non-path-prefixed substantive line.
    for line in blob.splitlines():
        line = line.strip()
        if not line:
            continue
        # Strip a Lean source-position prefix if present.
        line = re.sub(r"^[^\s:]+\.lean:\d+:\d+:\s*", "", line)
        if len(line) > 4:
            return line
    return ""


def print_attempt(rec: dict, color: bool, tactic_width: int = 60,
                  full: bool = False, problem_dir: Optional[Path] = None) -> None:
    rec = _normalize(rec)
    rec["failure_kind"] = classify_failure(rec)
    idx = rec.get("index", "?")
    t = rec.get("t_since_start_s")
    el = rec.get("elapsed_s") or 0
    ok = rec.get("ok", False)
    kind = "OK" if ok else rec.get("failure_kind", "?")

    if ok:
        kind_disp = _color(f"{kind:<22}", "green", color)
    elif kind == "timeout":
        kind_disp = _color(f"{kind:<22}", "yellow", color)
    elif kind in ("api_error",):
        kind_disp = _color(f"{kind:<22}", "red", color)
    else:
        kind_disp = _color(f"{kind:<22}", "red", color)

    tactic = (rec.get("tactic") or "").strip().replace("\n", "  ")
    if len(tactic) > tactic_width:
        tactic = tactic[: tactic_width - 1] + "…"
    tactic_disp = _color(tactic, "cyan", color)

    err = _pick_error_line(rec) if not ok else ""
    err = err[:120] + ("…" if len(err) > 120 else "")
    err_disp = _color(err, "dim", color)

    t_str = f"{t:>5.2f}" if isinstance(t, (int, float)) else "    ?"
    print(f"  #{idx:<3}  t={t_str}s  {el:>5.3f}s  "
          f"{kind_disp}  {tactic_disp:<{tactic_width + 12}}  {err_disp}")

    if full and problem_dir is not None:
        # Print the full prompt / response / compile output for this
        # attempt. Files only exist for LLM agents that write them
        # (llm_claude.py); the other agents skip the transcript dir.
        for label, key in [("prompt", "prompt_path"),
                           ("response", "response_path"),
                           ("compile", "compile.compile_path")]:
            # rec might have nested compile.compile_path
            if "." in key:
                outer, inner = key.split(".", 1)
                rel = (rec.get(outer) or {}).get(inner)
            else:
                rel = rec.get(key)
            if not rel:
                continue
            path = problem_dir / rel
            if not path.exists():
                continue
            body = path.read_text()
            if not body.strip():
                continue
            header = _color(f"        ─── {label} ({path.name}) ───",
                            "yellow", color)
            print(header)
            for line in body.rstrip().splitlines():
                print(f"          {line}")
            print()


def view_file(path: Path, color: bool, full: bool = False) -> None:
    if not path.exists():
        print(f"(no attempts.jsonl at {path})")
        return
    problem_dir = path.parent
    print(_color(f"=== {problem_dir.name} === ", "bold", color))
    if full:
        sys_prompt = problem_dir / "transcripts" / "system_prompt.txt"
        if sys_prompt.exists():
            print(_color(f"  [system prompt: {sys_prompt}]", "dim", color))
            for line in sys_prompt.read_text().rstrip().splitlines():
                print(f"    {line}")
            print()
    n = 0
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        print_attempt(rec, color, full=full, problem_dir=problem_dir)
        n += 1
    if n == 0:
        print("  (empty log)")


def view_dir(agent_dir: Path, filt: Optional[str], color: bool,
             full: bool = False) -> None:
    """Walk every problem subdir under agent_dir, filtered by name substring."""
    children = sorted(p for p in agent_dir.iterdir() if p.is_dir())
    if not children:
        print(f"no problem subdirs under {agent_dir}", file=sys.stderr)
        sys.exit(1)
    matched = 0
    for sub in children:
        if filt and filt not in sub.name:
            continue
        view_file(sub / "attempts.jsonl", color, full=full)
        matched += 1
        print()
    if matched == 0:
        print(f"no problems matched filter {filt!r}", file=sys.stderr)
        sys.exit(1)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("path", type=Path,
                    help="Either an attempts.jsonl file or an agent run dir.")
    ap.add_argument("--filter", default=None,
                    help="If `path` is a directory, only show problems whose "
                         "name contains this substring.")
    ap.add_argument("--full", action="store_true",
                    help="Also print the full prompt, response, and Lean "
                         "compile output saved per attempt under "
                         "transcripts/. Only LLM-style agents (llm_claude) "
                         "write these — for tactic-pool agents, --full "
                         "still prints the per-row summary plus stderr "
                         "from the JSONL where present.")
    ap.add_argument("--no-color", action="store_true")
    args = ap.parse_args()

    color = (not args.no_color) and sys.stdout.isatty()

    p = args.path.resolve()
    if p.is_file():
        view_file(p, color, full=args.full)
    elif p.is_dir():
        view_dir(p, args.filter, color, full=args.full)
    else:
        sys.exit(f"not a file or directory: {p}")


if __name__ == "__main__":
    main()
