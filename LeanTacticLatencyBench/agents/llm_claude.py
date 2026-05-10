#!/usr/bin/env python3
"""LLM agent: ask Claude to prove the theorem; retry with Lean error feedback.

Same CLI contract as the other agents under `agents/`:

  python3 llm_claude.py --problem PROBLEM.json --workdir OUT/ \
      [--model claude-opus-4-7] [--max-attempts 4] \
      [--per-tactic-timeout 30] \
      [--system-prompt-file agents/prompts/llm_claude_default.txt]

Reads `ANTHROPIC_API_KEY` from the environment. Without it, exits 2 with
a clear message — the orchestrator will mark every problem unsolved
with the reason `agent did not produce proof.lean`. See the project's
`config.example.env` for the recommended way to set the key.

Stdlib-only (urllib + json) — no `pip install anthropic`, no extra deps.

For every attempt, this agent saves:

  WORKDIR/
    proof.lean                          ← the winning proof (if any)
    summary.json                        ← claimed_solved, attempts, …
    attempts.jsonl                      ← per-attempt metrics (one line each)
    transcripts/
      attempt_000.prompt.txt            ← full user message sent to Claude
      attempt_000.response.txt          ← full reply from Claude
      attempt_000.compile.txt           ← full Lean stdout+stderr
      attempt_001.prompt.txt
      …

`profile_agent_run.py` reads `attempts.jsonl`; `view_attempts.py
--full` reads the transcripts. The full-text files are what you
want when you're trying to *understand* what an LLM agent saw and
why it picked the candidate it did.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Dict, List, Optional


ANTHROPIC_URL = "https://api.anthropic.com/v1/messages"
DEFAULT_MODEL = "claude-opus-4-7"
DEFAULT_PROMPT_FILE = "agents/prompts/llm_claude_default.txt"


def _make_lean_file(problem: dict, proof_src: str) -> str:
    imports = problem.get("imports", []) or []
    parts: List[str] = []
    for imp in imports:
        parts.append(f"import {imp}")
    if imports:
        parts.append("")
    parts.append(proof_src.rstrip())
    parts.append("")
    return "\n".join(parts)


def _try_compile(project_root: Path, lean_file: Path,
                 timeout_s: float) -> dict:
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(lean_file)],
            cwd=project_root,
            capture_output=True, text=True,
            timeout=timeout_s,
        )
        elapsed = time.perf_counter() - t0
        ok = (proc.returncode == 0
              and "error:" not in proc.stderr
              and "error:" not in proc.stdout)
        return {
            "elapsed_s": elapsed,
            "exit_code": proc.returncode,
            "ok": ok,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "timed_out": False,
        }
    except subprocess.TimeoutExpired:
        return {
            "elapsed_s": time.perf_counter() - t0,
            "exit_code": None,
            "ok": False,
            "stdout": "",
            "stderr": f"compile timed out after {timeout_s}s",
            "timed_out": True,
        }


def _extract_lean_block(text: str) -> Optional[str]:
    if not text:
        return None
    m = re.search(r"```lean\s*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    m = re.search(r"```(?:\w+)?\s*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    return text.strip() or None


def _claude_request(
    api_key: str,
    model: str,
    system: str,
    messages: List[Dict],
    max_tokens: int = 2048,
    timeout_s: float = 90.0,
) -> dict:
    payload = {
        "model": model,
        "max_tokens": max_tokens,
        "system": system,
        "messages": messages,
    }
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        ANTHROPIC_URL,
        data=body,
        headers={
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            return json.loads(resp.read())
    except urllib.error.HTTPError as e:
        try:
            err_body = e.read().decode("utf-8", errors="replace")
        except Exception:
            err_body = "<unreadable>"
        raise RuntimeError(f"Anthropic HTTP {e.code}: {err_body}")
    except urllib.error.URLError as e:
        raise RuntimeError(f"network error: {e}")


def _response_text(response: dict) -> str:
    out: List[str] = []
    for block in response.get("content", []) or []:
        if block.get("type") == "text":
            out.append(block.get("text", ""))
    return "\n".join(out)


def _build_initial_prompt(problem: dict) -> str:
    return (
        f"Prove the following Lean 4 theorem.\n\n"
        f"Theorem name: `{problem['name']}`\n\n"
        f"```lean\n{problem['statement']}\n```\n\n"
        f"Imports available: {problem.get('imports', []) or 'none'}.\n\n"
        f"Reply with a single Lean code block containing the complete "
        f"`theorem {problem['name']} : … := …` declaration."
    )


def _build_retry_prompt(prev_proof: str, lean_output: str,
                        max_lean_chars: int = 4000) -> str:
    if len(lean_output) > max_lean_chars:
        lean_output = lean_output[-max_lean_chars:]
    return (
        f"That proof did not compile. The candidate was:\n\n"
        f"```lean\n{prev_proof}\n```\n\n"
        f"Lean reported:\n\n```\n{lean_output}\n```\n\n"
        f"Produce a corrected proof. Reply with a single Lean code block."
    )


def _resolve_system_prompt(args, project_root: Path) -> str:
    """Pick which prompt to use, in priority order:
       1. --system-prompt (literal string)
       2. --system-prompt-file (file path)
       3. $LATB_SYSTEM_PROMPT_FILE (env var)
       4. agents/prompts/llm_claude_default.txt (default)
    """
    if args.system_prompt is not None:
        return args.system_prompt
    candidate: Optional[Path] = None
    if args.system_prompt_file is not None:
        candidate = args.system_prompt_file
    elif os.environ.get("LATB_SYSTEM_PROMPT_FILE"):
        candidate = Path(os.environ["LATB_SYSTEM_PROMPT_FILE"])
    else:
        candidate = project_root / DEFAULT_PROMPT_FILE
    if not candidate.is_absolute():
        candidate = project_root / candidate
    if not candidate.exists():
        raise SystemExit(
            f"llm_claude: system prompt file not found: {candidate}\n"
            f"  Create one, or pass --system-prompt-file <path>."
        )
    return candidate.read_text()


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--problem", type=Path, required=True)
    ap.add_argument("--workdir", type=Path, required=True)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--model",
                    default=os.environ.get("ANTHROPIC_MODEL", DEFAULT_MODEL),
                    help=(f"Claude model ID. Default: $ANTHROPIC_MODEL or "
                          f"{DEFAULT_MODEL}."))
    ap.add_argument("--system-prompt", default=None,
                    help="Override the system prompt with a literal string.")
    ap.add_argument("--system-prompt-file", type=Path, default=None,
                    help=(f"Path to a file containing the system prompt. "
                          f"Default: {DEFAULT_PROMPT_FILE}, override via "
                          f"$LATB_SYSTEM_PROMPT_FILE."))
    ap.add_argument("--max-attempts", type=int, default=4)
    ap.add_argument("--per-tactic-timeout", type=float, default=30.0)
    ap.add_argument("--api-timeout", type=float, default=90.0)
    ap.add_argument("--max-tokens", type=int, default=2048)
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    workdir = args.workdir.resolve()
    workdir.mkdir(parents=True, exist_ok=True)
    transcripts_dir = workdir / "transcripts"
    transcripts_dir.mkdir(exist_ok=True)

    api_key = os.environ.get("ANTHROPIC_API_KEY")
    problem = json.loads(args.problem.read_text())
    log_path = workdir / "attempts.jsonl"

    if not api_key:
        sys.stderr.write(
            "llm_claude: ANTHROPIC_API_KEY is not set; cannot call the API.\n"
            "  See config.example.env in the project root.\n"
        )
        (workdir / "summary.json").write_text(json.dumps({
            "agent": "llm_claude",
            "problem_name": problem["name"],
            "claimed_solved": False,
            "winning_attempt": None,
            "attempts": 0,
            "total_wall_s": 0.0,
            "error": "ANTHROPIC_API_KEY not set",
        }, indent=2))
        log_path.write_text("")
        sys.exit(2)

    system_prompt = _resolve_system_prompt(args, project_root)
    # Save the system prompt once per run for easy review.
    (transcripts_dir / "system_prompt.txt").write_text(system_prompt)

    log_f = log_path.open("w")
    started = time.perf_counter()
    messages: List[Dict] = [
        {"role": "user", "content": _build_initial_prompt(problem)},
    ]
    final_proof: Optional[str] = None
    winning_attempt: Optional[int] = None
    total_input_tokens = 0
    total_output_tokens = 0
    last_error: Optional[str] = None

    for i in range(args.max_attempts):
        attempt_log: Dict = {
            "index": i,
            "t_since_start_s": time.perf_counter() - started,
        }

        # Persist the prompt for this attempt (the *latest* user message).
        latest_user = messages[-1]["content"]
        prompt_path = transcripts_dir / f"attempt_{i:03d}.prompt.txt"
        prompt_path.write_text(latest_user)
        attempt_log["prompt_path"] = str(prompt_path.relative_to(workdir))
        attempt_log["prompt_chars"] = len(latest_user)

        # 1. Ask Claude.
        try:
            t_api0 = time.perf_counter()
            resp = _claude_request(
                api_key, args.model, system_prompt, messages,
                max_tokens=args.max_tokens,
                timeout_s=args.api_timeout,
            )
            attempt_log["api_elapsed_s"] = time.perf_counter() - t_api0
            usage = resp.get("usage", {}) or {}
            attempt_log["input_tokens"] = usage.get("input_tokens", 0)
            attempt_log["output_tokens"] = usage.get("output_tokens", 0)
            total_input_tokens += int(usage.get("input_tokens", 0) or 0)
            total_output_tokens += int(usage.get("output_tokens", 0) or 0)
            attempt_log["stop_reason"] = resp.get("stop_reason")
        except Exception as e:
            attempt_log["api_error"] = str(e)
            log_f.write(json.dumps(attempt_log) + "\n")
            log_f.flush()
            last_error = f"API error: {e}"
            break

        text = _response_text(resp)
        # Persist the full response.
        response_path = transcripts_dir / f"attempt_{i:03d}.response.txt"
        response_path.write_text(text)
        attempt_log["response_path"] = str(response_path.relative_to(workdir))

        proof_src = _extract_lean_block(text) or ""
        attempt_log["raw_reply_chars"] = len(text)
        attempt_log["candidate_chars"] = len(proof_src)
        attempt_log["tactic"] = (proof_src.replace("\n", " ").strip() or "<no Lean block>")[:200]

        if not proof_src.strip():
            attempt_log["compile"] = {"ok": False,
                                      "reason": "no Lean block in reply",
                                      "stderr_head": "Reply contained no ```lean block."}
            attempt_log["failure_kind"] = "no_lean_block"
            log_f.write(json.dumps(attempt_log) + "\n")
            log_f.flush()
            messages.append({"role": "assistant", "content": text})
            messages.append({"role": "user", "content":
                "I did not see a Lean code block. Please reply with a single "
                "fenced ```lean … ``` block containing the complete proof."
            })
            continue

        # 2. Compile.
        scratch = workdir / f"attempt_{i:03d}.lean"
        scratch.write_text(_make_lean_file(problem, proof_src))
        comp = _try_compile(project_root, scratch, args.per_tactic_timeout)

        # Persist the full compile output (stdout + stderr).
        compile_path = transcripts_dir / f"attempt_{i:03d}.compile.txt"
        compile_blob = (
            f"# Lean exit code: {comp.get('exit_code')}\n"
            f"# Elapsed: {comp.get('elapsed_s', 0):.3f}s\n"
            f"# Timed out: {comp.get('timed_out', False)}\n\n"
            f"--- stdout ---\n{comp.get('stdout', '')}\n"
            f"--- stderr ---\n{comp.get('stderr', '')}\n"
        )
        compile_path.write_text(compile_blob)
        attempt_log["compile"] = {
            "ok": comp["ok"],
            "elapsed_s": comp["elapsed_s"],
            "exit_code": comp.get("exit_code"),
            "stdout_head": (comp.get("stdout") or "")[:2000],
            "stderr_head": (comp.get("stderr") or "")[:2000],
            "timed_out": comp.get("timed_out", False),
            "compile_path": str(compile_path.relative_to(workdir)),
        }
        log_f.write(json.dumps(attempt_log) + "\n")
        log_f.flush()

        if comp["ok"]:
            final_proof = _make_lean_file(problem, proof_src)
            winning_attempt = i
            break

        # 3. Retry with feedback.
        lean_blob = (comp.get("stderr") or "") + (comp.get("stdout") or "")
        messages.append({"role": "assistant", "content": text})
        messages.append({"role": "user",
                         "content": _build_retry_prompt(proof_src, lean_blob)})
        last_error = lean_blob[:200]

    log_f.close()

    if final_proof is not None:
        (workdir / "proof.lean").write_text(final_proof)
        claimed = True
    else:
        claimed = False

    summary = {
        "agent": "llm_claude",
        "model": args.model,
        "system_prompt_chars": len(system_prompt),
        "system_prompt_path": str(
            (transcripts_dir / "system_prompt.txt").relative_to(workdir)),
        "problem_name": problem["name"],
        "claimed_solved": claimed,
        "winning_attempt": winning_attempt,
        "attempts": sum(1 for _ in open(log_path)) if log_path.exists() else 0,
        "total_wall_s": time.perf_counter() - started,
        "total_input_tokens": total_input_tokens,
        "total_output_tokens": total_output_tokens,
        "last_error": last_error,
    }
    (workdir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))
    sys.exit(0 if claimed else 1)


if __name__ == "__main__":
    main()
