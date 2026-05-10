#!/usr/bin/env python3
"""LLM agent (OpenAI): ask GPT to prove the theorem; retry with Lean error feedback.

Same CLI contract as the other agents under `agents/`:

  python3 llm_openai.py --problem PROBLEM.json --workdir OUT/ \
      [--model gpt-4o] [--max-attempts 4] \
      [--per-tactic-timeout 30] \
      [--system-prompt-file agents/prompts/llm_openai_default.txt] \
      [--api-key-file <path>]

API key resolution order (first hit wins):
  1. --api-key-file <path>
  2. $OPENAI_API_KEY
  3. <project>/api
  4. <project>/../api    (matches this repo's layout)

If none of those resolve to a non-empty file or env var, the agent
exits 2 with a clear message and the orchestrator records every
problem as UNSOLVED. The key is *never* echoed to stdout, the log,
or the saved transcripts.

Stdlib-only (urllib + json) — no `pip install openai`, no extra deps.

For every attempt, this agent saves the full prompt sent to OpenAI,
the full reply, and the full Lean compile output to
`<workdir>/transcripts/`. See README §"What gets saved per attempt".
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


OPENAI_URL = "https://api.openai.com/v1/chat/completions"
DEFAULT_MODEL = "gpt-4o"
DEFAULT_PROMPT_FILE = "agents/prompts/llm_openai_default.txt"


def _load_api_key(args, project_root: Path) -> Optional[str]:
    """Resolve the OpenAI API key without ever printing it.

    Priority: CLI flag → env var → project-root `api` → project-parent `api`.
    Returns None if nothing is found; the caller decides how to fail.
    """
    candidates: List[Path] = []
    if args.api_key_file is not None:
        p = args.api_key_file if args.api_key_file.is_absolute() \
            else (project_root / args.api_key_file)
        candidates.append(p)
    env_key = os.environ.get("OPENAI_API_KEY")
    if env_key:
        return env_key.strip()
    candidates += [project_root / "api", project_root.parent / "api"]
    for c in candidates:
        try:
            if c.is_file() and c.stat().st_size > 0:
                key = c.read_text().strip()
                if key:
                    return key
        except OSError:
            continue
    return None


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


def _openai_chat(
    api_key: str,
    model: str,
    messages: List[Dict],
    max_tokens: int = 2048,
    timeout_s: float = 90.0,
) -> dict:
    """One call to the OpenAI Chat Completions API."""
    payload = {
        "model": model,
        "messages": messages,
        "max_tokens": max_tokens,
    }
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        OPENAI_URL,
        data=body,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
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
        # Strip anything that looks like the bearer token from the
        # error body — defensive; OpenAI doesn't echo it back, but be
        # paranoid before this lands in a transcript.
        err_body = re.sub(r"sk-[A-Za-z0-9_\-]+", "<redacted>", err_body)
        raise RuntimeError(f"OpenAI HTTP {e.code}: {err_body}")
    except urllib.error.URLError as e:
        raise RuntimeError(f"network error: {e}")


def _response_text(response: dict) -> str:
    """Concatenate text from the first choice of an OpenAI Chat response."""
    choices = response.get("choices") or []
    if not choices:
        return ""
    msg = choices[0].get("message") or {}
    content = msg.get("content")
    if isinstance(content, str):
        return content
    # Some newer models return content as a list of parts.
    if isinstance(content, list):
        out = []
        for part in content:
            if isinstance(part, dict) and "text" in part:
                out.append(part["text"])
            elif isinstance(part, str):
                out.append(part)
        return "\n".join(out)
    return ""


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
            f"llm_openai: system prompt file not found: {candidate}\n"
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
                    default=os.environ.get("OPENAI_MODEL", DEFAULT_MODEL),
                    help=(f"OpenAI model ID. Default: $OPENAI_MODEL or "
                          f"{DEFAULT_MODEL}."))
    ap.add_argument("--system-prompt", default=None,
                    help="Override the system prompt with a literal string.")
    ap.add_argument("--system-prompt-file", type=Path, default=None,
                    help=(f"Path to a file containing the system prompt. "
                          f"Default: {DEFAULT_PROMPT_FILE}, override via "
                          f"$LATB_SYSTEM_PROMPT_FILE."))
    ap.add_argument("--api-key-file", type=Path, default=None,
                    help=("File containing the OpenAI API key (single line). "
                          "If unset, falls back to $OPENAI_API_KEY, then "
                          "<project>/api, then <project>/../api."))
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

    problem = json.loads(args.problem.read_text())
    log_path = workdir / "attempts.jsonl"

    api_key = _load_api_key(args, project_root)
    if not api_key:
        sys.stderr.write(
            "llm_openai: no OpenAI API key found.\n"
            "  Tried: --api-key-file, $OPENAI_API_KEY, <project>/api, "
            "<project>/../api.\n"
            "  See config.example.env in the project root.\n"
        )
        (workdir / "summary.json").write_text(json.dumps({
            "agent": "llm_openai",
            "problem_name": problem["name"],
            "claimed_solved": False,
            "winning_attempt": None,
            "attempts": 0,
            "total_wall_s": 0.0,
            "error": "OPENAI_API_KEY not set / no api file found",
        }, indent=2))
        log_path.write_text("")
        sys.exit(2)

    system_prompt = _resolve_system_prompt(args, project_root)
    (transcripts_dir / "system_prompt.txt").write_text(system_prompt)

    log_f = log_path.open("w")
    started = time.perf_counter()
    # OpenAI carries the system prompt inside `messages` (role=system),
    # not as a top-level field. We still keep `messages` as a list of
    # user/assistant turns and prepend the system message at call time
    # so retries can append to it cleanly.
    chat_turns: List[Dict] = [
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

        latest_user = chat_turns[-1]["content"]
        prompt_path = transcripts_dir / f"attempt_{i:03d}.prompt.txt"
        prompt_path.write_text(latest_user)
        attempt_log["prompt_path"] = str(prompt_path.relative_to(workdir))
        attempt_log["prompt_chars"] = len(latest_user)

        try:
            t_api0 = time.perf_counter()
            full_messages = [{"role": "system", "content": system_prompt}] + chat_turns
            resp = _openai_chat(
                api_key, args.model, full_messages,
                max_tokens=args.max_tokens,
                timeout_s=args.api_timeout,
            )
            attempt_log["api_elapsed_s"] = time.perf_counter() - t_api0
            usage = resp.get("usage", {}) or {}
            attempt_log["input_tokens"] = usage.get("prompt_tokens", 0)
            attempt_log["output_tokens"] = usage.get("completion_tokens", 0)
            total_input_tokens += int(usage.get("prompt_tokens", 0) or 0)
            total_output_tokens += int(usage.get("completion_tokens", 0) or 0)
            choices = resp.get("choices") or []
            attempt_log["finish_reason"] = (
                (choices[0].get("finish_reason") if choices else None))
        except Exception as e:
            attempt_log["api_error"] = str(e)
            log_f.write(json.dumps(attempt_log) + "\n")
            log_f.flush()
            last_error = f"API error: {e}"
            break

        text = _response_text(resp)
        response_path = transcripts_dir / f"attempt_{i:03d}.response.txt"
        response_path.write_text(text)
        attempt_log["response_path"] = str(response_path.relative_to(workdir))

        proof_src = _extract_lean_block(text) or ""
        attempt_log["raw_reply_chars"] = len(text)
        attempt_log["candidate_chars"] = len(proof_src)
        attempt_log["tactic"] = (proof_src.replace("\n", " ").strip()
                                 or "<no Lean block>")[:200]

        if not proof_src.strip():
            attempt_log["compile"] = {
                "ok": False,
                "reason": "no Lean block in reply",
                "stderr_head": "Reply contained no ```lean block.",
            }
            attempt_log["failure_kind"] = "no_lean_block"
            log_f.write(json.dumps(attempt_log) + "\n")
            log_f.flush()
            chat_turns.append({"role": "assistant", "content": text})
            chat_turns.append({"role": "user", "content":
                "I did not see a Lean code block. Please reply with a single "
                "fenced ```lean … ``` block containing the complete proof."
            })
            continue

        scratch = workdir / f"attempt_{i:03d}.lean"
        scratch.write_text(_make_lean_file(problem, proof_src))
        comp = _try_compile(project_root, scratch, args.per_tactic_timeout)

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

        lean_blob = (comp.get("stderr") or "") + (comp.get("stdout") or "")
        chat_turns.append({"role": "assistant", "content": text})
        chat_turns.append({"role": "user",
                           "content": _build_retry_prompt(proof_src, lean_blob)})
        last_error = lean_blob[:200]

    log_f.close()

    if final_proof is not None:
        (workdir / "proof.lean").write_text(final_proof)
        claimed = True
    else:
        claimed = False

    summary = {
        "agent": "llm_openai",
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
