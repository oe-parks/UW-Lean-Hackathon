#!/usr/bin/env python3
"""Verify an agent's proof of a problem.

Two-stage verification:

  STAGE 1 (textual / anti-cheat):
    Reject the proof if it contains any forbidden token: by default
      sorry, admit, axiom <name>, native_decide, unsafe.
    Configurable via --forbid / --allow.

  STAGE 2 (semantic):
    Construct a *fresh* Lean file that consists of:
      <official imports>
      <official `theorem <name> : <statement>`>
        := <proof body extracted from agent's file>
      #print axioms <name>
    Compile it under `lake env lean`. Reject if:
      - non-zero exit, OR
      - any error diagnostic is reported, OR
      - the printed axioms include `sorryAx` or any axiom not in the
        small allow-set ({propext, Classical.choice, Quot.sound}, plus
        explicit additions via --allow-axiom).

The verifier writes a verdict JSON; non-zero exit code means "did not
verify". The reason is included in the verdict.

Usage as a script:

  ./verify_proof.py --problem problem.json --proof proof.lean \
      [--out verdict.json] [--allow-axiom Classical.choice] \
      [--allow-token native_decide]

Usage as a library: `import verify_proof; verify_proof.verify(...)`.
"""

import argparse
import json
import re
import shlex
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import List, Optional, Set, Tuple


DEFAULT_FORBIDDEN_TOKENS = {
    "sorry", "admit", "axiom", "native_decide", "unsafe",
    "extern", "implementedBy",
}

# Axioms Lean's stdlib introduces; these are considered fine.
DEFAULT_ALLOWED_AXIOMS = {
    "propext", "Classical.choice", "Quot.sound",
}


def _tokenize_for_check(text: str) -> List[str]:
    """Crude tokenization: ignore line/block comments and strings, then
    split on Lean identifier boundaries."""
    # Strip block comments  /-  ...  -/  (non-greedy, multiline)
    text = re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)
    # Strip line comments  --  ...
    text = re.sub(r"--[^\n]*", " ", text)
    # Strip "..." string literals
    text = re.sub(r'"(?:[^"\\]|\\.)*"', " ", text, flags=re.DOTALL)
    return re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text)


def textual_check(proof_src: str, forbidden: Set[str]) -> Optional[str]:
    """Return None if clean, else a reason string."""
    tokens = _tokenize_for_check(proof_src)
    seen = set(tokens)
    bad = sorted(seen & forbidden)
    if bad:
        return f"forbidden token(s) present: {', '.join(bad)}"
    return None


def _extract_proof_body(proof_src: str, theorem_name: str) -> Optional[str]:
    """Best-effort: pull out everything from `:=` (or the final `by` group)
    through the end of the theorem block. Returns None if not parseable.

    Strategy: find the line declaring `theorem <theorem_name>` (or
    `def <theorem_name>` / `example`); keep everything after the first
    `:=` on that block, until the next top-level decl or EOF.
    """
    # We require an exact-name match for theorem/lemma/def.
    pat = re.compile(
        rf"(?:^|\n)(theorem|lemma|def|example)\s+(?:{re.escape(theorem_name)}\b|(?=\s*:))",
        re.MULTILINE,
    )
    m = pat.search(proof_src)
    if m is None:
        return None
    start = m.end()
    rest = proof_src[start:]
    # Find `:=`
    eq_idx = rest.find(":=")
    if eq_idx < 0:
        return None
    body_start = eq_idx + 2
    # Heuristic: stop at the next top-level keyword.
    stop_pat = re.compile(
        r"\n(theorem|lemma|def|example|namespace|end|#check|#eval|#print)\s",
    )
    stop = stop_pat.search(rest, body_start)
    body = rest[body_start: stop.start() if stop else len(rest)]
    return body.strip()


def _make_canonical_lean(problem: dict, proof_body: str,
                         add_print_axioms: bool = True) -> str:
    """Construct a canonical Lean file from problem + agent's proof body."""
    imports = problem.get("imports", [])
    statement = problem["statement"].rstrip()
    name = problem["name"]
    lines: List[str] = []
    for imp in imports:
        lines.append(f"import {imp}")
    if imports:
        lines.append("")
    # Wrap in a namespace to avoid collisions and to make
    # `#print axioms <ns>.<name>` deterministic.
    lines.append(f"namespace _LATB_check_{name}")
    lines.append("")
    lines.append(f"{statement} := {proof_body}")
    lines.append("")
    if add_print_axioms:
        lines.append(f"#print axioms {name}")
    lines.append("")
    lines.append(f"end _LATB_check_{name}")
    return "\n".join(lines) + "\n"


_AXIOM_LINE = re.compile(
    r"axioms:\s*\[([^\]]*)\]", re.IGNORECASE,
)


def _parse_axioms_output(stdout: str) -> Set[str]:
    """Parse the output of `#print axioms <name>` into a set of axiom names."""
    # Lean 4 prints either:
    #   "'foo' depends on axioms: [Classical.choice, propext]"
    # or
    #   "'foo' does not depend on any axioms"
    # We handle the first form.
    out: Set[str] = set()
    for line in stdout.splitlines():
        line = line.strip()
        m = _AXIOM_LINE.search(line)
        if m:
            for ax in m.group(1).split(","):
                ax = ax.strip()
                if ax:
                    out.add(ax)
    return out


def semantic_check(
    project_root: Path,
    problem: dict,
    proof_src: str,
    timeout_s: float,
    allowed_axioms: Set[str],
) -> dict:
    """Compile a canonical reconstruction of (problem + proof) and check
    `#print axioms`. Returns a verdict dict."""

    name = problem["name"]
    body = _extract_proof_body(proof_src, name)
    if body is None:
        return {
            "verified": False,
            "reason": "could not extract proof body for theorem "
                      f"`{name}` from the proof file",
            "stage": "semantic.parse",
        }

    canonical = _make_canonical_lean(problem, body, add_print_axioms=True)

    with tempfile.TemporaryDirectory(prefix="latb_verify_") as td:
        td_path = Path(td)
        canon_path = td_path / f"check_{name}.lean"
        canon_path.write_text(canonical)
        t0 = time.perf_counter()
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(canon_path)],
                cwd=project_root,
                capture_output=True, text=True,
                timeout=timeout_s,
            )
            elapsed = time.perf_counter() - t0
            stdout = proc.stdout
            stderr = proc.stderr
            exit_code = proc.returncode
            timed_out = False
        except subprocess.TimeoutExpired as e:
            elapsed = time.perf_counter() - t0
            stdout = (e.stdout or b"").decode("utf-8", errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
            stderr = (e.stderr or b"").decode("utf-8", errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
            exit_code = None
            timed_out = True

    # Compile must have exited cleanly.
    if timed_out:
        return {
            "verified": False,
            "reason": f"verification compile timed out after {timeout_s}s",
            "stage": "semantic.compile",
            "elapsed_s": elapsed,
        }
    if exit_code != 0:
        return {
            "verified": False,
            "reason": "verification compile failed",
            "stage": "semantic.compile",
            "elapsed_s": elapsed,
            "exit_code": exit_code,
            "stdout": stdout[:4000],
            "stderr": stderr[:4000],
        }
    # Lean prints errors on stderr even on exit 0 sometimes; check both.
    if "error:" in stderr or re.search(r"^.+:\d+:\d+: error:", stdout, re.MULTILINE):
        return {
            "verified": False,
            "reason": "verification produced error diagnostics",
            "stage": "semantic.diagnostics",
            "elapsed_s": elapsed,
            "stdout": stdout[:4000],
            "stderr": stderr[:4000],
        }

    used_axioms = _parse_axioms_output(stdout)
    forbidden_axioms = used_axioms - allowed_axioms
    if forbidden_axioms:
        return {
            "verified": False,
            "reason": "proof depends on disallowed axioms: "
                      f"{', '.join(sorted(forbidden_axioms))}",
            "stage": "semantic.axioms",
            "elapsed_s": elapsed,
            "axioms_used": sorted(used_axioms),
        }

    return {
        "verified": True,
        "stage": "semantic.ok",
        "elapsed_s": elapsed,
        "axioms_used": sorted(used_axioms),
        "canonical_lean_size": len(canonical),
    }


def verify(
    project_root: Path,
    problem: dict,
    proof_src: str,
    forbidden_tokens: Optional[Set[str]] = None,
    allowed_axioms: Optional[Set[str]] = None,
    timeout_s: float = 60.0,
) -> dict:
    """Top-level verification. Returns a verdict dict (always with
    `verified: bool`)."""
    if forbidden_tokens is None:
        forbidden_tokens = set(DEFAULT_FORBIDDEN_TOKENS)
    if allowed_axioms is None:
        allowed_axioms = set(DEFAULT_ALLOWED_AXIOMS)

    text_reason = textual_check(proof_src, forbidden_tokens)
    if text_reason is not None:
        return {
            "verified": False,
            "reason": text_reason,
            "stage": "textual",
        }
    return semantic_check(project_root, problem, proof_src, timeout_s,
                          allowed_axioms)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--problem", type=Path, required=True,
                    help="Path to a problem JSON.")
    ap.add_argument("--proof", type=Path, required=True,
                    help="Path to the agent's proof Lean file.")
    ap.add_argument("--out", type=Path, default=None,
                    help="Where to write the verdict JSON.")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--forbid-token", action="append", default=[],
                    help="Add a forbidden token. (Use multiple times.)")
    ap.add_argument("--allow-token", action="append", default=[],
                    help="Remove a forbidden token. (Use multiple times.)")
    ap.add_argument("--allow-axiom", action="append", default=[],
                    help="Add an axiom name to the allowed set.")
    args = ap.parse_args()

    problem = json.loads(args.problem.read_text())
    proof_src = args.proof.read_text()

    forbidden = set(DEFAULT_FORBIDDEN_TOKENS)
    forbidden |= set(args.forbid_token)
    forbidden -= set(args.allow_token)

    allowed_axioms = set(DEFAULT_ALLOWED_AXIOMS) | set(args.allow_axiom)

    verdict = verify(
        args.project_root.resolve(),
        problem, proof_src,
        forbidden_tokens=forbidden,
        allowed_axioms=allowed_axioms,
        timeout_s=args.timeout,
    )
    print(json.dumps(verdict, indent=2))
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(verdict, indent=2))
    sys.exit(0 if verdict.get("verified") else 1)


if __name__ == "__main__":
    main()
