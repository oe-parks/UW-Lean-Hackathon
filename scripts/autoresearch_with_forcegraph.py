# scripts/autoresearch.py
import os
import subprocess
import json
import re
import sys
import time
import glob
import anthropic
import openai as openai_lib

FAST_TIMEOUT = 45   # seconds for lake env lean single-file check
SORRY_RE = re.compile(r'^(\s*)sorry\b', re.MULTILINE)

# Hard ban: these are never acceptable in a submitted proof
BANNED_RE = re.compile(r'\b(sorry|admit|native_decide)\b')

# ---------------------------------------------------------------------------
# Proof quality scoring
# ---------------------------------------------------------------------------

# Opaque automation — penalize: the model should not collapse reasoning into hammers
AUTOMATION_COSTS = {
    "decide":   6,   # computational proof, fully opaque
    "aesop":    4,   # "find it for me" — gives up on structure
    "simp":     3,   # bare simp searches arbitrarily
    "tauto":    3,
    "omega":    2,   # ok for arithmetic, but lazy for structural goals
    "linarith": 2,
    "norm_num": 2,
    "ring":     1,   # acceptable for ring equalities
}

# Explicit structure — reward: these indicate real mathematical reasoning
STRUCTURE_BONUSES = {
    "calc":        4,   # step-by-step equational chains
    "have":        3,   # named intermediate results
    "obtain":      3,   # named destructions
    "refine":      2,   # partial application with named holes
    "rcases":      2,   # explicit case analysis
    "constructor": 2,
    "exact":       1,   # explicit term application
    "apply":       1,
    "rw":          1,
    "intro":       1,
}


def proof_quality_score(candidate: str, compile_time: float) -> float:
    """
    Lower is better.
    Structure and explicitness dominate; compile time is a minor tiebreaker.
    """
    automation = sum(
        len(re.findall(rf'\b{re.escape(t)}\b', candidate)) * cost
        for t, cost in AUTOMATION_COSTS.items()
    )
    structure = sum(
        len(re.findall(rf'\b{re.escape(t)}\b', candidate)) * bonus
        for t, bonus in STRUCTURE_BONUSES.items()
    )
    lines = len([l for l in candidate.splitlines() if l.strip()])
    brevity_penalty = max(0, (2 - lines) * 1.5)

    return (
        0.1 * compile_time
        + 2.0 * automation
        - 1.5 * structure
        + brevity_penalty
    )

# Backends: "anthropic" | "ollama" | "openai"
_backend = "anthropic"
_anthropic_client = None
_openai_client = None


def _setup_clients(backend: str):
    global _backend, _anthropic_client, _openai_client
    _backend = backend
    if backend == "ollama":
        _openai_client = openai_lib.OpenAI(
            base_url="http://localhost:11434/v1",
            api_key="ollama",
        )
    elif backend == "openai":
        _openai_client = openai_lib.OpenAI()
    else:
        _anthropic_client = anthropic.Anthropic()


# ---------------------------------------------------------------------------
# File discovery — no lake build required
# ---------------------------------------------------------------------------

def find_sorry_files_by_scan(target_file=None):
    """Scan .lean files for tactic-mode sorries. Returns {path: count}."""
    if target_file:
        candidates = glob.glob("Hackathon/**/*.lean", recursive=True)
        paths = [p for p in candidates if target_file in p]
        if not paths:
            paths = [target_file]
    else:
        paths = glob.glob("Hackathon/**/*.lean", recursive=True)

    result = {}
    for path in paths:
        try:
            content = read_file(path)
            count = len(SORRY_RE.findall(content))
            if count > 0:
                result[path] = count
        except FileNotFoundError:
            pass
    return result


# ---------------------------------------------------------------------------
# Build helpers (final confirmation only)
# ---------------------------------------------------------------------------

def build_and_measure():
    subprocess.run(["./scripts/measure-build.sh"], capture_output=True, text=True)
    with open("build-report.json") as f:
        return json.load(f)


def get_sorry_locations(report):
    sorry_files = report.get("sorry_per_file", {})
    return {
        path: count
        for path, count in sorry_files.items()
        if count > 0
        and "Hackathon/Untitled/.lake" not in path
        and path.startswith("Hackathon/")
    }


# ---------------------------------------------------------------------------
# File I/O
# ---------------------------------------------------------------------------

def read_file(path):
    with open(path) as f:
        return f.read()


def write_file(path, content):
    with open(path, "w") as f:
        f.write(content)


# ---------------------------------------------------------------------------
# Goal extraction (sorry-filling mode)
# ---------------------------------------------------------------------------

def find_first_tactic_sorry(content):
    for m in SORRY_RE.finditer(content):
        indent = m.group(1)
        if indent:
            return m.start(), indent
    return None, None


def _lake_run(file_path: str, timeout: int):
    """
    Run `lake env lean <file>` from the nearest lakefile ancestor of file_path.
    This lets files inside sub-projects (e.g. physlib-master) use their own
    lake environment instead of the repo root's environment.
    """
    directory = os.path.dirname(os.path.abspath(file_path))
    cwd = os.getcwd()
    while True:
        if (os.path.exists(os.path.join(directory, "lakefile.lean"))
                or os.path.exists(os.path.join(directory, "lakefile.toml"))):
            cwd = directory
            break
        parent = os.path.dirname(directory)
        if parent == directory:
            break
        directory = parent
    lean_arg = os.path.relpath(os.path.abspath(file_path), cwd)
    return subprocess.run(
        ["lake", "env", "lean", lean_arg],
        capture_output=True, text=True, timeout=timeout,
        cwd=cwd,
    )


def get_lean_goal_state(file_path, content):
    start, indent = find_first_tactic_sorry(content)
    if start is None:
        return ""
    modified = content[:start] + f"{indent}trace_state\n" + content[start:]
    write_file(file_path, modified)
    try:
        result = _lake_run(file_path, FAST_TIMEOUT)
        return _parse_goal_from_output(result.stderr + result.stdout)
    except subprocess.TimeoutExpired:
        return ""
    finally:
        write_file(file_path, content)


def _parse_goal_from_output(output):
    goal_lines = []
    capturing = False
    for line in output.split('\n'):
        if re.search(r':\d+:\d+: information:', line):
            capturing = True
            after = re.sub(r'.*:\d+:\d+: information:\s*', '', line)
            if after.strip():
                goal_lines.append(after)
            continue
        if capturing:
            if re.match(r'.+:\d+:\d+:', line):
                break
            goal_lines.append(line)
    return '\n'.join(goal_lines).strip()


# ---------------------------------------------------------------------------
# Fast single-file validation
# ---------------------------------------------------------------------------

def _has_lean_error(output: str, returncode: int) -> bool:
    """True only for real compile failures — sorry warnings are not errors."""
    return (
        returncode != 0
        or bool(re.search(r':\d+:\d+: error:', output))
        or bool(re.search(r'unsolved goals', output))
    )


def check_file_fast(file_path):
    try:
        result = _lake_run(file_path, FAST_TIMEOUT)
        output = result.stderr + result.stdout
        return not _has_lean_error(output, result.returncode), output
    except subprocess.TimeoutExpired:
        return False, "timeout"


def measure_compile_time(file_path, content=None):
    """Compile a file and return wall-clock seconds. Returns inf on failure."""
    if content is not None:
        write_file(file_path, content)
    t0 = time.time()
    try:
        result = _lake_run(file_path, 180)
        elapsed = time.time() - t0
        out = result.stderr + result.stdout
        if _has_lean_error(out, result.returncode):
            return float('inf')
        return elapsed
    except subprocess.TimeoutExpired:
        return float('inf')


def _parse_error_lines(output: str) -> set:
    """Return 1-indexed line numbers that have a Lean `: error:` marker."""
    return {int(m.group(1)) for m in re.finditer(r':(\d+):\d+: error:', output)}


def _measure_permissive(file_path: str, content: str, baseline_errors: set) -> float:
    """
    Compile file_path with content. Returns elapsed seconds unless the candidate
    introduces error lines beyond baseline_errors (i.e. makes things worse).
    Allows files that already have errors in other blocks to still be optimised.
    """
    write_file(file_path, content)
    t0 = time.time()
    try:
        result = _lake_run(file_path, 180)
        elapsed = time.time() - t0
        out = result.stderr + result.stdout
        new_errors = _parse_error_lines(out) - baseline_errors
        if new_errors:
            return float('inf')
        return elapsed
    except subprocess.TimeoutExpired:
        return float('inf')


# ---------------------------------------------------------------------------
# Proof-block parsing (optimize mode)
# ---------------------------------------------------------------------------

_BY_END_RE = re.compile(r':=\s*by\s*$')


def find_proof_blocks(content):
    """
    Find all `theorem/lemma/example/def ... := by` tactic proof blocks.
    Returns a list of dicts with:
      decl_line, proof_start, proof_end, declaration, proof_body, decl_indent
    """
    lines = content.split('\n')
    blocks = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if _BY_END_RE.search(line) and line.strip():
            decl_indent = len(line) - len(line.lstrip())
            # collect indented proof body
            j = i + 1
            proof_start = j
            while j < len(lines):
                pline = lines[j]
                if not pline.strip():
                    j += 1
                    continue
                if len(pline) - len(pline.lstrip()) > decl_indent:
                    j += 1
                else:
                    break
            # trim trailing blank lines
            proof_end = j
            while proof_end > proof_start and not lines[proof_end - 1].strip():
                proof_end -= 1

            if proof_end > proof_start:
                blocks.append({
                    'decl_line':   i,
                    'proof_start': proof_start,
                    'proof_end':   proof_end,
                    'declaration': line.strip(),
                    'proof_body':  '\n'.join(lines[proof_start:proof_end]),
                    'decl_indent': decl_indent,
                })
                i = proof_end
                continue
        i += 1
    return blocks


def replace_proof_block(content, block, new_proof_body):
    """Swap the proof body of a block with new_proof_body."""
    lines = content.split('\n')
    new_lines = (
        lines[:block['proof_start']]
        + new_proof_body.split('\n')
        + lines[block['proof_end']:]
    )
    return '\n'.join(new_lines)


# ---------------------------------------------------------------------------
# Candidate filtering
# ---------------------------------------------------------------------------

def is_banned(candidate: str) -> bool:
    return bool(BANNED_RE.search(candidate))


# ---------------------------------------------------------------------------
# LLM — sorry-filling
# ---------------------------------------------------------------------------

def _build_sorry_prompt(file_path, file_content, goal_state, error_feedback):
    system = (
        "You are an expert Lean 4 proof assistant for graph theory and combinatorics (Mathlib).\n"
        "Your task: close the first `sorry` with a CORRECT, READABLE proof.\n\n"
        "Output ONLY valid JSON:\n"
        '{"candidates": ["tactic1", "tactic2", ...], "reasoning": "..."}\n\n'
        "Guidelines:\n"
        "- Provide 3-5 candidates, ordered most-to-least likely to work\n"
        "- Each candidate replaces one `sorry`; use \\n for multi-line steps\n"
        "- STRONGLY PREFER multi-step proofs with named intermediate results:\n"
        "    have h : ... := ...\n"
        "    exact ...\n"
        "- PREFER explicit theorem applications: `exact Foo.bar h1 h2`, `apply Baz.lemma`\n"
        "- USE `exact?` or `apply?` when you are not sure of the exact lemma name —\n"
        "  these search the library and produce real proofs, not hallucinations\n"
        "- AVOID bare `simp`, `aesop`, `omega`, `decide` unless the goal is\n"
        "  purely computational with no mathematical content\n"
        "- NEVER use sorry, admit, native_decide\n"
        "- NEVER invent Mathlib lemma names — use exact?/apply? if uncertain\n"
        "- A proof with 4 explicit steps is better than `by simp`"
    )
    variable_parts = []
    if goal_state:
        variable_parts.append(f"Proof goal at first sorry:\n{goal_state}")
    if error_feedback:
        variable_parts.append(
            f"Previous candidates failed:\n{error_feedback[:600]}\n\n"
            "Try structurally different approaches — more `have` steps, different lemmas."
        )
    variable_parts.append("Return JSON candidates to close the first `sorry`.")
    user = f"File: {file_path}\n\n{file_content}\n\n" + "\n\n".join(variable_parts)
    return system, user


def _build_opt_prompt(block):
    system = (
        "You are a Lean 4 proof refactoring assistant.\n"
        "Your task: improve the CLARITY and STRUCTURE of a proof without changing its meaning.\n\n"
        "Output ONLY valid JSON:\n"
        '{"candidates": ["body1", "body2", ...], "reasoning": "..."}\n\n'
        "Allowed improvements:\n"
        "- Replace bare `simp` with `simp only [specific_lemmas]`\n"
        "- Extract repeated reasoning into named `have` blocks\n"
        "- Replace `omega` with an explicit arithmetic lemma when clearer\n"
        "- Replace anonymous `_` with named hypotheses\n"
        "- Break a long single-line tactic into readable steps\n\n"
        "FORBIDDEN — do NOT:\n"
        "- Introduce `aesop`, `decide`, `native_decide`, `tauto`\n"
        "- Collapse a structured proof into a single `simp` call\n"
        "- Increase the total automation level vs. the original\n"
        "- Add sorry or admit\n\n"
        "Each candidate is the INDENTED PROOF BODY only — no `by`, no declaration.\n"
        "Use \\n for newlines. Match the indentation of the current proof."
    )
    variable_ctx = (
        f"Proof block to refactor:\n"
        f"```lean\n{block['declaration']}\n  by\n{block['proof_body']}\n```\n\n"
        "Suggest 2-4 refactored proof bodies (proof body only, without `by`)."
    )
    return system, variable_ctx


def _parse_candidates(text):
    json_match = re.search(r'\{[\s\S]*\}', text)
    if json_match:
        try:
            data = json.loads(json_match.group())
            return data.get("candidates", []), data.get("reasoning", "")
        except json.JSONDecodeError:
            pass
    return [text.strip()], ""


def _call_llm(system, file_path, file_content, variable_ctx):
    if _backend in ("ollama", "openai"):
        model = "qwen2.5-coder:7b" if _backend == "ollama" else "gpt-4o"
        response = _openai_client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": system},
                {"role": "user", "content": f"File: {file_path}\n\n{file_content}\n\n{variable_ctx}"},
            ],
            max_tokens=1024,
            temperature=0.2,
        )
        return response.choices[0].message.content
    else:
        response = _anthropic_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=1024,
            system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral"}}],
            messages=[{"role": "user", "content": [
                {"type": "text", "text": f"File: {file_path}\n\n{file_content}",
                 "cache_control": {"type": "ephemeral"}},
                {"type": "text", "text": variable_ctx},
            ]}],
        )
        return response.content[0].text


def get_sorry_candidates(file_path, file_content, goal_state, error_feedback=None):
    system, user = _build_sorry_prompt(file_path, file_content, goal_state, error_feedback)
    # for sorry-filling the variable_ctx is baked into `user` already
    if _backend in ("ollama", "openai"):
        model = "qwen2.5-coder:7b" if _backend == "ollama" else "gpt-4o"
        response = _openai_client.chat.completions.create(
            model=model,
            messages=[{"role": "system", "content": system}, {"role": "user", "content": user}],
            max_tokens=1024, temperature=0.2,
        )
        text = response.choices[0].message.content
    else:
        response = _anthropic_client.messages.create(
            model="claude-sonnet-4-6", max_tokens=1024,
            system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral"}}],
            messages=[{"role": "user", "content": [
                {"type": "text", "text": f"File: {file_path}\n\n{file_content}",
                 "cache_control": {"type": "ephemeral"}},
                {"type": "text", "text": "\n\n".join(
                    ([f"Proof goal at first sorry:\n{goal_state}"] if goal_state else []) +
                    ([f"Previous candidates failed:\n{error_feedback[:600]}\nSuggest different approaches."]
                     if error_feedback else []) +
                    ["Return JSON candidates to close the first `sorry`."]
                )},
            ]}],
        )
        text = response.content[0].text
    return _parse_candidates(text)


def get_opt_candidates(file_path, file_content, block):
    system, variable_ctx = _build_opt_prompt(block)
    text = _call_llm(system, file_path, file_content, variable_ctx)
    return _parse_candidates(text)[0]  # just the candidates list


# ---------------------------------------------------------------------------
# Proof-search tree visualization
# ---------------------------------------------------------------------------

def _print_search_tree(header, results, chosen=None):
    """
    Render an ASCII tree of what was tried and what was selected.

    results: list of dicts with keys:
      short        one-line preview (already truncated)
      status       'banned' | 'fail' | 'pass'
      score        float — quality score (lower = better)
      compile_time float — seconds (inf if not compiled)
      error_msg    str
    chosen: the result dict that was selected (identity comparison), or None
    """
    results = [r for r in results if r]
    n = len(results)

    print(f"\n  ┌─ {header}")

    for i, r in enumerate(results):
        is_last = (i == n - 1)
        branch = "  └──" if is_last else "  ├──"
        cont   = "       " if is_last else "  │    "
        short  = r['short'][:52]

        if r['status'] == 'banned':
            print(f"{branch} [BANNED]  {short}")

        elif r['status'] == 'fail':
            print(f"{branch} [FAIL]    {short}")
            if r.get('error_msg'):
                print(f"{cont}           ↳ {r['error_msg'][:62]}")

        else:  # pass
            star = "★ " if r is chosen else "  "
            pct_vs_base = r.get('pct_vs_baseline')
            pct_str = f"  ({pct_vs_base:+.1f}% vs baseline)" if pct_vs_base is not None else ""
            print(
                f"{branch} [{star}PASS]  {short}"
                f"   score={r['score']:.2f}  t={r['compile_time']:.2f}s{pct_str}"
            )

    # Summary line + speed/quality comparison note
    if chosen:
        others = [r for r in results if r['status'] == 'pass' and r is not chosen]
        print(f"  └─ ★ chosen: \"{chosen['short'][:48]}\"")
        print(f"              score={chosen['score']:.2f}  t={chosen['compile_time']:.2f}s")
        for other in others:
            qdiff = other['score'] - chosen['score']    # positive = chosen has better quality
            tdiff = chosen['compile_time'] - other['compile_time']  # positive = chosen is slower
            q_note = (
                f"{qdiff:+.2f} quality advantage" if qdiff > 0
                else f"{qdiff:+.2f} quality disadvantage"
            )
            if abs(tdiff) < 0.02:
                t_note = "same speed"
            else:
                pct = abs(tdiff) / max(other['compile_time'], 0.001) * 100
                t_note = f"{'slower' if tdiff > 0 else 'faster'} by {abs(tdiff):.2f}s ({pct:.1f}%)"
            print(
                f"              vs \"{other['short'][:42]}\"  "
                f"score={other['score']:.2f} ({q_note}),  {t_note}"
            )
    elif not any(r['status'] == 'pass' for r in results):
        print(f"  └─ ✗ no candidate passed")
    print()
    _viz_record_search(header, results, chosen)


# ---------------------------------------------------------------------------
# HTML force-directed graph export
# ---------------------------------------------------------------------------

_viz_nodes: list = []
_viz_links: list = []
_viz_id = 0


def _viz_next_id() -> int:
    global _viz_id
    _viz_id += 1
    return _viz_id


def _viz_record_search(header: str, results: list, chosen=None):
    """Append one proof-search event to the global graph accumulator."""
    root_id = _viz_next_id()
    _viz_nodes.append({
        "id": root_id, "type": "search_root", "label": header,
        "score": None, "time": None, "error_msg": "", "pct_vs_baseline": None,
    })
    for r in results:
        nid = _viz_next_id()
        if r["status"] == "banned":
            ntype = "banned"
        elif r["status"] == "fail":
            ntype = "fail"
        elif r is chosen:
            ntype = "pass_chosen"
        else:
            ntype = "pass_other"
        _viz_nodes.append({
            "id":             nid,
            "type":           ntype,
            "label":          r["short"],
            "score":          None if r["score"] in (None, float("inf")) else r["score"],
            "time":           None if r["compile_time"] in (None, float("inf")) else r["compile_time"],
            "error_msg":      r.get("error_msg", ""),
            "pct_vs_baseline": r.get("pct_vs_baseline"),
        })
        _viz_links.append({"source": root_id, "target": nid, "is_chosen": r is chosen})


_VIZ_HTML = """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>autoresearch decision trace</title>
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    html, body { width: 100%; height: 100%; overflow: hidden; background: #0d1117; color: #e6edf3; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }

    #header {
      position: fixed; top: 0; left: 0; right: 0; z-index: 10;
      display: flex; align-items: center; gap: 16px;
      padding: 10px 18px;
      background: rgba(13,17,23,0.92); backdrop-filter: blur(8px);
      border-bottom: 1px solid #30363d;
    }
    #header h1 { font-size: 15px; font-weight: 600; color: #e6edf3; white-space: nowrap; }
    #header .meta { font-size: 12px; color: #7d8590; white-space: nowrap; }
    #header .spacer { flex: 1; }
    #legend { display: flex; gap: 10px; align-items: center; flex-wrap: wrap; }
    .leg { display: flex; align-items: center; gap: 5px; font-size: 11px; color: #adbac7; }
    .leg-dot { width: 12px; height: 12px; border-radius: 50%; border: 1.5px solid rgba(255,255,255,0.15); flex-shrink:0; }
    #controls { display: flex; gap: 8px; }
    button {
      background: #21262d; border: 1px solid #30363d; color: #adbac7;
      border-radius: 6px; padding: 4px 10px; font-size: 12px; cursor: pointer;
    }
    button:hover { background: #30363d; color: #e6edf3; }

    #canvas-wrap { position: fixed; top: 48px; left: 0; right: 0; bottom: 0; }
    svg { width: 100%; height: 100%; }

    .link { stroke: #444c56; stroke-opacity: 0.7; fill: none; }
    .link-label { font-size: 10px; fill: #7d8590; pointer-events: none; }

    .node-group { cursor: pointer; }
    .node-rect { rx: 7; stroke-width: 1.5; filter: drop-shadow(0 2px 6px rgba(0,0,0,0.5)); }
    .node-kind { font-size: 10px; fill: #7d8590; font-family: ui-monospace,monospace; }
    .node-label { font-size: 11px; fill: #e6edf3; font-weight: 600; }
    .node-status { font-size: 10px; font-family: ui-monospace,monospace; }
    .node-timing { font-size: 10px; fill: #7d8590; font-family: ui-monospace,monospace; }
    .node-group:hover .node-rect { stroke-opacity: 1 !important; stroke-width: 2; }

    #tooltip {
      position: fixed; z-index: 100; pointer-events: none;
      background: #161b22; border: 1px solid #30363d; border-radius: 8px;
      padding: 12px 14px; max-width: 420px; font-size: 12px; line-height: 1.55;
      box-shadow: 0 8px 24px rgba(0,0,0,0.6);
      display: none;
    }
    #tooltip .tt-kind { color: #7d8590; font-family: monospace; font-size: 11px; margin-bottom: 4px; }
    #tooltip .tt-label { color: #e6edf3; font-weight: 600; margin-bottom: 6px; word-break: break-word; }
    #tooltip .tt-status { font-weight: 700; font-family: monospace; margin-bottom: 6px; }
    #tooltip table { border-collapse: collapse; width: 100%; margin-top: 6px; }
    #tooltip th { text-align: right; color: #7d8590; padding: 2px 8px 2px 0; vertical-align: top; white-space: nowrap; font-weight: 400; }
    #tooltip td { color: #adbac7; padding: 2px 0; word-break: break-word; max-width: 280px; }
    #tooltip pre { background: #0d1117; border-radius: 4px; padding: 6px 8px; margin-top: 4px; white-space: pre-wrap; font-size: 11px; color: #adbac7; max-height: 160px; overflow-y: auto; }
  </style>
</head>
<body>
<div id="header">
  <h1>autoresearch decision trace</h1>
  <span class="meta">__META__</span>
  <div class="spacer"></div>
  <div id="legend">
    <div class="leg"><div class="leg-dot" style="background:#3fb950;"></div>Chosen ★</div>
    <div class="leg"><div class="leg-dot" style="background:#f0883e;"></div>Search root</div>
    <div class="leg"><div class="leg-dot" style="background:#388bfd;"></div>Passing</div>
    <div class="leg"><div class="leg-dot" style="background:#da3633;"></div>Failed</div>
    <div class="leg"><div class="leg-dot" style="background:#444c56;"></div>Banned</div>
  </div>
  <div id="controls">
    <button id="btn-reset">Reset view</button>
    <button id="btn-pin">Unpin all</button>
  </div>
</div>

<div id="canvas-wrap"><svg id="graph"></svg></div>
<div id="tooltip"></div>

<script src="https://cdnjs.cloudflare.com/ajax/libs/d3/7.9.0/d3.min.js"></script>
<script>
const GRAPH = __GRAPH_DATA__;

const STATUS_COLORS = {
  pass_chosen: "#3fb950",
  search_root: "#f0883e",
  pass_other:  "#388bfd",
  fail:        "#da3633",
  banned:      "#444c56",
};
const STATUS_TEXT = {
  pass_chosen: "#d2ffd8",
  search_root: "#ffd8a8",
  pass_other:  "#cae8ff",
  fail:        "#ffdcd7",
  banned:      "#adbac7",
};
const KIND_BG = {
  search_root: "#161b22",
  pass_chosen: "#1c2128",
  pass_other:  "#1c2128",
  fail:        "#161b22",
  banned:      "#161b22",
};

function nodeColor(d) { return STATUS_COLORS[d.status] || "#555"; }
function nodeBg(d)    { return KIND_BG[d.status]    || "#161b22"; }
function statusTextColor(d) { return STATUS_TEXT[d.status] || "#adbac7"; }

const nodeById = {};
GRAPH.nodes.forEach(n => { nodeById[n.id] = n; });

const nodes = GRAPH.nodes.map(n => ({
  id: n.id,
  kind: n.kind,
  label: n.label,
  status: n.status || "",
  attrs: n.attrs || {},
}));

const links = GRAPH.edges.map(e => ({
  source: e.from,
  target: e.to,
  label: e.label || "",
  is_chosen: e.is_chosen || false,
}));

const svg = d3.select("#graph");
const wrap = document.getElementById("canvas-wrap");

function dims() { return { w: wrap.clientWidth, h: wrap.clientHeight }; }

const defs = svg.append("defs");
defs.append("marker")
  .attr("id", "arrow")
  .attr("viewBox", "0 -4 8 8")
  .attr("refX", 8).attr("refY", 0)
  .attr("markerWidth", 6).attr("markerHeight", 6)
  .attr("orient", "auto")
  .append("path")
  .attr("d", "M0,-4L8,0L0,4")
  .attr("fill", "#555");

const g = svg.append("g");

const zoom = d3.zoom()
  .scaleExtent([0.08, 4])
  .on("zoom", e => g.attr("transform", e.transform));
svg.call(zoom);

const {w, h} = dims();
const sim = d3.forceSimulation(nodes)
  .force("link", d3.forceLink(links).id(d => d.id).distance(180).strength(0.6))
  .force("charge", d3.forceManyBody().strength(-600))
  .force("center", d3.forceCenter(w / 2, h / 2))
  .force("collide", d3.forceCollide(90))
  .force("x", d3.forceX(w / 2).strength(0.04))
  .force("y", d3.forceY(h / 2).strength(0.04));

const linkSel = g.append("g").selectAll("line")
  .data(links).join("line")
  .attr("class", "link")
  .attr("stroke", d => d.is_chosen ? "#3fb950" : "#444c56")
  .attr("stroke-opacity", d => d.is_chosen ? 0.9 : 0.7)
  .attr("stroke-width", d => d.is_chosen ? 2.5 : 1.5)
  .attr("marker-end", "url(#arrow)");

const linkLabelSel = g.append("g").selectAll("text")
  .data(links.filter(l => l.label)).join("text")
  .attr("class", "link-label")
  .text(d => d.label);

const NODE_W = 200, NODE_H = 72;

const nodeSel = g.append("g").selectAll("g")
  .data(nodes).join("g")
  .attr("class", "node-group")
  .call(d3.drag()
    .on("start", (e, d) => {
      if (!e.active) sim.alphaTarget(0.15).restart();
      d.fx = d.x; d.fy = d.y;
    })
    .on("drag", (e, d) => { d.fx = e.x; d.fy = e.y; })
    .on("end", (e, d) => {
      if (!e.active) sim.alphaTarget(0);
      // keep pinned
    })
  )
  .on("mouseover", showTooltip)
  .on("mousemove", moveTooltip)
  .on("mouseout", hideTooltip);

nodeSel.append("rect")
  .attr("class", "node-rect")
  .attr("x", -NODE_W / 2).attr("y", -NODE_H / 2)
  .attr("width", NODE_W).attr("height", NODE_H)
  .attr("rx", 7)
  .attr("fill", d => nodeBg(d))
  .attr("stroke", d => nodeColor(d))
  .attr("stroke-opacity", 0.7);

nodeSel.append("text")
  .attr("class", "node-kind")
  .attr("x", -NODE_W / 2 + 8).attr("y", -NODE_H / 2 + 14)
  .text(d => d.kind);

nodeSel.append("text")
  .attr("class", "node-status")
  .attr("x", NODE_W / 2 - 8).attr("y", -NODE_H / 2 + 14)
  .attr("text-anchor", "end")
  .attr("fill", d => statusTextColor(d))
  .text(d => d.status === "pass_chosen" ? "★ CHOSEN" : d.status);

nodeSel.each(function(d) {
  const el = d3.select(this);
  const words = d.label.split(/\\s+/);
  let line = "", lines = [];
  for (const w of words) {
    const test = line ? line + " " + w : w;
    if (test.length > 26 && line) { lines.push(line); line = w; }
    else { line = test; }
  }
  if (line) lines.push(line);
  lines = lines.slice(0, 2);
  lines.forEach((ln, i) => {
    el.append("text")
      .attr("class", "node-label")
      .attr("x", 0).attr("y", (i - (lines.length - 1) / 2) * 15)
      .attr("text-anchor", "middle")
      .text(ln.length > 28 ? ln.slice(0, 26) + "\\u2026" : ln);
  });
});

nodeSel.append("text")
  .attr("class", "node-timing")
  .attr("x", 0).attr("y", NODE_H / 2 - 9)
  .attr("text-anchor", "middle")
  .text(d => {
    const a = d.attrs;
    if (a.seconds != null && a.saved_seconds != null)
      return `${(+a.seconds).toFixed(2)}s  saved ${(+a.saved_seconds).toFixed(2)}s`;
    if (a.seconds != null) return `${(+a.seconds).toFixed(2)}s`;
    if (a.score != null)   return `score ${(+a.score).toFixed(2)}`;
    return "";
  });

sim.on("tick", () => {
  linkSel
    .attr("x1", d => d.source.x)
    .attr("y1", d => d.source.y)
    .attr("x2", d => {
      const dx = d.target.x - d.source.x, dy = d.target.y - d.source.y;
      const dist = Math.sqrt(dx*dx + dy*dy) || 1;
      return d.target.x - (dx / dist) * (NODE_W / 2 + 10);
    })
    .attr("y2", d => {
      const dx = d.target.x - d.source.x, dy = d.target.y - d.source.y;
      const dist = Math.sqrt(dx*dx + dy*dy) || 1;
      return d.target.y - (dy / dist) * (NODE_H / 2 + 10);
    });

  linkLabelSel
    .attr("x", d => (d.source.x + d.target.x) / 2)
    .attr("y", d => (d.source.y + d.target.y) / 2 - 4);

  nodeSel.attr("transform", d => `translate(${d.x},${d.y})`);
});

const tooltip = document.getElementById("tooltip");

function fmtVal(v) {
  if (v === null || v === undefined) return "";
  if (typeof v === "number") return v.toFixed ? v.toFixed(4).replace(/\\.?0+$/, "") : String(v);
  return String(v);
}

function showTooltip(event, d) {
  const rows = Object.entries(d.attrs)
    .filter(([, v]) => v !== null && v !== "" && v !== undefined)
    .map(([k, v]) => {
      const val = fmtVal(v);
      const cell = val.length > 80
        ? `<td><pre>${escHtml(val)}</pre></td>`
        : `<td>${escHtml(val)}</td>`;
      return `<tr><th>${escHtml(k)}</th>${cell}</tr>`;
    }).join("");

  tooltip.innerHTML = `
    <div class="tt-kind">${escHtml(d.kind)}</div>
    <div class="tt-label">${escHtml(d.label)}</div>
    ${d.status ? `<div class="tt-status" style="color:${statusTextColor(d)}">${escHtml(d.status)}</div>` : ""}
    ${rows ? `<table>${rows}</table>` : ""}
  `;
  tooltip.style.display = "block";
  moveTooltip(event);
}

function moveTooltip(event) {
  const tw = tooltip.offsetWidth, th = tooltip.offsetHeight;
  const bw = window.innerWidth, bh = window.innerHeight;
  let x = event.clientX + 14, y = event.clientY + 14;
  if (x + tw > bw - 8) x = event.clientX - tw - 14;
  if (y + th > bh - 8) y = event.clientY - th - 14;
  tooltip.style.left = x + "px";
  tooltip.style.top  = y + "px";
}

function hideTooltip() { tooltip.style.display = "none"; }

function escHtml(s) {
  return String(s)
    .replace(/&/g,"&amp;").replace(/</g,"&lt;")
    .replace(/>/g,"&gt;").replace(/"/g,"&quot;");
}

document.getElementById("btn-reset").addEventListener("click", () => {
  svg.transition().duration(600).call(
    zoom.transform,
    d3.zoomIdentity.translate(dims().w / 2, dims().h / 2).scale(0.8)
      .translate(-dims().w / 2, -dims().h / 2)
  );
});

document.getElementById("btn-pin").addEventListener("click", () => {
  nodes.forEach(d => { d.fx = null; d.fy = null; });
  sim.alphaTarget(0.2).restart();
  setTimeout(() => sim.alphaTarget(0), 1200);
});

window.addEventListener("resize", () => {
  const {w, h} = dims();
  sim.force("center", d3.forceCenter(w / 2, h / 2))
     .force("x", d3.forceX(w / 2).strength(0.04))
     .force("y", d3.forceY(h / 2).strength(0.04));
});
</script>
</body>
</html>"""


def write_viz_html(path: str = "proof-search.html"):
    """Write an interactive D3.js force-directed HTML visualization of the proof search.

    Converts the internal _viz_nodes / _viz_links accumulator into the node/edge
    schema expected by the sorryskip-style visualization (rectangular nodes, arrows,
    Reset/Unpin controls, rich tooltips).
    """
    if not _viz_nodes:
        return

    # Map nicks node schema → sorryskip node schema
    # nicks:  {id, type, label, score, time, error_msg, pct_vs_baseline}
    # target: {id, kind, label, status, attrs:{score, seconds, pct_vs_baseline, error_msg}}
    out_nodes = []
    for n in _viz_nodes:
        ntype = n["type"]  # search_root | pass_chosen | pass_other | fail | banned
        kind = "search-root" if ntype == "search_root" else "candidate"
        attrs = {}
        if n.get("score") is not None:
            attrs["score"] = n["score"]
        if n.get("time") is not None:
            attrs["seconds"] = n["time"]
        if n.get("pct_vs_baseline") is not None:
            attrs["pct_vs_baseline"] = n["pct_vs_baseline"]
        if n.get("error_msg"):
            attrs["error"] = n["error_msg"]
        out_nodes.append({
            "id":     n["id"],
            "kind":   kind,
            "label":  n["label"],
            "status": ntype,
            "attrs":  attrs,
        })

    # Map nicks link schema → sorryskip edge schema
    # nicks:  {source, target, is_chosen}
    # target: {from, to, label, is_chosen}
    out_edges = []
    for lk in _viz_links:
        out_edges.append({
            "from":      lk["source"],
            "to":        lk["target"],
            "label":     "chosen" if lk.get("is_chosen") else "",
            "is_chosen": lk.get("is_chosen", False),
        })

    graph_data = json.dumps({"nodes": out_nodes, "edges": out_edges})
    meta = f"proof-search &bull; {len(out_nodes)} nodes &bull; {len(out_edges)} edges"
    html = _VIZ_HTML.replace("__GRAPH_DATA__", graph_data).replace("__META__", meta)
    with open(path, "w") as f:
        f.write(html)
    print(f"\n  Visualization written → {path}  ({len(out_nodes)} nodes, {len(out_edges)} edges)")


# ---------------------------------------------------------------------------
# Candidate application + fast testing (sorry-filling)
# ---------------------------------------------------------------------------

def apply_candidate(content, candidate):
    def replacer(m):
        indent = m.group(1)
        lines = candidate.split('\n')
        return '\n'.join(indent + line for line in lines)
    return SORRY_RE.sub(replacer, content, count=1)


def try_candidates_fast(file_path, original_content, candidates):
    """
    Try all candidates, collect every passing one, then return the one with
    the best proof_quality_score (structure over automation over speed).
    Prints an ASCII search tree summarising what was tried and what was chosen.
    """
    all_errors = []
    results = []
    passing = []  # (score, candidate_text, modified_content, result_dict)

    for candidate in candidates:
        short = candidate.replace('\n', ' ')[:60]

        if is_banned(candidate):
            results.append({'short': short, 'status': 'banned',
                            'score': float('inf'), 'compile_time': float('inf'), 'error_msg': ''})
            continue

        modified = apply_candidate(original_content, candidate)
        if modified == original_content:
            continue

        write_file(file_path, modified)
        passed, output = check_file_fast(file_path)

        if passed:
            t = measure_compile_time(file_path, modified)
            score = proof_quality_score(candidate, t)
            r = {'short': short, 'status': 'pass', 'score': score,
                 'compile_time': t, 'error_msg': ''}
            results.append(r)
            passing.append((score, candidate, modified, r))
        else:
            err_preview = re.search(r'error:.*', output)
            err_msg = err_preview.group()[:80] if err_preview else "unknown error"
            results.append({'short': short, 'status': 'fail', 'score': float('inf'),
                            'compile_time': float('inf'), 'error_msg': err_msg})
            all_errors.append(f"Candidate `{candidate[:40]}`: {err_msg}")

    if passing:
        passing.sort(key=lambda x: x[0])
        _, _, best_content, chosen_r = passing[0]
        write_file(file_path, best_content)
        _print_search_tree("Proof search", results, chosen=chosen_r)
        return best_content, None

    write_file(file_path, original_content)
    _print_search_tree("Proof search (all failed)", results)
    return None, "\n".join(all_errors)


# ---------------------------------------------------------------------------
# Sorry-filling loop (default mode)
# ---------------------------------------------------------------------------

def autoresearch_loop(max_iterations=20, target_file=None):
    mode = {"ollama": "Ollama (local)", "openai": "OpenAI",
            "anthropic": "Claude (Anthropic)"}.get(_backend, _backend)
    print(f"=== autoresearch [sorry-filling] [{mode}] ===")
    print("Strategy: fast file scan → lake env lean per candidate → one final lake build")

    total_closed = 0

    for iteration in range(max_iterations):
        sorry_files = find_sorry_files_by_scan(target_file)
        sorry_count = sum(sorry_files.values())

        print(f"\n--- Iteration {iteration + 1}/{max_iterations} "
              f"| {sorry_count} open sorries in {len(sorry_files)} file(s) ---")

        if sorry_count == 0:
            print("All sorries closed!")
            break

        made_progress = False

        for file_path, _ in sorry_files.items():
            content = read_file(file_path)
            remaining = len(SORRY_RE.findall(content))
            if remaining == 0:
                continue

            print(f"\n  File: {file_path}  ({remaining} sorries)")
            print("  Extracting proof goal...")
            goal_state = get_lean_goal_state(file_path, content)
            if goal_state:
                print(f"  Goal: {goal_state[:120].replace(chr(10), ' ')}")
            else:
                print("  Goal: (none extracted — term-mode or timeout)")

            error_feedback = None
            for attempt in range(3):
                print(f"  Candidates round {attempt + 1}...")
                candidates, reasoning = get_sorry_candidates(
                    file_path, content, goal_state, error_feedback
                )
                if not candidates:
                    print("  No candidates returned.")
                    break
                if reasoning:
                    print(f"  Reasoning: {reasoning[:100]}")

                winning_content, error_feedback = try_candidates_fast(
                    file_path, content, candidates
                )
                if winning_content is not None:
                    content = winning_content
                    total_closed += 1
                    made_progress = True
                    print(f"  [CLOSED] sorry in {file_path} (total: {total_closed})")
                    break

        if not made_progress:
            print("\nNo progress this iteration. Stopping early.")
            break

    print(f"\n=== Fast-check phase done. Sorries closed: {total_closed} ===")
    if total_closed > 0:
        print("Running final lake build to confirm...")
        report = build_and_measure()
        final_sorry_files = get_sorry_locations(report)
        if target_file:
            final_sorry_files = {k: v for k, v in final_sorry_files.items()
                                  if target_file in k}
        final_count = sum(final_sorry_files.values())
        print(f"Final build: {final_count} open sorries remaining")
    else:
        print("No sorries were closed — skipping final build.")
    write_viz_html()


# ---------------------------------------------------------------------------
# Speed-optimization loop (--optimize mode)
# ---------------------------------------------------------------------------

def optimize_loop(target_file):
    """
    Take a fully proved Lean file and try to reduce its compile time by
    replacing tactic proof blocks with faster alternatives.

    Strategy:
    1. Measure baseline compile time for the whole file.
    2. Find all `by` proof blocks.
    3. For each block: ask the LLM for faster alternatives, try each,
       keep the version that compiles fastest without errors.
    4. Report total time saved.
    """
    mode = {"ollama": "Ollama (local)", "openai": "OpenAI",
            "anthropic": "Claude (Anthropic)"}.get(_backend, _backend)
    print(f"=== autoresearch [--optimize] [{mode}] ===")
    print(f"Target: {target_file}\n")

    content = read_file(target_file)

    print("Measuring baseline compile time...")
    t0 = time.time()
    baseline_result = _lake_run(target_file, 300)
    baseline = time.time() - t0
    baseline_out = baseline_result.stderr + baseline_result.stdout
    baseline_errors = _parse_error_lines(baseline_out)

    if baseline_errors:
        print(f"  Note: {len(baseline_errors)} error line(s) at {sorted(baseline_errors)} — "
              f"blocks overlapping those lines will be skipped.")
    print(f"Baseline: {baseline:.2f}s\n")

    blocks = find_proof_blocks(content)
    sorry_count = sum(1 for b in blocks if SORRY_RE.search(b['proof_body']))
    error_count = sum(
        1 for b in blocks
        if not SORRY_RE.search(b['proof_body'])
        and any(b['proof_start'] <= ln - 1 <= b['proof_end'] for ln in baseline_errors)
    )
    complete = len(blocks) - sorry_count - error_count
    print(f"Found {len(blocks)} tactic proof blocks: "
          f"{complete} optimisable, {sorry_count} with sorry, "
          f"{error_count} overlapping errors (all skipped).\n")

    # Use declaration text as stable key so line numbers stay valid after replacements
    decl_keys = [b['declaration'] for b in blocks]

    current_content = content
    current_time = baseline
    total_time_saved = 0.0
    blocks_improved = 0

    for idx, decl_key in enumerate(decl_keys):
        # Re-parse to get fresh line numbers after any prior replacements
        fresh_blocks = find_proof_blocks(current_content)
        block = next((b for b in fresh_blocks if b['declaration'] == decl_key), None)
        if block is None:
            continue

        print(f"[{idx + 1}/{len(decl_keys)}] {block['declaration'][:70]}")
        print(f"  Current proof:\n    {block['proof_body'].strip()[:100]}")

        if SORRY_RE.search(block['proof_body']):
            print("  [SKIP] proof contains sorry — leaving as-is\n")
            continue

        block_lines = set(range(block['proof_start'], block['proof_end']))
        if block_lines & {ln - 1 for ln in baseline_errors}:
            print("  [SKIP] block overlaps a compile error — leaving as-is\n")
            continue

        candidates = get_opt_candidates(target_file, current_content, block)
        if not candidates:
            print("  No candidates returned.\n")
            continue

        orig_score = proof_quality_score(block['proof_body'], current_time)
        best_score = orig_score
        best_time = current_time
        best_content = current_content
        chosen_opt_r = None
        opt_results = []

        for candidate in candidates:
            short = candidate.replace('\n', ' ')[:60]

            if is_banned(candidate):
                opt_results.append({'short': short, 'status': 'banned',
                                    'score': float('inf'), 'compile_time': float('inf'),
                                    'error_msg': ''})
                continue

            target_indent = ' ' * (block['decl_indent'] + 2)
            indented = '\n'.join(
                (target_indent + line.lstrip()) if line.strip() else line
                for line in candidate.split('\n')
            )

            modified = replace_proof_block(current_content, block, indented)
            t = _measure_permissive(target_file, modified, baseline_errors)

            if t == float('inf'):
                opt_results.append({'short': short, 'status': 'fail',
                                    'score': float('inf'), 'compile_time': float('inf'),
                                    'error_msg': 'compile error'})
                continue

            score = proof_quality_score(candidate, t)
            pct_vs_base = (baseline - t) / baseline * 100 if baseline > 0 else 0
            r = {'short': short, 'status': 'pass', 'score': score,
                 'compile_time': t, 'error_msg': '', 'pct_vs_baseline': pct_vs_base}
            opt_results.append(r)

            if score < best_score:
                best_score = score
                best_time = t
                best_content = modified
                chosen_opt_r = r

        _print_search_tree(
            f"Opt: {block['declaration'][:52]}  (baseline {baseline:.2f}s)",
            opt_results,
            chosen=chosen_opt_r,
        )

        if best_content is not current_content:
            time_saved = current_time - best_time
            pct_faster = time_saved / current_time * 100 if current_time > 0 else 0
            total_time_saved += time_saved
            blocks_improved += 1
            current_content = best_content
            current_time = best_time
            write_file(target_file, current_content)
            print(
                f"  → Kept better proof  "
                f"score {orig_score:.2f} → {best_score:.2f}  |  "
                f"{baseline:.2f}s → {best_time:.2f}s  ({pct_faster:+.1f}%)\n"
            )
        else:
            write_file(target_file, current_content)
            print(f"  → No improvement found.\n")

    overall_pct = (total_time_saved / baseline * 100) if baseline > 0 else 0
    print("=" * 60)
    print(f"Blocks reviewed:   {len(decl_keys)}")
    print(f"Blocks improved:   {blocks_improved}")
    print(f"Baseline runtime:  {baseline:.2f}s")
    print(f"Final runtime:     {current_time:.2f}s")
    print(f"Time saved:        {total_time_saved:.2f}s  ({overall_pct:.1f}% faster)")
    write_viz_html()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    args = sys.argv[1:]
    optimize_mode = "--optimize" in args
    if "--local" in args:
        backend = "ollama"
    elif "--openai" in args:
        backend = "openai"
    else:
        backend = "anthropic"
    target = next((a for a in args if not a.startswith("--")), None)
    _setup_clients(backend)

    if optimize_mode:
        if not target:
            print("Usage: python scripts/autoresearch.py --optimize <file.lean>")
            sys.exit(1)
        # Resolve partial path to actual file
        candidates = glob.glob("Hackathon/**/*.lean", recursive=True)
        resolved = next((p for p in candidates if target in p), target)
        optimize_loop(resolved)
    else:
        autoresearch_loop(target_file=target)