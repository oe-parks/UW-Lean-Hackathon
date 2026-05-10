# scripts/autoresearch.py
import os
import subprocess
import json
import re
import sys
import time
import glob
import datetime
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


_VIZ_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Autoresearch — Proof Search Graph</title>
<style>
  *{box-sizing:border-box;margin:0;padding:0}
  body{background:#0d1117;color:#c9d1d9;font-family:'SF Mono','Fira Code',monospace;overflow:hidden}
  #hdr{
    padding:10px 18px;background:#161b22;border-bottom:1px solid #30363d;
    display:flex;align-items:center;gap:18px;position:fixed;width:100%;z-index:10;height:46px
  }
  #hdr h1{font-size:14px;font-weight:600;color:#f0f6fc;white-space:nowrap}
  #legend{display:flex;gap:12px;font-size:10px;flex-wrap:wrap}
  .leg{display:flex;align-items:center;gap:4px;color:#8b949e}
  .ld{width:10px;height:10px;border-radius:50%;flex-shrink:0}
  #cnt{font-size:10px;color:#484f58;margin-left:auto;white-space:nowrap}
  svg{position:fixed;top:46px;left:0;width:100vw;height:calc(100vh - 46px)}
  .lk{stroke-opacity:.35}
  .lk-c{stroke-opacity:.9}
  .node circle{stroke-width:2px;cursor:grab}
  .node circle:hover{filter:brightness(1.4)}
  .node text{font-size:10px;fill:#6e7681;pointer-events:none}
  #tip{
    position:fixed;pointer-events:none;display:none;
    background:#161b22;border:1px solid #30363d;border-radius:8px;
    padding:11px 14px;font-size:12px;max-width:360px;line-height:1.7;
    box-shadow:0 8px 32px rgba(0,0,0,.65);z-index:100
  }
  .tl{color:#f0f6fc;font-weight:600;margin-bottom:5px;word-break:break-all;font-size:13px}
  .tb{display:inline-block;padding:1px 6px;border-radius:10px;font-size:10px;margin-left:5px}
  .tr{color:#8b949e}.tr b{color:#c9d1d9;font-weight:normal}
  .te{color:#f85149;margin-top:4px;word-break:break-all}
  #hint{position:fixed;bottom:12px;right:14px;font-size:10px;color:#21262d}
</style>
</head>
<body>
<div id="hdr">
  <h1>🔍 Autoresearch — Proof Search</h1>
  <div id="legend">
    <div class="leg"><div class="ld" style="background:#f0883e"></div>Search root</div>
    <div class="leg"><div class="ld" style="background:#3fb950"></div>Chosen ★</div>
    <div class="leg"><div class="ld" style="background:#388bfd"></div>Passing</div>
    <div class="leg"><div class="ld" style="background:#f85149"></div>Failed</div>
    <div class="leg"><div class="ld" style="background:#30363d;border:1px solid #484f58"></div>Banned</div>
  </div>
  <div id="cnt"></div>
</div>
<svg id="viz"></svg>
<div id="tip"></div>
<div id="hint">scroll to zoom · drag canvas to pan · drag nodes</div>

<script src="https://d3js.org/d3.v7.min.js"></script>
<script>
const G = __GRAPH_DATA__;

const R = {search_root:22,pass_chosen:14,pass_other:11,fail:10,banned:8};
const C = {search_root:'#f0883e',pass_chosen:'#3fb950',pass_other:'#388bfd',fail:'#f85149',banned:'#1c2128'};
const S = {search_root:'#e08830',pass_chosen:'#56d364',pass_other:'#58a6ff',fail:'#ff7b72',banned:'#484f58'};
const BB= {search_root:'#3d1f00',pass_chosen:'#0f2d1a',pass_other:'#0d2040',fail:'#2d0e0e',banned:'#161b22'};

const nodes = G.nodes.map(d=>({...d}));
const links = G.links.map(d=>({...d}));

document.getElementById('cnt').textContent = nodes.length+' nodes · '+links.length+' edges';

const svg = d3.select('#viz');
const W = window.innerWidth, H = window.innerHeight - 46;
const g = svg.append('g');

svg.call(d3.zoom().scaleExtent([0.04,6]).on('zoom', e => g.attr('transform', e.transform)));

const sim = d3.forceSimulation(nodes)
  .force('link',    d3.forceLink(links).id(d=>d.id).distance(d=>d.is_chosen?90:125))
  .force('charge',  d3.forceManyBody().strength(-520))
  .force('center',  d3.forceCenter(W/2, H/2))
  .force('collide', d3.forceCollide(d=>R[d.type]+24));

const link = g.append('g').selectAll('line').data(links).join('line')
  .attr('class', d=>d.is_chosen?'lk-c':'lk')
  .attr('stroke', d=>d.is_chosen?'#3fb950':'#30363d')
  .attr('stroke-width', d=>d.is_chosen?2.5:1.2);

const node = g.append('g').selectAll('g').data(nodes).join('g').attr('class','node')
  .call(d3.drag()
    .on('start',(e,d)=>{if(!e.active)sim.alphaTarget(0.3).restart();d.fx=d.x;d.fy=d.y})
    .on('drag', (e,d)=>{d.fx=e.x;d.fy=e.y})
    .on('end',  (e,d)=>{if(!e.active)sim.alphaTarget(0);d.fx=null;d.fy=null})
  );

node.append('circle')
  .attr('r',      d=>R[d.type])
  .attr('fill',   d=>C[d.type])
  .attr('stroke', d=>S[d.type]);

node.filter(d=>d.type==='pass_chosen').append('text')
  .attr('text-anchor','middle').attr('dy','0.4em')
  .attr('font-size','11px').attr('fill','#0d1117').attr('pointer-events','none')
  .text('★');

node.append('text')
  .attr('dx', d=>R[d.type]+5).attr('dy','0.35em')
  .text(d=>d.label.length>46 ? d.label.slice(0,45)+'…' : d.label);

const tip = d3.select('#tip');
node.on('pointermove',(e,d)=>{
  const tl = d.type.replace('_',' ');
  let h = `<div class="tl">${d.label}<span class="tb" style="background:${BB[d.type]};color:${S[d.type]};border:1px solid ${S[d.type]}">${tl}</span></div>`;
  if(d.score!=null)   h+=`<div class="tr">quality score <b>${d.score.toFixed(2)}</b> <span style="font-size:10px;color:#484f58">(lower = better)</span></div>`;
  if(d.time!=null)    h+=`<div class="tr">compile time <b>${d.time.toFixed(2)}s</b></div>`;
  if(d.pct_vs_baseline!=null){
    const col = d.pct_vs_baseline>=0?'#3fb950':'#f85149';
    h+=`<div class="tr">vs baseline <b style="color:${col}">${d.pct_vs_baseline>=0?'+':''}${d.pct_vs_baseline.toFixed(1)}%</b></div>`;
  }
  if(d.error_msg) h+=`<div class="te">↳ ${d.error_msg}</div>`;
  tip.style('display','block')
     .style('left', Math.min(e.clientX+15, W-375)+'px')
     .style('top',  Math.min(e.clientY-10, H-210)+'px')
     .html(h);
}).on('pointerleave',()=>tip.style('display','none'));

sim.on('tick',()=>{
  link.attr('x1',d=>d.source.x).attr('y1',d=>d.source.y)
      .attr('x2',d=>d.target.x).attr('y2',d=>d.target.y);
  node.attr('transform',d=>`translate(${d.x},${d.y})`);
});
</script>
</body>
</html>"""


def write_viz_html(path: str = "proof-search.html"):
    """Write an interactive D3.js force-directed HTML visualization of the proof search."""
    if not _viz_nodes:
        return
    graph_data = json.dumps({"nodes": _viz_nodes, "links": _viz_links})
    html = _VIZ_HTML.replace("__GRAPH_DATA__", graph_data)
    with open(path, "w") as f:
        f.write(html)
    print(f"\n  Visualization written → {path}  ({len(_viz_nodes)} nodes, {len(_viz_links)} edges)")


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

    # Open log file
    os.makedirs("logs", exist_ok=True)
    stem = os.path.splitext(os.path.basename(target_file))[0]
    ts   = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    log_path = os.path.join("logs", f"optimize-{stem}-{ts}.md")
    log = open(log_path, "w")

    def _log(text: str):
        log.write(text)
        log.flush()

    _log(f"# Optimize log — `{target_file}`\n\n")
    _log(f"**Date:** {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  \n")
    _log(f"**Backend:** {mode}  \n\n---\n\n")

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

    _log(f"**Baseline:** {baseline:.2f}s")
    if baseline_errors:
        _log(f" *(file has errors at lines {sorted(baseline_errors)})*")
    _log(f"  \n**Blocks:** {len(blocks)} total — "
         f"{complete} optimisable, {sorry_count} sorry, {error_count} error  \n\n---\n\n")

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
            old_body = block['proof_body']
            current_content = best_content
            current_time = best_time
            write_file(target_file, current_content)
            print(
                f"  → Kept better proof  "
                f"score {orig_score:.2f} → {best_score:.2f}  |  "
                f"{baseline:.2f}s → {best_time:.2f}s  ({pct_faster:+.1f}%)\n"
            )
            # Write change to log
            new_body = find_proof_blocks(current_content)
            new_body_text = next(
                (b['proof_body'] for b in new_body if b['declaration'] == decl_key),
                chosen_opt_r['short'] if chosen_opt_r else "—"
            )
            _log(f"## [{blocks_improved}] `{decl_key[:80]}`\n\n")
            _log(f"**Score:** {orig_score:.2f} → {best_score:.2f}  \n")
            _log(f"**Time:** {baseline:.2f}s → {best_time:.2f}s ({pct_faster:+.1f}%)  \n\n")
            _log(f"**Before:**\n```lean\n{old_body.strip()}\n```\n\n")
            _log(f"**After:**\n```lean\n{new_body_text.strip()}\n```\n\n")
            # Why this proof was chosen
            if chosen_opt_r:
                others = [r for r in opt_results if r['status'] == 'pass' and r is not chosen_opt_r]
                _log(f"**Why chosen:** best quality score ({best_score:.2f}).  \n")
                if others:
                    _log("**Alternatives considered:**  \n")
                    for o in others:
                        qdiff = o['score'] - best_score
                        tdiff = best_time - o['compile_time']
                        _log(f"- `{o['short'][:60]}` — score {o['score']:.2f} "
                             f"({qdiff:+.2f} vs chosen), "
                             f"t={o['compile_time']:.2f}s ({tdiff:+.2f}s vs chosen)  \n")
            _log("\n---\n\n")
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

    _log(f"## Summary\n\n")
    _log(f"| | |\n|---|---|\n")
    _log(f"| Blocks reviewed | {len(decl_keys)} |\n")
    _log(f"| Blocks improved | {blocks_improved} |\n")
    _log(f"| Baseline runtime | {baseline:.2f}s |\n")
    _log(f"| Final runtime | {current_time:.2f}s |\n")
    _log(f"| Time saved | {total_time_saved:.2f}s ({overall_pct:.1f}% faster) |\n")
    log.close()
    print(f"Log written → {log_path}")

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