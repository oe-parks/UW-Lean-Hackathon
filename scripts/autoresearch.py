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

# Reject tactics that are not real proofs
CHEAT_RE = re.compile(
    r'\b(sorry|admit|native_decide|exact\?|apply\?|simp\?|decide\?|rw\?|assumption\?|norm_num\?)\b'
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
    Run `lake env lean <file>` from the nearest lakefile ancestor.
    Handles sub-projects (e.g. physlib-master) that have their own lakefile.
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
        capture_output=True, text=True, timeout=timeout, cwd=cwd,
    )


def _has_lean_error(output: str, returncode: int) -> bool:
    """True only for real compile failures. Sorry warnings are not errors."""
    return (
        returncode != 0
        or bool(re.search(r':\d+:\d+: error:', output))
        or bool(re.search(r'unsolved goals', output))
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

def is_cheat(candidate: str) -> bool:
    return bool(CHEAT_RE.search(candidate))


# ---------------------------------------------------------------------------
# LLM — sorry-filling
# ---------------------------------------------------------------------------

def _build_sorry_prompt(file_path, file_content, goal_state, error_feedback):
    system = (
        "You are a Lean 4 proof assistant specializing in graph theory and combinatorics (Mathlib).\n"
        "Your task: suggest tactics to close the first `sorry` in a Lean 4 file.\n\n"
        "Output ONLY valid JSON in this exact format:\n"
        '{"candidates": ["tactic1", "tactic2", ...], "reasoning": "..."}\n\n'
        "Rules:\n"
        "- Provide 3-5 candidates ordered most-to-least likely to work\n"
        "- Each candidate replaces one `sorry`; use \\n for multi-line tactics\n"
        "- Prefer: exact, simp, omega, decide, apply, constructor, intro, rfl\n"
        "- Do NOT use sorry, admit, exact?, apply?, simp?, or any ?-suffix search tactics\n"
        "- Do NOT invent Mathlib lemma names\n"
        "- Read the proof goal state carefully before guessing"
    )
    variable_parts = []
    if goal_state:
        variable_parts.append(f"Proof goal at first sorry:\n{goal_state}")
    if error_feedback:
        variable_parts.append(
            f"Previous candidates failed:\n{error_feedback[:600]}\n\n"
            "Suggest different approaches that avoid these errors."
        )
    variable_parts.append("Return JSON candidates to close the first `sorry`.")
    user = f"File: {file_path}\n\n{file_content}\n\n" + "\n\n".join(variable_parts)
    return system, user


def _build_speed_prompt(block, baseline_time):
    system = (
        "You are a Lean 4 proof optimization expert specializing in compilation speed.\n"
        "Suggest faster proof bodies that reduce Lean elaboration time.\n\n"
        "Output ONLY valid JSON:\n"
        '{"candidates": ["body1", "body2", ...], "reasoning": "..."}\n\n'
        "Speed rules (fastest to slowest):\n"
        "1. Term proofs over tactic proofs: `reach_adj e01` beats `by apply reach_adj; exact e01`\n"
        "2. `le_refl _` or `Nat.le_refl _` over `by simp` for trivial ≤ goals\n"
        "3. `simp only [x, y]` over bare `simp`\n"
        "4. `Nat.le_trans hw hnm` over `by omega` for simple inequalities\n"
        "5. `rw [lemma]` + `omega` over `simp [lemma]` + `omega`\n"
        "6. Direct `Walk.reverse_length w ▸ hw` over `by simp [Walk.reverse_length, hw]`\n\n"
        "Each candidate is the INDENTED PROOF BODY only — do NOT include `by` or the declaration. "
        "Use \\n for newlines. Match the indentation of the current proof."
    )
    variable_ctx = (
        f"Declaration to speed up (file compiles in {baseline_time:.1f}s):\n"
        f"```\n{block['declaration']}\n  by\n{block['proof_body']}\n```\n\n"
        "Suggest 3-5 faster proof bodies (proof body only, without `by`)."
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


def get_speed_candidates(file_path, file_content, block, baseline_time):
    system, variable_ctx = _build_speed_prompt(block, baseline_time)
    text = _call_llm(system, file_path, file_content, variable_ctx)
    return _parse_candidates(text)[0]  # just the candidates list


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
    all_errors = []
    for candidate in candidates:
        if is_cheat(candidate):
            print(f"    [CHEAT] rejected: {candidate[:60]!r}")
            continue
        modified = apply_candidate(original_content, candidate)
        if modified == original_content:
            continue
        write_file(file_path, modified)
        passed, output = check_file_fast(file_path)
        short = candidate.replace('\n', ' ')[:70]
        if passed:
            print(f"    [PASS] {short}")
            return modified, None
        else:
            err_preview = re.search(r'error:.*', output)
            err_msg = err_preview.group()[:80] if err_preview else "unknown error"
            print(f"    [FAIL] {short!r:.50} → {err_msg}")
            all_errors.append(f"Candidate `{candidate[:40]}`: {err_msg}")
    write_file(file_path, original_content)
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
    baseline = measure_compile_time(target_file, content)
    if baseline == float('inf'):
        print("ERROR: file has real compile errors. Fix them before optimizing.")
        return
    print(f"Baseline: {baseline:.2f}s\n")

    blocks = find_proof_blocks(content)
    sorry_count = sum(1 for b in blocks if SORRY_RE.search(b['proof_body']))
    complete = len(blocks) - sorry_count
    print(f"Found {len(blocks)} tactic proof blocks: {complete} complete, {sorry_count} with sorry (will skip).\n")

    # Use declaration text as stable key so line numbers stay valid after replacements
    decl_keys = [b['declaration'] for b in blocks]

    current_content = content
    current_time = baseline
    total_saved = 0.0

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

        candidates = get_speed_candidates(target_file, current_content, block, current_time)
        if not candidates:
            print("  No candidates returned.\n")
            continue

        best_time = current_time
        best_content = current_content

        for candidate in candidates:
            if is_cheat(candidate):
                print(f"    [CHEAT] rejected")
                continue

            # Apply indentation matching the declaration level
            target_indent = ' ' * (block['decl_indent'] + 2)
            indented = '\n'.join(
                (target_indent + line.lstrip()) if line.strip() else line
                for line in candidate.split('\n')
            )

            modified = replace_proof_block(current_content, block, indented)
            t = measure_compile_time(target_file, modified)

            short = candidate.replace('\n', ' ')[:60]
            if t == float('inf'):
                print(f"    [ERROR]  {short!r:.60}")
            elif t < best_time - 0.05:   # require >50ms improvement to count
                print(f"    [FASTER] {t:.2f}s (saved {best_time - t:.2f}s)  {short!r:.50}")
                best_time = t
                best_content = modified
            else:
                print(f"    [SAME]   {t:.2f}s  {short!r:.50}")

        if best_content is not current_content:
            current_content = best_content
            write_file(target_file, current_content)
            saved = current_time - best_time
            total_saved += saved
            current_time = best_time
            print(f"  → Kept faster proof. Saved {saved:.2f}s\n")
        else:
            write_file(target_file, current_content)   # restore (in case a candidate was written)
            print(f"  → No improvement found.\n")

    print("=" * 60)
    print(f"Baseline:  {baseline:.2f}s")
    print(f"Final:     {current_time:.2f}s")
    print(f"Saved:     {total_saved:.2f}s  ({100 * total_saved / baseline:.0f}% faster)")


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
