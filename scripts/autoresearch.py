# scripts/autoresearch.py
import subprocess
import json
import re
import sys
import anthropic
import openai as openai_lib

FAST_TIMEOUT = 45   # seconds for lake env lean single-file check
SORRY_RE = re.compile(r'^(\s*)sorry\b', re.MULTILINE)

# Backends: "anthropic" | "ollama" | "openai"
_backend = "anthropic"
_anthropic_client = None
_openai_client = None   # shared for both ollama and openai backends


def _setup_clients(backend: str):
    global _backend, _anthropic_client, _openai_client
    _backend = backend
    if backend == "ollama":
        _openai_client = openai_lib.OpenAI(
            base_url="http://localhost:11434/v1",
            api_key="ollama",   # required by sdk but ignored by ollama
        )
    elif backend == "openai":
        _openai_client = openai_lib.OpenAI()  # reads OPENAI_API_KEY from env
    else:
        _anthropic_client = anthropic.Anthropic()  # reads ANTHROPIC_API_KEY from env


def build_and_measure():
    subprocess.run(["./scripts/measure-build.sh"], capture_output=True, text=True)
    with open("build-report.json") as f:
        return json.load(f)


def get_sorry_locations(report):
    """Return project source files with open sorries (excludes .lake internals)."""
    sorry_files = report.get("sorry_per_file", {})
    return {
        path: count
        for path, count in sorry_files.items()
        if count > 0
        and "Hackathon/Untitled/.lake" not in path
        and path.startswith("Hackathon/")
    }


def read_file(path):
    with open(path) as f:
        return f.read()


def write_file(path, content):
    with open(path, "w") as f:
        f.write(content)


def find_first_tactic_sorry(content):
    """
    Return (char_offset, indent) for the first tactic-mode sorry.
    Tactic-mode: indented line whose stripped content starts with 'sorry'.
    Returns (None, None) if not found.
    """
    for m in SORRY_RE.finditer(content):
        indent = m.group(1)
        if indent:
            return m.start(), indent
    return None, None


def get_lean_goal_state(file_path, content):
    """
    Extract the proof goal at the first tactic-mode sorry.
    Temporarily inserts `trace_state` before the sorry, runs lake env lean,
    parses the information: output, then restores the file.
    Returns the goal string, or "" on failure.
    """
    start, indent = find_first_tactic_sorry(content)
    if start is None:
        return ""

    modified = content[:start] + f"{indent}trace_state\n" + content[start:]
    write_file(file_path, modified)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", file_path],
            capture_output=True, text=True, timeout=FAST_TIMEOUT
        )
        return _parse_goal_from_output(result.stderr + result.stdout)
    except subprocess.TimeoutExpired:
        return ""
    finally:
        write_file(file_path, content)


def _parse_goal_from_output(output):
    """Extract goal lines following an 'information:' marker in Lean output."""
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


def check_file_fast(file_path):
    """
    Run lake env lean on a single file for fast pre-validation.
    Returns (passed: bool, output: str).
    """
    try:
        result = subprocess.run(
            ["lake", "env", "lean", file_path],
            capture_output=True, text=True, timeout=FAST_TIMEOUT
        )
        output = result.stderr + result.stdout
        has_error = result.returncode != 0 or bool(re.search(r':\d+:\d+: error:', output))
        return not has_error, output
    except subprocess.TimeoutExpired:
        return False, "timeout"


def _build_prompt(file_path, file_content, goal_state, error_feedback):
    system = (
        "You are a Lean 4 proof assistant specializing in graph theory and combinatorics (Mathlib).\n"
        "Your task: suggest tactics to close the first `sorry` in a Lean 4 file.\n\n"
        "Output ONLY valid JSON in this exact format:\n"
        '{"candidates": ["tactic1", "tactic2", ...], "reasoning": "..."}\n\n'
        "Rules:\n"
        "- Provide 3-5 candidates ordered most-to-least likely to work\n"
        "- Each candidate replaces one `sorry`; use \\n for multi-line tactics\n"
        "- Prefer: exact, simp, omega, decide, apply, constructor, intro, rfl\n"
        "- Do NOT invent Mathlib lemma names; use exact? or apply? when uncertain\n"
        "- Read the proof goal state carefully before guessing"
    )

    variable_parts = []
    if goal_state:
        variable_parts.append(f"Proof goal at first sorry:\n{goal_state}")
    if error_feedback:
        variable_parts.append(
            f"Previous candidates failed with these errors:\n{error_feedback[:600]}\n\n"
            "Suggest different approaches that avoid these errors."
        )
    variable_parts.append("Return JSON candidates to close the first `sorry`.")

    user = f"File: {file_path}\n\n{file_content}\n\n" + "\n\n".join(variable_parts)
    return system, user


def _parse_candidates(text):
    json_match = re.search(r'\{[\s\S]*\}', text)
    if json_match:
        try:
            data = json.loads(json_match.group())
            return data.get("candidates", []), data.get("reasoning", "")
        except json.JSONDecodeError:
            pass
    return [text.strip()], ""


def get_candidates(file_path, file_content, goal_state, error_feedback=None):
    """
    Ask the configured LLM for multiple tactic candidates.
    Uses prompt caching when running against Anthropic; plain messages for Ollama.
    Returns (candidates: list[str], reasoning: str).
    """
    system, user = _build_prompt(file_path, file_content, goal_state, error_feedback)

    if _backend in ("ollama", "openai"):
        model = "qwen2.5-coder:7b" if _backend == "ollama" else "gpt-4o"
        response = _openai_client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": system},
                {"role": "user", "content": user},
            ],
            max_tokens=1024,
            temperature=0.2,
        )
        text = response.choices[0].message.content
    else:  # anthropic
        response = _anthropic_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=1024,
            system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral"}}],
            messages=[{
                "role": "user",
                "content": [
                    {"type": "text", "text": f"File: {file_path}\n\n{file_content}",
                     "cache_control": {"type": "ephemeral"}},
                    {"type": "text", "text": "\n\n".join(
                        ([f"Proof goal at first sorry:\n{goal_state}"] if goal_state else []) +
                        ([f"Previous candidates failed:\n{error_feedback[:600]}\nSuggest different approaches."]
                         if error_feedback else []) +
                        ["Return JSON candidates to close the first `sorry`."]
                    )}
                ]
            }]
        )
        text = response.content[0].text

    return _parse_candidates(text)


def apply_candidate(content, candidate):
    """Replace the first tactic-mode sorry with candidate (preserving indent)."""
    def replacer(m):
        indent = m.group(1)
        lines = candidate.split('\n')
        return '\n'.join(indent + line for line in lines)

    return SORRY_RE.sub(replacer, content, count=1)


def try_candidates_fast(file_path, original_content, candidates):
    """
    Try each candidate with a fast single-file check (lake env lean).
    Returns (winning_content, error_output).
    """
    all_errors = []
    for candidate in candidates:
        modified = apply_candidate(original_content, candidate)
        if modified == original_content:
            continue
        write_file(file_path, modified)
        passed, output = check_file_fast(file_path)
        if passed:
            short = candidate.replace('\n', ' ')[:70]
            print(f"    [PASS] fast check: {short}")
            return modified, None
        else:
            short = candidate.replace('\n', ' ')[:50]
            err_preview = re.search(r'error:.*', output)
            err_msg = err_preview.group()[:80] if err_preview else "unknown error"
            print(f"    [FAIL] {short!r:.50} → {err_msg}")
            all_errors.append(f"Candidate `{candidate[:40]}`: {err_msg}")

    write_file(file_path, original_content)
    return None, "\n".join(all_errors)


def autoresearch_loop(max_iterations=10, target_file=None):
    mode = {"ollama": "Ollama (local)", "openai": "OpenAI", "anthropic": "Claude (Anthropic)"}.get(_backend, _backend)
    print(f"=== autoresearch loop starting [{mode}] ===")

    for i in range(max_iterations):
        print(f"\n--- Iteration {i + 1}/{max_iterations} ---")

        report = build_and_measure()
        sorry_files = get_sorry_locations(report)

        if target_file:
            sorry_files = {k: v for k, v in sorry_files.items() if target_file in k}

        sorry_count = sum(sorry_files.values())
        print(f"Open sorries: {sorry_count}  ({len(sorry_files)} files)")

        if sorry_count == 0:
            print("All sorries closed!")
            break

        target = list(sorry_files.keys())[0]
        print(f"Target: {target}  ({sorry_files[target]} sorries)")
        content = read_file(target)

        print("  Extracting proof goal state...")
        goal_state = get_lean_goal_state(target, content)
        if goal_state:
            print(f"  Goal: {goal_state[:120].replace(chr(10), ' ')}")
        else:
            print("  Goal: (none extracted — term-mode or timeout)")

        error_feedback = None
        closed = False
        for attempt in range(3):
            print(f"  Requesting candidates (round {attempt + 1})...")
            candidates, reasoning = get_candidates(target, content, goal_state, error_feedback)
            if not candidates:
                print("  No candidates returned, stopping.")
                break

            if reasoning:
                print(f"  Reasoning: {reasoning[:100]}")

            winning_content, error_feedback = try_candidates_fast(target, content, candidates)

            if winning_content is not None:
                print("  Fast check passed. Running full build to confirm...")
                full_report = build_and_measure()
                new_sorry_files = get_sorry_locations(full_report)
                if target_file:
                    new_sorry_files = {k: v for k, v in new_sorry_files.items()
                                       if target_file in k}
                new_count = sum(new_sorry_files.values())
                delta = sorry_count - new_count
                if delta > 0:
                    print(f"  SUCCESS: closed {delta} sorry(s). Remaining: {new_count}")
                else:
                    print("  WARNING: fast check passed but full build shows no progress.")
                    print("           Restoring original content.")
                    write_file(target, content)
                closed = True
                break

        if not closed:
            print(f"  Exhausted all attempts for {target}. Moving on.")


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--local" in args:
        backend = "ollama"
    elif "--openai" in args:
        backend = "openai"
    else:
        backend = "anthropic"
    target = next((a for a in args if not a.startswith("--")), None)
    _setup_clients(backend)
    autoresearch_loop(target_file=target)
