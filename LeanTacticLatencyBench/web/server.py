#!/usr/bin/env python3
"""LeanTacticLatencyBench — web UI.

  python3 web/server.py --host 0.0.0.0 --port 8000

Routes:
  GET  /                          dashboard with all agent runs
  GET  /agents                    list of available agent scripts
  GET  /agents/<a>                summary of one run (per-problem table)
  GET  /agents/<a>/<problem>      per-problem trail (with --full transcripts)
  GET  /agent-flow/<name>         workflow diagram + system-prompt editor
  POST /api/agents/<name>/prompt  save edited system prompt (llm_* only)
  GET  /problems                  list of corpus problems
  GET  /run                       form to launch a new run
  POST /api/run                   launch (returns job_id JSON)
  GET  /jobs                      list of jobs
  GET  /jobs/<id>                 live status page
  GET  /api/jobs/<id>             JSON status
  GET  /api/jobs/<id>/log         SSE log stream
  GET  /api/jobs/<id>/feed        SSE structured event stream
  GET  /compare?a=&b=             side-by-side compare
  GET  /static/style.css          stylesheet

This server is **public-by-design** when bound to 0.0.0.0. It will
happily run agents (including LLM agents that spend your API key) on
behalf of anyone who can reach the port. Mitigations baked in:

  * MAX_CONCURRENT_JOBS = 1     — one bench at a time, period.
  * MAX_BUDGET_S = 600          — per-problem wall-clock cap.
  * ALLOW_LLM_AGENTS env var    — if "0", LLM agents are disabled in the UI.
  * No static-file fallback     — the API key file at <repo>/../api is
                                  unreachable from any URL the server
                                  recognises.
"""

import argparse
import html
import json
import os
import re
import shlex
import subprocess
import sys
import threading
import time
import urllib.parse
import uuid
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# ───────────────────────── Configuration ──────────────────────────────

PROJECT_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = PROJECT_ROOT / "scripts"
AGENTS_DIR = PROJECT_ROOT / "agents"
PROMPTS_DIR = AGENTS_DIR / "prompts"
PROBLEMS_DIR = PROJECT_ROOT / "Bench" / "AgentProblems"
RESULTS_DIR = PROJECT_ROOT / "results" / "agents"

MAX_CONCURRENT_JOBS = 1
MAX_BUDGET_S = 600.0
DEFAULT_BUDGET_S = 60.0
MAX_PROMPT_BYTES = 32 * 1024  # 32 KB cap on saved prompts

ALLOW_LLM_AGENTS = os.environ.get("ALLOW_LLM_AGENTS", "1") == "1"


# ───────────────────────── Job tracking ───────────────────────────────

JOBS: Dict[str, dict] = {}
JOBS_LOCK = threading.Lock()


def _new_job_id() -> str:
    return uuid.uuid4().hex[:12]


def running_count() -> int:
    with JOBS_LOCK:
        return sum(1 for j in JOBS.values() if j["status"] == "running")


def start_job(agent_name: str, budget_s: float, label: str,
              filter_substr: Optional[str]) -> Tuple[str, Optional[str]]:
    """Spawn the agent run as a background subprocess. Returns
    (job_id, error_or_none)."""
    if running_count() >= MAX_CONCURRENT_JOBS:
        return ("", "another job is already running; please wait")
    agent_path = AGENTS_DIR / f"{agent_name}.py"
    if not agent_path.is_file():
        return ("", f"unknown agent: {agent_name!r}")
    if not ALLOW_LLM_AGENTS and agent_name.startswith("llm_"):
        return ("", "LLM agents are disabled on this server "
                    "(set ALLOW_LLM_AGENTS=1 to enable)")

    budget_s = max(1.0, min(float(budget_s), MAX_BUDGET_S))
    job_id = _new_job_id()

    cmd = [
        sys.executable, str(SCRIPTS_DIR / "run_agent.py"),
        "--agent", str(agent_path),
        "--budget", str(budget_s),
    ]
    if label:
        cmd += ["--agent-name", label]
    if filter_substr:
        cmd += ["--filter", filter_substr]

    log: List[str] = []
    feed: List[dict] = []
    job = {
        "id": job_id,
        "agent": agent_name,
        "label": label or agent_name,
        "budget_s": budget_s,
        "filter": filter_substr or "",
        "started_at": time.time(),
        "ended_at": None,
        "status": "running",
        "exit_code": None,
        "log": log,
        "log_lock": threading.Lock(),
        "log_event": threading.Event(),
        "feed": feed,                          # structured events (live UI)
        "feed_lock": threading.Lock(),
        "feed_event": threading.Event(),
        # Synchronisation between runner and watcher: the runner sets
        # `proc_done` when the subprocess exits, the watcher does a
        # final scan and sets `watcher_done`, *then* the runner flips
        # status. This guarantees the last batch of attempt /
        # problem_end events lands in the feed before the JS sees
        # `status: done` and closes the EventSource.
        "proc_done_event": threading.Event(),
        "watcher_done_event": threading.Event(),
        "_pending_status": None,                # set by runner, applied by self
        "command": " ".join(shlex.quote(c) for c in cmd),
        "output_dir": str((RESULTS_DIR / (label or agent_name)).resolve()),
    }
    with JOBS_LOCK:
        JOBS[job_id] = job

    def _push_feed(kind: str, data: dict) -> None:
        ev = {"t": time.time() - job["started_at"], "kind": kind, "data": data}
        with job["feed_lock"]:
            job["feed"].append(ev)
        job["feed_event"].set()

    def _runner():
        try:
            proc = subprocess.Popen(
                cmd,
                cwd=PROJECT_ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )
            job["pid"] = proc.pid
            assert proc.stdout is not None
            for line in proc.stdout:
                line = line.rstrip("\n")
                with job["log_lock"]:
                    job["log"].append(line)
                job["log_event"].set()
                _push_feed("orchestrator_log", {"line": line})
            proc.wait()
            job["exit_code"] = proc.returncode
            job["_pending_status"] = "done" if proc.returncode == 0 else "failed"
        except Exception as e:
            err = f"server: subprocess error: {e}"
            with job["log_lock"]:
                job["log"].append(err)
            _push_feed("orchestrator_log", {"line": err})
            job["exit_code"] = -1
            job["_pending_status"] = "failed"
        finally:
            # Tell the watcher to do its final scan, then wait until
            # it confirms it has drained, before publishing status.
            job["proc_done_event"].set()
            job["watcher_done_event"].wait(timeout=5.0)
            job["status"] = job.get("_pending_status") or "failed"
            job["ended_at"] = time.time()
            job["log_event"].set()
            _push_feed("status", {"status": job["status"]})

    def _watcher():
        """Poll the agent's output dir; emit a structured feed event for every
        new attempt, every new problem dir, and every problem completion.

        This is what makes the per-tactic live view possible: agents write
        attempts.jsonl line-by-line as they go, and we tail those files."""
        out = Path(job["output_dir"])
        problem_lookup = _build_problem_lookup()  # name → {statement, …}
        seen_problems: set = set()
        seen_attempts: Dict[str, int] = {}
        seen_done: set = set()

        def _scan() -> None:
            if not out.exists():
                return
            for sub in sorted(out.iterdir()):
                if not sub.is_dir():
                    continue
                problem = sub.name
                if problem not in seen_problems:
                    seen_problems.add(problem)
                    info = problem_lookup.get(problem, {})
                    _push_feed("problem_start", {
                        "problem": problem,
                        "statement": info.get("statement", ""),
                        "difficulty": info.get("difficulty", ""),
                        "imports": info.get("imports", []),
                    })
                attempts_path = sub / "attempts.jsonl"
                if attempts_path.exists():
                    try:
                        lines = attempts_path.read_text().splitlines()
                    except OSError:
                        lines = []
                    seen = seen_attempts.get(problem, 0)
                    for line in lines[seen:]:
                        line = line.strip()
                        if not line:
                            continue
                        try:
                            rec = json.loads(line)
                        except Exception:
                            continue
                        norm = _normalize_attempt(rec)
                        norm["problem"] = problem
                        _push_feed("attempt", norm)
                    seen_attempts[problem] = len(lines)

                summary_path = sub / "summary.json"
                if problem not in seen_done and summary_path.exists():
                    try:
                        s = json.loads(summary_path.read_text())
                    except Exception:
                        s = None
                    if s is not None:
                        seen_done.add(problem)
                        _push_feed("problem_end", {
                            "problem": problem,
                            "claimed_solved": bool(s.get("claimed_solved")),
                            "winning_attempt": s.get("winning_attempt"),
                            "winning_tactic": s.get("winning_tactic"),
                            "n_attempts": s.get("attempts", 0),
                            "total_wall_s": s.get("total_wall_s"),
                            "tokens_in": s.get("total_input_tokens"),
                            "tokens_out": s.get("total_output_tokens"),
                        })

        # Poll while the subprocess is alive. Once it exits
        # (`proc_done_event`), do a few extra scans to catch any
        # straggling files that the agent flushed at the very end,
        # then signal the runner that the feed has been fully drained.
        while not job["proc_done_event"].is_set():
            try:
                _scan()
            except Exception as e:
                _push_feed("watcher_error", {"error": str(e)})
            time.sleep(0.25)
        # Drain pass: a few quick rescans so we don't miss the very
        # last summary.json/attempts.jsonl writes.
        for _ in range(3):
            try:
                _scan()
            except Exception:
                pass
            time.sleep(0.1)
        job["watcher_done_event"].set()

    threading.Thread(target=_runner, daemon=True).start()
    threading.Thread(target=_watcher, daemon=True).start()
    return (job_id, None)


# ───────────────────────── Feed-event helpers ────────────────────────

_PROBLEM_LOOKUP_CACHE: Optional[Dict[str, dict]] = None


def _build_problem_lookup() -> Dict[str, dict]:
    """Map theorem-name → problem JSON (statement, difficulty, …).
    Cached at module level."""
    global _PROBLEM_LOOKUP_CACHE
    if _PROBLEM_LOOKUP_CACHE is not None:
        return _PROBLEM_LOOKUP_CACHE
    out: Dict[str, dict] = {}
    if PROBLEMS_DIR.exists():
        for pf in PROBLEMS_DIR.glob("*.problem.json"):
            try:
                obj = json.loads(pf.read_text())
            except Exception:
                continue
            name = obj.get("name")
            if name:
                out[name] = obj
    _PROBLEM_LOOKUP_CACHE = out
    return out


def _normalize_attempt(rec: dict) -> dict:
    """Flatten compile substructure and tag with failure_kind +
    error_excerpt so the front-end doesn't have to."""
    rec = dict(rec)
    if "compile" in rec and isinstance(rec["compile"], dict):
        c = rec["compile"]
        rec["ok"] = c.get("ok", False)
        rec["elapsed_s"] = c.get("elapsed_s")
        rec["exit_code"] = c.get("exit_code")
        rec["stdout_head"] = c.get("stdout_head", "")
        rec["stderr_head"] = c.get("stderr_head", "")
        rec["timed_out"] = c.get("timed_out", False)
    blob = (rec.get("stderr_head") or "") + "\n" + (rec.get("stdout_head") or "")
    rec["failure_kind"] = "success" if rec.get("ok") else _classify(rec, blob)
    rec["error_excerpt"] = _first_error_line(blob)[:400]
    # Trim noisy fields the UI doesn't need.
    for k in ("stdout_head", "stderr_head", "exit_code"):
        rec.pop(k, None)
    return rec


# ───────────────────────── Helpers ────────────────────────────────────

def list_agents() -> List[str]:
    if not AGENTS_DIR.exists():
        return []
    out = sorted(p.stem for p in AGENTS_DIR.glob("*.py") if not p.name.startswith("_"))
    if not ALLOW_LLM_AGENTS:
        out = [a for a in out if not a.startswith("llm_")]
    return out


def list_problems() -> List[dict]:
    out = []
    if not PROBLEMS_DIR.exists():
        return out
    for p in sorted(PROBLEMS_DIR.glob("*.problem.json")):
        try:
            obj = json.loads(p.read_text())
            obj["__file__"] = p.name
            out.append(obj)
        except Exception:
            continue
    return out


def list_runs() -> List[dict]:
    out = []
    if not RESULTS_DIR.exists():
        return out
    for sub in sorted(RESULTS_DIR.iterdir()):
        run_path = sub / "agent_run.json"
        if not run_path.is_file():
            continue
        try:
            run = json.loads(run_path.read_text())
        except Exception:
            continue
        out.append({
            "label": sub.name,
            "agent_name": run.get("agent_name", sub.name),
            "n_problems": run.get("n_problems", 0),
            "n_verified": run.get("n_verified", 0),
            "solve_rate": run.get("solve_rate", 0.0),
            "n_lying": run.get("n_lying", 0),
            "results": run.get("results", []),
        })
    return out


def get_run(label: str) -> Optional[dict]:
    p = RESULTS_DIR / label / "agent_run.json"
    if not p.is_file():
        return None
    try:
        return json.loads(p.read_text())
    except Exception:
        return None


def get_profile(label: str) -> Optional[dict]:
    """Return profile_summary.json, regenerating it if missing."""
    p = RESULTS_DIR / label / "profile_summary.json"
    if not p.is_file():
        run_path = RESULTS_DIR / label / "agent_run.json"
        if not run_path.is_file():
            return None
        # Generate it via the script.
        try:
            subprocess.run(
                [sys.executable, str(SCRIPTS_DIR / "profile_agent_run.py"),
                 "--run", str(run_path), "--no-csv"],
                cwd=PROJECT_ROOT, capture_output=True, timeout=60,
            )
        except Exception:
            pass
    if p.is_file():
        try:
            return json.loads(p.read_text())
        except Exception:
            return None
    return None


def load_attempts(label: str, problem_name: str) -> List[dict]:
    p = RESULTS_DIR / label / problem_name / "attempts.jsonl"
    if not p.is_file():
        return []
    out = []
    for line in p.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            out.append(json.loads(line))
        except Exception:
            continue
    return out


def transcript_text(label: str, problem_name: str, fname: str) -> Optional[str]:
    """Read a transcripts/ file safely (no path traversal)."""
    base = (RESULTS_DIR / label / problem_name / "transcripts").resolve()
    target = (base / fname).resolve()
    try:
        target.relative_to(base)
    except ValueError:
        return None
    if not target.is_file():
        return None
    return target.read_text(errors="replace")


# ───────────────────────── Agent prompt I/O ──────────────────────────

# Conservative agent-name pattern. Used for both filesystem lookups
# (`agents/<name>.py`, `agents/prompts/<name>_default.txt`) and as a
# component of safe path resolution.
AGENT_NAME_RE = re.compile(r"\A[A-Za-z0-9_]{1,64}\Z")


def _is_valid_agent_name(name: str) -> bool:
    return bool(AGENT_NAME_RE.fullmatch(name))


def agent_prompt_path(agent_name: str) -> Optional[Path]:
    """Return the on-disk system-prompt path for `agent_name`, with strict
    validation (no path traversal, must live under PROMPTS_DIR).
    Returns None if the name is invalid."""
    if not _is_valid_agent_name(agent_name):
        return None
    candidate = (PROMPTS_DIR / f"{agent_name}_default.txt").resolve()
    try:
        candidate.relative_to(PROMPTS_DIR.resolve())
    except ValueError:
        return None
    return candidate


def read_agent_prompt(agent_name: str) -> Tuple[Optional[str], Optional[Path]]:
    """Read the current default prompt for an agent. Returns
    (text, path) or (None, None) if no prompt exists for that agent."""
    p = agent_prompt_path(agent_name)
    if p is None or not p.is_file():
        return (None, p)
    try:
        return (p.read_text(), p)
    except OSError:
        return (None, p)


def write_agent_prompt(agent_name: str, text: str) -> Tuple[bool, str]:
    """Atomically save a new prompt for the agent. Keeps a `.bak`
    of the previous version. Returns (ok, message)."""
    p = agent_prompt_path(agent_name)
    if p is None:
        return (False, f"invalid agent name: {agent_name!r}")
    if not agent_name.startswith("llm_"):
        return (False, "only llm_* agents have an editable system prompt")
    encoded = text.encode("utf-8")
    if len(encoded) > MAX_PROMPT_BYTES:
        return (False, f"prompt too large: {len(encoded)} bytes "
                       f"(cap {MAX_PROMPT_BYTES})")
    try:
        p.parent.mkdir(parents=True, exist_ok=True)
        if p.is_file():
            bak = p.with_suffix(p.suffix + ".bak")
            try:
                bak.write_bytes(p.read_bytes())
            except OSError:
                pass
        tmp = p.with_suffix(p.suffix + ".tmp")
        tmp.write_bytes(encoded)
        os.replace(tmp, p)
    except OSError as e:
        return (False, f"write failed: {e}")
    return (True, f"saved {len(encoded)} bytes to {p.name}")


def compare_runs(a_label: str, b_label: str) -> str:
    a_path = RESULTS_DIR / a_label / "agent_run.json"
    b_path = RESULTS_DIR / b_label / "agent_run.json"
    if not (a_path.is_file() and b_path.is_file()):
        return "(one of the runs is missing)"
    try:
        proc = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "compare_agents.py"),
             "--a", str(a_path), "--b", str(b_path)],
            cwd=PROJECT_ROOT, capture_output=True, text=True, timeout=60,
        )
        return (proc.stdout or "") + (proc.stderr or "")
    except Exception as e:
        return f"(compare failed: {e})"


# ───────────────────────── HTML rendering ─────────────────────────────

def page(title: str, body: str, *, sub_nav: str = "") -> str:
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>{html.escape(title)} — LeanTacticLatencyBench</title>
  <link rel="stylesheet" href="/static/style.css">
</head>
<body>
  <header>
    <div class="brand"><a href="/">LeanTacticLatencyBench</a></div>
    <nav>
      <a href="/">Dashboard</a>
      <a href="/run">Run</a>
      <a href="/agents">Agents</a>
      <a href="/problems">Corpus</a>
      <a href="/jobs">Jobs</a>
    </nav>
  </header>
  <div class="warning">
    Public server. Anyone reaching this URL can launch experiments.
    Concurrent jobs are capped at {MAX_CONCURRENT_JOBS}; per-problem
    budget is capped at {int(MAX_BUDGET_S)} s. LLM agents are
    {"<b>enabled</b> — they will spend the configured API key" if ALLOW_LLM_AGENTS else "<b>disabled</b>"}.
  </div>
  {sub_nav}
  <main>
    {body}
  </main>
  <footer>
    <small>LeanTacticLatencyBench &middot; project root: <code>{html.escape(str(PROJECT_ROOT))}</code></small>
  </footer>
</body>
</html>"""


def tag(t: str, body: str = "", **attrs) -> str:
    a = " ".join(f'{k.replace("_","-")}="{html.escape(str(v))}"' for k, v in attrs.items())
    if a:
        return f"<{t} {a}>{body}</{t}>"
    return f"<{t}>{body}</{t}>"


def render_dashboard() -> str:
    runs = list_runs()
    if not runs:
        rows = "<tr><td colspan='5'><i>no runs yet — head to <a href='/run'>Run</a></i></td></tr>"
    else:
        rows = ""
        for r in runs:
            rate_pct = f"{r['solve_rate']*100:.0f}%"
            rows += (
                f"<tr>"
                f"<td><a href='/agents/{html.escape(r['label'])}'>{html.escape(r['label'])}</a></td>"
                f"<td>{html.escape(r['agent_name'])}</td>"
                f"<td>{r['n_verified']} / {r['n_problems']}</td>"
                f"<td><div class='bar'><div style='width:{r['solve_rate']*100:.0f}%'></div></div> {rate_pct}</td>"
                f"<td>{r['n_lying']}</td>"
                f"</tr>"
            )
    body = f"""
<h1>Agent runs</h1>
<table>
<thead><tr><th>Label</th><th>Agent</th><th>Verified</th><th>Solve rate</th><th>Lying</th></tr></thead>
<tbody>{rows}</tbody>
</table>
<p><a class="btn" href="/run">Run a new agent →</a></p>
<h2>Quick compare</h2>
<form action="/compare" method="get" class="inline-form">
  <label>A <select name="a">{_run_options()}</select></label>
  <label>B <select name="b">{_run_options()}</select></label>
  <button>Compare</button>
</form>
"""
    return page("Dashboard", body)


def _run_options() -> str:
    return "".join(
        f"<option value='{html.escape(r['label'])}'>{html.escape(r['label'])}</option>"
        for r in list_runs()
    )


def render_agents_list() -> str:
    rows = ""
    for a in list_agents():
        is_llm = a.startswith("llm_")
        prompt_text, prompt_path = read_agent_prompt(a)
        if is_llm:
            if prompt_path is not None and prompt_path.is_file():
                rel = prompt_path.relative_to(PROJECT_ROOT)
                prompt_cell = (
                    f"<small><code>{html.escape(str(rel))}</code> "
                    f"<span class='dim'>({len(prompt_text or '')} chars)</span></small>"
                )
            else:
                prompt_cell = "<small class='dim'>(no default prompt yet)</small>"
        else:
            prompt_cell = "<small class='dim'>(no prompt — non-LLM agent)</small>"
        rows += (
            f"<tr>"
            f"<td><a href='/agent-flow/{html.escape(a)}'><code>{html.escape(a)}</code></a></td>"
            f"<td><small><code>agents/{html.escape(a)}.py</code></small></td>"
            f"<td>{prompt_cell}</td>"
            f"<td><a class='btn-secondary' href='/agent-flow/{html.escape(a)}'>"
            "View flow & edit prompt</a></td>"
            f"</tr>"
        )
    body = f"""
<h1>Available agents</h1>
<p>Agent scripts found under <code>agents/</code>. Click an agent to
see its reasoning workflow as a diagram, edit its system prompt, and
launch a run with the new prompt — all from the browser.</p>
<table>
<thead><tr><th>Agent</th><th>Script</th><th>Prompt</th><th>Edit</th></tr></thead>
<tbody>{rows}</tbody>
</table>
<p class="hint">
  Add your own agent by dropping a Python file under <code>agents/</code>
  that implements the <code>--problem PROB.json --workdir WD/</code>
  contract (see <code>baseline_decide.py</code>). For LLM agents, drop a
  default prompt at <code>agents/prompts/&lt;name&gt;_default.txt</code>
  and it will appear here for editing.
</p>
"""
    return page("Agents", body)


def render_problems_list() -> str:
    rows = ""
    for p in list_problems():
        rows += (
            f"<tr>"
            f"<td><code>{html.escape(p.get('__file__', ''))}</code></td>"
            f"<td>{html.escape(p.get('name', ''))}</td>"
            f"<td>{html.escape(p.get('difficulty', ''))}</td>"
            f"<td><pre>{html.escape(p.get('statement', ''))}</pre></td>"
            f"</tr>"
        )
    body = f"""
<h1>Problem corpus</h1>
<p>{len(list_problems())} problems in <code>Bench/AgentProblems/</code>.
The orchestrator will iterate over every <code>*.problem.json</code>
under that directory.</p>
<table>
<thead><tr><th>File</th><th>Name</th><th>Difficulty</th><th>Statement</th></tr></thead>
<tbody>{rows}</tbody>
</table>
"""
    return page("Corpus", body)


def render_agent_flow(agent_name: str, *, saved: str = "", error: str = "") -> str:
    """Show an SVG workflow diagram of how this agent reasons + a textarea
    for editing its system prompt (LLM agents only)."""
    if not _is_valid_agent_name(agent_name):
        return page("agent flow",
                    f"<p>Invalid agent name <code>{html.escape(agent_name)}</code>.</p>")
    script_path = AGENTS_DIR / f"{agent_name}.py"
    if not script_path.is_file():
        return page("agent flow",
                    f"<p>No such agent: <code>{html.escape(agent_name)}</code>.</p>")
    is_llm = agent_name.startswith("llm_")
    prompt_text, prompt_path = read_agent_prompt(agent_name)

    # ── Workflow SVG ────────────────────────────────────────────────
    # Nodes:
    #   problem.json (input) ──► system prompt + user msg ──► LLM ──►
    #   candidate proof ──► lake env lean ──► (ok? exit) | (fail? feed back)
    svg = _agent_flow_svg(is_llm)

    # ── Prompt editor ───────────────────────────────────────────────
    if is_llm:
        if prompt_path is None or not prompt_path.is_file():
            editor_section = (
                "<p class='dim'>No default prompt file found at "
                f"<code>agents/prompts/{html.escape(agent_name)}_default.txt</code>. "
                "Saving below will create it.</p>"
                f"<form method='post' action='/api/agents/{html.escape(agent_name)}/prompt' "
                "id='prompt-form'>"
                "<textarea name='prompt' rows='18' "
                f"maxlength='{MAX_PROMPT_BYTES}'></textarea>"
                "<div class='editor-actions'>"
                "<button type='submit'>Save prompt</button>"
                "<a class='btn-secondary' href='/run'>Run with this prompt →</a>"
                "</div></form>"
            )
        else:
            rel = prompt_path.relative_to(PROJECT_ROOT)
            editor_section = (
                "<p class='dim'>Editing <code>" + html.escape(str(rel)) + "</code>. "
                "Saving overwrites this file (a <code>.bak</code> copy of the "
                "previous version is kept). The prompt is loaded fresh on every "
                "<code>run_agent.py</code> invocation.</p>"
                f"<form method='post' action='/api/agents/{html.escape(agent_name)}/prompt' "
                "id='prompt-form'>"
                f"<textarea name='prompt' rows='18' maxlength='{MAX_PROMPT_BYTES}'>"
                f"{html.escape(prompt_text or '')}</textarea>"
                "<div class='editor-actions'>"
                "<button type='submit'>Save prompt</button>"
                f"<a class='btn-secondary' href='/run?agent={html.escape(agent_name)}'>"
                "Run with this prompt →</a>"
                "</div></form>"
            )
    else:
        editor_section = (
            "<p class='dim'>This agent is not LLM-backed — its candidate set "
            f"lives directly in <code>agents/{html.escape(agent_name)}.py</code>. "
            "Edit that file (or fork the agent) to change behavior. "
            "There is no prompt to edit here.</p>"
        )

    flash = ""
    if saved:
        flash = f"<div class='flash ok'>{html.escape(saved)}</div>"
    if error:
        flash = f"<div class='flash fail'>{html.escape(error)}</div>"

    body = f"""
<p><a href="/agents">← all agents</a></p>
<h1>Agent: <code>{html.escape(agent_name)}</code></h1>
<p class="dim">Script: <code>agents/{html.escape(agent_name)}.py</code></p>

<section class="card">
  <h2>How this agent reasons</h2>
  <p class="dim">
    Each round, the agent sees the theorem statement plus the prior round's
    Lean output and must propose the next candidate proof. The verifier
    feeds the result back in until either Lean compiles cleanly or the
    budget is exhausted.
  </p>
  <div class="flow-svg-wrap">{svg}</div>
</section>

<section class="card">
  <h2>System prompt</h2>
  {flash}
  {editor_section}
</section>

<script>
const form = document.getElementById("prompt-form");
if (form) {{
  form.addEventListener("submit", async function(e) {{
    e.preventDefault();
    const fd = new FormData(form);
    const params = new URLSearchParams();
    for (const [k, v] of fd.entries()) params.append(k, v);
    const res = await fetch(form.action, {{
      method: "POST",
      headers: {{"Content-Type": "application/x-www-form-urlencoded"}},
      body: params.toString(),
    }});
    const data = await res.json().catch(() => ({{}}));
    const flash = document.createElement("div");
    flash.className = "flash " + (data.ok ? "ok" : "fail");
    flash.textContent = data.ok
        ? ("Saved — " + (data.message || ""))
        : ("Save failed — " + (data.error || data.message || "unknown"));
    const old = form.parentElement.querySelector(".flash");
    if (old) old.remove();
    form.parentElement.insertBefore(flash, form);
  }});
}}
</script>
"""
    return page(f"agent: {agent_name}", body)


def _agent_flow_svg(is_llm: bool) -> str:
    """Inline SVG of the agent's reasoning loop. Boxes describe the data
    that flows along each edge so it's clear what the LLM sees and what
    Lean sees. Renders for both llm_* and baseline_* agents (the latter
    just substitutes 'tactic-pool walker' for 'LLM')."""
    brain_label = "LLM (chat completion)" if is_llm else "Tactic-pool walker"
    brain_sub = ("system prompt + user msg → next proof"
                 if is_llm else "iterates over a fixed list of candidates")
    user_msg_lines = [
        "USER MESSAGE",
        "• theorem statement",
        "• prior attempt's tactic",
        "• Lean error excerpt",
    ] if is_llm else [
        "PICK NEXT TACTIC",
        "• fixed candidate pool",
        "• skip already-tried",
    ]
    sys_box_visible = is_llm

    def _box(x, y, w, h, *, fill, stroke, label_lines, kind=""):
        rect = (f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="8" ry="8" '
                f'fill="{fill}" stroke="{stroke}" stroke-width="1.5"/>')
        text_y = y + 22
        texts = []
        for i, line in enumerate(label_lines):
            cls = "title" if i == 0 else "sub"
            texts.append(
                f'<text x="{x + w/2}" y="{text_y + i*16}" '
                f'text-anchor="middle" class="{cls}">{html.escape(line)}</text>'
            )
        return rect + "\n" + "\n".join(texts)

    # Layout — 720 × 520 viewBox.
    inputs = _box(20, 30, 200, 64, fill="#eef2ff", stroke="#6366f1",
                  label_lines=["INPUT", "problem.json", "imports + statement"])
    sys_prompt = _box(20, 130, 200, 64, fill="#fef3c7", stroke="#d97706",
                      label_lines=["SYSTEM PROMPT", "agents/prompts/…", "(editable below)"]) \
                 if sys_box_visible else ""
    user_msg = _box(20, 230, 200, 78, fill="#ecfeff", stroke="#0891b2",
                    label_lines=user_msg_lines)
    brain   = _box(260, 130, 200, 78, fill="#ede9fe", stroke="#7c3aed",
                   label_lines=["AGENT", brain_label, brain_sub])
    proof   = _box(260, 250, 200, 64, fill="#f0f9ff", stroke="#0284c7",
                   label_lines=["PROPOSED PROOF", "Lean code block",
                                "(extracted from reply)"])
    lean    = _box(500, 250, 200, 64, fill="#f0fdf4", stroke="#15803d",
                   label_lines=["lake env lean", "compile + #print axioms",
                                "verify against statement"])
    feedback = _box(500, 130, 200, 78, fill="#fef2f2", stroke="#b91c1c",
                    label_lines=["LEAN OUTPUT", "stdout / stderr",
                                 "errors → next round"])
    done = _box(500, 360, 200, 56, fill="#dcfce7", stroke="#15803d",
                label_lines=["✓ VERIFIED", "save proof.lean, exit"])

    # Arrows. We use a marker for the arrowhead.
    marker = (
        '<defs>'
        '<marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" '
        'markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
        '<path d="M 0 0 L 10 5 L 0 10 z" fill="#475569"/>'
        '</marker>'
        '</defs>'
    )

    def _line(x1, y1, x2, y2, *, dashed=False, label="", curve=""):
        d = "stroke-dasharray='4 4'" if dashed else ""
        if curve:
            path = (f'<path d="{curve}" fill="none" stroke="#475569" '
                    f'stroke-width="1.5" marker-end="url(#arr)" {d}/>')
        else:
            path = (f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
                    f'stroke="#475569" stroke-width="1.5" '
                    f'marker-end="url(#arr)" {d}/>')
        if label:
            mx, my = (x1 + x2) / 2, (y1 + y2) / 2 - 4
            path += (f'<text x="{mx}" y="{my}" text-anchor="middle" '
                     f'class="edge">{html.escape(label)}</text>')
        return path

    arrows = []
    if sys_box_visible:
        arrows.append(_line(120, 94, 120, 130))   # input → sys prompt
        arrows.append(_line(120, 194, 120, 230))  # sys prompt → user msg
    else:
        arrows.append(_line(120, 94, 120, 230))   # input → user msg
    arrows.append(_line(220, 269, 260, 169))      # user msg → brain
    arrows.append(_line(360, 208, 360, 250))      # brain → proof
    arrows.append(_line(460, 282, 500, 282))      # proof → lean
    arrows.append(_line(600, 250, 600, 208, label="fail",
                        curve="M 600 250 C 600 230, 600 220, 600 208"))
    arrows.append(_line(600, 314, 600, 360, label="ok"))
    # feedback loop: lean output → user msg
    arrows.append(_line(500, 169, 220, 269, dashed=True, label="error feedback",
                        curve="M 500 150 C 380 60, 220 60, 130 230"))

    boxes_svg = "\n".join([inputs, sys_prompt, user_msg, brain, proof,
                           lean, feedback, done])
    arrows_svg = "\n".join(arrows)
    return (
        '<svg viewBox="0 0 720 440" class="flow-svg" xmlns="http://www.w3.org/2000/svg">'
        + marker + boxes_svg + arrows_svg
        + '</svg>'
    )


def render_run_form(*, prefill_agent: str = "") -> str:
    agents = list_agents()
    agent_opts = "".join(
        f"<option value='{html.escape(a)}'"
        + (" selected" if a == prefill_agent else "") + ">"
        + html.escape(a) + "</option>"
        for a in agents
    )
    body = f"""
<h1>Launch a new agent run</h1>
<form action="/api/run" method="post" class="run-form" id="run-form">
  <label>Agent
    <select name="agent" id="agent-select">{agent_opts}</select>
  </label>
  <p class="hint" id="agent-flow-link"></p>
  <label>Label (output dir under <code>results/agents/</code>)
    <input name="label" placeholder="e.g. baseline_decide_v2" />
  </label>
  <label>Per-problem budget (seconds, max {int(MAX_BUDGET_S)})
    <input name="budget" type="number" min="1" max="{int(MAX_BUDGET_S)}" value="{int(DEFAULT_BUDGET_S)}" />
  </label>
  <label>Filter (substring; only matching problems run)
    <input name="filter" placeholder="optional: e.g. nat_mul" />
  </label>
  <p class="hint">Limits — concurrent jobs: {MAX_CONCURRENT_JOBS},
    max budget: {int(MAX_BUDGET_S)} s/problem,
    LLM agents: <b>{"enabled" if ALLOW_LLM_AGENTS else "disabled"}</b>.</p>
  <button type="submit">Run</button>
</form>
<script>
function refreshAgentFlowLink() {{
  const sel = document.getElementById("agent-select");
  const link = document.getElementById("agent-flow-link");
  const a = sel.value;
  link.innerHTML = "→ <a href='/agent-flow/" + encodeURIComponent(a)
    + "'>View workflow & edit prompt for <code>" + a + "</code></a>";
}}
document.getElementById("agent-select").addEventListener("change", refreshAgentFlowLink);
refreshAgentFlowLink();
</script>
<script>
document.getElementById("run-form").addEventListener("submit", async function(e) {{
  e.preventDefault();
  const fd = new FormData(this);
  const params = new URLSearchParams();
  for (const [k, v] of fd.entries()) params.append(k, v);
  const res = await fetch("/api/run", {{
    method: "POST",
    headers: {{"Content-Type": "application/x-www-form-urlencoded"}},
    body: params.toString(),
  }});
  const data = await res.json();
  if (data.job_id) {{
    window.location = "/jobs/" + encodeURIComponent(data.job_id);
  }} else {{
    alert("Could not start: " + (data.error || "unknown error"));
  }}
}});
</script>
"""
    return page("Run", body)


def render_run_summary(label: str) -> str:
    run = get_run(label)
    if run is None:
        return page("not found", f"<p>No run named <code>{html.escape(label)}</code>.</p>")
    profile = get_profile(label) or {}
    totals = profile.get("totals") or {}
    rows = ""
    for r in run.get("results", []):
        verdict = ("VERIFIED" if r.get("verified") else
                   ("LYING" if r.get("claimed_lying") else
                    ("UNSOLVED" if not r.get("claimed_solved") else "REJECTED")))
        cls = ("ok" if r.get("verified") else "fail")
        rows += (
            f"<tr class='{cls}'>"
            f"<td><a href='/agents/{html.escape(label)}/{html.escape(r['problem_name'])}'>"
            f"{html.escape(r['problem_name'])}</a></td>"
            f"<td>{r.get('agent_wall_s', 0):.2f} s</td>"
            f"<td>{r.get('n_attempts', 0)}</td>"
            f"<td>{verdict}</td>"
            f"<td><small>{html.escape((r.get('verdict') or {}).get('reason', '')[:120])}</small></td>"
            f"</tr>"
        )
    waste = totals.get("waste_s", 0.0)
    productive = totals.get("productive_s", 0.0)
    waste_ratio = totals.get("waste_ratio", 0.0)
    failure_kinds = profile.get("failure_kinds") or []
    fk_rows = ""
    for fk in failure_kinds:
        fk_rows += (f"<tr><td>{html.escape(fk['kind'])}</td>"
                    f"<td>{fk['count']}</td><td>{fk['total_s']:.2f} s</td></tr>")
    top_w = profile.get("top_wasted_tactics") or []
    top_rows = ""
    for t in top_w[:8]:
        top_rows += (f"<tr><td>{t['count']}</td><td>{t['total_s']:.2f} s</td>"
                     f"<td><code>{html.escape(t['tactic'][:200])}</code></td></tr>")
    body = f"""
<h1>{html.escape(label)}</h1>
<p>
  Agent: <b>{html.escape(run.get('agent_name', '?'))}</b> &middot;
  verified <b>{run.get('n_verified', 0)} / {run.get('n_problems', 0)}</b> &middot;
  budget {run.get('budget_s', '?')} s.
</p>

<h2>Profile totals</h2>
<table class="stats">
<tr><th>Total attempts</th><td>{totals.get('n_attempts', 0)}</td></tr>
<tr><th>Failed attempts</th><td>{totals.get('n_failed', 0)}</td></tr>
<tr><th>Productive seconds</th><td>{productive:.2f}</td></tr>
<tr><th>Wasted seconds</th><td>{waste:.2f}</td></tr>
<tr><th>Waste ratio</th><td>{waste_ratio*100:.1f}%</td></tr>
<tr><th>Wall-clock (sum)</th><td>{totals.get('wall_s', 0):.2f}</td></tr>
</table>

<h2>Per-problem</h2>
<table>
<thead><tr><th>Problem</th><th>Wall</th><th>Attempts</th><th>Verdict</th><th>Detail</th></tr></thead>
<tbody>{rows}</tbody>
</table>

<h2>Failure kinds</h2>
<table>
<thead><tr><th>Kind</th><th>Count</th><th>Total time</th></tr></thead>
<tbody>{fk_rows}</tbody>
</table>

<h2>Top wasted tactics</h2>
<table>
<thead><tr><th>Count</th><th>Total time</th><th>Tactic</th></tr></thead>
<tbody>{top_rows}</tbody>
</table>
"""
    return page(label, body)


def render_problem_trail(label: str, problem_name: str, full: bool) -> str:
    attempts = load_attempts(label, problem_name)
    if not attempts:
        return page("trail",
                    f"<p>No <code>attempts.jsonl</code> for "
                    f"<code>{html.escape(label)}/{html.escape(problem_name)}</code>.</p>")
    rows = ""
    for a in attempts:
        # normalize compile structure
        if "compile" in a and isinstance(a["compile"], dict):
            ok = a["compile"].get("ok", False)
            elapsed = a["compile"].get("elapsed_s")
            stderr_head = a["compile"].get("stderr_head", "") or a["compile"].get("stdout_head", "")
            compile_path = a["compile"].get("compile_path")
        else:
            ok = a.get("ok", False)
            elapsed = a.get("elapsed_s")
            stderr_head = a.get("stderr_head", "") or a.get("stdout_head", "")
            compile_path = None
        kind = "OK" if ok else _classify(a, stderr_head)
        cls = "ok" if ok else "fail"
        tactic_disp = (a.get("tactic") or "")[:300]
        err_disp = _first_error_line(stderr_head)[:300]
        idx = a.get("index", "?")
        t_since = a.get("t_since_start_s")
        t_disp = f"{t_since:.2f}" if isinstance(t_since, (int, float)) else "?"
        elapsed_disp = f"{elapsed:.3f}" if isinstance(elapsed, (int, float)) else "?"

        details_html = ""
        if full:
            for slot, fname in [("prompt", a.get("prompt_path")),
                                ("response", a.get("response_path")),
                                ("compile", compile_path)]:
                if not fname:
                    continue
                # fname is e.g. "transcripts/attempt_000.prompt.txt"
                fname_ = fname.replace("\\", "/")
                if "/" not in fname_:
                    continue
                txt = transcript_text(label, problem_name,
                                      fname_.split("/", 1)[-1])
                if txt is None:
                    continue
                details_html += (
                    f"<details><summary>{slot} ({html.escape(fname_)})</summary>"
                    f"<pre>{html.escape(txt)}</pre></details>"
                )

        rows += (
            f"<tr class='{cls}'>"
            f"<td>#{idx}</td>"
            f"<td>{t_disp} s</td>"
            f"<td>{elapsed_disp} s</td>"
            f"<td><span class='kind {cls}'>{html.escape(kind)}</span></td>"
            f"<td><code>{html.escape(tactic_disp)}</code><br>"
            f"<small class='dim'>{html.escape(err_disp)}</small>"
            f"{details_html}"
            f"</td>"
            f"</tr>"
        )

    full_link = (f"/agents/{html.escape(label)}/{html.escape(problem_name)}"
                 + ("" if full else "?full=1"))
    full_label = "Hide full transcripts" if full else "Show full transcripts (LLM agents only)"
    sys_prompt_path = (RESULTS_DIR / label / problem_name /
                       "transcripts" / "system_prompt.txt")
    sys_prompt_disp = ""
    if full and sys_prompt_path.is_file():
        sys_prompt_disp = (
            f"<details open><summary>system prompt</summary>"
            f"<pre>{html.escape(sys_prompt_path.read_text())}</pre></details>"
        )
    body = f"""
<p><a href="/agents/{html.escape(label)}">← back to {html.escape(label)}</a></p>
<h1>{html.escape(label)} / {html.escape(problem_name)}</h1>
<p><a class="btn" href="{full_link}">{full_label}</a></p>
{sys_prompt_disp}
<table class="trail">
<thead><tr><th>#</th><th>t since start</th><th>elapsed</th><th>kind</th><th>tactic / error / transcripts</th></tr></thead>
<tbody>{rows}</tbody>
</table>
"""
    return page(f"{label}/{problem_name}", body)


def _classify(rec: dict, stderr_head: str) -> str:
    if rec.get("api_error"):
        return "api_error"
    if rec.get("timed_out") or (rec.get("compile") or {}).get("timed_out"):
        return "timeout"
    blob = (stderr_head or "").lower()
    if "type mismatch" in blob:
        return "type_mismatch"
    if "unknown constant" in blob or "unknown identifier" in blob:
        return "unknown_identifier"
    if "reduction got stuck" in blob:
        return "decide_stuck"
    if "simp made no progress" in blob:
        return "simp_no_progress"
    if "unsolved goals" in blob:
        return "unsolved_goals"
    if "rfl' failed" in blob or "tactic `rfl` failed" in blob:
        return "rfl_failed"
    if "decide' proved" in blob and "is false" in blob:
        return "decide_proved_false"
    if "tactic" in blob and "failed" in blob:
        return "tactic_failed"
    return "compile_failed" if blob else "no_output"


def _first_error_line(blob: str) -> str:
    if not blob:
        return ""
    for line in blob.splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.search(r"\berror:\s*(.*)$", line)
        if m and m.group(1).strip():
            return m.group(1).strip()
    for line in blob.splitlines():
        line = line.strip()
        if not line:
            continue
        line = re.sub(r"^[^\s:]+\.lean:\d+:\d+:\s*", "", line)
        if len(line) > 4:
            return line
    return ""


def render_compare(a_label: str, b_label: str) -> str:
    if not a_label or not b_label:
        return page("compare",
                    "<p>Pick two runs from the dashboard's Quick compare form.</p>")
    out = compare_runs(a_label, b_label)
    body = f"""
<h1>Compare: {html.escape(a_label)} vs {html.escape(b_label)}</h1>
<pre class="compare-output">{html.escape(out)}</pre>
"""
    return page("Compare", body)


def render_jobs_list() -> str:
    with JOBS_LOCK:
        jobs = sorted(JOBS.values(), key=lambda j: -(j.get("started_at") or 0))
    rows = ""
    for j in jobs:
        elapsed = ((j.get("ended_at") or time.time()) - (j.get("started_at") or 0))
        rows += (
            f"<tr class='{j['status']}'>"
            f"<td><a href='/jobs/{j['id']}'>{j['id']}</a></td>"
            f"<td>{html.escape(j['label'])}</td>"
            f"<td>{j['status']}</td>"
            f"<td>{elapsed:.1f} s</td>"
            f"<td>{j.get('exit_code') if j.get('exit_code') is not None else ''}</td>"
            f"</tr>"
        )
    if not rows:
        rows = "<tr><td colspan='5'><i>no jobs yet</i></td></tr>"
    body = f"""
<h1>Jobs</h1>
<p>In-memory; cleared when the server restarts.</p>
<table>
<thead><tr><th>id</th><th>label</th><th>status</th><th>elapsed</th><th>exit</th></tr></thead>
<tbody>{rows}</tbody>
</table>
"""
    return page("Jobs", body)


def render_job_detail(job_id: str) -> str:
    with JOBS_LOCK:
        job = JOBS.get(job_id)
    if not job:
        return page("job not found", f"<p>No job <code>{html.escape(job_id)}</code>.</p>")
    body = f"""
<div class="job-header">
  <h1>Job <code>{html.escape(job_id)}</code></h1>
  <div class="job-meta">
    <span class="pill" id="status-pill">{html.escape(job['status'])}</span>
    <span>label <b>{html.escape(job['label'])}</b></span>
    <span>agent <b>{html.escape(job['agent'])}</b></span>
    <span>budget <b>{job['budget_s']} s/problem</b></span>
    <span>elapsed <b id="elapsed">0.0</b> s</span>
  </div>
  <p id="results-link" class="hidden">→ <a href="/agents/{html.escape(job['label'])}">View final results & profile</a></p>
</div>

<div class="live-grid">
  <section id="now-proving-wrap" class="card now-proving">
    <h2>Currently proving <small id="current-name" class="dim">(waiting for first problem…)</small></h2>
    <div id="current-meta" class="dim"></div>
    <pre id="current-statement" class="theorem hidden"></pre>
    <h3>Attempts <small id="attempts-counter" class="dim"></small></h3>
    <div id="attempts" class="attempts"></div>
  </section>

  <aside class="card completed-panel">
    <h2>Done <small id="done-counter" class="dim">(0)</small></h2>
    <div id="completed" class="completed-grid"></div>
  </aside>
</div>

<details class="card orchestrator-log-wrap">
  <summary>Orchestrator log</summary>
  <pre id="orch-log" class="log"></pre>
</details>

<script>
const jobId = {json.dumps(job_id)};
const startedAtMs = {int(job["started_at"] * 1000)};
const elapsedEl = document.getElementById("elapsed");
const statusPill = document.getElementById("status-pill");
const linkEl = document.getElementById("results-link");
const orchLog = document.getElementById("orch-log");
const currentNameEl = document.getElementById("current-name");
const currentMetaEl = document.getElementById("current-meta");
const currentStmtEl = document.getElementById("current-statement");
const attemptsEl = document.getElementById("attempts");
const attemptsCounterEl = document.getElementById("attempts-counter");
const completedEl = document.getElementById("completed");
const doneCounterEl = document.getElementById("done-counter");

let currentProblem = null;
let attemptsByProblem = {{}};
let endedProblems = new Set();

function fmtElapsed(s) {{ return (s ?? 0).toFixed(2); }}

setInterval(() => {{
  const isDone = statusPill.classList.contains("done") || statusPill.classList.contains("failed");
  if (!isDone) {{
    elapsedEl.textContent = ((Date.now() - startedAtMs) / 1000).toFixed(1);
  }}
}}, 200);

function setStatus(s) {{
  statusPill.textContent = s;
  statusPill.className = "pill " + s;
  if (s === "done" || s === "failed") {{
    linkEl.classList.remove("hidden");
  }}
}}
setStatus({json.dumps(job["status"])});

function renderAttempt(a) {{
  const cls = a.ok ? "ok" : (a.failure_kind === "timeout" ? "timeout" : "fail");
  const card = document.createElement("div");
  card.className = "attempt " + cls;
  const idx = a.index ?? "?";
  const elapsed = a.elapsed_s != null ? a.elapsed_s.toFixed(3) : "?";
  const since  = a.t_since_start_s != null ? a.t_since_start_s.toFixed(2) : "?";
  const tactic = (a.tactic || "<no tactic>").trim();
  const errExc = a.error_excerpt || "";
  const kind = a.ok ? "OK" : (a.failure_kind || "fail");
  card.innerHTML = `
    <div class="attempt-head">
      <span class="kind ${{cls}}">#${{idx}} · ${{kind}}</span>
      <span class="time">elapsed ${{elapsed}}s · t=${{since}}s</span>
    </div>
    <pre class="attempt-tactic"></pre>
    <pre class="attempt-err"></pre>`;
  card.querySelector(".attempt-tactic").textContent = tactic;
  if (errExc) card.querySelector(".attempt-err").textContent = errExc;
  return card;
}}

function showCurrent(problem) {{
  currentProblem = problem.problem;
  currentNameEl.textContent = problem.problem + (problem.difficulty ? "  ·  " + problem.difficulty : "");
  currentMetaEl.textContent = problem.imports && problem.imports.length
      ? "imports: " + problem.imports.join(", ")
      : "no imports";
  if (problem.statement) {{
    currentStmtEl.textContent = problem.statement;
    currentStmtEl.classList.remove("hidden");
  }} else {{
    currentStmtEl.classList.add("hidden");
  }}
  attemptsEl.innerHTML = "";
  attemptsCounterEl.textContent = "(0)";
}}

function appendAttempt(a) {{
  if (!attemptsByProblem[a.problem]) attemptsByProblem[a.problem] = [];
  attemptsByProblem[a.problem].push(a);
  if (currentProblem !== a.problem) return;
  attemptsEl.appendChild(renderAttempt(a));
  attemptsCounterEl.textContent = "(" + attemptsByProblem[a.problem].length + ")";
  // auto-scroll to bottom of attempts panel only
  attemptsEl.scrollTop = attemptsEl.scrollHeight;
}}

function pushCompleted(p) {{
  if (endedProblems.has(p.problem)) return;
  endedProblems.add(p.problem);
  doneCounterEl.textContent = "(" + endedProblems.size + ")";
  const item = document.createElement("div");
  item.className = "completed-item " + (p.claimed_solved ? "ok" : "fail");
  const winTac = p.winning_tactic ? p.winning_tactic.replace(/\\n/g, " ").slice(0, 80) : "";
  item.innerHTML = `
    <div class="completed-head">
      <span class="dot"></span>
      <strong></strong>
      <span class="time">${{(p.total_wall_s ?? 0).toFixed(2)}}s · ${{p.n_attempts ?? 0}}×</span>
    </div>
    <div class="completed-tactic"></div>`;
  item.querySelector("strong").textContent = p.problem;
  item.querySelector(".completed-tactic").textContent = winTac;
  completedEl.prepend(item);
}}

const evt = new EventSource("/api/jobs/" + encodeURIComponent(jobId) + "/feed");
evt.addEventListener("orchestrator_log", e => {{
  const data = JSON.parse(e.data);
  orchLog.textContent += data.line + "\\n";
  orchLog.scrollTop = orchLog.scrollHeight;
}});
evt.addEventListener("problem_start", e => {{
  showCurrent(JSON.parse(e.data));
}});
evt.addEventListener("attempt", e => {{
  appendAttempt(JSON.parse(e.data));
}});
evt.addEventListener("problem_end", e => {{
  pushCompleted(JSON.parse(e.data));
}});
evt.addEventListener("status", e => {{
  setStatus(JSON.parse(e.data).status);
  if (statusPill.classList.contains("done") || statusPill.classList.contains("failed")) {{
    evt.close();
  }}
}});
evt.onerror = () => {{ /* let the browser retry */ }};
</script>
"""
    return page(f"job {job_id}", body)


# ───────────────────────── HTTP handler ───────────────────────────────

CSS = """
:root {
  --bg: #f8f9fb; --fg: #1c1c1e; --muted: #5f6168;
  --accent: #2563eb; --accent-fg: #fff;
  --ok: #15803d; --fail: #b91c1c; --warn: #92400e;
  --card: #fff; --border: #e5e7eb;
}
* { box-sizing: border-box; }
body { margin: 0; font: 14px/1.5 system-ui, -apple-system, Segoe UI, sans-serif;
  background: var(--bg); color: var(--fg); }
header { display: flex; align-items: center; justify-content: space-between;
  padding: 14px 24px; border-bottom: 1px solid var(--border); background: #fff; }
header .brand a { color: var(--fg); font-weight: 700; text-decoration: none; }
header nav a { margin-left: 18px; color: var(--accent); text-decoration: none; }
header nav a:hover { text-decoration: underline; }
.warning { background: #fff7ed; border-bottom: 1px solid #fed7aa;
  padding: 8px 24px; color: var(--warn); font-size: 13px; }
main { padding: 24px; max-width: 1100px; margin: 0 auto; }
footer { padding: 18px 24px; color: var(--muted); border-top: 1px solid var(--border); }
h1 { margin-top: 0; }
h2 { margin-top: 32px; }
table { border-collapse: collapse; width: 100%; background: var(--card); }
th, td { text-align: left; padding: 8px 12px; border-bottom: 1px solid var(--border);
  vertical-align: top; }
th { background: #fafafa; font-weight: 600; }
tr.ok td { background: #f0fdf4; }
tr.fail td { background: #fef2f2; }
tr.running td { background: #fef9c3; }
tr.done td { background: #f0fdf4; }
tr.failed td { background: #fef2f2; }
table.stats th { width: 220px; background: #fafafa; }
table.trail td { font-size: 13px; }
.kind { padding: 2px 8px; border-radius: 4px; background: #fee2e2;
  color: var(--fail); font-size: 12px; font-weight: 600; }
.kind.ok { background: #dcfce7; color: var(--ok); }
.bar { display: inline-block; width: 90px; height: 10px; background: #e5e7eb;
  border-radius: 5px; overflow: hidden; vertical-align: middle; }
.bar > div { height: 100%; background: var(--accent); }
code, pre { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; }
pre { background: #fff; border: 1px solid var(--border); border-radius: 6px;
  padding: 12px; overflow-x: auto; white-space: pre-wrap; word-break: break-word; }
.log { height: 480px; overflow-y: auto; background: #0f172a; color: #e2e8f0;
  border: none; }
.compare-output { background: #fff; }
.btn, button { background: var(--accent); color: var(--accent-fg);
  text-decoration: none; padding: 8px 16px; border-radius: 6px;
  border: 0; font: inherit; cursor: pointer; display: inline-block; }
.btn:hover, button:hover { filter: brightness(0.95); }
.run-form, .inline-form { display: grid; gap: 12px; max-width: 540px;
  background: var(--card); padding: 18px; border: 1px solid var(--border);
  border-radius: 8px; }
.run-form label, .inline-form label { display: grid; gap: 4px; font-weight: 500; }
.run-form input, .run-form select, .inline-form select {
  padding: 8px 10px; border: 1px solid var(--border); border-radius: 6px;
  font: inherit; background: #fff; }
.inline-form { display: flex; gap: 12px; align-items: end; flex-wrap: wrap; }
.inline-form label { flex: 0 0 220px; }
.hint { color: var(--muted); font-size: 12px; }
.hidden { display: none; }
.dim { color: var(--muted); }
details { margin-top: 6px; padding: 4px 0; }
details summary { cursor: pointer; color: var(--accent); font-size: 12px; }
details pre { font-size: 12px; max-height: 360px; overflow-y: auto; }

/* ── job detail / live UI ─────────────────────────────────────── */
.card { background: var(--card); border: 1px solid var(--border);
  border-radius: 8px; padding: 16px 20px; margin-top: 16px; }
.job-header { background: #fff; border: 1px solid var(--border);
  border-radius: 8px; padding: 16px 20px; margin-bottom: 8px; }
.job-header h1 { margin: 0 0 8px 0; }
.job-meta { display: flex; flex-wrap: wrap; gap: 18px; align-items: center;
  font-size: 13px; color: var(--muted); }
.pill { display: inline-block; padding: 4px 12px; border-radius: 999px;
  background: #fef9c3; color: #92400e; font-weight: 600; font-size: 12px;
  text-transform: uppercase; letter-spacing: 0.04em; }
.pill.running { background: #fef9c3; color: #92400e; }
.pill.done { background: #dcfce7; color: var(--ok); }
.pill.failed { background: #fee2e2; color: var(--fail); }

.live-grid { display: grid; grid-template-columns: minmax(0, 2fr) minmax(0, 1fr);
  gap: 16px; align-items: start; }
@media (max-width: 920px) { .live-grid { grid-template-columns: 1fr; } }

.now-proving h2 { margin-top: 0; }
.now-proving h3 { margin: 16px 0 8px 0; font-size: 14px; }
.theorem { background: #f1f5f9; border: 1px solid #cbd5e1;
  border-left: 4px solid var(--accent); color: #0f172a;
  padding: 12px 14px; border-radius: 6px; font-size: 13px;
  white-space: pre-wrap; word-break: break-word; }

.attempts { display: flex; flex-direction: column; gap: 10px;
  max-height: 540px; overflow-y: auto; padding-right: 4px; }
.attempt { border: 1px solid var(--border); border-radius: 6px;
  padding: 10px 12px; background: #fafafa; }
.attempt.ok { border-left: 4px solid var(--ok); background: #f0fdf4; }
.attempt.fail { border-left: 4px solid var(--fail); background: #fef2f2; }
.attempt.timeout { border-left: 4px solid var(--warn); background: #fff7ed; }
.attempt-head { display: flex; justify-content: space-between;
  align-items: center; font-size: 12px; }
.attempt-head .kind { padding: 2px 8px; border-radius: 4px;
  background: #fee2e2; color: var(--fail); font-weight: 600; }
.attempt-head .kind.ok { background: #dcfce7; color: var(--ok); }
.attempt-head .kind.timeout { background: #fef3c7; color: var(--warn); }
.attempt-head .time { color: var(--muted); font-family: ui-monospace, monospace; }
.attempt-tactic { font-family: ui-monospace, monospace; font-size: 12px;
  background: #fff; border: 1px solid var(--border); border-radius: 4px;
  padding: 8px 10px; margin: 8px 0 4px 0; white-space: pre-wrap;
  word-break: break-word; max-height: 200px; overflow-y: auto; }
.attempt-err { font-family: ui-monospace, monospace; font-size: 11px;
  color: #7f1d1d; background: #fef2f2; border-radius: 4px;
  padding: 6px 8px; margin: 0; white-space: pre-wrap; word-break: break-word;
  max-height: 80px; overflow-y: auto; }
.attempt-err:empty { display: none; }

.completed-panel h2 { margin-top: 0; }
.completed-grid { display: flex; flex-direction: column; gap: 8px;
  max-height: 720px; overflow-y: auto; }
.completed-item { border: 1px solid var(--border); border-radius: 6px;
  padding: 8px 10px; background: #fafafa; font-size: 12px; }
.completed-item.ok { border-left: 4px solid var(--ok); background: #f0fdf4; }
.completed-item.fail { border-left: 4px solid var(--fail); background: #fef2f2; }
.completed-head { display: flex; align-items: center; gap: 8px;
  justify-content: space-between; }
.completed-head strong { font-family: ui-monospace, monospace; font-size: 12px;
  flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.completed-head .dot { width: 8px; height: 8px; border-radius: 50%;
  background: var(--ok); flex: 0 0 8px; }
.completed-item.fail .dot { background: var(--fail); }
.completed-head .time { color: var(--muted); font-family: ui-monospace, monospace;
  font-size: 11px; flex: 0 0 auto; }
.completed-tactic { font-family: ui-monospace, monospace; font-size: 11px;
  color: var(--muted); margin-top: 4px; overflow: hidden;
  text-overflow: ellipsis; white-space: nowrap; }

.orchestrator-log-wrap summary { color: var(--accent);
  font-size: 13px; padding: 6px 0; }
.orchestrator-log-wrap .log { margin-top: 8px; max-height: 240px; }

/* ── agent flow + prompt editor ──────────────────────────────── */
.flow-svg-wrap { background: #fff; border: 1px solid var(--border);
  border-radius: 8px; padding: 12px; overflow-x: auto; }
.flow-svg { width: 100%; max-width: 760px; height: auto; display: block;
  margin: 0 auto; }
.flow-svg text { font: 11px ui-monospace, SFMono-Regular, Menlo, monospace;
  fill: #1c1c1e; }
.flow-svg text.title { font-weight: 700; font-size: 12px; }
.flow-svg text.sub { fill: #475569; font-size: 10px; }
.flow-svg text.edge { fill: #475569; font-size: 10px;
  font-family: system-ui, sans-serif; font-style: italic; }

textarea { width: 100%; font: 13px/1.5 ui-monospace, SFMono-Regular,
  Menlo, monospace; padding: 12px; border: 1px solid var(--border);
  border-radius: 6px; background: #fff; resize: vertical; min-height: 280px; }
.editor-actions { display: flex; gap: 12px; align-items: center;
  margin-top: 12px; }
.btn-secondary { background: #fff; color: var(--accent);
  border: 1px solid var(--accent); padding: 7px 15px; border-radius: 6px;
  text-decoration: none; font: inherit; cursor: pointer; }
.btn-secondary:hover { background: #eff6ff; }
.flash { padding: 10px 14px; border-radius: 6px; margin-bottom: 12px;
  font-weight: 500; }
.flash.ok { background: #dcfce7; color: var(--ok);
  border: 1px solid #86efac; }
.flash.fail { background: #fee2e2; color: var(--fail);
  border: 1px solid #fca5a5; }
"""


class Handler(BaseHTTPRequestHandler):
    server_version = "LeanTacticLatencyBenchWeb/1.0"

    def log_message(self, fmt, *args):
        sys.stderr.write("%s - - [%s] %s\n" %
                         (self.address_string(), self.log_date_time_string(),
                          fmt % args))

    def _write(self, status: int, body: bytes, ctype: str = "text/html; charset=utf-8") -> None:
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _write_html(self, status: int, body: str) -> None:
        self._write(status, body.encode("utf-8"))

    def _write_json(self, status: int, obj) -> None:
        self._write(status, json.dumps(obj).encode("utf-8"),
                    ctype="application/json")

    # ─── Routing ────────────────────────────────────────────────────
    def do_GET(self):
        url = urllib.parse.urlparse(self.path)
        parts = [p for p in url.path.split("/") if p]
        qs = urllib.parse.parse_qs(url.query)

        try:
            if not parts:
                return self._write_html(200, render_dashboard())
            if parts == ["static", "style.css"]:
                return self._write(200, CSS.encode("utf-8"),
                                   ctype="text/css; charset=utf-8")
            if parts == ["agents"]:
                return self._write_html(200, render_agents_list())
            if parts == ["problems"]:
                return self._write_html(200, render_problems_list())
            if parts == ["run"]:
                prefill = qs.get("agent", [""])[0]
                return self._write_html(200, render_run_form(prefill_agent=prefill))
            if len(parts) == 2 and parts[0] == "agent-flow":
                return self._write_html(200, render_agent_flow(parts[1]))
            if parts == ["compare"]:
                a = qs.get("a", [""])[0]
                b = qs.get("b", [""])[0]
                return self._write_html(200, render_compare(a, b))
            if parts == ["jobs"]:
                return self._write_html(200, render_jobs_list())
            if len(parts) == 2 and parts[0] == "jobs":
                return self._write_html(200, render_job_detail(parts[1]))
            if len(parts) == 3 and parts[:2] == ["api", "jobs"]:
                return self._write_json(200, _job_status(parts[2]))
            if len(parts) == 4 and parts[:2] == ["api", "jobs"] and parts[3] == "log":
                return self._stream_job_log(parts[2])
            if len(parts) == 4 and parts[:2] == ["api", "jobs"] and parts[3] == "feed":
                return self._stream_job_feed(parts[2])
            if len(parts) == 2 and parts[0] == "agents":
                return self._write_html(200, render_run_summary(parts[1]))
            if len(parts) == 3 and parts[0] == "agents":
                full = qs.get("full", ["0"])[0] not in ("", "0", "false")
                return self._write_html(200,
                    render_problem_trail(parts[1], parts[2], full))
            return self._write_html(404, page("404",
                f"<h1>404</h1><p>no route for <code>{html.escape(self.path)}</code></p>"))
        except Exception as e:
            sys.stderr.write(f"server error on GET {self.path}: {e}\n")
            return self._write_html(500,
                page("server error",
                     f"<h1>server error</h1><pre>{html.escape(str(e))}</pre>"))

    def do_POST(self):
        url = urllib.parse.urlparse(self.path)
        if url.path == "/api/run":
            return self._handle_post_run()
        # /api/agents/<name>/prompt
        parts = [p for p in url.path.split("/") if p]
        if (len(parts) == 4 and parts[0] == "api" and parts[1] == "agents"
                and parts[3] == "prompt"):
            return self._handle_post_prompt(parts[2])
        return self._write_json(404, {"error": "not found"})

    def _handle_post_prompt(self, agent_name: str) -> None:
        """Save a new system prompt for `agent_name`. Path-traversal safe;
        only allows llm_* agents; size-capped at MAX_PROMPT_BYTES."""
        if not _is_valid_agent_name(agent_name):
            return self._write_json(400, {"error": "invalid agent name"})
        try:
            length = int(self.headers.get("Content-Length", "0"))
            if length > MAX_PROMPT_BYTES + 4096:
                return self._write_json(413, {"error": "request too large"})
            raw = self.rfile.read(length).decode("utf-8")
            ctype = (self.headers.get("Content-Type") or "").lower()
            if "application/json" in ctype:
                obj = json.loads(raw)
                text = obj.get("prompt", "")
            else:
                params = urllib.parse.parse_qs(raw, keep_blank_values=True)
                text = (params.get("prompt") or [""])[0]
        except Exception as e:
            return self._write_json(400, {"error": f"bad request: {e}"})

        ok, msg = write_agent_prompt(agent_name, text)
        return self._write_json(200 if ok else 400,
                                {"ok": ok, "message": msg,
                                 "error": None if ok else msg})

    def _handle_post_run(self) -> None:
        try:
            length = int(self.headers.get("Content-Length", "0"))
            raw = self.rfile.read(length).decode("utf-8")
            params = urllib.parse.parse_qs(raw)
            agent = (params.get("agent") or [""])[0]
            label = (params.get("label") or [""])[0].strip() or agent
            budget = float((params.get("budget") or [str(DEFAULT_BUDGET_S)])[0])
            filter_substr = (params.get("filter") or [""])[0].strip() or None
        except Exception as e:
            return self._write_json(400, {"error": f"bad form: {e}"})

        # Sanitize the label: keep alnum, underscore, dash. No path
        # traversal under any circumstances.
        if not re.fullmatch(r"[A-Za-z0-9_\-]{1,64}", label):
            return self._write_json(400,
                {"error": "label must match [A-Za-z0-9_-]{1,64}"})
        if agent not in list_agents():
            return self._write_json(400,
                {"error": f"agent {agent!r} not available"})

        job_id, err = start_job(agent, budget, label, filter_substr)
        if err:
            return self._write_json(409, {"error": err})
        return self._write_json(200, {"job_id": job_id})

    # ─── SSE log streaming ──────────────────────────────────────────
    def _stream_job_log(self, job_id: str) -> None:
        with JOBS_LOCK:
            job = JOBS.get(job_id)
        if not job:
            return self._write_json(404, {"error": "no such job"})

        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "keep-alive")
        self.send_header("X-Accel-Buffering", "no")
        self.end_headers()

        idx = 0
        last_status = None
        try:
            while True:
                with job["log_lock"]:
                    new_lines = job["log"][idx:]
                    idx = len(job["log"])
                for ln in new_lines:
                    self.wfile.write(b"event: line\ndata: ")
                    self.wfile.write(ln.encode("utf-8", errors="replace"))
                    self.wfile.write(b"\n\n")
                if job["status"] != last_status:
                    self.wfile.write(b"event: status\ndata: ")
                    self.wfile.write(job["status"].encode("utf-8"))
                    self.wfile.write(b"\n\n")
                    last_status = job["status"]
                self.wfile.flush()
                if job["status"] in ("done", "failed"):
                    break
                # wait for an update or a 1s tick
                job["log_event"].wait(timeout=1.0)
                job["log_event"].clear()
        except (BrokenPipeError, ConnectionResetError):
            pass

    # ─── SSE structured-feed streaming ──────────────────────────────
    def _stream_job_feed(self, job_id: str) -> None:
        """Stream the per-job structured event feed (orchestrator_log,
        problem_start, attempt, problem_end, status) so the browser can
        render a live "I'm proving the theorem with the agent" view."""
        with JOBS_LOCK:
            job = JOBS.get(job_id)
        if not job:
            return self._write_json(404, {"error": "no such job"})

        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "keep-alive")
        self.send_header("X-Accel-Buffering", "no")
        self.end_headers()

        idx = 0
        try:
            while True:
                with job["feed_lock"]:
                    new_events = job["feed"][idx:]
                    idx = len(job["feed"])
                for ev in new_events:
                    payload = json.dumps(ev["data"], default=str)
                    self.wfile.write(b"event: ")
                    self.wfile.write(ev["kind"].encode("ascii"))
                    self.wfile.write(b"\ndata: ")
                    self.wfile.write(payload.encode("utf-8", errors="replace"))
                    self.wfile.write(b"\n\n")
                self.wfile.flush()
                if job["status"] in ("done", "failed") and idx >= len(job["feed"]):
                    break
                job["feed_event"].wait(timeout=1.0)
                job["feed_event"].clear()
        except (BrokenPipeError, ConnectionResetError):
            pass


def _job_status(job_id: str) -> dict:
    with JOBS_LOCK:
        job = JOBS.get(job_id)
    if not job:
        return {"error": "no such job"}
    return {
        "id": job["id"],
        "status": job["status"],
        "exit_code": job.get("exit_code"),
        "started_at": job.get("started_at"),
        "ended_at": job.get("ended_at"),
        "label": job["label"],
        "agent": job["agent"],
        "n_log_lines": len(job["log"]),
    }


# ───────────────────────── main ───────────────────────────────────────

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--host", default="0.0.0.0",
                    help="Bind host (default 0.0.0.0 — public).")
    ap.add_argument("--port", type=int, default=8000)
    args = ap.parse_args()

    print(f"# LeanTacticLatencyBench web — http://{args.host}:{args.port}")
    print(f"# project root: {PROJECT_ROOT}")
    print(f"# LLM agents: {'enabled' if ALLOW_LLM_AGENTS else 'DISABLED'}")
    print(f"# max concurrent jobs: {MAX_CONCURRENT_JOBS}, "
          f"max budget: {MAX_BUDGET_S}s/problem")

    httpd = ThreadingHTTPServer((args.host, args.port), Handler)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("# shutting down")
        httpd.server_close()


if __name__ == "__main__":
    main()
