# LeanTacticLatencyBench

A reproducible benchmark harness for evaluating Lean proof-search work
end-to-end. Two halves:

1. **Agent evaluation** (the headline) — drop in any agent that follows
   the CLI contract, run it over a problem corpus, get a verified
   solve-rate, time-to-first-correct-proof, token usage, and a paired
   comparison against any other agent. Built around a tamper-resistant
   verifier (Lean compile + `#print axioms` + forbidden-token grep) so
   `:= sorry` and friends can't sneak through.
2. **Engine micro-benchmarks** — measure Lean's *internal* latencies
   for failed proofs, stale-tactic LSP cancellation, and process-level
   portfolio races. Useful as denominators when an agent burns most of
   its budget waiting on Lean process startup.

Everything is plain Lean (no Mathlib in the harness itself; agents and
their proofs may import whatever they want), Python stdlib only, no
build step.

## Layout

```
LeanTacticLatencyBench/
├── lakefile.toml
├── lean-toolchain               ← leanprover/lean4:v4.29.1
├── agents/
│   ├── baseline_decide.py       ← walks a fixed tactic pool
│   ├── baseline_random.py       ← random sampler (noise floor)
│   ├── llm_openai.py            ← OpenAI API agent (urllib, stdlib-only)
│   ├── llm_claude.py            ← Anthropic API agent (urllib, stdlib-only)
│   └── prompts/
│       ├── llm_openai_default.txt
│       └── llm_claude_default.txt
├── Bench/
│   ├── AgentProblems/           ← *.problem.json corpus (12 problems, graded)
│   ├── FailedProofs/            ← engine micro-bench: failing .lean files
│   ├── PortfolioGoals/          ← engine micro-bench: parallel-tactic races
│   └── LspStale/                ← engine micro-bench: slow .lean for LSP
├── scripts/
│   ├── verify_proof.py          ← standalone verifier (compile + #print axioms + grep)
│   ├── run_agent.py             ← agent orchestrator (budget + verification)
│   ├── profile_agent_run.py     ← per-attempt profiling, failure kinds, waste/productive
│   ├── view_attempts.py         ← pretty-print attempts.jsonl for one problem
│   ├── compare_agents.py        ← paired comparison: solve rate, TTFC, McNemar
│   ├── summarize_results.py     ← engine-bench JSON → flat CSV
│   ├── run_failed_latency.py    ← engine bench: failed-proof latency
│   ├── run_portfolio.py         ← engine bench: portfolio search (--calibrate for savings)
│   └── run_lsp_stale_cancel.py  ← engine bench: LSP cancel latency
├── results/
│   ├── agents/                  ← one subdir per agent run
│   ├── raw/                     ← engine-bench per-run JSON
│   ├── summary.csv              ← engine-bench rolled-up CSV
│   └── NOTES.md                 ← what the latest engine run produced
├── web/
│   ├── server.py                ← stdlib HTTP server: dashboard, run, profile, trail
│   └── serve.sh                 ← launcher (foreground or --bg)
└── README.md
```

## Web UI

A stdlib-only browser UI for everything in the agent-evaluation half:
launch runs, **watch the agent prove each theorem live — tactic, goal,
error, and time as they happen** — browse per-attempt trails (with
full LLM transcripts), see profile breakdowns, and compare any two
runs side-by-side.

```bash
cd LeanTacticLatencyBench
./web/serve.sh                    # foreground, http://0.0.0.0:8000
./web/serve.sh --bg               # detach (writes web/server.log + web/server.pid)
./web/serve.sh --port 9000        # custom port
```

The `--bg` mode writes the pid to `web/server.pid` so you can
`kill $(cat web/server.pid)` to stop it.

### The headline route — live theorem-by-theorem view

Open `/jobs/<id>` while a run is in progress and you see the agent
working in real time:

- **Currently proving** panel showing the *actual theorem statement*
  (rendered from the corpus JSON, not paraphrased) above a stream of
  attempt cards. Each card lights up the moment it lands in
  `attempts.jsonl`:
  - one-line tactic preview (truncated, full text in `view_attempts`),
  - failure kind (`simp_no_progress`, `decide_stuck`, `type_mismatch`,
    `unsolved_goals`, `timeout`, …) color-coded green/orange/red,
  - elapsed compile time and seconds since the problem started,
  - a one-line excerpt of Lean's error message (the "goal at the time
    of failure" is the first non-empty line).
- **Done** sidebar that pushes each finished problem (with PASS/FAIL
  status and total time) as the run progresses, so you can see how far
  through the corpus the agent has gotten.
- **Status pill** at the top — `running` / `done` / `failed` —
  flipping when the orchestrator exits *and* the watcher has flushed
  the final attempts (so the UI is never out-of-sync with the file).
- **Orchestrator log** in a collapsible `<details>` block at the
  bottom for the raw stdout from `run_agent.py`.

The page is one HTTP request — no JS framework, no build step. It
streams via Server-Sent Events from `/api/jobs/<id>/feed`.

### Live-feed event types (`/api/jobs/<id>/feed`)

All events are SSE with a named `event:` line and a JSON `data:`
payload. The same endpoint serves an in-progress consumer and a
late-attaching consumer (it replays the full log first, then streams
new events).

| Event | When it fires | Payload |
|---|---|---|
| `orchestrator_log` | Every line `run_agent.py` writes to stdout | `{line}` |
| `problem_start` | A new problem's output dir appears | `{name, statement, difficulty, imports}` — the full theorem statement, copied from the corpus JSON via the server's `_build_problem_lookup()` |
| `attempt` | A new line is appended to that problem's `attempts.jsonl` | `{problem, index, tactic, ok, failure_kind, error_excerpt, elapsed_s, t_since_start_s, exit_code}` — `failure_kind` is classified by the server (not the agent) so it's consistent across agents |
| `problem_end` | The problem's `summary.json` is written | `{name, claimed_solved, attempts, total_wall_s, verified}` |
| `status` | The orchestrator process exits AND the watcher has done its final flush | `{status: "done"|"failed", code}` — fired last, never before any pending `attempt`/`problem_end` |

A watcher thread polls the output directory every 250 ms while the
job runs, tailing each problem's `attempts.jsonl` as it grows. When
the orchestrator exits, the watcher does three final scans before
acknowledging the status flip — so you'll always receive every
attempt before the page transitions to `done`.

You can subscribe from any client (the bundled UI is one consumer):

```bash
curl -N http://localhost:8000/api/jobs/<id>/feed
```

### Visualize and edit the agent

Open `/agents` to see every agent script, then click into
`/agent-flow/<name>` for two things side-by-side:

1. **Workflow diagram** — an inline SVG that shows the agent's
   reasoning loop concretely:

   ```
   problem.json ──► system prompt ──► user message ──► AGENT (LLM)
                                            ▲                │
                                            │                ▼
                              error feedback │        proposed proof
                                            │                │
                                            └── Lean output ◄┘
                                                        │
                                                        ▼ ok
                                                    ✓ verified
   ```

   The diagram makes the data flow explicit: which boxes the LLM sees
   (system prompt + user message), which boxes Lean produces (the
   error feedback that closes the loop), and where the canonical
   verifier sits. For non-LLM agents (`baseline_*`) the central box
   becomes "Tactic-pool walker" so you can see how a baseline differs.

2. **System-prompt editor** — a textarea pre-loaded with the contents
   of `agents/prompts/<name>_default.txt`. Save and the file is
   atomically rewritten (a `.bak` of the previous version is kept).
   The next `run_agent.py` invocation reads the prompt fresh, so you
   can iterate: tweak the prompt, hit "Run with this prompt →", watch
   the live theorem-by-theorem view to see how the new prompt
   performs, repeat.

Safeguards on the prompt editor:

- only `llm_*` agents have an editable prompt (baseline agents'
  candidate sets live in their `.py` files);
- agent names are validated against `[A-Za-z0-9_]{1,64}` — no path
  traversal possible;
- prompt body is capped at 32 KB.

This is the route to use when you want to do A/B experiments on
prompts: change the prompt, run, compare runs via `/compare`.

### All routes

| Path | What you get |
|---|---|
| `/` | Dashboard: every agent run with verified count + solve-rate bar |
| `/run` | Form to launch a new run (agent dropdown, label, budget, optional problem-name filter). After submit, redirects to `/jobs/<id>` so you immediately see the live view. |
| `/jobs` | Table of all jobs since server start; click an id for the live view |
| `/jobs/<id>` | **Live theorem-by-theorem view** (see above) — currently proving + completed sidebar + orchestrator log |
| `/api/jobs/<id>/feed` | SSE stream of structured events (`problem_start`, `attempt`, `problem_end`, `status`, `orchestrator_log`) |
| `/agents` | List of agent scripts; each links to its `/agent-flow/<name>` page |
| `/agent-flow/<name>` | Workflow diagram + system-prompt editor for one agent |
| `/api/agents/<name>/prompt` | `POST` — save a new system prompt (llm_* agents only; size-capped) |
| `/agents/<label>` | Post-run summary: profile totals, per-problem table, failure-kind histogram, top wasted tactics |
| `/agents/<label>/<problem>` | Per-attempt trail (same data as `view_attempts.py`); add `?full=1` to inline the LLM prompts/responses/Lean output |
| `/compare?a=&b=` | Side-by-side comparison output (same as `compare_agents.py`) |
| `/problems` | Corpus listing |

### Public-server warning (read this)

When bound to `0.0.0.0` (the default), **anyone who can reach the
port can launch experiments on your machine**. For LLM agents that
means anyone can spend the OpenAI / Anthropic key configured on the
server. Built-in mitigations:

| Limit | Default | How to change |
|---|---|---|
| Concurrent jobs | 1 | edit `MAX_CONCURRENT_JOBS` in `web/server.py` |
| Max budget | 600 s/problem | edit `MAX_BUDGET_S` |
| LLM agents enabled? | yes | `ALLOW_LLM_AGENTS=0 ./web/serve.sh` to disable |
| Path traversal | blocked | `transcript_text()` validates every path against the per-problem `transcripts/` dir |
| API-key file (`<repo>/../api`) | unreachable from any URL | the server has no static-file fallback — every route is hard-coded |

A banner at the top of every page restates these limits so it's
obvious to visitors.

If you want stricter access (only you can launch runs, anyone can
view), the simplest patch is to add a token check inside
`_handle_post_run` — three lines of code.

### Web UI live demo

```
http://<your-ec2-public-ip>:8000/
```

(Make sure inbound port 8000 is open in the EC2 security group.)

## Quick start

### Agent evaluation (the headline)

The four scripts split into two distinct roles. `run_agent.py` is the
**only one that actually executes the agent** (and Lean). The other
three are **offline analyzers** that read whatever `run_agent.py`
already wrote into `results/agents/<agent>/` — they finish in
milliseconds and run no tactics.

| Step | Script | What it does | Touches Lean? |
|---|---|---|---|
| 1 | `run_agent.py` | Runs agent on the corpus, verifies each proof, writes per-problem outputs | Yes (slow) |
| 2 | `profile_agent_run.py` | Reads the run, prints per-attempt + failure-kind + waste breakdown, writes CSV | No (fast) |
| 3 | `view_attempts.py` | Pretty-prints the tactic-by-tactic trail for one problem | No (fast) |
| 4 | `compare_agents.py` | Diffs two runs (solve rate Δ, McNemar, paired TTFC) | No (fast) |

```bash
cd LeanTacticLatencyBench

# 0. (One-time) — drop your OpenAI key in a file at the repo root.
printf '%s' 'sk-proj-…' > ../api
chmod 600 ../api

# 1. RUN agents over the corpus (this is the slow step).
python3 scripts/run_agent.py --agent agents/baseline_decide.py --budget 60
python3 scripts/run_agent.py --agent agents/baseline_random.py --budget 60
python3 scripts/run_agent.py --agent agents/llm_openai.py --budget 180
# Or, if you have an Anthropic key set:
# python3 scripts/run_agent.py --agent agents/llm_claude.py --budget 180

# 2. PROFILE that run (fast, offline, reads existing JSON).
python3 scripts/profile_agent_run.py \
  --run results/agents/llm_openai/agent_run.json --top 8

# 3. VIEW the trail for one problem (fast, offline).
python3 scripts/view_attempts.py \
  results/agents/llm_openai/nat_mul_comm/attempts.jsonl

# For LLM agents, --full also dumps the system prompt, every user
# message sent to the model, every model reply, and the full Lean
# stdout/stderr per attempt:
python3 scripts/view_attempts.py --full \
  results/agents/llm_openai/nat_mul_comm/attempts.jsonl

# 4. COMPARE two runs.
python3 scripts/compare_agents.py \
  --a results/agents/baseline_decide/agent_run.json \
  --b results/agents/llm_openai/agent_run.json

# 5. Spot-check a single proof manually.
python3 scripts/verify_proof.py \
  --problem Bench/AgentProblems/17_nat_mul_comm.problem.json \
  --proof results/agents/llm_openai/nat_mul_comm/proof.lean
```

Every script supports `--help`.

## Configuration

Two things to configure — both optional, both for the LLM agent:

### API keys

Two LLM agents ship with the harness; each reads its key from a
different source.

**OpenAI** (`agents/llm_openai.py`) — recommended pattern is a
single-line file, not an env var (so the key never lands in shell
history):

```bash
printf '%s' 'sk-proj-…' > ../api    # one line, no trailing newline
chmod 600 ../api                    # owner-only
```

The agent looks for the key in this order:
`--api-key-file <path>` → `$OPENAI_API_KEY` → `<project_root>/api` →
`<project_root>/../api` (matches this repo's layout). Override the
default model `gpt-4o` with `--model` or `$OPENAI_MODEL`.

**Anthropic** (`agents/llm_claude.py`) — env var:

```bash
cp config.example.env config.env
# edit config.env: ANTHROPIC_API_KEY="sk-ant-…"
source config.env
```

`config.env` is gitignored. Without `ANTHROPIC_API_KEY` the Claude
agent exits 2 on every problem with the reason
"ANTHROPIC_API_KEY not set" and the orchestrator records every
problem as `UNSOLVED`. Override the default model `claude-opus-4-7`
with `--model` or `$ANTHROPIC_MODEL`.

The `api` file (any pattern) is gitignored at the repo root so
neither key can be accidentally committed.

### Agent prompt

Each LLM agent reads its system prompt from a file under
`agents/prompts/`:

| Agent | Default prompt |
|---|---|
| `agents/llm_openai.py` | `agents/prompts/llm_openai_default.txt` |
| `agents/llm_claude.py` | `agents/prompts/llm_claude_default.txt` |

Edit those files directly to change the defaults; or override per-run:

```bash
# Per-run override via flag:
python3 scripts/run_agent.py \
  --agent "agents/llm_openai.py --system-prompt-file agents/prompts/my_prompt.txt" \
  --budget 180

# Or globally via env var (shell rc / config.env):
export LATB_SYSTEM_PROMPT_FILE="agents/prompts/my_prompt.txt"
```

The prompt actually used for every run is also saved to
`results/agents/<agent>/<problem>/transcripts/system_prompt.txt`, so
you can always tell *exactly* which prompt produced a given result.

### Engine micro-benchmarks

```bash
python3 scripts/run_failed_latency.py
python3 scripts/run_portfolio.py --timeout 30
python3 scripts/run_lsp_stale_cancel.py --stall-ms 200
python3 scripts/summarize_results.py        # rolls up results/raw/*.json
```

## Agent contract

An agent is any executable that accepts `--problem PROB.json --workdir
WD/`. After it exits, `WD/` must contain:

| File              | Required | Contents |
|---|---|---|
| `proof.lean`      | when claiming success | The candidate proof. The verifier reconstructs a fresh `theorem <name> : <statement> := <body>` from the problem statement and the body extracted from this file — so the agent cannot modify the statement. |
| `attempts.jsonl`  | always | One JSON line per attempt: `{index, t_since_start_s, …}`. The orchestrator counts these for `n_attempts`. |
| `summary.json`    | always | `{agent, problem_name, claimed_solved, attempts, total_wall_s, …}`. The agent's *self-report*; not trusted. |

The orchestrator wraps the agent in `/usr/bin/time -v` (when available)
to capture wall-clock, user/system CPU, and peak RSS, then runs the
verifier independently.

A **problem** looks like:

```json
{
  "name": "nat_add_comm_all",
  "difficulty": "easy",
  "imports": [],
  "statement": "theorem nat_add_comm_all : ∀ a b : Nat, a + b = b + a",
  "tags": ["arithmetic", "commutativity"]
}
```

`statement` is the *exact* line the verifier reconstructs against — no
substitution, no name games. If the agent's `proof.lean` reuses the
same theorem name, the canonical reconstruction compiles; otherwise the
verifier rejects it.

## Verification (anti-cheat)

`scripts/verify_proof.py` runs in two stages:

1. **Textual** — grep for forbidden tokens. By default:
   `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `extern`,
   `implementedBy`. Configurable via `--forbid-token` / `--allow-token`.
2. **Semantic** — extract the proof body, paste it into a *fresh* file
   built from the problem's official `imports` + `statement`, append
   `#print axioms <name>`, run `lake env lean`. Reject if the compile
   exits non-zero, emits any `error:` diagnostic, or `#print axioms`
   reports an axiom outside the allowed set
   (`propext`, `Classical.choice`, `Quot.sound` by default;
   extend with `--allow-axiom`).

Three things this catches that a naive "did Lean exit 0?" check would
miss:

| Cheat attempt | Caught by |
|---|---|
| `theorem foo : … := by sorry` | textual grep |
| `private axiom myAx : …` then use it | textual grep AND `#print axioms` |
| Modifying the theorem statement to something easy | canonical reconstruction (uses official statement) |

Verified on these three plus the 12 corpus problems with
`baseline_decide`: all 12 verify cleanly, neither `sorry` nor
axiom-injection passes.

## Detailed profiling (the "what is the agent actually doing?" view)

For convincing benchmarking — beyond just wall-clock — the harness
breaks every agent run into:

- **Number of failed attempts** per problem (and totals across the corpus).
- **Time spent on each failure** (mean, median, max).
- **Failure-kind histogram** — `simp_no_progress`, `decide_stuck`,
  `type_mismatch`, `rfl_failed`, `unsolved_goals`, `timeout`,
  `unknown_identifier`, `compile_failed`, …
- **Top wasted tactics** — cumulative seconds spent on each failed tactic
  string across the whole corpus, so you can see *exactly* what
  candidates an agent is repeatedly losing time to.
- **Cancellation what-if (oracle)** — `without_cancellation_s` (every
  attempt runs to completion) vs `with_oracle_s` (only the winning
  attempt). The difference is the *upper bound* on what early
  cancellation / smarter scheduling can save.

### `profile_agent_run.py` — every attempt, every failure kind

```text
$ python3 scripts/profile_agent_run.py \
    --run results/agents/baseline_random/agent_run.json --top 5
# Agent profile: baseline_random
# corpus:  12 problem(s)
# solved:  8/12

## Per-problem
  problem                       #att #fail   waste_s   prod_s   wall_s  status
  triv_True                        1     0     0.000    0.196    0.232  OK
  one_plus_one                     1     0     0.000    0.191    0.227  OK
  nat_add_zero_all                 3     2     0.365    0.185    0.588  OK
  nat_add_comm_all                30    30     5.492    0.000    5.538  FAIL
  …
  totals:                        140   132    24.482    1.498
  waste / (waste + productive) = 94.2%

## Failure kinds (across all problems)
  kind                    count    tot_s   mean_s
  unsolved_goals             36    6.654    0.185
  tactic_failed              30    5.571    0.186
  compile_failed             27    5.063    0.188
  type_mismatch              20    3.684    0.184
  unknown_identifier         16    2.953    0.185
  rfl_failed                  3    0.556    0.185

## Top 5 most-expensive failed tactics
     cum_s count  tactic
     1.883    10  trivial
     1.848    10  intros; intros
     1.468     8  intro l
     0.758     4  simp; intro h
     0.756     4  simp; decide

## Cancellation what-if (clairvoyant oracle)
  Without cancellation:    25.980s
  With perfect oracle:      1.498s
  Upper bound on savings:   24.482s (94.2%)
```

It also drops two artifacts next to the run:

- `results/agents/<agent>/attempts_detail.csv` — one row per tactic
  attempt across all problems (agent, problem, idx, tactic, elapsed,
  ok, failure_kind, exit_code). Open in pandas / a spreadsheet.
- `results/agents/<agent>/profile_summary.json` — machine-readable
  totals, failure-kind histogram, top wasted tactics, and the oracle
  cancellation numbers.

### `view_attempts.py` — debug a single problem's trail

```text
$ python3 scripts/view_attempts.py \
    results/agents/baseline_decide/nat_add_comm_all/attempts.jsonl
=== nat_add_comm_all ===
  #0    t= 0.18s  0.185s  tactic_failed     decide                  failed to synthesize
  #1    t= 0.37s  0.183s  rfl_failed        rfl                     Tactic `rfl` failed: Expected the goal to be a binary relation
  #2    t= 0.55s  0.185s  tactic_failed     trivial                 Tactic `assumption` failed
  #3    t= 0.74s  0.183s  type_mismatch     exact True.intro        Type mismatch
  #4    t= 0.92s  0.186s  rfl_failed        intro; rfl              Tactic `rfl` failed: Expected the goal to be a binary relation
  #5    t= 1.11s  0.185s  rfl_failed        intros; rfl             Tactic `rfl` failed: The left-hand side
  #6    t= 1.29s  0.183s  compile_failed    intro; decide           Expected type must not contain free variables
  …
  #12   t= 2.40s  0.188s  OK                intros; omega
```

Each row is one attempt: index, cumulative time-since-start, compile
elapsed, classified failure kind, the tactic, and a one-line excerpt
of Lean's error message. This is the format you want when reviewing
*why* an agent's strategy is wasting time.

Pass a directory to view multiple problems; pass `--filter substr`
to limit which problems print.

### What gets saved per attempt — the full per-step trail

Every `run_agent.py` invocation populates this layout under
`results/agents/<agent>/<problem>/`:

```
results/agents/llm_claude/nat_mul_comm/
├── attempts.jsonl              ← per-attempt metrics (one JSON line each)
├── proof.lean                  ← winning proof, if any
├── summary.json                ← claimed_solved, attempts, tokens, …
├── attempt_000.lean            ← the candidate Lean file the agent compiled
├── attempt_001.lean
└── transcripts/                ← (LLM agents only)
    ├── system_prompt.txt       ← exact system prompt used this run
    ├── attempt_000.prompt.txt  ← full user message sent to Claude
    ├── attempt_000.response.txt ← full reply from Claude
    ├── attempt_000.compile.txt ← full Lean stdout + stderr (not truncated)
    ├── attempt_001.prompt.txt
    ├── attempt_001.response.txt
    └── attempt_001.compile.txt
```

What each one is good for:

| File | Best when you want to… |
|---|---|
| `attempts.jsonl` | Numerically analyze attempts (timings, failure-kind histograms) — feed to `profile_agent_run.py`. |
| `attempt_NNN.lean` | See exactly what Lean was asked to compile — useful for reproducing a failure under `lake env lean`. |
| `transcripts/system_prompt.txt` | Confirm which version of the prompt produced this run (especially when comparing two prompt variants). |
| `transcripts/attempt_NNN.prompt.txt` | See the exact user message sent to the LLM, including any prior-attempt error feedback the agent injected. |
| `transcripts/attempt_NNN.response.txt` | See the LLM's full reply with its reasoning around the code block. |
| `transcripts/attempt_NNN.compile.txt` | Get the **full** Lean output (`attempts.jsonl` only stores the first 2 KB of stderr — the transcript file is unbounded). |

`view_attempts.py --full` interleaves all of these into one readable
stream:

```text
$ python3 scripts/view_attempts.py --full \
    results/agents/llm_claude/nat_mul_comm/attempts.jsonl
=== nat_mul_comm ===
  [system prompt: …/transcripts/system_prompt.txt]
    You are a Lean 4 proof assistant.
    Given a theorem, produce a complete Lean 4 proof.
    …

  #0  t= 0.00s  4.123s  unsolved_goals  by induction b with …       unsolved goals: case zero …
        ─── prompt (attempt_000.prompt.txt) ───
          Prove the following Lean 4 theorem.
          Theorem name: `nat_mul_comm`
          ```lean
          theorem nat_mul_comm : ∀ a b : Nat, a * b = b * a
          ```
          …
        ─── response (attempt_000.response.txt) ───
          ```lean
          theorem nat_mul_comm : ∀ a b : Nat, a * b = b * a := by
            intro a b
            induction b with
            …
          ```
        ─── compile (attempt_000.compile.txt) ───
          # Lean exit code: 1
          # Elapsed: 4.123s
          # Timed out: False
          --- stdout ---
          attempt_000.lean:6:5: error: unsolved goals
          …
```

This is what you want when investigating *why* an agent picked the
candidate it did, or when adapting the system prompt to fix a
recurring failure mode.

### Cancellation savings (portfolio bench)

The portfolio bench (`run_portfolio.py`) runs candidates in parallel
and SIGTERMs the losers when one wins. With `--calibrate`, it also
runs each candidate alone first to measure its **natural runtime** —
then computes exact compute saved by cancellation:

```text
$ python3 scripts/run_portfolio.py --calibrate --timeout 30
…
   calib : 'trivial'                           natural=0.195s  solo_exit=0
   calib : 'have-with-3000-rfl-then-trivial'   natural=0.187s  solo_exit=1
   …
   winner: 'trivial' in 0.201s
   loser : 'have-with-3000-rfl-then-trivial'   exit=-15  kill_latency=0.003s
                                               natural=0.187s saved=0.000s
   ── compute natural=0.761s actual=0.811s saved=0.000s
```

`saved` per loser is `natural_elapsed - actual_elapsed`. The aggregate
`saved` answers "how much compute did parallel-with-cancellation
**actually** save vs running every candidate to completion?" When all
candidates are similar in runtime (as in the plain-Lean fixtures
shipped here), savings are minimal — the framework lets you measure
this precisely once you wire in heavyweight candidates.

## Sample run (on this machine, 18-problem corpus)

Three agents, same corpus and same `--budget`, side-by-side:

| Agent | Solved | Median attempts | Median TTFC |
|---|---|---|---|
| `baseline_decide` | 17/18 | 11 | 2.07s |
| `baseline_random` | 13/18 | 3 | 0.62s |
| `llm_openai` (gpt-4o) | 14/18 | 1 | 1.28s |

The interesting finding is *which* problems each agent gets:

```
$ python3 scripts/compare_agents.py --a …/llm_openai/agent_run.json \
                                    --b …/baseline_decide/agent_run.json
## McNemar 2×2 (intersection)
                          baseline_decide=PASS  baseline_decide=FAIL
  llm_openai=PASS                     13                    1
  llm_openai=FAIL                      4                    0

## Per-problem outcomes
  nat_mul_comm                    PASS       fail        ← gpt-4o ONLY
  two_n_eq_n_plus_n               fail       PASS        ← baseline_decide ONLY
  nat_add_cancel_left             fail       PASS        ← baseline_decide ONLY
  list_reverse_reverse            fail       PASS        ← baseline_decide ONLY
  list_length_append              fail       PASS        ← baseline_decide ONLY
```

That's a real, defensible empirical claim:

* **`gpt-4o` is the only agent that proves `nat_mul_comm`** — the
  problem requires nested induction on `Nat` *with multiplication*,
  which `omega` doesn't handle and the `baseline_decide` tactic pool
  doesn't include.
* **`baseline_decide` wins on four induction-heavy problems** where
  the right `induction l <;> simp_all` happens to be in its pool but
  `gpt-4o` proposes an over-clever proof that doesn't compile within
  the 4-attempt cap.
* **`baseline_decide` is faster on jointly-solved problems** because
  Lean process startup (~200 ms) dominates and the OpenAI API adds
  1-5 s of round-trip per attempt; on problems where one tactic-pool
  candidate wins quickly, the LLM round-trip is pure overhead.
* **`gpt-4o`'s waste budget is far smaller in absolute terms**:
  `profile_agent_run.py` reports 4.2 s of wasted compute vs 33.6 s
  for `baseline_decide` (89.3% waste-ratio), because each LLM attempt
  is one informed try rather than a sweep through a fixed pool.

This is the kind of nuanced comparison the framework is built to
surface — different scheduling strategies don't just compete on
"who solves more" but on *which* problems they specialize in.

## Bundled agents

| Agent | Purpose | Notes |
|---|---|---|
| `baseline_decide` | Walks a hand-tuned list of high-leverage tactics in order; first success wins. Sets the practical solve-rate ceiling for plain-Lean problems. | No external dependencies. |
| `baseline_random` | Samples random combinations from a small atom pool. The noise floor — a real agent should beat this. | Seed-controlled (`--seed`). |
| `llm_openai` | Asks OpenAI's Chat Completions API to write the proof; on compile failure, sends the Lean error back and retries. | Reads key from `--api-key-file`, `$OPENAI_API_KEY`, or `<project>/api` / `<project>/../api`. Default model `gpt-4o`. urllib only. Records token counts per attempt. |
| `llm_claude` | Asks Claude to write the proof; on compile failure, sends the Lean error back and retries. | Reads `ANTHROPIC_API_KEY`. Default model `claude-opus-4-7`. urllib only. Records token counts per attempt. |

Add your own agent: drop a script in `agents/`, accept `--problem` and
`--workdir`, write `proof.lean` / `attempts.jsonl` / `summary.json`,
exit 0/1.

## Bundled corpus (18 problems)

| File | Difficulty | Statement |
|---|---|---|
| `01_trivial_True` | trivial | `True` |
| `02_one_plus_one` | trivial | `(1 : Nat) + 1 = 2` |
| `03_nat_add_zero` | easy | `∀ n : Nat, n + 0 = n` |
| `04_nat_add_comm` | easy | `∀ a b : Nat, a + b = b + a` |
| `05_nat_add_assoc` | easy | `∀ a b c : Nat, (a + b) + c = a + (b + c)` |
| `06_nat_le_succ` | easy | `∀ n : Nat, n ≤ n + 1` |
| `07_nat_succ_ne_zero` | medium | `∀ n : Nat, n.succ ≠ 0` |
| `08_nat_two_n_eq_n_plus_n` | medium | `∀ n : Nat, 2 * n = n + n` |
| `09_list_append_nil` | medium | `∀ (l : List Nat), l ++ [] = l` |
| `10_list_length_reverse` | medium | `∀ (l : List Nat), l.reverse.length = l.length` |
| `11_nat_dichotomy` | hard | `∀ a b : Nat, a ≤ b ∨ b ≤ a` |
| `12_list_map_id` | hard | `∀ (l : List Nat), l.map id = l` |
| `13_nat_add_cancel` | hard | `∀ a b c : Nat, a + b = a + c → b = c` |
| `14_list_append_assoc` | hard | `∀ (l₁ l₂ l₃ : List Nat), (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃)` |
| `15_list_reverse_reverse` | very_hard | `∀ (l : List Nat), l.reverse.reverse = l` |
| `16_list_length_append` | hard | `∀ (l₁ l₂ : List Nat), (l₁ ++ l₂).length = l₁.length + l₂.length` |
| `17_nat_mul_comm` | very_hard | `∀ a b : Nat, a * b = b * a` |
| `18_list_map_compose` | very_hard | `∀ (l : List Nat), ((l.map (· + 1)).map (· + 2)) = l.map (· + 3)` |

The trivial / easy / medium tier exercises `decide`, `omega`, `rfl`,
`simp`, basic induction, and case analysis over `Or`. The hard /
very_hard tier exercises induction with hypotheses, multi-step
inductions, list-induction-with-Nat, higher-order combinators, and
nonlinear arithmetic — `nat_mul_comm` in particular **defeats**
`baseline_decide` because `omega` doesn't handle multiplication and
the agent's hand-written tactic pool doesn't include the right
two-induction combinator.

The harness is corpus-agnostic — point `run_agent.py` at any
directory of `*.problem.json` files.

## Metrics & reliability

| Column | Reliability |
|---|---|
| `verified` | Ground truth — independent compile + axiom check. |
| `claimed_solved` | Self-report. Could be `true` while `verified=false` (the orchestrator flags this as "lying"). |
| `time_to_first_verified_s` (a.k.a. TTFC) | Wall-clock to verified `proof.lean`. Includes Lean process startup (~200 ms baseline) and inter-attempt overhead. Reliable but noisy at sub-second scale. |
| `agent_wall_s` | Wall-clock for the agent process from spawn to exit. |
| `agent_user_s` / `agent_system_s` / `agent_peak_rss_kb` | From `/usr/bin/time -v`; absent on macOS BSD `time`. |
| `n_attempts` | Lines in `attempts.jsonl`. Lower is better when both agents verify; cosmetic when neither does. |
| `total_input_tokens` / `total_output_tokens` | LLM agents only; sourced from the agent's `summary.json`. |

Cross-agent metrics (from `compare_agents.py`):

- **Solve rate** — `verified / corpus_size`. Headline number.
- **Median TTFC on intersected solved set** — fairer than mean-of-everything because unsolved → no TTFC.
- **McNemar 2×2** — paired solve/no-solve counts. Drop into a stats package for a p-value if you need it.
- **Per-problem wins** — count of problems where each agent had the lower TTFC.

## Limitations

- The corpus is plain-Lean only (no Mathlib). For Mathlib-aware agents,
  point `--corpus` at a custom directory and add `imports` to each
  problem JSON.
- Anti-cheat is conservative-grep + canonical reconstruction. A
  determined adversary could craft a custom `Decidable` instance that
  produces a vacuous proof — easier path is to add the new tactic name
  to `--forbid-token`. Document the configured forbid list in any
  paper.
- TTFC measurement includes Lean process startup. For ratio-style
  comparisons between agents on the same machine this cancels out, but
  absolute TTFC is not a "pure" reasoning-time number. The engine
  micro-benches (below) help quantify the startup floor.
- The LLM agent does not yet use prompt caching (corpus prompts are
  too short — under the 4096-token Opus 4.7 minimum). For larger
  corpora with shared system prompts, caching would cut cost
  ~10× per cached read.

## Engine micro-benchmarks

These measure Lean's internal latencies, independent of any agent.
Useful for separating "the agent is slow" from "Lean's failure
detection is slow." See [`results/NOTES.md`](results/NOTES.md) for
the most recent run; the rolled-up CSV is `results/summary.csv`.

| Suite | What it measures | Typical value (this machine) |
|---|---|---|
| Failed-proof latency | wall-clock for one Lean process to detect a failing tactic, including process startup | ~200 ms |
| Portfolio search | wall-clock from spawn to first winner; SIGTERM-to-exit kill latency for losers | winner ~200 ms; kill latency ~50 ms |
| LSP stale cancel | `didChange` to first clean `publishDiagnostics` | ~200 ms |

Running the engine benches:

```bash
python3 scripts/run_failed_latency.py --repeats 2
python3 scripts/run_portfolio.py --timeout 30
python3 scripts/run_lsp_stale_cancel.py --stall-ms 200
python3 scripts/summarize_results.py
```

## How to use this to evaluate an agent claim

A typical workflow when someone says "my new agentic workflow is
faster":

1. **Snapshot baseline.** Run the existing workflow against the corpus
   with `--budget` matching production constraints. Save
   `results/agents/<name>_baseline/`.
2. **Run the proposed workflow** under the same `--budget`. Save
   `results/agents/<name>_proposed/`.
3. **Compare.** `compare_agents.py --a baseline --b proposed`:
   - Solve rate Δ (positive = proposed solves more)
   - McNemar a-only / b-only (asymmetric wins)
   - TTFC Δ on the intersection (positive = proposed is slower on
     jointly-solved problems)
4. **Profile both.** `profile_agent_run.py` on each run gives:
   - Per-attempt counts (#attempts, #failed) — fewer tries is one
     way to be faster; faster individual tries is another.
   - Failure-kind histogram — does the proposed agent eliminate a
     specific failure mode? (e.g. fewer `simp_no_progress`)
   - Top wasted tactics — does the proposed agent stop trying the
     same expensive losers?
   - Oracle cancellation upper bound — bounds how much room is left
     for further improvement before "skip every losing attempt".
5. **Inspect specific failures** with `view_attempts.py`. When the
   proposed agent regresses on a problem the baseline solved,
   diffing `attempts.jsonl` shows exactly which tactic the new agent
   gave up on.
6. **Slice.** Filter the corpus by difficulty tag, plot TTFC vs
   `n_attempts`, or split by failure-kind to see if the speedup
   comes from "fewer tries", "faster tries", or "different tries".

The corpus and budget should be the same for both runs; the agent
command is the only change. All metrics are reproducible from the
JSON outputs alone — share the `results/agents/<name>/` dir to share
the result.
