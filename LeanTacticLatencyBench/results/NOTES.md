# Run notes

Bench host: AWS EC2 (Amazon Linux 2023, x86_64), Python 3.9, Lean
`leanprover/lean4:v4.29.1`. `/usr/bin/time -v` is available, so RSS,
user, and system times are populated.

## What we observed

### Failed-proof latency
* All four canonical "failed proof" inputs (`HeavySimpFails`,
  `SlowDecideFails`, `SlowRflFails`, `SlowSimpFails`) terminate with
  exit code 1 in about **0.2 – 0.27 s** wall-clock per run, of which
  the bulk is Lean process startup (~200 ms baseline). Peak RSS
  is ~430 MB consistently.
* These benchmarks are deliberately *small* — they measure
  "time to recognise failure" on top of Lean's per-process startup,
  which is the right baseline before tuning failure-detection
  shortcuts.
* Adding `--profiler` is supported (`-Dtrace.profiler=true`,
  `-Dtrace.profiler.threshold=0`); profiler output appears in the
  captured stderr (truncated to 2 kB in the JSON; raw stderr can be
  inspected by re-running with `--profiler --label …` and watching
  the live console).

### Portfolio tactic search
* For "easy" goals (e.g. `True`, `100 ≤ 200`), the per-process
  startup dominates: every candidate finishes in ~200 ms, the
  declared "winner" is whichever tactic the polling loop notices
  first (Python polls every 20 ms), and the losers' kill latencies
  show up as `—` because they finished before any kill signal could
  be sent. This is itself a useful baseline: it tells us how much
  the *Lean process* itself costs versus the actual tactic.
* The `fast_vs_slow` goal mixes a `trivial` candidate against three
  `(have : … = … := by rfl); trivial` candidates that force kernel
  reduction of progressively larger `List.replicate` folds. There,
  `trivial` wins in ~200 ms and the slow candidates are SIGTERM-ed
  with measured kill latency of ~50 ms each. That 50 ms is the
  cancellation budget end-to-end, including signal delivery and the
  Lean process's signal handler. In future versions we can split this
  into "signal sent → process exit" vs "process exit → harness
  reaped".

### LSP stale cancellation
* Slow file: six chained `have` blocks each of the form
  `∀ n : Fin 800, n.val < 1000 := by decide`, so total cold-batch
  elaboration takes ~0.9 s; the harness sleeps `--stall-ms` (default
  200 ms) after `didOpen` before sending `didChange` with a `trivial`
  body.
* Measured **cancel latency** (`didChange → first clean
  publishDiagnostics`): **~0.2 s** consistently across two runs.
* Caveat: we treat *any* `publishDiagnostics` with no errors after the
  `didChange` timestamp as the signal that the new version has been
  processed. We do *not* yet match against the `version` field of the
  diagnostic message; if Lean ever emits a stale clean-diagnostics
  notification for the *old* file before processing the change, this
  harness would report it as success. v2 should match `version=2`.

## Reproducing

All commands are run from the project root:

```bash
cd LeanTacticLatencyBench
python3 scripts/run_failed_latency.py --repeats 2
python3 scripts/run_portfolio.py --timeout 30
python3 scripts/run_lsp_stale_cancel.py --stall-ms 200
python3 scripts/summarize_results.py
```

Raw JSON lands in `results/raw/`, the rolled-up CSV in
`results/summary.csv`.

## Known limitations / TODOs

* Failed-proof inputs would benefit from a Mathlib-import variant
  (e.g. `nlinarith` on an unprovable nonlinear goal) — that would
  give us seconds-scale, not 200 ms-scale, fail latencies. Held off
  in v1 to keep the project Mathlib-free and fast to install.
* Portfolio harness should record the `t_after_spawn` for each loser
  separately from `kill_latency`; currently kill latency is the only
  cancellation metric.
* LSP harness should
  - match `version` field on diagnostics,
  - send periodic synchronous requests (e.g. `textDocument/hover`)
    during the stale-work window and time round-trips, to quantify
    server responsiveness while it's busy,
  - sample the server's CPU usage via `psutil`.
* No experiment-level repetition / statistics yet (no median, p95).
  `summarize_results.py` writes a flat CSV; a notebook or pandas
  step is the natural follow-up.
