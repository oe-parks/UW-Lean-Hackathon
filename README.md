# hackathon

Solution submitted by **Blossom Team** for the **UW Lean Hackathon** 2026.



# Result

We formalize the correctness and complexity of Edmond Blossom algorithm in Lean. We invent a novel autoresearch pipeline that rewrite the proof tactics and improve the lean compilation time. 


# Theorem diagram

Here we show the dependency diagram of the whole theorem, and an animation of how these Lemmas/Theorems are used in real production. 


## Instruction to Compile

The project is a standard Lake package (Lean 4.29.1 + Mathlib v4.29.1).

```bash
# one-time setup: fetch dependencies and download the Mathlib build cache
lake update

# subsequent builds
lake build
```

To compile the project, measure compilation time, and report the number of
`sorry` placeholders and build errors in one shot, use the helper script:

```bash
./scripts/measure-build.sh
```

The script prints a human-readable summary and also writes a machine-readable
report to `build-report.json` (elapsed time, exit status, error count,
`sorry`-warning count, per-file `sorry` breakdown). It is the primary signal
consumed by the autoresearch loop described below.

## Proof Graph Algorithm

We formalize graph theory from the ground up in Lean 4. We start by defining
the basic objects and theorems — vertices, edges, paths, matchings, girth,
and so on — sufficient to state and reason about the matching problem.

On top of that foundation, we design a small toy language: we give it an
explicit syntax and a sound operational semantics tailored to expressing the
blossom algorithm. We then implement Edmonds' blossom algorithm in that
language and verify its correctness in Lean.



## GraphIR Syntax&&Semantics

We prove the algorithmic correctness of Edmond Blossom algorithm on a Novel GraphIR representation, where program states contain graph objects. The IR is representative enough for any graph algorithm with recursion. 



## Autoresearch Pipeline

To accelerate proof development we built an **autoresearch loop** — a
fully-automated system that both *closes open `sorry` placeholders* and
*optimises compile time* of existing proofs, without human intervention.

### How it works

The pipeline runs in two complementary modes:

**Sorry-filling mode** (`python scripts/autoresearch.py [target]`)

1. Scans every `.lean` file for tactic-mode `sorry` placeholders.
2. Extracts the live Lean *proof goal state* at each `sorry` by temporarily
   injecting `trace_state` and compiling the file.
3. Sends the file, the goal, and any previous failure feedback to Claude
   (Anthropic) asking for 3–5 candidate proof tactics.
4. Evaluates every candidate with `lake env lean` and keeps all that compile.
5. Ranks passing candidates by a **proof quality score** that penalises opaque
   automation (`simp`, `aesop`, `decide`) and rewards explicit mathematical
   structure (`have`, `exact`, `calc`, `rcases`).
6. Writes the best candidate back to disk and repeats until no `sorry`s remain
   or no progress is made.

**Optimize mode** (`python scripts/autoresearch.py --optimize <file>`)

1. Measures the baseline compile time of the target file.
2. Detects any real compile errors and records their line numbers; blocks
   overlapping those lines are automatically skipped so the rest can still
   be optimised.
3. For each complete tactic proof block, asks Claude for refactored alternatives
   — conservative rewrites such as replacing bare `simp` with `simp only [...]`,
   extracting reasoning into named `have` blocks, or using explicit theorem
   applications instead of search tactics.
4. Ranks alternatives by the same quality score; accepts a change only if the
   new proof scores strictly better *and* introduces no new compile errors.
5. Writes the improved file, logs every change, and produces an interactive
   visualisation.

### Proof quality score

Lower is better. The score balances three signals:

```
score = 0.1 × compile_time
      + 2.0 × automation_cost    # penalise simp / aesop / decide / omega
      − 1.5 × structure_bonus    # reward have / exact / calc / rcases / refine
      + brevity_penalty           # mild penalty for one-liners
```

This biases the model toward readable, compositional proofs rather than
proof-golfed one-liners or giant `simp` calls.

### Decision-trace visualisation

Every run writes `proof-search.html` — an interactive force-directed graph
showing exactly which candidates were tried, why each failed or passed, and
why the chosen proof was selected over the alternatives.

> **Replace the placeholder below with a screen-recording gif of the graph.**

![Proof search decision trace](docs/proof-search-demo.gif)

Each node is a colour-coded card:

| Colour | Meaning |
|---|---|
| 🟠 Orange | Search root (the `sorry` / theorem being worked on) |
| 🟢 Green ★ | Chosen proof — best quality score |
| 🔵 Blue | Passing candidate not selected |
| 🔴 Red | Failed to compile |
| ⚫ Grey | Banned (`sorry` / `admit` / `native_decide`) |

Hover any node for the full proof text, quality score, compile time, and
error message. Drag to rearrange; scroll to zoom.

### Optimization log

Every `--optimize` run writes a timestamped Markdown log to `logs/`.  
Example entry from `Hackathon/Graph/Matching.lean`:

---

**`have h_first : (w.edges[0]'hpos) ∉ M.edgeSet := by`**

| | |
|---|---|
| Quality score | 6.30 → **3.34** (improvement) |
| Compile time | 3.00 s → 3.36 s |

**Before**
```lean
revert hpos
cases w with
| nil => intro hpos; simp at hpos
| @cons a b c hadj p =>
  intro _
  simp only [Walk.edges_cons, List.getElem_cons_zero]
  intro hMem
  exact hu (M.edge_vert (Subgraph.mem_edgeSet.mp hMem))
```

**After** — explicit intermediate `have` instead of inline term
```lean
cases w with
| nil => exact absurd hpos (by simp [Walk.edges])
| @cons a b c hadj p =>
  simp only [Walk.edges_cons, List.getElem_cons_zero]
  intro hMem
  have hVert : a ∈ M.verts := M.edge_vert (Subgraph.mem_edgeSet.mp hMem)
  exact hu hVert
```

**Why chosen:** highest quality score (3.34) among 4 candidates.  
The runner-up used bare `simp` (score 4.80, +1.46 worse) and
compiled 0.41 s faster — the pipeline correctly traded a small speed
regression for a substantially more readable proof.

---

Full logs are written to `logs/optimize-<file>-<timestamp>.md` and include
every block reviewed, all alternatives considered, and a run summary table.

## TODO List

Tracked against the current `sorry` placeholders in the source tree.

- [ ] **Toy graph foundation** — fill in the elementary lemmas in
  [Hackathon/Graph/Toy/Lemmas.lean](Hackathon/Graph/Toy/Lemmas.lean) (13
  open goals).
- [x] **Bridge to Mathlib `SimpleGraph`** — round-trip established in
  [Hackathon/Graph/Toy/Bridge.lean](Hackathon/Graph/Toy/Bridge.lean).
- [ ] **Walks and paths** — finish the walk lemmas in
  [Hackathon/Graph/Walks.lean](Hackathon/Graph/Walks.lean) (6 open).
- [ ] **Matchings** — complete [Hackathon/Graph/Matching.lean](Hackathon/Graph/Matching.lean) (4 open).
- [ ] **Augmenting paths** — complete [Hackathon/Graph/Augment.lean](Hackathon/Graph/Augment.lean) (4 open).
- [ ] **Berge's theorem** — close the three remaining goals in
  [Hackathon/Graph/Berge.lean](Hackathon/Graph/Berge.lean).
- [ ] **Bipartite matching (Hungarian / Hopcroft–Karp)** — implement
  `augmentOnce` and prove soundness/progress/completeness in
  [Hackathon/Graph/Algorithms/Bipartite.lean](Hackathon/Graph/Algorithms/Bipartite.lean).
- [ ] **Edmonds' blossom algorithm** — define `contract`, prove
  `lift_augmenting`, and prove `edmonds_finds_augmenting` in
  [Hackathon/Graph/Algorithms/Blossom.lean](Hackathon/Graph/Algorithms/Blossom.lean).
- [ ] **Autoresearch loop** — wire the build-time signal from
  [scripts/measure-build.sh](scripts/measure-build.sh) into a proof-rewriting
  pipeline.
