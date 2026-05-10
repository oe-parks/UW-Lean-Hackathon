# Hackathon

Solution submitted by **Team Blossom** for the **UW Lean Hackathon 2026**.

## Instruction to Compile

The project is a standard Lake package (Lean 4.29.1 + Mathlib v4.29.1).


```bash
# one-time setup: fetch dependencies and download the Mathlib build cache
lake update

# subsequent builds
lake build
```

To compile the project, measure compilation time, and report the number of `sorry` placeholders and build errors in one shot, use the helper script:

```bash
./scripts/measure-build.sh
```

The script prints a human-readable summary and also writes a machine-readable report to `build-report.json` (elapsed time, exit status, error count, `sorry`-warning count, per-file `sorry` breakdown). It is the primary signal consumed by the autoresearch loop described below.

## Result

Formalized the correctness and complexity of Edmond Blossom algorithm in Lean and invented a novel autoresearch pipeline that rewrite the proof tactics and improve the lean compilation time.

## Proof Graph Algorithm

We formalize graph theory from the ground up in Lean 4. We start by defining the basic objects and theorems — vertices, edges, paths, matchings, girth, and so on — sufficient to state and reason about the matching problem.

On top of that foundation, we design a small toy language: we give it an explicit syntax and a sound operational semantics tailored to expressing the blossom algorithm. We then implement Edmonds' blossom algorithm in that language and verify its correctness in Lean.

## Theorem diagram 

Here we show the dependency diagram of the whole theorem, and an animation of how these Lemmas/Theorems are used in real production.

![Augmenting Path Discovery](visuals/augmenting_path_manim.gif)

## Optimization

To accelerate proof development we build an **autoresearch loop** that closes on itself in two stages.

First, we instrument compilation so we can measure build time as a primary signal. Second, we drive an autoresearch pipeline that rewrites proofs and optimizes the compile time of the full workflow end-to-end.

## Contributors

This project was developed as part of the UW Lean Hackathon.

### Core Team

- **John Ye** — [GitHub](https://github.com/yezhuoyang) | [Website](https://yezhuoyang.github.io/)
- **Nicholas Mundy** - [GitHub](https://github.com/nmmundy)
- **Kieran Rullman** - [GitHub](https://github.com/kieranrullman) 
- **Owen Parks** - [GitHub](https://github.com/oe-parks) | [Website](https://owenparks.com)

## TODO List

Tracked against the current `sorry` placeholders in the source tree.

- [ ] **Toy graph foundation** — fill in the elementary lemmas in [Hackathon/Graph/Toy/Lemmas.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Toy/Lemmas.lean) (13 open goals).
- [x] **Bridge to Mathlib `SimpleGraph`** — round-trip established in [Hackathon/Graph/Toy/Bridge.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Toy/Bridge.lean).
- [ ] **Walks and paths** — finish the walk lemmas in [Hackathon/Graph/Walks.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Walks.lean) (6 open).
- [ ] **Matchings** — complete [Hackathon/Graph/Matching.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Matching.lean) (4 open).
- [ ] **Augmenting paths** — complete [Hackathon/Graph/Augment.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Augment.lean) (4 open).
- [ ] **Berge's theorem** — close the three remaining goals in [Hackathon/Graph/Berge.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Berge.lean).
- [ ] **Bipartite matching (Hungarian / Hopcroft–Karp)** — implement `augmentOnce` and prove soundness/progress/completeness in [Hackathon/Graph/Algorithms/Bipartite.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Algorithms/Bipartite.lean).
- [ ] **Edmonds' blossom algorithm** — define `contract`, prove `lift_augmenting`, and prove `edmonds_finds_augmenting` in [Hackathon/Graph/Algorithms/Blossom.lean](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/Hackathon/Graph/Algorithms/Blossom.lean).
- [ ] **Autoresearch loop** — wire the build-time signal from [scripts/measure-build.sh](https://github.com/oe-parks/UW-Lean-Hackathon/blob/main/scripts/measure-build.sh) into a proof-rewriting pipeline.