# Edmonds' blossom — step-by-step matching visualizer

A browser visualization that runs Edmonds' blossom algorithm on a user-supplied
graph and animates every step: BFS frontier expansion, alternating-forest
growth, blossom detection and contraction, augmenting-path discovery, and the
final symmetric-difference augmentation.

It's a companion to the Lean development under
[`Hackathon/Graph/Algorithms/Blossom.lean`](../Hackathon/Graph/Algorithms/Blossom.lean).
The animation is *not* a separate algorithm — the algorithm runs once, emits a
trace of discrete events, and the player replays those events. So whatever you
see on the canvas is exactly what the algorithm did.

## Running

No build step. Three options, in order of convenience:

**1. Use the included script** — starts a local server on `http://127.0.0.1:8000` and opens your browser:

```bash
./web/serve.sh                 # local only (recommended)
./web/serve.sh -p 8080         # custom port
./web/serve.sh --public        # bind 0.0.0.0 for LAN/public access
./web/serve.sh -h              # help
```

**2. Or any static server** in the `web/` directory:

```bash
cd web && python3 -m http.server 8000
```

**3. Or open [`index.html`](index.html) directly** — works for most features but some browsers block `file://` module imports:

```bash
xdg-open web/index.html        # Linux
open web/index.html            # macOS
```

Cytoscape.js loads from `unpkg.com`; you need internet access on first load.

## Using

- **Edit mode** (default): click empty canvas to add a vertex; click two
  vertices in turn to toggle the edge between them; shift- or right-click a
  vertex to delete it. Soft cap: 30 vertices.
- **Preset dropdown**: load a canonical example (triangle blossom, K3,3, Petersen, …).
- **Run mode**: press *Run* in the top bar. The trace builds once, then you
  can ▶ play, ⏭ step, ⏮ reset, or scrub via the event log.

## Architecture

```
src/
├── graph.js        Graph + Matching data structures.
├── blossom.js      Edmonds' algorithm. Pure: graph → { matching, events }.
├── verifier.js     Post-run sanity: is matching valid + maximum?
├── presets.js      Sample graphs.
├── editor.js       Click-to-edit on top of Cytoscape.
├── player.js       Replays events; only this file renders.
└── main.js         Wiring + DOM controls.
```

Key invariant: `blossom.js` has no DOM dependency. It can be used standalone
to compute a maximum matching on any graph; the `events` array is the
side-channel for animation.

### Event types

Every algorithmic step emits one event. The animation player consumes events
and toggles CSS classes on the Cytoscape elements — no parallel logic.

| Event | When |
|---|---|
| `init` | start; carries the initial matching |
| `pickRoot` | a new BFS starts from an unmatched vertex |
| `visit` | popped a vertex from the BFS queue |
| `inspectEdge` | examining an edge incident to the visited vertex |
| `growForest` | added an odd-level vertex and its M-partner to the forest |
| `blossomDetected` | found a non-M edge between two even-level vertices in the same tree |
| `contract` | the blossom's vertices have been merged via base-pointer rewiring |
| `pathFound` | reached an unmatched vertex (or another tree's root) — augmenting path identified |
| `noPathFromRoot` | BFS exhausted with no augmenting path from this root |
| `augment` | applied symmetric difference; the matching grew by one edge |
| `done` | no more augmenting paths exist; matching is maximum |

## Verifier

After the trace finishes, [`verifier.js`](src/verifier.js) brute-force checks:

1. The output is a valid matching (no two edges share a vertex; every edge is
   in the input graph).
2. No augmenting path remains (DFS over alternating walks from each unmatched
   vertex).

If either fails, a red banner appears in the right panel. This is an
independent tripwire against the blossom implementation.

## Limitations

- Vertex cap of 30 in the editor (visual clarity). The algorithm itself is fine
  with bigger graphs — drop a larger graph in via the JSON pane.
- Self-loops and multi-edges are silently rejected (the spec uses
  `SimpleGraph`).
- The blossom contraction is shown by drawing a dashed purple ring around the
  member vertices; the vertices stay visible rather than being merged into a
  super-node, which keeps the picture pedagogically clearer.
