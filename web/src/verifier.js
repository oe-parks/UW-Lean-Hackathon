// Cross-check the algorithm's output against the matching spec:
//   1. Output is a valid matching (no two edges share a vertex).
//   2. Every output edge is an edge of the input graph.
//   3. There is no M-augmenting path remaining (i.e. M is maximum).
// (3) is brute-forced by DFS from each unmatched vertex; only feasible on
// small graphs, but this is a step-by-step visualizer so that's fine.

import { Matching, edgeKey } from './graph.js';

export function verify(graph, matching) {
  const issues = [];

  // 1. Output is a valid matching.
  const seen = new Set();
  for (const [u, v] of matching.edges()) {
    if (seen.has(u)) issues.push(`vertex ${u} is in two matching edges`);
    if (seen.has(v)) issues.push(`vertex ${v} is in two matching edges`);
    seen.add(u);
    seen.add(v);
    if (!graph.hasEdge(u, v)) issues.push(`matching edge (${u},${v}) is not in the graph`);
  }

  // 2. (Implicit above.)

  // 3. Maximum: search for any augmenting path.
  const aug = findAugmentingPathBrute(graph, matching);
  if (aug !== null) {
    issues.push(`not maximum: augmenting path ${aug.join(' → ')} still exists`);
  }

  return {
    ok: issues.length === 0,
    issues,
    size: matching.edges().length,
  };
}

// Brute-force DFS for any M-alternating path from an unmatched vertex to
// another unmatched vertex. Used only as a tripwire — algorithmically
// distinct from the blossom code we're verifying.
function findAugmentingPathBrute(graph, M) {
  const verts = [...graph.vertices];
  for (const start of verts) {
    if (M.isMatched(start)) continue;
    const visitedEdges = new Set();
    const stack = [{ v: start, path: [start], lastWasMatched: null }];
    while (stack.length > 0) {
      const { v, path, lastWasMatched } = stack.pop();
      for (const u of graph.neighbours(v)) {
        const matched = M.partner(v) === u;
        // Alternation: each step's matched-ness must flip the previous.
        if (lastWasMatched !== null && matched === lastWasMatched) continue;
        const ek = edgeKey(v, u);
        if (visitedEdges.has(ek)) continue;
        // Avoid trivial cycles in the same simple path.
        if (path.includes(u)) continue;
        const newPath = [...path, u];
        if (!matched && !M.isMatched(u) && u !== start) {
          // augmenting (start unmatched, end unmatched, alternates with non-M first)
          // The first edge from `start` (which is unmatched) must be non-matched.
          // We need at least one edge.
          return newPath;
        }
        // Continue DFS, marking this edge to avoid trivial backtracking.
        const next = { v: u, path: newPath, lastWasMatched: matched };
        stack.push(next);
      }
    }
  }
  return null;
}
