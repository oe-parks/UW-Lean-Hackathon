// Edmonds' Blossom Algorithm — finds a maximum matching in a general graph,
// emitting an event trace suitable for step-by-step animation.
//
// Implementation follows the classical formulation (cp-algorithms / e-maxx):
// for each unmatched vertex `root`, run a BFS that grows an alternating forest.
// When two even-level vertices in the same tree are joined by a non-matching
// edge, a blossom is detected; its vertices are merged via base[] and the
// parent pointers around the cycle are rewritten so that walking parent[]
// later still yields a valid alternating path *through* the blossom (this
// substitutes for an explicit lift pass).
//
// Trace events:
//   { kind: 'init', matching }
//   { kind: 'pickRoot', root }
//   { kind: 'visit', vertex }                                  -- popped from BFS queue
//   { kind: 'inspectEdge', from, to }
//   { kind: 'growForest', from, odd, even }                    -- (from,odd) non-M, (odd,even) M
//   { kind: 'blossomDetected', vertices, base, closingEdge }
//   { kind: 'contract', vertices, base }                       -- after rewiring
//   { kind: 'pathFound', path }
//   { kind: 'noPathFromRoot', root }
//   { kind: 'augment', path, pathEdges, newMatching }
//   { kind: 'done', matching }

import { Matching } from './graph.js';

function pairwise(arr) {
  const out = [];
  for (let i = 0; i + 1 < arr.length; i++) out.push([arr[i], arr[i + 1]]);
  return out;
}

function findLCA(a, b, base, parent, M) {
  // Walk up from `a`, marking visited bases; then walk up from `b`,
  // returning the first base already marked. "Up" means: hop along the
  // matched edge (one odd level), then along the parent edge (back to even).
  const seen = new Set();
  let cur = a;
  while (true) {
    cur = base.get(cur);
    seen.add(cur);
    const m = M.partner(cur);
    if (m === undefined) break;            // root reached
    cur = parent.get(m);
    if (cur === undefined) break;          // safety
  }
  cur = b;
  while (true) {
    cur = base.get(cur);
    if (seen.has(cur)) return cur;
    const m = M.partner(cur);
    if (m === undefined) return null;      // not in same tree (shouldn't happen)
    cur = parent.get(m);
    if (cur === undefined) return null;
  }
}

function markPath(v, b, child, base, parent, blossomMark, M) {
  // Walk from v upward to base b, marking blossom membership and rewiring
  // parent pointers so that walking parent[] from inside the blossom now
  // crosses to the other half of the cycle.
  while (base.get(v) !== b) {
    blossomMark.add(base.get(v));
    blossomMark.add(base.get(M.partner(v)));
    parent.set(v, child);
    child = M.partner(v);
    v = parent.get(M.partner(v));
  }
}

function reconstructPath(endpoint, parent, M) {
  // endpoint is the unmatched vertex where the augmenting path ends.
  // Walk: endpoint → parent(endpoint) → match(parent) → parent(match) → ...
  const path = [endpoint];
  let cur = parent.get(endpoint);
  while (cur !== undefined && cur !== null) {
    path.push(cur);
    const m = M.partner(cur);
    if (m === undefined) break;            // reached root
    path.push(m);
    cur = parent.get(m);
  }
  return path;
}

function findAugmentingPath(graph, M, events, root) {
  const verts = [...graph.vertices];
  const used = new Set();
  const parent = new Map();          // odd-level non-root vertices have this set
  const base = new Map();
  const queue = [];

  for (const v of verts) base.set(v, v);

  used.add(root);
  queue.push(root);
  events.push({ kind: 'pickRoot', root });

  while (queue.length > 0) {
    const v = queue.shift();
    events.push({ kind: 'visit', vertex: v });

    for (const to of graph.neighbours(v)) {
      if (base.get(v) === base.get(to)) continue;     // same blossom
      if (M.partner(v) === to) continue;              // matched edge — skip

      events.push({ kind: 'inspectEdge', from: v, to });

      // Is `to` in the forest at an even level?
      //   - to === root, or
      //   - to is matched and its partner has parent set (i.e., its partner
      //     is an odd-level forest vertex).
      const toEvenInForest =
        to === root ||
        (M.isMatched(to) && parent.has(M.partner(to)));

      if (toEvenInForest) {
        // Blossom!
        const lca = findLCA(v, to, base, parent, M);
        const blossomMark = new Set();
        markPath(v, lca, to, base, parent, blossomMark, M);
        markPath(to, lca, v, base, parent, blossomMark, M);

        const blossomVerts = [];
        for (const i of verts) {
          if (blossomMark.has(base.get(i))) {
            blossomVerts.push(i);
            base.set(i, lca);
            if (!used.has(i)) {
              used.add(i);
              queue.push(i);
            }
          }
        }
        events.push({
          kind: 'blossomDetected',
          vertices: blossomVerts,
          base: lca,
          closingEdge: [v, to],
        });
        events.push({ kind: 'contract', vertices: blossomVerts, base: lca });
      } else if (!parent.has(to)) {
        // `to` is not yet in the forest. Two sub-cases.
        parent.set(to, v);
        if (!M.isMatched(to)) {
          // Augmenting path ends here.
          const path = reconstructPath(to, parent, M);
          events.push({ kind: 'pathFound', path });
          return path;
        } else {
          const w = M.partner(to);
          used.add(w);
          queue.push(w);
          events.push({ kind: 'growForest', from: v, odd: to, even: w });
        }
      }
      // else: `to` is in forest at odd level — skip.
    }
  }

  events.push({ kind: 'noPathFromRoot', root });
  return null;
}

export function bloomMatching(graph, initialMatching = new Matching()) {
  const events = [];
  const M = initialMatching.clone();
  events.push({ kind: 'init', matching: M.edges() });

  const verts = [...graph.vertices].sort((a, b) => {
    if (typeof a === 'number' && typeof b === 'number') return a - b;
    return String(a).localeCompare(String(b));
  });

  // Outer loop: keep finding augmenting paths from any unmatched vertex
  // until none exist (Berge's theorem ⇒ M is then maximum).
  outer: while (true) {
    for (const r of verts) {
      if (M.isMatched(r)) continue;
      const path = findAugmentingPath(graph, M, events, r);
      if (path !== null) {
        const pathEdges = pairwise(path);
        const newM = M.symDiff(pathEdges);
        M.match = newM.match;
        events.push({
          kind: 'augment',
          path,
          pathEdges,
          newMatching: M.edges(),
        });
        continue outer;     // restart scan from M's new state
      }
    }
    break;                  // no augmenting path from any unmatched vertex
  }

  events.push({ kind: 'done', matching: M.edges() });
  return { matching: M, events };
}
