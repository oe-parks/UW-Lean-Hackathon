// Simple undirected graph data model.
// Vertices are integers 0..n-1 (or any value with stable === equality).
// Edges are unordered pairs; we canonicalise as [min, max] when storing in sets.

export function edgeKey(u, v) {
  return u < v ? `${u}|${v}` : `${v}|${u}`;
}

export class Graph {
  constructor() {
    this.vertices = new Set();
    this.adj = new Map();         // v -> Set of neighbours
    this._edgeSet = new Set();    // canonical edgeKey strings
  }

  static fromJSON(obj) {
    const g = new Graph();
    for (const v of obj.vertices ?? []) g.addVertex(v);
    for (const [u, v] of obj.edges ?? []) g.addEdge(u, v);
    return g;
  }

  toJSON() {
    return {
      vertices: [...this.vertices],
      edges: this.edges().map(([u, v]) => [u, v]),
    };
  }

  clone() {
    return Graph.fromJSON(this.toJSON());
  }

  addVertex(v) {
    if (this.vertices.has(v)) return;
    this.vertices.add(v);
    this.adj.set(v, new Set());
  }

  removeVertex(v) {
    if (!this.vertices.has(v)) return;
    for (const u of this.adj.get(v)) {
      this.adj.get(u).delete(v);
      this._edgeSet.delete(edgeKey(u, v));
    }
    this.adj.delete(v);
    this.vertices.delete(v);
  }

  hasEdge(u, v) {
    return this._edgeSet.has(edgeKey(u, v));
  }

  addEdge(u, v) {
    if (u === v) return false;          // no self-loops in a SimpleGraph
    if (!this.vertices.has(u) || !this.vertices.has(v)) return false;
    if (this.hasEdge(u, v)) return false;
    this.adj.get(u).add(v);
    this.adj.get(v).add(u);
    this._edgeSet.add(edgeKey(u, v));
    return true;
  }

  removeEdge(u, v) {
    if (!this.hasEdge(u, v)) return false;
    this.adj.get(u).delete(v);
    this.adj.get(v).delete(u);
    this._edgeSet.delete(edgeKey(u, v));
    return true;
  }

  toggleEdge(u, v) {
    return this.hasEdge(u, v) ? (this.removeEdge(u, v), false) : (this.addEdge(u, v), true);
  }

  neighbours(v) {
    return [...(this.adj.get(v) ?? [])];
  }

  edges() {
    const out = [];
    for (const k of this._edgeSet) {
      const [a, b] = k.split('|').map(Number);
      out.push([a, b]);
    }
    return out;
  }

  vertexCount() { return this.vertices.size; }
  edgeCount()   { return this._edgeSet.size; }
}

// A matching is a Map from vertex -> matched partner (or absent if unmatched).
export class Matching {
  constructor(pairs = []) {
    this.match = new Map();
    for (const [u, v] of pairs) this.set(u, v);
  }
  static fromMap(m) {
    const x = new Matching();
    for (const [u, v] of m) x.match.set(u, v);
    return x;
  }
  clone() { return Matching.fromMap(this.match); }

  set(u, v) {
    this.match.set(u, v);
    this.match.set(v, u);
  }
  unset(u) {
    const v = this.match.get(u);
    if (v !== undefined) {
      this.match.delete(u);
      this.match.delete(v);
    }
  }
  partner(v)    { return this.match.get(v); }
  isMatched(v)  { return this.match.has(v); }
  isExposed(v)  { return !this.match.has(v); }

  edges() {
    const seen = new Set();
    const out = [];
    for (const [u, v] of this.match) {
      const k = edgeKey(u, v);
      if (seen.has(k)) continue;
      seen.add(k);
      out.push([Math.min(u, v), Math.max(u, v)]);
    }
    return out;
  }

  // Symmetric difference with a list of edges (the augmenting path).
  symDiff(pathEdges) {
    const next = this.clone();
    for (const [u, v] of pathEdges) {
      if (next.partner(u) === v) {
        next.unset(u);
      } else {
        // Before adding, drop any prior partners.
        if (next.isMatched(u)) next.unset(u);
        if (next.isMatched(v)) next.unset(v);
        next.set(u, v);
      }
    }
    return next;
  }

  size() { return this.edges().length; }
}
