// Click-to-edit graph editor on top of a Cytoscape instance.
//   - tap empty canvas: add a vertex
//   - tap two vertices in turn: toggle the edge between them
//   - shift- or right-click a vertex: delete it (and incident edges)

const VERTEX_CAP = 30;

export class Editor {
  constructor(cy, graph, hooks = {}) {
    this.cy = cy;
    this.graph = graph;
    this.hooks = hooks;
    this.cap = VERTEX_CAP;
    this.pendingVertex = null;
    this.nextId = 0;
    this.enabled = true;
    this._bind();
  }

  setEnabled(b) { this.enabled = b; }

  _bind() {
    // Tap on empty space → add vertex.
    this.cy.on('tap', (e) => {
      if (!this.enabled) return;
      if (e.target !== this.cy) return;       // clicked something
      if (this.graph.vertexCount() >= this.cap) {
        this.hooks.onWarn?.(`vertex cap is ${this.cap}`);
        return;
      }
      const id = this._freshId();
      const pos = e.position;
      this.graph.addVertex(id);
      this.cy.add({
        group: 'nodes',
        data: { id: String(id), label: String(id) },
        position: { x: pos.x, y: pos.y },
      });
      this._clearPending();
      this.hooks.onChange?.();
    });

    // Tap on a node → either select first endpoint or finish edge / delete.
    this.cy.on('tap', 'node', (e) => {
      if (!this.enabled) return;
      const ev = e.originalEvent;
      const id = vid(e.target.id());
      if (ev && (ev.shiftKey || ev.button === 2 || ev.altKey)) {
        this._deleteVertex(id);
        return;
      }
      if (this.pendingVertex === null) {
        this.pendingVertex = id;
        this.cy.getElementById(String(id)).addClass('pending');
      } else if (this.pendingVertex === id) {
        // tapping the same vertex twice cancels.
        this._clearPending();
      } else {
        const a = this.pendingVertex, b = id;
        const wasPresent = this.graph.hasEdge(a, b);
        this.graph.toggleEdge(a, b);
        if (wasPresent) {
          const sel = this.cy.edges(`[source = "${a}"][target = "${b}"], [source = "${b}"][target = "${a}"]`);
          sel.remove();
        } else {
          this.cy.add({
            group: 'edges',
            data: { id: `e${a}_${b}`, source: String(a), target: String(b) },
          });
        }
        this._clearPending();
        this.hooks.onChange?.();
      }
    });

    // Right-click on node → delete.
    this.cy.on('cxttap', 'node', (e) => {
      if (!this.enabled) return;
      this._deleteVertex(vid(e.target.id()));
    });
  }

  _deleteVertex(id) {
    this.graph.removeVertex(id);
    this.cy.getElementById(String(id)).remove();
    if (this.pendingVertex === id) this._clearPending();
    this.hooks.onChange?.();
  }

  _clearPending() {
    if (this.pendingVertex !== null) {
      this.cy.getElementById(String(this.pendingVertex)).removeClass('pending');
      this.pendingVertex = null;
    }
  }

  _freshId() {
    while (this.graph.vertices.has(this.nextId)) this.nextId++;
    return this.nextId++;
  }

  rebuildFromGraph(positions = {}) {
    // Clear and redraw everything from this.graph.
    this.cy.elements().remove();
    this.nextId = 0;
    const pos = positions ?? {};
    for (const v of this.graph.vertices) {
      const p = pos[v] ?? { x: 200 + Math.random() * 300, y: 100 + Math.random() * 300 };
      const xy = Array.isArray(p) ? { x: p[0], y: p[1] } : p;
      this.cy.add({
        group: 'nodes',
        data: { id: String(v), label: String(v) },
        position: xy,
      });
      if (typeof v === 'number') this.nextId = Math.max(this.nextId, v + 1);
    }
    for (const [u, v] of this.graph.edges()) {
      this.cy.add({
        group: 'edges',
        data: { id: `e${u}_${v}`, source: String(u), target: String(v) },
      });
    }
    this._clearPending();
  }
}

function vid(s) {
  const n = Number(s);
  return Number.isNaN(n) ? s : n;
}
