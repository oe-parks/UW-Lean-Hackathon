// Replays a precomputed event trace on a Cytoscape instance.
// The algorithm core has already decided everything; the player only
// renders. This separation is what makes the animation an exact
// reflection of the algorithm.

import { edgeKey } from './graph.js';

const VERTEX_CLASSES = ['vExposed', 'vMatched', 'vForestEven', 'vForestOdd'];
const EDGE_CLASSES = ['eMatching', 'eForest', 'eAugment', 'eInspect'];

export class Player {
  constructor(cy, events, hooks = {}) {
    this.cy = cy;
    this.events = events;
    this.hooks = hooks;            // { onStep(idx, event), onDone() }
    this.idx = -1;
    this.timer = null;
    this.delayMs = 700;
    this._matching = new Set();    // edgeKey strings, current matching
    this._forestVerts = new Map(); // vid -> 'even' | 'odd'
    this._forestEdges = new Set(); // edgeKey strings (forest tree edges)
    this._blossomGroups = [];      // arrays of vids that have been contracted
    this._inspect = null;          // edgeKey or null
    this._lastVisited = null;
    this._augHighlight = null;     // {pathEdges, vertices} or null
    this.applyClasses();
  }

  setSpeed(ms) { this.delayMs = ms; }

  reset() {
    this.stop();
    this.idx = -1;
    this._matching.clear();
    this._forestVerts.clear();
    this._forestEdges.clear();
    this._blossomGroups = [];
    this._inspect = null;
    this._lastVisited = null;
    this._augHighlight = null;
    this.applyClasses();
    this.hooks.onStep?.(this.idx, null);
  }

  isAtEnd() { return this.idx >= this.events.length - 1; }
  isAtStart() { return this.idx < 0; }
  totalSteps() { return this.events.length; }
  currentIdx() { return this.idx; }

  stepForward() {
    if (this.isAtEnd()) return false;
    this.idx++;
    this._apply(this.events[this.idx]);
    this.applyClasses();
    this.hooks.onStep?.(this.idx, this.events[this.idx]);
    return true;
  }

  stepBackward() {
    if (this.isAtStart()) return false;
    // Cheap impl: rebuild from scratch up to idx-1.
    const target = this.idx - 1;
    this.reset();
    while (this.idx < target) this.stepForward();
    return true;
  }

  jumpToEnd() {
    while (this.stepForward()) {}
  }

  jumpToStart() { this.reset(); }

  play() {
    if (this.timer) return;
    if (this.isAtEnd()) this.reset();
    const tick = () => {
      const ok = this.stepForward();
      if (!ok) {
        this.stop();
        this.hooks.onDone?.();
        return;
      }
      this.timer = setTimeout(tick, this.delayMs);
    };
    tick();
  }

  stop() {
    if (this.timer) { clearTimeout(this.timer); this.timer = null; }
  }

  _apply(ev) {
    // Clear per-step transient highlights (inspect, last-visit pulse).
    this._inspect = null;
    if (ev.kind !== 'augment' && ev.kind !== 'pathFound') {
      // augmenting events keep the augHighlight visible briefly
    }

    switch (ev.kind) {
      case 'init':
        for (const [u, v] of ev.matching) this._matching.add(edgeKey(u, v));
        break;
      case 'pickRoot':
        // start of a new BFS — clear forest from previous attempt
        this._forestVerts.clear();
        this._forestEdges.clear();
        this._blossomGroups = [];
        this._forestVerts.set(ev.root, 'even');
        this._lastVisited = ev.root;
        this._augHighlight = null;
        break;
      case 'visit':
        this._lastVisited = ev.vertex;
        break;
      case 'inspectEdge':
        this._inspect = edgeKey(ev.from, ev.to);
        break;
      case 'growForest':
        this._forestVerts.set(ev.odd, 'odd');
        this._forestVerts.set(ev.even, 'even');
        this._forestEdges.add(edgeKey(ev.from, ev.odd));
        this._forestEdges.add(edgeKey(ev.odd, ev.even));
        break;
      case 'blossomDetected':
        // visual: the blossom cycle highlighted; closing edge featured
        this._inspect = edgeKey(ev.closingEdge[0], ev.closingEdge[1]);
        break;
      case 'contract':
        this._blossomGroups.push([...ev.vertices]);
        // After contraction, every vertex in the blossom is even-level.
        for (const v of ev.vertices) this._forestVerts.set(v, 'even');
        break;
      case 'pathFound':
        this._augHighlight = {
          vertices: new Set(ev.path),
          edges: new Set(),
        };
        for (let i = 0; i + 1 < ev.path.length; i++) {
          this._augHighlight.edges.add(edgeKey(ev.path[i], ev.path[i + 1]));
        }
        break;
      case 'noPathFromRoot':
        this._forestVerts.clear();
        this._forestEdges.clear();
        this._blossomGroups = [];
        break;
      case 'augment': {
        // Apply symmetric difference to current matching set.
        for (const [u, v] of ev.pathEdges) {
          const k = edgeKey(u, v);
          if (this._matching.has(k)) this._matching.delete(k);
          else this._matching.add(k);
        }
        // Clear forest after a successful augmentation.
        this._forestVerts.clear();
        this._forestEdges.clear();
        this._blossomGroups = [];
        // Keep augHighlight to show the path one more frame.
        break;
      }
      case 'done':
        this._forestVerts.clear();
        this._forestEdges.clear();
        this._blossomGroups = [];
        this._augHighlight = null;
        break;
    }
  }

  applyClasses() {
    const cy = this.cy;
    cy.batch(() => {
      // Reset all classes.
      cy.nodes().removeClass(VERTEX_CLASSES.join(' ') + ' inspected augHL');
      cy.edges().removeClass(EDGE_CLASSES.join(' ') + ' augHL inspected');

      // Vertex matched/exposed.
      const matchedV = new Set();
      for (const k of this._matching) {
        const [a, b] = k.split('|').map(Number);
        matchedV.add(a); matchedV.add(b);
      }
      cy.nodes().forEach(n => {
        const id = vid(n.id());
        if (matchedV.has(id)) n.addClass('vMatched');
        else n.addClass('vExposed');
      });

      // Forest level overrides matched/exposed colour.
      for (const [v, level] of this._forestVerts) {
        const n = cy.getElementById(String(v));
        if (n.length === 0) continue;
        n.removeClass('vMatched vExposed');
        n.addClass(level === 'even' ? 'vForestEven' : 'vForestOdd');
      }

      // Edge classes.
      cy.edges().forEach(e => {
        const u = vid(e.data('source'));
        const v = vid(e.data('target'));
        const k = edgeKey(u, v);
        if (this._matching.has(k)) e.addClass('eMatching');
        if (this._forestEdges.has(k)) e.addClass('eForest');
        if (this._inspect === k) e.addClass('eInspect inspected');
        if (this._augHighlight?.edges.has(k)) e.addClass('eAugment augHL');
      });

      // Augmenting path vertex glow.
      if (this._augHighlight) {
        for (const v of this._augHighlight.vertices) {
          cy.getElementById(String(v)).addClass('augHL');
        }
      }

      // Blossom groups: draw a ring overlay using a 'blossom' class on
      // member nodes (rendered via stylesheet).
      cy.nodes().removeClass('inBlossom');
      for (const group of this._blossomGroups) {
        for (const v of group) cy.getElementById(String(v)).addClass('inBlossom');
      }

      // Last-visited pulse.
      if (this._lastVisited !== null && this._lastVisited !== undefined) {
        cy.getElementById(String(this._lastVisited)).addClass('justVisited');
        // Other nodes shouldn't carry this class.
        cy.nodes().forEach(n => {
          if (vid(n.id()) !== this._lastVisited) n.removeClass('justVisited');
        });
      }
    });
  }
}

function vid(s) {
  const n = Number(s);
  return Number.isNaN(n) ? s : n;
}
