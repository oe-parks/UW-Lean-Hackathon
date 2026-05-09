// Top-level wiring: editor ↔ algorithm ↔ player ↔ DOM controls.

import { Graph, Matching } from './graph.js';
import { bloomMatching } from './blossom.js';
import { verify } from './verifier.js';
import { Editor } from './editor.js';
import { Player } from './player.js';
import { PRESETS } from './presets.js';

const $ = (id) => document.getElementById(id);

// Cytoscape stylesheet — drives all visual states the player toggles.
const CY_STYLE = [
  {
    selector: 'node',
    style: {
      label: 'data(label)',
      'text-valign': 'center',
      'text-halign': 'center',
      color: '#0e1116',
      'font-size': 13,
      'font-weight': 'bold',
      'background-color': '#8b949e',
      'border-width': 2,
      'border-color': '#30363d',
      width: 32, height: 32,
      'transition-property': 'background-color, border-color, border-width',
      'transition-duration': 150,
    },
  },
  { selector: 'node.vExposed',     style: { 'background-color': '#f0883e' } },
  { selector: 'node.vMatched',     style: { 'background-color': '#58a6ff' } },
  { selector: 'node.vForestEven',  style: { 'background-color': '#3fb950', 'border-color': '#3fb950' } },
  { selector: 'node.vForestOdd',   style: { 'background-color': '#d29922', 'border-color': '#d29922' } },
  { selector: 'node.justVisited',  style: { 'border-color': '#e6edf3', 'border-width': 4 } },
  { selector: 'node.augHL',        style: { 'border-color': '#f85149', 'border-width': 4 } },
  { selector: 'node.inBlossom',    style: { 'border-color': '#bc8cff', 'border-width': 5, 'border-style': 'dashed' } },
  { selector: 'node.pending',      style: { 'border-color': '#58a6ff', 'border-width': 4, 'border-style': 'dashed' } },

  {
    selector: 'edge',
    style: {
      'curve-style': 'straight',
      'line-color': '#6e7681',
      width: 2,
      'transition-property': 'line-color, width',
      'transition-duration': 150,
    },
  },
  { selector: 'edge.eMatching',  style: { 'line-color': '#58a6ff', width: 5 } },
  { selector: 'edge.eForest',    style: { 'line-color': '#d29922', width: 4 } },
  { selector: 'edge.inspected',  style: { 'line-color': '#e6edf3', width: 4, 'line-style': 'dashed' } },
  { selector: 'edge.eAugment',   style: { 'line-color': '#f85149', width: 6 } },
];

// ---- state ----
let graph = new Graph();
let cy = null;
let editor = null;
let player = null;
let buildResult = null;     // { matching, events }
let mode = 'edit';

// ---- UI helpers ----
function setMode(next) {
  mode = next;
  $('modeEdit').classList.toggle('active', next === 'edit');
  $('modeRun').classList.toggle('active', next === 'run');
  $('editorPanel').hidden = next !== 'edit';
  $('runPanel').hidden = next !== 'run';
  $('resultPanel').hidden = next !== 'run';
  if (editor) editor.setEnabled(next === 'edit');
  if (next === 'edit') {
    if (player) { player.stop(); player.reset(); }
  }
}

function refreshCount() {
  $('vCount').textContent = graph.vertexCount();
}

function setStatus(msg) {
  $('status').textContent = msg ?? '';
}

function fmtEvent(ev) {
  switch (ev.kind) {
    case 'init':         return `init: |M|=${ev.matching.length}`;
    case 'pickRoot':     return `pick root r=${ev.root}`;
    case 'visit':        return `visit ${ev.vertex}`;
    case 'inspectEdge':  return `inspect (${ev.from},${ev.to})`;
    case 'growForest':   return `grow forest: odd=${ev.odd}, even=${ev.even}`;
    case 'blossomDetected': return `blossom! verts={${ev.vertices.join(',')}}, base=${ev.base}`;
    case 'contract':     return `contract → base ${ev.base}`;
    case 'pathFound':    return `augmenting path: ${ev.path.join('→')}`;
    case 'noPathFromRoot': return `no path from root ${ev.root}`;
    case 'augment':      return `augment along ${ev.path.join('→')} (|M|=${ev.newMatching.length})`;
    case 'done':         return `done. final |M|=${ev.matching.length}`;
    default:             return ev.kind;
  }
}

function renderLog() {
  const log = $('log');
  log.innerHTML = '';
  for (let i = 0; i < (buildResult?.events.length ?? 0); i++) {
    const li = document.createElement('li');
    li.textContent = fmtEvent(buildResult.events[i]);
    li.dataset.idx = i;
    log.appendChild(li);
  }
}

function highlightLog(idx) {
  const log = $('log');
  for (const li of log.children) {
    li.classList.toggle('current', Number(li.dataset.idx) === idx);
    if (Number(li.dataset.idx) === idx) {
      li.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
    }
  }
}

function updateProgress(idx, total) {
  $('progress').max = Math.max(total, 1);
  $('progress').value = idx + 1;
  $('progressLabel').textContent = `${idx + 1} / ${total}`;
}

function showVerifier(result) {
  const out = $('verifierOut');
  out.classList.remove('ok', 'bad');
  if (result.ok) {
    out.classList.add('ok');
    out.innerHTML = `<div class="kv">
      <span>Status</span><span>✓ matching is valid and maximum</span>
      <span>Size</span><span>${result.size}</span>
    </div>`;
  } else {
    out.classList.add('bad');
    out.innerHTML = `<div class="kv">
      <span>Status</span><span>✗ verifier failed</span>
      <span>Size</span><span>${result.size}</span>
      <span>Issues</span><span>${result.issues.join('; ')}</span>
    </div>`;
  }
}

// ---- preset / JSON ----
function loadPreset(p) {
  graph = new Graph();
  for (const v of p.vertices) graph.addVertex(v);
  for (const [u, v] of p.edges) graph.addEdge(u, v);
  editor.graph = graph;
  editor.rebuildFromGraph(p.positions ?? {});
  if (p.note) setStatus(p.note);
  refreshCount();
  if (player) player.reset();
}

function clearGraph() {
  graph = new Graph();
  editor.graph = graph;
  editor.rebuildFromGraph();
  refreshCount();
  setStatus('');
  if (player) player.reset();
}

function exportJson() {
  $('jsonArea').value = JSON.stringify(graph.toJSON(), null, 2);
}

function importJson() {
  try {
    const obj = JSON.parse($('jsonArea').value);
    const g = Graph.fromJSON(obj);
    graph = g;
    editor.graph = graph;
    editor.rebuildFromGraph();
    refreshCount();
    setStatus(`imported: ${g.vertexCount()} vertices, ${g.edgeCount()} edges`);
  } catch (err) {
    setStatus(`import failed: ${err.message}`);
  }
}

// ---- run / build ----
function buildTrace() {
  buildResult = bloomMatching(graph, new Matching());
  if (player) player.stop();
  player = new Player(cy, buildResult.events, {
    onStep: (idx) => {
      if (idx >= 0 && idx < buildResult.events.length) {
        highlightLog(idx);
        updateProgress(idx, buildResult.events.length);
      } else {
        updateProgress(-1, buildResult.events.length);
        highlightLog(-1);
      }
    },
    onDone: () => {
      const result = verify(graph, buildResult.matching);
      showVerifier(result);
    },
  });
  renderLog();
  updateProgress(-1, buildResult.events.length);
  setStatus(`built ${buildResult.events.length} events. Press ▶ to play.`);
}

function bindRunControls() {
  $('runBuild').addEventListener('click', buildTrace);
  $('runReset').addEventListener('click', () => { player?.reset(); updateProgress(-1, buildResult?.events.length ?? 0); });
  $('stepBack').addEventListener('click', () => { player?.jumpToStart(); updateProgress(-1, buildResult?.events.length ?? 0); });
  $('stepPrev').addEventListener('click', () => player?.stepBackward());
  $('stepNext').addEventListener('click', () => player?.stepForward());
  $('stepEnd').addEventListener('click', () => {
    player?.jumpToEnd();
    if (player && buildResult) {
      const result = verify(graph, buildResult.matching);
      showVerifier(result);
    }
  });
  $('playBtn').addEventListener('click', () => {
    if (!player) return;
    if (player.timer) {
      player.stop();
      $('playBtn').textContent = '▶ Play';
    } else {
      player.play();
      $('playBtn').textContent = '⏸ Pause';
    }
  });
  $('speed').addEventListener('input', (e) => {
    const v = Number(e.target.value);
    $('speedLabel').textContent = `${v} ms`;
    player?.setSpeed(v);
  });
}

// ---- init ----
function init() {
  cy = cytoscape({
    container: $('cy'),
    style: CY_STYLE,
    minZoom: 0.2,
    maxZoom: 4,
    wheelSensitivity: 0.15,
  });

  editor = new Editor(cy, graph, {
    onChange: () => {
      refreshCount();
      // editing invalidates any prior trace
      buildResult = null;
      if (player) { player.stop(); player.reset(); }
    },
    onWarn: setStatus,
  });

  // mode buttons
  $('modeEdit').addEventListener('click', () => setMode('edit'));
  $('modeRun').addEventListener('click', () => {
    setMode('run');
    if (!buildResult) buildTrace();
  });

  // preset dropdown
  const sel = $('presetSelect');
  for (let i = 0; i < PRESETS.length; i++) {
    const opt = document.createElement('option');
    opt.value = String(i);
    opt.textContent = PRESETS[i].name;
    sel.appendChild(opt);
  }
  sel.addEventListener('change', (e) => {
    const i = Number(e.target.value);
    if (Number.isFinite(i) && PRESETS[i]) loadPreset(PRESETS[i]);
  });

  // clear / json
  $('clearBtn').addEventListener('click', clearGraph);
  $('jsonImport').addEventListener('click', importJson);
  $('jsonExport').addEventListener('click', exportJson);

  bindRunControls();

  setMode('edit');

  // start with first preset for delight on first load
  loadPreset(PRESETS[0]);
  sel.value = '0';
}

if (typeof cytoscape === 'undefined') {
  document.body.innerHTML = '<p style="padding:24px;color:#f85149">Cytoscape failed to load. Are you offline? The page needs <code>https://unpkg.com/cytoscape</code>.</p>';
} else {
  init();
}
