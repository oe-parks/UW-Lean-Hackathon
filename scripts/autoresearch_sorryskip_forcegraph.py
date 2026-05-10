# scripts/autoresearch.py
import argparse
import subprocess
import json
import re
import time
import glob
import html
import os
import pathlib
import shutil
import textwrap

FAST_TIMEOUT = 45   # seconds for lake env lean single-file check
DEFAULT_TRACE_DIR = "autoresearch-traces"
DEFAULT_MIN_SPEEDUP_MS = 50
DEFAULT_MEASURE_REPEATS = 1
SORRY_RE = re.compile(r'^(\s*)sorry\b', re.MULTILINE)

# Reject tactics that are not real proofs
CHEAT_RE = re.compile(
    r'\b(sorry|admit|native_decide|exact\?|apply\?|simp\?|decide\?|rw\?|assumption\?|norm_num\?)\b'
)

# Backends: "anthropic" | "ollama" | "openai"
_backend = "anthropic"
_anthropic_client = None
_openai_client = None
anthropic = None
openai_lib = None


def _setup_clients(backend: str):
    global _backend, _anthropic_client, _openai_client, anthropic, openai_lib
    _backend = backend
    if backend == "ollama":
        if openai_lib is None:
            try:
                import openai as openai_lib
            except ImportError as exc:
                raise SystemExit("Missing `openai` package for Ollama backend.") from exc
        _openai_client = openai_lib.OpenAI(
            base_url="http://localhost:11434/v1",
            api_key="ollama",
        )
    elif backend == "openai":
        if openai_lib is None:
            try:
                import openai as openai_lib
            except ImportError as exc:
                raise SystemExit("Missing `openai` package for OpenAI backend.") from exc
        _openai_client = openai_lib.OpenAI()
    else:
        if anthropic is None:
            try:
                import anthropic
            except ImportError as exc:
                raise SystemExit("Missing `anthropic` package for Anthropic backend.") from exc
        _anthropic_client = anthropic.Anthropic()


# ---------------------------------------------------------------------------
# Decision tracing / visualization
# ---------------------------------------------------------------------------

def _safe_slug(value, fallback="target"):
    value = re.sub(r'[^A-Za-z0-9_.-]+', '-', value).strip('-')
    return value[:80] or fallback


def _jsonable(value):
    if isinstance(value, float):
        if value == float('inf'):
            return "inf"
        return round(value, 6)
    if isinstance(value, dict):
        return {k: _jsonable(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_jsonable(v) for v in value]
    return value


def _short_text(value, limit=220):
    value = str(value).replace('\r', '').strip()
    if len(value) <= limit:
        return value
    return value[:limit - 1] + "..."


def _render_html_to_png(html_path, png_path):
    """
    Best-effort conversion of the self-contained trace HTML into a PNG.

    This intentionally has no hard dependency: it tries Python Playwright first,
    then common local Chromium/Chrome executables. The SVG trace is still
    emitted even when PNG rendering is unavailable.
    """
    uri = pathlib.Path(os.path.abspath(html_path)).as_uri()
    playwright_error = None
    try:
        from playwright.sync_api import sync_playwright

        with sync_playwright() as p:
            browser = p.chromium.launch()
            page = browser.new_page(
                viewport={"width": 1600, "height": 1200},
                device_scale_factor=1,
            )
            page.goto(uri, wait_until="networkidle")
            page.screenshot(path=png_path, full_page=True)
            browser.close()
        if os.path.exists(png_path) and os.path.getsize(png_path) > 0:
            return True, "rendered with Playwright"
    except Exception as exc:
        playwright_error = _short_text(exc, 180)

    browser_candidates = [
        os.environ.get("CHROME_BIN"),
        shutil.which("chromium"),
        shutil.which("chromium-browser"),
        shutil.which("google-chrome"),
        shutil.which("google-chrome-stable"),
        shutil.which("chrome"),
        shutil.which("msedge"),
        "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
        "/Applications/Chromium.app/Contents/MacOS/Chromium",
        "/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge",
    ]
    browser_candidates = [
        path for path in browser_candidates
        if path and os.path.exists(path)
    ]
    for browser in browser_candidates:
        for headless_flag in ("--headless=new", "--headless"):
            try:
                result = subprocess.run(
                    [
                        browser,
                        headless_flag,
                        "--disable-gpu",
                        "--hide-scrollbars",
                        "--window-size=1600,1200",
                        f"--screenshot={png_path}",
                        uri,
                    ],
                    capture_output=True,
                    text=True,
                    timeout=45,
                )
                if (
                    result.returncode == 0
                    and os.path.exists(png_path)
                    and os.path.getsize(png_path) > 0
                ):
                    return True, f"rendered with {os.path.basename(browser)}"
            except Exception:
                pass

    reason = "no Playwright or headless Chrome renderer was available"
    if playwright_error:
        reason += f"; Playwright error: {playwright_error}"
    return False, reason


def _print_trace_paths(paths):
    print(f"Decision trace: {paths['html']} (JSON: {paths['json']}, DOT: {paths['dot']})")
    if paths.get("picture"):
        print(f"Trace picture: {paths['picture']}")
    if paths.get("png_error"):
        print(f"PNG render skipped: {paths['png_error']}")


def _write_trace_svg_from_json(json_path, svg_path):
    with open(json_path) as f:
        payload = json.load(f)

    trace = object.__new__(DecisionTrace)
    trace.mode = payload.get("metadata", {}).get("mode", "trace")
    trace.target_file = payload.get("metadata", {}).get("target_file", "")
    trace.output_dir = os.path.dirname(svg_path)
    trace.render_picture = False
    trace.nodes = payload.get("nodes", [])
    trace.edges = payload.get("edges", [])
    trace.root_id = trace.nodes[0]["id"] if trace.nodes else "n0"

    with open(svg_path, "w") as f:
        f.write(trace._to_svg(payload))
    return svg_path


def trace_html_to_picture(html_path, output_path=None):
    html_path = os.path.abspath(html_path)
    if not os.path.exists(html_path):
        raise SystemExit(f"Trace HTML not found: {html_path}")

    base, _ = os.path.splitext(html_path)
    output_path = os.path.abspath(output_path) if output_path else None
    if output_path and output_path.lower().endswith(".svg"):
        json_path = base + ".json"
        if not os.path.exists(json_path):
            raise SystemExit(f"SVG fallback needs sibling JSON trace: {json_path}")
        svg_path = _write_trace_svg_from_json(json_path, output_path)
        print(f"Trace picture: {svg_path}")
        return

    png_path = output_path or base + ".png"
    ok, message = _render_html_to_png(html_path, png_path)
    if ok:
        print(f"Trace picture: {png_path} ({message})")
        return

    print(f"PNG render skipped: {message}")
    json_path = base + ".json"
    if not os.path.exists(json_path):
        raise SystemExit(f"No sibling JSON trace found for SVG fallback: {json_path}")

    svg_path = base + ".svg"
    _write_trace_svg_from_json(json_path, svg_path)
    print(f"Trace picture: {svg_path}")


class DecisionTrace:
    """
    Records the search tree for a run and emits JSON, DOT, and self-contained
    HTML views. Nodes are intentionally simple so traces can be diffed or
    post-processed later.
    """

    def __init__(self, mode, target_file, output_dir=DEFAULT_TRACE_DIR, render_picture=True):
        self.mode = mode
        self.target_file = target_file
        self.output_dir = output_dir
        self.render_picture = render_picture
        self.nodes = []
        self.edges = []
        self._next_id = 0
        self.root_id = self.add_node(
            kind="run",
            label=f"{mode}: {target_file}",
            status="START",
            target_file=target_file,
        )

    def add_node(self, kind, label, parent=None, edge_label="", **attrs):
        node_id = f"n{self._next_id}"
        self._next_id += 1
        node = {
            "id": node_id,
            "kind": kind,
            "label": _short_text(label, 500),
            "status": attrs.pop("status", None),
            "attrs": _jsonable(attrs),
        }
        self.nodes.append(node)
        if parent is not None:
            self.edges.append({
                "from": parent,
                "to": node_id,
                "label": _short_text(edge_label, 120),
            })
        return node_id

    def write_outputs(self):
        os.makedirs(self.output_dir, exist_ok=True)
        stamp = time.strftime("%Y%m%d-%H%M%S")
        target = _safe_slug(os.path.basename(self.target_file))
        base = os.path.join(self.output_dir, f"{self.mode}-{target}-{stamp}")
        json_path = base + ".json"
        dot_path = base + ".dot"
        html_path = base + ".html"
        svg_path = base + ".svg"
        png_path = base + ".png"

        payload = {
            "metadata": {
                "mode": self.mode,
                "target_file": self.target_file,
                "created_at": stamp,
                "decision_rule": (
                    "The LLM proposes candidates using speed heuristics; "
                    "the script decides by measured `lake env lean` wall time. "
                    "A candidate is accepted only if it beats the current best "
                    "by the configured threshold."
                ),
            },
            "nodes": self.nodes,
            "edges": self.edges,
        }
        with open(json_path, "w") as f:
            json.dump(payload, f, indent=2)
        with open(dot_path, "w") as f:
            f.write(self._to_dot())
        with open(html_path, "w") as f:
            f.write(self._to_html(payload))
        paths = {
            "json": json_path,
            "dot": dot_path,
            "html": html_path,
        }
        if self.render_picture:
            with open(svg_path, "w") as f:
                f.write(self._to_svg(payload))
            paths["svg"] = svg_path
            paths["picture"] = svg_path
        return paths

    def _to_dot(self):
        def esc(s):
            return str(s).replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n')

        colors = {
            "ACCEPTED": "#d7f5df",
            "FASTER": "#dfefff",
            "SAME": "#eeeeee",
            "ERROR": "#ffe1e1",
            "FAIL": "#ffe1e1",
            "CHEAT": "#fff1cc",
            "START": "#f5f5f5",
        }
        lines = [
            "digraph autoresearch {",
            "  rankdir=LR;",
            '  node [shape=box, style="rounded,filled", fontname="Menlo"];',
            '  edge [fontname="Menlo"];',
        ]
        for node in self.nodes:
            status = node.get("status") or ""
            attrs = node.get("attrs") or {}
            details = []
            for key in ("seconds", "saved_seconds", "reasoning", "rationale", "decision"):
                if key in attrs and attrs[key] not in (None, ""):
                    details.append(f"{key}: {attrs[key]}")
            label = node["label"]
            if status:
                label += f"\n[{status}]"
            if details:
                label += "\n" + "\n".join(_short_text(x, 90) for x in details)
            color = colors.get(status, "#ffffff")
            lines.append(f'  {node["id"]} [label="{esc(label)}", fillcolor="{color}"];')
        for edge in self.edges:
            label = edge.get("label") or ""
            lines.append(
                f'  {edge["from"]} -> {edge["to"]} [label="{esc(label)}"];'
            )
        lines.append("}")
        return "\n".join(lines) + "\n"

    def _to_svg(self, payload):
        children = {node["id"]: [] for node in self.nodes}
        for edge in self.edges:
            children.setdefault(edge["from"], []).append(edge["to"])

        positions = {}
        leaf_index = 0

        def place(node_id, depth=0):
            nonlocal leaf_index
            child_ids = children.get(node_id, [])
            if not child_ids:
                y = leaf_index
                leaf_index += 1
            else:
                child_ys = [place(child, depth + 1) for child in child_ids]
                y = sum(child_ys) / len(child_ys)
            positions[node_id] = (depth, y)
            return y

        place(self.root_id)
        max_depth = max((depth for depth, _ in positions.values()), default=0)
        max_y = max((y for _, y in positions.values()), default=0)
        margin = 32
        box_w = 330
        box_h = 96
        x_gap = 390
        y_gap = 132
        width = int(margin * 2 + box_w + max_depth * x_gap)
        height = int(margin * 2 + box_h + max_y * y_gap)

        colors = {
            "ACCEPTED": "#d7f5df",
            "FASTER": "#dfefff",
            "SAME": "#eeeeee",
            "ERROR": "#ffe1e1",
            "FAIL": "#ffe1e1",
            "CHEAT": "#fff1cc",
            "START": "#f5f5f5",
            None: "#ffffff",
            "": "#ffffff",
        }

        def xy(node_id):
            depth, y = positions[node_id]
            return margin + depth * x_gap, margin + y * y_gap

        def text_lines(node):
            status = node.get("status") or ""
            attrs = node.get("attrs") or {}
            heading = f"{node['kind']}: {node['label']}"
            lines = textwrap.wrap(heading, width=46)[:2]
            if status:
                lines.append(f"[{status}]")
            for key in ("seconds", "saved_seconds", "decision"):
                if key in attrs and attrs[key] not in (None, ""):
                    lines.extend(textwrap.wrap(f"{key}: {attrs[key]}", width=46)[:2])
            return lines[:5]

        parts = [
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
            f'viewBox="0 0 {width} {height}">',
            "<style>",
            "text { font-family: Menlo, Consolas, monospace; font-size: 12px; fill: #1f2328; }",
            ".edge { stroke: #8c959f; stroke-width: 1.4; fill: none; }",
            ".box { stroke: #d0d7de; stroke-width: 1.2; rx: 7; }",
            "</style>",
            f'<rect width="{width}" height="{height}" fill="#fbfbfb"/>',
            '<text x="32" y="22" font-size="15" font-weight="700">autoresearch decision trace</text>',
        ]

        for edge in self.edges:
            x1, y1 = xy(edge["from"])
            x2, y2 = xy(edge["to"])
            start_x = x1 + box_w
            start_y = y1 + box_h / 2
            end_x = x2
            end_y = y2 + box_h / 2
            mid_x = (start_x + end_x) / 2
            parts.append(
                f'<path class="edge" d="M {start_x:.1f} {start_y:.1f} '
                f'C {mid_x:.1f} {start_y:.1f}, {mid_x:.1f} {end_y:.1f}, {end_x:.1f} {end_y:.1f}"/>'
            )
            label = edge.get("label") or ""
            if label:
                parts.append(
                    f'<text x="{mid_x - 38:.1f}" y="{min(start_y, end_y) - 8:.1f}" '
                    f'fill="#59636e">{html.escape(label)}</text>'
                )

        for node in self.nodes:
            x, y = xy(node["id"])
            fill = colors.get(node.get("status"), "#ffffff")
            parts.append(f'<rect class="box" x="{x}" y="{y}" width="{box_w}" height="{box_h}" fill="{fill}"/>')
            for line_idx, line in enumerate(text_lines(node)):
                weight = "700" if line_idx == 0 else "400"
                parts.append(
                    f'<text x="{x + 12}" y="{y + 22 + line_idx * 16}" '
                    f'font-weight="{weight}">{html.escape(line)}</text>'
                )

        parts.append("</svg>")
        return "\n".join(parts) + "\n"

    def _to_html(self, payload):
        graph_json = json.dumps(payload, indent=2)
        target_esc = html.escape(payload.get("metadata", {}).get("target_file", ""))
        mode_esc = html.escape(payload.get("metadata", {}).get("mode", ""))
        created_esc = html.escape(payload.get("metadata", {}).get("created_at", ""))
        return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>autoresearch decision trace &mdash; {target_esc}</title>
  <style>
    *, *::before, *::after {{ box-sizing: border-box; margin: 0; padding: 0; }}
    html, body {{ width: 100%; height: 100%; overflow: hidden; background: #0d1117; color: #e6edf3; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }}

    #header {{
      position: fixed; top: 0; left: 0; right: 0; z-index: 10;
      display: flex; align-items: center; gap: 16px;
      padding: 10px 18px;
      background: rgba(13,17,23,0.92); backdrop-filter: blur(8px);
      border-bottom: 1px solid #30363d;
    }}
    #header h1 {{ font-size: 15px; font-weight: 600; color: #e6edf3; white-space: nowrap; }}
    #header .meta {{ font-size: 12px; color: #7d8590; white-space: nowrap; }}
    #header .spacer {{ flex: 1; }}
    #legend {{ display: flex; gap: 10px; align-items: center; flex-wrap: wrap; }}
    .leg {{ display: flex; align-items: center; gap: 5px; font-size: 11px; color: #adbac7; }}
    .leg-dot {{ width: 12px; height: 12px; border-radius: 50%; border: 1.5px solid rgba(255,255,255,0.15); flex-shrink:0; }}
    #controls {{ display: flex; gap: 8px; }}
    button {{
      background: #21262d; border: 1px solid #30363d; color: #adbac7;
      border-radius: 6px; padding: 4px 10px; font-size: 12px; cursor: pointer;
    }}
    button:hover {{ background: #30363d; color: #e6edf3; }}

    #canvas-wrap {{ position: fixed; top: 48px; left: 0; right: 0; bottom: 0; }}
    svg {{ width: 100%; height: 100%; }}

    .link {{ stroke: #444c56; stroke-opacity: 0.7; fill: none; }}
    .link-label {{ font-size: 10px; fill: #7d8590; pointer-events: none; }}

    .node-group {{ cursor: pointer; }}
    .node-rect {{ rx: 7; stroke-width: 1.5; filter: drop-shadow(0 2px 6px rgba(0,0,0,0.5)); }}
    .node-kind {{ font-size: 10px; fill: #7d8590; font-family: ui-monospace,monospace; }}
    .node-label {{ font-size: 11px; fill: #e6edf3; font-weight: 600; }}
    .node-status {{ font-size: 10px; font-family: ui-monospace,monospace; }}
    .node-timing {{ font-size: 10px; fill: #7d8590; font-family: ui-monospace,monospace; }}
    .node-group:hover .node-rect {{ stroke-opacity: 1 !important; stroke-width: 2; }}

    #tooltip {{
      position: fixed; z-index: 100; pointer-events: none;
      background: #161b22; border: 1px solid #30363d; border-radius: 8px;
      padding: 12px 14px; max-width: 420px; font-size: 12px; line-height: 1.55;
      box-shadow: 0 8px 24px rgba(0,0,0,0.6);
      display: none;
    }}
    #tooltip .tt-kind {{ color: #7d8590; font-family: monospace; font-size: 11px; margin-bottom: 4px; }}
    #tooltip .tt-label {{ color: #e6edf3; font-weight: 600; margin-bottom: 6px; word-break: break-word; }}
    #tooltip .tt-status {{ font-weight: 700; font-family: monospace; margin-bottom: 6px; }}
    #tooltip table {{ border-collapse: collapse; width: 100%; margin-top: 6px; }}
    #tooltip th {{ text-align: right; color: #7d8590; padding: 2px 8px 2px 0; vertical-align: top; white-space: nowrap; font-weight: 400; }}
    #tooltip td {{ color: #adbac7; padding: 2px 0; word-break: break-word; max-width: 280px; }}
    #tooltip pre {{ background: #0d1117; border-radius: 4px; padding: 6px 8px; margin-top: 4px; white-space: pre-wrap; font-size: 11px; color: #adbac7; max-height: 160px; overflow-y: auto; }}
  </style>
</head>
<body>
<div id="header">
  <h1>autoresearch decision trace</h1>
  <span class="meta">{mode_esc} &nbsp;&bull;&nbsp; {target_esc} &nbsp;&bull;&nbsp; {created_esc}</span>
  <div class="spacer"></div>
  <div id="legend">
    <div class="leg"><div class="leg-dot" style="background:#2ea043;"></div>ACCEPTED / FASTER</div>
    <div class="leg"><div class="leg-dot" style="background:#388bfd;"></div>START</div>
    <div class="leg"><div class="leg-dot" style="background:#444c56;"></div>SAME</div>
    <div class="leg"><div class="leg-dot" style="background:#da3633;"></div>ERROR / FAIL</div>
    <div class="leg"><div class="leg-dot" style="background:#9e6a03;"></div>CHEAT</div>
  </div>
  <div id="controls">
    <button id="btn-reset">Reset view</button>
    <button id="btn-pin">Unpin all</button>
  </div>
</div>

<div id="canvas-wrap"><svg id="graph"></svg></div>
<div id="tooltip"></div>

<script src="https://cdnjs.cloudflare.com/ajax/libs/d3/7.9.0/d3.min.js"></script>
<script>
const GRAPH = {graph_json};

const STATUS_COLORS = {{
  ACCEPTED: "#2ea043",
  FASTER:   "#388bfd",
  START:    "#388bfd",
  SAME:     "#444c56",
  ERROR:    "#da3633",
  FAIL:     "#da3633",
  CHEAT:    "#9e6a03",
}};
const STATUS_TEXT = {{
  ACCEPTED: "#d2ffd8",
  FASTER:   "#cae8ff",
  START:    "#cae8ff",
  SAME:     "#adbac7",
  ERROR:    "#ffdcd7",
  FAIL:     "#ffdcd7",
  CHEAT:    "#ffe8a3",
}};
const KIND_BG = {{
  "run":          "#161b22",
  "baseline":     "#161b22",
  "pass":         "#1c2128",
  "proof-block":  "#1c2128",
  "llm-heuristic":"#1c2128",
  "candidate":    "#161b22",
  "decision":     "#21262d",
  "summary":      "#21262d",
}};

function nodeColor(d) {{
  return STATUS_COLORS[d.status] || "#555";
}}
function nodeBg(d) {{
  return KIND_BG[d.kind] || "#161b22";
}}
function statusTextColor(d) {{
  return STATUS_TEXT[d.status] || "#adbac7";
}}

// Build node / link arrays
const nodeById = {{}};
GRAPH.nodes.forEach(n => {{ nodeById[n.id] = n; }});

const nodes = GRAPH.nodes.map(n => ({{
  id: n.id,
  kind: n.kind,
  label: n.label,
  status: n.status || "",
  attrs: n.attrs || {{}},
}}));

const links = GRAPH.edges.map(e => ({{
  source: e.from,
  target: e.to,
  label: e.label || "",
}}));

// ---- D3 setup ----
const svg = d3.select("#graph");
const wrap = document.getElementById("canvas-wrap");

function dims() {{
  return {{ w: wrap.clientWidth, h: wrap.clientHeight }};
}}

const defs = svg.append("defs");
defs.append("marker")
  .attr("id", "arrow")
  .attr("viewBox", "0 -4 8 8")
  .attr("refX", 8).attr("refY", 0)
  .attr("markerWidth", 6).attr("markerHeight", 6)
  .attr("orient", "auto")
  .append("path")
  .attr("d", "M0,-4L8,0L0,4")
  .attr("fill", "#555");

const g = svg.append("g");

const zoom = d3.zoom()
  .scaleExtent([0.08, 4])
  .on("zoom", e => g.attr("transform", e.transform));
svg.call(zoom);

const {{w, h}} = dims();
const sim = d3.forceSimulation(nodes)
  .force("link", d3.forceLink(links).id(d => d.id).distance(180).strength(0.6))
  .force("charge", d3.forceManyBody().strength(-600))
  .force("center", d3.forceCenter(w / 2, h / 2))
  .force("collide", d3.forceCollide(90))
  .force("x", d3.forceX(w / 2).strength(0.04))
  .force("y", d3.forceY(h / 2).strength(0.04));

// Links
const linkSel = g.append("g").selectAll("line")
  .data(links).join("line")
  .attr("class", "link")
  .attr("stroke-width", 1.5)
  .attr("marker-end", "url(#arrow)");

const linkLabelSel = g.append("g").selectAll("text")
  .data(links.filter(l => l.label)).join("text")
  .attr("class", "link-label")
  .text(d => d.label);

// Nodes
const NODE_W = 200, NODE_H = 72;

const nodeSel = g.append("g").selectAll("g")
  .data(nodes).join("g")
  .attr("class", "node-group")
  .call(d3.drag()
    .on("start", (e, d) => {{
      if (!e.active) sim.alphaTarget(0.15).restart();
      d.fx = d.x; d.fy = d.y;
    }})
    .on("drag", (e, d) => {{ d.fx = e.x; d.fy = e.y; }})
    .on("end", (e, d) => {{
      if (!e.active) sim.alphaTarget(0);
      // keep pinned
    }})
  )
  .on("mouseover", showTooltip)
  .on("mousemove", moveTooltip)
  .on("mouseout", hideTooltip);

nodeSel.append("rect")
  .attr("class", "node-rect")
  .attr("x", -NODE_W / 2).attr("y", -NODE_H / 2)
  .attr("width", NODE_W).attr("height", NODE_H)
  .attr("fill", d => nodeBg(d))
  .attr("stroke", d => nodeColor(d))
  .attr("stroke-opacity", 0.7);

// kind label
nodeSel.append("text")
  .attr("class", "node-kind")
  .attr("x", -NODE_W / 2 + 8).attr("y", -NODE_H / 2 + 14)
  .text(d => d.kind);

// status badge (right)
nodeSel.append("text")
  .attr("class", "node-status")
  .attr("x", NODE_W / 2 - 8).attr("y", -NODE_H / 2 + 14)
  .attr("text-anchor", "end")
  .attr("fill", d => statusTextColor(d))
  .text(d => d.status);

// main label (wrapped to 2 lines)
nodeSel.each(function(d) {{
  const el = d3.select(this);
  const words = d.label.split(/\\s+/);
  let line = "", lines = [];
  for (const w of words) {{
    const test = line ? line + " " + w : w;
    if (test.length > 26 && line) {{ lines.push(line); line = w; }}
    else {{ line = test; }}
  }}
  if (line) lines.push(line);
  lines = lines.slice(0, 2);
  lines.forEach((ln, i) => {{
    el.append("text")
      .attr("class", "node-label")
      .attr("x", 0).attr("y", (i - (lines.length - 1) / 2) * 15)
      .attr("text-anchor", "middle")
      .text(ln.length > 28 ? ln.slice(0, 26) + "…" : ln);
  }});
}});

// timing footer
nodeSel.append("text")
  .attr("class", "node-timing")
  .attr("x", 0).attr("y", NODE_H / 2 - 9)
  .attr("text-anchor", "middle")
  .text(d => {{
    const a = d.attrs;
    if (a.seconds != null && a.saved_seconds != null)
      return `${{(+a.seconds).toFixed(2)}}s  saved ${{(+a.saved_seconds).toFixed(2)}}s`;
    if (a.seconds != null) return `${{(+a.seconds).toFixed(2)}}s`;
    return "";
  }});

sim.on("tick", () => {{
  linkSel
    .attr("x1", d => d.source.x)
    .attr("y1", d => d.source.y)
    .attr("x2", d => {{
      const dx = d.target.x - d.source.x, dy = d.target.y - d.source.y;
      const dist = Math.sqrt(dx*dx + dy*dy) || 1;
      return d.target.x - (dx / dist) * (NODE_W / 2 + 10);
    }})
    .attr("y2", d => {{
      const dx = d.target.x - d.source.x, dy = d.target.y - d.source.y;
      const dist = Math.sqrt(dx*dx + dy*dy) || 1;
      return d.target.y - (dy / dist) * (NODE_H / 2 + 10);
    }});

  linkLabelSel
    .attr("x", d => (d.source.x + d.target.x) / 2)
    .attr("y", d => (d.source.y + d.target.y) / 2 - 4);

  nodeSel.attr("transform", d => `translate(${{d.x}},${{d.y}})`);
}});

// ---- Tooltip ----
const tooltip = document.getElementById("tooltip");

function fmtVal(v) {{
  if (v === null || v === undefined) return "";
  if (typeof v === "number") return v.toFixed ? v.toFixed(4).replace(/\\.?0+$/, "") : String(v);
  return String(v);
}}

function showTooltip(event, d) {{
  const rows = Object.entries(d.attrs)
    .filter(([, v]) => v !== null && v !== "" && v !== undefined)
    .map(([k, v]) => {{
      const val = fmtVal(v);
      const cell = val.length > 80
        ? `<td><pre>${{escHtml(val)}}</pre></td>`
        : `<td>${{escHtml(val)}}</td>`;
      return `<tr><th>${{escHtml(k)}}</th>${{cell}}</tr>`;
    }}).join("");

  tooltip.innerHTML = `
    <div class="tt-kind">${{escHtml(d.kind)}}</div>
    <div class="tt-label">${{escHtml(d.label)}}</div>
    ${{d.status ? `<div class="tt-status" style="color:${{statusTextColor(d)}}">${{escHtml(d.status)}}</div>` : ""}}
    ${{rows ? `<table>${{rows}}</table>` : ""}}
  `;
  tooltip.style.display = "block";
  moveTooltip(event);
}}

function moveTooltip(event) {{
  const tw = tooltip.offsetWidth, th = tooltip.offsetHeight;
  const bw = window.innerWidth, bh = window.innerHeight;
  let x = event.clientX + 14, y = event.clientY + 14;
  if (x + tw > bw - 8) x = event.clientX - tw - 14;
  if (y + th > bh - 8) y = event.clientY - th - 14;
  tooltip.style.left = x + "px";
  tooltip.style.top  = y + "px";
}}

function hideTooltip() {{
  tooltip.style.display = "none";
}}

function escHtml(s) {{
  return String(s)
    .replace(/&/g,"&amp;").replace(/</g,"&lt;")
    .replace(/>/g,"&gt;").replace(/"/g,"&quot;");
}}

// ---- Controls ----
document.getElementById("btn-reset").addEventListener("click", () => {{
  svg.transition().duration(600).call(
    zoom.transform,
    d3.zoomIdentity.translate(dims().w / 2, dims().h / 2).scale(0.8)
      .translate(-dims().w / 2, -dims().h / 2)
  );
}});

document.getElementById("btn-pin").addEventListener("click", () => {{
  nodes.forEach(d => {{ d.fx = null; d.fy = null; }});
  sim.alphaTarget(0.2).restart();
  setTimeout(() => sim.alphaTarget(0), 1200);
}});

window.addEventListener("resize", () => {{
  const {{w, h}} = dims();
  sim.force("center", d3.forceCenter(w / 2, h / 2))
     .force("x", d3.forceX(w / 2).strength(0.04))
     .force("y", d3.forceY(h / 2).strength(0.04));
}});
</script>
</body>
</html>
"""


# ---------------------------------------------------------------------------
# File discovery — no lake build required
# ---------------------------------------------------------------------------

def find_sorry_files_by_scan(target_file=None):
    """Scan .lean files for tactic-mode sorries. Returns {path: count}."""
    if target_file:
        candidates = glob.glob("Hackathon/**/*.lean", recursive=True)
        paths = [p for p in candidates if target_file in p]
        if not paths:
            paths = [target_file]
    else:
        paths = glob.glob("Hackathon/**/*.lean", recursive=True)

    result = {}
    for path in paths:
        try:
            content = read_file(path)
            count = len(SORRY_RE.findall(content))
            if count > 0:
                result[path] = count
        except FileNotFoundError:
            pass
    return result


# ---------------------------------------------------------------------------
# Build helpers (final confirmation only)
# ---------------------------------------------------------------------------

def build_and_measure():
    subprocess.run(["./scripts/measure-build.sh"], capture_output=True, text=True)
    with open("build-report.json") as f:
        return json.load(f)


def get_sorry_locations(report):
    sorry_files = report.get("sorry_per_file", {})
    return {
        path: count
        for path, count in sorry_files.items()
        if count > 0
        and "Hackathon/Untitled/.lake" not in path
        and path.startswith("Hackathon/")
    }


# ---------------------------------------------------------------------------
# File I/O
# ---------------------------------------------------------------------------

def read_file(path):
    with open(path) as f:
        return f.read()


def write_file(path, content):
    with open(path, "w") as f:
        f.write(content)


# ---------------------------------------------------------------------------
# Goal extraction (sorry-filling mode)
# ---------------------------------------------------------------------------

def find_first_tactic_sorry(content):
    for m in SORRY_RE.finditer(content):
        indent = m.group(1)
        if indent:
            return m.start(), indent
    return None, None


def get_lean_goal_state(file_path, content):
    start, indent = find_first_tactic_sorry(content)
    if start is None:
        return ""
    modified = content[:start] + f"{indent}trace_state\n" + content[start:]
    write_file(file_path, modified)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", file_path],
            capture_output=True, text=True, timeout=FAST_TIMEOUT
        )
        return _parse_goal_from_output(result.stderr + result.stdout)
    except subprocess.TimeoutExpired:
        return ""
    finally:
        write_file(file_path, content)


def _parse_goal_from_output(output):
    goal_lines = []
    capturing = False
    for line in output.split('\n'):
        if re.search(r':\d+:\d+: information:', line):
            capturing = True
            after = re.sub(r'.*:\d+:\d+: information:\s*', '', line)
            if after.strip():
                goal_lines.append(after)
            continue
        if capturing:
            if re.match(r'.+:\d+:\d+:', line):
                break
            goal_lines.append(line)
    return '\n'.join(goal_lines).strip()


# ---------------------------------------------------------------------------
# Fast single-file validation
# ---------------------------------------------------------------------------

def check_file_fast(file_path):
    try:
        result = subprocess.run(
            ["lake", "env", "lean", file_path],
            capture_output=True, text=True, timeout=FAST_TIMEOUT
        )
        output = result.stderr + result.stdout
        has_error = (
            result.returncode != 0
            or bool(re.search(r':\d+:\d+: error:', output))
            or bool(re.search(r'unsolved goals', output))
            or bool(re.search(r'declaration uses sorry', output))
        )
        return not has_error, output
    except subprocess.TimeoutExpired:
        return False, "timeout"


def measure_compile_time(file_path, content=None, repeats=DEFAULT_MEASURE_REPEATS):
    """
    Compile a file and return the fastest wall-clock sample in seconds.

    The fastest sample is used because Lean checks can have noisy cold-cache
    spikes; candidates still must compile cleanly on every measured run.
    Returns inf on failure.
    """
    if content is not None:
        write_file(file_path, content)
    samples = []
    for _ in range(max(1, repeats)):
        t0 = time.time()
        try:
            result = subprocess.run(
                ["lake", "env", "lean", file_path],
                capture_output=True, text=True, timeout=180
            )
            elapsed = time.time() - t0
            out = result.stderr + result.stdout
            if (result.returncode != 0
                    or re.search(r':\d+:\d+: error:', out)
                    or re.search(r'unsolved goals', out)
                    or re.search(r'declaration uses sorry', out)):
                return float('inf')
            samples.append(elapsed)
        except subprocess.TimeoutExpired:
            return float('inf')
    return min(samples) if samples else float('inf')


# ---------------------------------------------------------------------------
# Proof-block parsing (optimize mode)
# ---------------------------------------------------------------------------

_BY_END_RE = re.compile(r':=\s*by\s*$')


def find_proof_blocks(content):
    """
    Find all `theorem/lemma/example/def ... := by` tactic proof blocks.
    Returns a list of dicts with:
      decl_line, proof_start, proof_end, declaration, proof_body, decl_indent
    """
    lines = content.split('\n')
    blocks = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if _BY_END_RE.search(line) and line.strip():
            decl_indent = len(line) - len(line.lstrip())
            # collect indented proof body
            j = i + 1
            proof_start = j
            while j < len(lines):
                pline = lines[j]
                if not pline.strip():
                    j += 1
                    continue
                if len(pline) - len(pline.lstrip()) > decl_indent:
                    j += 1
                else:
                    break
            # trim trailing blank lines
            proof_end = j
            while proof_end > proof_start and not lines[proof_end - 1].strip():
                proof_end -= 1

            if proof_end > proof_start:
                blocks.append({
                    'decl_line':   i,
                    'proof_start': proof_start,
                    'proof_end':   proof_end,
                    'declaration': line.strip(),
                    'proof_body':  '\n'.join(lines[proof_start:proof_end]),
                    'decl_indent': decl_indent,
                })
                i = proof_end
                continue
        i += 1
    return blocks


def replace_proof_block(content, block, new_proof_body):
    """Swap the proof body of a block with new_proof_body."""
    lines = content.split('\n')
    new_lines = (
        lines[:block['proof_start']]
        + new_proof_body.split('\n')
        + lines[block['proof_end']:]
    )
    return '\n'.join(new_lines)


# ---------------------------------------------------------------------------
# Candidate filtering
# ---------------------------------------------------------------------------

def is_cheat(candidate: str) -> bool:
    return bool(CHEAT_RE.search(candidate))


# ---------------------------------------------------------------------------
# LLM — sorry-filling
# ---------------------------------------------------------------------------

def _build_sorry_prompt(file_path, file_content, goal_state, error_feedback):
    system = (
        "You are a Lean 4 proof assistant specializing in graph theory and combinatorics (Mathlib).\n"
        "Your task: suggest tactics to close the first `sorry` in a Lean 4 file.\n\n"
        "Output ONLY valid JSON in this exact format:\n"
        '{"candidates": ["tactic1", "tactic2", ...], "reasoning": "..."}\n\n'
        "Rules:\n"
        "- Provide 3-5 candidates ordered most-to-least likely to work\n"
        "- Each candidate replaces one `sorry`; use \\n for multi-line tactics\n"
        "- Prefer: exact, simp, omega, decide, apply, constructor, intro, rfl\n"
        "- Do NOT use sorry, admit, exact?, apply?, simp?, or any ?-suffix search tactics\n"
        "- Do NOT invent Mathlib lemma names\n"
        "- Read the proof goal state carefully before guessing"
    )
    variable_parts = []
    if goal_state:
        variable_parts.append(f"Proof goal at first sorry:\n{goal_state}")
    if error_feedback:
        variable_parts.append(
            f"Previous candidates failed:\n{error_feedback[:600]}\n\n"
            "Suggest different approaches that avoid these errors."
        )
    variable_parts.append("Return JSON candidates to close the first `sorry`.")
    user = f"File: {file_path}\n\n{file_content}\n\n" + "\n\n".join(variable_parts)
    return system, user


def _build_speed_prompt(block, baseline_time):
    system = (
        "You are a Lean 4 proof optimization expert specializing in compilation speed.\n"
        "Suggest tactically diverse proof bodies that may reduce Lean elaboration time.\n"
        "You only estimate speed; an external runner will decide faster/slower by timing Lean.\n\n"
        "Output ONLY valid JSON:\n"
        '{"candidates": ["body1", "body2", ...], '
        '"rationales": ["why candidate 1 might be faster", "..."], '
        '"reasoning": "brief summary of your speed heuristic"}\n\n'
        "Speed rules (fastest to slowest):\n"
        "1. Term proofs over tactic proofs: `reach_adj e01` beats `by apply reach_adj; exact e01`\n"
        "2. `le_refl _` or `Nat.le_refl _` over `by simp` for trivial ≤ goals\n"
        "3. `simp only [x, y]` over bare `simp`\n"
        "4. `Nat.le_trans hw hnm` over `by omega` for simple inequalities\n"
        "5. `rw [lemma]` + `omega` over `simp [lemma]` + `omega`\n"
        "6. Direct `Walk.reverse_length w ▸ hw` over `by simp [Walk.reverse_length, hw]`\n\n"
        "Try different tactics when plausible: direct `exact`, `simpa only`, `rw`, `constructor`, "
        "`cases`, `refine`, `omega`, or a compact term proof. Avoid near-duplicates.\n"
        "Do NOT invent Mathlib lemma names. Do NOT use `sorry`, `admit`, or `?` search tactics.\n\n"
        "Each candidate is the INDENTED PROOF BODY only — do NOT include `by` or the declaration. "
        "Use \\n for newlines. Match the indentation of the current proof."
    )
    variable_ctx = (
        f"Declaration to speed up (file compiles in {baseline_time:.1f}s):\n"
        f"```\n{block['declaration']}\n  by\n{block['proof_body']}\n```\n\n"
        "Suggest 3-5 faster proof bodies (proof body only, without `by`)."
    )
    return system, variable_ctx


def _parse_candidates(text):
    json_match = re.search(r'\{[\s\S]*\}', text)
    if json_match:
        try:
            data = json.loads(json_match.group())
            return data.get("candidates", []), data.get("reasoning", "")
        except json.JSONDecodeError:
            pass
    return [text.strip()], ""


def _parse_candidate_payload(text):
    json_match = re.search(r'\{[\s\S]*\}', text)
    if not json_match:
        candidate = text.strip()
        return ([candidate] if candidate else []), "", {}
    try:
        data = json.loads(json_match.group())
    except json.JSONDecodeError:
        candidate = text.strip()
        return ([candidate] if candidate else []), "", {}

    candidates = data.get("candidates", [])
    reasoning = data.get("reasoning", "")
    raw_rationales = (
        data.get("rationales")
        or data.get("candidate_rationales")
        or data.get("why_faster")
        or {}
    )

    rationales = {}
    if isinstance(raw_rationales, list):
        for candidate, rationale in zip(candidates, raw_rationales):
            rationales[candidate] = rationale
    elif isinstance(raw_rationales, dict):
        rationales = raw_rationales
    return candidates, reasoning, rationales


def _call_llm(system, file_path, file_content, variable_ctx):
    if _backend in ("ollama", "openai"):
        model = "qwen2.5-coder:7b" if _backend == "ollama" else "gpt-4o"
        response = _openai_client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": system},
                {"role": "user", "content": f"File: {file_path}\n\n{file_content}\n\n{variable_ctx}"},
            ],
            max_tokens=1024,
            temperature=0.2,
        )
        return response.choices[0].message.content
    else:
        response = _anthropic_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=1024,
            system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral"}}],
            messages=[{"role": "user", "content": [
                {"type": "text", "text": f"File: {file_path}\n\n{file_content}",
                 "cache_control": {"type": "ephemeral"}},
                {"type": "text", "text": variable_ctx},
            ]}],
        )
        return response.content[0].text


def get_sorry_candidates(file_path, file_content, goal_state, error_feedback=None):
    system, user = _build_sorry_prompt(file_path, file_content, goal_state, error_feedback)
    # for sorry-filling the variable_ctx is baked into `user` already
    if _backend in ("ollama", "openai"):
        model = "qwen2.5-coder:7b" if _backend == "ollama" else "gpt-4o"
        response = _openai_client.chat.completions.create(
            model=model,
            messages=[{"role": "system", "content": system}, {"role": "user", "content": user}],
            max_tokens=1024, temperature=0.2,
        )
        text = response.choices[0].message.content
    else:
        response = _anthropic_client.messages.create(
            model="claude-sonnet-4-6", max_tokens=1024,
            system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral"}}],
            messages=[{"role": "user", "content": [
                {"type": "text", "text": f"File: {file_path}\n\n{file_content}",
                 "cache_control": {"type": "ephemeral"}},
                {"type": "text", "text": "\n\n".join(
                    ([f"Proof goal at first sorry:\n{goal_state}"] if goal_state else []) +
                    ([f"Previous candidates failed:\n{error_feedback[:600]}\nSuggest different approaches."]
                     if error_feedback else []) +
                    ["Return JSON candidates to close the first `sorry`."]
                )},
            ]}],
        )
        text = response.content[0].text
    return _parse_candidates(text)


def get_speed_candidates(file_path, file_content, block, baseline_time):
    system, variable_ctx = _build_speed_prompt(block, baseline_time)
    text = _call_llm(system, file_path, file_content, variable_ctx)
    return _parse_candidate_payload(text)


# ---------------------------------------------------------------------------
# Candidate application + fast testing (sorry-filling)
# ---------------------------------------------------------------------------

def apply_candidate(content, candidate):
    def replacer(m):
        indent = m.group(1)
        lines = candidate.split('\n')
        return '\n'.join(indent + line for line in lines)
    return SORRY_RE.sub(replacer, content, count=1)


def try_candidates_fast(file_path, original_content, candidates):
    all_errors = []
    for candidate in candidates:
        if is_cheat(candidate):
            print(f"    [CHEAT] rejected: {candidate[:60]!r}")
            continue
        modified = apply_candidate(original_content, candidate)
        if modified == original_content:
            continue
        write_file(file_path, modified)
        passed, output = check_file_fast(file_path)
        short = candidate.replace('\n', ' ')[:70]
        if passed:
            print(f"    [PASS] {short}")
            return modified, None
        else:
            err_preview = re.search(r'error:.*', output)
            err_msg = err_preview.group()[:80] if err_preview else "unknown error"
            print(f"    [FAIL] {short!r:.50} → {err_msg}")
            all_errors.append(f"Candidate `{candidate[:40]}`: {err_msg}")
    write_file(file_path, original_content)
    return None, "\n".join(all_errors)


# ---------------------------------------------------------------------------
# Sorry-filling loop (default mode)
# ---------------------------------------------------------------------------

def autoresearch_loop(max_iterations=20, target_file=None):
    mode = {"ollama": "Ollama (local)", "openai": "OpenAI",
            "anthropic": "Claude (Anthropic)"}.get(_backend, _backend)
    print(f"=== autoresearch [sorry-filling] [{mode}] ===")
    print("Strategy: fast file scan → lake env lean per candidate → one final lake build")

    total_closed = 0
    touched_files = set()

    for iteration in range(max_iterations):
        sorry_files = find_sorry_files_by_scan(target_file)
        sorry_count = sum(sorry_files.values())

        print(f"\n--- Iteration {iteration + 1}/{max_iterations} "
              f"| {sorry_count} open sorries in {len(sorry_files)} file(s) ---")

        if sorry_count == 0:
            print("All sorries closed!")
            break

        made_progress = False

        for file_path, _ in sorry_files.items():
            content = read_file(file_path)
            remaining = len(SORRY_RE.findall(content))
            if remaining == 0:
                continue

            print(f"\n  File: {file_path}  ({remaining} sorries)")
            print("  Extracting proof goal...")
            goal_state = get_lean_goal_state(file_path, content)
            if goal_state:
                print(f"  Goal: {goal_state[:120].replace(chr(10), ' ')}")
            else:
                print("  Goal: (none extracted — term-mode or timeout)")

            error_feedback = None
            for attempt in range(3):
                print(f"  Candidates round {attempt + 1}...")
                candidates, reasoning = get_sorry_candidates(
                    file_path, content, goal_state, error_feedback
                )
                if not candidates:
                    print("  No candidates returned.")
                    break
                if reasoning:
                    print(f"  Reasoning: {reasoning[:100]}")

                winning_content, error_feedback = try_candidates_fast(
                    file_path, content, candidates
                )
                if winning_content is not None:
                    content = winning_content
                    total_closed += 1
                    touched_files.add(file_path)
                    made_progress = True
                    print(f"  [CLOSED] sorry in {file_path} (total: {total_closed})")
                    break

        if not made_progress:
            print("\nNo progress this iteration. Stopping early.")
            break

    print(f"\n=== Fast-check phase done. Sorries closed: {total_closed} ===")
    if total_closed > 0:
        print("Running final lake build to confirm...")
        report = build_and_measure()
        final_sorry_files = get_sorry_locations(report)
        if target_file:
            final_sorry_files = {k: v for k, v in final_sorry_files.items()
                                  if target_file in k}
        final_count = sum(final_sorry_files.values())
        print(f"Final build: {final_count} open sorries remaining")
    else:
        print("No sorries were closed — skipping final build.")
    return sorted(touched_files)


# ---------------------------------------------------------------------------
# Speed-optimization loop (--optimize mode)
# ---------------------------------------------------------------------------

def _indent_candidate_body(candidate, decl_indent):
    target_indent = ' ' * (decl_indent + 2)
    return '\n'.join(
        (target_indent + line.lstrip()) if line.strip() else line
        for line in candidate.split('\n')
    )


def _candidate_rationale(rationales, candidate, index):
    if not rationales:
        return ""
    if isinstance(rationales, dict):
        return (
            rationales.get(candidate)
            or rationales.get(str(index))
            or rationales.get(str(index + 1))
            or ""
        )
    return ""


def optimize_loop(
    target_file,
    passes=1,
    measure_repeats=DEFAULT_MEASURE_REPEATS,
    min_speedup_ms=DEFAULT_MIN_SPEEDUP_MS,
    trace_dir=DEFAULT_TRACE_DIR,
    trace_picture=True,
):
    """
    Take a fully proved Lean file and try to reduce its compile time by
    replacing tactic proof blocks with faster alternatives.

    Strategy:
    1. Measure baseline compile time for the whole file.
    2. Find all `by` proof blocks.
    3. For each block: ask the LLM for faster alternatives, try each,
       keep the version that compiles fastest without errors.
    4. Report total time saved.
    """
    mode = {"ollama": "Ollama (local)", "openai": "OpenAI",
            "anthropic": "Claude (Anthropic)"}.get(_backend, _backend)
    print(f"=== autoresearch [--optimize] [{mode}] ===")
    print(f"Target: {target_file}\n")
    print(
        "Decision rule: the LLM proposes faster-looking tactic bodies from "
        "heuristics; this script accepts only measured Lean wall-time wins."
    )
    print(
        f"Measurement: {measure_repeats} run(s), fastest clean run wins, "
        f"minimum improvement {min_speedup_ms}ms.\n"
    )

    trace = (
        DecisionTrace("optimize", target_file, trace_dir, render_picture=trace_picture)
        if trace_dir else None
    )
    min_speedup = max(0.0, min_speedup_ms / 1000.0)

    content = read_file(target_file)

    print("Measuring baseline compile time...")
    baseline = measure_compile_time(target_file, content, repeats=measure_repeats)
    if baseline == float('inf'):
        print("ERROR: file does not compile cleanly. Fix errors before optimizing.")
        if trace:
            trace.add_node(
                kind="baseline",
                label="baseline compile failed",
                parent=trace.root_id,
                status="ERROR",
            )
            paths = trace.write_outputs()
            _print_trace_paths(paths)
        return
    print(f"Baseline: {baseline:.2f}s\n")
    if trace:
        trace.add_node(
            kind="baseline",
            label=f"baseline {baseline:.2f}s",
            parent=trace.root_id,
            status="START",
            seconds=baseline,
        )

    blocks = find_proof_blocks(content)
    print(f"Found {len(blocks)} tactic proof blocks to consider.\n")

    # Use declaration text as stable key so line numbers stay valid after replacements
    decl_keys = [b['declaration'] for b in blocks]

    current_content = content
    current_time = baseline
    total_saved = 0.0
    passes = max(1, passes)

    for pass_idx in range(passes):
        made_progress = False
        pass_node = None
        if trace:
            pass_node = trace.add_node(
                kind="pass",
                label=f"optimization pass {pass_idx + 1}",
                parent=trace.root_id,
                status="START",
                seconds=current_time,
            )
        print(f"--- Optimization pass {pass_idx + 1}/{passes} ---")

        for idx, decl_key in enumerate(decl_keys):
            # Re-parse to get fresh line numbers after any prior replacements
            fresh_blocks = find_proof_blocks(current_content)
            block = next((b for b in fresh_blocks if b['declaration'] == decl_key), None)
            if block is None:
                continue

            # Skip blocks that still contain sorry — they aren't real proofs yet
            if SORRY_RE.search(block['proof_body']):
                print(f"[{idx + 1}/{len(decl_keys)}] SKIP (contains sorry): {block['declaration'][:70]}")
                continue

            print(f"[{idx + 1}/{len(decl_keys)}] {block['declaration'][:70]}")
            print(f"  Current proof:\n    {block['proof_body'].strip()[:100]}")

            block_node = None
            if trace:
                block_node = trace.add_node(
                    kind="proof-block",
                    label=block['declaration'],
                    parent=pass_node,
                    edge_label=f"block {idx + 1}",
                    status="START",
                    current_seconds=current_time,
                    current_proof=block['proof_body'],
                )

            candidates, reasoning, rationales = get_speed_candidates(
                target_file, current_content, block, current_time
            )
            if reasoning:
                print(f"  LLM speed heuristic: {reasoning[:140]}")
            if not candidates:
                print("  No candidates returned.\n")
                if trace:
                    trace.add_node(
                        kind="decision",
                        label="no candidates returned",
                        parent=block_node,
                        status="FAIL",
                    )
                continue

            best_time = current_time
            best_content = current_content
            best_candidate_label = None

            if trace:
                trace.add_node(
                    kind="llm-heuristic",
                    label="LLM candidate-generation rationale",
                    parent=block_node,
                    status="START",
                    reasoning=reasoning,
                )

            for cidx, candidate in enumerate(candidates):
                short = candidate.replace('\n', ' ')[:60]
                rationale = _candidate_rationale(rationales, candidate, cidx)
                if is_cheat(candidate):
                    print(f"    [CHEAT] rejected")
                    if trace:
                        trace.add_node(
                            kind="candidate",
                            label=short,
                            parent=block_node,
                            edge_label=f"candidate {cidx + 1}",
                            status="CHEAT",
                            rationale=rationale,
                            proof_body=candidate,
                            decision="Rejected before timing because it contains a banned proof search or placeholder.",
                        )
                    continue

                indented = _indent_candidate_body(candidate, block['decl_indent'])
                modified = replace_proof_block(current_content, block, indented)
                t = measure_compile_time(target_file, modified, repeats=measure_repeats)

                if t == float('inf'):
                    print(f"    [ERROR]  {short!r:.60}")
                    status = "ERROR"
                    decision = "Rejected because Lean did not compile cleanly."
                    saved = None
                elif t < best_time - min_speedup:
                    saved = best_time - t
                    print(f"    [FASTER] {t:.2f}s (saved {saved:.2f}s)  {short!r:.50}")
                    status = "FASTER"
                    decision = (
                        f"Measured {saved:.3f}s faster than the current best, "
                        f"exceeding the {min_speedup:.3f}s threshold."
                    )
                    best_time = t
                    best_content = modified
                    best_candidate_label = short
                else:
                    saved = best_time - t if t != float('inf') else None
                    print(f"    [SAME]   {t:.2f}s  {short!r:.50}")
                    status = "SAME"
                    decision = (
                        "Rejected because the measured time did not beat the "
                        f"current best by at least {min_speedup:.3f}s."
                    )

                if trace:
                    trace.add_node(
                        kind="candidate",
                        label=short,
                        parent=block_node,
                        edge_label=f"candidate {cidx + 1}",
                        status=status,
                        rationale=rationale,
                        proof_body=candidate,
                        seconds=t,
                        saved_seconds=saved,
                        decision=decision,
                    )

            if best_content != current_content:
                current_content = best_content
                write_file(target_file, current_content)
                saved = current_time - best_time
                total_saved += saved
                current_time = best_time
                made_progress = True
                print(f"  -> Kept faster proof. Saved {saved:.2f}s\n")
                if trace:
                    trace.add_node(
                        kind="decision",
                        label="accepted faster proof",
                        parent=block_node,
                        status="ACCEPTED",
                        candidate=best_candidate_label,
                        seconds=current_time,
                        saved_seconds=saved,
                    )
            else:
                write_file(target_file, current_content)   # restore candidate writes
                print(f"  -> No improvement found.\n")
                if trace:
                    trace.add_node(
                        kind="decision",
                        label="kept existing proof",
                        parent=block_node,
                        status="SAME",
                        seconds=current_time,
                    )

        if not made_progress:
            print("No measured improvements in this pass. Stopping.\n")
            break

    print("=" * 60)
    print(f"Baseline:  {baseline:.2f}s")
    print(f"Final:     {current_time:.2f}s")
    print(f"Saved:     {total_saved:.2f}s  ({100 * total_saved / baseline:.0f}% faster)")
    if trace:
        trace.add_node(
            kind="summary",
            label="optimization summary",
            parent=trace.root_id,
            status="ACCEPTED" if total_saved > 0 else "SAME",
            baseline_seconds=baseline,
            final_seconds=current_time,
            saved_seconds=total_saved,
        )
        paths = trace.write_outputs()
        _print_trace_paths(paths)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def _resolve_lean_target(target):
    if not target:
        return None
    if os.path.exists(target):
        return target

    candidates = []
    for pattern in ("Hackathon/**/*.lean", "**/*.lean"):
        for path in glob.glob(pattern, recursive=True):
            if ".lake" in path or not path.endswith(".lean"):
                continue
            if path not in candidates:
                candidates.append(path)
    return next((p for p in candidates if target in p), target)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=(
            "Fill Lean sorries and/or search for faster proof bodies by timing "
            "`lake env lean`."
        )
    )
    parser.add_argument("target", nargs="?", help="Lean file or substring to target")
    parser.add_argument("--optimize", action="store_true",
                        help="optimize existing proof blocks instead of filling sorries")
    parser.add_argument("--optimize-after-sorries", action="store_true",
                        help="after filling sorries, optimize any file changed by this run")
    parser.add_argument("--optimize-passes", type=int, default=1,
                        help="maximum measured optimization passes")
    parser.add_argument("--measure-repeats", type=int, default=DEFAULT_MEASURE_REPEATS,
                        help="number of clean Lean timing samples per candidate")
    parser.add_argument("--min-speedup-ms", type=float, default=DEFAULT_MIN_SPEEDUP_MS,
                        help="minimum measured improvement needed to accept a candidate")
    parser.add_argument("--trace-dir", default=DEFAULT_TRACE_DIR,
                        help="directory for optimization decision-tree JSON/DOT/HTML/images")
    parser.add_argument("--no-trace", action="store_true",
                        help="disable optimization decision-tree output")
    parser.add_argument("--no-trace-picture", action="store_true",
                        help="skip trace SVG/PNG picture generation")
    parser.add_argument("--trace-html-to-picture", metavar="HTML",
                        help="convert an existing decision-trace HTML file to a picture")
    parser.add_argument("--trace-picture-out", metavar="PATH",
                        help="output path for --trace-html-to-picture")
    parser.add_argument("--local", action="store_true",
                        help="use local Ollama OpenAI-compatible endpoint")
    parser.add_argument("--openai", action="store_true",
                        help="use OpenAI backend")
    args = parser.parse_args()

    if args.trace_html_to_picture:
        trace_html_to_picture(args.trace_html_to_picture, args.trace_picture_out)
        raise SystemExit(0)

    if args.optimize and not args.target:
        parser.error("--optimize requires <file.lean>")

    if args.local:
        backend = "ollama"
    elif args.openai:
        backend = "openai"
    else:
        backend = "anthropic"
    _setup_clients(backend)
    trace_dir = None if args.no_trace else args.trace_dir
    trace_picture = not args.no_trace_picture

    if args.optimize:
        resolved = _resolve_lean_target(args.target)
        optimize_loop(
            resolved,
            passes=args.optimize_passes,
            measure_repeats=args.measure_repeats,
            min_speedup_ms=args.min_speedup_ms,
            trace_dir=trace_dir,
            trace_picture=trace_picture,
        )
    else:
        touched = autoresearch_loop(target_file=args.target)
        if args.optimize_after_sorries:
            targets = touched
            if not targets and args.target:
                targets = [_resolve_lean_target(args.target)]
            for path in targets:
                remaining = len(SORRY_RE.findall(read_file(path)))
                if remaining:
                    print(f"Skipping optimize for {path}: {remaining} sorry/sorries remain.")
                    continue
                optimize_loop(
                    path,
                    passes=args.optimize_passes,
                    measure_repeats=args.measure_repeats,
                    min_speedup_ms=args.min_speedup_ms,
                    trace_dir=trace_dir,
                    trace_picture=trace_picture,
                )
