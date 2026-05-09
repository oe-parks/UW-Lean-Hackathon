from manim import *

# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║                        USER CONFIGURATION                                   ║
# ╠══════════════════════════════════════════════════════════════════════════════╣
# ║  Edit the three sections below to define any graph and augmentation steps.  ║
# ║  Everything else is automatic — layout, colors, animation, legend.          ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

# ── 1. NODE POSITIONS ─────────────────────────────────────────────────────────
# Keys are node IDs (any int or string). Values are (x, y) coordinates.
# x ranges roughly -6 to 6, y ranges roughly -3.5 to 3.5.
#
# Current layout:
#   0 ─── 1 ─── 2 ─── 3
#         |           |
#         4     5 ─── 6 ─── 7
#              (0,5 cross-edge)
#
NODE_POSITIONS = {
    0: (-4.5,  1.5),
    1: (-1.5,  1.5),
    2: ( 1.5,  1.5),
    3: ( 4.5,  1.5),
    4: (-1.5, -1.5),
    5: (-4.5, -1.5),
    6: ( 4.5, -1.5),
    7: ( 1.5, -1.5),
}

# ── 2. EDGES ──────────────────────────────────────────────────────────────────
# List of (u, v) pairs. Order doesn't matter; each edge is undirected.
EDGE_LIST = [
    (0, 1), (1, 2), (2, 3),   # top row
    (3, 6), (2, 7), (1, 4),   # verticals
    (6, 7),                    # bottom right
    (0, 5), (4, 5),            # cross + bottom left
]

# ── 3. AUGMENTATION STEPS ─────────────────────────────────────────────────────
# Each step is a dict with:
#
#   "title"      : heading shown at the top
#   "subtitle"   : smaller text below the heading
#   "free_nodes" : nodes to pulse orange before walking (usually path endpoints)
#   "path"       : list of (u, v, kind) tuples walked in order
#                    kind = "free"    → orange  (edge not in current matching)
#                    kind = "matched" → red     (edge currently in matching)
#   "flip"       : dict describing what changes after augmenting
#                    "remove" : list of (u,v) edges to un-match
#                    "add"    : list of (u,v) edges to newly match
#
# HOW TO BUILD A STEP:
#   1. Identify two free (unmatched) nodes to connect.
#   2. Trace an alternating path between them: free edge, matched edge, free edge, ...
#   3. In "path", label each edge "free" or "matched" accordingly.
#   4. In "flip": remove every matched edge on the path, add every free edge on the path.
#
AUGMENTATION_STEPS = [
    # ── Step 1: trivial — augment single free edge (1,2) ─────────────────────
    {
        "title":    "Step 1 — Simplest augmenting path",
        "subtitle": "Matching is empty — any edge between two free vertices works",
        "free_nodes": [1, 2],
        "path": [
            (1, 2, "free"),
        ],
        "flip": {
            "remove": [],
            "add":    [(1, 2)],
        },
        "flip_subtitle": "Flip: edge (1,2) joins the matching.   Matching size: 0 → 1",
    },

    # ── Step 2: trivial — augment single free edge (6,7) ─────────────────────
    {
        "title":    "Step 2 — Another trivial augmenting path",
        "subtitle": "Nodes 6 and 7 are still free — edge (6,7) is a valid path",
        "free_nodes": [6, 7],
        "path": [
            (6, 7, "free"),
        ],
        "flip": {
            "remove": [],
            "add":    [(6, 7)],
        },
        "flip_subtitle": "Flip: edge (6,7) joins the matching.   Matching size: 1 → 2",
    },

    # ── Step 3: interesting — path 0→1→2→3 crosses matched edge (1,2) ────────
    # Matching before: {(1,2),(6,7)}   Free nodes: {0,3,4,5}
    {
        "title":    "Step 3 — First interesting augmenting path",
        "subtitle": "Path reroutes through existing matched edge (1,2)",
        "free_nodes": [0, 3],
        "path": [
            (0, 1, "free"),
            (1, 2, "matched"),   # ← traversing the matched edge
            (2, 3, "free"),
        ],
        "flip": {
            "remove": [(1, 2)],
            "add":    [(0, 1), (2, 3)],
        },
        "flip_subtitle": "Remove (1,2) from matching; add (0,1) and (2,3).   Size: 2 → 3",
    },

    # ── Step 4: interesting — path 4→1→0→5 crosses matched edge (0,1) ────────
    # Matching before: {(0,1),(2,3),(6,7)}   Free nodes: {4,5}
    {
        "title":    "Step 4 — Another alternating path",
        "subtitle": "Path threads through matched nodes 1 and 0 to reach free node 5",
        "free_nodes": [4, 5],
        "path": [
            (4, 1, "free"),
            (1, 0, "matched"),   # ← traversing matched edge (0,1)
            (0, 5, "free"),
        ],
        "flip": {
            "remove": [(0, 1)],
            "add":    [(1, 4), (0, 5)],
        },
        "flip_subtitle": "Remove (0,1) from matching; add (1,4) and (0,5).   Size: 3 → 4",
    },
]

# ── 4. FINAL MATCHING ─────────────────────────────────────────────────────────
# The maximum matching after all steps. Used for the final pulse animation.
FINAL_MATCHING = [(1, 4), (0, 5), (2, 3), (6, 7)]

# ── 5. COLORS (optional — change to restyle) ──────────────────────────────────
C_BG        = "#ffffff"
C_NODE      = "#4a90d9"
C_MATCHED   = "#2ecc71"
C_PATH_FREE = "#f0a500"
C_PATH_MAT  = "#e74c3c"
C_EDGE      = "#000000"
C_TEXT      = "#000000"
C_DIM       = "#000000"
C_NODE_LABEL = "#000000"
C_NODE_LABEL_ON_DARK = "#ffffff"

# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║               ANIMATION ENGINE — no need to edit below here                 ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

config.background_color = C_BG

def to_manim_pos(x, y):
    return x * RIGHT + y * UP


class AugmentingPath(Scene):

    def make_node(self, n):
        pos = to_manim_pos(*NODE_POSITIONS[n])
        c = Circle(radius=0.30, color=C_NODE, fill_color=C_NODE,
                   fill_opacity=1, stroke_width=0)
        c.move_to(pos)
        lbl = Text(str(n), font_size=20, color=C_NODE_LABEL, weight=BOLD)
        lbl.move_to(pos)
        return VGroup(c, lbl)

    def make_edge(self, u, v):
        pu = to_manim_pos(*NODE_POSITIONS[u])
        pv = to_manim_pos(*NODE_POSITIONS[v])
        return Line(pu, pv, color=C_EDGE, stroke_width=2.5)

    def get_edge(self, edges, u, v):
        return edges.get((u, v)) or edges.get((v, u))

    def recolor_node(self, node_mob, color):
        node_mob[0].set_fill(color, opacity=1)
        node_mob[0].set_stroke(color, width=0)
        node_mob[1].set_color(self.node_label_color(color))

    def node_label_color(self, color):
        hex_color = str(color).lstrip("#")
        if len(hex_color) == 6:
            r = int(hex_color[0:2], 16)
            g = int(hex_color[2:4], 16)
            b = int(hex_color[4:6], 16)
            if 0.2126 * r + 0.7152 * g + 0.0722 * b <= 40:
                return C_NODE_LABEL_ON_DARK
        return C_NODE_LABEL

    def flash_edge(self, edge_mob, color):
        return ShowPassingFlash(
            edge_mob.copy().set_color(color).set_stroke(width=7),
            time_width=0.45, run_time=0.55,
        )

    def section_title(self, text, sub=""):
        t = Text(text, font_size=25, color=C_TEXT, weight=BOLD).to_edge(UP, buff=0.25)
        s = (Text(sub, font_size=17, color=C_DIM, slant=ITALIC).next_to(t, DOWN, buff=0.1)
             if sub else None)
        return t, s

    def show_title(self, t, s):
        anims = [FadeIn(t)]
        if s:
            anims.append(FadeIn(s))
        self.play(*anims)

    def hide_title(self, t, s):
        anims = [FadeOut(t)]
        if s:
            anims.append(FadeOut(s))
        self.play(*anims)

    def do_augment(self, edges, nodes, u, v):
        """Flash a single edge green and recolor its endpoints."""
        e = self.get_edge(edges, u, v)
        e.set_color(C_MATCHED).set_stroke(width=4)
        self.recolor_node(nodes[u], C_MATCHED)
        self.recolor_node(nodes[v], C_MATCHED)
        self.play(Flash(e.get_center(), color=C_MATCHED,
                        line_length=0.22, num_lines=8, run_time=0.4))

    def walk_path(self, edges, nodes, path):
        """Animate walking a path. path = list of (u, v, 'free'|'matched')."""
        color_map = {"free": C_PATH_FREE, "matched": C_PATH_MAT}
        for u, v, kind in path:
            col = color_map[kind]
            e = self.get_edge(edges, u, v)
            e.set_color(col).set_stroke(width=4)
            self.play(
                self.flash_edge(e, col),
                Indicate(nodes[v][0], color=col, scale_factor=1.3),
                run_time=0.5,
            )

    def _leg(self, label, color, stroke_width=4):
        sample = Line(LEFT * 0.18, RIGHT * 0.18, color=color,
                      stroke_width=stroke_width)
        txt = Text(label, font_size=14, color=C_DIM)
        return VGroup(sample, txt).arrange(RIGHT, buff=0.15)

    def construct(self):
        nodes = {n: self.make_node(n) for n in NODE_POSITIONS}
        edges = {(u, v): self.make_edge(u, v) for u, v in EDGE_LIST}

        # ── intro ─────────────────────────────────────────────────────────────
        t0, s0 = self.section_title(
            "Augmenting Path Discovery",
            "Edmonds' Maximum Matching Algorithm",
        )
        self.show_title(t0, s0)
        self.wait(0.3)

        self.play(LaggedStart(*[Create(e) for e in edges.values()], lag_ratio=0.05), run_time=1.1)
        self.play(LaggedStart(*[GrowFromCenter(n) for n in nodes.values()], lag_ratio=0.05), run_time=0.9)
        self.wait(0.6)

        leg = VGroup(
            self._leg("Unmatched edge",       C_EDGE, 2.5),
            self._leg("Matched edge",         C_MATCHED, 4),
            self._leg("Free edge on path",    C_PATH_FREE, 5),
            self._leg("Matched edge on path", C_PATH_MAT, 5),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        leg.to_corner(DR, buff=0.35)
        leg_bg = SurroundingRectangle(
            leg, color="#cccccc", fill_color="#ffffff",
            fill_opacity=0.92, corner_radius=0.1, buff=0.15,
        )
        self.play(FadeIn(leg_bg), FadeIn(leg))
        self.hide_title(t0, s0)
        self.wait(0.2)

        # ── augmentation steps (driven entirely by AUGMENTATION_STEPS) ────────
        for step in AUGMENTATION_STEPS:
            # show path
            t, s = self.section_title(step["title"], step["subtitle"])
            self.show_title(t, s)

            for n in step["free_nodes"]:
                self.recolor_node(nodes[n], C_PATH_FREE)
            self.play(
                *[Indicate(nodes[n][0], color=C_PATH_FREE, scale_factor=1.45)
                  for n in step["free_nodes"]],
                run_time=0.7,
            )

            self.walk_path(edges, nodes, step["path"])
            self.wait(0.4)
            self.hide_title(t, s)

            # flip / augment
            flip_sub = step.get("flip_subtitle", "")
            tb, sb = self.section_title(f"{step['title'].split('—')[0].strip()} — Augment", flip_sub)
            self.show_title(tb, sb)

            for u, v in step["flip"]["remove"]:
                e = self.get_edge(edges, u, v)
                e.set_color(C_EDGE).set_stroke(width=2.5)
                self.recolor_node(nodes[u], C_NODE)
                self.recolor_node(nodes[v], C_NODE)

            for u, v in step["flip"]["add"]:
                self.do_augment(edges, nodes, u, v)

            self.wait(0.8)
            self.hide_title(tb, sb)

        # ── final ──────────────────────────────────────────────────────────────
        tf, sf = self.section_title(
            "Maximum Matching Found ✓",
            "No augmenting path exists  ⟹  matching is maximum   (Berge, 1957)",
        )
        self.show_title(tf, sf)

        self.play(
            LaggedStart(
                *[Indicate(nodes[n][0], color=C_MATCHED, scale_factor=1.35)
                  for n in NODE_POSITIONS],
                lag_ratio=0.08,
            ),
            run_time=1.3,
        )
        self.play(
            *[self.get_edge(edges, u, v).animate.set_stroke(width=6)
              for u, v in FINAL_MATCHING],
            run_time=0.5,
        )
        self.wait(2.5)
