from manim import *

# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║                        USER CONFIGURATION                                   ║
# ╠══════════════════════════════════════════════════════════════════════════════╣
# ║  Graph contains a blossom (odd cycle 5-6-7) so the blossom-contraction     ║
# ║  phase of Edmonds' algorithm can be demonstrated.                           ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

# ── 1. NODE POSITIONS ─────────────────────────────────────────────────────────
#
#   0 ──── 1 ──── 2 ──── 3
#                 |
#                 4
#                 |
#         8 ──── 5
#        /      / \
#       /      6   7       ← blossom: triangle 5-6-7
#      /        \ /
#   (free)       (forms the odd cycle for blossom detection)
#
NODE_POSITIONS = {
    0: (-5.5,  2.0),
    1: (-2.5,  2.0),
    2: ( 0.5,  2.0),
    3: ( 3.5,  2.0),
    4: ( 0.5,  0.2),
    5: ( 0.5, -1.5),
    6: (-1.0, -3.0),
    7: ( 2.0, -3.0),
    8: (-2.5, -1.5),
}

# ── 2. EDGES ──────────────────────────────────────────────────────────────────
EDGE_LIST = [
    (0, 1), (1, 2), (2, 3),   # top row
    (2, 4),                    # vertical spine
    (4, 5),                    # into blossom region
    (5, 6), (6, 7), (7, 5),   # ← the blossom (odd cycle)
    (8, 5), (1, 8),            # entry path to blossom
]

# ── 3. AUGMENTATION STEPS ─────────────────────────────────────────────────────
AUGMENTATION_STEPS = [
    # ── Step 1 ────────────────────────────────────────────────────────────────
    {
        "title":    "Step 1 — Trivial augmenting path",
        "subtitle": "Matching is empty — edge (2,3) connects two free vertices",
        "free_nodes": [2, 3],
        "path": [
            (2, 3, "free"),
        ],
        "flip": {
            "remove": [],
            "add":    [(2, 3)],
        },
        "flip_subtitle": "Flip: edge (2,3) joins the matching.   Matching size: 0 → 1",
    },

    # ── Step 2 ────────────────────────────────────────────────────────────────
    {
        "title":    "Step 2 — Another trivial augmenting path",
        "subtitle": "Nodes 0 and 1 are free — edge (0,1) is a valid path",
        "free_nodes": [0, 1],
        "path": [
            (0, 1, "free"),
        ],
        "flip": {
            "remove": [],
            "add":    [(0, 1)],
        },
        "flip_subtitle": "Flip: edge (0,1) joins the matching.   Matching size: 1 → 2",
    },
]

# ── 4. BLOSSOM CONFIG ─────────────────────────────────────────────────────────
# Describes the blossom phase shown after the regular augmentation steps.
BLOSSOM = {
    # BFS walk that discovers the blossom.
    # Source is free node 8; BFS fans out and hits the odd cycle.
    "bfs_source": 8,
    "bfs_target": 4,    # free node we're trying to reach

    # Matching before the blossom phase: {(0,1),(2,3)}
    # Free nodes: 4, 5, 6, 7, 8
    "matching_before": [(0, 1), (2, 3)],

    # The BFS walk shown before the blossom is detected.
    # (u, v, kind)  kind = "tree" (BFS tree edge) or "back" (closes odd cycle)
    "bfs_walk": [
        (8, 1,  "tree"),     # 8 → 1  (free edge, but 1 is matched)
        (8, 5,  "tree"),     # 8 → 5  (free edge, 5 is free → open)
        (5, 6,  "tree"),     # explore from 5
        (5, 7,  "tree"),     # explore from 5
        (6, 7,  "back"),     # ← closes odd cycle! blossom 5-6-7 detected
    ],

    # The three nodes forming the blossom (odd cycle).
    "blossom_nodes": [5, 6, 7],
    # The blossom edge that closes the cycle (shown as the "collision" edge).
    "blossom_closing_edge": (6, 7),

    # Super-node position (centroid of blossom nodes).
    "supernode_pos": (0.5, -2.25),
    "supernode_label": "B",

    # Edges in the contracted graph that matter for finding the path.
    # After contraction: 8-B is the free edge, B-4 doesn't exist directly —
    # the path is: free_node(8) → B (via 8-5) → 4 (via 5-4).
    # We show the path in contracted graph as: 8 → B → 4.
    "contracted_path": [
        (8, "B", "free"),
        ("B", 4, "free"),
    ],

    # Full lifted path in original graph.
    # Matching before: {(0,1),(2,3)}.  We want free node 8 → free node 4.
    # Lifted path: 8 → 5 → 7 → 6 → (through blossom) → 4? 
    # Actually correct lift: 8-5 (free), 5-4 (free) with blossom interior:
    # through blossom we enter at 5, exit at 5 via 5→7→6 or 5→6→7 to pick up 5→4.
    # Simplest valid lift: 8 →(free) 5 →(free) 4, and inside blossom match (6,7).
    # So the path walk is: 8→5→4, and we additionally match (6,7) inside the blossom.
    "lifted_path": [
        (8, 5, "free"),
        (5, 4, "free"),
    ],
    "lifted_blossom_internal_match": (6, 7),   # edge matched inside the blossom after lift

    "flip": {
        "remove": [],
        "add": [(8, 5), (5, 4), (6, 7)],
    },
    "flip_subtitle": "Add (8,5), (5,4), (6,7) to matching.   Matching size: 2 → 4  (maximum)",
}

# ── 5. FINAL MATCHING ─────────────────────────────────────────────────────────
FINAL_MATCHING = [(0, 1), (2, 3), (8, 5), (5, 4), (6, 7)]

# ── 6. COLORS ─────────────────────────────────────────────────────────────────
C_BG             = "#ffffff"
C_NODE           = "#4a90d9"
C_MATCHED        = "#2ecc71"
C_PATH_FREE      = "#f0a500"
C_PATH_MAT       = "#e74c3c"
C_EDGE           = "#000000"
C_TEXT           = "#000000"
C_DIM            = "#444444"
C_NODE_LABEL     = "#000000"
C_NODE_LABEL_ON_DARK = "#ffffff"
C_BLOSSOM_RING   = "#9b59b6"    # purple — highlight the odd cycle
C_BLOSSOM_NODE   = "#9b59b6"
C_SUPERNODE      = "#9b59b6"
C_BFS_TREE       = "#f0a500"
C_BFS_BACK       = "#e74c3c"

# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║               ANIMATION ENGINE                                              ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

config.background_color = C_BG


def to_manim_pos(x, y):
    return x * RIGHT + y * UP


class AugmentingPath(Scene):

    # ── helpers ───────────────────────────────────────────────────────────────

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
        node_mob[1].set_color(self._label_color(color))

    def _label_color(self, color):
        hex_color = str(color).lstrip("#")
        if len(hex_color) == 6:
            r = int(hex_color[0:2], 16)
            g = int(hex_color[2:4], 16)
            b = int(hex_color[4:6], 16)
            if 0.2126 * r + 0.7152 * g + 0.0722 * b <= 60:
                return C_NODE_LABEL_ON_DARK
        return C_NODE_LABEL

    def flash_edge(self, edge_mob, color):
        return ShowPassingFlash(
            edge_mob.copy().set_color(color).set_stroke(width=7),
            time_width=0.45, run_time=0.55,
        )

    def section_title(self, text, sub=""):
        t = Text(text, font_size=24, color=C_TEXT, weight=BOLD).to_edge(UP, buff=0.22)
        s = (Text(sub, font_size=16, color=C_DIM, slant=ITALIC).next_to(t, DOWN, buff=0.08)
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
        e = self.get_edge(edges, u, v)
        e.set_color(C_MATCHED).set_stroke(width=4)
        self.recolor_node(nodes[u], C_MATCHED)
        self.recolor_node(nodes[v], C_MATCHED)
        self.play(Flash(e.get_center(), color=C_MATCHED,
                        line_length=0.22, num_lines=8, run_time=0.4))

    def walk_path(self, edges, nodes, path):
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
        sample = Line(LEFT * 0.18, RIGHT * 0.18, color=color, stroke_width=stroke_width)
        txt = Text(label, font_size=13, color=C_DIM)
        return VGroup(sample, txt).arrange(RIGHT, buff=0.15)

    def _node_leg(self, label, fill_color):
        dot = Circle(radius=0.12, color=fill_color, fill_color=fill_color, fill_opacity=1,
                     stroke_width=0)
        txt = Text(label, font_size=13, color=C_DIM)
        return VGroup(dot, txt).arrange(RIGHT, buff=0.15)

    # ── blossom-phase helpers ─────────────────────────────────────────────────

    def make_supernode(self, label="B", pos=None):
        """Return a VGroup (circle + label) for the contracted super-node."""
        c = Circle(radius=0.42, color=C_SUPERNODE, fill_color=C_SUPERNODE,
                   fill_opacity=1, stroke_width=3, stroke_color=WHITE)
        lbl = Text(label, font_size=22, color=WHITE, weight=BOLD)
        grp = VGroup(c, lbl)
        if pos is not None:
            grp.move_to(pos)
        return grp

    def highlight_blossom(self, nodes, blossom_nodes, edges):
        """
        Pulse the blossom cycle purple and draw a dashed ring around it.
        Returns the ring mobject so the caller can remove it later.
        """
        bn = blossom_nodes
        # recolor the three nodes
        for n in bn:
            self.recolor_node(nodes[n], C_BLOSSOM_NODE)

        # Draw the three blossom edges in purple
        blossom_edge_pairs = [(bn[0], bn[1]), (bn[1], bn[2]), (bn[2], bn[0])]
        for u, v in blossom_edge_pairs:
            e = self.get_edge(edges, u, v)
            if e:
                e.set_color(C_BLOSSOM_RING).set_stroke(width=4.5)

        # Compute centroid for the ring
        positions = [to_manim_pos(*NODE_POSITIONS[n]) for n in bn]
        cx = sum(p[0] for p in positions) / 3
        cy = sum(p[1] for p in positions) / 3
        centroid = np.array([cx, cy, 0])

        radius = max(np.linalg.norm(p - centroid) for p in positions) + 0.45
        ring = DashedVMobject(
            Circle(radius=radius, color=C_BLOSSOM_RING, stroke_width=3),
            num_dashes=18,
        )
        ring.move_to(centroid)

        self.play(
            *[Indicate(nodes[n][0], color=C_BLOSSOM_RING, scale_factor=1.4) for n in bn],
            Create(ring),
            run_time=0.9,
        )
        return ring, centroid

    def contract_blossom(self, nodes, blossom_nodes, edges, ring, centroid):
        """
        Animate the three blossom nodes collapsing into a super-node.
        Returns the supernode VGroup.
        """
        sn = self.make_supernode("B", centroid)

        # Edges connected to blossom nodes (other than internal blossom edges)
        blossom_edge_pairs = {
            frozenset([blossom_nodes[0], blossom_nodes[1]]),
            frozenset([blossom_nodes[1], blossom_nodes[2]]),
            frozenset([blossom_nodes[2], blossom_nodes[0]]),
        }

        fade_targets = [ring]
        for n in blossom_nodes:
            fade_targets.append(nodes[n])
        # Also fade internal blossom edges
        for u, v in [(blossom_nodes[i], blossom_nodes[j])
                     for i in range(3) for j in range(i+1, 3)]:
            e = self.get_edge(edges, u, v)
            if e:
                fade_targets.append(e)

        self.play(
            *[mob.animate.move_to(centroid).scale(0.1) for mob in
              [nodes[n] for n in blossom_nodes]],
            FadeOut(ring),
            run_time=0.7,
        )
        self.play(GrowFromCenter(sn), run_time=0.6)

        # Hide internal edges properly
        for u, v in [(blossom_nodes[i], blossom_nodes[j])
                     for i in range(3) for j in range(i+1, 3)]:
            e = self.get_edge(edges, u, v)
            if e:
                e.set_opacity(0)

        return sn

    def expand_blossom(self, nodes, blossom_nodes, edges, sn, centroid):
        """
        Reverse contraction: fade out super-node, restore original nodes/edges.
        """
        self.play(FadeOut(sn), run_time=0.5)

        # Restore internal edges
        for u, v in [(blossom_nodes[i], blossom_nodes[j])
                     for i in range(3) for j in range(i+1, 3)]:
            e = self.get_edge(edges, u, v)
            if e:
                e.set_opacity(1)
                e.set_color(C_BLOSSOM_RING).set_stroke(width=4)

        # Restore nodes at their original positions
        for n in blossom_nodes:
            pos = to_manim_pos(*NODE_POSITIONS[n])
            nodes[n].move_to(pos)
            nodes[n].scale(10)   # undo the .scale(0.1) from contraction
            self.recolor_node(nodes[n], C_BLOSSOM_NODE)

        self.play(
            *[GrowFromCenter(nodes[n]) for n in blossom_nodes],
            run_time=0.7,
        )

    # ── main ──────────────────────────────────────────────────────────────────

    def construct(self):
        nodes = {n: self.make_node(n) for n in NODE_POSITIONS}
        edges = {(u, v): self.make_edge(u, v) for u, v in EDGE_LIST}

        # ── intro ─────────────────────────────────────────────────────────────
        t0, s0 = self.section_title(
            "Augmenting Path Discovery",
            "Edmonds' Maximum Matching with Blossom Contraction",
        )
        self.show_title(t0, s0)
        self.wait(0.3)

        self.play(LaggedStart(*[Create(e) for e in edges.values()], lag_ratio=0.05), run_time=1.1)
        self.play(LaggedStart(*[GrowFromCenter(n) for n in nodes.values()], lag_ratio=0.05), run_time=0.9)
        self.wait(0.5)

        # Legend
        leg = VGroup(
            self._leg("Unmatched edge",        C_EDGE,        2.5),
            self._leg("Matched edge",           C_MATCHED,     4),
            self._leg("Free edge on path",      C_PATH_FREE,   5),
            self._leg("Matched edge on path",   C_PATH_MAT,    5),
            self._leg("Blossom cycle",          C_BLOSSOM_RING, 4.5),
            self._node_leg("Super-node B",      C_SUPERNODE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
        leg.to_corner(DR, buff=0.3)
        leg_bg = SurroundingRectangle(
            leg, color="#cccccc", fill_color="#f9f9f9",
            fill_opacity=0.95, corner_radius=0.1, buff=0.14,
        )
        self.play(FadeIn(leg_bg), FadeIn(leg))
        self.hide_title(t0, s0)
        self.wait(0.2)

        # ── regular augmentation steps ────────────────────────────────────────
        for step in AUGMENTATION_STEPS:
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

        # ══════════════════════════════════════════════════════════════════════
        # BLOSSOM PHASE
        # ══════════════════════════════════════════════════════════════════════
        B = BLOSSOM

        # ── Phase B1: BFS discovers the blossom ───────────────────────────────
        tb1, sb1 = self.section_title(
            "Step 3 — BFS explores from free node 8",
            "Searching for an augmenting path to free node 4",
        )
        self.show_title(tb1, sb1)

        src = B["bfs_source"]
        self.recolor_node(nodes[src], C_PATH_FREE)
        self.play(Indicate(nodes[src][0], color=C_PATH_FREE, scale_factor=1.5), run_time=0.6)

        color_map_bfs = {"tree": C_PATH_FREE, "back": C_BFS_BACK}
        for u, v, kind in B["bfs_walk"]:
            col = color_map_bfs[kind]
            e = self.get_edge(edges, u, v)
            if e is None:
                continue
            e.set_color(col).set_stroke(width=4)
            self.play(
                self.flash_edge(e, col),
                Indicate(nodes[v][0], color=col, scale_factor=1.3),
                run_time=0.5,
            )

        self.wait(0.5)
        self.hide_title(tb1, sb1)

        # ── Phase B2: announce blossom detection ──────────────────────────────
        tb2, sb2 = self.section_title(
            "Blossom Detected — odd cycle 5 – 6 – 7",
            "BFS back-edge (6,7) closes an odd cycle: naive augmentation fails here",
        )
        self.show_title(tb2, sb2)
        self.wait(0.5)

        ring, centroid = self.highlight_blossom(nodes, B["blossom_nodes"], edges)
        self.wait(0.8)
        self.hide_title(tb2, sb2)

        # ── Phase B3: contract ────────────────────────────────────────────────
        tb3, sb3 = self.section_title(
            "Contract Blossom → Super-node B",
            "Nodes 5, 6, 7 collapse into a single vertex B in the contracted graph",
        )
        self.show_title(tb3, sb3)

        sn = self.contract_blossom(nodes, B["blossom_nodes"], edges, ring, centroid)
        self.wait(0.5)

        # Redirect edges that touched 5, 6, or 7 (but aren't internal) to point at B.
        # The only external edges that matter for the path are: 8-5 and 5-4.
        # We show them by creating temporary arrows from 8 → B and B → 4.
        sn_center = sn.get_center()
        node8_pos  = to_manim_pos(*NODE_POSITIONS[8])
        node4_pos  = to_manim_pos(*NODE_POSITIONS[4])

        def shrunk_line(start, end, color, width=3.5):
            """Line that stops at node/supernode boundary (r=0.3 or 0.42)."""
            direction = end - start
            d = np.linalg.norm(direction)
            unit = direction / d
            return Line(start + unit * 0.31, end - unit * 0.43,
                        color=color, stroke_width=width)

        tmp_8B = shrunk_line(node8_pos, sn_center, C_PATH_FREE)
        tmp_B4 = shrunk_line(sn_center, node4_pos, C_PATH_FREE)

        self.play(Create(tmp_8B), Create(tmp_B4), run_time=0.6)
        self.play(
            ShowPassingFlash(tmp_8B.copy().set_stroke(width=8, color=C_PATH_FREE),
                             time_width=0.5, run_time=0.6),
            Indicate(sn[0], color=C_PATH_FREE, scale_factor=1.2),
        )
        self.play(
            ShowPassingFlash(tmp_B4.copy().set_stroke(width=8, color=C_PATH_FREE),
                             time_width=0.5, run_time=0.6),
            Indicate(nodes[4][0], color=C_PATH_FREE, scale_factor=1.2),
        )

        self.wait(0.4)
        self.hide_title(tb3, sb3)

        # ── Phase B4: expand / lift ───────────────────────────────────────────
        tb4, sb4 = self.section_title(
            "Expand Blossom — lift path back to original graph",
            "Path 8 → B → 4 lifts to 8 → 5 → 4  (blossom interior: match 6–7)",
        )
        self.show_title(tb4, sb4)

        self.play(FadeOut(tmp_8B), FadeOut(tmp_B4), run_time=0.3)
        self.expand_blossom(nodes, B["blossom_nodes"], edges, sn, centroid)
        self.wait(0.4)

        # Animate the lifted path
        for u, v, kind in B["lifted_path"]:
            col = C_PATH_FREE
            e = self.get_edge(edges, u, v)
            if e:
                e.set_color(col).set_stroke(width=4)
                self.play(
                    self.flash_edge(e, col),
                    Indicate(nodes[v][0], color=col, scale_factor=1.3),
                    run_time=0.55,
                )

        self.wait(0.4)
        self.hide_title(tb4, sb4)

        # ── Phase B5: augment ─────────────────────────────────────────────────
        tb5, sb5 = self.section_title(
            "Step 3 — Augment",
            "Add (8,5), (5,4) and internal blossom edge (6,7).   Matching size: 2 → 4",
        )
        self.show_title(tb5, sb5)

        for u, v in B["flip"]["add"]:
            self.do_augment(edges, nodes, u, v)

        self.wait(0.8)
        self.hide_title(tb5, sb5)

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
