from manim import *

# ── palette ───────────────────────────────────────────────────────────────────
C_BG        = "#0d1117"
C_NODE      = "#4a90d9"
C_MATCHED   = "#2ecc71"
C_PATH_FREE = "#f0a500"
C_PATH_MAT  = "#e74c3c"
C_EDGE      = "#3a3f4b"
C_TEXT      = "#e6edf3"
C_DIM       = "#8b949e"

config.background_color = C_BG

# Graph:
#   0 ─── 1 ─── 2 ─── 3
#         |     |     |
#         4     5     6 ─── 7
#
# EDGE_LIST
# top row:    (0,1),(1,2),(2,3)
# verticals:  (1,4),(2,5),(3,6)
# bottom:     (6,7)
#
# Step 1 trivial:  augment (0,1)          → matching {(0,1)}
# Step 2 trivial:  augment (4, ?)  — (4,5) not in edges; use (6,7) → matching {(0,1),(6,7)}
# Step 3 interesting: free nodes are 2,3,4,5
#   path: 4 →(1,4 free)→ 1 →(0,1 MATCHED)→ 0   — 0 is matched endpoint, dead end
#   path: 4 →(1,4 free)→ 1 →(1,2 free)→ 2 →(2,5 free)→ 5  — all free, boring
#   path: 5 →(2,5 free)→ 2 →(1,2 free)→ 1 →(1,4 free)→ 4  — boring
#   path: 4 →(1,4)→ 1 →(0,1 MATCHED)→ 0 ...dead
#
# Hmm. Let me try matching {(1,2),(6,7)} after step 2.
# Free nodes: 0,3,4,5
# Interesting path: 0 →(0,1 free)→ 1 →(1,2 MATCHED)→ 2 →(2,3 free)→ 3
# YES! This is the canonical example. 0 and 3 are free, path passes through
# matched edge (1,2), alternating perfectly.
#
# So: Step1 augment (1,2), Step2 augment (6,7), Step3 interesting 0→1→2→3
# Step4 augment remaining (4, ?) and (5, ?) — but what's left?
# After step3 flip: (0,1) and (2,3) become matched, (1,2) unmatched
# matching = {(0,1),(2,3),(6,7)}
# free: 4,5
# step4: augment (4,...5) — is there an edge (4,5)? not in our list.
# Need to add (4,5) to edges. Or use (2,5) and reroute.
# path: 4 →(1,4)→ 1[matched via 0,1] →(0,1 MATCHED)→ 0: dead (0 is endpoint)
# path: 5 →(2,5)→ 2[matched via 2,3] →(2,3 MATCHED)→ 3: dead (3 matched endpoint)
# path: 4 →(1,4)→ 1[matched] →(1,2 FREE now)→ 2[matched] →(2,5 free)→ 5
# YES! 4→1(free edge 1,4)→matched node 1→free edge (1,2)→matched node 2→free edge (2,5)→5
# Wait: after step3 flip, (1,2) is UNMATCHED and (0,1),(2,3) are MATCHED.
# path 4→1→2→5: edges (1,4) free, (1,2) free, (2,5) free — all free, boring again.
#
# I need a path that actually traverses a matched edge in the middle.
# path 4→1(free 1,4)→0(matched 0,1)→? : 0 has edges (0,1) only. dead end.
# path 5→2(free 2,5)→3(matched 2,3)→6(free 3,6)→7(matched 6,7)→? : 7 has edge (6,7) only. dead.
# path 5→2(free)→3(matched 2,3)→6(free 3,6)→7(matched 6,7) — 7 is matched endpoint. still dead.
#
# For a valid augmenting path through matched edges: need the path to EXIT the matched
# segment to a genuinely FREE vertex. This requires a free vertex adjacent to a matched
# vertex via a free edge, where that matched vertex is NOT the endpoint of its matched edge
# but rather INTERIOR to the alternating path.
# 
# Actually re-read: an alternating path starting at free u goes:
# u --(free)--> v --(matched)--> w --(free)--> x --(matched)--> y ...
# u and the final vertex must be free (unmatched).
# v is matched (part of edge v--w), w is matched (same edge v--w).
# After v--w (matched), we go w--(free)-->x. x must be either free (path ends) or matched.
# 
# So VALID interesting path: free 4 →(1,4 free)→ matched 1 →(0,1 MATCHED)→ matched 0 →(? free)→ free ?
# 0 only connects to 1 in our graph. Dead end.
#
# The graph needs node 0 to have another neighbor for this to work.
# ADD edge (0,5):
# Then after matching {(0,1),(2,3),(6,7)}, path:
# 4 →(1,4 free)→ 1 →(0,1 MATCHED)→ 0 →(0,5 free)→ 5
# 4 and 5 are free! This is a perfect interesting alternating path!
# ─────────────────────────────────────────────────────────────────────────────

class AugmentingPath(Scene):
    POSITIONS = {
        0: LEFT  * 4.5 + UP   * 1.5,
        1: LEFT  * 1.5 + UP   * 1.5,
        2: RIGHT * 1.5 + UP   * 1.5,
        3: RIGHT * 4.5 + UP   * 1.5,
        4: LEFT  * 1.5 + DOWN * 1.5,
        5: LEFT  * 4.5 + DOWN * 1.5,
        6: RIGHT * 4.5 + DOWN * 1.5,
        7: RIGHT * 1.5 + DOWN * 1.5,
    }

    # Edge layout:
    # top row:   0─1─2─3
    # verticals: 1─4, 2─7, 3─6
    # bottom:    4─5 (will be added via (0,5) cross? No, let's do:
    # cross:     0─5
    # bottom:    6─7
    EDGE_LIST = [
        (0,1),(1,2),(2,3),   # top row
        (3,6),(2,7),(1,4),   # verticals
        (6,7),               # bottom right
        (0,5),(4,5),         # cross + bottom left
    ]

    def make_node(self, n):
        c = Circle(radius=0.30, color=C_NODE, fill_color=C_NODE,
                   fill_opacity=1, stroke_width=0)
        c.move_to(self.POSITIONS[n])
        lbl = Text(str(n), font_size=20, color=C_BG, weight=BOLD)
        lbl.move_to(self.POSITIONS[n])
        return VGroup(c, lbl)

    def make_edge(self, u, v):
        return Line(self.POSITIONS[u], self.POSITIONS[v],
                    color=C_EDGE, stroke_width=2.5)

    def get_edge(self, edges, u, v):
        return edges.get((u,v)) or edges.get((v,u))

    def recolor_node(self, node_mob, color):
        node_mob[0].set_fill(color, opacity=1)
        node_mob[0].set_stroke(color, width=0)

    def flash_edge(self, edge_mob, color):
        return ShowPassingFlash(
            edge_mob.copy().set_color(color).set_stroke(width=7),
            time_width=0.45, run_time=0.55
        )

    def section_title(self, text, sub=""):
        t = Text(text, font_size=25, color=C_TEXT, weight=BOLD).to_edge(UP, buff=0.25)
        s = Text(sub, font_size=17, color=C_DIM, slant=ITALIC).next_to(t, DOWN, buff=0.1) if sub else None
        return t, s

    def show_title(self, t, s):
        anims = [FadeIn(t)]
        if s: anims.append(FadeIn(s))
        self.play(*anims)

    def hide_title(self, t, s):
        anims = [FadeOut(t)]
        if s: anims.append(FadeOut(s))
        self.play(*anims)

    def augment_edge(self, edges, nodes, u, v):
        """Turn a single edge into a matched edge with flash."""
        e = self.get_edge(edges, u, v)
        e.set_color(C_MATCHED).set_stroke(width=4)
        self.recolor_node(nodes[u], C_MATCHED)
        self.recolor_node(nodes[v], C_MATCHED)
        self.play(Flash(e.get_center(), color=C_MATCHED,
                        line_length=0.22, num_lines=8, run_time=0.4))

    def walk_path(self, edges, nodes, seq):
        """
        seq: list of (u, v, color) tuples defining the path walk.
        color is C_PATH_FREE or C_PATH_MAT.
        """
        for u, v, col in seq:
            e = self.get_edge(edges, u, v)
            e.set_color(col).set_stroke(width=4)
            self.play(
                self.flash_edge(e, col),
                Indicate(nodes[v][0], color=col, scale_factor=1.3),
                run_time=0.5
            )

    def construct(self):
        nodes = {n: self.make_node(n) for n in self.POSITIONS}
        edges = {(u,v): self.make_edge(u,v) for u,v in self.EDGE_LIST}

        # ── INTRO ─────────────────────────────────────────────────────────────
        t0, s0 = self.section_title(
            "Augmenting Path Discovery",
            "Edmonds' Maximum Matching Algorithm"
        )
        self.show_title(t0, s0)
        self.wait(0.3)

        self.play(LaggedStart(*[Create(e) for e in edges.values()], lag_ratio=0.05), run_time=1.1)
        self.play(LaggedStart(*[GrowFromCenter(n) for n in nodes.values()], lag_ratio=0.05), run_time=0.9)
        self.wait(0.6)

        leg = VGroup(
            self._leg("Unmatched edge",     C_EDGE),
            self._leg("Matched edge",       C_MATCHED),
            self._leg("Free edge on path",  C_PATH_FREE),
            self._leg("Matched edge on path", C_PATH_MAT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        leg.to_corner(DR, buff=0.35)
        leg_bg = SurroundingRectangle(leg, color="#21262d", fill_color="#161b22",
                                      fill_opacity=0.92, corner_radius=0.1, buff=0.15)
        self.play(FadeIn(leg_bg), FadeIn(leg))
        self.hide_title(t0, s0)
        self.wait(0.2)

        # ══════════════════════════════════════════════════════════════════════
        # STEP 1 — trivial: single free edge (1,2)
        # ══════════════════════════════════════════════════════════════════════
        t1, s1 = self.section_title(
            "Step 1 — Simplest augmenting path",
            "Matching is empty — any single edge between two free vertices works"
        )
        self.show_title(t1, s1)

        for n in [1, 2]:
            self.recolor_node(nodes[n], C_PATH_FREE)
        self.play(*[Indicate(nodes[n][0], color=C_PATH_FREE, scale_factor=1.45)
                    for n in [1, 2]], run_time=0.7)

        e12 = self.get_edge(edges, 1, 2)
        e12.set_color(C_PATH_FREE).set_stroke(width=4)
        self.play(self.flash_edge(e12, C_PATH_FREE), run_time=0.55)
        self.wait(0.4)
        self.hide_title(t1, s1)

        t1b, s1b = self.section_title(
            "Step 1 — Augment",
            "Flip: edge (1,2) joins the matching.   Matching size: 0 → 1"
        )
        self.show_title(t1b, s1b)
        self.augment_edge(edges, nodes, 1, 2)
        self.wait(0.8)
        self.hide_title(t1b, s1b)

        # ══════════════════════════════════════════════════════════════════════
        # STEP 2 — trivial: single free edge (6,7)
        # ══════════════════════════════════════════════════════════════════════
        t2, s2 = self.section_title(
            "Step 2 — Another trivial augmenting path",
            "Nodes 6 and 7 are still free — edge (6,7) is a valid path"
        )
        self.show_title(t2, s2)

        for n in [6, 7]:
            self.recolor_node(nodes[n], C_PATH_FREE)
        self.play(*[Indicate(nodes[n][0], color=C_PATH_FREE, scale_factor=1.45)
                    for n in [6, 7]], run_time=0.7)

        e67 = self.get_edge(edges, 6, 7)
        e67.set_color(C_PATH_FREE).set_stroke(width=4)
        self.play(self.flash_edge(e67, C_PATH_FREE), run_time=0.55)
        self.wait(0.4)
        self.hide_title(t2, s2)

        t2b, s2b = self.section_title(
            "Step 2 — Augment",
            "Flip: edge (6,7) joins the matching.   Matching size: 1 → 2"
        )
        self.show_title(t2b, s2b)
        self.augment_edge(edges, nodes, 6, 7)
        self.wait(0.8)
        self.hide_title(t2b, s2b)

        # ══════════════════════════════════════════════════════════════════════
        # STEP 3 — INTERESTING: path 0 → 1 → 2 → 3
        # Matching = {(1,2),(6,7)}, free nodes = {0,3,4,5}
        # Path: free 0 →(free edge 0,1)→ matched 1 →(MATCHED edge 1,2)→ matched 2 →(free edge 2,3)→ free 3
        # This is the key: the path REROUTES through matched edge (1,2) to grow the matching
        # ══════════════════════════════════════════════════════════════════════
        t3, s3 = self.section_title(
            "Step 3 — First interesting augmenting path",
            "Path must reroute through an existing matched edge"
        )
        self.show_title(t3, s3)

        # highlight free endpoints
        for n in [0, 3]:
            self.recolor_node(nodes[n], C_PATH_FREE)
        self.play(*[Indicate(nodes[n][0], color=C_PATH_FREE, scale_factor=1.45)
                    for n in [0, 3]], run_time=0.7)

        # walk: 0→1 free (orange), 1→2 MATCHED (red), 2→3 free (orange)
        self.walk_path(edges, nodes, [
            (0, 1, C_PATH_FREE),
            (1, 2, C_PATH_MAT),    # traversing the matched edge!
            (2, 3, C_PATH_FREE),
        ])
        self.wait(0.6)
        self.hide_title(t3, s3)

        t3b, s3b = self.section_title(
            "Step 3 — Augment (flip the path)",
            "Matched edge (1,2) is removed; free edges (0,1) and (2,3) join the matching"
        )
        self.show_title(t3b, s3b)

        # remove (1,2) from matching
        e12.set_color(C_EDGE).set_stroke(width=2.5)
        self.recolor_node(nodes[1], C_NODE)
        self.recolor_node(nodes[2], C_NODE)

        # add (0,1) and (2,3)
        self.augment_edge(edges, nodes, 0, 1)
        self.augment_edge(edges, nodes, 2, 3)
        self.wait(0.8)
        self.hide_title(t3b, s3b)

        # ══════════════════════════════════════════════════════════════════════
        # STEP 4 — INTERESTING: path 4 → 1 → 0 → 5
        # Matching = {(0,1),(2,3),(6,7)}, free nodes = {4,5,7... wait
        # 7 is matched via (6,7). free nodes = {4,5}
        # path: free 4 →(1,4 free)→ matched 1 →(0,1 MATCHED)→ matched 0 →(0,5 free)→ free 5
        # PERFECT second interesting path!
        # ══════════════════════════════════════════════════════════════════════
        t4, s4 = self.section_title(
            "Step 4 — Another alternating path",
            "Path threads through two matched nodes to connect free vertices 4 and 5"
        )
        self.show_title(t4, s4)

        for n in [4, 5]:
            self.recolor_node(nodes[n], C_PATH_FREE)
        self.play(*[Indicate(nodes[n][0], color=C_PATH_FREE, scale_factor=1.45)
                    for n in [4, 5]], run_time=0.7)

        # walk: 4→1 free, 1→0 MATCHED, 0→5 free
        self.walk_path(edges, nodes, [
            (4, 1, C_PATH_FREE),
            (1, 0, C_PATH_MAT),    # traversing matched edge (0,1)!
            (0, 5, C_PATH_FREE),
        ])
        self.wait(0.6)
        self.hide_title(t4, s4)

        t4b, s4b = self.section_title(
            "Step 4 — Augment",
            "Matched edge (0,1) is removed; free edges (1,4) and (0,5) join the matching"
        )
        self.show_title(t4b, s4b)

        # remove (0,1)
        e01 = self.get_edge(edges, 0, 1)
        e01.set_color(C_EDGE).set_stroke(width=2.5)
        self.recolor_node(nodes[0], C_NODE)
        self.recolor_node(nodes[1], C_NODE)

        # add (1,4) and (0,5)
        self.augment_edge(edges, nodes, 1, 4)
        self.augment_edge(edges, nodes, 0, 5)
        self.wait(0.8)
        self.hide_title(t4b, s4b)

        # ══════════════════════════════════════════════════════════════════════
        # FINAL — matching {(1,4),(0,5),(2,3),(6,7)}, all 8 nodes matched
        # ══════════════════════════════════════════════════════════════════════
        tf, sf = self.section_title(
            "Maximum Matching Found ✓",
            "No augmenting path exists  ⟹  matching is maximum   (Berge, 1957)"
        )
        self.show_title(tf, sf)

        self.play(LaggedStart(
            *[Indicate(nodes[n][0], color=C_MATCHED, scale_factor=1.35)
              for n in self.POSITIONS],
            lag_ratio=0.08), run_time=1.3)

        final_edges = [(1,4),(0,5),(2,3),(6,7)]
        self.play(*[
            self.get_edge(edges, u, v).animate.set_stroke(width=6)
            for u,v in final_edges
        ], run_time=0.5)

        self.wait(2.5)

    def _leg(self, label, color):
        dot = Circle(radius=0.09, color=color, fill_color=color,
                     fill_opacity=1, stroke_width=0)
        txt = Text(label, font_size=14, color=C_DIM)
        return VGroup(dot, txt).arrange(RIGHT, buff=0.15)
