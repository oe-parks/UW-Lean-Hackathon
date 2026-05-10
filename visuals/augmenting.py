from manim import *

# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║                        USER CONFIGURATION                                   ║
# ╠══════════════════════════════════════════════════════════════════════════════╣
# ║  Graph contains a five-node blossom so the contraction/lifting phase of     ║
# ║  Edmonds' algorithm is the main visual focus.                               ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

# ── 1. NODE POSITIONS ─────────────────────────────────────────────────────────
#
#                    7 ─── 8 ─── 9
#                   ╱
#              1 ───── 2
#           ╱             ╲
#     6 ── 5               3
#           ╲             ╱
#                 4
#
#   blossom: odd cycle 1-2-3-4-5-1
#   starting matching: (2,3), (4,5), (7,8)
#   contracted augmenting path: B-7-8-9
#   lifted augmenting path: 1-2-3-7-8-9
#

NODE_POSITIONS = {
    1: (-2.0,  1.6),
    2: ( 1.4,  1.6),
    3: ( 2.5, -0.7),
    4: (-0.3, -2.35),
    5: (-3.1, -0.7),
    6: (-4.9, -1.35),
    7: ( 3.8,  0.55),
    8: ( 5.0,  0.9),
    9: ( 6.2,  0.55),
}

# ── 2. EDGES ──────────────────────────────────────────────────────────────────
EDGE_LIST = [
    (1, 2), (2, 3), (3, 4), (4, 5), (5, 1),  # five-node blossom
    (5, 6),                                  # edge exposed after contraction
    (3, 7), (7, 8), (8, 9),                  # side branch used after contraction
]

# ── 3. AUGMENTATION STEPS ─────────────────────────────────────────────────────
# Keep the scene focused on the blossom contraction instead of spending screen
# space on unrelated trivial augmenting paths.
AUGMENTATION_STEPS = []

# ── 4. BLOSSOM CONFIG ─────────────────────────────────────────────────────────
# Describes the blossom phase shown after the regular augmentation steps.
BLOSSOM = {
    # BFS walk that discovers the blossom.
    # Source is free node 1; the contracted blossom exposes free node 9.
    "bfs_source": 1,
    "bfs_target": 9,

    # Matching before the blossom phase: {(2,3),(4,5),(7,8)}
    # Free nodes: 1, 6, and 9.
    "matching_before": [(2, 3), (4, 5), (7, 8)],

    # The BFS walk shown before the blossom is detected.
    # (u, v, kind)  kind = "free", "matched", or "back" (closes odd cycle)
    "bfs_walk": [
        (1, 2, "free"),
        (2, 3, "matched"),
        (3, 4, "free"),
        (4, 5, "matched"),
        (5, 1, "back"),      # closes odd cycle 1-2-3-4-5-1
    ],

    # The five nodes forming the blossom (odd cycle).
    "blossom_nodes": [1, 2, 3, 4, 5],
    # The blossom edge that closes the cycle (shown as the "collision" edge).
    "blossom_closing_edge": (5, 1),

    # Contract onto node 5, so the existing 5-6 edge becomes the contracted B-6 edge.
    "supernode_pos": (-3.1, -0.7),
    "supernode_label": "B",

    # External blossom edges visible after contraction.
    # 5-6 becomes B-6; 3-7 becomes B-7.
    "contracted_edges": [
        ("B", 6, "plain"),
        ("B", 7, "free"),
    ],

    # Augmenting path found while the blossom is still contracted.
    "contracted_path": [
        ("B", 7, "free"),
        (7, 8, "matched"),
        (8, 9, "free"),
    ],
    "contracted_flip": {
        "remove": [(7, 8)],
        "add": [("B", 7), (8, 9)],
    },

    # Full lifted path in original graph.
    # Matching before: {(2,3),(4,5),(7,8)}.
    # Lifted augmenting path alternates:
    # 1-2 free, 2-3 matched, 3-7 free, 7-8 matched, 8-9 free.
    "lifted_path": [
        (1, 2, "free"),
        (2, 3, "matched"),
        (3, 7, "free"),
        (7, 8, "matched"),
        (8, 9, "free"),
    ],

    "flip": {
        "remove": [(2, 3), (7, 8)],
        "add": [(1, 2), (3, 7), (8, 9)],
    },
    "flip_subtitle": "Flip lifted path: remove (2,3), (7,8); add (1,2), (3,7), (8,9).   Size: 3 → 4",
}

# ── 5. FINAL MATCHING ─────────────────────────────────────────────────────────
FINAL_MATCHING = [(1, 2), (4, 5), (3, 7), (8, 9)]

# ── 6. COLORS ─────────────────────────────────────────────────────────────────
C_BG             = "#ffffff"
C_NODE           = "#000000"
C_MATCHED        = "#2ecc71"
C_PATH_FREE      = "#f0a500"
C_PATH_MAT       = "#e74c3c"
C_EDGE           = "#000000"
C_TEXT           = "#000000"
C_DIM            = "#444444"
C_NODE_LABEL     = "#000000"
C_NODE_LABEL_ON_DARK = "#ffffff"
C_BLOSSOM_RING   = "#9b59b6"    # purple — highlight the odd cycle
C_BLOSSOM_NODE   = C_BLOSSOM_RING
C_SUPERNODE      = C_BLOSSOM_RING
C_BFS_TREE       = "#f0a500"
C_BFS_BACK       = C_PATH_FREE

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
        c = Circle(radius=0.22, color=C_NODE, fill_color=C_NODE,
                   fill_opacity=1, stroke_width=0)
        c.move_to(pos)
        lbl = Text(str(n), font_size=16, color=self._label_color(C_NODE), weight=BOLD)
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

    def mark_matched_edge(self, edge_mob, *node_mobs, color=C_MATCHED, node_color=C_MATCHED):
        edge_mob.set_color(color).set_stroke(width=4.5)
        if node_color is not None:
            for node_mob in node_mobs:
                self.recolor_node(node_mob, node_color)
        self.play(
            self.flash_edge(edge_mob, color),
            run_time=0.6,
        )

    def walk_path(self, edges, nodes, path):
        color_map = {"free": C_PATH_FREE, "matched": C_PATH_MAT}
        for u, v, kind in path:
            col = color_map[kind]
            e = self.get_edge(edges, u, v)
            e.set_color(col).set_stroke(width=4)
            self.play(
                self.flash_edge(e, col),
                run_time=0.5,
            )

    def contracted_connector(self, edges, blossom_nodes, external):
        for n in blossom_nodes:
            connector = self.get_edge(edges, n, external)
            if connector is not None:
                return n, connector
        return None, None

    def contracted_line(self, start, end, color=C_EDGE, width=3.5):
        direction = end - start
        d = np.linalg.norm(direction)
        unit = direction / d
        line = Line(start + unit * 0.56, end - unit * 0.31,
                    color=color, stroke_width=width)
        line.set_z_index(-1)
        return line

    # ── blossom-phase helpers ─────────────────────────────────────────────────

    def make_supernode(self, label="B", pos=None):
        """Return a VGroup (circle + label) for the contracted super-node."""
        c = Circle(radius=0.55, color=C_SUPERNODE, fill_color=C_SUPERNODE,
                   fill_opacity=1, stroke_width=3, stroke_color=WHITE)
        lbl = Text(label, font_size=26, color=WHITE, weight=BOLD)
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
        for n in bn:
            self.recolor_node(nodes[n], C_BLOSSOM_NODE)

        # Draw the blossom cycle in purple.
        blossom_edge_pairs = [(bn[i], bn[(i + 1) % len(bn)]) for i in range(len(bn))]
        for u, v in blossom_edge_pairs:
            e = self.get_edge(edges, u, v)
            if e:
                e.set_color(C_BLOSSOM_RING).set_stroke(width=4.5)

        # Compute centroid for the ring
        positions = [to_manim_pos(*NODE_POSITIONS[n]) for n in bn]
        cx = sum(p[0] for p in positions) / len(positions)
        cy = sum(p[1] for p in positions) / len(positions)
        centroid = np.array([cx, cy, 0])

        radius = max(np.linalg.norm(p - centroid) for p in positions) + 0.55
        ring = DashedVMobject(
            Circle(radius=radius, color=C_BLOSSOM_RING, stroke_width=3),
            num_dashes=24,
        )
        ring.move_to(centroid)

        self.play(
            Create(ring),
            run_time=0.9,
        )
        return ring

    def contract_blossom(self, nodes, blossom_nodes, edges, ring, contract_pos):
        """
        Animate the blossom nodes collapsing into a super-node.
        Returns the supernode VGroup.
        """
        sn = self.make_supernode("B", contract_pos)

        self.play(
            *[mob.animate.move_to(contract_pos).scale(0.1) for mob in
              [nodes[n] for n in blossom_nodes]],
            FadeOut(ring),
            run_time=0.7,
        )
        self.play(GrowFromCenter(sn), run_time=0.6)

        # Hide internal edges properly
        for u, v in [(blossom_nodes[i], blossom_nodes[j])
                     for i in range(len(blossom_nodes)) for j in range(i+1, len(blossom_nodes))]:
            e = self.get_edge(edges, u, v)
            if e:
                e.set_opacity(0)

        return sn

    def expand_blossom(self, nodes, blossom_nodes, edges, sn,
                       temporary_edges=None, final_edges=None):
        """
        Reverse contraction: fade out super-node, restore original nodes/edges.
        """
        temporary_edges = temporary_edges or []
        final_edges = final_edges or set()
        final_nodes = {n for edge in final_edges for n in edge}
        self.play(
            FadeOut(sn),
            *[FadeOut(temp_edge) for temp_edge, _ in temporary_edges],
            run_time=0.5,
        )

        # Restore internal edges
        for u, v in [(blossom_nodes[i], blossom_nodes[j])
                     for i in range(len(blossom_nodes)) for j in range(i+1, len(blossom_nodes))]:
            e = self.get_edge(edges, u, v)
            if e:
                if frozenset((u, v)) in final_edges:
                    edge_color = C_MATCHED
                    edge_width = 4
                else:
                    edge_color = C_EDGE
                    edge_width = 2.5
                e.set_opacity(1)
                e.set_color(edge_color).set_stroke(width=edge_width)

        # Restore nodes at their original positions
        for n in blossom_nodes:
            pos = to_manim_pos(*NODE_POSITIONS[n])
            nodes[n].move_to(pos)
            nodes[n].scale(10)   # undo the .scale(0.1) from contraction
            self.recolor_node(nodes[n], C_MATCHED if n in final_nodes else C_NODE)

        restore_external_anims = [
            original_edge.animate.set_opacity(1).set_color(C_PATH_MAT).set_stroke(width=4.5)
            for _, original_edge in temporary_edges
        ]

        self.play(
            *[GrowFromCenter(nodes[n]) for n in blossom_nodes],
            *restore_external_anims,
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

        self.hide_title(t0, s0)
        self.wait(0.2)

        # ── regular augmentation steps ────────────────────────────────────────
        for step in AUGMENTATION_STEPS:
            t, s = self.section_title(step["title"], step["subtitle"])
            self.show_title(t, s)

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

        # ── Phase B0: show the partial matching ──────────────────────────────
        tb0, sb0 = self.section_title(
            "Step 1 — Partial Matching",
            "Matched edges (2,3), (4,5), and (7,8) leave free nodes 1, 6, and 9",
        )
        self.show_title(tb0, sb0)

        for u, v in B["matching_before"]:
            self.do_augment(edges, nodes, u, v)

        self.wait(0.5)
        self.hide_title(tb0, sb0)

        # ── Phase B1: BFS discovers the blossom ───────────────────────────────
        tb1, sb1 = self.section_title(
            "Step 2 — BFS explores from free node 1",
            "Alternating search reaches an even vertex already in the tree",
        )
        self.show_title(tb1, sb1)

        color_map_bfs = {"free": C_PATH_FREE, "matched": C_PATH_MAT, "back": C_BFS_BACK}
        for u, v, kind in B["bfs_walk"]:
            col = color_map_bfs[kind]
            e = self.get_edge(edges, u, v)
            if e is None:
                continue
            e.set_color(col).set_stroke(width=4)
            self.play(
                self.flash_edge(e, col),
                run_time=0.5,
            )

        self.wait(0.5)
        self.hide_title(tb1, sb1)

        # ── Phase B2: announce blossom detection ──────────────────────────────
        tb2, sb2 = self.section_title(
            "Blossom Detected — odd cycle 1–2–3–4–5",
            "Back-edge (5,1) closes an odd cycle, so Edmonds contracts it",
        )
        self.show_title(tb2, sb2)
        self.wait(0.5)

        ring = self.highlight_blossom(nodes, B["blossom_nodes"], edges)
        self.wait(0.8)
        self.hide_title(tb2, sb2)

        # ── Phase B3: contract ────────────────────────────────────────────────
        tb3, sb3 = self.section_title(
            "Contract Blossom → Super-node B",
            "The contracted node keeps both outside edges: B–6 and B–7",
        )
        self.show_title(tb3, sb3)

        contract_pos = to_manim_pos(*B["supernode_pos"])
        sn = self.contract_blossom(nodes, B["blossom_nodes"], edges, ring, contract_pos)

        def edge_key(u, v):
            return frozenset((u, v))

        color_map_contract = {
            "plain": C_EDGE,
            "free": C_PATH_FREE,
            "matched": C_PATH_MAT,
        }
        contracted_edge_mobs = {}
        temporary_contract_edges = []
        create_contracted_anims = []

        for u, v, kind in B["contracted_edges"]:
            col = color_map_contract[kind]
            if u == B["supernode_label"]:
                external = v
            elif v == B["supernode_label"]:
                external = u
            else:
                continue

            owner, connector = self.contracted_connector(edges, B["blossom_nodes"], external)
            if connector is not None:
                if NODE_POSITIONS[owner] == B["supernode_pos"]:
                    connector.set_color(col).set_stroke(width=3.5 if kind == "plain" else 4)
                    edge_mob = connector
                else:
                    connector.set_opacity(0)
                    edge_mob = self.contracted_line(
                        contract_pos,
                        to_manim_pos(*NODE_POSITIONS[external]),
                        col,
                        width=3.5 if kind == "plain" else 4,
                    )
                    temporary_contract_edges.append((edge_mob, connector))
                    create_contracted_anims.append(Create(edge_mob))

                contracted_edge_mobs[edge_key(B["supernode_label"], external)] = edge_mob

        if create_contracted_anims:
            self.play(*create_contracted_anims, run_time=0.45)

        for u, v, kind in B["contracted_path"]:
            col = color_map_contract[kind]
            if u == B["supernode_label"] or v == B["supernode_label"]:
                external = v if u == B["supernode_label"] else u
                edge_mob = contracted_edge_mobs.get(edge_key(B["supernode_label"], external))
            else:
                edge_mob = self.get_edge(edges, u, v)
            if edge_mob is None:
                continue
            edge_mob.set_color(col).set_stroke(width=4)
            self.play(
                self.flash_edge(edge_mob, col),
            )

        self.wait(0.4)
        self.hide_title(tb3, sb3)

        # ── Phase B4: augment in the contracted graph ─────────────────────────
        tb4, sb4 = self.section_title(
            "Augment In Contracted Graph",
            "Flip B–7–8–9: replace (7,8) with (B,7) and (8,9)",
        )
        self.show_title(tb4, sb4)

        for u, v in B["contracted_flip"]["remove"]:
            edge_mob = self.get_edge(edges, u, v)
            if edge_mob is not None:
                edge_mob.set_color(C_PATH_MAT).set_stroke(width=4.5)
                self.play(self.flash_edge(edge_mob, C_PATH_MAT), run_time=0.45)
                self.play(edge_mob.animate.set_color(C_EDGE).set_stroke(width=2.5), run_time=0.25)

        for u, v in B["contracted_flip"]["add"]:
            if u == B["supernode_label"] or v == B["supernode_label"]:
                external = v if u == B["supernode_label"] else u
                edge_mob = contracted_edge_mobs.get(edge_key(B["supernode_label"], external))
                node_mobs = [sn, nodes[external]]
            else:
                edge_mob = self.get_edge(edges, u, v)
                node_mobs = [nodes[u], nodes[v]]
            if edge_mob is not None:
                self.mark_matched_edge(edge_mob, *node_mobs, color=C_PATH_MAT)

        self.wait(0.8)
        self.hide_title(tb4, sb4)

        # ── Phase B5: expand / lift ───────────────────────────────────────────
        tb5, sb5 = self.section_title(
            "Uncontract Blossom — lift the match",
            "Matched B–7 lifts to (3,7), with internal blossom edge (1,2)",
        )
        self.show_title(tb5, sb5)

        final_edges = {frozenset((u, v)) for u, v in FINAL_MATCHING}
        self.expand_blossom(nodes, B["blossom_nodes"], edges, sn,
                            temporary_contract_edges, final_edges)
        self.wait(0.4)

        for u, v in B["flip"]["remove"]:
            e = self.get_edge(edges, u, v)
            if e:
                self.play(e.animate.set_color(C_EDGE).set_stroke(width=2.5), run_time=0.25)

        reset_anims = [
            e.animate.set_color(C_EDGE).set_stroke(width=2.5)
            for pair, e in edges.items()
            if frozenset(pair) not in final_edges
        ]
        if reset_anims:
            self.play(*reset_anims, run_time=0.35)

        # (3,7) and (8,9) were red after uncontract; now confirm them as matched
        self.play(
            self.get_edge(edges, 3, 7).animate.set_color(C_MATCHED).set_stroke(width=4.5),
            self.get_edge(edges, 8, 9).animate.set_color(C_MATCHED).set_stroke(width=4.5),
            run_time=0.4,
        )

        self.wait(0.8)
        self.hide_title(tb5, sb5)

        # ── final ──────────────────────────────────────────────────────────────
        tf, sf = self.section_title(
            "Maximum Matching Found ✓",
            "No augmenting path exists  ⟹  matching is maximum   (Berge, 1957)",
        )
        self.show_title(tf, sf)

        final_nodes = {n for u, v in FINAL_MATCHING for n in (u, v)}
        self.play(
            LaggedStart(
                *[Indicate(nodes[n][0], color=C_MATCHED, scale_factor=1.35)
                  for n in final_nodes],
                lag_ratio=0.08,
            ),
            run_time=1.3,
        )
        self.play(
            *[self.get_edge(edges, u, v).animate.set_color(C_MATCHED).set_stroke(width=6)
              for u, v in FINAL_MATCHING],
            run_time=0.5,
        )
        self.play(
            *[FadeOut(nodes[n][1]) for n in nodes],
            run_time=0.4,
        )
        self.wait(2.5)
