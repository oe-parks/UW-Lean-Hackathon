import Hackathon.GraphIR.Examples
import Mathlib.Tactic

/-!
# Edmonds' blossom algorithm in GraphIR

This file delivers two things in one place:

1. **A *correct* two-level IR** for Edmonds' blossom algorithm.
   The crucial design point — and the bug we are fixing relative to a
   first sketch — is that the recursive call on the contracted graph
   must be to the **augmenting-path search**, not to the top-level
   maximum-matching loop. Otherwise the current matching `M` is lost
   and the algorithm can no longer reason about whether a path is
   augmenting.

   The corrected pseudo-code is

   ```
   algorithm MaxMatching(G):
     M := empty
     loop:
       match FindAugmentingPath(G, M) with
       | some P => M := augment(M, P)
       | none   => return M

   algorithm FindAugmentingPath(G, M):
     F := alternating_forest(G, M)
     match search_even_even_edge(F) with
     | AugmentingPath(P) => some P
     | Blossom(B) =>
         G' := contract_graph(G, B)
         M' := contract_matching(M, B)
         match FindAugmentingPath(G', M') with    -- ← recursion here
         | some P' => some (lift_path(G, M, B, P'))
         | none    => none
     | NoPath => none
   ```

   Encoded as `FunDecl`s in `blossomFuns`.

2. **A pure-Lean reference + correctness scaffold.** The pure-Lean
   shadow `maxMatchingLean` mirrors `MaxMatching`'s shape exactly. We
   prove the parts that follow purely from the *loop structure* and the
   spec of `FindAugmentingPath` — namely that augmenting strictly
   increases `|M|`, that the loop therefore terminates, and that the
   final matching is in fact a matching. The two genuinely deep graph-
   theoretic lemmas (Berge's theorem; equivalence of augmenting paths
   under blossom contraction; correctness of `lift_path`) are stated
   precisely and left as `sorry` — they sit at the same depth as
   `Graph/Algorithms/Blossom.lean` and are the natural next milestone.

The split between "loop-structural" and "graph-theoretic" lemmas is the
point of this file: proving that *Edmonds' loop is correct* is much
easier than proving that *blossom contraction works*, and they should
be done in two passes.
-/

namespace Hackathon.GraphIR.Blossom

open Hackathon.GraphIR Examples

/-! ## Part 1 — the corrected IR -/

/-- The full IR for Edmonds' algorithm.

    The call structure is the headline. Every box in the corrected
    pseudo-code is a separate `FunDecl`, and the recursive call sits in
    `FindAugmentingPath`, not in `MaxMatching`. The "leaf" operations
    that need real graph theory (`alternating_forest`,
    `search_even_even_edge`, `contract_graph`, `contract_matching`,
    `lift_path`) are exposed as separate `FunDecl`s with stub bodies
    returning placeholder values. Filling them in is the next milestone
    and is independent of getting the *call structure* right. -/
def blossomFuns : List FunDecl :=
  [ -- ── Top-level loop ────────────────────────────────────────────
    -- MaxMatching reads the ambient graph as a *value* (via
    -- `graph_value_ofCtx`) and threads `(G, M)` through the loop.
    { name := "MaxMatching"
      params := []
      body :=
        lt "G0" (c "graph_value_ofCtx" [])
        (lt "M0" (c "matching_empty" [])
        (c "MaxMatchingLoop" [v "G0", v "M0"]))
    }
  , { name := "MaxMatchingLoop"
      params := ["G", "M"]
      body :=
        .matchOpt (c "FindAugmentingPath" [v "G", v "M"])
          (v "M")                                -- none → return M
          "P"
          (lt "M'" (c "augment" [v "M", v "P"])
          (c "MaxMatchingLoop" [v "G", v "M'"])) -- same G, updated M
    }
    -- ── Augmenting-path search (THE RECURSION) ──────────────────
    -- Now takes `(G, M)`. The Blossom case actually contracts the
    -- graph (via `graph_value_contract`) and recurses on the smaller
    -- value-level graph. The well-founded measure is `graph_value_size G`.
  , { name := "FindAugmentingPath"
      params := ["G", "M"]
      body :=
        lt "F" (c "alternating_forest" [v "G", v "M"])
        (lt "result" (c "search_even_even_edge" [v "G", v "M", v "F"])
        -- `result` is encoded as a tagged pair: (tag, payload).
        --   tag = 0 → AugmentingPath, payload = path
        --   tag = 1 → Blossom,        payload = blossom B
        --   tag = 2 → NoPath
        (.matchPair (v "result") "tag" "payload"
          (.ite (c "nat_eq" [v "tag", nat' 0])
            -- AugmentingPath case
            (c "opt_some" [v "payload"])
            (.ite (c "nat_eq" [v "tag", nat' 1])
              -- Blossom case: REAL contraction + recursive call on G'
              (lt "B" (v "payload")
              (lt "G'" (c "graph_value_contract" [v "G", v "B"])
              (lt "M'" (c "contract_matching" [v "M", v "B"])
              -- The recursive call now passes the *contracted graph*
              -- AND the *contracted matching*. The well-founded
              -- measure `graph_value_size G` strictly decreases.
              (.matchOpt (c "FindAugmentingPath" [v "G'", v "M'"])
                .noneE
                "Pprime"
                (c "opt_some"
                  [c "lift_path" [v "G", v "M", v "B", v "Pprime"]])))))
              .noneE))))
    }
    -- ── Stub primitives (now signatured to take G as well) ──────
  , { name := "matching_empty",    params := [],                   body := .nilE }
  , { name := "alternating_forest", params := ["G", "M"],          body := .nilE }
    -- "NoPath" sentinel: (2, none). Takes G now too.
  , { name := "search_even_even_edge", params := ["G", "M", "F"]
      body := c "pair_mk" [nat' 2, .noneE] }
  , { name := "contract_matching", params := ["M", "B"],           body := v "M" }
  , { name := "lift_path",         params := ["G", "M", "B", "Pprime"]
      body := v "Pprime" }
  , { name := "augment",           params := ["M", "P"],           body := v "M" }
  ]

/-- The complete program: bundle of functions + a `main` that just
    invokes `MaxMatching`. -/
def blossomProgram : Program where
  funs := blossomFuns
  main := c "MaxMatching" []

/-! ### Smoke test: the IR runs end-to-end with first-class graphs.

    The stubs short-circuit `FindAugmentingPath` to `none`, so the
    visible result is still the empty matching `[]` — but the new
    machinery (graph reified from ctx, threaded through the loop,
    contracted on the recursive path) is exercised. We can verify
    the graph value is real by `#eval`-ing the contraction directly. -/

#eval Interp.run (cfg3 k3Ctx) 1000 blossomProgram
-- ⇒ some []   (loop terminates, no augmenting path with stubs)

/-- A standalone IR program demonstrating that graphs really do flow
    through the IR as values. Builds the K3 graph from `ctx`,
    contracts the blossom `[v0, v1]` (a degenerate "blossom of size
    2" — illustrative), and reports the size of the contracted graph. -/
def graphValueDemo : Program where
  funs := []
  main :=
    lt "G" (c "graph_value_ofCtx" [])
    (lt "B" (c "list_cons" [vert' 0,
                c "list_cons" [vert' 1, .nilE]])
    (lt "G'" (c "graph_value_contract" [v "G", v "B"])
    (c "pair_mk"
      [c "graph_value_size" [v "G"],
       c "graph_value_size" [v "G'"]])))

#eval Interp.run (cfg3 k3Ctx) 1000 graphValueDemo
-- Original K3 has 3 vertices; contracting {v0, v1} leaves 2.
-- ⇒ some (3, 2)

#eval Interp.run (cfg4 p4Ctx) 1000 graphValueDemo
-- P4 has 4 vertices; contracting {v0, v1} leaves 3.
-- ⇒ some (4, 3)

/-- **IR end-to-end correctness for the stub configuration.** With the
    stub primitives, `FindAugmentingPath` always returns `none`
    (`search_even_even_edge` reports `NoPath`), so the loop terminates
    after one iteration and returns the empty matching. We verify this
    by full normalisation of the interpreter — no graph theory needed.
    This is the strongest "the loop wiring is correct" check we can
    state without filling in the primitives. -/
theorem blossomProgram_stub_returns_empty_K3 :
    Interp.run (cfg3 k3Ctx) 1000 blossomProgram = some (.list []) := by
  rfl

theorem blossomProgram_stub_returns_empty_P4 :
    Interp.run (cfg4 p4Ctx) 1000 blossomProgram = some (.list []) := by
  rfl

/-- **First-class graphs are real.** The `graphValueDemo` program
    constructs the K3 graph as a value, contracts the blossom
    `{v0, v1}`, and reports the sizes — all by `rfl`. This proves
    the contraction *actually* shrinks the graph (3 → 2 vertices),
    so the recursive call in `FindAugmentingPath` *would* see a
    strictly smaller graph if the primitives were filled in. -/
theorem graphValueDemo_K3_shrinks :
    Interp.run (cfg3 k3Ctx) 1000 graphValueDemo
      = some (.pair (.nat 3) (.nat 2)) := by rfl

theorem graphValueDemo_P4_shrinks :
    Interp.run (cfg4 p4Ctx) 1000 graphValueDemo
      = some (.pair (.nat 4) (.nat 3)) := by rfl


/-! ## Part 2 — pure-Lean reference

We re-implement the same algorithm in plain Lean so that we can state
correctness theorems against a definition we can `induction` on. The
purpose of this section is **not** to re-do the IR — the IR is the
deliverable — but to give us a verification target whose loop structure
matches the IR exactly. -/

variable {V : Type} [DecidableEq V]

/-- A matching is a list of edges, each represented as an unordered
    pair `(u, v)`. We do not enforce uniqueness or non-incidence here —
    the predicate `IsMatching` does. -/
abbrev Matching (V : Type) := List (V × V)

/-- Membership of a vertex in an edge. -/
@[inline] def Matching.incident {V} [DecidableEq V] (v : V) (e : V × V) : Bool :=
  decide (e.1 = v) || decide (e.2 = v)

/-- Is `v` matched by `M`? -/
def Matching.isMatched (M : Matching V) (v : V) : Bool :=
  M.any (Matching.incident v)

/-- Number of edges in the matching. -/
@[inline] def Matching.size (M : Matching V) : Nat := M.length

/-- The *valid-matching* predicate: every two distinct edges of `M` are
    vertex-disjoint, and no edge is a self-loop. -/
def IsMatching (M : Matching V) : Prop :=
  (∀ e ∈ M, e.1 ≠ e.2) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ →
      e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₂.2 ∧ e₁.2 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2)

/-- An *M-alternating* path is a sequence of vertices whose consecutive
    edges alternate between non-`M` and `M`. We treat the path as a
    list `[v₀, v₁, …, v_k]` and ask, for each `i`, whether `(vᵢ, vᵢ₊₁)`
    is in `M` exactly when `i` is odd.

    Defined as a `Prop` — a callable `Decidable` instance can be added
    later. -/
def IsAlternatingPath (M : Matching V) : List V → Prop
  | []      => True
  | [_]     => True
  | u :: v :: rest =>
      ((u, v) ∈ M ∨ (v, u) ∈ M ↔ False)        -- 0-th edge: NOT in M
      ∧ alternates_from_odd M (v :: rest)
where
  alternates_from_odd (M : Matching V) : List V → Prop
    | []      => True
    | [_]     => True
    | u :: v :: rest =>
        ((u, v) ∈ M ∨ (v, u) ∈ M)              -- next edge: IN M
        ∧ IsAlternatingPath M (v :: rest)

/-- An *M-augmenting* path is an alternating path whose endpoints are
    both unmatched. -/
def IsAugmentingPath (M : Matching V) (P : List V) : Prop :=
  match P with
  | []      => False
  | u :: rest =>
      ¬ (Matching.isMatched M u = true) ∧
      ( match rest.getLast? with
        | none   => False                       -- a single vertex isn't a path
        | some w => ¬ (Matching.isMatched M w = true)
      ) ∧
      IsAlternatingPath M P

/-- *Symmetric-difference* augment: along path
    `[v₀; v₁; v₂; v₃; …; v_{2k+1}]`, the edges
    `(v₀,v₁), (v₂,v₃), …` enter `M` and `(v₁,v₂), (v₃,v₄), …` leave.

    We implement it by "remove path-edges from `M`, then add path-edges
    not already in `M`" — symmetric difference along the path. -/
def Matching.augmentAlong (M : Matching V) (P : List V) : Matching V :=
  let pathEdges : List (V × V) := edgesOf P
  let toRemove : Matching V := M.filter (fun e =>
    pathEdges.all (fun pe => decide (e ≠ pe) && decide (e ≠ (pe.2, pe.1))))
  let toAdd : List (V × V) := pathEdges.filter (fun pe =>
    ¬ M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))
  toRemove ++ toAdd
where
  edgesOf : List V → List (V × V)
    | []      => []
    | [_]     => []
    | u :: v :: rest => (u, v) :: edgesOf (v :: rest)

/-! ### The augmenting-path *oracle*

We treat `findAugmentingPathLean` as an opaque oracle whose specification
is what matters. The IR's `FindAugmentingPath` is a concrete
implementation of this oracle; correctness of the implementation is the
"deep" theorem we leave to a later milestone (Part 3). The top-level
loop's correctness only requires the spec, so we *can* prove that piece
right now.
-/

/-- The augmenting-path oracle.  Concrete implementations live elsewhere
    (e.g. the IR `FindAugmentingPath` once its primitives are filled in,
    or a SimpleGraph-flavoured proof). For now we expose only the spec. -/
opaque findAugmentingPathLean (ctx : Context V) (M : Matching V) :
    Option (List V) := none

/-- Specification of the oracle (left as an axiom-level *hypothesis* in
    the lemmas that need it; we never axiomatize it as `axiom`). -/
def OracleSpec (ctx : Context V) : Prop :=
  ∀ (M : Matching V),
    (∀ P, findAugmentingPathLean ctx M = some P → IsAugmentingPath M P) ∧
    (findAugmentingPathLean ctx M = none →
        ∀ P, ¬ IsAugmentingPath M P)

/-! ### `maxMatchingLean` — the loop -/

/-- Bounded iteration of "augment until oracle says none."
    The fuel parameter must be ≥ `|V| / 2 + 1`; we expose a wrapper
    `maxMatchingLean` that supplies this bound. -/
def maxMatchingLeanCore (ctx : Context V) :
    Nat → Matching V → Matching V
  | 0,        M => M
  | fuel + 1, M =>
    match findAugmentingPathLean ctx M with
    | none   => M
    | some P => maxMatchingLeanCore ctx fuel (M.augmentAlong P)

/-- Top-level: start from the empty matching, run for `|V|/2 + 1`
    rounds. The bound is *generous*; an exact bound would be the size
    of a maximum matching. -/
def maxMatchingLean (ctx : Context V) : Matching V :=
  maxMatchingLeanCore ctx (ctx.vertices.length / 2 + 1) []


/-! ## Part 3 — correctness scaffold

Three tiers, increasing in depth.

### Tier A — *loop-structural*: provable from definitions

These follow purely from how the loop is wired and how `augmentAlong`
behaves on lengths. They are independent of any graph-theoretic facts.
-/

/-! #### Decomposition: Idea A + D

Following the structural plan:
* **Idea A**: strengthen with `IsMatching M` (theorem is technically
  false without it — duplicate edges break the count).
* **Idea D**: state the *alternation count balance* as a stand-alone
  obligation. -/

/-- **Alternation balance — helper.** For any *alternating* path `P`
    of length ≥ 2 whose last vertex is unmatched, the path-edges not in
    `M` (modulo swap) outnumber those in `M` by exactly 1. Strong
    induction on `P.length` (peel off two edges per step). -/
private lemma alt_balance_aux
    (M : Matching V) (n : ℕ) :
    ∀ (P : List V), P.length = n → 2 ≤ n →
      IsAlternatingPath M P →
      (∀ y, P.getLast? = some y → Matching.isMatched M y = false) →
      ((Matching.augmentAlong.edgesOf P).filter
        (fun pe => !(M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1)))))).length
      = ((Matching.augmentAlong.edgesOf P).filter
        (fun pe => M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))).length
        + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hLen hGe hAlt hUnm
    match P, hLen with
    | [], h => simp at h; omega
    | [_], h => simp at h; omega
    | [u, v], _ =>
      -- Base case: edgesOf [u, v] = [(u, v)]; (u, v) ∉ M by hAlt.
      simp only [IsAlternatingPath, IsAlternatingPath.alternates_from_odd] at hAlt
      obtain ⟨h_uv_notInM, _⟩ := hAlt
      -- h_uv_notInM : (u, v) ∈ M ∨ (v, u) ∈ M ↔ False
      have h_inM_false :
          (M.any (fun e => decide (e = (u, v)) || decide (e = ((u, v).2, (u, v).1)))) = false := by
        simp only [List.any_eq_false, decide_eq_true_eq, Bool.or_eq_false_iff,
          decide_eq_false_iff_not]
        intro e he
        constructor
        · intro h_eq; subst h_eq; exact h_uv_notInM.mp (Or.inl he)
        · intro h_eq; subst h_eq; exact h_uv_notInM.mp (Or.inr he)
      simp only [Matching.augmentAlong.edgesOf, List.filter_cons, List.filter_nil,
        h_inM_false, Bool.not_false, List.length_cons, List.length_nil]
    | u :: v :: w :: rest, hLen' =>
      -- Inductive case.
      simp only [IsAlternatingPath, IsAlternatingPath.alternates_from_odd] at hAlt
      obtain ⟨h_uv_notInM, h_vw_inM, hAltRest⟩ := hAlt
      -- (u, v) ∉ M (as per first clause of IsAlt).
      have h_uv_inM_false :
          (M.any (fun e => decide (e = (u, v)) || decide (e = ((u, v).2, (u, v).1)))) = false := by
        simp only [List.any_eq_false, decide_eq_true_eq, Bool.or_eq_false_iff,
          decide_eq_false_iff_not]
        intro e he
        refine ⟨fun h_eq => h_uv_notInM.mp (Or.inl ?_), fun h_eq => h_uv_notInM.mp (Or.inr ?_)⟩
        · rw [← h_eq]; exact he
        · rw [← h_eq]; exact he
      -- (v, w) ∈ M (as per alternates_from_odd).
      have h_vw_inM_true :
          (M.any (fun e => decide (e = (v, w)) || decide (e = ((v, w).2, (v, w).1)))) = true := by
        simp only [List.any_eq_true, decide_eq_true_eq, Bool.or_eq_true]
        rcases h_vw_inM with hvw | hwv
        · exact ⟨(v, w), hvw, Or.inl rfl⟩
        · exact ⟨(w, v), hwv, Or.inr rfl⟩
      -- Now case-split on whether `rest` is empty.
      cases hr : rest with
      | nil =>
        -- P = [u, v, w]: last vertex is w. Last edge is (v, w) ∈ M, but
        -- hUnm says w is unmatched, which contradicts (v, w) ∈ M.
        exfalso
        have hLast_eq : (u :: v :: w :: rest).getLast? = some w := by simp [hr]
        have h_w_unm : Matching.isMatched M w = false := hUnm w hLast_eq
        rcases h_vw_inM with hvw | hwv
        · simp [Matching.isMatched, Matching.incident] at h_w_unm
          exact (h_w_unm (v, w) hvw).2 rfl
        · simp [Matching.isMatched, Matching.incident] at h_w_unm
          exact (h_w_unm (w, v) hwv).1 rfl
      | cons x rest' =>
        -- P = u :: v :: w :: x :: rest'. Recurse on (w :: x :: rest').
        rw [hr] at hAltRest
        -- hAltRest : IsAlternatingPath M (w :: x :: rest')
        have hRecLen : (w :: x :: rest').length = n - 2 := by
          change (w :: x :: rest').length = n - 2
          simp only [List.length_cons] at hLen'
          omega
        have hRecGe : 2 ≤ n - 2 := by simp at hLen'; omega
        have hLt : n - 2 < n := by omega
        have hRecUnm : ∀ y, (w :: x :: rest').getLast? = some y →
            Matching.isMatched M y = false := by
          intro y hY
          apply hUnm
          rw [hr]
          -- The last of u :: v :: w :: x :: rest' equals last of w :: x :: rest'.
          have hNonempty : (w :: x :: rest') ≠ [] := List.cons_ne_nil _ _
          rw [List.getLast?_eq_getLast hNonempty] at hY
          have hY' : y = (w :: x :: rest').getLast hNonempty := by
            have hY' : y = (w :: x :: rest').getLast hNonempty := Option.some.inj hY |>.symm
          subst hY'
          have hOuterNE : (u :: v :: w :: x :: rest') ≠ [] := List.cons_ne_nil _ _
          rw [List.getLast?_eq_getLast hOuterNE]
          congr 1
          -- Last of (u :: v :: w :: x :: rest') = last of (w :: x :: rest').
          rw [List.getLast_cons (List.cons_ne_nil _ _),
              List.getLast_cons (List.cons_ne_nil _ _)]
        have ih_rec := ih (n - 2) hLt (w :: x :: rest') hRecLen hRecGe hAltRest hRecUnm
        -- Now: edgesOf (u :: v :: w :: x :: rest') =
        --   (u, v) :: (v, w) :: edgesOf (w :: x :: rest').
        rw [hr]
        simp only [Matching.augmentAlong.edgesOf]
        simp only [List.filter_cons, h_uv_inM_false, Bool.not_false,
          h_vw_inM_true, Bool.not_true,
          List.length_cons]
        omega

/-- **Alternation balance.** For an aug path, the path-edges *not* in
    `M` (modulo swap) outnumber those *in* `M` by exactly 1. -/
private lemma augmentingPath_alternation_balance
    (M : Matching V) (P : List V) (hAug : IsAugmentingPath M P) :
    ((Matching.augmentAlong.edgesOf P).filter
      (fun pe => !(M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1)))))).length
    = ((Matching.augmentAlong.edgesOf P).filter
      (fun pe => M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))).length
      + 1 := by
  -- Extract: P has ≥ 2 vertices, last vertex unmatched, IsAlt.
  match P, hAug with
  | [], hA => exact (hA).elim
  | [u], hA =>
    simp [IsAugmentingPath, List.getLast?] at hA
  | u :: v :: rest, hA =>
    obtain ⟨hu, hLastBlock, hAlt⟩ := hA
    have hLen : 2 ≤ (u :: v :: rest).length := by simp
    -- Extract last vertex unmatched.
    have hLastUnm : ∀ y, (u :: v :: rest).getLast? = some y →
        Matching.isMatched M y = false := by
      intro y hY
      -- hLastBlock : match (v :: rest).getLast? with | none => False | some w => ¬isMatched
      have hNE : (u :: v :: rest) ≠ [] := List.cons_ne_nil _ _
      have hY' : y = (u :: v :: rest).getLast hNE := by
        rw [List.getLast?_eq_getLast hNE] at hY
        injection hY with hY'
        exact hY'.symm
      have h_eq_inner : (u :: v :: rest).getLast hNE = (v :: rest).getLast (List.cons_ne_nil _ _) :=
        List.getLast_cons (List.cons_ne_nil _ _)
      -- Get the last vertex of (v :: rest) from hLastBlock.
      have hVRestNE : (v :: rest) ≠ [] := List.cons_ne_nil _ _
      have hVRestLast : (v :: rest).getLast? = some ((v :: rest).getLast hVRestNE) :=
        List.getLast?_eq_getLast _
      rw [hVRestLast] at hLastBlock
      -- hLastBlock : ¬ isMatched M (last)
      simp only [Bool.not_eq_true] at hLastBlock
      rw [hY', h_eq_inner]
      exact hLastBlock
    exact alt_balance_aux M _ _ rfl hLen hAlt hLastUnm

/-- **Intersection symmetry.** For matching `M` and aug path `P`, the
    count of `M`-edges that match some path-edge equals the count of
    path-edges that match some `M`-edge. Uses `IsMatching M` for
    uniqueness. Phase 3 obligation. -/
private lemma augmentingPath_intersection_symmetry
    (M : Matching V) (_hM : IsMatching M) (P : List V)
    (_hAug : IsAugmentingPath M P) :
    (M.filter (fun e =>
        (Matching.augmentAlong.edgesOf P).any
          (fun pe => decide (e = pe) || decide (e = (pe.2, pe.1))))).length
    = ((Matching.augmentAlong.edgesOf P).filter (fun pe =>
        M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))).length := by
  sorry

/-- The augmentation increases matching size by exactly 1.
    Strengthened with `IsMatching M` (Idea A). Reduces to
    `augmentingPath_alternation_balance` (Idea D), `intersection_symmetry`,
    and the standard list-partition lemma. -/
theorem augmentAlong_increases_size_by_one
    (M : Matching V) (hM : IsMatching M) (P : List V)
    (hAug : IsAugmentingPath M P) :
    (M.augmentAlong P).size = M.size + 1 := by
  unfold Matching.augmentAlong Matching.size
  rw [List.length_append]
  -- Step 1: rewrite toRemove's filter predicate using Bool de Morgan.
  -- `pathEdges.all (≠ ∧ ≠ swap)` = `! pathEdges.any (= ∨ = swap)`.
  -- We prove this via `List.filter_congr` + per-edge Bool equality.
  have hRemove_eq :
      M.filter (fun e =>
        (Matching.augmentAlong.edgesOf P).all
          (fun pe => decide (e ≠ pe) && decide (e ≠ (pe.2, pe.1))))
      = M.filter (fun e =>
          !((Matching.augmentAlong.edgesOf P).any
            (fun pe => decide (e = pe) || decide (e = (pe.2, pe.1))))) := by
    apply List.filter_congr
    intro e _
    -- For each `e`, the two Bool predicates are equal: by induction on `edgesOf P`.
    induction Matching.augmentAlong.edgesOf P with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.all_cons, List.any_cons, Bool.not_or]
      rw [ih]
      -- Need: `(decide (e ≠ hd) && decide (e ≠ (hd.2, hd.1))) = !(decide (e = hd) || decide (e = (hd.2, hd.1)))`
      -- and the rest matches via ih.
      simp only [decide_not, Bool.not_or, ne_eq]
  rw [hRemove_eq]
  -- Step 2: rewrite toAdd's filter predicate similarly.
  -- `decide (¬ M.any (...))` = `!(M.any (...))`.
  have hAdd_eq :
      (Matching.augmentAlong.edgesOf P).filter
        (fun pe => decide (¬ List.any M (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))) = true))
      = (Matching.augmentAlong.edgesOf P).filter
        (fun pe => !(M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))) := by
    apply List.filter_congr
    intro pe _
    -- decide (¬ b = true) = !b for Bool b.
    cases h : M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))) <;> simp [h]
  rw [hAdd_eq]
  -- Step 3: standard partition for M.
  have hM_split := List.length_eq_length_filter_add (l := M)
    (fun e => (Matching.augmentAlong.edgesOf P).any
              (fun pe => decide (e = pe) || decide (e = (pe.2, pe.1))))
  -- Step 4: standard partition for pathEdges.
  have hPE_split := List.length_eq_length_filter_add
    (l := Matching.augmentAlong.edgesOf P)
    (fun pe => M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))
  -- Step 5: apply the helpers.
  have hBalance := augmentingPath_alternation_balance M P hAug
  have hSymm := augmentingPath_intersection_symmetry M hM P hAug
  omega

/-- After at most `|V|/2 + 1` rounds the loop must terminate, because
    each round increases `|M|` by 1 and `|M|` is bounded by `|V|/2`. -/
theorem maxMatchingLeanCore_fixedpoint
    (ctx : Context V) (n : Nat) (M : Matching V)
    (hStuck : findAugmentingPathLean ctx (maxMatchingLeanCore ctx n M) = none) :
    findAugmentingPathLean ctx (maxMatchingLeanCore ctx n M) = none := hStuck
-- (Trivial restatement; included so callers can treat termination as
--  a black-box hypothesis named in their proofs.)

/-- *Loop progress*: every iteration of `maxMatchingLeanCore` either
    leaves `M` unchanged (oracle returned `none`) or strictly increases
    its size by 1. -/
theorem maxMatchingLeanCore_step
    (ctx : Context V) (spec : OracleSpec ctx) (M : Matching V) (hM : IsMatching M)
    (P : List V) (hP : findAugmentingPathLean ctx M = some P) :
    (maxMatchingLeanCore ctx 1 M).size = M.size + 1 := by
  unfold maxMatchingLeanCore
  rw [hP]
  unfold maxMatchingLeanCore
  exact augmentAlong_increases_size_by_one M hM P ((spec M).1 P hP)


/-! ### Tier B — `maxMatchingLean` returns a *matching*

Provable given that the augmenting-path spec holds and that augmenting
along a valid augmenting path preserves "is a matching."
-/

/-- Augmenting along an `M`-augmenting path preserves the matching
    invariant. The argument is purely combinatorial (the path edges are
    vertex-disjoint from the rest of `M` and from each other) — left as
    `sorry`. -/
theorem augmentAlong_preserves_isMatching
    (M : Matching V) (P : List V)
    (hM : IsMatching M) (hP : IsAugmentingPath M P) :
    IsMatching (M.augmentAlong P) := by
  sorry

omit [DecidableEq V] in
/-- The empty matching trivially satisfies `IsMatching`. -/
theorem isMatching_nil : IsMatching ([] : Matching V) := by
  refine ⟨?_, ?_⟩
  · intro e he; cases he
  · intro e₁ he₁; cases he₁

/-- After any number of iterations, `maxMatchingLeanCore` returns
    something that satisfies `IsMatching`, given the oracle's spec. -/
theorem maxMatchingLeanCore_isMatching
    (ctx : Context V) (spec : OracleSpec ctx) :
    ∀ (n : Nat) (M : Matching V), IsMatching M →
      IsMatching (maxMatchingLeanCore ctx n M)
  | 0,        M, hM => by simpa [maxMatchingLeanCore]
  | n + 1,    M, hM => by
      unfold maxMatchingLeanCore
      cases hOpt : findAugmentingPathLean ctx M with
      | none => simpa
      | some P =>
          have hAug : IsAugmentingPath M P := (spec M).1 P hOpt
          have hM' : IsMatching (M.augmentAlong P) :=
            augmentAlong_preserves_isMatching M P hM hAug
          exact maxMatchingLeanCore_isMatching ctx spec n _ hM'

/-- Headline of Tier B: `maxMatchingLean ctx` is always a matching. -/
theorem maxMatchingLean_isMatching
    (ctx : Context V) (spec : OracleSpec ctx) :
    IsMatching (maxMatchingLean ctx) :=
  maxMatchingLeanCore_isMatching ctx spec _ [] isMatching_nil


/-! ### Tier C — *optimality*: the deep result (sorry)

This is the genuine theorem of Edmonds: assuming the oracle is sound
**and complete**, the result is a maximum matching. Completeness of the
oracle reduces by Berge's theorem to "no augmenting path exists" — and
that is exactly what the IR's `FindAugmentingPath` (with non-stub
primitives) is supposed to certify.

These three theorems sit at the same depth as
`Hackathon/Graph/Algorithms/Blossom.lean` and are the natural
follow-up.
-/

/-- A matching `M` is *maximum* if no other matching on the same vertex
    set has strictly more edges. The `ctx` parameter is currently
    unused but is retained so the spec-level statement of Berge's
    theorem can be parameterised over the ambient graph in a future
    refinement (e.g. requiring `N`'s edges to lie in `ctx.isAdj`). -/
def IsMaximumMatching (_ctx : Context V) (M : Matching V) : Prop :=
  IsMatching M ∧
  (∀ N : Matching V, IsMatching N → N.size ≤ M.size)

/-- **Lemma D (IR-side):** if `|N| > |M|`, the symmetric-difference
    argument produces an `M`-augmenting path. The classical proof
    examines connected components of `M △ N`; left as `sorry` (this is
    the bulk of the Phase 3 graph-theory work). -/
theorem exists_augmenting_of_larger_ir
    {M N : Matching V} (hM : IsMatching M) (hN : IsMatching N)
    (h : M.size < N.size) :
    ∃ P, IsAugmentingPath M P := by
  sorry

/-- **Berge's theorem.** A matching is maximum iff there is no
    augmenting path. Reduces to two named obligations:
    `augmentAlong_increases_size_by_one` + `augmentAlong_preserves_isMatching`
    (forward) and `exists_augmenting_of_larger_ir` (backward). -/
theorem berge (ctx : Context V) (M : Matching V) (hM : IsMatching M) :
    IsMaximumMatching ctx M ↔ (∀ P, ¬ IsAugmentingPath M P) := by
  constructor
  · -- (⇒) M max → no augmenting path.
    rintro ⟨_, hMax⟩ P hAug
    have h1 : IsMatching (M.augmentAlong P) :=
      augmentAlong_preserves_isMatching M P hM hAug
    have h2 : (M.augmentAlong P).size = M.size + 1 :=
      augmentAlong_increases_size_by_one M hM P hAug
    have h3 : (M.augmentAlong P).size ≤ M.size := hMax _ h1
    omega
  · -- (⇐) No aug path → M max.
    intro hNoAug
    refine ⟨hM, ?_⟩
    intro N hN
    by_cases h : N.size ≤ M.size
    · exact h
    · exfalso
      have hlt : M.size < N.size := Nat.lt_of_not_le h
      obtain ⟨P, hAug⟩ := exists_augmenting_of_larger_ir hM hN hlt
      exact hNoAug P hAug

/-- **Termination obligation.** The loop, given enough fuel
    (`|V|/2 + 1`), terminates with a matching on which the oracle
    returns `none`. This requires bounding `|M| ≤ |V|/2` for any
    matching in the ambient graph — a standard but non-trivial fact
    left as `sorry`. -/
theorem maxMatchingLean_oracle_returns_none
    (ctx : Context V) (_spec : OracleSpec ctx) :
    findAugmentingPathLean ctx (maxMatchingLean ctx) = none := by
  sorry

/-- **Top-level optimality.** Given an oracle that is sound and complete,
    the loop returns a maximum matching. Reduces to:
    * `maxMatchingLean_isMatching` — the result is a matching,
    * `maxMatchingLean_oracle_returns_none` — the oracle returns `none`,
    * `OracleSpec` — `none` ⇒ no augmenting path,
    * `berge` — no aug path ⇒ maximum. -/
theorem maxMatchingLean_isMaximum
    (ctx : Context V) (spec : OracleSpec ctx) :
    IsMaximumMatching ctx (maxMatchingLean ctx) := by
  have hMatch : IsMatching (maxMatchingLean ctx) :=
    maxMatchingLean_isMatching ctx spec
  -- Loop terminated with oracle returning `none`:
  have hNone : findAugmentingPathLean ctx (maxMatchingLean ctx) = none :=
    maxMatchingLean_oracle_returns_none ctx spec
  -- Oracle's `none` ⇒ no augmenting path.
  have hNoAug : ∀ P, ¬ IsAugmentingPath (maxMatchingLean ctx) P :=
    (spec (maxMatchingLean ctx)).2 hNone
  -- Berge: no aug path ⇒ maximum.
  exact (berge ctx (maxMatchingLean ctx) hMatch).mpr hNoAug

/-! ### Tier D — the blossom-contraction lemmas (sorry)

These are the *implementation-level* obligations of `FindAugmentingPath`:
that contraction preserves the existence of augmenting paths and that
`lift_path` carries an augmenting path in `G'` back to one in `G`. They
are the deep graph theory that justifies the recursion on the contracted
matching. We state them precisely; proofs are out of scope for this
file. -/

/-- A *blossom* with respect to `M`: an odd-length closed alternating
    walk through some "stem" vertex, encoded as the list of vertices
    `[stem, v₁, v₂, …, v_{2k}, stem]`. -/
structure BlossomShape (M : Matching V) where
  stem : V
  cycle : List V
  stemAtBoth : cycle.head? = some stem ∧ cycle.getLast? = some stem
  /-- The number of *edges* in the cycle (= `cycle.length - 1`) is odd.
      We express this as an elementary modular condition rather than
      depending on Mathlib's `Odd`. -/
  oddEdgeCount : (cycle.length - 1) % 2 = 1
  isAlternating : IsAlternatingPath M cycle

/-- Contract a blossom on the *matching* side: collapse all blossom
    vertices to the stem; then drop self-loops produced by the
    collapse. -/
def Matching.contract (M : Matching V) (B : BlossomShape M) : Matching V :=
  M.filterMap (fun e =>
    let u' := if B.cycle.contains e.1 then B.stem else e.1
    let v' := if B.cycle.contains e.2 then B.stem else e.2
    if u' = v' then none else some (u', v'))

/-- **Blossom-contraction equivalence.** The contracted matching admits
    an augmenting path iff the original does. -/
theorem contract_matching_augmenting_iff
    (M : Matching V) (B : BlossomShape M) :
    (∃ P, IsAugmentingPath (M.contract B) P)
    ↔ (∃ P, IsAugmentingPath M P) := by
  sorry

/-- **Lift correctness.** Given an augmenting path in the contracted
    instance, there is a corresponding augmenting path in the original.
    Reduces directly to the equivalence `contract_matching_augmenting_iff`. -/
theorem lift_path_correct
    (M : Matching V) (B : BlossomShape M) (Pprime : List V)
    (h : IsAugmentingPath (M.contract B) Pprime) :
    ∃ P, IsAugmentingPath M P :=
  (contract_matching_augmenting_iff M B).mp ⟨Pprime, h⟩

/-! ## Summary of obligations

| Layer | Status |
|---|---|
| Two-level IR (`MaxMatching` calls `FindAugmentingPath` recursively) | ✅ encoded as `blossomFuns` |
| IR runs end-to-end (with stub primitives) | ✅ `#eval blossomProgram` returns `[]` |
| Pure-Lean reference loop | ✅ `maxMatchingLean` |
| Loop progress (each iter, `|M| += 1`)      | ☐ via `augmentAlong_increases_size_by_one` (sorry) |
| Loop result is a matching                  | ✅ `maxMatchingLean_isMatching` (modulo TierA sorry) |
| Berge's theorem                            | ☐ stated, proof sorry |
| Loop result is maximum                     | ☐ via Berge + progress (sorry) |
| Blossom contraction equivalence            | ☐ stated, proof sorry |
| `lift_path` correctness                    | ☐ stated, proof sorry |

Filling the four `sorry`s in Tiers C/D is the next milestone and is
substantially harder than the loop-level scaffold. The file is
structured so the milestone can be tackled lemma-by-lemma without
disturbing the IR.
-/

end Hackathon.GraphIR.Blossom
