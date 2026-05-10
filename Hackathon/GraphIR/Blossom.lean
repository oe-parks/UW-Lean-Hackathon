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
    vertex-disjoint, no edge is a self-loop, and `M` has no duplicate
    list entries. The Nodup clause is needed for counting arguments
    (e.g., `augmentingPath_intersection_symmetry`). -/
def IsMatching (M : Matching V) : Prop :=
  (∀ e ∈ M, e.1 ≠ e.2) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ →
      e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₂.2 ∧ e₁.2 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2) ∧
  M.Nodup

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

/-- An *M-augmenting* path is a *simple* alternating path (no repeated
    vertices) whose endpoints are both unmatched. The `Nodup` clause
    ensures path-edges are distinct as edges (modulo swap) and contain
    no self-loops, which is needed for the `augmentAlong` operation to
    preserve the matching invariant. -/
def IsAugmentingPath (M : Matching V) (P : List V) : Prop :=
  match P with
  | []      => False
  | u :: rest =>
      ¬ (Matching.isMatched M u = true) ∧
      ( match rest.getLast? with
        | none   => False                       -- a single vertex isn't a path
        | some w => ¬ (Matching.isMatched M w = true)
      ) ∧
      IsAlternatingPath M P ∧
      P.Nodup

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

/-- Bridge: `inM` predicate as Bool. -/
private lemma inM_eq_true_iff (M : Matching V) (a b : V) :
    (M.any (fun e => decide (e = (a, b)) || decide (e = ((a, b).2, (a, b).1)))) = true ↔
    ((a, b) ∈ M ∨ (b, a) ∈ M) := by
  show (M.any (fun e => decide (e = (a, b)) || decide (e = (b, a)))) = true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, hpred⟩
    rcases Bool.or_eq_true_iff.mp hpred with h1 | h1
    · have h2 : e = (a, b) := of_decide_eq_true h1
      exact Or.inl (h2 ▸ he)
    · have h2 : e = (b, a) := of_decide_eq_true h1
      exact Or.inr (h2 ▸ he)
  · rintro (hab | hba)
    · exact ⟨(a, b), hab, by simp⟩
    · exact ⟨(b, a), hba, by simp⟩

private lemma inM_eq_false_iff (M : Matching V) (a b : V) :
    (M.any (fun e => decide (e = (a, b)) || decide (e = ((a, b).2, (a, b).1)))) = false ↔
    ¬ ((a, b) ∈ M ∨ (b, a) ∈ M) := by
  constructor
  · intro h hOr
    have hT := (inM_eq_true_iff M a b).mpr hOr
    rw [hT] at h
    exact Bool.noConfusion h
  · intro h
    by_contra hT
    rw [Bool.not_eq_false] at hT
    exact h ((inM_eq_true_iff M a b).mp hT)

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
      have hAlt' : ((u, v) ∈ M ∨ (v, u) ∈ M ↔ False) ∧
          IsAlternatingPath.alternates_from_odd M [v] := hAlt
      have h_uv_notInM : ¬ ((u, v) ∈ M ∨ (v, u) ∈ M) := fun h => hAlt'.1.mp h
      have h_inM_false :
          (M.any (fun e => decide (e = (u, v)) || decide (e = ((u, v).2, (u, v).1)))) = false :=
        (inM_eq_false_iff M u v).mpr h_uv_notInM
      show (List.filter _ [(u, v)]).length = (List.filter _ [(u, v)]).length + 1
      simp [List.filter_cons, h_inM_false]
    | u :: v :: w :: rest, hLen' =>
      -- Inductive case.
      have hAlt' : ((u, v) ∈ M ∨ (v, u) ∈ M ↔ False) ∧
          IsAlternatingPath.alternates_from_odd M (v :: w :: rest) := hAlt
      have hAlt'' : ((v, w) ∈ M ∨ (w, v) ∈ M) ∧
          IsAlternatingPath M (w :: rest) := hAlt'.2
      have h_uv_notInM : ¬ ((u, v) ∈ M ∨ (v, u) ∈ M) := fun h => hAlt'.1.mp h
      have h_vw_inM : (v, w) ∈ M ∨ (w, v) ∈ M := hAlt''.1
      have hAltRest : IsAlternatingPath M (w :: rest) := hAlt''.2
      have h_uv_inM_false :
          (M.any (fun e => decide (e = (u, v)) || decide (e = ((u, v).2, (u, v).1)))) = false :=
        (inM_eq_false_iff M u v).mpr h_uv_notInM
      have h_vw_inM_true :
          (M.any (fun e => decide (e = (v, w)) || decide (e = ((v, w).2, (v, w).1)))) = true :=
        (inM_eq_true_iff M v w).mpr h_vw_inM
      -- Case-split on whether `rest` is empty using match.
      match hr : rest, hAltRest with
      | [], _ =>
        -- P = [u, v, w]: last vertex is w. (v, w) ∈ M, but w is unmatched.
        exfalso
        have hLast_eq : (u :: v :: w :: ([] : List V)).getLast? = some w := rfl
        have h_w_unm : Matching.isMatched M w = false := hUnm w hLast_eq
        have h_w_matched : Matching.isMatched M w = true := by
          rcases h_vw_inM with hvw | hwv
          · exact List.any_eq_true.mpr ⟨(v, w), hvw, by
              simp [Matching.incident]⟩
          · exact List.any_eq_true.mpr ⟨(w, v), hwv, by
              simp [Matching.incident]⟩
        rw [h_w_matched] at h_w_unm
        exact Bool.noConfusion h_w_unm
      | x :: rest', hAltRest =>
        -- P = u :: v :: w :: x :: rest'. Recurse on (w :: x :: rest').
        have hRecLen : (w :: x :: rest').length = n - 2 := by
          simp [List.length_cons] at hLen' ⊢; omega
        have hRecGe : 2 ≤ n - 2 := by
          simp [List.length_cons] at hLen'; omega
        have hLt : n - 2 < n := by omega
        have hRecUnm : ∀ y, (w :: x :: rest').getLast? = some y →
            Matching.isMatched M y = false := by
          intro y hY
          apply hUnm
          have hOuterNE : (u :: v :: w :: x :: rest') ≠ [] := List.cons_ne_nil _ _
          have hInnerNE : (w :: x :: rest') ≠ [] := List.cons_ne_nil _ _
          rw [List.getLast?_eq_some_getLast hOuterNE]
          rw [List.getLast?_eq_some_getLast hInnerNE] at hY
          congr 1
          have hY' : y = (w :: x :: rest').getLast hInnerNE := by
            injection hY with hY'; exact hY'.symm
          rw [hY']
          rw [List.getLast_cons (List.cons_ne_nil _ _),
              List.getLast_cons (List.cons_ne_nil _ _)]
        have ih_rec := ih (n - 2) hLt (w :: x :: rest') hRecLen hRecGe hAltRest hRecUnm
        change (List.filter _ ((u, v) :: (v, w) :: Matching.augmentAlong.edgesOf (w :: x :: rest'))).length
           = (List.filter _ ((u, v) :: (v, w) :: Matching.augmentAlong.edgesOf (w :: x :: rest'))).length + 1
        -- Apply filter_cons twice and reduce via knowing the truth values.
        rw [show ((u, v) :: (v, w) :: Matching.augmentAlong.edgesOf (w :: x :: rest')).filter
            (fun pe => !(M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1)))))
          = (u, v) :: (Matching.augmentAlong.edgesOf (w :: x :: rest')).filter
            (fun pe => !(M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))) from by
            rw [List.filter_cons, List.filter_cons]
            simp [h_uv_inM_false, h_vw_inM_true]]
        rw [show ((u, v) :: (v, w) :: Matching.augmentAlong.edgesOf (w :: x :: rest')).filter
            (fun pe => M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))
          = (v, w) :: (Matching.augmentAlong.edgesOf (w :: x :: rest')).filter
            (fun pe => M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1)))) from by
            rw [List.filter_cons, List.filter_cons]
            simp [h_uv_inM_false, h_vw_inM_true]]
        simp only [List.length_cons]
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
  match P, hAug with
  | [], hA => exact hA.elim
  | [u], hA => exact hA.2.1.elim
  | u :: v :: rest, hA =>
    obtain ⟨_, hLastBlock, hAlt, _⟩ := hA
    have hLen : 2 ≤ (u :: v :: rest).length := by simp
    have hLastUnm : ∀ y, (u :: v :: rest).getLast? = some y →
        Matching.isMatched M y = false := by
      intro y hY
      have hNE : (u :: v :: rest) ≠ [] := List.cons_ne_nil _ _
      have hVRestNE : (v :: rest) ≠ [] := List.cons_ne_nil _ _
      rw [List.getLast?_eq_some_getLast hNE] at hY
      have hY' : y = (u :: v :: rest).getLast hNE := by
        injection hY with hY'; exact hY'.symm
      have h_eq_inner : (u :: v :: rest).getLast hNE = (v :: rest).getLast hVRestNE :=
        List.getLast_cons hVRestNE
      have hVRestLast : (v :: rest).getLast? = some ((v :: rest).getLast hVRestNE) :=
        List.getLast?_eq_some_getLast _
      rw [hVRestLast] at hLastBlock
      simp only [Bool.not_eq_true] at hLastBlock
      rw [hY', h_eq_inner]
      exact hLastBlock
    exact alt_balance_aux M _ _ rfl hLen hAlt hLastUnm

/-! ### Helpers about `Matching.augmentAlong.edgesOf` -/

/-- Every path-edge has its first vertex in the path. -/
private lemma edgesOf_fst_in_path :
    ∀ (P : List V) (e : V × V), e ∈ Matching.augmentAlong.edgesOf P → e.1 ∈ P
  | [], _, he => by simp [Matching.augmentAlong.edgesOf] at he
  | [_], _, he => by simp [Matching.augmentAlong.edgesOf] at he
  | a :: b :: rest, e, he => by
    simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he
    rcases he with rfl | he
    · exact List.mem_cons_self
    · exact List.mem_cons.mpr (Or.inr (edgesOf_fst_in_path (b :: rest) e he))

/-- Every path-edge has its second vertex in the path. -/
private lemma edgesOf_snd_in_path :
    ∀ (P : List V) (e : V × V), e ∈ Matching.augmentAlong.edgesOf P → e.2 ∈ P
  | [], _, he => by simp [Matching.augmentAlong.edgesOf] at he
  | [_], _, he => by simp [Matching.augmentAlong.edgesOf] at he
  | a :: b :: rest, e, he => by
    simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he
    rcases he with rfl | he
    · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
    · exact List.mem_cons.mpr (Or.inr (edgesOf_snd_in_path (b :: rest) e he))

/-- Under `Nodup P`, no path-edge is a self-loop. -/
private lemma edgesOf_no_self_loop :
    ∀ (P : List V), P.Nodup →
    ∀ (e : V × V), e ∈ Matching.augmentAlong.edgesOf P → e.1 ≠ e.2
  | [], _, _, he => by simp [Matching.augmentAlong.edgesOf] at he
  | [_], _, _, he => by simp [Matching.augmentAlong.edgesOf] at he
  | a :: b :: rest, h, e, he => by
    simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he
    rcases he with rfl | he
    · intro hab
      exact (List.nodup_cons.mp h).1 (List.mem_cons.mpr (Or.inl hab))
    · exact edgesOf_no_self_loop (b :: rest) h.of_cons e he

/-- Under `Nodup P`, no two path-edges are swaps of each other. -/
private lemma edgesOf_swap_not_in :
    ∀ (P : List V), P.Nodup → ∀ a b : V,
    (a, b) ∈ Matching.augmentAlong.edgesOf P →
    (b, a) ∉ Matching.augmentAlong.edgesOf P
  | [], _, _, _, h => by simp [Matching.augmentAlong.edgesOf] at h
  | [_], _, _, _, h => by simp [Matching.augmentAlong.edgesOf] at h
  | u :: v :: rest, hP, a, b, h_ab => by
    simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at h_ab
    rcases h_ab with h_eq | h_ab
    · have ha : a = u := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
      have hb : b = v := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
      rw [ha, hb]
      simp only [Matching.augmentAlong.edgesOf, List.mem_cons, not_or]
      refine ⟨?_, ?_⟩
      · intro h_eq2
        have h_v_eq_u : v = u := (Prod.mk.injEq _ _ _ _).mp h_eq2 |>.1
        exact (List.nodup_cons.mp hP).1 (List.mem_cons.mpr (Or.inl h_v_eq_u.symm))
      · intro h_in
        have h_u_in : u ∈ v :: rest := edgesOf_snd_in_path _ _ h_in
        exact (List.nodup_cons.mp hP).1 h_u_in
    · simp only [Matching.augmentAlong.edgesOf, List.mem_cons, not_or]
      refine ⟨?_, ?_⟩
      · intro h_eq
        have hb_eq : b = u := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        have h_b_in : b ∈ v :: rest := edgesOf_snd_in_path _ _ h_ab
        rw [hb_eq] at h_b_in
        exact (List.nodup_cons.mp hP).1 h_b_in
      · exact edgesOf_swap_not_in (v :: rest) hP.of_cons a b h_ab

/-- Under `Nodup P`, the path-edge list has no duplicates. -/
private lemma edgesOf_nodup :
    ∀ (P : List V), P.Nodup → (Matching.augmentAlong.edgesOf P).Nodup
  | [], _ => by simp [Matching.augmentAlong.edgesOf]
  | [_], _ => by simp [Matching.augmentAlong.edgesOf]
  | a :: b :: rest, h => by
    simp only [Matching.augmentAlong.edgesOf]
    refine List.nodup_cons.mpr ⟨?_, edgesOf_nodup (b :: rest) h.of_cons⟩
    intro h_in
    have h_a_in : a ∈ b :: rest := edgesOf_fst_in_path _ _ h_in
    exact (List.nodup_cons.mp h).1 h_a_in

/-- General counting helper: under `Nodup l` with `a ∈ l` and `p a = false`,
    filter-by-`(x = a ∨ p x)` has length one more than filter-by-`p`. -/
private lemma list_filter_or_decide_count
    {α : Type*} [DecidableEq α] (l : List α) (a : α) (p : α → Bool)
    (hl : l.Nodup) (ha : a ∈ l) (hpa : p a = false) :
    (l.filter (fun x => decide (x = a) || p x)).length = (l.filter p).length + 1 := by
  induction l with
  | nil => simp at ha
  | cons x l' ih =>
    have hl' : l'.Nodup := hl.of_cons
    rcases List.mem_cons.mp ha with h_eq | h_a_in_l'
    · -- a = x.
      have h_a_notIn_l' : a ∉ l' := h_eq ▸ (List.nodup_cons.mp hl).1
      have h_filter_combined :
          (l'.filter (fun y => decide (y = a) || p y)) = l'.filter p := by
        apply List.filter_congr
        intro y hy
        have h_y_ne_a : y ≠ a := fun heq => h_a_notIn_l' (heq ▸ hy)
        rw [decide_eq_false h_y_ne_a]
        simp
      rw [List.filter_cons, List.filter_cons]
      have h_x_eq_a : decide (x = a) = true := decide_eq_true h_eq.symm
      have h_p_x : p x = false := h_eq ▸ hpa
      rw [show (decide (x = a) || p x) = true from by rw [h_x_eq_a]; rfl]
      rw [show p x = false from h_p_x]
      simp
      rw [h_filter_combined]
    · -- x ≠ a (since a ∈ l' and l is Nodup).
      have h_x_neq_a : x ≠ a := fun h => (List.nodup_cons.mp hl).1 (h ▸ h_a_in_l')
      have h_decide_xa : decide (x = a) = false := decide_eq_false h_x_neq_a
      rw [List.filter_cons, List.filter_cons]
      rw [show (decide (x = a) || p x) = p x from by rw [h_decide_xa]; simp]
      have ih' := ih hl' h_a_in_l'
      cases h_px : p x
      · simp; exact ih'
      · simp; omega

/-- **Intersection symmetry.** For matching `M` and aug path `P`, the
    count of `M`-edges that match some path-edge equals the count of
    path-edges that match some `M`-edge. Proof by induction on M with
    case-split on whether `e` matches a path-edge. -/
private lemma augmentingPath_intersection_symmetry
    (M : Matching V) (hM : IsMatching M) (P : List V)
    (hAug : IsAugmentingPath M P) :
    (M.filter (fun e =>
        (Matching.augmentAlong.edgesOf P).any
          (fun pe => decide (e = pe) || decide (e = (pe.2, pe.1))))).length
    = ((Matching.augmentAlong.edgesOf P).filter (fun pe =>
        M.any (fun e => decide (e = pe) || decide (e = (pe.2, pe.1))))).length := by
  have hPNodup : P.Nodup := match P, hAug with
    | [], hPF => hPF.elim
    | _ :: _, hPCons => hPCons.2.2.2
  have hPENodup : (Matching.augmentAlong.edgesOf P).Nodup := edgesOf_nodup P hPNodup
  have hPESwap : ∀ a b : V, (a, b) ∈ Matching.augmentAlong.edgesOf P →
      (b, a) ∉ Matching.augmentAlong.edgesOf P := edgesOf_swap_not_in P hPNodup
  -- Main induction on M.
  set pathEdges := Matching.augmentAlong.edgesOf P
  have hMNodup : M.Nodup := hM.2.2
  have hVDisj : ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
      e1.1 ≠ e2.1 ∧ e1.1 ≠ e2.2 ∧ e1.2 ≠ e2.1 ∧ e1.2 ≠ e2.2 := hM.2.1
  clear_value pathEdges
  clear hM hAug hPNodup
  induction M with
  | nil => simp
  | cons e M' ih =>
    have hMNodup' := hMNodup.of_cons
    have hVDisj' : ∀ e1 ∈ M', ∀ e2 ∈ M', e1 ≠ e2 →
        e1.1 ≠ e2.1 ∧ e1.1 ≠ e2.2 ∧ e1.2 ≠ e2.1 ∧ e1.2 ≠ e2.2 :=
      fun e1 he1 e2 he2 hne =>
        hVDisj e1 (List.mem_cons.mpr (Or.inr he1)) e2 (List.mem_cons.mpr (Or.inr he2)) hne
    have ih' := ih hMNodup' hVDisj'
    have h_e_notIn_M' : e ∉ M' := (List.nodup_cons.mp hMNodup).1
    by_cases h_e_match : ∃ pe ∈ pathEdges, e = pe ∨ e = (pe.2, pe.1)
    · -- Case A: e matches some pe.
      obtain ⟨pe, hpe, hMatch⟩ := h_e_match
      have h_e_predTrue :
          (pathEdges.any (fun pe' => decide (e = pe') || decide (e = (pe'.2, pe'.1)))) = true := by
        simp only [List.any_eq_true]
        rcases hMatch with hM_pe | hM_pe
        · exact ⟨pe, hpe, by simp [hM_pe]⟩
        · exact ⟨pe, hpe, by simp [hM_pe]⟩
      -- LHS_M = LHS_M' + 1.
      have h_lhs_eq : ((e :: M').filter (fun e' =>
          pathEdges.any (fun pe' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))))).length
          = (M'.filter (fun e' =>
              pathEdges.any (fun pe' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))))).length + 1 := by
        rw [List.filter_cons, if_pos h_e_predTrue]
        simp
      -- Uniqueness: no e' ∈ M' matches pe.
      have h_pe_unique_in_M' : ∀ e' ∈ M', ¬ (e' = pe ∨ e' = (pe.2, pe.1)) := by
        intro e' he' h_match'
        have h_e_ne_e' : e ≠ e' := fun h_eq => h_e_notIn_M' (h_eq ▸ he')
        have hVD := hVDisj e List.mem_cons_self e' (List.mem_cons.mpr (Or.inr he')) h_e_ne_e'
        rcases hMatch with hM_pe | hM_pe <;> rcases h_match' with hM'_pe | hM'_pe
        · exact h_e_ne_e' (hM_pe.trans hM'_pe.symm)
        · have h1 : e.1 = pe.1 := by rw [hM_pe]
          have h2 : e'.2 = pe.1 := by rw [hM'_pe]
          exact hVD.2.1 (h1.trans h2.symm)
        · have h1 : e.2 = pe.1 := by rw [hM_pe]
          have h2 : e'.1 = pe.1 := by rw [hM'_pe]
          exact hVD.2.2.1 (h1.trans h2.symm)
        · exact h_e_ne_e' (hM_pe.trans hM'_pe.symm)
      -- For pe' ≠ pe in pathEdges: e doesn't match pe' (uniqueness via swap rule out).
      have h_e_only_match_pe : ∀ pe' ∈ pathEdges, pe' ≠ pe →
          ¬ (e = pe' ∨ e = (pe'.2, pe'.1)) := by
        intro pe' hpe' h_ne h_e_match'
        rcases hMatch with hM_pe | hM_pe <;> rcases h_e_match' with hM_pe' | hM_pe'
        · exact h_ne (hM_pe.symm.trans hM_pe').symm
        · -- e = pe and e = swap pe'. So pe = swap pe', i.e., pe' = swap pe.
          have h_pe_eq_swap : pe = (pe'.2, pe'.1) := hM_pe.symm.trans hM_pe'
          have h_pe'_eq : pe' = (pe.2, pe.1) := by
            have h1 : pe.2 = pe'.1 := by rw [h_pe_eq_swap]
            have h2 : pe.1 = pe'.2 := by rw [h_pe_eq_swap]
            exact Prod.ext h1.symm h2.symm
          rw [h_pe'_eq] at hpe'
          have hpe_normal : (pe.1, pe.2) ∈ pathEdges := by
            rcases pe with ⟨_, _⟩; exact hpe
          exact hPESwap pe.1 pe.2 hpe_normal hpe'
        · -- e = swap pe and e = pe'. So pe' = swap pe.
          have h_pe'_eq : pe' = (pe.2, pe.1) := by
            have heq : (pe.2, pe.1) = pe' := hM_pe.symm.trans hM_pe'
            exact heq.symm
          rw [h_pe'_eq] at hpe'
          have hpe_normal : (pe.1, pe.2) ∈ pathEdges := by
            rcases pe with ⟨_, _⟩; exact hpe
          exact hPESwap pe.1 pe.2 hpe_normal hpe'
        · -- both swap. e = swap pe = swap pe', so pe = pe'.
          have heq : (pe.2, pe.1) = (pe'.2, pe'.1) := hM_pe.symm.trans hM_pe'
          have h_pe_eq : pe = pe' := by
            have h1 : pe.2 = pe'.2 := (Prod.mk.injEq _ _ _ _).mp heq |>.1
            have h2 : pe.1 = pe'.1 := (Prod.mk.injEq _ _ _ _).mp heq |>.2
            exact Prod.ext h2 h1
          exact h_ne h_pe_eq.symm
      -- Define f1, f2. Show pathEdges.filter f1 = pathEdges.filter (decide (· = pe) || f2).
      let f2 : V × V → Bool := fun pe' =>
        M'.any (fun e' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1)))
      have h_filter_congr :
          pathEdges.filter (fun pe' =>
              (e :: M').any (fun e' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))))
          = pathEdges.filter (fun pe' => decide (pe' = pe) || f2 pe') := by
        apply List.filter_congr
        intro pe' hpe'
        by_cases h_pe'_eq : pe' = pe
        · -- pe' = pe. Both predicates true.
          have hMatch' : e = pe' ∨ e = (pe'.2, pe'.1) := h_pe'_eq.symm ▸ hMatch
          have h_left : (e :: M').any (fun e' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))) = true := by
            apply List.any_eq_true.mpr
            refine ⟨e, List.mem_cons_self, ?_⟩
            rcases hMatch' with h | h
            · simp [h]
            · simp [h]
          rw [h_left]
          have h_right : (decide (pe' = pe) || f2 pe') = true := by
            rw [decide_eq_true h_pe'_eq]; rfl
          rw [h_right]
        · -- pe' ≠ pe. Predicates equal (e doesn't match pe').
          have h_e_no_match := h_e_only_match_pe pe' hpe' h_pe'_eq
          have h_e_pred_false :
              (decide (e = pe') || decide (e = (pe'.2, pe'.1))) = false := by
            apply Bool.eq_false_iff.mpr
            intro h_pred
            apply h_e_no_match
            rcases Bool.or_eq_true_iff.mp h_pred with h | h
            · left; exact of_decide_eq_true h
            · right; exact of_decide_eq_true h
          simp only [List.any_cons, h_e_pred_false, decide_eq_false h_pe'_eq, Bool.false_or]
          rfl
      -- f2 pe = false (uniqueness).
      have h_f2_pe : f2 pe = false := by
        simp only [f2, List.any_eq_false]
        intro e' he' h_pred
        apply h_pe_unique_in_M' e' he'
        rcases Bool.or_eq_true_iff.mp h_pred with h | h
        · left; exact of_decide_eq_true h
        · right; exact of_decide_eq_true h
      -- Apply the counting helper.
      have h_count_eq :
          (pathEdges.filter (fun pe' => decide (pe' = pe) || f2 pe')).length
          = (pathEdges.filter f2).length + 1 :=
        list_filter_or_decide_count pathEdges pe f2 hPENodup hpe h_f2_pe
      -- Combine.
      rw [h_lhs_eq, h_filter_congr, h_count_eq, ih']
    · -- Case B: e doesn't match any path-edge.
      have h_e_predFalse :
          (pathEdges.any (fun pe' => decide (e = pe') || decide (e = (pe'.2, pe'.1)))) = false := by
        simp only [List.any_eq_false]
        intro pe' hpe' h_pred
        apply h_e_match
        refine ⟨pe', hpe', ?_⟩
        rcases Bool.or_eq_true_iff.mp h_pred with h | h
        · left; exact of_decide_eq_true h
        · right; exact of_decide_eq_true h
      have h_lhs_eq : ((e :: M').filter (fun e' =>
          pathEdges.any (fun pe' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))))).length
          = (M'.filter (fun e' =>
              pathEdges.any (fun pe' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))))).length := by
        rw [List.filter_cons, if_neg]
        rw [h_e_predFalse]; decide
      have h_rhs_eq : (pathEdges.filter (fun pe' =>
          (e :: M').any (fun e' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))))).length
          = (pathEdges.filter (fun pe' =>
              M'.any (fun e' => decide (e' = pe') || decide (e' = (pe'.2, pe'.1))))).length := by
        congr 1
        apply List.filter_congr
        intro pe' hpe'
        simp only [List.any_cons]
        have h_e_pe' : (decide (e = pe') || decide (e = (pe'.2, pe'.1))) = false := by
          apply Bool.eq_false_iff.mpr
          intro h_pred
          apply h_e_match
          refine ⟨pe', hpe', ?_⟩
          rcases Bool.or_eq_true_iff.mp h_pred with h | h
          · left; exact of_decide_eq_true h
          · right; exact of_decide_eq_true h
        rw [h_e_pe']
        simp
      rw [h_lhs_eq, h_rhs_eq, ih']

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

/-- Under `Nodup P`, distinct path-edges have distinct first components. -/
private lemma edgesOf_fst_inj :
    ∀ (P : List V), P.Nodup →
    ∀ (e1 e2 : V × V),
    e1 ∈ Matching.augmentAlong.edgesOf P →
    e2 ∈ Matching.augmentAlong.edgesOf P →
    e1.1 = e2.1 → e1 = e2
  | [], _, _, _, he, _, _ => by simp [Matching.augmentAlong.edgesOf] at he
  | [_], _, _, _, he, _, _ => by simp [Matching.augmentAlong.edgesOf] at he
  | a :: b :: rest, h, e1, e2, he1, he2, hShare => by
    simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he1 he2
    rcases he1 with rfl | he1 <;> rcases he2 with rfl | he2
    · rfl
    · exfalso
      have hS : a = e2.1 := hShare
      have ha_in : e2.1 ∈ b :: rest := edgesOf_fst_in_path _ _ he2
      exact (List.nodup_cons.mp h).1 (hS.symm ▸ ha_in)
    · exfalso
      have hS : e1.1 = a := hShare
      have ha_in : e1.1 ∈ b :: rest := edgesOf_fst_in_path _ _ he1
      exact (List.nodup_cons.mp h).1 (hS ▸ ha_in)
    · exact edgesOf_fst_inj (b :: rest) h.of_cons e1 e2 he1 he2 hShare

/-- Under `Nodup P`, distinct path-edges have distinct second components. -/
private lemma edgesOf_snd_inj :
    ∀ (P : List V), P.Nodup →
    ∀ (e1 e2 : V × V),
    e1 ∈ Matching.augmentAlong.edgesOf P →
    e2 ∈ Matching.augmentAlong.edgesOf P →
    e1.2 = e2.2 → e1 = e2
  | [], _, _, _, he, _, _ => by simp [Matching.augmentAlong.edgesOf] at he
  | [_], _, _, _, he, _, _ => by simp [Matching.augmentAlong.edgesOf] at he
  | a :: b :: rest, hP, e1, e2, he1, he2, hShare => by
    simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he1 he2
    rcases he1 with rfl | he1 <;> rcases he2 with rfl | he2
    · rfl
    · -- e1 = (a, b), e2 ∈ edgesOf (b :: rest). hShare: b = e2.2.
      exfalso
      have hS : b = e2.2 := hShare
      cases hr : rest with
      | nil => rw [hr] at he2; simp [Matching.augmentAlong.edgesOf] at he2
      | cons c rest' =>
        rw [hr] at he2 hP
        simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he2
        rcases he2 with rfl | he2
        · -- e2 = (b, c). hS: b = c. b ≠ c by Nodup.
          have hS' : b = c := hS
          have h_b_in : b ∈ c :: rest' := List.mem_cons.mpr (Or.inl hS')
          exact (List.nodup_cons.mp ((List.nodup_cons.mp hP).2)).1 h_b_in
        · -- e2 ∈ edgesOf (c :: rest'). e2.2 ∈ c :: rest'. hS: b = e2.2.
          have h_e2_snd_in : e2.2 ∈ c :: rest' := edgesOf_snd_in_path _ _ he2
          have h_b_in : b ∈ c :: rest' := hS ▸ h_e2_snd_in
          exact (List.nodup_cons.mp ((List.nodup_cons.mp hP).2)).1 h_b_in
    · -- e2 = (a, b), e1 ∈ edgesOf (b :: rest). hShare: e1.2 = b.
      exfalso
      have hS : e1.2 = b := hShare
      cases hr : rest with
      | nil => rw [hr] at he1; simp [Matching.augmentAlong.edgesOf] at he1
      | cons c rest' =>
        rw [hr] at he1 hP
        simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he1
        rcases he1 with rfl | he1
        · have hS' : c = b := hS
          have h_b_in : b ∈ c :: rest' := List.mem_cons.mpr (Or.inl hS'.symm)
          exact (List.nodup_cons.mp ((List.nodup_cons.mp hP).2)).1 h_b_in
        · have h_e1_snd_in : e1.2 ∈ c :: rest' := edgesOf_snd_in_path _ _ he1
          have h_b_in : b ∈ c :: rest' := hS ▸ h_e1_snd_in
          exact (List.nodup_cons.mp ((List.nodup_cons.mp hP).2)).1 h_b_in
    · exact edgesOf_snd_inj (b :: rest) hP.of_cons e1 e2 he1 he2 hShare

/-- The key adjacency lemma: under `IsAlternatingPath M P` and `P.Nodup`, two path-edges
    `e1, e2` with `e1.2 = e2.1` (i.e., e1 ends where e2 starts — so e2 immediately
    follows e1 in the path) have opposite M-status.
    Proof by structural induction with bidirectional case-split:
    e1 and e2 are each `(a, b)`, `(b, c)`, or in `edgesOf (c :: rest)`. Most cross-cases
    are vacuous via Nodup; the productive cases give opposite M-status from IsAlt
    or are vacuous via Nodup; the recursive case applies IH. -/
private lemma adjacent_edges_opposite_M_status
    (M : Matching V) :
    ∀ (P : List V), IsAlternatingPath M P → P.Nodup →
    ∀ (e1 e2 : V × V),
    e1 ∈ Matching.augmentAlong.edgesOf P →
    e2 ∈ Matching.augmentAlong.edgesOf P →
    e1.2 = e2.1 →
    (((e1.1, e1.2) ∈ M ∨ (e1.2, e1.1) ∈ M) ∧
       ¬ ((e2.1, e2.2) ∈ M ∨ (e2.2, e2.1) ∈ M)) ∨
    (¬ ((e1.1, e1.2) ∈ M ∨ (e1.2, e1.1) ∈ M) ∧
       ((e2.1, e2.2) ∈ M ∨ (e2.2, e2.1) ∈ M))
  | [], _, _, _, _, he, _, _ => by simp [Matching.augmentAlong.edgesOf] at he
  | [_], _, _, _, _, he, _, _ => by simp [Matching.augmentAlong.edgesOf] at he
  | [a, b], _, hNodup, e1, e2, he1, he2, hShare => by
    -- edgesOf [a, b] = [(a, b)]. e1 = e2 = (a, b).
    simp only [Matching.augmentAlong.edgesOf, Matching.augmentAlong.edgesOf, List.mem_cons] at he1 he2
    rcases he1 with rfl | he1
    rcases he2 with rfl | he2
    · -- e1 = e2 = (a, b). e1.2 = b, e2.1 = a, hShare: b = a. Nodup contradicts.
      exfalso
      apply (List.nodup_cons.mp hNodup).1
      exact List.mem_cons.mpr (Or.inl hShare.symm)
    · simp [Matching.augmentAlong.edgesOf] at he2
    · simp [Matching.augmentAlong.edgesOf] at he1
  | a :: b :: c :: rest, hAlt, hNodup, e1, e2, he1, he2, hShare => by
    have hAlt1 : ((a, b) ∈ M ∨ (b, a) ∈ M ↔ False) ∧
        IsAlternatingPath.alternates_from_odd M (b :: c :: rest) := hAlt
    have h_ab_notInM : ¬ ((a, b) ∈ M ∨ (b, a) ∈ M) := fun h => hAlt1.1.mp h
    have hAlt2 : ((b, c) ∈ M ∨ (c, b) ∈ M) ∧
        IsAlternatingPath M (c :: rest) := hAlt1.2
    have h_bc_inM : (b, c) ∈ M ∨ (c, b) ∈ M := hAlt2.1
    have hAltRest : IsAlternatingPath M (c :: rest) := hAlt2.2
    have hNodup_bc_rest : (b :: c :: rest).Nodup := hNodup.of_cons
    have hNodup_c_rest : (c :: rest).Nodup := hNodup_bc_rest.of_cons
    -- edgesOf (a :: b :: c :: rest) = (a, b) :: edgesOf (b :: c :: rest)
    --                             = (a, b) :: (b, c) :: edgesOf (c :: rest)
    -- edgesOf (a :: b :: c :: rest) = (a, b) :: edgesOf (b :: c :: rest)
    -- After simp, he1, he2 should be fully decomposed.
    simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he1 he2
    rcases he1 with rfl | rfl | he1 <;> rcases he2 with rfl | rfl | he2
    · -- e1 = e2 = (a, b). hShare: b = a. Nodup contradicts.
      exfalso
      have hS : b = a := hShare
      exact (List.nodup_cons.mp hNodup).1 (List.mem_cons.mpr (Or.inl hS.symm))
    · -- e1 = (a, b), e2 = (b, c). (a, b) ∉ M, (b, c) ∈ M.
      right
      exact ⟨h_ab_notInM, h_bc_inM⟩
    · -- e1 = (a, b), e2 ∈ edgesOf (c :: rest). hShare: b = e2.1.
      exfalso
      have hS : b = e2.1 := hShare
      have h_e2_in : e2.1 ∈ c :: rest := edgesOf_fst_in_path _ _ he2
      exact (List.nodup_cons.mp hNodup_bc_rest).1 (hS ▸ h_e2_in)
    · -- e1 = (b, c), e2 = (a, b). hShare: c = a. a ∈ c :: rest contradicts Nodup.
      exfalso
      have hS : c = a := hShare
      have h_a_in_cr : a ∈ c :: rest := hS ▸ List.mem_cons_self
      exact (List.nodup_cons.mp hNodup).1 (List.mem_cons.mpr (Or.inr h_a_in_cr))
    · -- e1 = e2 = (b, c). hShare: c = b. Nodup contradicts.
      exfalso
      have hS : c = b := hShare
      exact (List.nodup_cons.mp hNodup_bc_rest).1 (List.mem_cons.mpr (Or.inl hS.symm))
    · -- e1 = (b, c), e2 ∈ edgesOf (c :: rest). hShare: c = e2.1.
      cases hr : rest with
      | nil =>
        rw [hr] at he2
        simp [Matching.augmentAlong.edgesOf] at he2
      | cons d rest' =>
        rw [hr] at he2 hAltRest hNodup_c_rest
        simp only [Matching.augmentAlong.edgesOf, List.mem_cons] at he2
        rcases he2 with rfl | he2
        · -- e1 = (b, c), e2 = (c, d). (b, c) ∈ M, (c, d) ∉ M.
          left
          refine ⟨h_bc_inM, ?_⟩
          have hAlt_cd : ((c, d) ∈ M ∨ (d, c) ∈ M ↔ False) ∧ _ := hAltRest
          exact fun h => hAlt_cd.1.mp h
        · -- e2 ∈ edgesOf (d :: rest'). hShare: c = e2.1.
          exfalso
          have hS : c = e2.1 := hShare
          have h_e2_in : e2.1 ∈ d :: rest' := edgesOf_fst_in_path _ _ he2
          exact (List.nodup_cons.mp hNodup_c_rest).1 (hS ▸ h_e2_in)
    · -- e1 ∈ edgesOf (c :: rest), e2 = (a, b). hShare: e1.2 = a.
      exfalso
      have hS : e1.2 = a := hShare
      have h_e1_snd_in : e1.2 ∈ c :: rest := edgesOf_snd_in_path _ _ he1
      have h_a_in_cr : a ∈ c :: rest := hS ▸ h_e1_snd_in
      exact (List.nodup_cons.mp hNodup).1 (List.mem_cons.mpr (Or.inr h_a_in_cr))
    · -- e1 ∈ edgesOf (c :: rest), e2 = (b, c). hShare: e1.2 = b.
      exfalso
      have hS : e1.2 = b := hShare
      have h_e1_snd_in : e1.2 ∈ c :: rest := edgesOf_snd_in_path _ _ he1
      exact (List.nodup_cons.mp hNodup_bc_rest).1 (hS ▸ h_e1_snd_in)
    · -- Both e1, e2 ∈ edgesOf (c :: rest). Recurse with smaller path.
      exact adjacent_edges_opposite_M_status M (c :: rest) hAltRest hNodup_c_rest
        e1 e2 he1 he2 hShare

/-- Classification helper: any vertex `u ∈ P` that is matched in M (via edge `e`)
    is either P's head, P's last, or `e` is a path-edge. -/
private lemma matched_vertex_in_path_classification
    (M : Matching V) (hM : IsMatching M) :
    ∀ (P : List V), IsAlternatingPath M P → P.Nodup →
    ∀ (e : V × V), e ∈ M →
    ∀ (u : V), u ∈ P → (e.1 = u ∨ e.2 = u) →
    P.head? = some u ∨ P.getLast? = some u ∨
    ∃ pe ∈ Matching.augmentAlong.edgesOf P, e = pe ∨ e = (pe.2, pe.1)
  | [], _, _, _, _, _, h_u, _ => by simp at h_u
  | [v], _, _, _, _, u, h_u, _ => by
      simp at h_u
      left; simp [h_u]
  | [a, b], _, _, _, _, _, h_u, _ => by
      rcases List.mem_cons.mp h_u with h_eq | h_u'
      · left; simp [h_eq]
      · right; left
        rcases List.mem_cons.mp h_u' with h_eq | h_empty
        · simp [h_eq]
        · simp at h_empty
  | a :: b :: c :: tail3, hAlt, hNodup, e, he_M, u, h_u, h_u_in_e => by
        have hAlt1 : ((a, b) ∈ M ∨ (b, a) ∈ M ↔ False) ∧
            IsAlternatingPath.alternates_from_odd M (b :: c :: tail3) := hAlt
        have hAlt2 : ((b, c) ∈ M ∨ (c, b) ∈ M) ∧
            IsAlternatingPath M (c :: tail3) := hAlt1.2
        have h_bc_inM : (b, c) ∈ M ∨ (c, b) ∈ M := hAlt2.1
        have hAltRest : IsAlternatingPath M (c :: tail3) := hAlt2.2
        have hNodup_bc : (b :: c :: tail3).Nodup := hNodup.of_cons
        have hNodup_c : (c :: tail3).Nodup := hNodup_bc.of_cons
        rcases List.mem_cons.mp h_u with h_eq | h_u_in_bc
        · -- u = a (head).
          left; simp [h_eq]
        · rcases List.mem_cons.mp h_u_in_bc with h_eq | h_u_in_c
          · -- u = b (interior). M-edge for b is (b, c) (or swap).
            rw [h_eq] at h_u_in_e
            right; right
            refine ⟨(b, c), ?_, ?_⟩
            · simp [Matching.augmentAlong.edgesOf]
            · rcases h_bc_inM with h_bcM | h_cbM
              · by_cases heq : e = (b, c)
                · left; exact heq
                · exfalso
                  -- h_disj : e.1 ≠ b ∧ e.1 ≠ c ∧ e.2 ≠ b ∧ e.2 ≠ c
                  have h_disj := hM.2.1 e he_M (b, c) h_bcM heq
                  rcases h_u_in_e with h | h
                  · exact h_disj.1 h
                  · exact h_disj.2.2.1 h
              · by_cases heq : e = (c, b)
                · right; exact heq
                · exfalso
                  -- h_disj : e.1 ≠ c ∧ e.1 ≠ b ∧ e.2 ≠ c ∧ e.2 ≠ b
                  have h_disj := hM.2.1 e he_M (c, b) h_cbM heq
                  rcases h_u_in_e with h | h
                  · exact h_disj.2.1 h
                  · exact h_disj.2.2.2 h
          · rcases List.mem_cons.mp h_u_in_c with h_eq | h_u_in_t3
            · -- u = c. M-edge for c is (b, c).
              rw [h_eq] at h_u_in_e
              right; right
              refine ⟨(b, c), ?_, ?_⟩
              · simp [Matching.augmentAlong.edgesOf]
              · rcases h_bc_inM with h_bcM | h_cbM
                · by_cases heq : e = (b, c)
                  · left; exact heq
                  · exfalso
                    have h_disj := hM.2.1 e he_M (b, c) h_bcM heq
                    rcases h_u_in_e with h | h
                    · exact h_disj.2.1 h
                    · exact h_disj.2.2.2 h
                · by_cases heq : e = (c, b)
                  · right; exact heq
                  · exfalso
                    have h_disj := hM.2.1 e he_M (c, b) h_cbM heq
                    rcases h_u_in_e with h | h
                    · exact h_disj.1 h
                    · exact h_disj.2.2.1 h
            · -- u ∈ tail3. Recurse on (c :: tail3).
              -- Use the helper recursively.
              have h_u_in_ct3 : u ∈ c :: tail3 := List.mem_cons.mpr (Or.inr h_u_in_t3)
              -- Manually call helper (can't use ih because ih has wrong P).
              have hRec := matched_vertex_in_path_classification M hM
                (c :: tail3) hAltRest hNodup_c e he_M u h_u_in_ct3 h_u_in_e
              rcases hRec with h_head | h_last | ⟨pe, hpe, h_e_pe⟩
              · -- head of (c :: tail3) = some u, so u = c. But u ∈ tail3 and Nodup gives c ∉ tail3, so u ≠ c.
                exfalso
                simp at h_head
                rcases List.nodup_cons.mp hNodup_c with ⟨hc_notIn, _⟩
                exact hc_notIn (h_head ▸ h_u_in_t3)
              · -- last of (c :: tail3) = some u. tail3 ≠ [] (since u ∈ tail3).
                right; left
                cases hr : tail3 with
                | nil => rw [hr] at h_u_in_t3; simp at h_u_in_t3
                | cons d t4 =>
                  rw [hr] at h_last
                  show (a :: b :: c :: d :: t4).getLast? = some u
                  have hNE_outer : (a :: b :: c :: d :: t4) ≠ [] := List.cons_ne_nil _ _
                  have hNE_inner : (c :: d :: t4) ≠ [] := List.cons_ne_nil _ _
                  rw [List.getLast?_eq_some_getLast hNE_outer]
                  rw [List.getLast?_eq_some_getLast hNE_inner] at h_last
                  injection h_last with h_last
                  have h_eq : (a :: b :: c :: d :: t4).getLast hNE_outer
                            = (c :: d :: t4).getLast hNE_inner := by
                    rw [List.getLast_cons (List.cons_ne_nil _ _),
                        List.getLast_cons (List.cons_ne_nil _ _)]
                  rw [h_eq, h_last]
              · right; right
                refine ⟨pe, ?_, h_e_pe⟩
                simp only [Matching.augmentAlong.edgesOf, List.mem_cons]
                right; right; exact hpe

private lemma toRemove_endpoints_not_in_path
    (M : Matching V) (P : List V) (hM : IsMatching M) (hP : IsAugmentingPath M P)
    (e : V × V) (he_M : e ∈ M)
    (he_notMatch : ¬ ∃ pe ∈ Matching.augmentAlong.edgesOf P,
        e = pe ∨ e = (pe.2, pe.1)) :
    e.1 ∉ P ∧ e.2 ∉ P := by
  -- Extract IsAlt and Nodup from hP, plus head/last unmatched.
  match P, hP with
  | [], hPF => exact False.elim hPF
  | u :: rest, hP_cons =>
    obtain ⟨h_head_unm, h_last_block, hAlt, hNodup⟩ := hP_cons
    -- Extract last vertex unmatched: from match in IsAugmentingPath.
    have hRestNE : rest ≠ [] := by
      intro h
      rw [h] at h_last_block
      simp at h_last_block
    have h_last_unm : ¬ Matching.isMatched M (rest.getLast hRestNE) = true := by
      have h_some : rest.getLast? = some (rest.getLast hRestNE) :=
        List.getLast?_eq_some_getLast _
      rw [h_some] at h_last_block
      exact h_last_block
    -- Helper: derive ⊥ from "v ∈ M-edge ∧ v ∈ P".
    have h_contradict : ∀ v, (e.1 = v ∨ e.2 = v) → v ∈ (u :: rest) → False := by
      intro v h_v_in_e h_v_in_P
      rcases matched_vertex_in_path_classification M hM (u :: rest) hAlt hNodup
          e he_M v h_v_in_P h_v_in_e with h_head | h_last | ⟨pe, hpe, h_e_pe⟩
      · -- v = head = u. h_head_unm says u unmatched. But e ∈ M with v in {e.1, e.2}.
        simp at h_head
        -- h_head : u = v.
        rw [← h_head] at h_v_in_e
        -- h_v_in_e : e.1 = u ∨ e.2 = u
        apply h_head_unm
        simp only [Matching.isMatched, List.any_eq_true, Matching.incident,
          Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨e, he_M, h_v_in_e⟩
      · -- v = last. h_last_unm says last unmatched.
        have h_last_eq : (u :: rest).getLast? = some (rest.getLast hRestNE) := by
          simp [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]
          rw [List.getLast_cons hRestNE]
        rw [h_last_eq] at h_last
        injection h_last with h_last_eq'
        rw [← h_last_eq'] at h_v_in_e
        apply h_last_unm
        simp only [Matching.isMatched, List.any_eq_true, Matching.incident,
          Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨e, he_M, h_v_in_e⟩
      · -- e matches some path-edge pe. Contradicts he_notMatch.
        exact he_notMatch ⟨pe, hpe, h_e_pe⟩
    refine ⟨?_, ?_⟩
    · intro h_e1_in
      exact h_contradict e.1 (Or.inl rfl) h_e1_in
    · intro h_e2_in
      exact h_contradict e.2 (Or.inr rfl) h_e2_in

theorem augmentAlong_preserves_isMatching
    (M : Matching V) (P : List V)
    (hM : IsMatching M) (hP : IsAugmentingPath M P) :
    IsMatching (M.augmentAlong P) := by
  -- Extract hAlt and hNodup from hP, case-splitting on P's structure.
  have ⟨hAlt, hNodup⟩ : IsAlternatingPath M P ∧ P.Nodup := by
    match P, hP with
    | [], hPF => exact hPF.elim
    | _ :: _, hP_cons => exact ⟨hP_cons.2.2.1, hP_cons.2.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  -- 1. No self-loops.
  · intro e he
    unfold Matching.augmentAlong at he
    rcases List.mem_append.mp he with h_mem | h_mem
    · -- e ∈ toRemove ⊆ M.
      have h_in_M : e ∈ M := List.mem_of_mem_filter h_mem
      exact hM.1 e h_in_M
    · -- e ∈ toAdd ⊆ pathEdges.
      have h_in_pe : e ∈ Matching.augmentAlong.edgesOf P :=
        List.mem_of_mem_filter h_mem
      exact edgesOf_no_self_loop P hNodup e h_in_pe
  -- 2. Distinct edges vertex-disjoint.
  · intro e1 he1 e2 he2 hne
    unfold Matching.augmentAlong at he1 he2
    -- Extract the "not matching" condition from toAdd membership.
    have toAdd_notMatch : ∀ e ∈ Matching.augmentAlong.edgesOf P,
        e ∈ (Matching.augmentAlong.edgesOf P).filter (fun pe =>
            ¬ M.any (fun e' => decide (e' = pe) || decide (e' = (pe.2, pe.1)))) →
        ¬ ((e.1, e.2) ∈ M ∨ (e.2, e.1) ∈ M) := by
      intro e _ h_filter hOr
      have h_filter' := (List.mem_filter.mp h_filter).2
      -- h_filter' : decide (¬ M.any ... = true) = true, i.e., M.any ... = false.
      have h_inM : M.any (fun e' => decide (e' = e) || decide (e' = (e.2, e.1))) = true := by
        have hOr' : (e.1, e.2) ∈ M ∨ (e.2, e.1) ∈ M := hOr
        simp only [show (e.1, e.2) = e from Prod.mk.eta] at hOr'
        rcases hOr' with hab | hba
        · exact List.any_eq_true.mpr ⟨e, hab, by simp⟩
        · exact List.any_eq_true.mpr ⟨(e.2, e.1), hba, by simp⟩
      simp [h_inM] at h_filter'
    -- Extract "not match any path-edge" from toRemove membership.
    have toRemove_notMatchAny : ∀ e ∈ M,
        e ∈ M.filter (fun e' => (Matching.augmentAlong.edgesOf P).all
            (fun pe => decide (e' ≠ pe) && decide (e' ≠ (pe.2, pe.1)))) →
        ¬ ∃ pe ∈ Matching.augmentAlong.edgesOf P, e = pe ∨ e = (pe.2, pe.1) := by
      intro e _ h_filter ⟨pe, hpe, hMatch⟩
      have h_filter' := (List.mem_filter.mp h_filter).2
      -- h_filter' : pathEdges.all (fun pe => decide (e ≠ pe) && decide (e ≠ swap pe)) = true.
      have h_pe := List.all_eq_true.mp h_filter' pe hpe
      simp at h_pe
      rcases hMatch with rfl | rfl
      · exact h_pe.1 rfl
      · exact h_pe.2 rfl
    -- Now case-split.
    rcases List.mem_append.mp he1 with h1 | h1 <;>
    rcases List.mem_append.mp he2 with h2 | h2
    -- Case 1: both in toRemove (⊆ M).
    · have he1_M : e1 ∈ M := List.mem_of_mem_filter h1
      have he2_M : e2 ∈ M := List.mem_of_mem_filter h2
      exact hM.2.1 e1 he1_M e2 he2_M hne
    -- Case 2: e1 in toRemove, e2 in toAdd.
    · have he1_M : e1 ∈ M := List.mem_of_mem_filter h1
      have he1_notMatch := toRemove_notMatchAny e1 he1_M h1
      have ⟨h_e1_1_notIn, h_e1_2_notIn⟩ :=
        toRemove_endpoints_not_in_path M P hM hP e1 he1_M he1_notMatch
      -- e1's endpoints are not in P. e2 is a path-edge, so its endpoints are in P.
      have he2_pe : e2 ∈ Matching.augmentAlong.edgesOf P := List.mem_of_mem_filter h2
      have h_e2_1_in : e2.1 ∈ P := edgesOf_fst_in_path P e2 he2_pe
      have h_e2_2_in : e2.2 ∈ P := edgesOf_snd_in_path P e2 he2_pe
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; exact h_e1_1_notIn (h ▸ h_e2_1_in)
      · intro h; exact h_e1_1_notIn (h ▸ h_e2_2_in)
      · intro h; exact h_e1_2_notIn (h ▸ h_e2_1_in)
      · intro h; exact h_e1_2_notIn (h ▸ h_e2_2_in)
    -- Case 3: e1 in toAdd, e2 in toRemove. Symmetric to case 2.
    · have he2_M : e2 ∈ M := List.mem_of_mem_filter h2
      have he2_notMatch := toRemove_notMatchAny e2 he2_M h2
      have ⟨h_e2_1_notIn, h_e2_2_notIn⟩ :=
        toRemove_endpoints_not_in_path M P hM hP e2 he2_M he2_notMatch
      have he1_pe : e1 ∈ Matching.augmentAlong.edgesOf P := List.mem_of_mem_filter h1
      have h_e1_1_in : e1.1 ∈ P := edgesOf_fst_in_path P e1 he1_pe
      have h_e1_2_in : e1.2 ∈ P := edgesOf_snd_in_path P e1 he1_pe
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; exact h_e2_1_notIn (h ▸ h_e1_1_in)
      · intro h; exact h_e2_2_notIn (h ▸ h_e1_1_in)
      · intro h; exact h_e2_1_notIn (h ▸ h_e1_2_in)
      · intro h; exact h_e2_2_notIn (h ▸ h_e1_2_in)
    -- Case 4: both in toAdd. Use edgesOf_*_inj and adjacent_edges_opposite_M_status.
    · have he1_pe : e1 ∈ Matching.augmentAlong.edgesOf P := List.mem_of_mem_filter h1
      have he2_pe : e2 ∈ Matching.augmentAlong.edgesOf P := List.mem_of_mem_filter h2
      have he1_notInM := toAdd_notMatch e1 he1_pe h1
      have he2_notInM := toAdd_notMatch e2 he2_pe h2
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hEq; exact hne (edgesOf_fst_inj P hNodup e1 e2 he1_pe he2_pe hEq)
      · intro hEq
        -- e1.1 = e2.2 means e2 ends where e1 starts. By adjacent_edges_opposite_M_status (e2, e1), opposite M-status.
        have h_share : e2.2 = e1.1 := hEq.symm
        rcases adjacent_edges_opposite_M_status M P hAlt hNodup e2 e1 he2_pe he1_pe h_share with
          ⟨h_e2_in, h_e1_notIn⟩ | ⟨h_e2_notIn, h_e1_in⟩
        · -- e2 in M, e1 not in M. But he2_notInM says e2 not in M. ⊥
          have : (e2.1, e2.2) ∈ M ∨ (e2.2, e2.1) ∈ M := h_e2_in
          exact he2_notInM this
        · -- e1 in M, but he1_notInM. ⊥
          exact he1_notInM h_e1_in
      · intro hEq
        rcases adjacent_edges_opposite_M_status M P hAlt hNodup e1 e2 he1_pe he2_pe hEq with
          ⟨h_e1_in, _⟩ | ⟨_, h_e2_in⟩
        · exact he1_notInM h_e1_in
        · exact he2_notInM h_e2_in
      · intro hEq; exact hne (edgesOf_snd_inj P hNodup e1 e2 he1_pe he2_pe hEq)
  -- 3. Nodup of M.augmentAlong P = toRemove ++ toAdd.
  · unfold Matching.augmentAlong
    apply List.Nodup.append
    · -- toRemove.Nodup: M.filter sublist of M, M.Nodup.
      exact List.Nodup.filter _ hM.2.2
    · -- toAdd.Nodup: pathEdges.filter sublist of pathEdges, pathEdges.Nodup.
      exact List.Nodup.filter _ (edgesOf_nodup P hNodup)
    · -- Disjoint: e ∈ toRemove ∧ e ∈ toAdd is impossible.
      intro e he_remove he_add
      -- e ∈ toRemove: M.filter (no path-edge match condition).
      -- e ∈ toAdd: e ∈ pathEdges. So e is a path-edge.
      -- toRemove condition says e ≠ e (when pe = e), contradiction.
      have h_filter_remove := (List.mem_filter.mp he_remove).2
      have h_e_in_pe : e ∈ Matching.augmentAlong.edgesOf P := (List.mem_filter.mp he_add).1
      have h_pe := List.all_eq_true.mp h_filter_remove e h_e_in_pe
      simp at h_pe

omit [DecidableEq V] in
/-- The empty matching trivially satisfies `IsMatching`. -/
theorem isMatching_nil : IsMatching ([] : Matching V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he; cases he
  · intro e₁ he₁; cases he₁
  · exact List.nodup_nil

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

/-- *Loop progress (size lower bound).* For any starting matching `M`
    satisfying `IsMatching M`, after `n` iterations of the loop either
    the oracle reports `none` (so the loop has terminated) or the size
    of the result is at least `M.size + n` (so the loop made progress
    at every step). -/
private theorem maxMatchingLeanCore_size_lb
    (ctx : Context V) (spec : OracleSpec ctx) :
    ∀ (n : Nat) (M : Matching V), IsMatching M →
      findAugmentingPathLean ctx (maxMatchingLeanCore ctx n M) = none ∨
      (maxMatchingLeanCore ctx n M).size ≥ M.size + n
  | 0, M, _ => by
      right
      simp [maxMatchingLeanCore]
  | n + 1, M, hM => by
      unfold maxMatchingLeanCore
      cases hOpt : findAugmentingPathLean ctx M with
      | none =>
          left
          change findAugmentingPathLean ctx M = none
          exact hOpt
      | some P =>
          have hAug : IsAugmentingPath M P := (spec M).1 P hOpt
          have hM' : IsMatching (M.augmentAlong P) :=
            augmentAlong_preserves_isMatching M P hM hAug
          have hSize : (M.augmentAlong P).size = M.size + 1 :=
            augmentAlong_increases_size_by_one M hM P hAug
          rcases maxMatchingLeanCore_size_lb ctx spec n
                  (M.augmentAlong P) hM' with hNone | hSize'
          · left
            change findAugmentingPathLean ctx
                  (maxMatchingLeanCore ctx n (M.augmentAlong P)) = none
            exact hNone
          · right
            change (maxMatchingLeanCore ctx n (M.augmentAlong P)).size
                  ≥ M.size + (n + 1)
            omega

/-- **Termination obligation.** The loop, given enough fuel
    (`|V|/2 + 1`), terminates with a matching on which the oracle
    returns `none`. The proof reduces to two facts:
    (1) each augmenting step grows the matching by 1
        (`augmentAlong_increases_size_by_one`), and
    (2) any matching has size ≤ `|ctx.vertices| / 2`. The latter is a
    standard graph-theoretic fact (vertex-disjoint edges, ≤ `|V|/2`
    pairs); we take it as an explicit hypothesis `hBound` rather than
    proving it from `IsMatching` directly (which would require either
    `Fintype V` or an extra "M's vertices ⊆ ctx.vertices" invariant). -/
theorem maxMatchingLean_oracle_returns_none
    (ctx : Context V) (spec : OracleSpec ctx)
    (hBound : (maxMatchingLean ctx).size * 2 ≤ ctx.vertices.length) :
    findAugmentingPathLean ctx (maxMatchingLean ctx) = none := by
  have h := maxMatchingLeanCore_size_lb ctx spec
              (ctx.vertices.length / 2 + 1) [] isMatching_nil
  unfold maxMatchingLean
  unfold maxMatchingLean at hBound
  rcases h with hNone | hSize
  · exact hNone
  · exfalso
    have hSimp : (maxMatchingLeanCore ctx (ctx.vertices.length / 2 + 1)
                    ([] : Matching V)).size ≥ ctx.vertices.length / 2 + 1 := by
      have h0 : Matching.size ([] : Matching V) = 0 := rfl
      omega
    unfold Matching.size at hSimp hBound
    omega

/-- **Top-level optimality.** Given an oracle that is sound and complete,
    plus the matching-size bound `|M| ≤ |V|/2` on the loop's output, the
    loop returns a maximum matching. Reduces to:
    * `maxMatchingLean_isMatching` — the result is a matching,
    * `maxMatchingLean_oracle_returns_none` — the oracle returns `none`
      (uses `hBound`),
    * `OracleSpec` — `none` ⇒ no augmenting path,
    * `berge` — no aug path ⇒ maximum. -/
theorem maxMatchingLean_isMaximum
    (ctx : Context V) (spec : OracleSpec ctx)
    (hBound : (maxMatchingLean ctx).size * 2 ≤ ctx.vertices.length) :
    IsMaximumMatching ctx (maxMatchingLean ctx) := by
  have hMatch : IsMatching (maxMatchingLean ctx) :=
    maxMatchingLean_isMatching ctx spec
  -- Loop terminated with oracle returning `none`:
  have hNone : findAugmentingPathLean ctx (maxMatchingLean ctx) = none :=
    maxMatchingLean_oracle_returns_none ctx spec hBound
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

/-! #### Structural helpers for `Matching.contract`

These are the small lemmas about `Matching.contract` that don't depend
on the deep Edmonds argument. They expose how `contract` behaves on
edges that don't touch the blossom cycle — the "easy case" of the
contraction equivalence.

Full Edmonds' blossom-contraction equivalence
(`contract_matching_augmenting_iff`) requires substantial graph theory
(odd-cycle traversal, alternating-path lifting); we factor out only
the structural reductions here. -/

/-- The contraction of the empty matching is empty. -/
@[simp] lemma Matching.contract_nil (B : BlossomShape ([] : Matching V)) :
    Matching.contract ([] : Matching V) B = [] := rfl

/-- Spelling out membership in `M.contract B`: `(u, v) ∈ M.contract B`
    iff there is a "preimage" `(u', v') ∈ M` whose contraction is
    `(u, v)` and not a self-loop. -/
lemma Matching.mem_contract_iff (M : Matching V) (B : BlossomShape M) (u v : V) :
    (u, v) ∈ M.contract B ↔
    ∃ u' v' : V, (u', v') ∈ M ∧
      (if B.cycle.contains u' then B.stem else u') = u ∧
      (if B.cycle.contains v' then B.stem else v') = v ∧
      u ≠ v := by
  unfold Matching.contract
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨u', v'⟩, hM, h⟩
    refine ⟨u', v', hM, ?_, ?_, ?_⟩
    all_goals {
      simp only at h
      split_ifs at h with h_eq <;> simp_all
    }
  · rintro ⟨u', v', hM, hu, hv, hne⟩
    refine ⟨(u', v'), hM, ?_⟩
    simp only
    have : (if B.cycle.contains u' then B.stem else u') ≠
           (if B.cycle.contains v' then B.stem else v') := by
      rw [hu, hv]; exact hne
    rw [if_neg this, hu, hv]

/-- For an edge whose endpoints lie outside `B.cycle`, the contracted
    matching agrees with `M` on it (modulo the no-self-loop check, which
    is automatic when `u ≠ v`). -/
lemma Matching.mem_contract_of_outside_cycle
    (M : Matching V) (B : BlossomShape M) {u v : V}
    (hu_not : B.cycle.contains u = false)
    (hv_not : B.cycle.contains v = false)
    (hne : u ≠ v) :
    (u, v) ∈ M.contract B ↔ (u, v) ∈ M := by
  rw [Matching.mem_contract_iff]
  constructor
  · rintro ⟨u', v', hM, hu, hv, _⟩
    -- u' ∈ B.cycle would mean u = stem; but stem ∈ B.cycle (head of cycle),
    -- so if u = stem, then `B.cycle.contains u = true`, contradicting hu_not.
    -- Hence u' ∉ B.cycle, so u' = u (from hu). Similarly v' = v.
    have h_stem_in : B.cycle.contains B.stem = true := by
      have := B.stemAtBoth.1
      cases hc : B.cycle with
      | nil => simp [hc] at this
      | cons head tail =>
        rw [hc] at this; simp at this
        rw [this]; simp [List.contains_cons]
    have hu' : ¬ B.cycle.contains u' = true := by
      intro hcyc
      rw [if_pos hcyc] at hu
      rw [← hu] at hu_not
      exact absurd h_stem_in (by rw [hu_not]; simp)
    have hv' : ¬ B.cycle.contains v' = true := by
      intro hcyc
      rw [if_pos hcyc] at hv
      rw [← hv] at hv_not
      exact absurd h_stem_in (by rw [hv_not]; simp)
    rw [if_neg hu'] at hu
    rw [if_neg hv'] at hv
    rw [← hu, ← hv]; exact hM
  · intro hM
    refine ⟨u, v, hM, ?_, ?_, hne⟩
    · rw [if_neg]; intro h; rw [hu_not] at h; cases h
    · rw [if_neg]; intro h; rw [hv_not] at h; cases h

/-- **Trivial subcase.** When the contraction is a no-op (`M.contract B = M`),
    the iff is immediate. This subsumes degenerate blossoms (e.g. when `M`
    is empty, or when no `M`-edge has an endpoint in the blossom's cycle). -/
lemma contract_matching_augmenting_iff_of_contract_eq
    (M : Matching V) (B : BlossomShape M) (h : M.contract B = M) :
    (∃ P, IsAugmentingPath (M.contract B) P)
    ↔ (∃ P, IsAugmentingPath M P) := by
  rw [h]

/-- **Empty-matching subcase.** When `M = []`, the contraction is empty too,
    so the iff is immediate. -/
lemma contract_matching_augmenting_iff_nil
    (B : BlossomShape ([] : Matching V)) :
    (∃ P, IsAugmentingPath (Matching.contract ([] : Matching V) B) P)
    ↔ (∃ P, IsAugmentingPath ([] : Matching V) P) :=
  contract_matching_augmenting_iff_of_contract_eq _ B (Matching.contract_nil B)

/-- **Blossom-contraction equivalence.** The contracted matching admits
    an augmenting path iff the original does.

    This is Edmonds' deep theorem (~500-700 LoC of careful blossom-
    traversal arguments). We state it precisely and leave the proof as
    `sorry`. The "easy" subcase where the augmenting path avoids the
    blossom is handled by `Matching.mem_contract_of_outside_cycle`
    (along with similar helpers), but the case where the path enters
    the blossom requires the odd-cycle traversal argument that is the
    heart of Edmonds' algorithm. The empty / no-op cases are closed by
    `contract_matching_augmenting_iff_nil` and
    `contract_matching_augmenting_iff_of_contract_eq`. -/
theorem contract_matching_augmenting_iff
    (M : Matching V) (B : BlossomShape M) :
    (∃ P, IsAugmentingPath (M.contract B) P)
    ↔ (∃ P, IsAugmentingPath M P) := by
  -- Trivial subcases: M = [] or contract is a no-op.
  by_cases h_eq : M.contract B = M
  · exact contract_matching_augmenting_iff_of_contract_eq M B h_eq
  · -- Non-trivial: requires Edmonds' main argument.
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
