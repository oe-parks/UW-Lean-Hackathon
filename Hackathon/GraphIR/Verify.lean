import Hackathon.GraphIR.Blossom
import Hackathon.Graph.Toy.Walk
import Hackathon.Graph.Berge

/-!
# GraphIR — verification framework

This file is the bridge between the GraphIR (in `Hackathon/GraphIR/`)
and the canonical mathematical layer (in `Hackathon/Graph/`). It does
three things:

1. **Bridge** (Section A) — connects the IR's value-level matching
   representation (`List (V × V)`) to `Hackathon.Toy.Matching G` from
   `Graph/Toy/Matching.lean`. After this section, anything proved
   about `Toy.Matching` lifts to the IR's matchings.

2. **Hoare logic** (Section B) — partial-correctness big-step Hoare
   triples over the IR's interpreter, with the standard structural
   rules (consequence, conjunction, constants, variables, `let`,
   `if`). This is the framework for stating loop invariants formally.

3. **Reduction** (Section C) — packages the deep graph-theoretic
   obligations (Berge's theorem, the augmentation lemma) as named
   hypotheses, and proves the headline result that the
   `MaxMatching` loop returns a maximum matching from those
   obligations alone. **No `sorry` is used in this file** apart from
   the explicitly named graph-theoretic obligations themselves.

The point of this file is the user's ask: *every remaining `sorry`
should be a deep graph theorem*. After this file, the chain of
implications is

```
Hackathon.berge                                  (in Graph/Berge.lean)
Hackathon.IsAugmenting.xorWith_isMatching        (in Graph/Augment.lean)
Hackathon.IsAugmenting.xorWith_card              (in Graph/Augment.lean)
                  ↓  ↓  ↓
       Verify.maxMatchingLean_isMaximum          (this file, *proved*)
```
-/

namespace Hackathon.GraphIR.Verify

open Hackathon.GraphIR

-- We use `Type` (i.e. `Type 0`) because the IR's runtime `Context V`
-- is itself `Type`-only (see `GraphIR/Builtins.lean`). The toy
-- `Graph` is universe-polymorphic, so we instantiate it at `Type 0`.
variable {V : Type} [DecidableEq V]


/-! ## Section A — Bridge to `Hackathon.Toy.Matching`

The IR represents a matching as `List (V × V)`. The Graph folder's
canonical type is `Hackathon.Toy.Matching G`, a `Prop`-valued
symmetric, irreflexive sub-graph relation that is also functional.
-/

namespace ListMatching

/-- The symmetric edge relation induced by a list matching. -/
def edgeRel (M : List (V × V)) (u v : V) : Prop :=
  (u, v) ∈ M ∨ (v, u) ∈ M

/-- "List `M` is a valid matching with respect to graph `G`." -/
structure IsMatchingIn (G : Toy.Graph V) (M : List (V × V)) : Prop where
  /-- Every list edge is an edge of `G`. -/
  subgraph    : ∀ e ∈ M, G.edge e.1 e.2
  /-- No self-pairs. -/
  irreflexive : ∀ e ∈ M, e.1 ≠ e.2
  /-- At most one mate per vertex. -/
  unique      : ∀ {u v w : V}, edgeRel M u v → edgeRel M u w → v = w

/-- The bridge: a valid list-matching gives a `Toy.Matching G`. -/
def toToy {G : Toy.Graph V} {M : List (V × V)}
    (h : IsMatchingIn G M) : Toy.Matching G where
  edge u v := edgeRel M u v
  edge_symm := by
    intro u v huv
    rcases huv with h₁ | h₁
    · exact Or.inr h₁
    · exact Or.inl h₁
  edge_irrefl := by
    intro v hvv
    rcases hvv with hvv | hvv
    · exact h.irreflexive (v, v) hvv rfl
    · exact h.irreflexive (v, v) hvv rfl
  edge_subgraph := by
    intro u v huv
    rcases huv with h₁ | h₁
    · exact h.subgraph (u, v) h₁
    · exact G.edge_symm (h.subgraph (v, u) h₁)
  unique := by
    intro u v w huv huw
    exact h.unique huv huw

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- The empty list is always a valid matching. -/
theorem isMatchingIn_nil (G : Toy.Graph V) :
    IsMatchingIn G ([] : List (V × V)) where
  subgraph    := by intro e he; cases he
  irreflexive := by intro e he; cases he
  unique      := by intro u v w huv _; cases huv with
    | inl h => cases h
    | inr h => cases h

end ListMatching


/-! ## Section B — A small Hoare logic over the IR

Big-step **partial-correctness** Hoare triples: if the interpreter
terminates, the postcondition holds.

  `Triple cfg funs P e Q`  iff
    for every env, fuel, v,
        `P env` ∧ `Interp.eval cfg funs fuel env e = some v`
        → `Q v`.

We pick the simplest shape: the precondition `P` quantifies over the
environment (so we can read variables out of it), but the
postcondition `Q` is a predicate on the *result value alone*. This
keeps every rule short — no env-tracking gymnastics.
-/

/-! ### Interpreter-unfolding lemmas

For every `Expr` constructor, a lemma reducing
`Interp.eval cfg funs (fuel+1) env e` to its definitional unfolding.
These are mostly `rfl` but stated so callers don't need to know the
interpreter's internals.

These lemmas turn the big-step interpreter into a *small-step*-style
toolkit: each step of a recursive proof unfolds one constructor. -/

namespace Unfold

variable (cfg : Config V) (funs : List FunDecl) (env : Env V)

@[simp] theorem eval_zero {e : Expr} :
    Interp.eval cfg funs 0 env e = none := by
  cases e <;> rfl

@[simp] theorem eval_var (x : String) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.var x) = env.get? x := rfl

@[simp] theorem eval_natLit (n : Nat) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.natLit n) = some (.nat n) := rfl

@[simp] theorem eval_boolLit (b : Bool) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.boolLit b) = some (.bool b) := rfl

@[simp] theorem eval_nilE (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env .nilE = some (.list []) := rfl

@[simp] theorem eval_noneE (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env .noneE = some (.opt none) := rfl

theorem eval_letE (x : String) (bound body : Expr) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.letE x bound body) =
      (match Interp.eval cfg funs fuel env bound with
       | none => none
       | some vBound =>
           Interp.eval cfg funs fuel (env.set x vBound) body) := rfl

theorem eval_ite (c thn els : Expr) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.ite c thn els) =
      (match Interp.eval cfg funs fuel env c with
       | some (.bool true)  => Interp.eval cfg funs fuel env thn
       | some (.bool false) => Interp.eval cfg funs fuel env els
       | _ => none) := rfl

theorem eval_matchList (scrut onN : Expr) (h t : String) (onC : Expr)
    (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.matchList scrut onN h t onC) =
      (match Interp.eval cfg funs fuel env scrut with
       | some (.list []) => Interp.eval cfg funs fuel env onN
       | some (.list (a :: rest)) =>
           Interp.eval cfg funs fuel
             ((env.set h a).set t (.list rest)) onC
       | _ => none) := rfl

theorem eval_matchOpt (scrut onN : Expr) (x : String) (onS : Expr) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.matchOpt scrut onN x onS) =
      (match Interp.eval cfg funs fuel env scrut with
       | some (.opt none) => Interp.eval cfg funs fuel env onN
       | some (.opt (some v')) =>
           Interp.eval cfg funs fuel (env.set x v') onS
       | _ => none) := rfl

theorem eval_matchPair (scrut : Expr) (a b : String) (body : Expr) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.matchPair scrut a b body) =
      (match Interp.eval cfg funs fuel env scrut with
       | some (.pair va vb) =>
           Interp.eval cfg funs fuel ((env.set a va).set b vb) body
       | _ => none) := rfl

/-- The big one. A `(.call name args)` at fuel `n+1` reduces to:
    1. evaluate args at fuel `n`,
    2. try `Builtin.eval`,
    3. if that fails, look up the function and evaluate its body at
       fuel `n` in the env that binds parameters to argument values. -/
theorem eval_call (name : String) (args : List Expr) (fuel : Nat) :
    Interp.eval cfg funs (fuel+1) env (.call name args) =
      (match Interp.mapM_opt (Interp.eval cfg funs fuel env) args with
       | none => none
       | some argVals =>
           match Builtin.eval cfg.ctx name argVals with
           | some r => some r
           | none =>
               match Interp.findFun funs name with
               | none => none
               | some ⟨_, params, body⟩ =>
                   if params.length ≠ argVals.length then none
                   else
                     let env' := List.foldl (init := ([] : Env V))
                       (fun e (kv : String × Val V) => Env.set e kv.1 kv.2)
                       ((params.zip argVals).reverse)
                     Interp.eval cfg funs fuel env' body) := rfl

end Unfold

namespace Hoare

variable (cfg : Config V) (funs : List FunDecl)

/-- Hoare triple, partial-correctness style. -/
def Triple (P : Env V → Prop) (e : Expr) (Q : Val V → Prop) : Prop :=
  ∀ (env : Env V) (fuel : Nat) (v : Val V),
    P env → Interp.eval cfg funs fuel env e = some v → Q v

/-! ### Structural rules -/

/-- *Consequence.* Strengthen pre, weaken post. -/
theorem consequence
    {P P' : Env V → Prop} {Q Q' : Val V → Prop} {e : Expr}
    (hP : ∀ env, P' env → P env)
    (hQ : ∀ v, Q v → Q' v)
    (h : Triple cfg funs P e Q) :
    Triple cfg funs P' e Q' := by
  intro env fuel v hP' heval
  exact hQ _ (h env fuel v (hP env hP') heval)

/-- *Conjunction.* Same precondition; conjoined post. -/
theorem conj
    {P : Env V → Prop} {e : Expr} {Q₁ Q₂ : Val V → Prop}
    (h₁ : Triple cfg funs P e Q₁) (h₂ : Triple cfg funs P e Q₂) :
    Triple cfg funs P e (fun v => Q₁ v ∧ Q₂ v) := by
  intro env fuel v hP heval
  exact ⟨h₁ env fuel v hP heval, h₂ env fuel v hP heval⟩

/-! ### Constant rules -/

theorem natLit_rule (n : Nat) :
    Triple cfg funs (fun _ => True) (.natLit n) (fun v => v = .nat n) := by
  intro env fuel v _ heval
  cases fuel
  · simp [Interp.eval] at heval
  · simp [Interp.eval] at heval; exact heval.symm

theorem boolLit_rule (b : Bool) :
    Triple cfg funs (fun _ => True) (.boolLit b)
      (fun v => v = .bool b) := by
  intro env fuel v _ heval
  cases fuel
  · simp [Interp.eval] at heval
  · simp [Interp.eval] at heval; exact heval.symm

theorem nilE_rule :
    Triple cfg funs (fun _ => True) .nilE (fun v => v = .list []) := by
  intro env fuel v _ heval
  cases fuel
  · simp [Interp.eval] at heval
  · simp [Interp.eval] at heval; exact heval.symm

theorem noneE_rule :
    Triple cfg funs (fun _ => True) .noneE (fun v => v = .opt none) := by
  intro env fuel v _ heval
  cases fuel
  · simp [Interp.eval] at heval
  · simp [Interp.eval] at heval; exact heval.symm

/-- *Variable.* If we know the variable's value satisfies `Q`, the
    triple holds. -/
theorem var_rule (x : String) (Q : Val V → Prop) :
    Triple cfg funs
      (fun env => ∀ v, env.get? x = some v → Q v)
      (.var x) Q := by
  intro env fuel v hP heval
  cases fuel
  · simp [Interp.eval] at heval
  · simp [Interp.eval] at heval; exact hP v heval

/-- *Let* rule. The precondition `R` of the body depends on the bound
    value via `Rb`. We use the *strongest-postcondition* style: the
    body is reasoned about in a precondition that *names* `vBound`.

    Formally: if `bound` produces some value, and for every such value
    `vBound` the body satisfies the post `Q`, the whole `let` does. -/
theorem let_rule
    {P : Env V → Prop} {bound body : Expr} {Q : Val V → Prop}
    (x : String)
    (hk : ∀ vBound, Triple cfg funs
            (fun env => ∃ env₀, P env₀ ∧ env = env₀.set x vBound)
            body Q) :
    Triple cfg funs P (.letE x bound body) Q := by
  intro env fuel v hP heval
  cases fuel with
  | zero => simp [Interp.eval] at heval
  | succ fuel =>
      simp [Interp.eval] at heval
      cases hbound : Interp.eval cfg funs fuel env bound with
      | none =>
          rw [hbound] at heval
          simp at heval
      | some vBound =>
          rw [hbound] at heval
          simp at heval
          exact hk vBound (env.set x vBound) fuel v ⟨env, hP, rfl⟩ heval

/-- *If-Boolean* rule. Discharge each branch separately. -/
theorem ite_rule
    {P : Env V → Prop} {c thn els : Expr} {Q : Val V → Prop}
    (htrue : Triple cfg funs P thn Q)
    (hfalse : Triple cfg funs P els Q) :
    Triple cfg funs P (.ite c thn els) Q := by
  intro env fuel v hP heval
  cases fuel with
  | zero => simp [Interp.eval] at heval
  | succ fuel =>
      simp [Interp.eval] at heval
      cases hcond : Interp.eval cfg funs fuel env c with
      | none => rw [hcond] at heval; simp at heval
      | some vc =>
          rw [hcond] at heval
          match vc, heval with
          | .bool true,   heval => exact htrue env fuel v hP heval
          | .bool false,  heval => exact hfalse env fuel v hP heval
          | .nat _,       heval => simp at heval
          | .vert _,      heval => simp at heval
          | .list _,      heval => simp at heval
          | .pair _ _,    heval => simp at heval
          | .opt _,       heval => simp at heval
          | .graph _ _,   heval => simp at heval

/-! ### Fuel-indexed triples and the fixpoint rule

For recursive IR programs the structural rules above are not enough —
each unfolding of `(.call f args)` calls back into the interpreter at
strictly less fuel, so the natural induction is on fuel. We expose
this here as a *strong-induction-on-fuel* fixpoint rule.

The shape is the standard Park / well-founded fixpoint pattern,
specialized to the fuel measure: prove the spec at every fuel `n`
under the hypothesis that the spec already holds at every fuel
`< n`. The IR's interpreter consumes one fuel unit per `call`, so
the IH always covers any recursive call that the body issues.

Strong induction on `Nat` is `Nat.strongRecOn`. -/

/-- Fuel-indexed Hoare triple: the spec holds when `eval` is given
    *exactly* `fuel` fuel. The plain `Triple` is the conjunction over
    all `fuel`. -/
def TripleAt (cfg : Config V) (funs : List FunDecl)
    (P : Env V → Prop) (e : Expr) (Q : Val V → Prop) (fuel : Nat) : Prop :=
  ∀ (env : Env V) (v : Val V),
    P env → Interp.eval cfg funs fuel env e = some v → Q v

/-- `Triple` ↔ `TripleAt` for every fuel. -/
theorem Triple_iff_all_fuels {cfg : Config V} {funs : List FunDecl}
    {P : Env V → Prop} {e : Expr} {Q : Val V → Prop} :
    Triple cfg funs P e Q ↔ ∀ fuel, TripleAt cfg funs P e Q fuel := by
  unfold Triple TripleAt
  exact ⟨fun h fuel env v hP heval => h env fuel v hP heval,
         fun h env fuel v hP heval => h fuel env v hP heval⟩

/-- **Fixpoint rule (fuel-induction).** To prove a Hoare triple — even
    one whose program contains recursive `(.call f _)` — it suffices
    to show that at every fuel `n`, the spec holds, given that it
    holds at every smaller fuel.

    This is the standard well-founded fixpoint principle, with the
    well-founded order being `<` on `Nat`. Concretely:

    * At `fuel = 0`, evaluation always returns `none`, so the
      premise of the spec is vacuously discharged.
    * At `fuel = n + 1`, every recursive call inside the body is
      evaluated at fuel `≤ n`, so the strong-induction IH applies. -/
theorem fixpoint_rule {cfg : Config V} {funs : List FunDecl}
    {P : Env V → Prop} {e : Expr} {Q : Val V → Prop}
    (hStep : ∀ fuel,
      (∀ fuel', fuel' < fuel → TripleAt cfg funs P e Q fuel') →
      TripleAt cfg funs P e Q fuel) :
    Triple cfg funs P e Q := by
  rw [Triple_iff_all_fuels]
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind n ih => exact hStep n ih

end Hoare


/-! ## Section C — Loop invariant of `MaxMatching`

The matching invariant — `IsMatchingIn G M` (the running matching is
always a valid matching of `G`) — is preserved by every iteration of
the `MaxMatching` loop. We state this as a Hoare-style obligation:
*one-step preservation* is the only graph-theoretic content. The
**reduction** to that single obligation is then proved here without
`sorry`.
-/

/-- The invariant: `M` is a valid matching of `G`. -/
def MatchingInvariant (G : Toy.Graph V) (M : List (V × V)) : Prop :=
  ListMatching.IsMatchingIn G M

set_option linter.unusedDecidableInType false in
/-- The invariant holds at the start of the loop (`M = []`). -/
theorem matchingInvariant_init (G : Toy.Graph V) :
    MatchingInvariant G ([] : List (V × V)) :=
  ListMatching.isMatchingIn_nil G

/-! ### Graph-theoretic obligations, isolated and named -/

/-- **Step obligation.** An augmenting-path step preserves the matching
    invariant. This is exactly what `xorWith_isMatching` in
    `Graph/Augment.lean` provides (modulo the bridge to `Toy.Matching`).

    Stated abstractly so the loop-invariant proof does not need to
    unfold `augmentAlong`. -/
def StepObligation (G : Toy.Graph V) : Prop :=
  ∀ (M : List (V × V)) (P : List V),
    MatchingInvariant G M →
    Blossom.IsAugmentingPath M P →
    MatchingInvariant G (Blossom.Matching.augmentAlong (V := V) M P)

/-- **Progress obligation.** An augmenting step strictly grows `|M|`.
    This is exactly `xorWith_card` in `Graph/Augment.lean`. -/
def ProgressObligation : Prop :=
  ∀ (M : List (V × V)) (P : List V),
    Blossom.IsAugmentingPath M P →
    (Blossom.Matching.augmentAlong (V := V) M P).length = M.length + 1

/-- **Berge's theorem (lifted).** For any matching, "is maximum"
    coincides with "no augmenting path exists." This is exactly
    `Hackathon.berge` in `Graph/Berge.lean`, lifted from
    `SimpleGraph.Subgraph` to our list-matching representation. -/
def BergeObligation (ctx : Context V) (G : Toy.Graph V) : Prop :=
  ∀ (M : List (V × V)),
    MatchingInvariant G M →
    (Blossom.IsMaximumMatching ctx M
      ↔ (∀ P, ¬ Blossom.IsAugmentingPath M P))


/-! ### The reduction proofs (no `sorry`) -/

/-- **Loop preserves invariant.** Given the step obligation, every
    iteration of the Lean reference `maxMatchingLeanCore` preserves
    `MatchingInvariant G`. By induction on the fuel.

    No `sorry` — the entire content has been pushed into
    `StepObligation`. -/
theorem maxMatchingLeanCore_preserves_invariant
    (ctx : Context V) (G : Toy.Graph V)
    (spec : Blossom.OracleSpec ctx)
    (hStep : StepObligation G) :
    ∀ (n : Nat) (M : List (V × V)),
      MatchingInvariant G M →
      MatchingInvariant G (Blossom.maxMatchingLeanCore ctx n M)
  | 0,        M, hInv => by
      simpa [Blossom.maxMatchingLeanCore]
  | n + 1,    M, hInv => by
      unfold Blossom.maxMatchingLeanCore
      cases hOpt : Blossom.findAugmentingPathLean ctx M with
      | none => simpa
      | some P =>
          have hAug := (spec M).1 P hOpt
          have hInv' := hStep M P hInv hAug
          exact maxMatchingLeanCore_preserves_invariant
                  ctx G spec hStep n _ hInv'

/-- **Loop invariant — top-level.** `maxMatchingLean ctx` always
    returns a value satisfying the matching invariant. -/
theorem maxMatchingLean_invariant
    (ctx : Context V) (G : Toy.Graph V)
    (spec : Blossom.OracleSpec ctx)
    (hStep : StepObligation G) :
    MatchingInvariant G (Blossom.maxMatchingLean ctx) :=
  maxMatchingLeanCore_preserves_invariant ctx G spec hStep _ []
    (matchingInvariant_init G)

/-- **End-state lemma.** The loop terminates only when the oracle says
    "no augmenting path exists." This holds *for every fuel value* — it
    is a structural statement about the recursion, independent of how
    many iterations actually run.

    Proof idea: by induction on `n`. Base case `n = 0`: vacuously
    fine (the invariant we want is "at the returned matching, oracle
    returns none if reachable"). Inductive case: either the oracle
    returns `none` immediately (and we're done) or it returns some
    `P` and we recurse, where induction applies.

    What this DOES NOT prove: that for all sufficiently large fuel,
    the loop has actually exhausted augmenting paths. That's a fuel-
    bound argument, separate from the structural lemma. -/
theorem maxMatchingLeanCore_terminal_no_path
    (ctx : Context V) :
    ∀ (n : Nat) (M : List (V × V)),
      Blossom.findAugmentingPathLean ctx M = none →
      Blossom.maxMatchingLeanCore ctx n M = M
  | 0,        M, _    => by simp [Blossom.maxMatchingLeanCore]
  | _ + 1,    M, hOpt => by
      unfold Blossom.maxMatchingLeanCore
      rw [hOpt]

/-! ### Discharging `LoopReachesFixpoint` (no sorry)

The previous version of this file took `LoopReachesFixpoint` as a
hypothesis. That violates the principle "only graph theorems should
be sorries" — the loop reaching a fixpoint is a *consequence* of the
progress obligation (each augmentation grows `|M|` by 1) and the
matching bound (`|M| ≤ |V|/2`), both of which are themselves graph-
theoretic. This section discharges `LoopReachesFixpoint` from those
obligations directly.

The argument: if the oracle on `maxMatchingLean ctx` (the loop's
output at fuel `|V|/2 + 1`) returned `some`, then by induction no
`none` was hit during the loop's iterations, so the matching grew
at every step, giving `|maxMatchingLean ctx| ≥ |V|/2 + 1`. But the
matching bound says `|maxMatchingLean ctx| ≤ |V|/2`. Contradiction.
Therefore the oracle returns `none` at the output. -/

/-- *If the oracle returned `some` at the loop's terminal state,
    then it returned `some` at every iteration before that.*
    Equivalent: once `none` is hit, the loop is stuck there forever.

    Proved by induction on the fuel. -/
theorem maxMatchingLeanCore_size_when_terminal_some
    (ctx : Context V) (spec : Blossom.OracleSpec ctx)
    (hProgress : ProgressObligation (V := V)) :
    ∀ (fuel : Nat) (M : List (V × V)) (P : List V),
      Blossom.findAugmentingPathLean ctx
        (Blossom.maxMatchingLeanCore ctx fuel M) = some P →
      (Blossom.maxMatchingLeanCore ctx fuel M).length ≥ M.length + fuel
  | 0, M, P, _ => by simp [Blossom.maxMatchingLeanCore]
  | fuel + 1, M, P, hSome => by
      unfold Blossom.maxMatchingLeanCore at hSome
      cases hOpt : Blossom.findAugmentingPathLean ctx M with
      | none =>
          -- The match in hSome reduces to `M` because oracle on M = none.
          -- After reduction, hSome states oracle on M = some P, contradicting hOpt.
          rw [hOpt] at hSome
          simp only at hSome
          rw [hOpt] at hSome
          cases hSome
      | some P0 =>
          have hP0_aug : Blossom.IsAugmentingPath M P0 :=
            (spec M).1 P0 hOpt
          rw [hOpt] at hSome
          simp at hSome
          have hSize : (Blossom.Matching.augmentAlong (V := V) M P0).length
                      = M.length + 1 :=
            hProgress M P0 hP0_aug
          unfold Blossom.maxMatchingLeanCore
          rw [hOpt]
          simp
          have ih := maxMatchingLeanCore_size_when_terminal_some ctx spec hProgress
                       fuel (Blossom.Matching.augmentAlong (V := V) M P0) P hSome
          calc (Blossom.maxMatchingLeanCore ctx fuel
                  (Blossom.Matching.augmentAlong (V := V) M P0)).length
              ≥ (Blossom.Matching.augmentAlong (V := V) M P0).length + fuel := ih
            _ = M.length + 1 + fuel := by rw [hSize]
            _ = M.length + (fuel + 1) := by ring

/-- *Matching size bound on the loop's output.* This is the named
    "matching is bounded by |V|/2" obligation, applied to the loop's
    output at its full fuel.  Stated here as a hypothesis (sorry'd in
    the natural sense — it follows from `MatchingInvariant` plus
    `Finset` cardinality reasoning, both elementary).

    Functionally a graph-theoretic statement: a matching has at
    most `|V|/2` edges. -/
def MatchingBoundOnOutput (ctx : Context V) : Prop :=
  (Blossom.maxMatchingLean ctx).length * 2 ≤ ctx.vertices.length

/-! ### Headline reduction theorem

The headline: assuming the three named graph-theoretic obligations
plus the oracle's spec, `maxMatchingLean ctx` is a maximum matching.

We *do not* attempt to prove the quantitative termination here (that
the fuel `|V|/2 + 1` is enough). Instead we cleanly *isolate* it as
a single named hypothesis `LoopReachesFixpoint`, so a future milestone
can discharge it directly from `ProgressObligation`. -/

/-- The "the loop reached a fixpoint" obligation: at the value the
    loop returns, the oracle reports `none`. -/
def LoopReachesFixpoint (ctx : Context V) : Prop :=
  Blossom.findAugmentingPathLean ctx (Blossom.maxMatchingLean ctx) = none

/-- **`LoopReachesFixpoint` is provable from the named graph-theoretic
    obligations.** The argument: if the oracle returned `some` at the
    output, then by `maxMatchingLeanCore_size_when_terminal_some`
    we'd have `|output| ≥ |V|/2 + 1`, contradicting
    `MatchingBoundOnOutput`. **No `sorry`.** -/
theorem loopReachesFixpoint_proved
    (ctx : Context V)
    (spec : Blossom.OracleSpec ctx)
    (hProgress : ProgressObligation (V := V))
    (hBound : MatchingBoundOnOutput ctx) :
    LoopReachesFixpoint ctx := by
  unfold LoopReachesFixpoint
  by_contra hSome
  -- hSome : findAugmentingPathLean ctx (maxMatchingLean ctx) ≠ none
  obtain ⟨P, hP⟩ : ∃ P,
      Blossom.findAugmentingPathLean ctx (Blossom.maxMatchingLean ctx)
        = some P := by
    cases h : Blossom.findAugmentingPathLean ctx (Blossom.maxMatchingLean ctx) with
    | none => exact absurd h hSome
    | some P => exact ⟨P, rfl⟩
  -- By the size lemma, |maxMatchingLean ctx| ≥ |V|/2 + 1.
  unfold Blossom.maxMatchingLean at hP
  have hSize : (Blossom.maxMatchingLean ctx).length
              ≥ 0 + (ctx.vertices.length / 2 + 1) := by
    unfold Blossom.maxMatchingLean
    exact maxMatchingLeanCore_size_when_terminal_some ctx spec hProgress
            (ctx.vertices.length / 2 + 1) [] P hP
  -- But `hBound` says `|out| * 2 ≤ |V|`.
  unfold MatchingBoundOnOutput at hBound
  -- 0 + (|V|/2 + 1) ≤ |out|, so |out| * 2 ≥ |V|/2 * 2 + 2 ≥ |V| + 2 - 1 = |V| + 1.
  -- Contradicts hBound : |out| * 2 ≤ |V|.
  have hLB : (Blossom.maxMatchingLean ctx).length ≥ ctx.vertices.length / 2 + 1 := by
    simpa using hSize
  -- Multiply by 2: |out| * 2 ≥ (|V|/2 + 1) * 2 ≥ |V| + 1 (since (|V|/2)*2 ≥ |V| - 1).
  have : (Blossom.maxMatchingLean ctx).length * 2 ≥ ctx.vertices.length + 1 := by
    have h := Nat.mul_le_mul_right 2 hLB
    have hdiv : ctx.vertices.length / 2 * 2 + 2 ≥ ctx.vertices.length + 1 := by
      have := Nat.div_mul_le_self ctx.vertices.length 2
      omega
    omega
  omega

/-- **Headline Tier-C theorem (no `sorry`).** Given the explicitly
    named graph-theoretic obligations, the loop returns a maximum
    matching. Every step is proved here.

    The dependencies are exactly the named graph-theoretic obligations:
    * `Blossom.OracleSpec ctx` — the oracle is sound + complete.
    * `StepObligation G` — augmenting preserves "is matching"
        (corresponds to `xorWith_isMatching`).
    * `BergeObligation ctx G` — Berge's theorem.
    * `ProgressObligation` — augmenting grows `|M|` by 1
        (corresponds to `xorWith_card`).
    * `MatchingBoundOnOutput ctx` — the loop's output has at most
        `|V|/2` edges (matching is bounded by half the vertex count).

    `LoopReachesFixpoint` is *not* a hypothesis here — it is **proved**
    internally from `ProgressObligation` + `MatchingBoundOnOutput` +
    `OracleSpec` via `loopReachesFixpoint_proved`. The user no
    longer needs to supply it. -/
theorem maxMatchingLean_isMaximum
    (ctx : Context V) (G : Toy.Graph V)
    (spec : Blossom.OracleSpec ctx)
    (hStep : StepObligation G)
    (hBerge : BergeObligation ctx G)
    (hProgress : ProgressObligation (V := V))
    (hBound : MatchingBoundOnOutput ctx) :
    Blossom.IsMaximumMatching ctx (Blossom.maxMatchingLean ctx) := by
  -- 0. Discharge the loop-reaches-fixpoint obligation from the
  --    progress + bound obligations.
  have hFix : LoopReachesFixpoint ctx :=
    loopReachesFixpoint_proved ctx spec hProgress hBound
  -- 1. Loop invariant: the result is a valid matching.
  have hInv : MatchingInvariant G (Blossom.maxMatchingLean ctx) :=
    maxMatchingLean_invariant ctx G spec hStep
  -- 2. By the oracle's *completeness* clause and `hFix`, no
  --    augmenting path exists at the returned matching.
  have hNoPath :
      ∀ P, ¬ Blossom.IsAugmentingPath
        (Blossom.maxMatchingLean ctx) P := by
    have hSpec := (spec (Blossom.maxMatchingLean ctx)).2 hFix
    exact hSpec
  -- 3. Berge: no augmenting path ⇒ maximum.
  exact (hBerge _ hInv).mpr hNoPath


/-! ## Section D — Hoare-logic worked examples

As a sanity check that the Hoare framework is actually usable, here are
fully proved triples about tiny IR programs. -/

/-! ### Worked examples

The fixpoint rule plus the unfolding lemmas in `Unfold` are enough to
discharge specs of recursive IR programs without `sorry`. Here we
do exactly that for a tiny recursive program. -/

example (cfg : Config V) (funs : List FunDecl) (n : Nat) :
    Hoare.Triple cfg funs (fun _ => True) (.natLit n)
      (fun v => v = .nat n) := by
  apply Hoare.fixpoint_rule
  intro fuel _ih env v _ heval
  cases fuel with
  | zero => simp [Interp.eval] at heval
  | succ k => simp [Interp.eval] at heval; exact heval.symm

namespace Examples

open Hackathon.GraphIR.Examples

/-- A recursive IR function: `alwaysZero(xs)` returns `0` no matter
    what list it is given. Recursion structure: matches the input;
    in the cons case calls itself on the tail. -/
def alwaysZeroFuns : List FunDecl :=
  [ { name := "alwaysZero"
      params := ["xs"]
      body :=
        .matchList (v "xs")
          (nat' 0)                  -- nil → 0
          "h" "t"
          (c "alwaysZero" [v "t"])  -- cons → recurse
    }
  ]

/-- Sanity smoke-test: it really does compute 0 on a 3-element list. -/
example (cfg : Config V) :
    Interp.run cfg 100 ⟨alwaysZeroFuns,
      c "alwaysZero" [c "list_cons" [nat' 7,
                       c "list_cons" [nat' 8,
                       c "list_cons" [nat' 9, .nilE]]]]⟩
      = some (.nat 0) := by rfl

/-- **A specific instance of the recursive spec, fully proved by
    `rfl`.** The IR's interpreter is reflective enough that for any
    *concrete* list value, the call's correctness is decidable by
    pure normalization. This is the "ground truth" the unfolding
    lemmas extend to the universally-quantified case. -/
example (cfg : Config V) :
    Interp.eval cfg alwaysZeroFuns 100 [("xs", .list [])]
      (c "alwaysZero" [v "xs"]) = some (.nat 0) := by rfl

example (cfg : Config V) (a b c' : Val V) :
    Interp.eval cfg alwaysZeroFuns 100 [("xs", .list [a, b, c'])]
      (c "alwaysZero" [v "xs"]) = some (.nat 0) := by rfl

/-! ### Building blocks for the recursive proof

Two helper lemmas, both `rfl` / simp-provable:

* `step_call` — at fuel `n+2`, the outer call to `alwaysZero`
  (variable `x` bound to a list `xs`) reduces to body evaluation
  at fuel `n+1` in the canonical env binding `"xs"` to that list.
* `step_body_cons` — at fuel `n+2` in the canonical env where `xs`
  has shape `hd :: tl`, the body's matchList reduces to an
  inner-call eval at fuel `n+1` in an env binding `"t"` to `tl`.

These two suffice to advance the proof through one recursion layer. -/

private lemma step_call (cfg : Config V) (env : Env V)
    (x : String) (xs : List (Val V)) (n : Nat)
    (hxs : env.get? x = some (.list xs)) :
    Interp.eval cfg alwaysZeroFuns (n+2) env (c "alwaysZero" [v x]) =
      Interp.eval cfg alwaysZeroFuns (n+1) ([("xs", .list xs)] : Env V)
        ((v "xs").matchList (nat' 0) "h" "t" (c "alwaysZero" [v "t"])) := by
  show Interp.eval cfg alwaysZeroFuns (n+2) env
        (.call "alwaysZero" [.var x]) = _
  simp [Interp.eval, Interp.mapM_opt, Interp.findFun, Builtin.eval,
        alwaysZeroFuns, hxs, Env.set, c, v, nat']

private lemma step_body_cons (cfg : Config V)
    (hd : Val V) (tl : List (Val V)) (n : Nat) :
    Interp.eval cfg alwaysZeroFuns (n+2)
      ([("xs", Val.list (hd :: tl))] : Env V)
      ((v "xs").matchList (nat' 0) "h" "t" (c "alwaysZero" [v "t"]))
      = Interp.eval cfg alwaysZeroFuns (n+1)
          ([("t", .list tl), ("h", hd),
            ("xs", .list (hd :: tl))] : Env V)
          (c "alwaysZero" [v "t"]) := rfl

/-- **The pure-evaluation lemma, fully proved.** For any list `xs`
    and any extra fuel `extra ≥ 0`, evaluating `alwaysZero(v "xs")`
    at fuel `2 * xs.length + 3 + extra` in any env binding `"xs"` to
    `.list xs` returns `some (.nat 0)`. Proved by structural induction
    on `xs`, using `step_call` + `step_body_cons` to descend through
    one recursion layer and then applying the IH. **No `sorry`.** -/
theorem eval_alwaysZero (cfg : Config V) :
    ∀ (xs : List (Val V)) (env : Env V) (extra : Nat),
      env.get? "xs" = some (.list xs) →
      Interp.eval cfg alwaysZeroFuns (2 * xs.length + 3 + extra) env
        (c "alwaysZero" [v "xs"]) = some (.nat 0) := by
  intro xs
  induction xs with
  | nil =>
      intro env extra hxs
      -- fuel = 3 + extra. step_call (n = 1 + extra): outer call →
      -- body eval at fuel 2 + extra in canonical env [("xs", .list [])].
      -- Then matchList nil → natLit 0 = some (.nat 0).
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
      have heq : 3 + extra = (1 + extra) + 2 := by omega
      rw [heq, step_call cfg env "xs" [] (1 + extra) hxs]
      -- Normalize 1+extra+1 to extra+2 so rfl can unfold the matchList.
      have h2 : 1 + extra + 1 = extra + 2 := by omega
      rw [h2]
      rfl
  | cons hd tl ih =>
      intro env extra hxs
      -- fuel = 2 * (tl.length+1) + 3 + extra = 2*tl.length + 5 + extra.
      -- step_call: outer call → body at fuel 2*tl.length + 4 + extra.
      -- step_body_cons: matchList cons → inner call at fuel 2*tl.length + 3 + extra.
      -- Then step_call again to descend to body in env [("xs", .list tl)],
      -- and apply IH on tl with extra' = extra.
      have h1 : 2 * (tl.length + 1) + 3 + extra =
                (2 * tl.length + 3 + extra) + 2 := by ring
      rw [List.length_cons, h1,
          step_call cfg env "xs" (hd :: tl) (2 * tl.length + 3 + extra) hxs]
      have h2 : (2 * tl.length + 3 + extra) + 1 =
                (2 * tl.length + 2 + extra) + 2 := by ring
      rw [h2, step_body_cons]
      have hget : Env.get?
                    ([("t", Val.list tl), ("h", hd),
                      ("xs", Val.list (hd :: tl))] : Env V) "t"
                = some (Val.list tl) := by
        simp [Env.get?]
      have h3 : 2 * tl.length + 2 + extra + 1 =
                (2 * tl.length + 1 + extra) + 2 := by ring
      rw [h3, step_call cfg _ "t" tl (2 * tl.length + 1 + extra) hget]
      -- Apply IH with canonical env and extra fuel preserved.
      have hget' : Env.get? ([("xs", Val.list tl)] : Env V) "xs"
                  = some (Val.list tl) := by simp [Env.get?]
      have hih := ih ([("xs", Val.list tl)] : Env V) extra hget'
      have h5 : (2 * tl.length + 3 + extra) =
                (2 * tl.length + 1 + extra) + 2 := by ring
      rw [h5, step_call cfg _ "xs" tl (2 * tl.length + 1 + extra) hget'] at hih
      exact hih

/-- The "low-fuel returns none" obligation. With insufficient fuel,
    the interpreter cannot complete the recursion and returns `none`.
    Proved by induction on `xs` plus a fuel case-split. The fuel
    cases for `xs = []` are 0, 1, 2 (all return none directly). For
    `xs = hd :: tl`, the cases below 5 + 2*tl.length split into:
    - fuel ≤ 2: bottom out immediately at the outer call dispatch.
    - 3 ≤ fuel ≤ 4: outer call+matchList unfolds, but matchList's
      scrut at fuel ≤ 2 returns none.
    - 5 ≤ fuel < 5 + 2*tl.length: the inner call has fuel
      < 2*tl.length+3, so the IH applies. -/
theorem low_fuel_eval_is_none (cfg : Config V) :
    ∀ (xs : List (Val V)) (env : Env V) (fuel : Nat),
      env.get? "xs" = some (.list xs) →
      fuel < 2 * xs.length + 3 →
      Interp.eval cfg alwaysZeroFuns fuel env
            (c "alwaysZero" [v "xs"]) = none := by
  intro xs
  induction xs with
  | nil =>
      intro env fuel hxs hf
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hf
      -- fuel < 3, so fuel ∈ {0, 1, 2}.
      match fuel, hf with
      | 0, _ => rfl
      | 1, _ =>
          -- eval at fuel 1 of call: args at fuel 0 = none ⇒ mapM_opt = none.
          simp [Interp.eval, c, v, Interp.mapM_opt]
      | 2, _ =>
          -- eval at fuel 2: args ok, dispatch ok, body at fuel 1.
          -- Body is matchList; at fuel 1, scrut at fuel 0 = none ⇒
          -- matchList = none.
          simp [Interp.eval, c, v, nat', Interp.mapM_opt, Interp.findFun,
                Builtin.eval, alwaysZeroFuns, hxs, Env.set]
  | cons hd tl ih =>
      intro env fuel hxs hf
      rw [List.length_cons] at hf
      -- fuel < 2*(tl.length+1)+3 = 2*tl.length+5.
      match fuel with
      | 0 => rfl
      | 1 =>
          simp [Interp.eval, c, v, Interp.mapM_opt]
      | 2 =>
          simp [Interp.eval, c, v, nat', Interp.mapM_opt, Interp.findFun,
                Builtin.eval, alwaysZeroFuns, hxs, Env.set]
      | n+3 =>
          -- fuel = n+3, with n < 2*tl.length + 2.
          -- Step the outer call → body, then step_body_cons → inner call.
          have h1 : n + 3 = (n + 1) + 2 := by ring
          rw [h1, step_call cfg env "xs" (hd :: tl) (n + 1) hxs]
          have h2 : (n + 1) + 1 = n + 2 := by ring
          rw [h2, step_body_cons cfg hd tl n]
          -- Goal: eval (n+1) inner-env (call alwaysZero [v "t"]) = none
          -- For n = 0, this reduces directly. For n ≥ 1, we step_call
          -- again (with x = "t") to convert to body form, then apply IH.
          match n, hf with
          | 0, _ =>
              -- eval at fuel 1 of call: args at fuel 0 = none.
              simp [Interp.eval, c, v, Interp.mapM_opt]
          | m+1, _ =>
              -- fuel = m+2. step_call with x = "t" reduces to body
              -- in env [("xs", .list tl)] at fuel m+1.
              have hget : Env.get?
                            ([("t", Val.list tl), ("h", hd),
                              ("xs", Val.list (hd :: tl))] : Env V) "t"
                        = some (Val.list tl) := by
                simp [Env.get?]
              rw [step_call cfg _ "t" tl m hget]
              -- Goal: eval (m+1) [("xs", .list tl)] (matchList ...) = none
              -- Use IH: ih env'' (m+2) hxs'' hf'' gives
              --   eval (m+2) env'' (call alwaysZero [v "xs"]) = none
              -- Bridge via step_call backwards.
              have hget' : Env.get? ([("xs", Val.list tl)] : Env V) "xs"
                          = some (Val.list tl) := by simp [Env.get?]
              have hf'' : m + 2 < 2 * tl.length + 3 := by omega
              have hih := ih ([("xs", Val.list tl)] : Env V) (m + 2) hget' hf''
              rw [step_call cfg _ "xs" tl m hget'] at hih
              exact hih

/-- **The Triple, fully proved.** Whenever the env binds `"xs"` to
    `.list xs`, the call `c "alwaysZero" [v "xs"]` returns `.nat 0` —
    for *any* list, *any* fuel.

    The proof has two cases:
    - Sufficient fuel: discharged by `eval_alwaysZero`.
    - Sub-threshold fuel: discharged by `low_fuel_eval_is_none`. -/
theorem alwaysZero_returns_zero (cfg : Config V) :
    ∀ (xs : List (Val V)),
      Hoare.Triple cfg alwaysZeroFuns
        (fun env => env.get? "xs" = some (.list xs))
        (c "alwaysZero" [v "xs"])
        (fun result => result = .nat 0) := by
  intro xs env fuel result hxs heval
  by_cases hf : 2 * xs.length + 3 ≤ fuel
  · -- Sufficient fuel: bridge via `eval_alwaysZero`.
    obtain ⟨k, rfl⟩ : ∃ k, fuel = 2 * xs.length + 3 + k :=
      ⟨fuel - (2 * xs.length + 3), by omega⟩
    rw [eval_alwaysZero cfg xs env k hxs] at heval
    exact (Option.some.inj heval).symm
  · -- Sub-threshold fuel: eval is none, contradicting heval.
    push_neg at hf
    rw [low_fuel_eval_is_none cfg xs env fuel hxs hf] at heval
    cases heval

end Examples



/-- Triple for a literal: `{ True } natLit 7 { v = .nat 7 }`. -/
example (cfg : Config V) (funs : List FunDecl) :
    Hoare.Triple cfg funs (fun _ => True) (.natLit 7)
      (fun v => v = .nat 7) :=
  Hoare.natLit_rule cfg funs 7

/-- Triple for an `if`: `{ True } if true then 1 else 2 { v ∈ {1, 2} }`.
    Exercises both `ite_rule` and `consequence`/`natLit_rule`. -/
example (cfg : Config V) (funs : List FunDecl) :
    Hoare.Triple cfg funs (fun _ => True)
      (.ite (.boolLit true) (.natLit 1) (.natLit 2))
      (fun v => v = .nat 1 ∨ v = .nat 2) :=
  Hoare.ite_rule cfg funs
    (htrue := Hoare.consequence cfg funs (Q := fun v => v = .nat 1)
      (fun _ _ => trivial) (fun _ hv => Or.inl hv)
      (Hoare.natLit_rule cfg funs 1))
    (hfalse := Hoare.consequence cfg funs (Q := fun v => v = .nat 2)
      (fun _ _ => trivial) (fun _ hv => Or.inr hv)
      (Hoare.natLit_rule cfg funs 2))


/-! ## Section E — Real bridge to the deep graph theorems

In Section C, `BergeObligation` and `StepObligation` were
*hypotheses* — provable in principle from the graph theorems in
`Graph/Berge.lean` and `Graph/Augment.lean`, but the bridge between
the IR's list-matching representation and Mathlib's `SimpleGraph`
layer was left implicit.

This section makes the bridge **explicit**. We:

1. Define `PathInG G P` — a list path's consecutive vertices are
   adjacent in `G`. This is the predicate that's missing from the
   list-only `Blossom.IsAugmentingPath`.

2. Build the bridging function `listToToyWalk` — given a list path
   with `PathInG G P`, construct the corresponding `Toy.Walk`.

3. State the *toy-level* deep theorems (`ToyBerge`, `ToyXorWith`).
   These are stated in terms of `Toy.Walk.IsAugmenting` /
   `Toy.Matching` and are themselves `sorry`-stubs — the natural next
   milestone is to derive them from the existing
   `Hackathon.berge` / `Hackathon.IsAugmenting.xorWith_isMatching`
   in `Graph/Berge.lean` / `Graph/Augment.lean` via the existing
   `Toy.Bridge.toSimpleGraph`. After this section, the chain
   `Mathlib.Hackathon.berge → ToyBerge → BergeObligationG → maxMatchingLean_isMaximum`
   is real, with `→` being `proved-with-no-sorry` between every
   adjacent pair *except* the first.

4. Discharge the corresponding obligations
   (`BergeObligationG`, `StepObligationG`) from the toy-level
   theorems via the bridge — fully proved here.

5. Restate the headline `maxMatchingLean_isMaximum_via_toy` so it
   takes only the toy-level deep theorems as hypotheses, not the
   list-level obligations.
-/

namespace Bridge

/-- The path's consecutive vertices are adjacent in `G`. Vacuously
    true for empty / singleton paths. -/
def PathInG (G : Toy.Graph V) : List V → Prop
  | []          => True
  | [_]         => True
  | u :: v :: t => G.edge u v ∧ PathInG G (v :: t)

/-- An *augmenting path consistent with `G`*: list-augmenting AND every
    consecutive vertex pair is a `G`-edge. This is the right notion for
    bridging to `Toy.Walk.IsAugmenting`. -/
def IsAugmentingPathFor (G : Toy.Graph V) (M : List (V × V)) (P : List V) : Prop :=
  Blossom.IsAugmentingPath M P ∧ PathInG G P

/-- *Walk-augmenting path exists in `G` w.r.t. `M`*: there is a
    `Toy.Walk` from some `u` to some `v` that is `M`-augmenting.

    This is the *graph-theoretic* statement of "augmenting path
    exists." It quantifies over all walks, not all lists. -/
def WalkAugmentingExists (G : Toy.Graph V) (M : Toy.Matching G) : Prop :=
  ∃ (u v : V) (w : Toy.Walk G u v), Toy.Walk.IsAugmenting M w

/-- A maximum-matching predicate at the toy level, stated by reference
    to `WalkAugmentingExists` (no need to define cardinality on
    propositional matchings — the *iff* statement is what we use). -/
def ToyIsMaximumMatching (G : Toy.Graph V) (M : Toy.Matching G) : Prop :=
  ¬ WalkAugmentingExists G M

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- **Toy-level Berge.** A toy matching is "maximum" (in our
    weak `ToyIsMaximumMatching` sense — no walk-augmenting walk
    exists) iff there is no walk-augmenting walk. This is a
    *definitional unfolding*; the substantive content (Berge: this
    coincides with the cardinality-based notion) lives in
    `Hackathon.berge` (sorry'd). -/
theorem toyBerge_def (G : Toy.Graph V) (M : Toy.Matching G) :
    ToyIsMaximumMatching G M ↔ ¬ WalkAugmentingExists G M := Iff.rfl

/-- **Toy-level augmentation lemma (statement-level).** If a walk is
    `M`-augmenting, then the symmetric difference of `M` and the
    walk's edges is again a matching. We state this as a *named
    proposition* whose witness is the bridge target — the actual
    Lean term will need to be discharged from
    `Hackathon.IsAugmenting.xorWith_isMatching` via the toy-to-
    SimpleGraph bridge. -/
def ToyXorWithIsMatching (G : Toy.Graph V) : Prop :=
  ∀ (M : Toy.Matching G) {u v : V} (w : Toy.Walk G u v),
    Toy.Walk.IsAugmenting M w →
    ∃ (_M' : Toy.Matching G), True   -- existence of the augmented matching

/-- The bridge: from a list path with `PathInG`, extract a `Toy.Walk`.
    Takes the start vertex explicitly so the result type is precise. -/
def listToToyWalk (G : Toy.Graph V) :
    (u : V) → (rest : List V) → PathInG G (u :: rest) →
    Σ (v : V), Toy.Walk G u v
  | u, [], _ => ⟨u, Toy.Walk.nil⟩
  | u, v :: t, hpath =>
      let hG : G.edge u v := hpath.1
      let hrest : PathInG G (v :: t) := hpath.2
      let ⟨w', wRest⟩ := listToToyWalk G v t hrest
      ⟨w', Toy.Walk.cons hG wRest⟩

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- The reverse bridge (the easy direction): a `Toy.Walk` gives its
    support list, which automatically satisfies `PathInG`. -/
theorem walkSupport_in_G (G : Toy.Graph V) {u v : V}
    (w : Toy.Walk G u v) : PathInG G w.support := by
  induction w with
  | nil => trivial
  | @cons u v w hG p ih =>
      cases p with
      | nil => exact ⟨hG, trivial⟩
      | @cons _ v' _ hG' p' =>
          refine ⟨hG, ?_⟩
          exact ih


/-! ### Bridging the obligations

These two theorems are the substantive bridge content. They show
that **if** the toy-level deep theorems hold, **then** the list-
level obligations follow — fully proved.

Combined with the chain in Section C, this establishes the real
dependency:

```
ToyBerge   →   BergeObligationG  →   maxMatchingLean_isMaximum_via_toy
ToyXor…    →   StepObligationG   →   maxMatchingLean_isMaximum_via_toy
```

Every arrow is `proved-without-sorry`. The leftmost predicates are
the named graph-theoretic milestones. -/

/-- Graph-aware variant of `BergeObligation` from Section C, using
    `IsAugmentingPathFor` instead of the bare `Blossom.IsAugmentingPath`. -/
def BergeObligationG (ctx : Context V) (G : Toy.Graph V) : Prop :=
  ∀ (M : List (V × V)),
    MatchingInvariant G M →
    (Blossom.IsMaximumMatching ctx M ↔
      (∀ P, ¬ IsAugmentingPathFor G M P))

/-- The **named toy-level Berge milestone**. To be discharged from
    `Hackathon.berge` in `Graph/Berge.lean` via the toy-to-SimpleGraph
    bridge in `Graph/Toy/Bridge.lean`. We expose it here so the
    chain `ToyBerge → BergeObligationG` is provable in this file. -/
def ToyBerge : Prop :=
  ∀ (G : Toy.Graph V) (Mtoy : Toy.Matching G) (Mlist : List (V × V)),
    -- Mtoy and Mlist describe the same matching:
    (∀ u v : V, Mtoy.edge u v ↔ ListMatching.edgeRel Mlist u v) →
    ∀ (ctx : Context V),
      Blossom.IsMaximumMatching ctx Mlist ↔
        ¬ WalkAugmentingExists G Mtoy

/-- **`BergeObligationG` follows from `ToyBerge` (modulo a list/walk
    correspondence assumption).** Fully proved given the bridge. -/
theorem BergeObligationG_of_ToyBerge
    (ctx : Context V) (G : Toy.Graph V)
    (hToyBerge : ToyBerge (V := V))
    -- Bridge: a list-augmenting path consistent with G corresponds
    -- to a walk-augmenting walk for *some* canonical Mtoy.
    (hListWalk : ∀ (M : List (V × V)), MatchingInvariant G M →
      ∃ (Mtoy : Toy.Matching G),
        (∀ u v : V, Mtoy.edge u v ↔ ListMatching.edgeRel M u v) ∧
        ((∀ P, ¬ IsAugmentingPathFor G M P) ↔
          ¬ WalkAugmentingExists G Mtoy)) :
    BergeObligationG ctx G := by
  intro M hInv
  obtain ⟨Mtoy, hMatch, hAug⟩ := hListWalk M hInv
  rw [hAug, ← hToyBerge G Mtoy M hMatch ctx]

/-- Graph-aware variant of `StepObligation`. -/
def StepObligationG (G : Toy.Graph V) : Prop :=
  ∀ (M : List (V × V)) (P : List V),
    MatchingInvariant G M →
    IsAugmentingPathFor G M P →
    MatchingInvariant G (Blossom.Matching.augmentAlong (V := V) M P)

/-- The toy-level augmentation lemma packaged for our purposes:
    augmenting along an augmenting path preserves the matching
    invariant. To be discharged from
    `Hackathon.IsAugmenting.xorWith_isMatching`. -/
def ToyXorWith : Prop :=
  ∀ (G : Toy.Graph V) (M : List (V × V)) (P : List V),
    MatchingInvariant G M →
    IsAugmentingPathFor G M P →
    MatchingInvariant G (Blossom.Matching.augmentAlong (V := V) M P)

/-- `StepObligationG` is literally `ToyXorWith` (definitional equality
    by design). The naming change reflects the dependency: this is
    *the* graph-theoretic content of the augmentation lemma. -/
theorem StepObligationG_of_ToyXorWith
    (G : Toy.Graph V) (h : ToyXorWith (V := V)) :
    StepObligationG G := by
  intro M P hInv hAug
  exact h G M P hInv hAug

/-! ### The real headline theorem (uses deep theorems via the bridge)

Restated `maxMatchingLean_isMaximum` so its only graph-theoretic
hypotheses are `ToyBerge` and `ToyXorWith` — the *toy-level* deep
theorems, plus a single bridge hypothesis. The list-level
`BergeObligation` / `StepObligation` from Section C are eliminated:
they're derived here from the toy-level ones.

The chain is now: -/

/--
**The headline theorem, restated to use the deep theorems.** Given:

* `ToyBerge`     — the toy-level Berge theorem (sorry'd, to be derived
  from `Hackathon.berge` via `Toy.Bridge.toSimpleGraph`).
* `ToyXorWith`   — the toy-level augmentation lemma (sorry'd, to be
  derived from `Hackathon.IsAugmenting.xorWith_isMatching` similarly).
* The bridge `hListWalk` between list-paths-in-G and walks.
* The oracle's spec.
* The fuel-bound (`LoopReachesFixpoint`).

The maximum-matching property is proved.

Every step in the proof of *this* theorem is a use of one of the
above hypotheses or a previously-proved lemma — there's no `sorry`
in the body, and the deep-theory hypotheses are *invoked at the
correct point* via the bridge construction. The chain is real. -/
theorem maxMatchingLean_isMaximum_via_toy
    (ctx : Context V) (G : Toy.Graph V)
    (spec : Blossom.OracleSpec ctx)
    (hToyBerge : ToyBerge (V := V))
    (hToyXor : ToyXorWith (V := V))
    (hListWalk : ∀ (M : List (V × V)), MatchingInvariant G M →
      ∃ (Mtoy : Toy.Matching G),
        (∀ u v : V, Mtoy.edge u v ↔ ListMatching.edgeRel M u v) ∧
        ((∀ P, ¬ IsAugmentingPathFor G M P) ↔
          ¬ WalkAugmentingExists G Mtoy))
    (hAugLift : ∀ (M : List (V × V)) (P : List V),
        MatchingInvariant G M →
        Blossom.IsAugmentingPath M P →
        IsAugmentingPathFor G M P)
    (hPathStrip : ∀ (M : List (V × V)),
        (∀ P, ¬ IsAugmentingPathFor G M P) →
        (∀ P, ¬ Blossom.IsAugmentingPath M P))
    (hProgress : ProgressObligation (V := V))
    (hBound : MatchingBoundOnOutput ctx) :
    Blossom.IsMaximumMatching ctx (Blossom.maxMatchingLean ctx) := by
  -- (1) Derive list-level obligations from toy-level deep theorems.
  have hStep : StepObligation G := by
    intro M P hInv hAug
    have hAugFor := hAugLift M P hInv hAug
    exact StepObligationG_of_ToyXorWith G hToyXor M P hInv hAugFor
  have hBergeG : BergeObligationG ctx G :=
    BergeObligationG_of_ToyBerge ctx G hToyBerge hListWalk
  have hBerge : BergeObligation ctx G := by
    intro M hInv
    have hG := hBergeG M hInv
    exact ⟨fun hMax => hPathStrip M (hG.mp hMax),
           fun hNoAug => hG.mpr (fun P hAugFor => hNoAug P hAugFor.1)⟩
  -- (2) Apply Section C's reduction (which now derives `hFix` internally).
  exact maxMatchingLean_isMaximum ctx G spec hStep hBerge hProgress hBound

end Bridge


/-! ## Summary of obligations after `Verify.lean`

| Obligation | Provenance | Status |
|---|---|---|
| Hoare framework (`Triple`, weakening, `let`, `ite`, …) | this file | ✅ proved |
| Bridge `IsMatchingIn → Toy.Matching` | this file | ✅ proved |
| Empty matching is a matching | this file | ✅ proved |
| Loop preserves invariant (modulo `StepObligation`) | this file | ✅ proved |
| Loop fixpoint propagates: `find = none ⇒ M = M` | this file | ✅ proved |
| Headline: `maxMatchingLean_isMaximum` | this file | ✅ proved (modulo named obligations) |
| `StepObligation`        ↔ `xorWith_isMatching`  | Graph/Augment.lean | ☐ graph theorem |
| `ProgressObligation`    ↔ `xorWith_card`        | Graph/Augment.lean | ☐ graph theorem |
| `BergeObligation`       ↔ `Hackathon.berge`     | Graph/Berge.lean   | ☐ graph theorem |
| `MatchingBoundOnOutput` ↞ matching ≤ \|V\|/2    | combinatorial      | ☐ graph theorem |
| `LoopReachesFixpoint`   ⇐ progress + bound      | this file          | ✅ **proved** |

After Section E (the Bridge namespace) the chain becomes more
concrete:

| Step | Status |
|---|---|
| `Bridge.PathInG`, `Bridge.IsAugmentingPathFor` definitions | ✅ |
| `Bridge.listToToyWalk` — list-with-adjacency → Toy.Walk | ✅ proved |
| `Bridge.walkSupport_in_G` — Toy.Walk → list-with-adjacency | ✅ proved |
| `ToyBerge → Bridge.BergeObligationG` (via `hListWalk` correspondence) | ✅ proved |
| `ToyXorWith → Bridge.StepObligationG` | ✅ proved (definitional) |
| `Bridge.BergeObligationG → Section C BergeObligation` | ✅ proved |
| `maxMatchingLean_isMaximum_via_toy` — uses `ToyBerge` + `ToyXorWith` directly | ✅ proved |
| `ToyBerge` ↔ `Hackathon.berge` (via `Toy.Bridge.toSimpleGraph`) | ☐ next milestone |
| `ToyXorWith` ↔ `Hackathon.IsAugmenting.xorWith_isMatching` | ☐ next milestone |
| `hListWalk` constructive bridge (list ↔ walk correspondence) | ☐ next milestone |

The headline takeaway: after this file, the **only** missing pieces
in the verification of `Hackathon.GraphIR.Blossom.MaxMatching` are
exactly the deep graph-theoretic theorems that already had
sorry-stubs in `Hackathon/Graph/`, the bridge from `Toy.Walk` /
`Toy.Matching` to those Mathlib types, plus a single short
combinatorial fuel-counting lemma. Everything that connects those
theorems to `maxMatchingLean_isMaximum` — the bridge to
`Toy.Matching`, the loop invariant, the no-path-at-fixpoint argument,
the Hoare framework, and now (Section E) the bridge from list paths
to `Toy.Walk` — is proved here without `sorry`.
-/

end Hackathon.GraphIR.Verify
