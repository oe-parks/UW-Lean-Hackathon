-- DFS Correctness in Lean 4 (v4.29.1) -- autoresearch target
--
-- Graph model : adjacency list  (Fin n -> List (Fin n))
-- Algorithm   : fuel-based DFS; fuel = n*n+n+1 is always enough
-- Theorems    : (1) visited only grows  (2) every reachable node is found
--
-- Proof bodies are replaced with `sorry`; autoresearch fills them in.

namespace Hackathon.DFS

-- A finite directed graph on n vertices represented as an adjacency list.
def Graph (n : Nat) := Fin n -> List (Fin n)

-- Directed reachability by induction on path length.
inductive Reachable {n : Nat} (g : Graph n) : Fin n -> Fin n -> Prop where
  | refl : forall v, Reachable g v v
  | step : forall u w v, w ∈ g u -> Reachable g w v -> Reachable g u v

-- Fuel-based DFS; any fuel >= stack.length + n suffices.
def dfs {n : Nat} (g : Graph n)
    (stack visited : List (Fin n)) (fuel : Nat) : List (Fin n) :=
  match fuel with
  | 0 => visited
  | fuel + 1 =>
    match stack with
    | [] => visited
    | v :: vs =>
      if visited.contains v then dfs g vs visited fuel
      else dfs g (g v ++ vs) (v :: visited) fuel

-- Top-level DFS from a single source vertex.
def dfsFull {n : Nat} (g : Graph n) (src : Fin n) : List (Fin n) :=
  dfs g [src] [] (n * n + n + 1)

-- Theorem 1: the visited accumulator only grows.
theorem dfs_visited_subset {n : Nat} (g : Graph n)
    (stack visited : List (Fin n)) (fuel : Nat) :
    visited ⊆ dfs g stack visited fuel := by
  induction fuel generalizing stack visited with
    | zero => intro x hx; exact hx
    | succ f ih =>
      unfold dfs
      split
      · exact List.Subset.refl _
      · rename_i v vs
        split
        · exact ih vs visited
        · intro x hx
          apply ih (g v ++ vs) (v :: visited)
          exact List.mem_cons_of_mem v hx

-- Theorem 2: if every node on the stack reaches v then v ends up visited.
theorem dfs_reaches {n : Nat} (g : Graph n)
    (stack visited : List (Fin n)) (fuel : Nat) (v : Fin n)
    (hv    : forall u, u ∈ stack -> Reachable g u v)
    (hfuel : stack.length + n ≤ fuel) :
    v ∈ dfs g stack visited fuel ∨ v ∈ visited := by
  sorry

-- Corollary: DFS completeness.
-- Every vertex reachable from src is present in dfsFull g src.
theorem dfs_complete {n : Nat} (g : Graph n) (src v : Fin n)
    (h : Reachable g src v) :
    v ∈ dfsFull g src := by
  sorry

-- Sanity checks (these examples must stay green).

-- Every node reaches itself.
example {n : Nat} (g : Graph n) (src : Fin n) :
    src ∈ dfsFull g src :=
  dfs_complete g src src (Reachable.refl src)

-- Single-node graph with self-loop.
example : (⟨0, by omega⟩ : Fin 1) ∈ dfsFull (fun _ => [⟨0, by omega⟩]) ⟨0, by omega⟩ :=
  dfs_complete _ _ _ (Reachable.refl _)

end Hackathon.DFS
