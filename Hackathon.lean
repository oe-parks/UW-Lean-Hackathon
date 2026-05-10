import Hackathon.Basic

-- Toy graph framework (warm-up): own Graph definition + practice lemmas.
import Hackathon.Graph.Toy.Basic
import Hackathon.Graph.Toy.Examples
import Hackathon.Graph.Toy.Lemmas
import Hackathon.Graph.Toy.Bridge

-- Mathlib SimpleGraph layer.
import Hackathon.Graph.Walks
import Hackathon.Graph.Matching

-- Phase 2 skeletons: theorems / algorithms with `sorry` stubs.
import Hackathon.Graph.Augment
import Hackathon.Graph.Berge
import Hackathon.Graph.Algorithms.Bipartite
import Hackathon.Graph.Algorithms.Blossom

-- Toy graph layer: matchings, walks, alternating + augmenting paths.
import Hackathon.Graph.Toy.Matching
import Hackathon.Graph.Toy.Walk

-- Exercises: concrete graphs + a worked example + sorry-stubs to fill in.
import Hackathon.Exercises.Graphs
import Hackathon.Exercises.Worked
import Hackathon.Exercises.Matchings
import Hackathon.Exercises.Augmenting

-- GraphIR (Layer 2.5): functional/SSA-style IR for graph algorithms,
-- with a runnable interpreter and a BFS correctness scaffold.
import Hackathon.GraphIR.Types
import Hackathon.GraphIR.Syntax
import Hackathon.GraphIR.Builtins
import Hackathon.GraphIR.Interpreter
import Hackathon.GraphIR.Examples
import Hackathon.GraphIR.BFS
import Hackathon.GraphIR.Blossom
import Hackathon.GraphIR.Verify
import Hackathon.GraphIR.Primitives
