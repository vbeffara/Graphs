import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

structure FiniteGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

end SimpleGraph
