import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

structure FiniteGraph where
  support : Type*
  finite : Fintype support
  graph : SimpleGraph support

end SimpleGraph
