import Mathlib.Order.WellQuasiOrder
import Graphs.Minor

variable {α : Type*} [Fintype α] {G : SimpleGraph α}

open SimpleGraph

structure FiniteGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

instance : Preorder FiniteGraph where
  le G H := G.graph ≼ H.graph
  le_refl G := IsMinor.refl
  le_trans G H K := IsMinor.trans

instance GraphMinorTheorem : WellQuasiOrderedLE FiniteGraph := sorry

theorem Wagner : G ≼ Plane ↔ K5 ⋠ G ∧ K33 ⋠ G := sorry
