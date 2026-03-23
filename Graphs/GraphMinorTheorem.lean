import Architect
import Mathlib.Order.WellQuasiOrder
import Graphs.Minor

variable {α : Type*} {G : SimpleGraph α}

open SimpleGraph

structure FiniteGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

@[blueprint "def:graph_minor_preorder"]
instance : Preorder FiniteGraph where
  le G H := G.graph ≼ H.graph
  le_refl G := IsMinor.refl
  le_trans G H K := IsMinor.trans

@[blueprint
  "thm:graph-minor-theorem"
  (title := "Diestel Theorem~12.7.1 (Robertson--Seymour 1986--2004)")
  (statement := /-- Finite graphs are well-quasi-ordered by the minor relation. -/)
  (proof := /-- Not yet formalized in this project. -/)]
instance GraphMinorTheorem : WellQuasiOrderedLE FiniteGraph := sorry

@[blueprint
  "thm:wagner"
  (title := "Planar forbidden-minor pointer")
  (statement := /-- \(G \preceq \mathrm{Plane} \iff K_5 \not\preceq G \land K_{3,3} \not\preceq G\).
    -/)
  (proof := /-- Not yet formalized in this project. -/)]
theorem Wagner : G ≼ Plane ↔ K5 ⋠ G ∧ K33 ⋠ G := sorry
