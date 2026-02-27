import Mathlib

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V} {A B S : Set V}

namespace SimpleGraph

/-
A set of vertices S separates A from B in G if every A-B path in G contains a vertex from S.
-/
def Separates (G : SimpleGraph V) (A B : Set V) (S : Set V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, ∀ p : G.Walk u v, ∃ x ∈ p.support, x ∈ S

theorem separates_cover (h : A ∪ B = univ) : G.Separates A B S ↔
    ((A ∩ B ⊆ S) ∧ (∀ u ∈ A, ∀ v ∈ B, G.Adj u v → u ∈ S ∨ v ∈ S)) := by
  sorry

end SimpleGraph
