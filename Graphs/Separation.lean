import Mathlib

open SimpleGraph

variable {V : Type*}

namespace SimpleGraph

/-
A set of vertices S separates A from B in G if every A-B path in G contains a vertex from S.
-/
def Separates (G : SimpleGraph V) (A B : Set V) (S : Set V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, ∀ p : G.Walk u v, ∃ x ∈ p.support, x ∈ S

end SimpleGraph
