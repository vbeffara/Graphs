import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

open Classical Function

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {e : Sym2 V}

def Minus (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V := G.deleteEdges {e}

infix:60 " -ₑ " => Minus

@[simp] lemma Minus_le : G -ₑ e ≤ G := deleteEdges_le _ _

lemma Minus.card_edge (h : e ∈ G.edgeSet) :
    Fintype.card (G -ₑ e).edgeSet < Fintype.card G.edgeSet := by
  let φ (f : (G -ₑ e).edgeSet) : G.edgeSet := ⟨f, edgeSet_subset_edgeSet.mpr Minus_le f.2⟩
  have φ_inj : Injective φ := by intro e₁ e₂ h ; ext1 ; simpa using h
  apply Fintype.card_lt_of_injective_of_not_mem (b := ⟨_, h⟩) φ φ_inj
  rcases e with ⟨x, y⟩ ; simp [Minus]

end SimpleGraph
