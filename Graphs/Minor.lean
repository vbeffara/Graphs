import Mathlib
import Graphs.Basic
import Graphs.Contraction

open SimpleGraph

variable {α β γ : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {K : SimpleGraph γ}

def IsMinor (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ K : Subgraph H, G ≼c K.coe

infix:50 " ≼ " => IsMinor

namespace IsMinor

@[refl] theorem refl : G ≼ G := by
  refine ⟨⊤, ?_⟩
  sorry

theorem of_Iso (h : G ≃g H) : G ≼ H := by
  sorry

theorem of_Subgraph (K : Subgraph H) : K.coe ≼ H := ⟨K, .refl⟩

theorem of_isContraction : G ≼c H → G ≼ H := by
  rintro ⟨φ, h1, h2, rfl⟩
  refine ⟨⊤, fun x => φ x, ?_, ?_, ?_⟩
  · intro y ; obtain ⟨x, rfl⟩ := h1 y ; simp
  · simp
    sorry
  all_goals sorry

theorem trans (h1 : G ≼ H) (h2 : H ≼ K) : G ≼ K := by
  obtain ⟨H', ⟨φ, h3, h4, rfl⟩⟩ := h1
  obtain ⟨K', ⟨ψ, h6, h7, rfl⟩⟩ := h2
  let SK : Set γ := { z : γ | ∃ hz : z ∈ K'.verts, ψ ⟨z, hz⟩ ∈ H'.verts }
  let SK' := Subtype.val '' (ψ ⁻¹' H'.verts)
  have : SK = SK' := by ext z ; simp [SK, SK']
  let ad (z z' : γ) : Prop := z ∈ SK ∧ z' ∈ SK ∧ K.Adj z z'
  let K'' : Subgraph K := by
    refine ⟨SK, ?_, ?_, ?_, ?_⟩
    all_goals sorry
  refine ⟨?_, ?_⟩
  all_goals sorry

end IsMinor
