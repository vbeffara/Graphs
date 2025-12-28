import Mathlib
import Graphs.Basic
import Graphs.Contraction

open SimpleGraph

variable {α β γ : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {K : SimpleGraph γ}

def IsMinor (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ K : Subgraph H, G ≼c K.coe

infix:50 " ≼ " => IsMinor

namespace IsMinor

@[refl] theorem refl : G ≼ G := ⟨⊤, .iso_left Subgraph.topIso.symm .refl⟩

theorem iso_left (h1 : G ≃g H) (h2 : H ≼ K) : G ≼ K := by
  obtain ⟨L, hL⟩ := h2
  exact ⟨L, .iso_left h1 hL⟩

theorem of_iso (h : G ≃g H) : G ≼ H := iso_left h .refl

theorem of_Subgraph (K : Subgraph H) : K.coe ≼ H := ⟨K, .refl⟩

theorem of_isContraction (h : G ≼c H) : G ≼ H := ⟨⊤, .iso_right h Subgraph.topIso.symm⟩

theorem trans (h1 : G ≼ H) (h2 : H ≼ K) : G ≼ K := by
  sorry

end IsMinor
