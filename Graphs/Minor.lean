import Mathlib
import Graphs.Basic
import Graphs.Contraction

open SimpleGraph

variable {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}

def IsMinor (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ K : Subgraph H, G ≼c K.coe

def IsMinor' (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ (γ : Type*) (K : SimpleGraph γ), G ≼s K ∧ K ≼c H

theorem isMinor_iff_isMinor' : IsMinor G H ↔ IsMinor' G H := by
  constructor
  · rintro ⟨K, f, hf1, hf2, hf3⟩
    all_goals sorry
  · rintro ⟨γ, K, f, g⟩
    all_goals sorry

infix:50 " ≼ " => IsMinor
