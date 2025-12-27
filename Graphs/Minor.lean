import Mathlib
import Graphs.Basic
import Graphs.Contraction

variable {α β : Type*}

def IsMinor (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ (γ : Type*) (K : SimpleGraph γ), G ≼s K ∧ K ≼c H

infix:50 " ≼ " => IsMinor
