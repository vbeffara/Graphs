-- This module serves as the root of the `RobertsonSeymour` library.
-- Import modules here that should be built as part of the library.
import RobertsonSeymour.Basic
import Mathlib

variable {α β : Type*}

theorem ramsey2 {G : SimpleGraph α} {c : ℕ} (φ : G.edgeSet → Fin c) :
    ∃ i : Fin c, ∃ Y : Set α, Y.Infinite ∧
    ∀ x ∈ Y, ∀ y ∈ Y, ∀ h : G.Adj x y, φ ⟨_, G.mem_edgeSet.2 h⟩ = i := by
  sorry

def CompleteGraph α : Graph α (α × α) where
  vertexSet := Set.univ
  IsLink e x y := e = (x, y) ∨ e = (y, x)
  isLink_symm e h u v := by grind
  eq_or_eq_of_isLink_of_isLink := by grind
  left_mem_of_isLink := by grind

example : WellQuasiOrdered (α := Nat) (fun a b ↦ a ≤ b) := by
  exact wellQuasiOrdered_le

example : ¬ WellQuasiOrdered (α := Nat) (fun a b ↦ b ≤ a) := by
  simp [WellQuasiOrdered]
  use id
  grind

example {X : Type*} [Preorder X] :
    WellQuasiOrderedLE X ↔
    (¬ ∃ s : Set X, Set.Infinite s ∧ IsAntichain (· ≤ ·) s) ∧
    (¬ ∃ f : ℕ → X, StrictAnti f)
    := by
  constructor
  · intro h
    constructor
    · intro ⟨s, h₁, h₂⟩
      exact h₁ $ h.finite_of_isAntichain h₂
    · intro ⟨f, hf⟩
      obtain ⟨a, b, h₁, h₂⟩ := h.wqo f
      exact not_lt_of_ge h₂ $ hf h₁
  · intro ⟨h₁, h₂⟩
    constructor
    intro f
    let G := SimpleGraph.completeGraph ℕ
    let φ : G.edgeSet → Fin 3 := sorry
    have key := ramsey2 φ
    sorry
