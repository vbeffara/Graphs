import Architect
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Order.WellQuasiOrder

variable {α : Type*} [Preorder α]

theorem StrictAnti_iff_descending {X : Type*} [Preorder X] {f : ℕ → X} :
    StrictAnti f ↔ ∀ n, f (n + 1) < f n := by
  refine ⟨?_, strictAnti_nat_of_succ_lt⟩
  intro h n
  exact h $ lt_add_one n

@[blueprint
  "prop:wqo-criterion"
  (title := "WQO criterion in Lean")
  (statement := /-- The Diestel criterion above is equivalent to the standard WQO formulation. -/)
  (latexEnv := "proposition")]
theorem WQO_iff : WellQuasiOrderedLE α ↔
    (∀ s : Set α, IsAntichain (· ≤ ·) s → Set.Finite s) ∧
    (∀ f : ℕ → α, ¬ StrictAnti f) := by
  rw [wellQuasiOrderedLE_iff, and_comm]
  simp [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain,
    ← StrictAnti_iff_descending, isEmpty_subtype]

def FinsetLE (s t : Finset α) : Prop := ∃ f : s ↪ t, ∀ x, x.val ≤ f x

-- Lemma 12.1.3
@[blueprint
  "lem:higman"
  (title := "Diestel Lemma~12.1.3 (Higman)")
  (statement := /-- If \(X\) is WQO, then finite sequences/finite supports over \(X\) are WQO. -/)
  (latexEnv := "lemma")]
theorem Higman (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  sorry
