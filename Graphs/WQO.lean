import Mathlib

-- No need for Ramsey theory for this, it is in mathlib already

theorem StrictAnti_iff_descending {X : Type*} [Preorder X] {f : ℕ → X} :
    StrictAnti f ↔ ∀ n, f (n + 1) < f n := by
  refine ⟨?_, strictAnti_nat_of_succ_lt⟩
  intro h n
  exact h $ lt_add_one n

example {X : Type*} [PartialOrder X] :
    WellQuasiOrderedLE X ↔
    (∀ s : Set X, IsAntichain (· ≤ ·) s → Set.Finite s) ∧
    (∀ f : ℕ → X, ¬ StrictAnti f)
    := by
  rw [wellQuasiOrderedLE_iff, and_comm]
  simp [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain,
    ← StrictAnti_iff_descending, isEmpty_subtype]

variable {α : Type*} [Preorder α]

def FinsetLE (s t : Finset α) : Prop := ∃ f : s ↪ t, ∀ x : s, x.val ≤ f x

-- Lemma 12.1.3
theorem WQO_Finset (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  sorry
