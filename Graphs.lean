import Graphs.Basic
import Graphs.Ramsey

-- No need for Ramsey theory for this, it is in mathlib already

theorem toto {X : Type*} [Preorder X] {f : ℕ → X} :
    StrictAnti f ↔ ∀ n, f (n + 1) < f n := by
  refine ⟨?_, strictAnti_nat_of_succ_lt⟩
  intro h n
  exact h $ lt_add_one n

example {X : Type*} [PartialOrder X] :
    WellQuasiOrderedLE X ↔
    (¬ ∃ s : Set X, Set.Infinite s ∧ IsAntichain (· ≤ ·) s) ∧
    (¬ ∃ f : ℕ → X, StrictAnti f)
    := by
  rw [wellQuasiOrderedLE_iff, and_comm]
  convert Iff.rfl
  · push_neg
    simp only [← Set.not_finite, not_imp_not]
  · simp [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain, ← toto, isEmpty_subtype]
