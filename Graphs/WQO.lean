import Mathlib
import Graphs.Ramsey

open Classical

variable {α : Type*} [PartialOrder α]

theorem QO_tricolor {X : Type*} [Preorder X] {f : ℕ → X} : ∃ g : ℕ ↪o ℕ, (Monotone (f ∘ g) ∨ StrictAnti (f ∘ g) ∨ (∀ i : ℕ, ∀ j : ℕ, ¬ ((f (g i) ≤ f (g j)) ∨ (f (g i) > f (g j))))) := by
  let K := SimpleGraph.completeGraph ℕ
  let C := Fin 3
  let c : K.EdgeLabeling C := by
    refine SimpleGraph.EdgeLabeling.mk ?_ ?_
    · rintro i j -
      by_cases f (min i j) ≤ f (max i j) ; exact 0
      by_cases f (min i j) > f (max i j) ; exact 1
      exact 2
    · intro i j h1
      -- have hmin : min i j = min j i := by
      --   apply le_antisymm
      --   apply le_min
      --   apply min_le_right
      --   apply min_le_left
      --   apply le_min
      --   apply min_le_right
      --   apply min_le_left
      -- have hmax : max i j = max j i := by
      --   apply le_antisymm
      --   apply max_le
      --   apply le_max_right
      --   apply le_max_left
      --   apply max_le
      --   apply le_max_right
      --   apply le_max_left
      repeat rw [← min_comm i j]
      repeat rw [← max_comm i j]

  obtain ⟨S, h1, ⟨i, h2⟩⟩ := SimpleGraph.ramsey2 c
  simp [c, SimpleGraph.EdgeLabeling.get_mk] at h2
  have : Infinite S := Set.infinite_coe_iff.mpr h1
  let g := Nat.orderEmbeddingOfSet S
  use g
  fin_cases i
  simp at h2
  left
  unfold Monotone
  intro a b hab
  have h3 {i : ℕ} : g i ∈ S := by simp [g]
  have h4 {i j : ℕ} : K.Adj i j := by sorry
  specialize h2 (g a) h3 (g b) h3 h4

theorem StrictAnti_iff_descending {X : Type*} [Preorder X] {f : ℕ → X} :
    StrictAnti f ↔ ∀ n, f (n + 1) < f n := by
  refine ⟨?_, strictAnti_nat_of_succ_lt⟩
  intro h n
  exact h $ lt_add_one n

theorem WQO_iff : WellQuasiOrderedLE α ↔
    (∀ s : Set α, IsAntichain (· ≤ ·) s → Set.Finite s) ∧
    (∀ f : ℕ → α, ¬ StrictAnti f) := by
  rw [wellQuasiOrderedLE_iff, and_comm]
  simp [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain,
    ← StrictAnti_iff_descending, isEmpty_subtype]

def FinsetLE (s t : Finset α) : Prop := ∃ f : s ↪ t, ∀ x, x.val ≤ f x

-- Lemma 12.1.3
theorem Higman (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  sorry
