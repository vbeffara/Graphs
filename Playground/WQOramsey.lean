import Mathlib
import Graphs.Ramsey

open SimpleGraph Classical Set Function

theorem QO_tricolor {X : Type*} [Preorder X] {f : ℕ → X} : ∃ g : ℕ ↪o ℕ,
    Monotone (f ∘ g) ∨ StrictAnti (f ∘ g) ∨
    (∀ i : ℕ, ∀ j : ℕ, i < j → ¬ ((f (g i) ≤ f (g j)) ∨ (f (g i) > f (g j)))) := by

  let φ : (completeGraph ℕ).EdgeLabeling (Fin 3) := by
    refine EdgeLabeling.mk ?_ ?_
    · rintro i j -
      by_cases f (i ⊓ j) ≤ f (i ⊔ j) ; exact 0
      by_cases f (i ⊔ j) < f (i ⊓ j) ; exact 1
      exact 2
    · grind

  obtain ⟨S, h1, ⟨i, h2⟩⟩ := ramsey2 φ
  simp [φ, EdgeLabeling.get_mk] at h2
  have : Infinite S := Set.infinite_coe_iff.mpr h1
  let g := Nat.orderEmbeddingOfSet S
  have h3 {i : ℕ} : g i ∈ S := by simp [g]
  have h5 {i j : ℕ} (hij : i < j) : g i < g j := g.strictMono hij
  have h4 {i j : ℕ} (hij : i < j) : g i ≠ g j := (h5 hij).ne
  use g ; fin_cases i
  · grind [monotone_iff_forall_lt]
  · grind [StrictAnti]
  · grind
