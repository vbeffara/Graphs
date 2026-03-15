import Mathlib

open Fin

variable {α : Type*} [Preorder α] {P : (ℕ → α) → Prop} {f f' : ℕ → α} {hf : P f} {n : ℕ}

def MinAt (P : (ℕ → α) → Prop) (n : ℕ) (f : ℕ → α) : Prop :=
    P f ∧ ∀ g : ℕ → α, (∀ m < n, g m = f m) → (g n < f n) → ¬ P g

theorem MinAt_of_eq (hf : MinAt P n f) (h : ∀ k ≤ n, f' k = f k) : MinAt P n f' := sorry

def MinUntil (P : (ℕ → α) → Prop) (n : ℕ) (f : ℕ → α) : Prop := P f ∧ ∀ k < n, MinAt P k f

def QuasiMin (P : (ℕ → α) → Prop) (f : ℕ → α) : Prop := ∀ n, MinAt P n f

noncomputable def extendAt [Preorder α] [WellFoundedLT α] (P : (ℕ → α) → Prop) (hf : P f) (n : ℕ) :
    { g : ℕ → α // (∀ m < n, g m = f m) ∧ MinAt P n g } := by
  let good (x : α) : Prop := ∃ g, P g ∧ (∀ m < n, g m = f m) ∧ g n = x
  have h1 : ∃ x, good x := ⟨f n, ⟨f, hf, by simp⟩⟩
  have h2 : ∃ x, Minimal good x := exists_minimal_of_wellFoundedLT good h1
  choose x h3 h4 using h2
  obtain ⟨h5, h6, h7⟩ := Classical.choose_spec h3
  refine ⟨_, h6, h5, ?_⟩
  rintro g h8 h9 h10
  have h11 : good (g n) := ⟨g, h10, fun m hm => by simp [h6, h8, hm], rfl⟩
  specialize h4 h11
  grind

noncomputable def extend [Preorder α] [WellFoundedLT α] (P : (ℕ → α) → Prop) (hf : P f) :
    { g // QuasiMin P g } := by
  let φ m : { g : ℕ → α // MinUntil P m g } := by
    refine Nat.recOn m ?_ (fun m fm => ?_)
    · refine ⟨f, hf, by tauto⟩
    · obtain ⟨g, h1, h2⟩ := extendAt P fm.2.1 m
      refine ⟨g, h2.1, fun k hk => ?_⟩
      by_cases h3 : k = m
      · simpa only [h3]
      · have h4 : k < m := by omega
        have h5 := fm.2.2 k h4
        apply MinAt_of_eq h5
        grind
  let g (n : ℕ) : α := (φ (n + 1)).1 n
  have key : ∀ n, ∀ k ≤ n, g k = (φ (n + 1)).1 k := sorry
  have Pg : P g := sorry
  refine ⟨g, fun n => ?_⟩
  apply MinAt_of_eq ((φ (n + 1)).2.2 n (by grind)) (by grind)
