import Mathlib

open Fin

variable {α : Type*} [Preorder α] {P : (ℕ → α) → Prop} {f f' : ℕ → α} {hf : P f} {n : ℕ}

def MinAt (P : (ℕ → α) → Prop) (n : ℕ) (f : ℕ → α) : Prop :=
    ∀ g, (∀ m < n, g m = f m) → (g n < f n) → ¬ P g

theorem MinAt_of_eq (hf : MinAt P n f) (h : ∀ k ≤ n, f' k = f k) : MinAt P n f' := by
  grind [MinAt]

def MinUntil (P : (ℕ → α) → Prop) (n : ℕ) (f : ℕ → α) : Prop := ∀ k < n, MinAt P k f

def QuasiMin (P : (ℕ → α) → Prop) (f : ℕ → α) : Prop := ∀ n, MinAt P n f

noncomputable def extendAt [Preorder α] [WellFoundedLT α] (P : (ℕ → α) → Prop) (hf : P f) (n : ℕ) :
    { g : ℕ → α // P g ∧ (∀ m < n, g m = f m) ∧ MinAt P n g } := by
  let good (x : α) : Prop := ∃ g, P g ∧ (∀ m < n, g m = f m) ∧ g n = x
  have h1 : ∃ x, good x := ⟨f n, ⟨f, hf, by simp⟩⟩
  have h2 : ∃ x, Minimal good x := exists_minimal_of_wellFoundedLT good h1
  choose x h3 h4 using h2
  obtain ⟨h5, h6, h7⟩ := Classical.choose_spec h3
  refine ⟨_, h5, h6, ?_⟩
  rintro g h8 h9 h10
  have h11 : good (g n) := ⟨g, h10, fun m hm => by simp [h6, h8, hm], rfl⟩
  specialize h4 h11
  grind

noncomputable def extendAux [Preorder α] [WellFoundedLT α] (P : (ℕ → α) → Prop) (hf : P f) :
    ∀ m : ℕ, { g : ℕ → α // P g ∧ MinUntil P m g }
| 0 => ⟨f, hf, by tauto⟩
| m + 1 => by
    let g := extendAux P hf m
    use extendAt P g.2.1 m
    let ⟨g', h3, h4, h5⟩ := extendAt P g.2.1 m
    refine ⟨h3, fun k hk => ?_⟩
    by_cases h6 : k = m
    · simpa only [h6]
    · have h4 : k < m := by omega
      apply MinAt_of_eq (g.2.2 k h4)
      grind

theorem extendAux_next [WellFoundedLT α] {k} (hk : k < n) :
    (extendAux P hf (n + 1)).1 k = (extendAux P hf n).1 k := by
  exact (extendAt P (extendAux P hf n).2.1 n).2.2.1 k hk

theorem extendAux_later [WellFoundedLT α] {k m} (hk : k < n) :
    (extendAux P hf (n + m)).1 k = (extendAux P hf n).1 k := by
  induction m with
  | zero => rfl
  | succ m ih => rwa [← add_assoc, extendAux_next (by omega)]

noncomputable def extend [Preorder α] [WellFoundedLT α] (P : (ℕ → α) → Prop) (hf : P f) :
    { g // QuasiMin P g } := by
  let φ := extendAux P hf
  let g (n : ℕ) : α := (φ (n + 1)).1 n
  have key n k (hk : k ≤ n) : g k = (φ (n + 1)).1 k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have := @extendAux_later α _ P f hf (k + 1) _ k m (by omega)
    grind
  refine ⟨g, fun n => ?_⟩
  apply MinAt_of_eq ((φ (n + 1)).2.2 n (by grind)) (by grind)

theorem exists_quasiMin [WellFoundedLT α] (P : (ℕ → α) → Prop) (hf : ∃ f, P f) : ∃ g, QuasiMin P g := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := extend P hf
  exact ⟨g, hg⟩
