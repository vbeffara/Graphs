import Mathlib
import Graphs.WQO

open Set PartiallyWellOrderedOn

namespace RootedTree

instance : Preorder RootedTree where
  le t₁ t₂ := Nonempty (t₁ ↪o t₂)
  le_refl t := ⟨RelEmbedding.refl _⟩
  le_trans t₁ t₂ t₃ h₁₂ h₂₃ := by obtain ⟨f⟩ := h₁₂ ; obtain ⟨g⟩ := h₂₃ ; exact ⟨f.trans g⟩

abbrev FiniteTree := {T : RootedTree // Finite T}

variable ⦃t₁ t₂ : FiniteTree⦄

lemma card_le_of_le (h : t₁ ≤ t₂) : Nat.card t₁ ≤ Nat.card t₂ := by
  have := t₂.prop
  obtain ⟨f⟩ := h
  exact Nat.card_le_card_of_injective _ f.injective

lemma card_lt_of_lt (h : t₁ < t₂) : Nat.card t₁ < Nat.card t₂ := by
  rw [lt_iff_le_not_ge] at h ⊢
  obtain ⟨⟨f⟩, h2⟩ := h
  refine ⟨card_le_of_le ⟨f⟩, ?_⟩
  contrapose h2
  have h6 := t₂.prop
  have h4 := f.injective.bijective_of_nat_card_le h2
  have h5 := RelIso.ofSurjective f h4.surjective
  exact ⟨h5.symm, by simp⟩

instance : WellFoundedLT FiniteTree := StrictMono.wellFoundedLT card_lt_of_lt

def Bad (f : ℕ → FiniteTree) : Prop := ∀ (m n : ℕ), m < n → ¬f m ≤ f n

abbrev Prefix (n : ℕ) := { f : Fin n → FiniteTree // ∃ g : ℕ → FiniteTree, Bad g ∧ ∀ k : Fin n, g k = f k }

noncomputable def nextPrefix {n} : {f : Prefix n // IsMin f} → {f : Prefix (n + 1) // IsMin f} := by
  rintro ⟨f, hf⟩
  choose g hg1 hg2 using f.2
  let s := {f : Prefix (n + 1) | ∀ k, f.1 k = g k}
  have h1 : s.Nonempty := ⟨⟨fun k => g k, g, by grind⟩, by grind⟩
  let ff := WellFounded.min (r := LT.lt) IsWellFounded.wf _ h1
  refine ⟨ff, ?_⟩

  sorry

def MinimalBadUntil (f : ℕ → FiniteTree) (n : ℕ) : Prop :=
  Bad f ∧ ∀ m < n, ∀ g : ℕ → FiniteTree, (∀ k < m, g k = f k) → (g m < f m) → ¬ Bad g

def MinimalBad (f : ℕ → FiniteTree) : Prop :=
  Bad f ∧ ∀ n, ∀ g : ℕ → FiniteTree, (∀ m < n, g m = f m) → (g n < f n) → ¬ Bad g

lemma exists_minimalBad_aux {f : ℕ → FiniteTree} (hf : Bad f) (n : ℕ) :
    ∃ g : ℕ → FiniteTree, MinimalBadUntil g n := sorry

lemma exists_minimalBad {f : ℕ → FiniteTree} (hf : Bad f) : ∃ g, MinimalBad g := by
  sorry

theorem kruskal : WellQuasiOrderedLE FiniteTree := by
  rw [wellQuasiOrderedLE_def, WellQuasiOrdered]
  by_contra! h : ∃ A, Bad A ; obtain ⟨A, hA⟩ := h
  sorry

end RootedTree
