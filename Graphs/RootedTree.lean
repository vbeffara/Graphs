import Mathlib
import Graphs.WQO

universe u

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
  have h3 := card_le_of_le ⟨f⟩
  refine ⟨h3, ?_⟩
  contrapose h2
  have h6 := t₂.prop
  have h4 := f.injective.bijective_of_nat_card_le h2
  have h5 := RelIso.ofSurjective f h4.surjective
  exact ⟨h5.symm, by simp⟩

instance finiteTree_wf : WellFoundedLT FiniteTree := StrictMono.wellFoundedLT card_lt_of_lt

theorem kruskal : WellQuasiOrderedLE FiniteTree.{u} := by
  rw [wellQuasiOrderedLE_def, WellQuasiOrdered]
  by_contra!
  sorry

end RootedTree
