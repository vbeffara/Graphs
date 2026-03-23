import Architect
import Graphs.QuasiMin
import Mathlib.Order.SuccPred.Tree
import Mathlib.Order.WellQuasiOrder
import Mathlib.SetTheory.Cardinal.Finite

open Set

namespace RootedTree

@[blueprint "def:rooted_tree_preorder"]
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

def IsBadSeq {α : Type*} [LE α] (f : ℕ → α) : Prop := ∀ i j, i < j → ¬ (f i ≤ f j)

-- Being a bad sequence is a local property
theorem key {α : Type*} [LE α] : localProp (IsBadSeq (α := α)) := by
  intro f h i j hij ; grind [IsBadSeq, h (1 + max i j)]

@[blueprint "thm:kruskal"
  (title := "Kruskal's Tree Theorem")
  (statement := /-- Finite rooted trees are well-quasi-ordered by the embedding relation. -/)]
theorem kruskal : WellQuasiOrderedLE FiniteTree := by
  rw [wellQuasiOrderedLE_def, WellQuasiOrdered]
  by_contra! : ∃ A : ℕ → FiniteTree, IsBadSeq A
  obtain ⟨A, A_bad, A_min⟩ := exists_quasiMin key this
  sorry

end RootedTree
