-- This module serves as the root of the `Graphs` library.
-- Import modules here that should be built as part of the library.
import Mathlib
import Graphs.Ramsey

def CompleteGraph α : Graph α (α × α) where
  vertexSet := Set.univ
  IsLink e x y := e = (x, y) ∨ e = (y, x)
  isLink_symm e h u v := by grind
  eq_or_eq_of_isLink_of_isLink := by grind
  left_mem_of_isLink := by grind

example : WellQuasiOrdered (α := Nat) (fun a b ↦ a ≤ b) := by
  exact wellQuasiOrdered_le

example : ¬ WellQuasiOrdered (α := Nat) (fun a b ↦ b ≤ a) := by
  simp [WellQuasiOrdered]
  use id
  grind

example {X : Type*} [Preorder X] :
    WellQuasiOrderedLE X ↔
    (¬ ∃ s : Set X, Set.Infinite s ∧ IsAntichain (· ≤ ·) s) ∧
    (¬ ∃ f : ℕ → X, StrictAnti f)
    := by
  classical
  constructor
  · intro h
    constructor
    · intro ⟨s, h₁, h₂⟩
      exact h₁ $ h.finite_of_isAntichain h₂
    · intro ⟨f, hf⟩
      obtain ⟨a, b, h₁, h₂⟩ := h.wqo f
      exact not_lt_of_ge h₂ $ hf h₁
  · intro ⟨h₁, h₂⟩
    constructor
    intro f
    let G := SimpleGraph.completeGraph ℕ
    let ψ : ∀ i j : ℕ, G.Adj i j → Fin 3 := fun i j h =>
      if f (min i j) ≤ f (max i j) then 0 else
      if f (min i j) > f (max i j) then 1 else
      2
    let φ := SimpleGraph.EdgeLabeling.mk ψ (by grind)
    obtain ⟨c, x, hc₁, hc₂⟩ := ramsey2 (by grind) φ
    all_goals sorry
    -- fin_cases c
    -- · simp
    --   let g := f ∘ x
    --   have hg : Monotone g := by sorry
    --   refine ⟨min (x 0) (x 1), max (x 0) (x 1), ?_, ?_⟩
    --   · grind
    --   · have : G.Adj (x 0) (x 1) := by { simp [G] ; grind }
    --     specialize hc₂ 0 1 this
    --     simp [φ, SimpleGraph.EdgeLabeling.get_mk] at hc₂
    --     grind
    -- · let g := f ∘ x
    --   have hg : StrictAnti g := by
    --     intro i j hij
    --     have : G.Adj (x i) (x j) := by { simp [G] ; grind }
    --     specialize hc₂ i j this
    --     simp [φ, SimpleGraph.EdgeLabeling.get_mk, ψ] at hc₂
    --     sorry
    --   cases h₂ ⟨g, hg⟩
    -- · let S := f '' Set.range x
    --   have hS : Set.Infinite S := by sorry
    --   have hS₂ : IsAntichain (· ≤ ·) S := by sorry
    --   cases h₁ ⟨S, hS, hS₂⟩
