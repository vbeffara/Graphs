-- This module serves as the root of the `RobertsonSeymour` library.
-- Import modules here that should be built as part of the library.
import RobertsonSeymour.Basic
import Mathlib

variable {α β : Type*}

-- Like (9.1.2) in Diestel's Graph Theory book
theorem ramsey2 [Infinite α] {G : SimpleGraph α} {c : ℕ} (φ : G.EdgeLabeling (Fin c)) :
    ∃ i : Fin c, ∃ f : ℕ → α, f.Injective ∧
    ∀ u v : ℕ, ∀ h : G.Adj (f u) (f v), φ.get (f u) (f v) h = i := by

  have key1 : ∃ X : ℕ → Set α, ∃ x : ℕ → α, ∃ C : ℕ → Fin c, ∀ n,
    ((X n).Infinite) ∧
    (x n ∈ X n) ∧
    (X (n + 1) ⊆ X n \ {x n}) ∧
    (∀ u ∈ X (n + 1), ∀ h : G.Adj (x n) u, φ.get (x n) u h = C n) := by sorry

  obtain ⟨X, x, C, hX⟩ := key1

  have X_mono : Antitone X := sorry

  have key2 : ∃ g : ℕ → ℕ, ∃ C₀ : Fin c, g.Injective ∧ ∀ n, C (g n) = C₀ := by sorry

  obtain ⟨g, C₀, hg_inj, hC⟩ := key2

  use C₀
  use x ∘ g
  constructor
  · sorry
  · intro i j h
    have : g i ≠ g j := by
      intro h1
      simp [h1] at h
    cases this.lt_or_gt with
    | inl hij =>
      have h₁ : x (g j) ∈ X (g i + 1) := by
        have : g i + 1 ≤ g j := Order.add_one_le_iff.mpr hij
        have := X_mono this
        exact this (hX (g j)).2.1
      have := (hX (g i)).2.2.2 (x (g j)) h₁
      grind
    | inr hij =>
      have h₁ : x (g i) ∈ X (g j + 1) := by
        have : g j + 1 ≤ g i := Order.add_one_le_iff.mpr hij
        have := X_mono this
        exact this (hX (g i)).2.1
      have := (hX (g j)).2.2.2 (x (g i)) h₁ h.symm
      rw [SimpleGraph.EdgeLabeling.get_comm]
      grind

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
    obtain ⟨c, x, hc₁, hc₂⟩ := ramsey2 φ
    fin_cases c
    · simp
      let g := f ∘ x
      have hg : Monotone g := by sorry
      refine ⟨min (x 0) (x 1), max (x 0) (x 1), ?_, ?_⟩
      · grind
      · have : G.Adj (x 0) (x 1) := by { simp [G] ; grind }
        specialize hc₂ 0 1 this
        simp [φ, SimpleGraph.EdgeLabeling.get_mk] at hc₂
        grind
    · let g := f ∘ x
      have hg : StrictAnti g := by
        intro i j hij
        have : G.Adj (x i) (x j) := by { simp [G] ; grind }
        specialize hc₂ i j this
        simp [φ, SimpleGraph.EdgeLabeling.get_mk, ψ] at hc₂
        sorry
      cases h₂ ⟨g, hg⟩
    · let S := f '' Set.range x
      have hS : Set.Infinite S := by sorry
      have hS₂ : IsAntichain (· ≤ ·) S := by sorry
      cases h₁ ⟨S, hS, hS₂⟩
