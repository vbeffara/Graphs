-- This module serves as the root of the `RobertsonSeymour` library.
-- Import modules here that should be built as part of the library.
import RobertsonSeymour.Basic
import Mathlib

variable {α β : Type*} [hα : Infinite α] {c : ℕ} {G : SimpleGraph α}

structure Fan (φ : G.EdgeLabeling (Fin c)) where
  x : α
  X : Set α
  i : Fin c
  --
  hx : x ∉ X
  hX : X.Infinite
  hC : ∀ u ∈ X, ∀ h : G.Adj x u, φ.get x u h = i

def ramsey_key (hc : 0 < c) (φ : G.EdgeLabeling (Fin c)) (X : Set α) (hx : X.Infinite) (x : α) :
    ∃ Y ⊆ X, Y.Infinite ∧ ∃ C : Fin c, ∀ u ∈ Y, ∀ h : G.Adj x u, φ.get x u h = C := by
  let f : Fin c → Set α := fun i ↦ { y ∈ X | ∀ h : G.Adj x y, φ.get x y h = i }
  suffices ∃ i : Fin c, (f i).Infinite by
    obtain ⟨i, hi⟩ := this
    refine ⟨f i, by grind, hi, i, by grind⟩
  have key : ⋃ i, f i = X := by
    ext y
    rw [Set.mem_iUnion]
    constructor
    · grind
    · intro h
      by_cases hy : G.Adj x y
      · use φ.get x y hy ; grind
      · use ⟨0, hc⟩ ; grind
  have : (⋃ i, f i).Infinite := by grind
  contrapose! this
  exact Set.finite_iUnion this

def next_fan (hc : 0 < c) (φ : G.EdgeLabeling (Fin c)) (F : Fan φ) :
    ∃ G : Fan φ, G.x ∈ F.X ∧ G.X ⊂ F.X := by
  obtain ⟨y, hy⟩ := F.hX.nonempty
  have hXy : (F.X \ {y}).Infinite := Set.Infinite.diff F.hX $ Set.finite_singleton y
  obtain ⟨Y, hY1, hY2, i, hY3⟩ := ramsey_key hc φ (F.X \ {y}) hXy y
  refine ⟨⟨y, Y, i, by grind, hY2, hY3⟩, hy, by grind⟩

-- Like (9.1.2) in Diestel's Graph Theory book
theorem ramsey2 (hc : 0 < c) (φ : G.EdgeLabeling (Fin c)) :
    ∃ S : Set α, S.Infinite ∧ ∃ i : Fin c,
    ∀ u ∈ S, ∀ v ∈ S, ∀ h : G.Adj u v, φ.get u v h = i := by

  let x₀ := Classical.choice $ Infinite.nonempty α
  have : (Set.univ \ {x₀}).Infinite := sorry
  obtain ⟨X₀, hX₀, hX₀', i₀, h₀⟩ := ramsey_key hc φ _ this x₀
  let F₀ : Fan φ := ⟨x₀, X₀, i₀, by grind, hX₀', h₀⟩

  choose Φ hΦ using next_fan hc φ
  let F (n : ℕ) : Fan φ := Φ^[n] F₀
  let C (i : Fin c) : Set ℕ := { n | (F n).i = i }
  have key0 : ∃ i : Fin c, (C i).Infinite := by sorry
  obtain ⟨i, hi⟩ := key0

  let X (n : ℕ) : Set α := (F n).X
  let x (n : ℕ) : α := (F n).x

  have H1 : StrictAnti X := by
    apply strictAnti_of_succ_lt
    simp [X, F, -Function.iterate_succ, Function.iterate_succ']
    grind

  have H2 : Function.Injective x := sorry

  have H3 ⦃m n : ℕ⦄ (hmn : m < n) : x n ∈ X m := sorry

  refine ⟨x '' C i, ?_, i, ?_⟩
  · exact hi.image H2.injOn
  · rintro u ⟨m, rfl, rfl⟩ v ⟨n, hn, rfl⟩ hmn
    have : m ≠ n := by
      rintro rfl
      simp at hmn
    cases lt_or_gt_of_ne this with
    | inl h => exact (F m).hC (x n) (H3 h) hmn
    | inr h =>
      rw [SimpleGraph.EdgeLabeling.get_comm]
      simp [C] at hn
      have := (F n).hC (x m) (H3 h) hmn.symm
      simpa [←hn]

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
