-- import Mathlib
import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.BourbakiWitt

open Set Function

variable {α ι : Type*} [Finite ι] [Nonempty ι] {G : SimpleGraph α}

structure Fan (φ : G.EdgeLabeling ι) where
  x : α
  X : Set α
  i : ι
  --
  hx : x ∉ X
  hX : X.Infinite
  hC : ∀ u ∈ X, ∀ h : G.Adj x u, φ.get x u h = i

def Monochromatic (φ : G.EdgeLabeling ι) (S : Set α) : Prop :=
  ∃ i : ι, ∀ u ∈ S, ∀ v ∈ S, ∀ h : G.Adj u v, φ.get u v h = i

theorem ramsey_key (φ : G.EdgeLabeling ι) (X : Set α) (hx : X.Infinite) (x : α) :
    ∃ Y ⊆ X, Y.Infinite ∧ ∃ C : ι, ∀ u ∈ Y, ∀ h : G.Adj x u, φ.get x u h = C := by
  let f : ι → Set α := fun i ↦ { y ∈ X | ∀ h : G.Adj x y, φ.get x y h = i }
  suffices ∃ i : ι, (f i).Infinite by
    obtain ⟨i, hi⟩ := this
    refine ⟨f i, by grind, hi, i, by grind⟩
  have key : ⋃ i, f i = X := by
    ext y
    rw [mem_iUnion]
    constructor
    · grind
    · intro h
      by_cases hy : G.Adj x y
      · use φ.get x y hy ; grind
      · use Classical.choice inferInstance ; grind
  have : (⋃ i, f i).Infinite := by grind
  contrapose! this
  exact finite_iUnion this

theorem next_fan (φ : G.EdgeLabeling ι) (F : Fan φ) : ∃ G : Fan φ, G.x ∈ F.X ∧ G.X ⊂ F.X := by
  obtain ⟨y, hy⟩ := F.hX.nonempty
  have hXy : (F.X \ {y}).Infinite := Infinite.diff F.hX $ finite_singleton y
  obtain ⟨Y, hY1, hY2, i, hY3⟩ := ramsey_key φ (F.X \ {y}) hXy y
  refine ⟨⟨y, Y, i, by grind, hY2, hY3⟩, hy, by grind⟩

-- Special case of Theorem 9.1.2 in Diestel's Graph Theory book, for `k=2`
theorem ramsey2 [Infinite α] (φ : G.EdgeLabeling ι) :
    ∃ S : Set α, S.Infinite ∧ Monochromatic φ S := by

  let x₀ := Classical.choice $ Infinite.nonempty α
  have : (univ \ {x₀}).Infinite :=
    Infinite.diff infinite_univ (finite_singleton _)
  obtain ⟨X₀, hX₀, hX₀', i₀, h₀⟩ := ramsey_key φ (univ \ {x₀}) this x₀
  let F₀ : Fan φ := ⟨x₀, X₀, i₀, by grind, hX₀', h₀⟩

  choose Φ hΦ₁ hΦ₂ using next_fan φ
  let F (n : ℕ) : Fan φ := Φ^[n] F₀
  let C (i : ι) : Set ℕ := { n | (F n).i = i }
  have key0 : ∃ i : ι, (C i).Infinite := by
    simp [C, ← infinite_coe_iff]
    exact Finite.exists_infinite_fiber _
  obtain ⟨i, hi⟩ := key0

  let X (n : ℕ) : Set α := (F n).X
  let x (n : ℕ) : α := (F n).x

  have H1 : StrictAnti X := by
    apply strictAnti_of_succ_lt
    simp [X, F, -Function.iterate_succ, Function.iterate_succ']
    grind

  have H3 ⦃m n : ℕ⦄ (hmn : m < n) : x n ∈ X m := by
    cases n with
    | zero => contradiction
    | succ n =>
      simp [x, F, -Function.iterate_succ, Function.iterate_succ']
      exact H1.antitone (Nat.le_of_lt_succ hmn) (hΦ₁ (F n))

  have H2 : Function.Injective x := by
    apply injective_of_lt_imp_ne
    intro m n h₁
    by_contra h₂
    have h₃ := H3 h₁
    rw [← h₂] at h₃
    exact (F m).hx h₃

  refine ⟨x '' C i, hi.image H2.injOn, i, ?_⟩
  rintro u ⟨m, rfl, rfl⟩ v ⟨n, hn, rfl⟩ hmn
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

-- Now for the more general version (without a graph)

variable {k : ℕ} [Infinite α]

def parts (k : ℕ) (α : Type*) := { s : Finset α // s.card = k }

def Monochromatic' (φ : parts k α → ι) (S : Set α) : Prop :=
  ∃ i : ι, ∀ s : parts k α, (s.1 : Set α) ⊆ S → φ s = i

structure Fan' (φ : parts (k+1) α → ι) where
  x : α
  X : Set α
  i : ι
  --
  hx : x ∉ X
  hX : X.Infinite
  hC : ∀ (s : parts k α) (hs : (s.1 : Set α) ⊆ X), φ ⟨Finset.cons x s.1 (by grind), by simp [s.2]⟩ = i

theorem ramsey912 (k : ℕ) (φ : parts k α → ι) : ∃ S : Set α,
    S.Infinite ∧ Monochromatic' φ S := by
  induction k generalizing α with
  | zero =>
    refine ⟨univ, infinite_univ, φ ⟨∅, rfl⟩, ?_⟩
    simp [parts] ; grind
  | succ k ih =>
    have key (X : Set α) (hX : X.Infinite) (x : α) (hxX : x ∉ X) :
        ∃ Y : Set α, ∃ hY : Y ⊆ X, Y.Infinite ∧ ∃ C : ι, ∀ u : parts k α, ∀ h : (u.1 : Set α) ⊆ Y,
        φ ⟨Finset.cons x u.1 (by grind), by simp [u.2]⟩ = C := by

      let ψ (s : parts k X) : ι :=
        let s' : parts k α := ⟨Finset.map (Embedding.subtype _) s.1, by simp [s.2]⟩
        φ ⟨Finset.cons x s'.1 (by simp [s', hxX]), (by simp [s'.2])⟩

      obtain ⟨S, h1, C, h2⟩ := @ih X hX.to_subtype ψ

      refine ⟨Embedding.subtype _ '' S, ?_, ?_, C, ?_⟩
      · simp
      · exact h1.image (Embedding.subtype_injective _ |>.injOn)
      rintro s hs
      simp at hs
      have hs' : (s.1 : Set _) ⊆ X := by
        intro u hu
        have := hs hu
        grind
      let ss : parts k X := by
        refine ⟨?_, ?_⟩
        · classical exact Finset.subtype _ s.1
        · simpa [← s.2, Finset.card_filter_eq_iff] using hs'
      have h3 : (ss.1 : Set _) ⊆ S := sorry
      specialize h2 ss h3
      convert h2
      ext
      simp [ss]
      grind

    have next (F : Fan' φ) : ∃ G : Fan' φ, G.x ∈ F.X ∧ G.X ⊂ F.X := by
      obtain ⟨y, hy⟩ := F.hX.nonempty
      have hXy : (F.X \ {y}).Infinite := Infinite.diff F.hX $ finite_singleton y
      obtain ⟨Y, hY1, hY2, C, hY3⟩ := key _ hXy y (by grind)
      refine ⟨⟨y, Y, C, by grind, hY2, hY3⟩, hy, by grind⟩

    all_goals sorry
