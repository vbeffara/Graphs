import Mathlib

variable {α ι : Type*} [Infinite α] [Finite ι] [Nonempty ι] {G : SimpleGraph α}

structure Fan (φ : G.EdgeLabeling ι) where
  x : α
  X : Set α
  i : ι
  --
  hx : x ∉ X
  hX : X.Infinite
  hC : ∀ u ∈ X, ∀ h : G.Adj x u, φ.get x u h = i

def ramsey_key (φ : G.EdgeLabeling ι) (X : Set α) (hx : X.Infinite) (x : α) :
    ∃ Y ⊆ X, Y.Infinite ∧ ∃ C : ι, ∀ u ∈ Y, ∀ h : G.Adj x u, φ.get x u h = C := by
  let f : ι → Set α := fun i ↦ { y ∈ X | ∀ h : G.Adj x y, φ.get x y h = i }
  suffices ∃ i : ι, (f i).Infinite by
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
      · use Classical.choice inferInstance ; grind
  have : (⋃ i, f i).Infinite := by grind
  contrapose! this
  exact Set.finite_iUnion this

def next_fan (φ : G.EdgeLabeling ι) (F : Fan φ) :
    ∃ G : Fan φ, G.x ∈ F.X ∧ G.X ⊂ F.X := by
  obtain ⟨y, hy⟩ := F.hX.nonempty
  have hXy : (F.X \ {y}).Infinite := Set.Infinite.diff F.hX $ Set.finite_singleton y
  obtain ⟨Y, hY1, hY2, i, hY3⟩ := ramsey_key φ (F.X \ {y}) hXy y
  refine ⟨⟨y, Y, i, by grind, hY2, hY3⟩, hy, by grind⟩

-- Like (9.1.2) in Diestel's Graph Theory book
theorem ramsey2 (φ : G.EdgeLabeling ι) :
    ∃ S : Set α, S.Infinite ∧ ∃ i : ι,
    ∀ u ∈ S, ∀ v ∈ S, ∀ h : G.Adj u v, φ.get u v h = i := by

  let x₀ := Classical.choice $ Infinite.nonempty α
  have : (Set.univ \ {x₀}).Infinite := sorry
  obtain ⟨X₀, hX₀, hX₀', i₀, h₀⟩ := ramsey_key φ (Set.univ \ {x₀}) this x₀
  let F₀ : Fan φ := ⟨x₀, X₀, i₀, by grind, hX₀', h₀⟩

  choose Φ hΦ using next_fan φ
  let F (n : ℕ) : Fan φ := Φ^[n] F₀
  let C (i : ι) : Set ℕ := { n | (F n).i = i }
  have key0 : ∃ i : ι, (C i).Infinite := by sorry
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
