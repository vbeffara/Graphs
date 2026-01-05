-- import Mathlib
import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.BourbakiWitt

open Set Function

variable {α ι : Type*} [Finite ι] {k : ℕ}

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

theorem ramsey912 [Infinite α] (φ : parts k α → ι) : ∃ S : Set α, S.Infinite ∧ Monochromatic' φ S := by
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
      have h3 : (ss.1 : Set _) ⊆ S := by
        simp [ss]
        intro a ha
        simp at ha
        specialize hs ha
        grind
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

    let x₀ := Classical.choice $ Infinite.nonempty α

    have : (univ \ {x₀}).Infinite :=
      Infinite.diff infinite_univ (finite_singleton _)
    obtain ⟨X₀, hX₀, hX₀', i₀, h₀⟩ := key (univ \ {x₀}) this x₀ (by grind)
    let F₀ : Fan' φ := ⟨x₀, X₀, i₀, by grind, hX₀', h₀⟩

    choose Φ hΦ₁ hΦ₂ using next

    let F (n : ℕ) : Fan' φ := Φ^[n] F₀
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

    rintro s hs
    have s_nonempty : s.1.Nonempty := by simp [← Finset.card_pos, s.2]
    let ns : Set ℕ := { n | x n ∈ s.1 }
    have hns : ns.Nonempty := by
      obtain ⟨a, ha⟩ := s_nonempty
      have := hs ha
      obtain ⟨n, hn, rfl⟩ := this
      exact ⟨n, ha⟩
    classical
    let n₀ := Nat.find hns
    have h1 : x n₀ ∈ s.1 := Nat.find_spec hns
    let s' : parts k α := by
      refine ⟨s.1.erase (x n₀), ?_⟩
      simp [h1, s.2]
    have h2 : (s'.1 : Set _) ⊆ (F n₀).X := by
      intro a ha
      simp [s'] at ha
      obtain ⟨m, hm, rfl⟩ := hs ha.1
      have n₀_le_m : n₀ ≤ m := Nat.find_min' hns ha.1
      apply H3
      apply lt_of_le_of_ne n₀_le_m
      grind

    have := (F n₀).hC s' h2
    simp [s', x, h1] at this
    convert ← this
    change n₀ ∈ C i
    have := hs h1
    exact (Injective.mem_set_image H2).mp (hs h1)

-- PRevious special case

variable {G : SimpleGraph α}

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

-- Special case of Theorem 9.1.2 in Diestel's Graph Theory book, for `k=2`
theorem ramsey2 [Nonempty ι] [Infinite α] (φ : G.EdgeLabeling ι) :
    ∃ S : Set α, S.Infinite ∧ Monochromatic φ S := by

  let ψ (s : parts 2 α) : ι := by
    by_cases h : ∃ e ∈ G.edgeSet, e.toFinset = s.1
    · choose e he1 he2 using h
      exact φ ⟨e, he1⟩
    · exact Classical.choice inferInstance
  obtain ⟨S, hS1, i, hS2⟩ := ramsey912 ψ
  refine ⟨S, hS1, i, fun x hx y hy h => ?_⟩
  let s : parts 2 α := ⟨Finset.cons x {y} (by simp [h.ne]), by simp⟩
  have hs : (s.1 : Set α) ⊆ S := by grind
  specialize hS2 s hs
  let e : Sym2 α := s(x, y)
  have he1 : e ∈ G.edgeSet := by
    exact (SimpleGraph.mem_edgeSet G).mpr h
  classical
  have he2 : e.toFinset = {x, y} := by ext ; simp [e]
  have : ∃ e ∈ G.edgeSet, e.toFinset = {x, y} := ⟨e, he1, he2⟩
  have he3 := Classical.choose_spec this
  simp [ψ, s, this, SimpleGraph.EdgeLabeling.get] at hS2 ⊢
  convert hS2
  ext u
  simp [← Sym2.mem_toFinset, he3] ; simp
