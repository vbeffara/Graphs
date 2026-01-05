-- import Mathlib
import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.BourbakiWitt

open Set Function Finset Classical

variable {α ι : Type*} [Finite ι] {k : ℕ}

def parts (k : ℕ) (α : Type*) := { s : Finset α // s.card = k }

namespace parts

def cons (s : parts k α) (x : α) (hx : x ∉ s.1) : parts (k+1) α :=
  ⟨s.1.cons x hx, by simp only [card_cons, s.2]⟩

def of (k : ℕ) (α : Type*) (S : Set α) := { s : parts k α // (s.1 : Set α) ⊆ S }

end parts

def Monochromatic (φ : parts k α → ι) (S : Set α) : Prop :=
  ∃ i : ι, ∀ s : parts.of k α S, φ s.1 = i

structure Fan' (φ : parts (k+1) α → ι) where
  x : α
  X : Set α
  i : ι
  --
  hx : x ∉ X
  hX : X.Infinite
  hC : ∀ (s : parts.of k α X), φ ⟨s.1.1.cons x (by grind), by simp only [card_cons, s.1.2]⟩ = i

theorem ramsey912 [Infinite α] (φ : parts k α → ι) : ∃ S : Set α, S.Infinite ∧ Monochromatic φ S := by
  induction k generalizing α with
  | zero =>
    refine ⟨univ, infinite_univ, φ ⟨∅, rfl⟩, ?_⟩
    simp [parts, parts.of] ; grind
  | succ k ih =>
    have key {X : Set α} (hX : X.Infinite) (x : α) (hxX : x ∉ X) : ∃ (Y : Set α) (hY : Y ⊆ X),
        Y.Infinite ∧ ∃ C : ι, ∀ u : parts.of k α Y, φ (u.1.cons x (by grind)) = C := by

      let ψ (s : parts k X) : ι :=
        let s' : parts k α := ⟨Finset.map (Embedding.subtype _) s.1, by simp [s.2]⟩
        φ (s'.cons x (by simp [s', hxX]))

      obtain ⟨S, h1, C, h2⟩ := @ih X hX.to_subtype ψ

      refine ⟨Embedding.subtype _ '' S, by simp, ?_, C, ?_⟩
      · exact h1.image (Embedding.subtype_injective _ |>.injOn)
      · rintro ⟨s, hs⟩
        change (s.1 : Set _) ⊆ Subtype.val '' S at hs
        have hs' : (s.1 : Set _) ⊆ X := by grind
        let ss : parts.of k X S := by
          refine ⟨⟨Finset.subtype _ s.1, ?_⟩, ?_⟩
          · simpa [← s.2, Finset.card_filter_eq_iff] using hs'
          · intro a ha
            simp only [SetLike.mem_coe, mem_subtype] at ha
            grind [hs ha]
        specialize h2 ss
        simp [parts.cons, ψ, ss] at h2 ⊢
        convert h2 ; grind

    have next (F : Fan' φ) : ∃ G : Fan' φ, G.x ∈ F.X ∧ G.X ⊂ F.X := by
      obtain ⟨y, hy⟩ := F.hX.nonempty
      have hXy : (F.X \ {y}).Infinite := Infinite.diff F.hX $ finite_singleton y
      obtain ⟨Y, hY1, hY2, C, hY3⟩ := key hXy y (by grind)
      refine ⟨⟨y, Y, C, by grind, hY2, hY3⟩, hy, by grind⟩
    choose Φ hΦ₁ hΦ₂ using next

    let x₀ := Classical.choice $ Infinite.nonempty α

    have : (univ \ {x₀}).Infinite := Infinite.diff infinite_univ (finite_singleton _)
    obtain ⟨X₀, hX₀, hX₀', i₀, h₀⟩ := key this x₀ (by grind)
    let F₀ : Fan' φ := ⟨x₀, X₀, i₀, by grind, hX₀', h₀⟩

    let F (n : ℕ) : Fan' φ := Φ^[n] F₀
    let C (i : ι) : Set ℕ := { n | (F n).i = i }
    let X (n : ℕ) : Set α := (F n).X
    let x (n : ℕ) : α := (F n).x

    obtain ⟨i, hi⟩ : ∃ i : ι, (C i).Infinite := by
      simp [C, ← infinite_coe_iff]
      exact Finite.exists_infinite_fiber _

    have H1 : StrictAnti X := by
      refine strictAnti_nat_of_succ_lt (fun n => ?_)
      simpa [X, F, -Function.iterate_succ, Function.iterate_succ'] using hΦ₂ _

    have H3 ⦃m n : ℕ⦄ (hmn : m < n) : x n ∈ X m := by
      cases n with
      | zero => contradiction
      | succ n =>
        simp [x, F, -Function.iterate_succ, Function.iterate_succ']
        exact H1.antitone (Nat.le_of_lt_succ hmn) (hΦ₁ _)

    have H2 : Function.Injective x := by
      apply injective_of_lt_imp_ne
      intro m n h₁
      have := (F m).hx
      contrapose this
      simpa only [← this] using H3 h₁

    refine ⟨x '' C i, hi.image H2.injOn, i, ?_⟩

    rintro ⟨s, hs⟩
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
    let s' : parts.of k α (X n₀) := by
      refine ⟨⟨s.1.erase (x n₀), by simp [h1, s.2]⟩, ?_⟩
      intro a ha
      simp at ha
      obtain ⟨m, hm, rfl⟩ := hs ha.1
      apply H3
      apply lt_of_le_of_ne (Nat.find_min' hns ha.1)
      grind

    have : φ s = (F n₀).i := by simpa [s', x, h1] using (F n₀).hC s'
    convert ← this
    exact (Injective.mem_set_image H2).mp (hs h1)

namespace SimpleGraph

variable {G : SimpleGraph α}

structure Fan (φ : G.EdgeLabeling ι) where
  x : α
  X : Set α
  i : ι
  --
  hx : x ∉ X
  hX : X.Infinite
  hC : ∀ u ∈ X, ∀ h : G.Adj x u, φ.get x u h = i

def EdgeLabeling.isMonochromatic (φ : G.EdgeLabeling ι) (S : Set α) : Prop :=
  ∃ i : ι, ∀ u ∈ S, ∀ v ∈ S, ∀ h : G.Adj u v, φ.get u v h = i

-- Graph version, obtained as a special case of Theorem 9.1.2 in Diestel's Graph
-- Theory book, for `k=2`
theorem ramsey2 [Nonempty ι] [Infinite α] (φ : G.EdgeLabeling ι) :
    ∃ S : Set α, S.Infinite ∧ φ.isMonochromatic S := by
  let ψ (s : parts 2 α) : ι := by
    by_cases h : ∃ e ∈ G.edgeSet, e.toFinset = s.1
    · choose e he1 he2 using h
      exact φ ⟨e, he1⟩
    · exact Classical.choice inferInstance
  obtain ⟨S, hS1, i, hS2⟩ := ramsey912 ψ
  refine ⟨S, hS1, i, fun x hx y hy h => ?_⟩
  let s : parts 2 α := ⟨cons x {y} (by simp [h.ne]), by simp only [card_cons, Finset.card_singleton] ⟩
  have hs : (s.1 : Set α) ⊆ S := by grind
  let e : Sym2 α := s(x, y)
  have he1 : e ∈ G.edgeSet := by
    exact (SimpleGraph.mem_edgeSet G).mpr h
  classical
  have he2 : ∃ e ∈ G.edgeSet, e.toFinset = {x, y} := ⟨e, he1, (by ext ; simp [e])⟩
  have he3 := Classical.choose_spec he2
  convert hS2 ⟨s, hs⟩
  simp [ψ, s, he2, SimpleGraph.EdgeLabeling.get]
  congr
  ext u
  simp [← Sym2.mem_toFinset, he3] ; simp

end SimpleGraph
