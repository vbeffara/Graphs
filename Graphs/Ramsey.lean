import Mathlib

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

namespace ramsey912

structure Fan (φ : parts (k+1) α → ι) where
  x : α
  X : Set α
  i : ι
  --
  hx : x ∉ X
  hX : X.Infinite
  hC (s : parts.of k α X) : φ (s.1.cons x (by grind)) = i

theorem inj {x : ℕ → α} {X : ℕ → Set α} (h : ∀ n, x n ∉ X n) (H3 : ∀ {m n}, m < n → x n ∈ X m) :
    Injective x :=
  injective_of_lt_imp_ne (by grind)

end ramsey912

open ramsey912

theorem ramsey912 [Infinite α] (φ : parts k α → ι) : ∃ S : Set α, S.Infinite ∧ Monochromatic φ S := by
  induction k generalizing α with
  | zero =>
    refine ⟨univ, infinite_univ, φ ⟨∅, rfl⟩, ?_⟩
    simp only [parts.of, parts, Subtype.forall, card_eq_zero] ; grind
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

    have next (F : Fan φ) : ∃ G : Fan φ, G.x ∈ F.X ∧ G.X ⊂ F.X := by
      obtain ⟨y, hy⟩ := F.hX.nonempty
      have hXy : (F.X \ {y}).Infinite := Infinite.diff F.hX $ finite_singleton y
      obtain ⟨Y, hY1, hY2, C, hY3⟩ := key hXy y (by grind)
      refine ⟨⟨y, Y, C, by grind, hY2, hY3⟩, hy, by grind⟩
    choose Φ hΦ₁ hΦ₂ using next

    let x₀ := choice $ Infinite.nonempty α
    have : (univ \ {x₀}).Infinite := Infinite.diff infinite_univ (finite_singleton _)
    obtain ⟨X₀, hX₀, hX₀', i₀, h₀⟩ := key this x₀ (by grind)
    let F₀ : Fan φ := ⟨x₀, X₀, i₀, by grind, hX₀', h₀⟩

    let F (n : ℕ) := Φ^[n] F₀
    let X (n : ℕ) := (F n).X
    let x (n : ℕ) := (F n).x

    have X_anti : Antitone X := by
      refine antitone_nat_of_succ_le (fun n => le_of_lt ?_)
      convert hΦ₂ (F n) ; apply Function.iterate_succ_apply'
    have x_mem_X {m n : ℕ} (hmn : m < n) : x n ∈ X m := by
      obtain _ | n := n ; contradiction
      apply X_anti (Nat.le_of_lt_succ hmn)
      simpa [x, F, -Function.iterate_succ, Function.iterate_succ'] using hΦ₁ _
    have x_injective : x.Injective := inj (fun n => (F n).hx) x_mem_X

    obtain ⟨i, hi⟩ : ∃ i, Set.Infinite { n | (F n).i = i } := by
      simp only [← infinite_coe_iff, coe_setOf]
      exact Finite.exists_infinite_fiber _
    refine ⟨x '' { n | (F n).i = i }, hi.image x_injective.injOn, i, fun s => ?_⟩

    let ns : Set ℕ := x ⁻¹' s.1.1
    have ns_nonempty : ns.Nonempty := by
      obtain ⟨a, ha⟩ : s.1.1.Nonempty := by simp [← Finset.card_pos, s.1.2]
      obtain ⟨n, hn, rfl⟩ := s.2 ha
      exact ⟨n, ha⟩
    let n₀ := Nat.find ns_nonempty
    have h1 : x n₀ ∈ s.1.1 := Nat.find_spec ns_nonempty
    let s' : parts.of k α (X n₀) := by
      refine ⟨⟨s.1.1.erase (x n₀), by simp [h1, s.1.2]⟩, fun a ha => ?_⟩
      simp at ha
      obtain ⟨m, hm, rfl⟩ := s.2 ha.1
      exact x_mem_X $ lt_of_le_of_ne (Nat.find_min' ns_nonempty ha.1) (by grind)
    have : (F n₀).i = i := (Injective.mem_set_image x_injective).mp (s.2 h1)
    simpa [s', parts.cons, x, h1, this] using (F n₀).hC s'

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

-- This got some input from Aristotle.
noncomputable def FinsetEquivSym2 : {s : Finset α // s.card = 2} ≃ {z : Sym2 α // ¬z.IsDiag} where
  toFun s := ⟨(Sym2.equivMultiset α).symm ⟨s.1.val, s.2⟩,
    by rcases s with ⟨s, hs⟩; rw [Finset.card_eq_two] at hs; aesop⟩
  invFun z := ⟨z.1.toFinset, Sym2.card_toFinset_of_not_isDiag _ z.2⟩
  left_inv s := by
    obtain ⟨s, hs⟩ := s
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
    ext a ; simp ; erw [Sym2.mem_iff] ; simp [List.insert, hxy]
  right_inv s := by
    obtain ⟨⟨a, b⟩, hs⟩ := s
    obtain rfl | h := eq_or_ne a b ; contradiction
    have : s(a, b).toFinset = {a, b} := by { ext; simp_all }
    simp_all ; rfl

theorem ramsey2 [Nonempty ι] [Infinite α] (φ : G.EdgeLabeling ι) :
    ∃ S : Set α, S.Infinite ∧ φ.isMonochromatic S := by
  let ψ (s : parts 2 α) : ι := if h : (FinsetEquivSym2 s).1 ∈ G.edgeSet then φ ⟨_, h⟩
    else Classical.choice inferInstance
  obtain ⟨S, hS1, i, hS2⟩ := ramsey912 ψ
  refine ⟨S, hS1, i, fun x hx y hy h => ?_⟩
  let s : parts.of 2 α S := ⟨FinsetEquivSym2.symm ⟨s(x, y), by aesop⟩,
    by { simp [FinsetEquivSym2, Sym2.toFinset_mk_eq]; grind }⟩
  simpa [ψ, s, G.mem_edgeSet.mpr h] using hS2 s

end SimpleGraph
