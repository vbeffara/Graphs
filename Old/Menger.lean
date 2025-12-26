import Mathlib.Tactic
import Untitled.Graphs.Contraction
import Untitled.Graphs.Map
import Untitled.Graphs.Minus
import Untitled.Graphs.Walk

set_option autoImplicit false

open Classical Function Finset

variable {V V' : Type*} [Fintype V] [Fintype V']
variable {G G₁ G₂ : SimpleGraph V}
variable {a : V} {A B X Y Z : Finset V} -- {e : G.Dart}
-- variable {f : V → V'} {hf : G.Adapted f}

namespace SimpleGraph

namespace Menger

@[ext] structure AB_Walk (G : SimpleGraph V) (A B : Finset V) :=
  (a b : V) (ha : a ∈ A) (hb : b ∈ B)
  (to_Walk : G.Walk a b)

-- variable {P : Finset (AB_Walk G A B)}

namespace AB_Walk

def Reverse (p : AB_Walk G A B) : AB_Walk G B A := ⟨p.b, p.a, p.hb, p.ha, p.to_Walk.reverse⟩

@[simp] lemma Reverse_to_Walk {p : AB_Walk G A B} : p.Reverse.to_Walk = p.to_Walk.reverse := rfl

def Disjoint (p q : AB_Walk G A B) : Prop := List.Disjoint p.to_Walk.support q.to_Walk.support

def pwd (P : Finset (AB_Walk G A B)) : Prop := P.toSet.Pairwise Disjoint

def minimal (p : AB_Walk G A B) : Prop :=
  (∀ x ∈ p.to_Walk.init₀, x ∉ B) ∧ (∀ x ∈ p.to_Walk.tail₀, x ∉ A)

lemma minimal_ext {p : AB_Walk G₁ A B} {p' : AB_Walk G₂ A B}
    (h : p.to_Walk.support = p'.to_Walk.support) : p.minimal ↔ p'.minimal := by
  simp_rw [minimal, Walk.init_eq_take_support, Walk.tail_eq_tail_support, h]

lemma tototo : A ∩ B = ∅ ↔ ∀ x ∈ A, x ∉ B where
  mp h x hA hB := by cases h ▸ Finset.mem_inter.mpr ⟨hA, hB⟩
  mpr h := by
    ext x ; constructor <;> intro h'
    · obtain ⟨h1, h2⟩ := Finset.mem_inter.mp h'
      cases h x h1 h2
    · cases h'

noncomputable def lift (f : V → V') (hf : G.Adapted f)
    (p : AB_Walk (G.map' f) (A.image f) (B.image f)) : AB_Walk G A B := by
  choose a h1 h2 using mem_image.mp p.ha
  choose b h3 h4 using mem_image.mp p.hb
  exact ⟨a, b, h1, h3, pull_Walk f hf a b <| p.to_Walk.copy h2.symm h4.symm⟩

@[simp] lemma lift_a {f : V → V'} {hf : G.Adapted f} {p : AB_Walk (G.map' f) (A.image f) (B.image f)} :
    f (lift f hf p).a = p.a :=
  Classical.choose_spec (mem_image.mp p.ha) |>.2

@[simp] lemma lift_b {f : V → V'} {hf : G.Adapted f} {p : AB_Walk (G.map' f) (A.image f) (B.image f)} :
    f (lift f hf p).b = p.b :=
  Classical.choose_spec (mem_image.mp p.hb) |>.2

noncomputable def push (f : V → V') (p : AB_Walk G A B) :
    AB_Walk (G.map' f) (A.image f) (B.image f) := by
  refine ⟨_, _, mem_image_of_mem f p.ha, mem_image_of_mem f p.hb, push_Walk f p.to_Walk⟩

@[simp] lemma push_a {f : V → V'} {p : AB_Walk G A B} : (push f p).a = f p.a := rfl

@[simp] lemma push_b {f : V → V'} {p : AB_Walk G A B} : (push f p).b = f p.b := rfl

lemma push_lift {f : V → V'} {hf : G.Adapted f} :
    LeftInverse (push f (A := A) (B := B)) (lift f hf) := by
  rintro ⟨a, b, ha, hb, p⟩
  ext <;> try simp [push, lift]
  have h1 := Classical.choose_spec (mem_image.mp ha) |>.2
  have h2 := Classical.choose_spec (mem_image.mp hb) |>.2
  have : HEq (p.copy rfl rfl) p := by rfl
  convert this

lemma lift_inj {f : V → V'} {hf : G.Adapted f} : Injective (lift f hf (A := A) (B := B)) :=
  LeftInverse.injective push_lift

noncomputable def trim_aux (p : AB_Walk G A B) :
    {q : AB_Walk G A B // q.minimal ∧ q.to_Walk.support ⊆ p.to_Walk.support} := by
--   rcases p with ⟨p₁, p₁a, p₁b⟩,
--   have h₁ : (p₁.range ∩ A).nonempty := ⟨p₁.a, by simp [p₁a]⟩,
--   rcases p₁.after A h₁ with ⟨p₂, p₂a, p₂b, p₂r, p₂i, -, p₂t⟩,
--   have h₂ : (p₂.range ∩ B).nonempty := by { refine ⟨p₂.b, _⟩, simp, rwa p₂b },
--   rcases p₂.until B h₂ with ⟨p₃, p₃a, p₃b, p₃r, p₃i, -, p₃t⟩,
--   refine ⟨⟨p₃, p₃a.symm ▸ p₂a, p₃b⟩, ⟨by simp [p₃i], _⟩, p₃r.trans p₂r⟩,
--   have : p₃.tail ∩ A ⊆ p₂.tail ∩ A := inter_subset_inter_right p₃t,
--   rw ←subset_empty, apply this.trans, rw p₂t, refl
  sorry

noncomputable def trim (p : AB_Walk G A B) : AB_Walk G A B := p.trim_aux.val

lemma trim_minimal {p : AB_Walk G A B} : p.trim.minimal := p.trim_aux.prop.1

lemma trim_range {p : AB_Walk G A B} : p.trim.to_Walk.support ⊆ p.to_Walk.support :=
  p.trim_aux.prop.2

noncomputable def massage_aux (h : G₂ ≤ G₁) (p : AB_Walk G₂ A X) :
    {q : AB_Walk G₁ A X // q.minimal ∧ q.to_Walk.support ⊆ p.to_Walk.support} := by
  obtain ⟨q, hq⟩ := p.trim.to_Walk.transport (Walk.transportable_to_of_le h)
  set q' : AB_Walk G₁ A X := ⟨_, _, p.trim.ha, p.trim.hb, q⟩
  refine ⟨q', ?_, ?_⟩
  · have : q = q'.to_Walk := rfl ; rw [this] at hq
    simpa [minimal_ext hq] using trim_minimal
  · simpa [hq] using trim_range

noncomputable def massage (h : G₂ ≤ G₁) (p : AB_Walk G₂ A X) : AB_Walk G₁ A X :=
  (p.massage_aux h).val

end AB_Walk

open AB_Walk

lemma le_A {P : Finset (AB_Walk G A B)} (dis : pwd P) : P.card ≤ A.card := by
  let φ (p : P) : A := ⟨p.val.a, p.val.ha⟩
  have : Injective φ := by
    rintro p₁ p₂ h
    by_contra h'
    have h'' : p₁.val ≠ p₂.val := by simpa [← Subtype.ext_iff]
    have h1 : p₁.val.a ∈ p₁.val.to_Walk.support := Walk.start_mem_support _
    have h2 : p₁.val.a ∈ p₂.val.to_Walk.support := by
      simp at h ; rw [h]
      exact Walk.start_mem_support _
    exact dis p₁.prop p₂.prop h'' h1 h2
  simp_rw [← Fintype.card_coe]
  exact Fintype.card_le_of_injective φ this

lemma le_B {P : Finset (AB_Walk G A B)} (dis : pwd P) : P.card ≤ B.card := by
  let φ (p : P) : B := ⟨p.val.b, p.val.hb⟩
  have : Injective φ := by
    rintro p₁ p₂ h
    by_contra h'
    have h'' : p₁.val ≠ p₂.val := by simpa [← Subtype.ext_iff]
    have h1 : p₁.val.b ∈ p₁.val.to_Walk.support := Walk.end_mem_support _
    have h2 : p₁.val.b ∈ p₂.val.to_Walk.support := by
      simp at h ; rw [h]
      exact Walk.end_mem_support _
    exact dis p₁.prop p₂.prop h'' h1 h2
  simp_rw [← Fintype.card_coe]
  exact Fintype.card_le_of_injective φ this

def Separates (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ γ : AB_Walk G A B, ∃ x ∈ X, x ∈ γ.to_Walk.support

namespace Separates

lemma self : Separates G A B A := λ γ => ⟨γ.a, γ.ha, γ.to_Walk.start_mem_support⟩

lemma symm (h : Separates G A B X) : Separates G B A X := λ p => by simpa using h p.Reverse

lemma inter_subset (h : Separates G A B X) : A ∩ B ⊆ X := by
  intro x h1
  rw [mem_inter] at h1
  simpa using h ⟨x, x, h1.1, h1.2, Walk.nil⟩

end Separates

def Separator (G : SimpleGraph V) (A B : Finset V) := {P : Finset V // Separates G A B P}

namespace Separator

def card (X : Separator G A B) : ℕ := X.val.card

instance : Nonempty (Separator G A B) := ⟨⟨A, Separates.self⟩⟩

def symm : Separator G A B → Separator G B A := λ ⟨X, sep⟩ => ⟨X, sep.symm⟩

@[simp] lemma card_symm {X : Separator G A B} : X.symm.card = X.card := by
  cases X
  simp [symm, card]

-- def comm : separator G A B ≃ separator G B A :=
-- { to_fun := symm,
--   inv_fun := symm,
--   left_inv := λ ⟨X,sep⟩, by simp only [symm],
--   right_inv := λ ⟨X,sep⟩, by simp only [symm] }

end Separator

def is_cut_set_size (G : SimpleGraph V) (A B : Finset V) (n : ℕ) : Prop :=
  ∃ X : Separator G A B, X.card = n

noncomputable def min_cut (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  @Nat.find (is_cut_set_size G A B) _ ⟨A.card, ⟨A, Separates.self⟩, rfl⟩

namespace min_cut

lemma symm : min_cut G A B = min_cut G B A := by
  simp_rw [min_cut]
  congr 1
  ext n
  constructor <;> exact λ ⟨X, h⟩ => ⟨X.symm, by simp [h]⟩

lemma spec : is_cut_set_size G A B (min_cut G A B) := Nat.find_spec _

noncomputable def set (G : SimpleGraph V) (A B : Finset V) :
    {X : Separator G A B // X.card = min_cut G A B} :=
  subtype_of_exists (spec)

-- lemma le {X : separator G A B} : min_cut G A B ≤ X.card :=
-- nat.find_le ⟨X, rfl⟩

lemma le' (sep : Separates G A B X) : min_cut G A B ≤ X.card := Nat.find_le ⟨⟨X,sep⟩, rfl⟩

lemma inter_le_min_cut : (A ∩ B).card ≤ min_cut G A B := by
  rw [min_cut, Nat.le_find_iff]
  rintro n hn ⟨⟨X, h⟩, h'⟩
  simp only [Separator.card] at h'
  linarith [card_le_card h.inter_subset]

end min_cut

def isMenger (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ A B : Finset V, ∃ P : Finset (AB_Walk G A B), pwd P ∧ P.card = min_cut G A B

lemma path_le_cut {P : Finset (AB_Walk G A B)} (dis : pwd P) (sep : Separates G A B X) :
    P.card ≤ X.card := sorry
-- begin
--   let φ : Π γ : P, γ.val.to_Walk.range ∩ X := λ γ, by { choose z hz using sep γ, exact ⟨z,hz⟩ },
--   let ψ : P → X := λ γ, ⟨_, mem_of_mem_inter_right (φ γ).prop⟩,
--   have h₁ : ∀ γ, (ψ γ).val ∈ γ.val.to_Walk.range := λ γ, let z := φ γ in (mem_inter.mp z.2).1,
--   have h₂ : injective ψ := λ γ γ' h, dis ⟨_, mem_inter_of_mem (h₁ γ) (by { rw h, exact (h₁ γ') })⟩,
--   simp_rw [←Fintype.card_coe], convert Fintype.card_le_of_injective ψ h₂
-- end

lemma upper_bound {P : Finset (AB_Walk G A B)} (dis : pwd P) : P.card ≤ min_cut G A B := by
  obtain ⟨⟨X, h₁⟩, h₂⟩ := min_cut.set G A B
  simpa [← h₂] using path_le_cut dis h₁

lemma bot_iff_no_edge : Fintype.card G.Dart = 0 ↔ G = ⊥ where
  mp h := by
    ext x y ; simp ; exact λ h' => isEmpty_iff.mp (Fintype.card_eq_zero_iff.mp h) ⟨⟨x, y⟩, h'⟩
  mpr h := by simpa only [h] using Fintype.card_eq_zero_iff.mpr <| isEmpty_iff.mpr Dart.is_adj

lemma bot_Separates_iff : Separates ⊥ A B X ↔ (A ∩ B) ⊆ X where
  mp := Separates.inter_subset
  mpr := λ h ⟨a, b, ha, hb, p⟩ => by cases p with
    | nil => exact ⟨a, by simpa using h <| mem_inter_of_mem ha hb⟩
    | cons h' _ => cases h'

lemma bot_min_cut : min_cut ⊥ A B = (A ∩ B).card := by
  refine le_antisymm ?_ min_cut.inter_le_min_cut
  rw [min_cut, Nat.find_le_iff]
  refine ⟨(A ∩ B).card, le_rfl, ?_⟩
  simpa only [is_cut_set_size] using ⟨⟨A ∩ B, bot_Separates_iff.mpr le_rfl⟩, rfl⟩

@[simp] lemma isMenger_bot : isMenger (⊥ : SimpleGraph V) := by
  rintro A B
  rw [bot_min_cut]
  let φ (z : (A ∩ B : Finset V)) : AB_Walk ⊥ A B :=
    let h := mem_inter.mp z.prop ; ⟨z, z, h.1, h.2, Walk.nil⟩
  have φ_inj : Injective φ := by intro u v h ; ext ; simp [φ] at h ; exact h.1
  refine ⟨image φ univ, ?_, by simp [card_image_of_injective, φ_inj]⟩
  rintro ⟨a, b, _, _, p⟩ hp ⟨a', b', _, _, q⟩ hq h
  simp at hp hq h
  rcases hp with ⟨rfl, -, h4⟩
  rcases hq with ⟨rfl, -, h8⟩
  subst_vars
  simp [AB_Walk.Disjoint]
  rintro rfl
  simp at h

lemma AB_lift_dis {f : V → V'} {hf : G.Adapted f}
  (P' : Finset (AB_Walk (map' f G) (A.image f) (B.image f))) :
  pwd P' → pwd (P'.image (AB_Walk.lift f hf)) := sorry
-- begin
--   rintro hP' ⟨γ₁,h₁⟩ ⟨γ₂,h₂⟩ h, simp at h ⊢, choose z h using h,
--   choose γ'₁ h'₁ h''₁ using mem_image.mp h₁,
--   choose γ'₂ h'₂ h''₂ using mem_image.mp h₂,
--   have h₃ := congr_arg (AB_Walk.push f A B) h''₁, rw AB_Walk.push_lift at h₃,
--   have h₄ := congr_arg (AB_Walk.push f A B) h''₂, rw AB_Walk.push_lift at h₄,
--   suffices : γ'₁ = γ'₂, { rw [←h''₁,←h''₂,this] },
--   have := @hP' ⟨_,h'₁⟩ ⟨_,h'₂⟩, simp at this, apply this,
--   simp [h₃,h₄,AB_Walk.push,Walk.push_range], use f z, rw mem_inter at h ⊢, split,
--   exact mem_image_of_mem f h.1, exact mem_image_of_mem f h.2
-- end

lemma transportable_of_not_dart {e : G.Dart} {a b : V} {p : G.Walk a b} (h : e ∉ p.darts)
    (h' : e.symm ∉ p.darts) : Walk.transportable_to (G -ₑ e.edge) p := by
  intro f hf
  simp [Minus, f.is_adj, Dart.edge]
  intro hef
  cases hef with
  | inl h1 => exact h <| Dart.ext _ _ h1 ▸ hf
  | inr h2 => rw [← Dart.symm_toProd] at h2 ; exact h' <| Dart.ext _ _ h2 ▸ hf

lemma sep_AB_of_sep₂_AX ⦃e : G.Dart⦄ (ex_in_X : e.fst ∈ X) (ey_in_X : e.snd ∈ X)
    (X_sep_AB : Separates G A B X) (Z_sep₂_AX : Separates (G -ₑ e.edge) A X Z) : Separates G A B Z := by
  intro γ
  obtain ⟨x, hx1, hx2⟩ := X_sep_AB γ
  let δ := takeUntil γ.to_Walk (· ∈ X) ⟨x, hx2, hx1⟩
  have key : Walk.transportable_to (G -ₑ e.edge) δ := by
    apply transportable_of_not_dart
    · sorry
    · sorry
    -- apply transportable_of_not_dart
    -- sorry
    -- sorry
--     revert δ_init, refine Walk.rec₀ _ _ δ,
--     { simp [Walk.transportable_to,Walk.edges] },
--     { rintro e' p h ih h₁ e'' h₂,
--       have h₃ : p.init ∩ X = ∅ :=
--       by { apply subset_empty.mp, rw [←h₁], apply inter_subset_inter_right,
--         rw [Walk.init_cons], apply subset_union_right },
--       simp at h₂, cases h₂,
--       { subst e'', simp at h₁, simp [minus,e'.is_Adj],
--         have : e'.fst ∉ X :=
--         by { rw [inter_distrib_right, union_eq_empty_iff] at h₁, intro h,
--           apply not_nonempty_empty, rw ←h₁.1,
--           exact ⟨e'.fst, by simp only [h, singleton_inter_of_mem, mem_singleton]⟩ },
--         intro h', apply this, rw [Dart.edge,sym2.mk_eq_mk_iff] at h',
--         cases h'; { rw h', assumption } },
--       { exact ih h₃ e'' h₂ }
  obtain ⟨ζ, hζ⟩ := δ.transport key
  let ζ' : AB_Walk (G -ₑ e.edge) A X := ⟨_, _, γ.ha, entrance_prop (P := (· ∈ X)), ζ⟩
  obtain ⟨z, hz1, hz2⟩ := Z_sep₂_AX ζ'
  simp [hζ] at hz2
  have := ((takeUntil_aux γ.to_Walk (· ∈ X) ⟨x, hx2, hx1⟩).2.2.1).subset
  refine ⟨z, hz1, this hz2⟩

lemma massage_eq (hG : G₂ ≤ G₁) {P : Finset (AB_Walk G₂ A B)} {p₁ p₂ : P} (hP : pwd P)
    (h : ∃ z ∈ (p₁.val.massage hG).to_Walk.support, z ∈ (p₂.val.massage hG).to_Walk.support) :
    p₁ = p₂ := by
  by_contra hp
  obtain ⟨z, hz₁, hz₂⟩ := h
  have h1 := (p₁.val.massage_aux hG).prop.2 hz₁
  have h2 := (p₂.val.massage_aux hG).prop.2 hz₂
  have h3 : p₁.1 ≠ p₂.1 := by contrapose! hp ; ext <;> rw [hp]
  exact hP p₁.prop p₂.prop h3 h1 h2

lemma massage_disjoint {h : G₂ ≤ G₁} {P : Finset (AB_Walk G₂ A B)} (h₁ : pwd P) :
    pwd (image (AB_Walk.massage h) P) := by
  rintro p₁ hp₁ p₂ hp₂ hp₁p₂ z hz₁ hz₂
  apply hp₁p₂
  choose q₁ hq₁ hq₁' using mem_image.mp hp₁
  choose q₂ hq₂ hq₂' using mem_image.mp hp₂
  subst_vars
  let γ₁ : P := ⟨q₁, hq₁⟩
  let γ₂ : P := ⟨q₂, hq₂⟩
  congr
  suffices γ₁ = γ₂ by simpa using this
  exact massage_eq h h₁ ⟨z, hz₁, hz₂⟩

lemma massage_card {h : G₂ ≤ G₁} {P : Finset (AB_Walk G₂ A B)} (hP : pwd P) :
    (image (AB_Walk.massage h) P).card = P.card := by
  apply Finset.card_image_of_injOn
  rintro p₁ hp₁ p₂ hp₂ he
  let q₁ : P := ⟨p₁, hp₁⟩
  let q₂ : P := ⟨p₂, hp₂⟩
  suffices q₁ = q₂ by simpa using this
  apply massage_eq h hP
  use (massage h p₂).a
  rw [he]
  simp

lemma meet_sub_X (X_sep_AB : Separates G A B X) (p : AB_Walk G A X) (q : AB_Walk G B X)
    (hp : p.minimal) (hq : q.minimal) :
    ∀ x, x ∈ p.to_Walk.support → x ∈ q.to_Walk.support → x ∈ X := by
  obtain ⟨ap, bp, pa, pb, p⟩ := p
  obtain ⟨aq, bq, qa, qb, q⟩ := q
  intro x hx₁ hx₂
  dsimp at hx₁ hx₂
  by_contra

  obtain ⟨⟨x, rfl⟩, p', hp1, _⟩ := takeUntil_aux p (· = x) ⟨x, hx₁, rfl⟩
  have h1 : ∀ y ∈ p'.support, y ∉ X := by
    intro y hy
    simp [Walk.support_eq_init₀_union_last] at hy
    cases hy with
    | inl h => exact hp.1 y <| Walk.init₀_subset_of_support_prefix hp1 h
    | inr h => rwa [h]

  obtain ⟨⟨x, rfl⟩, q', hq1, _⟩ := takeUntil_aux q (· = x) ⟨x, hx₂, rfl⟩
  have h2 : ∀ y ∈ q'.support, y ∉ X := by
    intro y hy
    simp [Walk.support_eq_init₀_union_last] at hy
    cases hy with
    | inl h => exact hq.1 y <| Walk.init₀_subset_of_support_prefix hq1 h
    | inr h => rwa [h]

  choose z hz hz' using X_sep_AB ⟨_, _, pa, qa, p'.append q'.reverse⟩
  simp at hz'
  cases hz' with
  | inl h => cases h1 _ h hz
  | inr h => cases h2 _ h hz

noncomputable def endpoint (P : Finset (AB_Walk G A B)) (P_dis : pwd P) (P_eq : P.card = B.card) :
    P ≃ B := by
  refine Equiv.ofBijective (λ p => ⟨p.val.b, p.val.hb⟩) ?_
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by simp [P_eq]⟩
  intro p₁ p₂ h
  simp at h
  ext1
  have := P_dis p₁.prop p₂.prop
  contrapose! this
  simp [this, AB_Walk.Disjoint, List.Disjoint]
  use p₁.val.b
  simp
  simp [h]

noncomputable def sep_cleanup {e : G.Dart} (ex_in_X : e.fst ∈ X) (ey_in_X : e.snd ∈ X)
    (X_eq_min : X.card = min_cut G A B) (X_sep_AB : Separates G A B X)
    (ih : ∃ (P : Finset (AB_Walk (G -ₑ e.edge) A X)), pwd P ∧ P.card = min_cut (G -ₑ e.edge) A X) :
    {P : Finset (AB_Walk G A X) // pwd P ∧ P.card = X.card ∧ ∀ p : P, p.val.minimal} := by
  choose P h₁ h₂ using ih
  use image (AB_Walk.massage Minus_le) P
  refine ⟨?_, ?_, ?_⟩
  · exact massage_disjoint h₁
  · rw [massage_card h₁]
    apply le_antisymm (le_B h₁)
    rcases min_cut.set (G -ₑ e.edge) A X with ⟨⟨Z, Z_sep₂_AB⟩, Z_eq_min⟩
    rw [X_eq_min, h₂, ← Z_eq_min]
    apply min_cut.le'
    exact sep_AB_of_sep₂_AX ex_in_X ey_in_X X_sep_AB Z_sep₂_AB
  · intro p
    choose p' _ hp'₂ using mem_image.mp p.prop
    have := (p'.massage_aux Minus_le).prop.1
    simp [AB_Walk.massage] at hp'₂
    rwa [hp'₂] at this

noncomputable def stitch (X_sep_AB : Separates G A B X)
    (P : Finset (AB_Walk G A X)) (P_dis: pwd P) (P_eq_X: P.card = X.card)
    (Q : Finset (AB_Walk G B X)) (Q_dis: pwd Q) (Q_eq_X: Q.card = X.card)
    (hP : ∀ p : P, p.val.minimal) (hQ : ∀ q : Q, q.val.minimal) :
    {R : Finset (AB_Walk G A B) // pwd R ∧ R.card = X.card} := by
  let φ : X ≃ P := (endpoint P P_dis P_eq_X).symm
  let ψ : X ≃ Q := (endpoint Q Q_dis Q_eq_X).symm
  have φxb (x : X) : (φ x).val.b = x.val := by
    set γ := φ x
    have : x = φ.symm (φ x) := by simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
    rw [this]
    rfl
  have ψxb (x : X) : (ψ x).val.b = x.val := by
    set γ := ψ x
    have : x = ψ.symm γ := by simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
    rw [this]
    rfl
  let Ψ (x : X) : AB_Walk G A B := ⟨_, _, (φ x).val.ha, (ψ x).val.ha,
    Walk.append ((φ x).1.to_Walk.copy rfl (φxb x)) ((ψ x).1.to_Walk.copy rfl (ψxb x)).reverse⟩
  have bla {x y : X} (h : y.val ∈ (Ψ x).to_Walk.support) : y = x := by
    simp at h; simp [Walk.support_eq_init₀_union_last] at h
    cases h with
    | inl h => cases h with
      | inl h => cases (hP (φ x)).1 y h y.prop
      | inr h => ext1 ; simpa [← φxb x]
    | inr h => cases h with
      | inl h => cases (hQ (ψ x)).1 y h y.prop
      | inr h => ext1 ; simpa [← ψxb x]
  have Ψ_inj : Injective Ψ := by
    intro x y h
    apply bla
    rw [← h]
    simp
    left
    rw [← φxb]
    apply Walk.end_mem_support
  have ll (x y z) (hz1 : z ∈ (φ x).val.to_Walk.support) (hz2 : z ∈ (ψ y).val.to_Walk.support) : x = y := by
    have z_in_X : z ∈ X := meet_sub_X X_sep_AB (φ x) (ψ y) (hP (φ x)) (hQ (ψ y)) z hz1 hz2
    have z_is_x : z = x := by
      have := (hP (φ x))
      simp [minimal] at this
      simp [Walk.support_eq_init₀_union_last] at hz1
      cases hz1 with
      | inl h => cases this.1 z h z_in_X
      | inr h => simpa [φxb x] using h
    have z_is_y : z = y := by
      have := (hQ (ψ y))
      simp [minimal] at this
      simp [Walk.support_eq_init₀_union_last] at hz2
      cases hz2 with
      | inl h => cases this.1 z h z_in_X
      | inr h => simpa [ψxb y] using h
    subst_vars ; ext1 ; assumption
  have R_dis : pwd (image Ψ univ) := by
    rintro γ₁ hγ₁ γ₂ hγ₂ h_dis
    obtain ⟨x, -, hx⟩ := mem_image.mp hγ₁ ; subst hx
    obtain ⟨y, -, hy⟩ := mem_image.mp hγ₂ ; subst hy
    contrapose! h_dis
    congr
    simp [AB_Walk.Disjoint, List.Disjoint] at h_dis
    obtain ⟨a, ha₁, ha₂⟩ := h_dis
    cases ha₁ with
    | inl h => cases ha₂ with
      | inl h' =>
        specialize P_dis (φ x).prop (φ y).prop
        rw [not_imp_comm, AB_Walk.Disjoint, List.Disjoint] at P_dis
        simp at P_dis
        apply φ.left_inv.injective
        ext1
        exact P_dis a h h'
      | inr h' =>
        simp at h'
        exact ll x y a h h'
    | inr h => cases ha₂ with
      | inl h' => exact (ll y x a h' h).symm
      | inr h' =>
        specialize Q_dis (ψ x).prop (ψ y).prop
        rw [not_imp_comm, AB_Walk.Disjoint, List.Disjoint] at Q_dis
        simp at Q_dis
        apply ψ.left_inv.injective
        ext1
        exact Q_dis a h h'
  refine ⟨_, R_dis, ?_⟩
  rw [card_image_of_injective _ Ψ_inj]
  exact Fintype.card_coe X

lemma sep_of_sep_in_merge {e}
    (Y_sep : Separates (G /ₑ e) (image (merge_edge e) A) (image (merge_edge e) B) Y) :
    Separates G A B (Y ∪ {e.snd}) := by
  rintro γ
  obtain ⟨z, hz1, hz2⟩ := Y_sep (γ.push (merge_edge e))
  simp [mem_inter, push] at hz2
  have := support_push_Walk hz2
  simp at this
  obtain ⟨x, hx₁, hx₂⟩ := this
  use x
  by_cases h : x = e.snd <;> simp [merge_edge, update, h] at hx₂ <;> subst_vars <;> simp [hx₁, hz1]

lemma step_1 {e} (h_contract : isMenger (G /ₑ e))
    (too_small : ∀ P : Finset (AB_Walk G A B), pwd P → P.card < min_cut G A B) :
    ∃ X : Finset V, e.fst ∈ X ∧ e.snd ∈ X ∧ Separates G A B X ∧ X.card = min_cut G A B := by
  let A₁ := image (merge_edge e) A
  let B₁ := image (merge_edge e) B
  obtain ⟨Y, Y_eq_min₁⟩ := min_cut.set (G /ₑ e) A₁ B₁
  let X := Y.val ∪ {e.snd}

  have Y_lt_min : Y.card < min_cut G A B := by
    obtain ⟨P₁, P₁_dis, P₁_eq_min₁⟩ := h_contract A₁ B₁
    rw [Y_eq_min₁, ← P₁_eq_min₁]
    rw [← card_image_of_injective P₁ AB_Walk.lift_inj]
    · apply too_small
      apply AB_lift_dis
      exact P₁_dis
    · exact merge_edge_adapted

  have X_sep_AB : Separates G A B X := sep_of_sep_in_merge Y.prop
  refine ⟨X, ?_, ?_, X_sep_AB, ?_⟩
  · rw [mem_union]
    left
    by_contra
    suffices Separates G A B Y.val from not_lt_of_le (min_cut.le' this) Y_lt_min
    intro p
    obtain ⟨z, hz1, hz2⟩ := Y.prop (p.push <| merge_edge e)
    refine ⟨z, hz1, ?_⟩
    simp [push, push_Walk] at hz2
    have := support_push_Walk hz2
    simp at this
    obtain ⟨a, ha1, ha2⟩ := this
    by_cases h : a = e.snd <;> simp [merge_edge, update, h] at ha2 <;> subst_vars
    · contradiction
    · assumption
  · simp [mem_union, mem_singleton]
  · refine le_antisymm ?_ (min_cut.le' X_sep_AB)
    exact (card_union_le _ _).trans (Nat.succ_le_of_lt Y_lt_min)

lemma induction_step (e : G.Dart) : isMenger (G /ₑ e) → isMenger (G -ₑ e.edge) → isMenger G := by
  intro h_contract h_minus A B
  apply not_imp_self.mp
  intro too_small
  push_neg at too_small
  replace too_small : ∀ P : Finset (AB_Walk G A B), pwd P → P.card < min_cut G A B
  · exact λ P h => lt_of_le_of_ne (upper_bound h) (too_small P h)
  obtain ⟨X, ex_in_X, ey_in_X, X_sep_AB, X_eq_min⟩ := step_1 h_contract too_small
  obtain ⟨P, hP⟩ := sep_cleanup ex_in_X ey_in_X X_eq_min X_sep_AB (h_minus A X)
  have X_eq_min' : X.card = min_cut G B A := X_eq_min.trans min_cut.symm
  obtain ⟨Q, hQ⟩ := sep_cleanup ex_in_X ey_in_X X_eq_min' X_sep_AB.symm (h_minus B X)
  rw [← X_eq_min]
  apply Subtype.exists_of_subtype
  exact stitch X_sep_AB P hP.1 hP.2.1 Q hQ.1 hQ.2.1 hP.2.2 hQ.2.2

theorem bla {α : Type*} (f : α → ℕ) {motive : α → Prop}
    (h1 : ∀ a, (∀ b, f b < f a → motive b) → motive a) {a} : motive a :=
  Nat.strongInductionOn (motive := fun x ↦ ∀ {a}, f a = x → motive a) (f a)
    (fun _ ih {a} h ↦ h1 a fun b hb ↦ ih (f b) (h ▸ hb) rfl) (Eq.refl (f a))

theorem graph_induction {motive : SimpleGraph V → Prop}
    (h1 : ∀ G, (∀ G', Fintype.card (Dart G') < Fintype.card (Dart G) → motive G') → motive G) :
    motive G :=
  bla (f := λ G => Fintype.card (Dart G)) h1

theorem Menger : isMenger G := by
  induction' h : Fintype.card G.edgeSet using Nat.strongInductionOn with n ih generalizing G
  subst h
  by_cases h' : Fintype.card G.Dart = 0
  · simp [bot_iff_no_edge.mp h']
  · have h2 : ¬ IsEmpty G.Dart := by simpa [← Fintype.card_eq_zero_iff]
    obtain ⟨e⟩ := not_isEmpty_iff.mp h2
    refine induction_step e (ih _ contract_edge.fewer_edges rfl) (ih _ (Minus.card_edge e.edge_mem) rfl)

end Menger

end SimpleGraph
