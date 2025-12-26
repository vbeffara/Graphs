import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

-- import combinatorics.SimpleGraph.basic combinatorics.SimpleGraph.connectivity data.set.basic
-- import graph_theory.basic

open Function Set Classical

variable {V V' V'' : Type*} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
variable {G G₁ G₂ : SimpleGraph V} {G' G'₁ G'₂ : SimpleGraph V'} {G'' : SimpleGraph V''}

namespace SimpleGraph

-- def pull (f : V → V') (G' : SimpleGraph V') : SimpleGraph V :=
-- { adj := G'.adj on f,
--   symm := λ _ _ h, G'.symm h,
--   loopless := λ _, G'.loopless _ }

-- namespace pull
-- lemma comp : pull (g ∘ f) = pull f ∘ pull g :=
-- by { ext x y, exact iff.rfl }

-- def to_iso (f : V ≃ V') (G' : SimpleGraph V') : pull f G' ≃g G' :=
-- ⟨f,λ x y, iff.rfl⟩

-- lemma from_iso (φ : G ≃g G') : pull φ G' = G :=
-- by { ext x y, have := φ.map_rel_iff', exact this }

-- lemma mono : monotone (pull f) :=
-- by { intros G'₁ G'₂ h x' y', apply h }
-- end pull

-- -- TODO: this is an alternative definition for pull
-- def pull' (f : V → V') (G' : SimpleGraph V') : SimpleGraph V :=
-- { adj := λ x y, x ≠ y ∧ (f x = f y ∨ G'.adj (f x) (f y)),
--   symm := λ x y ⟨h₁,h₂⟩, by { refine ⟨h₁.symm,_⟩, cases h₂, left, exact h₂.symm,
--     right, exact h₂.symm },
--   loopless := λ x, by { push_neg, intro, contradiction } }

-- namespace pull'
-- lemma comp : pull' (g ∘ f) = pull' f ∘ pull' g :=
-- begin
--   ext G'' x y, split,
--   { rintros ⟨h₁,h₂⟩, refine ⟨h₁,_⟩, by_cases f x = f y,
--     { left, exact h },
--     { right, exact ⟨h,h₂⟩ } },
--   { rintros ⟨h₁,h₂⟩, refine ⟨h₁,_⟩, cases h₂,
--     { left, convert congr_arg g h₂ },
--     { rcases h₂ with ⟨h₃,h₄⟩, cases h₄, left, exact h₄, right, exact h₄ } }
-- end

-- lemma iff_pull_of_inj (hf : injective f) : pull f G' = pull' f G' :=
-- begin
--   ext x y, split,
--   { intro h₁, refine ⟨SimpleGraph.ne_of_adj _ h₁,_⟩, right, exact h₁ },
--   { rintros ⟨h₁,h₂⟩, cases h₂, have := hf h₂, contradiction, exact h₂ }
-- end

-- def to_iso (f : V ≃ V') (G' : SimpleGraph V') : pull' f G' ≃g G' :=
-- by { rewrite ← iff_pull_of_inj f.injective, apply pull.to_iso }

-- lemma from_iso (φ : G ≃g G') : pull' φ G' = G :=
-- by { rewrite ← iff_pull_of_inj φ.injective, apply pull.from_iso }

-- lemma mono : monotone (pull' f) :=
-- by { rintros G H h x y ⟨h₁,h₂⟩, refine ⟨h₁,_⟩, cases h₂, left, exact h₂, right, exact h h₂ }
-- end pull'

def map' (f : V → V') (G : SimpleGraph V) : SimpleGraph V' :=
{ Adj := Ne ⊓ Relation.Map G.Adj f f,
  symm := λ _ _ ⟨h₁, u, v, h₂, h₃, h₄⟩ => ⟨h₁.symm, v, u, h₂.symm, h₄, h₃⟩,
  loopless := λ _ ⟨h, _⟩ => h rfl }

-- namespace map
-- noncomputable instance : decidable_rel (map f G).adj := by { classical, apply_instance }

-- @[simp] lemma id : map id G = G :=
-- begin
--   ext : 1,
--   simp only [map, relation.map, id.def, exists_eq_right_right, exists_eq_right, inf_eq_right],
--   apply ne_of_adj,
-- end

-- lemma adj (f : V → V') : G.adj x y → f x = f y ∨ (map f G).adj (f x) (f y) :=
-- by { intro h₁, by_cases f x = f y, left, exact h, right, refine ⟨h,x,y,h₁,rfl,rfl⟩ }

-- lemma comp : map (g ∘ f) = map g ∘ map f :=
-- begin
--   ext G x'' y'', split,
--   { rintro ⟨h₁,u,v,h₂,rfl,rfl⟩, exact ⟨h₁,f u,f v,⟨ne_of_apply_ne _ h₁,u,v,h₂,rfl,rfl⟩,rfl,rfl⟩ },
--   { rintro ⟨h₁,x',y',⟨h₂,x,y,h₃,rfl,rfl⟩,rfl,rfl⟩, exact ⟨h₁,x,y,h₃,rfl,rfl⟩ }
-- end

-- lemma left_inverse_of_injective (h : injective f) : left_inverse (pull f) (map f) :=
-- begin
--   intro G, ext x y, split,
--   { rintro ⟨h₁,u,v,h₂,h₃,h₄⟩, rw [←h h₃, ←h h₄], exact h₂ },
--   { intro h₁, exact ⟨h.ne (G.ne_of_adj h₁),x,y,h₁,rfl,rfl⟩ }
-- end

-- lemma left_inverse_of_injective' (h : injective f) : left_inverse (pull' f) (map f) :=
-- begin
--   intro G, ext x y, split,
--   { rintro ⟨h₁,h₂⟩, cases h₂, have := h h₂, contradiction,
--     rcases h₂ with ⟨h₂,x',y',h₃,h₄,h₅⟩, rwa [←h h₄, ←h h₅] },
--   { intro h₁, refine ⟨G.ne_of_adj h₁, _⟩, by_cases h₂ : f x = f y,
--     left, exact h₂, right, exact ⟨h₂,x,y,h₁,rfl,rfl⟩ }
-- end

-- lemma right_inverse_of_surjective (h : surjective f) : right_inverse (pull f) (map f) :=
-- begin
--   intro G', ext x' y', split,
--   { rintro ⟨-,x,y,h₂,rfl,rfl⟩, exact h₂ },
--   { intro h₁, cases h x' with x, cases h y' with y, substs x' y',
--     exact ⟨G'.ne_of_adj h₁,x,y,h₁,rfl,rfl⟩ }
-- end

-- lemma right_inverse_of_surjective' (h : surjective f) : right_inverse (pull' f) (map f) :=
-- begin
--   intro G', ext x' y', split,
--   { rintro ⟨h₁,x,y,⟨-,h₃⟩,rfl,rfl⟩, cases h₃, contradiction, exact h₃ },
--   { intro h₁, cases h x' with x, cases h y' with y, substs x' y',
--     refine ⟨G'.ne_of_adj h₁,x,y,_,rfl,rfl⟩, refine ⟨_,_⟩, intro h₂,
--     exact G'.ne_of_adj h₁ (congr_arg f h₂), right, exact h₁ }
-- end

-- def to_iso (f : V ≃ V') (G : SimpleGraph V) : G ≃g map f G :=
-- by { convert ← pull.to_iso f _, apply left_inverse_of_injective f.left_inv.injective }

-- lemma from_iso (φ : G ≃g G') : G' = map φ G :=
-- by { convert ← congr_arg _ (pull.from_iso φ),
--   apply right_inverse_of_surjective φ.right_inv.surjective }

-- lemma mono : monotone (map f) :=
-- by { rintros G₁ G₂ h₁ x' y' ⟨h₂,x,y,h₃,rfl,rfl⟩, exact ⟨h₂,x,y,h₁ h₃,rfl,rfl⟩ }

-- lemma le {φ : G →g G'} : map φ G ≤ G' :=
-- by { rintros x' y' ⟨-,x,y,h₂,rfl,rfl⟩, exact φ.map_rel h₂ }

-- end map

def merge_edge [DecidableEq V] {G : SimpleGraph V} (e : G.Dart) : V → V :=
  update id e.snd e.fst

def merge_sym2 (e : Sym2 V) : Type _ := by
  let rel (x y : V) : Prop := x = y ∨ s(x, y) = e
  have : Equivalence rel := {
    refl := by simp
    symm := by rintro x y (rfl | h) <;> simp [Sym2.eq_swap, *]
    trans := by
      rintro x y z (rfl | h₁) (rfl | h₂) <;> try { simp [*] }
      subst_vars ; rw [Sym2.eq_swap, Sym2.congr_left] at h₂ ; simp [h₂]
  }
  exact Quotient ⟨rel, this⟩

def merge_map (e : Sym2 V) : V → merge_sym2 e := Quotient.mk''

def contract_edge (G : SimpleGraph V) [DecidableEq V] (e : G.Dart) :=
  G.map' (merge_edge e)

def contract_edge' (G : SimpleGraph V) [DecidableEq V] (e : G.edgeSet) : SimpleGraph (merge_sym2 e.1) := by
  refine G.map' <| merge_map e.1

infix:60 " /ₑ " => contract_edge

namespace contract_edge

-- variable [fintype V] [DecidableEq V] [DecidableEq V'] [decidable_rel G.adj]

-- @[reducible] def preserved (f : V → V') (G : SimpleGraph V) : Type* :=
-- {e : G.Dart // f e.fst ≠ f e.snd}

-- def proj_edge (e : G.Dart) : preserved (merge_edge e) G → (G/e).Dart :=
-- λ ⟨⟨⟨x,y⟩,hxy⟩,h₁⟩, ⟨(merge_edge e x, merge_edge e y), ⟨h₁,x,y,hxy,rfl,rfl⟩⟩

-- lemma proj_edge_surj {e : G.Dart} : surjective (proj_edge e) :=
-- begin
--   rintro ⟨⟨x',y'⟩,⟨h₁,⟨x,y,h₂,h₃,h₄⟩⟩⟩, refine ⟨⟨⟨(x,y),h₂⟩,_⟩,_⟩,
--   { rw [h₃,h₄], exact h₁ },
--   { simp only [proj_edge, prod.mk.inj_iff], exact ⟨h₃,h₄⟩ }
-- end

lemma fewer_edges [Fintype V] {e : G.Dart} :
  Fintype.card (G /ₑ e).edgeSet < Fintype.card G.edgeSet := sorry
-- calc fintype.card (G/e).Dart ≤ fintype.card (preserved (merge_edge e) G) :
--   fintype.card_le_of_surjective _ proj_edge_surj
--                         ...  < fintype.card (G.Dart) :
--   by { apply fintype.card_lt_of_injective_of_not_mem _ subtype.coe_injective,
--     swap, exact e, simp [merge_edge,update] }

end contract_edge

-- def select (P : V → Prop) (G : SimpleGraph V) : SimpleGraph (subtype P) :=
-- pull subtype.val G

-- namespace select
-- variable {P : V → Prop} {P' : V' → Prop}

-- lemma mono {P : V → Prop} : monotone (select P) :=
-- by { apply pull.mono }

-- def fmap (f : V → V') (P' : V' → Prop) : {x : V // P' (f x)} → {x' : V' // P' x'} :=
-- λ x, ⟨f x, x.prop⟩

-- def push_walk (p : walk G x y) (hp : ∀ z ∈ p.support, P z) :
--   walk (select P G) ⟨x, hp x (walk.start_mem_support p)⟩ ⟨y, hp y (walk.end_mem_support p)⟩ :=
-- begin
--   induction p with a a b c h₁ p ih, refl,
--   have hp' : ∀ z ∈ p.support, P z := by { intros z hz, apply hp, right, exact hz },
--   refine walk.cons _ (ih hp'), exact h₁
-- end

-- lemma mem_push_walk {p : G.walk x y} {hp : ∀ z ∈ p.support, P z} {z' : subtype P} :
--   z' ∈ (push_walk p hp).support ↔ z'.val ∈ p.support :=
-- begin
--   induction p with a a b c h₁ p ih,
--   { simp [push_walk, subtype.ext_iff, subtype.coe_mk] },
--   { split,
--     { rintro (h|h), left, subst h, right, exact ih.mp h },
--     { rintro (h|h), left, subst h, simp, right, exact ih.mpr h } }
-- end

-- def pull_walk {x y} (p : walk (select P G) x y) : walk G x.val y.val :=
-- by { induction p with a a b c h₁ p ih, refl, refine walk.cons h₁ ih }

-- lemma pull_walk_spec {x y} (p : walk (select P G) x y) : ∀ z ∈ (pull_walk p).support, P z :=
-- begin
--   induction p with a a b c h₁ p ih,
--   { intros z hz, cases hz, rw hz, exact a.prop, cases hz },
--   { intros z hz, cases hz, rw hz, exact a.prop, exact ih z hz }
-- end

-- end select

-- namespace is_smaller

-- lemma select_left {pred : V → Prop} : G ≼s G' -> select pred G ≼s G' :=
-- λ ⟨⟨f,h₁⟩,h₂⟩,
-- let g : {x // pred x} -> V' := f ∘ subtype.val
-- in ⟨⟨g,λ a b,h₁⟩,h₂.comp subtype.val_injective⟩

-- end is_smaller

-- def embed (f : V → V') : SimpleGraph V → SimpleGraph (range f) :=
-- select (range f) ∘ map f

-- namespace embed
-- noncomputable def iso (f_inj : injective f) : G ≃g embed f G :=
-- let φ : V → range f := λ x, ⟨f x, x, rfl⟩,
--     ψ : range f → V := λ y, some y.prop in
-- { to_fun := φ,
--   inv_fun := ψ,
--   left_inv := λ x, f_inj (some_spec (subtype.prop (φ x))),
--   right_inv := λ y, subtype.ext (some_spec y.prop),
--   map_rel_iff' := λ a b, by { dsimp only [φ], split,
--   { rintros ⟨-,x,y,h₂,h₃,h₄⟩, rwa [←f_inj h₃, ←f_inj h₄] },
--   { intro h₁, refine ⟨f_inj.ne (G.ne_of_adj h₁),a,b,h₁,rfl,rfl⟩ } } }

-- lemma le_select {f : G →g G'} (f_inj : injective f) : embed f G ≤ select (range f) G' :=
-- select.mono map.le

-- end embed

end SimpleGraph
