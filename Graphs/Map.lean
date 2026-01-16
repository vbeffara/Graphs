-- import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Function

variable {V V' V'' : Type*} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
variable {G G₁ G₂ : SimpleGraph V} {G' G'₁ G'₂ : SimpleGraph V'} {G'' : SimpleGraph V''}

namespace SimpleGraph

-- SimpleGraph.map needs `f` to be injective
def map' (f : V → V') (G : SimpleGraph V) : SimpleGraph V' where
  Adj := Ne ⊓ Relation.Map G.Adj f f
  symm := λ _ _ ⟨h₁, u, v, h₂, h₃, h₄⟩ => ⟨h₁.symm, v, u, h₂.symm, h₄, h₃⟩

-- This is true but `fromRel` is more tedious to use (because it does not use the
-- symmetry of `G.Adj`, making all proofs more complicated).
example : map' f G = .fromRel (Relation.Map G.Adj f f) := by
  ext x y
  simp [map']
  rintro h ⟨a, b, hab, rfl, rfl⟩
  refine ⟨b, a, hab.symm, rfl, rfl⟩

theorem map'_eq_map_of_injective (hf : Injective f) : G.map' f = G.map ⟨f, hf⟩ := by
  ext x y
  simp [map', Relation.Map]
  rintro u v huv rfl rfl
  apply hf.ne huv.ne

@[simp] theorem map'_id : map' id G = G := by
  ext x y
  simpa [map'] using Adj.ne

theorem map'_adj (h : G.Adj x y) : f x = f y ∨ (map' f G).Adj (f x) (f y) := by
  simp [map', Relation.Map] ; grind

theorem map'_map' : map' g (map' f G) = map' (g ∘ f) G := by
  ext x y ; dsimp [map', Relation.Map] ; grind

theorem map'_monotone : Monotone (map' f) := by
  intro G₁ G₂ h x' y' ⟨h1, h2⟩
  exact ⟨h1, Relation.map_mono h _ _ h2⟩

theorem map'_le {f : G →g G'} : map' f G ≤ G' := by
  rintro x' y' ⟨-, x, y, h, rfl, rfl⟩
  exact f.map_adj h

def comap' (f : V → V') (G' : SimpleGraph V') : SimpleGraph V where
  Adj x y := x ≠ y ∧ (f x = f y ∨ G'.Adj (f x) (f y))
  symm _ _ := by simp [eq_comm, G'.adj_comm]

def comap'_subgraph (f : V → V') (H' : G'.Subgraph) : Subgraph (comap' f G') where
  verts := f ⁻¹' H'.verts
  Adj x y := x ≠ y ∧ f x ∈ H'.verts ∧ f y ∈ H'.verts ∧ (f x = f y ∨ H'.Adj (f x) (f y))
  adj_sub := by
    rintro x y ⟨h₁, h₂, h₃, h₄ | h₅⟩
    · exact ⟨h₁, .inl h₄⟩
    · exact ⟨h₁, .inr (H'.adj_sub h₅)⟩
  edge_vert := by grind
  symm x y h := by simp [eq_comm, H'.adj_comm, *]

def comap'_map'_le (f : V → V') (G : SimpleGraph V) : G ≤ comap' f (map' f G) := by
  rintro x y h
  refine ⟨h.ne, ?_⟩
  by_cases h' : f x = f y
  · exact .inl h'
  · exact .inr ⟨h', x, y, h, rfl, rfl⟩

def subgraph_inter (H : G.Subgraph) (G' : SimpleGraph V) : G'.Subgraph where
  verts := H.verts
  Adj := H.Adj ⊓ G'.Adj
  adj_sub h := h.2
  edge_vert h := H.edge_vert h.1
  symm x y := by simp [H.adj_comm, G'.adj_comm]

def comap'_subgraph' (H' : (map' f G).Subgraph) : Subgraph G :=
  subgraph_inter (comap'_subgraph f H') G

@[simp] theorem comap'_comap' : comap' f (comap' g G'') = comap' (g ∘ f) G'' := by
  ext x y ; dsimp [comap'] ; grind

theorem comap_eq_comap'_of_injective (hf : Injective f) : G'.comap f = G'.comap' f := by
  ext x y ; simp [comap'] ; grind [Adj.ne]

theorem comap'_monotone : Monotone (comap' f) := by
  rintro G'₁ G'₂ h x y ⟨h1, h2 | h2⟩ <;> refine ⟨h1, ?_⟩
  · exact Or.inl h2
  · exact Or.inr (h h2)

-- def merge_edge [DecidableEq V] {G : SimpleGraph V} (e : G.Dart) : V → V :=
--   update id e.snd e.fst

-- def merge_sym2 (e : Sym2 V) : Type _ := by
--   let rel (x y : V) : Prop := x = y ∨ s(x, y) = e
--   have : Equivalence rel := {
--     refl := by simp
--     symm := by rintro x y (rfl | h) <;> simp [Sym2.eq_swap, *]
--     trans := by
--       rintro x y z (rfl | h₁) (rfl | h₂) <;> try { simp [*] }
--       subst_vars ; rw [Sym2.eq_swap, Sym2.congr_left] at h₂ ; simp [h₂]
--   }
--   exact Quotient ⟨rel, this⟩

-- def merge_map (e : Sym2 V) : V → merge_sym2 e := Quotient.mk''

-- def contract_edge (G : SimpleGraph V) [DecidableEq V] (e : G.Dart) :=
--   G.map' (merge_edge e)

-- def contract_edge' (G : SimpleGraph V) [DecidableEq V] (e : G.edgeSet) : SimpleGraph (merge_sym2 e.1) := by
--   refine G.map' <| merge_map e.1

-- infix:60 " /ₑ " => contract_edge

-- namespace contract_edge

-- -- variable [fintype V] [DecidableEq V] [DecidableEq V'] [decidable_rel G.adj]

-- -- @[reducible] def preserved (f : V → V') (G : SimpleGraph V) : Type* :=
-- -- {e : G.Dart // f e.fst ≠ f e.snd}

-- -- def proj_edge (e : G.Dart) : preserved (merge_edge e) G → (G/e).Dart :=
-- -- λ ⟨⟨⟨x,y⟩,hxy⟩,h₁⟩, ⟨(merge_edge e x, merge_edge e y), ⟨h₁,x,y,hxy,rfl,rfl⟩⟩

-- -- lemma proj_edge_surj {e : G.Dart} : surjective (proj_edge e) :=
-- -- begin
-- --   rintro ⟨⟨x',y'⟩,⟨h₁,⟨x,y,h₂,h₃,h₄⟩⟩⟩, refine ⟨⟨⟨(x,y),h₂⟩,_⟩,_⟩,
-- --   { rw [h₃,h₄], exact h₁ },
-- --   { simp only [proj_edge, prod.mk.inj_iff], exact ⟨h₃,h₄⟩ }
-- -- end

-- lemma fewer_edges [Fintype V] {e : G.Dart} :
--   Fintype.card (G /ₑ e).edgeSet < Fintype.card G.edgeSet := sorry
-- -- calc fintype.card (G/e).Dart ≤ fintype.card (preserved (merge_edge e) G) :
-- --   fintype.card_le_of_surjective _ proj_edge_surj
-- --                         ...  < fintype.card (G.Dart) :
-- --   by { apply fintype.card_lt_of_injective_of_not_mem _ subtype.coe_injective,
-- --     swap, exact e, simp [merge_edge,update] }

-- end contract_edge

-- -- def select (P : V → Prop) (G : SimpleGraph V) : SimpleGraph (subtype P) :=
-- -- pull subtype.val G

-- -- namespace select
-- -- variable {P : V → Prop} {P' : V' → Prop}

-- -- lemma mono {P : V → Prop} : monotone (select P) :=
-- -- by { apply pull.mono }

-- -- def fmap (f : V → V') (P' : V' → Prop) : {x : V // P' (f x)} → {x' : V' // P' x'} :=
-- -- λ x, ⟨f x, x.prop⟩

-- -- def push_walk (p : walk G x y) (hp : ∀ z ∈ p.support, P z) :
-- --   walk (select P G) ⟨x, hp x (walk.start_mem_support p)⟩ ⟨y, hp y (walk.end_mem_support p)⟩ :=
-- -- begin
-- --   induction p with a a b c h₁ p ih, refl,
-- --   have hp' : ∀ z ∈ p.support, P z := by { intros z hz, apply hp, right, exact hz },
-- --   refine walk.cons _ (ih hp'), exact h₁
-- -- end

-- -- lemma mem_push_walk {p : G.walk x y} {hp : ∀ z ∈ p.support, P z} {z' : subtype P} :
-- --   z' ∈ (push_walk p hp).support ↔ z'.val ∈ p.support :=
-- -- begin
-- --   induction p with a a b c h₁ p ih,
-- --   { simp [push_walk, subtype.ext_iff, subtype.coe_mk] },
-- --   { split,
-- --     { rintro (h|h), left, subst h, right, exact ih.mp h },
-- --     { rintro (h|h), left, subst h, simp, right, exact ih.mpr h } }
-- -- end

-- -- def pull_walk {x y} (p : walk (select P G) x y) : walk G x.val y.val :=
-- -- by { induction p with a a b c h₁ p ih, refl, refine walk.cons h₁ ih }

-- -- lemma pull_walk_spec {x y} (p : walk (select P G) x y) : ∀ z ∈ (pull_walk p).support, P z :=
-- -- begin
-- --   induction p with a a b c h₁ p ih,
-- --   { intros z hz, cases hz, rw hz, exact a.prop, cases hz },
-- --   { intros z hz, cases hz, rw hz, exact a.prop, exact ih z hz }
-- -- end

-- -- end select

-- -- namespace is_smaller

-- -- lemma select_left {pred : V → Prop} : G ≼s G' -> select pred G ≼s G' :=
-- -- λ ⟨⟨f,h₁⟩,h₂⟩,
-- -- let g : {x // pred x} -> V' := f ∘ subtype.val
-- -- in ⟨⟨g,λ a b,h₁⟩,h₂.comp subtype.val_injective⟩

-- -- end is_smaller

-- -- def embed (f : V → V') : SimpleGraph V → SimpleGraph (range f) :=
-- -- select (range f) ∘ map f

-- -- namespace embed
-- -- noncomputable def iso (f_inj : injective f) : G ≃g embed f G :=
-- -- let φ : V → range f := λ x, ⟨f x, x, rfl⟩,
-- --     ψ : range f → V := λ y, some y.prop in
-- -- { to_fun := φ,
-- --   inv_fun := ψ,
-- --   left_inv := λ x, f_inj (some_spec (subtype.prop (φ x))),
-- --   right_inv := λ y, subtype.ext (some_spec y.prop),
-- --   map_rel_iff' := λ a b, by { dsimp only [φ], split,
-- --   { rintros ⟨-,x,y,h₂,h₃,h₄⟩, rwa [←f_inj h₃, ←f_inj h₄] },
-- --   { intro h₁, refine ⟨f_inj.ne (G.ne_of_adj h₁),a,b,h₁,rfl,rfl⟩ } } }

-- -- lemma le_select {f : G →g G'} (f_inj : injective f) : embed f G ≤ select (range f) G' :=
-- -- select.mono map.le

-- -- end embed

end SimpleGraph
