import Mathlib.Combinatorics.SimpleGraph.Subgraph

open Function Classical Set Finset

variable {V V' V'' : Type*}
variable {G H : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}

namespace SimpleGraph

structure FiniteGraph where
  support : Type*
  finite : Fintype support
  graph : SimpleGraph support

def IsSmaller (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ f : G →g G', Injective f

def IsSmaller' (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ H : Subgraph G', Nonempty (G ≃g H.coe)

def subgraph_map (f : G →g G') : Subgraph G' where
  verts := range f
  Adj x' y' := ∃ x y, x' = f x ∧ y' = f y ∧ G.Adj x y
  adj_sub := by rintro _ _ ⟨x, y, rfl, rfl, h⟩ ; exact f.map_rel h
  edge_vert := by grind
  symm := by rintro _ _ ⟨x, y, rfl, rfl, h⟩ ; refine ⟨y, x, rfl, rfl, h.symm⟩

noncomputable def subgraph_map_iso (f : G →g G') (hf : Injective f) : G ≃g (subgraph_map f).coe where
  toEquiv := Equiv.ofInjective f hf
  map_rel_iff' {x y} := by simp only [subgraph_map, Equiv.ofInjective_apply, Subgraph.coe_adj] ; grind

def ofSet (G : SimpleGraph V) (S : Set V) : Subgraph G where
  verts := S
  Adj x y := x ∈ S ∧ y ∈ S ∧ G.Adj x y
  adj_sub := by grind
  symm := by grind [Symmetric, G.adj_comm]
  edge_vert := by grind

theorem isSmaller_iff_isSmaller' : IsSmaller G G' ↔ IsSmaller' G G' := by
  constructor
  · rintro ⟨f, hf⟩ ; exact ⟨_, ⟨subgraph_map_iso f hf⟩⟩
  · rintro ⟨H, ⟨f⟩⟩ ; exact ⟨H.hom.comp f.toHom, by simpa using f.injective⟩

infix:50 " ≼s " => IsSmaller

namespace IsSmaller

lemma of_le (h : G ≤ H) : G ≼s H := ⟨⟨id, (h ·)⟩, injective_id⟩

lemma of_iso : G ≃g G' → G ≼s G' := λ ⟨⟨f, _, h1, _⟩, h3⟩ => ⟨⟨f, h3.2⟩, h1.injective⟩

@[refl] lemma refl : G ≼s G := ⟨⟨id, id⟩, injective_id⟩

@[trans] lemma trans : G ≼s G' → G' ≼s G'' → G ≼s G'' :=
  λ ⟨f₁, h₁⟩ ⟨f₂, h₂⟩ => ⟨f₂.comp f₁, h₂.comp h₁⟩

lemma iso_left (h1 : G ≃g G') (h2 : G' ≼s G'') : G ≼s G'' := of_iso h1 |>.trans h2

lemma le_left (h1 : G ≤ H) (h2 : H ≼s G') : G ≼s G' := of_le h1 |>.trans h2

lemma iso_right (h1 : G ≼s G') (h2 : G' ≃g G'') : G ≼s G'' := h1.trans (of_iso h2)

end IsSmaller
