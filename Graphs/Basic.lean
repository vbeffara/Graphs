import Mathlib.Combinatorics.SimpleGraph.Subgraph

open Function Classical Set Finset SimpleGraph

variable {α β γ : Type*}
variable {G G' : SimpleGraph α} {H : SimpleGraph β} {K : SimpleGraph γ}

namespace SimpleGraph

structure FiniteGraph where
  support : Type*
  finite : Fintype support
  graph : SimpleGraph support

def IsSmaller (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ f : G →g H, Injective f

def IsSmaller' (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ H : Subgraph H, Nonempty (G ≃g H.coe)

def subgraph_map (f : G →g H) : Subgraph H where
  verts := range f
  Adj x' y' := ∃ x y, x' = f x ∧ y' = f y ∧ G.Adj x y
  adj_sub := by rintro _ _ ⟨x, y, rfl, rfl, h⟩ ; exact f.map_rel h
  edge_vert := by grind
  symm := by rintro _ _ ⟨x, y, rfl, rfl, h⟩ ; refine ⟨y, x, rfl, rfl, h.symm⟩

noncomputable def subgraph_map_iso (f : G →g H) (hf : Injective f) : G ≃g (subgraph_map f).coe where
  toEquiv := Equiv.ofInjective f hf
  map_rel_iff' {x y} := by simp only [subgraph_map, Equiv.ofInjective_apply, Subgraph.coe_adj] ; grind

def ofSet (G : SimpleGraph α) (S : Set α) : Subgraph G where
  verts := S
  Adj x y := x ∈ S ∧ y ∈ S ∧ G.Adj x y
  adj_sub := by grind
  symm := by grind [Symmetric, G.adj_comm]
  edge_vert := by grind

theorem isSmaller_iff_isSmaller' : IsSmaller G H ↔ IsSmaller' G H := by
  constructor
  · rintro ⟨f, hf⟩ ; exact ⟨_, ⟨subgraph_map_iso f hf⟩⟩
  · rintro ⟨H, ⟨f⟩⟩ ; exact ⟨H.hom.comp f.toHom, by simpa using f.injective⟩

infix:50 " ≼s " => IsSmaller

namespace IsSmaller

lemma of_le (h : G ≤ G') : G ≼s G' := ⟨⟨id, (h ·)⟩, injective_id⟩

lemma of_iso : G ≃g H → G ≼s H := λ ⟨⟨f, _, h1, _⟩, h3⟩ => ⟨⟨f, h3.2⟩, h1.injective⟩

@[refl] lemma refl : G ≼s G := ⟨⟨id, id⟩, injective_id⟩

@[trans] lemma trans : G ≼s H → H ≼s K → G ≼s K :=
  λ ⟨f₁, h₁⟩ ⟨f₂, h₂⟩ => ⟨f₂.comp f₁, h₂.comp h₁⟩

lemma iso_left (h1 : G ≃g H) (h2 : H ≼s K) : G ≼s K := of_iso h1 |>.trans h2

lemma le_left (h1 : G ≤ G') (h2 : G' ≼s H) : G ≼s H := of_le h1 |>.trans h2

lemma iso_right (h1 : G ≼s H) (h2 : H ≃g K) : G ≼s K := h1.trans (of_iso h2)

end IsSmaller
