import Mathlib

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

end SimpleGraph
