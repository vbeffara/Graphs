import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Function

variable {V V' V'' : Type*} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
variable {G G₁ G₂ : SimpleGraph V} {G' G'₁ G'₂ : SimpleGraph V'} {G'' : SimpleGraph V''}

namespace SimpleGraph

-- This is true but `fromRel` is more tedious to use (because it does not use the
-- symmetry of `G.Adj`, making all proofs more complicated).
example : G.map f = .fromRel (Relation.Map G.Adj f f) := by
  ext x y
  simp [SimpleGraph.map]
  rintro h ⟨a, b, hab, rfl, rfl⟩
  refine ⟨b, a, hab.symm, rfl, rfl⟩

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

def comap'_map'_le (f : V → V') (G : SimpleGraph V) : G ≤ comap' f (G.map f) := by
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

def comap'_subgraph' (H' : (G.map f).Subgraph) : Subgraph G :=
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
