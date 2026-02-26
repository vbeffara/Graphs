import Mathlib

open Equiv Classical Function MulAction Set

variable {V E : Type*} {n : ℕ} {i : Fin n} {d : V → ℕ}

-- As in https://ncatlab.org/nlab/show/combinatorial+map
structure PlanarMap (E : Type*) where
  σ : Perm E
  α : Perm E
  φ : Perm E
  rel : φ * α * σ = 1
  trans : MulAction.IsPretransitive (Subgroup.closure {σ, α, φ}) E
  invol : α * α = 1
  nofix e : α e ≠ e

namespace PlanarMap

variable {G : PlanarMap E} {e : E}

def cartoGroup (G : PlanarMap E) := Subgroup.closure {G.σ, G.α, G.φ}

@[simp] theorem fixed : fixedPoints G.α = ∅ := by
  by_contra! ; obtain ⟨e, he⟩ := this ; exact G.nofix e he

theorem even {G : PlanarMap E} [Fintype E] : Even (Fintype.card E) := by
  have h2 : G.α.support = Finset.univ := by ext e; simpa using G.nofix e
  simpa [even_iff_two_dvd, h2] using G.α.two_dvd_card_support G.invol

theorem αα_eq (G : PlanarMap E) (e : E) : G.α (G.α e) = e := by
  rw [← Equiv.Perm.mul_apply, G.invol] ; rfl

@[reducible]
def vertexType (G : PlanarMap E) := orbitRel.Quotient (Subgroup.closure {G.σ}) E

@[reducible]
def edgeType (G : PlanarMap E) := orbitRel.Quotient (Subgroup.closure {G.α}) E

@[reducible]
def faceType (G : PlanarMap E) := orbitRel.Quotient (Subgroup.closure {G.φ}) E

noncomputable def eulerChar [Fintype E] (G : PlanarMap E) : ℤ :=
  Fintype.card (vertexType G) - Fintype.card (edgeType G) + Fintype.card (faceType G)

def dual (G : PlanarMap E) : PlanarMap E where
  σ := G.φ⁻¹
  α := G.α⁻¹
  φ := G.σ⁻¹
  rel := by simpa only [← mul_inv_rev, inv_eq_one] using G.rel
  trans := by
    have h1 : ({G.φ⁻¹, G.α⁻¹, G.σ⁻¹} : Set (Perm E)) = {G.σ⁻¹, G.α⁻¹, G.φ⁻¹} := by grind
    have := G.trans
    rwa [← Subgroup.closure_inv, Set.inv_insert, Set.inv_insert, Set.inv_singleton, ← h1] at this
  invol := by simpa using congr_arg (fun x => x⁻¹) G.invol
  nofix e he := G.nofix (G.α⁻¹ e) (by simpa using he.symm)

end PlanarMap
