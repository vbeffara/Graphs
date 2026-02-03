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

theorem αα_eq (G : PlanarMap E) (e : E) : G.α (G.α e) = e := by
  rw [← Equiv.Perm.mul_apply, G.invol] ; rfl

@[reducible]
def vertexType (G : PlanarMap E) := orbitRel.Quotient (Subgroup.closure {G.σ}) E

@[reducible]
def edgeType (G : PlanarMap E) := orbitRel.Quotient (Subgroup.closure {G.α}) E

@[reducible]
def faceType (G : PlanarMap E) := orbitRel.Quotient (Subgroup.closure {G.φ}) E

lemma good_s (f : Perm E) (s : Finset E) (x : E) (hx : x ∉ s) : ∃ n > 0, f^[n] x ∉ s := by
  sorry

noncomputable def skip (f : Perm E) (s : Finset E) : Perm {e : E // e ∉ s} where
  toFun x := by
    let n' := Nat.find (p := fun n => n > 0 ∧ f^[n] x ∉ s) (good_s f s x x.2)
    exact ⟨f^[n'] x, Nat.find_spec (p := fun n => n > 0 ∧ f^[n] x ∉ s) _ |>.2⟩
  invFun x := by
    let n' := Nat.find (p := fun n => n > 0 ∧ f.symm^[n] x ∉ s) (good_s f⁻¹ s x x.2)
    exact ⟨f.symm^[n'] x, Nat.find_spec (p := fun n => n > 0 ∧ f.symm^[n] x ∉ s) _ |>.2⟩
  left_inv x := sorry
  right_inv x := sorry

theorem skip_empty (f : Perm E) (x : E) : skip f ∅ ⟨x, by simp⟩ = f x := by
  simp [skip]
  sorry

#exit

def σ_skip (G : PlanarMap E) (e : E) : Perm {f : E // f ≠ e ∧ f ≠ G.α e} where
  toFun d := by
    by_cases h : G.σ d ≠ e ∧ G.σ d ≠ G.α e ; exact ⟨_, h⟩
    refine ⟨G.σ (G.α (G.σ d)), ?_⟩
    · rw [← or_iff_not_and_not] at h
      obtain ⟨d, hd1, hd2⟩ := d
      dsimp at h ⊢
      obtain rfl | h := h
      · simp
        constructor
        · exact hd2.symm
        · intro h
          have h1 := G.σ.injective.ne hd2
          rw [h] at h1
          have h2 := G.α.injective.ne hd1
          sorry
      · sorry
  invFun := sorry

def contract (G : PlanarMap E) (e : E) : PlanarMap {f : E // f ≠ e ∧ f ≠ G.α e} where
  σ := sorry
  α := sorry
  φ := sorry
  rel := sorry
  trans := sorry
  invol := sorry
  nofix := sorry

noncomputable def genus [Fintype E] (G : PlanarMap E) : ℤ :=
  (2 - G.eulerCharacteristic) / 2

example {V : Type} [Group V] (a b : V) : a⁻¹ * b⁻¹ = (b * a)⁻¹ := by
  exact Eq.symm (DivisionMonoid.mul_inv_rev b a)

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

namespace Fin

def next {n : ℕ} (i : Fin n) : Fin n :=
  match n with
  | 0 => i.elim0
  | 1 => i
  | _ + 2 => i + 1

def prev {n : ℕ} (i : Fin n) : Fin n :=
  match n with
  | 0 => i.elim0
  | 1 => i
  | _ + 2 => i - 1

@[simp] theorem next_prev : i.prev.next = i := by
  match n with
  | 0 => exact i.elim0
  | 1 => rfl
  | _ + 2 => simp only [next, prev, sub_add_cancel]

@[simp] theorem prev_next : i.next.prev = i := by
  match n with
  | 0 => exact i.elim0
  | 1 => rfl
  | _ + 2 => simp only [prev, next, add_sub_cancel_right]

def rotate : Perm (Σ v, Fin (d v)) where
  toFun e := ⟨e.1, e.2.next⟩
  invFun e := ⟨e.1, e.2.prev⟩
  left_inv e := by simp
  right_inv e := by simp

end Fin

structure ConcretePlanarMap (V : Type*) where
  deg : V → ℕ
  α' : Perm (Σ v, Fin (deg v))
  α'_ne e : α' e ≠ e
  α'_sq : α' ^ 2 = 1
  trans' : MulAction.IsPretransitive (Subgroup.closure {Fin.rotate, α'}) (Σ v, Fin (deg v))

namespace ConcretePlanarMap

def darts (G : ConcretePlanarMap V) := Σ v, Fin (G.deg v)

variable {G : ConcretePlanarMap V} {e : G.darts}

instance [Fintype V] : Fintype G.darts := by unfold darts ; infer_instance

def σ (G : ConcretePlanarMap V) : Perm (darts G) := Fin.rotate

@[simp] theorem σ_fst : (G.σ e).1 = e.1 := rfl

def α (G : ConcretePlanarMap V) : Perm (darts G) := G.α'

@[simp] theorem α_ne : G.α e ≠ e := G.α'_ne e

@[simp] theorem α_sq : G.α ^ 2 = 1 := G.α'_sq

@[simp] theorem α_α : G.α (G.α e) = e := by change (G.α ^ 2) e = e ; simp

@[simp] theorem fixedPoints_α : fixedPoints G.α = ∅ := by
  by_contra! ; obtain ⟨e, he⟩ := this ; exact G.α_ne he

def φ (G : ConcretePlanarMap V) : Perm (darts G) := (G.σ)⁻¹ * (G.α)⁻¹

@[simp] theorem σαφ : G.φ * G.α * G.σ = 1 := by simp [φ]

def n_vertices [Fintype V] (_ : ConcretePlanarMap V) : ℕ := Fintype.card V

def n_edges [Fintype V] (G : ConcretePlanarMap V) : ℕ := Fintype.card (G.darts) / 2

noncomputable def n_faces [Fintype V] (G : ConcretePlanarMap V) : ℕ := by
  exact G.φ.cycleType.card + Fintype.card (fixedPoints G.φ)

theorem darts_even [Fintype V] : Even (Fintype.card G.darts) := by
  have h2 : G.α.support = Finset.univ := by ext e ; simp
  simpa [even_iff_two_dvd, ← Finset.card_univ, ← h2] using G.α.two_dvd_card_support G.α_sq

def CartoGroup (G : ConcretePlanarMap V) := Subgroup.closure {G.α, G.σ}

noncomputable def χ [Fintype V] (G : ConcretePlanarMap V) : ℤ :=
  G.n_vertices - G.n_edges + G.n_faces

example [Fintype V] : Even G.χ := by -- this is only true for connected planar maps
  sorry

noncomputable def genus [Fintype V] (G : ConcretePlanarMap V) : ℤ :=
  (2 - G.χ) / 2

instance : HasQuotient E (Subgroup (Perm E)) := ⟨fun G => orbitRel.Quotient G E⟩

end ConcretePlanarMap
