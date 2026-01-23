import Mathlib

open Equiv Classical Function

variable {V : Type*} {n : ℕ} {i : Fin n}

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

end Fin

structure PlanarMap (V : Type*) where
  deg : V → ℕ
  α' : Perm (Σ v, Fin (deg v))
  α'_ne e : α' e ≠ e
  α'_sq : α' ^ 2 = 1

namespace PlanarMap

def darts (G : PlanarMap V) := Σ v, Fin (G.deg v)

variable {G : PlanarMap V} {e : G.darts}

instance [Fintype V] : Fintype G.darts := by unfold darts ; infer_instance

def σ (G : PlanarMap V) : Perm (darts G) where
  toFun e := ⟨e.1, e.2.next⟩
  invFun e := ⟨e.1, e.2.prev⟩
  left_inv e := by simp
  right_inv e := by simp

@[simp] theorem σ_fst : (G.σ e).1 = e.1 := rfl

def α (G : PlanarMap V) : Perm (darts G) := G.α'

@[simp] theorem α_ne : G.α e ≠ e := G.α'_ne e

@[simp] theorem α_sq : G.α ^ 2 = 1 := G.α'_sq

@[simp] theorem α_α : G.α (G.α e) = e := by change (G.α ^ 2) e = e ; simp

def φ (G : PlanarMap V) : Perm (darts G) := (G.σ)⁻¹ * (G.α)⁻¹

@[simp] theorem σαφ : G.φ * G.α * G.σ = 1 := by simp [φ]

def n_vertices [Fintype V] (_ : PlanarMap V) : ℕ := Fintype.card V

def n_edges [Fintype V] (G : PlanarMap V) : ℕ := Fintype.card (G.darts) / 2

noncomputable def n_faces [Fintype V] (G : PlanarMap V) : ℕ := by
  exact G.φ.cycleType.card + Fintype.card (fixedPoints G.φ)

@[simp] theorem fixedPoints_α [Fintype V] : fixedPoints G.α = ∅ := by
  by_contra! ; obtain ⟨e, he⟩ := this ; exact G.α_ne he

theorem darts_even [Fintype V] : Even (Fintype.card G.darts) := by
  have h2 : G.α.support = Finset.univ := by ext e ; simp
  simpa [even_iff_two_dvd, ← Finset.card_univ, ← h2] using G.α.two_dvd_card_support G.α_sq

noncomputable def χ [Fintype V] (G : PlanarMap V) : ℤ :=
  G.n_vertices - G.n_edges + G.n_faces

example [Fintype V] : Even G.χ := by -- this is only true for connected planar maps
  sorry

noncomputable def genus [Fintype V] (G : PlanarMap V) : ℤ :=
  (2 - G.χ) / 2

end PlanarMap
