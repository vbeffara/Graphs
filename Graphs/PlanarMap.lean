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
  degree : V → ℕ
  α' : Perm (Σ v, Fin (degree v))
  α_ne e : α' e ≠ e
  α_sq : α' * α' = 1

variable {G : PlanarMap V}

namespace PlanarMap

def darts (G : PlanarMap V) := Σ v, Fin (G.degree v)

instance [Fintype V] : Fintype G.darts := by unfold darts ; infer_instance

theorem darts_even [Fintype V] : Even (Fintype.card G.darts) := by
  sorry

def σ (G : PlanarMap V) : Perm (darts G) where
  toFun e := ⟨e.1, e.2.next⟩
  invFun e := ⟨e.1, e.2.prev⟩
  left_inv e := by simp
  right_inv e := by simp

@[simp] theorem σ_fst {e : G.darts} : (G.σ e).1 = e.1 := rfl

def α (G : PlanarMap V) : Perm (darts G) := G.α'

def φ (G : PlanarMap V) : Perm (darts G) := (G.σ)⁻¹ * (G.α)⁻¹

@[simp] theorem σαφ : G.φ * G.α * G.σ = 1 := by simp [φ]

def n_vertices [Fintype V] (_ : PlanarMap V) : ℕ := Fintype.card V

def n_edges [Fintype V] (G : PlanarMap V) : ℕ := Fintype.card (G.darts) / 2

noncomputable def n_faces [Fintype V] (G : PlanarMap V) : ℕ := by
  exact G.φ.cycleType.card + Fintype.card (fixedPoints G.φ)

noncomputable def χ [Fintype V] (G : PlanarMap V) : ℤ :=
  G.n_vertices - G.n_edges + G.n_faces

example [Fintype V] : Even G.χ := by
  sorry

noncomputable def genus [Fintype V] (G : PlanarMap V) : ℤ :=
  (2 - G.χ) / 2

end PlanarMap
