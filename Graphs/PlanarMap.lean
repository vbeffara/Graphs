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
  α_ne e : α' e ≠ e
  α_sq e : α' (α' e) = e

variable {G : PlanarMap V}

namespace PlanarMap

def darts (G : PlanarMap V) := Σ v, Fin (G.deg v)

instance [Fintype V] : Fintype G.darts := by unfold darts ; infer_instance

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

@[simp] theorem fixedPoints_α [Fintype V] : fixedPoints G.α = ∅ := by
  by_contra! ; obtain ⟨e, he⟩ := this ; exact G.α_ne e he

theorem darts_even [Fintype V] : Even (Fintype.card G.darts) := by
  let S : Finset (Finset G.darts) := Finset.image (fun e => {e, G.α e}) Finset.univ
  have h1 : ∀ s ∈ S, s.card = 2 := by
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]
    intro e
    exact Finset.card_pair (G.α_ne e).symm
  have h3 : (Finset.univ : Finset G.darts) = Finset.biUnion S id := by
    ext e; simp [S, Finset.mem_biUnion, Finset.mem_image]
  have h4 : (S : Set (Finset G.darts)).PairwiseDisjoint id := by
    simp [S]
    rintro d1 ⟨e1, rfl⟩ d2 ⟨e2, rfl⟩
    simp [Finset.disjoint_left]
    have s1 : ∀ e, G.α e ≠ e := G.α_ne
    have s2 : ∀ e, G.α (G.α e) = e := G.α_sq
    grind
  simpa [← Finset.card_univ, h3, Finset.card_biUnion h4] using Finset.even_sum _ (by grind)

noncomputable def χ [Fintype V] (G : PlanarMap V) : ℤ :=
  G.n_vertices - G.n_edges + G.n_faces

example [Fintype V] : Even G.χ := by
  sorry

noncomputable def genus [Fintype V] (G : PlanarMap V) : ℤ :=
  (2 - G.χ) / 2

end PlanarMap
