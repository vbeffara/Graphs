/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e7124df4-c4ac-4dfa-b52e-da205c37fdcf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem darts_even [Fintype V] : Even (Fintype.card G.darts)

The following was negated by Aristotle:

- example [Fintype V] : Even G.χ

Here is the code for the `negate_state` tactic, used within these negations:
-/

import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)

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
  -- Since each dart has another dart that's its "next" dart, and each pair is counted twice, the total number of darts must be even.
  have h_even_darts : ∃ α : Equiv.Perm G.darts, ∀ e : G.darts, α e ≠ e ∧ α (α e) = e := by
    exact ⟨ G.α', fun e => ⟨ G.α_ne e, by simpa [ sq ] using congr_arg ( fun f => f e ) G.α_sq ⟩ ⟩;
  obtain ⟨α, hα⟩ := h_even_darts
  have h_even_card : Even (Finset.card (Finset.univ : Finset G.darts)) := by
    -- Since α is a permutation of the darts, the set of darts can be partitioned into pairs {e, α(e)}.
    have h_partition : ∃ S : Finset (Finset G.darts), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) ∧ (Finset.univ : Finset G.darts) = Finset.biUnion S id := by
      refine' ⟨ Finset.image ( fun e => { e, α e } ) Finset.univ, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
      · exact fun e => Finset.card_pair ( by specialize hα e; tauto );
      · grind only [= Finset.mem_insert, = Finset.mem_singleton]
      · ext e; simp [Finset.mem_biUnion, Finset.mem_image];
    obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_partition; rw [ hS₃, Finset.card_biUnion ] <;> aesop;
  exact h_even_card

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

theorem counterexample : ∃ (V : Type) (_ : Fintype V) (G : PlanarMap V), ¬ (Even G.χ) := by
  refine ⟨Fin 1, inferInstance, ⟨0, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨v, ⟨i, hi⟩⟩ <;> contradiction
  · rintro ⟨v, ⟨i, hi⟩⟩ ; contradiction
  · ext ⟨v, ⟨i, hi⟩⟩ <;> contradiction
  simp [χ, n_vertices]

-- example [Fintype V] : Even G.χ := by sorry

noncomputable def genus [Fintype V] (G : PlanarMap V) : ℤ :=
  (2 - G.χ) / 2

end PlanarMap
