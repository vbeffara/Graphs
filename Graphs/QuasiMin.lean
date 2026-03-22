import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Minimal

open Fin Nat

variable {α : Type*} [Preorder α] {P : (ℕ → α) → Prop} {f f' : ℕ → α} {hf : P f} {m n k : ℕ}

def MinAt (P : (ℕ → α) → Prop) (n : ℕ) (f : ℕ → α) : Prop :=
    ∀ g, (∀ m < n, g m = f m) → (g n < f n) → ¬ P g

theorem MinAt_of_eq (hf : MinAt P n f) (h : ∀ k ≤ n, f' k = f k) : MinAt P n f' := by grind [MinAt]

def MinUntil (P : (ℕ → α) → Prop) (n : ℕ) (f : ℕ → α) : Prop := ∀ k < n, MinAt P k f

def QuasiMin (P : (ℕ → α) → Prop) (f : ℕ → α) : Prop := ∀ n, MinAt P n f

variable [WellFoundedLT α]

noncomputable def extendAt (P : (ℕ → α) → Prop) (hf : P f) (n : ℕ) :
    { g : ℕ → α // P g ∧ (∀ m < n, g m = f m) ∧ MinAt P n g } := by
  let good (x : α) : Prop := ∃ g, P g ∧ (∀ m < n, g m = f m) ∧ g n = x
  choose x h3 h4 using exists_minimal_of_wellFoundedLT good ⟨f n, ⟨f, hf, by simp⟩⟩
  obtain ⟨h5, h6, h7⟩ := Classical.choose_spec h3
  refine ⟨_, h5, h6, fun g h8 h9 h10 => ?_⟩
  have h11 : good (g n) := ⟨g, h10, fun m hm => by simp [h6, h8, hm], rfl⟩
  specialize h4 h11 ; grind

noncomputable def extendAux (P : (ℕ → α) → Prop) (hf : P f) : ∀ m, { g : ℕ → α // P g ∧ MinUntil P m g }
  | 0 => ⟨f, hf, by tauto⟩
  | m + 1 => by
    let g := extendAux P hf m
    use extendAt P g.2.1 m
    obtain ⟨g', h3, h4, h5⟩ := extendAt P g.2.1 m
    refine ⟨h3, fun k hk => ?_⟩
    obtain (h | h) := Nat.lt_succ_iff_lt_or_eq.1 hk
    · exact MinAt_of_eq (g.2.2 k h) (by grind)
    · grind

theorem extendAux_next (hk : k < n) : (extendAux P hf (n + 1)).1 k = (extendAux P hf n).1 k :=
  (extendAt P (extendAux P hf n).2.1 n).2.2.1 k hk

theorem extendAux_later (hk : k < n) (hm : n ≤ m) : (extendAux P hf m).1 k = (extendAux P hf n).1 k := by
  induction m, hm using le_induction with
  | base => rfl
  | succ m hm ih => rwa [extendAux_next (by omega)]

noncomputable def extend (P : (ℕ → α) → Prop) (hf : P f) (n : ℕ) : α := (extendAux P hf (n + 1)).1 n

theorem extend_eq (hk : k ≤ n) : extend P hf k = (extendAux P hf (n + 1)).1 k := by
  rw [extend, eq_comm, extendAux_later] <;> omega

theorem extend_quasiMin : QuasiMin P (extend P hf) :=
  fun n => MinAt_of_eq ((extendAux P hf (n + 1)).2.2 n (by grind)) (by grind [extend_eq])

def localProp (P : (ℕ → α) → Prop) := ∀ ⦃f⦄, (∀ n, ∃ g, P g ∧ ∀ k < n, g k = f k) → P f

theorem extend_spec (hP : localProp P) : P (extend P hf) := by
  refine hP (fun n => ⟨extendAux P hf n, (extendAux P hf n).2.1, fun k hk => ?_⟩)
  apply extendAux_later <;> omega

theorem exists_quasiMin (hP : localProp P) (h : ∃ f, P f) : ∃ f, P f ∧ QuasiMin P f := by
  obtain ⟨f, hf⟩ := h
  refine ⟨extend P hf, extend_spec hP, extend_quasiMin⟩
