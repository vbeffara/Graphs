import Mathlib

open Fin

variable {α : Type*} {P : (ℕ → α) → Prop} {n : ℕ}

def pref (P : (ℕ → α) → Prop) (X : Fin n → α) : Prop := ∃ A : ℕ → α, P A ∧ ∀ i : Fin n, A i = X i

def concat (X : Fin n → α) (Xn : α) (i : Fin (n + 1)) : α := if h : i < n then X ⟨i, h⟩ else Xn

def next_vals (P : (ℕ → α) → Prop) (X : Fin n → α) : Set α := { x | pref P (concat X x) }

lemma nexts_nonempty (X : Fin n → α) (hX : pref P X) : (next_vals P X).Nonempty := by
  obtain ⟨A, hA, hAX⟩ := hX
  exact ⟨A n, A, hA, by grind [concat]⟩

noncomputable def next [Preorder α] [WellFoundedLT α] (P : (ℕ → α) → Prop) (X : Fin n → α) (hX : pref P X) : α :=
  Classical.choose (exists_minimal_of_wellFoundedLT (next_vals P X) (nexts_nonempty X hX))

lemma next_pref [Preorder α] [WellFoundedLT α] (P : (ℕ → α) → Prop) (X : Fin n → α) (hX : pref P X) :
    Minimal (next_vals P X) (next P X hX) :=
  Classical.choose_spec (exists_minimal_of_wellFoundedLT (next_vals P X) (nexts_nonempty X hX))

noncomputable def extend [Preorder α] [WellFoundedLT α] (X : { X : Fin n → α // pref P X }) :
    { X : Fin (n + 1) → α // pref P X } :=
  ⟨_, (next_pref P X.val X.prop).prop⟩

noncomputable def minimize [Preorder α] [WellFoundedLT α] (A : ℕ → α) (hA : P A) : (ℕ → α) := by
  let X0 : Fin 0 → α := fun i => by cases i ; contradiction
  have H0 : pref P X0 := ⟨A, hA, by grind⟩
  let Y (n : ℕ) : { X : Fin n → α // pref P X } :=
    Nat.recOn n ⟨X0, H0⟩ (fun n Yn => extend ⟨Yn, Yn.prop⟩)
  exact fun n => (Y (n + 1)).val ⟨n, by grind⟩

def IsQuasiMin [LT α] (f : ℕ → α) (S : Set (ℕ → α)) : Prop :=
  f ∈ S ∧ ∀ g ∈ S, ∀ n, (∀ m < n, g m = f m) → (g n < f n) → g ∉ S

namespace IsQuasiMin

abbrev Prefix (n : ℕ) (S : Set (ℕ → α)) := { f : Fin n → α | ∃ g ∈ S, ∀ k : Fin n, f k = g k }

def nexts (f : Prefix n P) := { g | g ∈ Prefix (n + 1) P ∧ g ∘ castSucc = f.1 }

lemma nexts_nonempty {f : Prefix n P} : (nexts f).Nonempty := by
  obtain ⟨f, g, h1, h2⟩ := f
  refine ⟨fun k => g k, ?_, ?_⟩ <;> grind [nexts]

theorem _root_.WellFounded.notMem_of_lt_min {r} {wf : WellFounded r} {s : Set α} {hs : s.Nonempty} {x : α}
    (hx : r x (wf.min s hs)) : x ∉ s :=
  (wf.not_lt_min s hs · hx)

noncomputable def step [Preorder α] [WellFoundedLT α] (f : Prefix n P) :
    { g // g ∈ Prefix (n + 1) P ∧ g ∘ castSucc = f.1 ∧ ∀ g' : Fin (n + 1) → α,
      g' ∘ castSucc = f.1 → g' (last _) < g (last _) → g' ∉ Prefix (n + 1) P } := by
  let s := nexts f
  have h1 : s.Nonempty := nexts_nonempty
  set g := IsWellFounded.wf.min (r := LT.lt) s h1 with hg
  have h2 : g ∈ s := IsWellFounded.wf.min_mem (r := LT.lt) s h1
  refine ⟨g, h2.1, h2.2, ?_⟩
  rintro g' h3 h4 h5
  have h6 : g' ∈ s := ⟨h5, h3⟩
  have h7 := IsWellFounded.wf.not_lt_min (r := LT.lt) s h1 h6
  apply h7
  simp [Pi.lt_def, Pi.le_def]
  refine ⟨fun i => ?_, by grind⟩
  · obtain (⟨j, rfl⟩ | rfl) := eq_castSucc_or_eq_last i
    · have h8 : g j.castSucc = f.1 j := congr_fun h2.2 j
      have h9 : g' j.castSucc = f.1 j := congr_fun h3 j
      grind
    · grind

noncomputable def minimize [Preorder α] [WellFoundedLT α] {f} (hf : P f) (n : ℕ) : α := by
  let X0 : Prefix 0 P := ⟨elim0, ⟨f, hf, by simp⟩⟩
  let φ n : Prefix n P := Nat.recOn n X0 (fun n Xn => ⟨_, (step Xn).2.1⟩)
  exact (φ _).1 (last n)

theorem exists_quasiMin [Preorder α] [WellFoundedLT α] {f} (hf : P f) : IsQuasiMin (minimize hf) P := by
  constructor
  · sorry
  · sorry

end IsQuasiMin
