import Mathlib.Order.Minimal

variable {α : Type*} [Preorder α] {n : ℕ}

def bad (A : ℕ → α) : Prop := ∀ i j, i < j → ¬ (A i ≤ A j)

def pref (X : Fin n → α) : Prop := ∃ A : ℕ → α, bad A ∧ ∀ i : Fin n, A i = X i

def concat (X : Fin n → α) (Xn : α) (i : Fin (n + 1)) : α := if h : i < n then X ⟨i, h⟩ else Xn

def concat' (X : Fin n → α) (Xn : α) : Fin (n + 1) → α := by
  intro i
  by_cases h : i < n
  · exact X ⟨i, h⟩
  · exact Xn

def nexts (X : Fin n → α) : Set α := { x | pref (concat X x) }

lemma nexts_nonempty (X : Fin n → α) (hX : pref X) : (nexts X).Nonempty := by
  obtain ⟨A, hA, hAX⟩ := hX
  exact ⟨A n, A, hA, by grind [concat]⟩

variable [WellFoundedLT α]

noncomputable def next (X : Fin n → α) (hX : pref X) : α :=
  Classical.choose (exists_minimal_of_wellFoundedLT (nexts X) (nexts_nonempty X hX))

lemma next_pref (X : Fin n → α) (hX : pref X) : Minimal (nexts X) (next X hX) :=
  Classical.choose_spec (exists_minimal_of_wellFoundedLT (nexts X) (nexts_nonempty X hX))

noncomputable def extend (X : { X : Fin n → α // pref X }) : { X : Fin (n + 1) → α // pref X } :=
  ⟨_, (next_pref X.val X.prop).prop⟩

noncomputable def minimize (A : ℕ → α) (hA : bad A) : (ℕ → α) := by
  let X0 : Fin 0 → α := fun i => by cases i ; contradiction
  have H0 : pref X0 := ⟨A, hA, by grind⟩
  let Y (n : ℕ) : { X : Fin n → α // pref X } :=
    Nat.recOn n ⟨X0, H0⟩ (fun n Yn => extend ⟨Yn, Yn.prop⟩)
  exact fun n => (Y (n + 1)).val ⟨n, by grind⟩
