import Mathlib

-- open Classical

variable {m n : ℕ} {p : ℕ → Prop} [DecidablePred p] {h1 : ∃ n, p n} {h2 : ∃ N, ∀ n, p n → n ≤ N}

-- Find the last natural number `n` satisfying a predicate `p`
noncomputable def find' (_ : ∃ n, p n) (h2 : ∃ N, ∀ n, p n → n ≤ N) : ℕ :=
  Nat.findGreatest p (Classical.choose h2)

theorem find'_spec : p (find' h1 h2) := by
  obtain ⟨m, hm⟩ := h1
  exact Nat.findGreatest_spec (Classical.choose_spec h2 m hm) hm

theorem le_find' (hn : p n) : n ≤ find' h1 h2 :=
  Nat.le_findGreatest (Classical.choose_spec h2 n hn) hn

theorem findGreatest_le_find' : Nat.findGreatest p m ≤ find' h1 h2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    by_cases h' : p (n + 1) <;> rw [Nat.findGreatest_succ] <;> simp only [h', ↓reduceIte]
    · exact le_find' h'
    · exact ih

theorem find_le_find' : Nat.find h1 ≤ find' h1 h2 :=
  le_find' $ Nat.find_spec h1

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
