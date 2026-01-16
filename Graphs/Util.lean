import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Find

variable {m n : ℕ} {p : ℕ → Prop} [DecidablePred p] {h1 : ∃ n, p n} {h2 : ∃ N, ∀ n, p n → n ≤ N}

-- Find the last natural number `n` satisfying a predicate `p`
noncomputable def Nat.find' (_ : ∃ n, p n) (h2 : ∃ N, ∀ n, p n → n ≤ N) : ℕ :=
  Nat.findGreatest p (Classical.choose h2)

theorem find'_spec : p (Nat.find' h1 h2) := by
  obtain ⟨m, hm⟩ := h1
  exact Nat.findGreatest_spec (Classical.choose_spec h2 m hm) hm

theorem le_find' (hn : p n) : n ≤ Nat.find' h1 h2 :=
  Nat.le_findGreatest (Classical.choose_spec h2 n hn) hn

theorem find'_le (hm : ∀ n, p n → n ≤ m) : Nat.find' h1 h2 ≤ m :=
  hm _ find'_spec

theorem findGreatest_le_find' : Nat.findGreatest p m ≤ Nat.find' h1 h2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    by_cases h' : p (n + 1) <;> rw [Nat.findGreatest_succ] <;> simp only [h', ↓reduceIte]
    · exact le_find' h'
    · exact ih

theorem findGreatest_eq_find' (hm : ∀ n, p n → n ≤ m) : Nat.findGreatest p m = Nat.find' h1 h2 := by
  refine Nat.findGreatest_eq_iff.mpr ⟨hm _ find'_spec, fun _ => find'_spec, fun n hn hmn => ?_⟩
  contrapose! hn ; exact le_find' hn

theorem find_le_find' : Nat.find h1 ≤ Nat.find' h1 h2 :=
  le_find' $ Nat.find_spec h1
