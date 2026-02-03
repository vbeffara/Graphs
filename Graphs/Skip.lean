import Mathlib

open Equiv Classical Function MulAction Set

variable {V : Type*} {f : Perm V} {s : Set V}

def IsRecurrent (f : Perm V) (s : Set V) : Prop := ∀ x : s, ∃ n, (f ^ n) (f x) ∈ s

theorem isRecurrent_of_cofinite (hs : sᶜ.Finite) : IsRecurrent f s := by
  rintro ⟨x, hx⟩
  by_contra! (h : ∀ (n : ℕ), (f ^ n) (f x) ∈ sᶜ)
  obtain ⟨a, b, hab, hfab⟩ := hs.exists_lt_map_eq_of_forall_mem h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have key : (f ^ (a + 1)) x = (f ^ (a + 1)) ((f ^ (k + 1)) x) := by calc
    (f ^ (a + 1)) x = (f ^ (a + k + 1)) (f x) := hfab
    _ = (f ^ ((a + 1) + k)) (f x) := by ring_nf
    _ = ((f ^ (a + 1)) * (f ^ k)) (f x) := by rw [pow_add]
    _ = (f ^ (a + 1)) ((f ^ k) (f x)) := by rw [Perm.mul_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq] at key
  rw [key] at hx
  specialize h k
  contradiction

noncomputable def next_return (hs : IsRecurrent f s) (x : s) : s :=
  ⟨_, Nat.find_spec (hs x)⟩

noncomputable def returns (hs : IsRecurrent f s) (hs' : IsRecurrent f⁻¹ s) :
    Perm s where
  toFun := next_return hs
  invFun := next_return hs'
  left_inv x := sorry
  right_inv := sorry
