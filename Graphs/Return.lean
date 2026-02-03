import Mathlib

open Equiv Classical Function MulAction Set

variable {V : Type*} {f : Perm V} {s : Set V} {x y : V} {n : ℕ}

def IsRecurrent (f : Perm V) (s : Set V) : Prop := ∀ x : s, ∃ n, (f ^ n) (f x) ∈ s

theorem isRecurrent_of_cofinite (hs : sᶜ.Finite) : IsRecurrent f s := by
  rintro ⟨x, hx⟩
  by_contra! (h : ∀ (n : ℕ), (f ^ n) (f x) ∈ sᶜ)
  obtain ⟨a, b, hab, hfab⟩ := hs.exists_lt_map_eq_of_forall_mem h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
  rw [add_assoc, add_comm k 1, ← add_assoc, pow_add, Perm.mul_apply, ← Perm.mul_apply, ← pow_succ,
    EmbeddingLike.apply_eq_iff_eq] at hfab
  rw [hfab] at hx
  specialize h k
  contradiction

noncomputable def next_return (hs : IsRecurrent f s) (x : s) : s :=
  ⟨_, Nat.find_spec (hs x)⟩

theorem next_return_iff (x y : s) (hs : IsRecurrent f s) : next_return hs x = y ↔
    ∃ n, y = (f ^ (n + 1)) x ∧ ∀ m < n, (f ^ (m + 1)) x ∉ s := by
  constructor
  · rintro rfl ; exact ⟨Nat.find (hs x), rfl, fun m => Nat.find_min _⟩
  · obtain ⟨y, hy⟩ := y
    rintro ⟨n, rfl, hn⟩
    simp [← Nat.find_eq_iff (hs x) |>.mpr ⟨hy, hn⟩]
    rfl

noncomputable def returns (hs : IsRecurrent f s) (hs' : IsRecurrent f⁻¹ s) : Perm s where
  toFun := next_return hs
  invFun := next_return hs'
  left_inv x := by
    obtain ⟨n, h1, h2⟩ := next_return_iff x (next_return hs x) hs |>.mp rfl
    rw [next_return_iff, h1]
    refine ⟨n, by simp, fun m hm => ?_⟩
    rw [← Perm.mul_apply]
    convert h2 (n - m - 1) (by omega) using 3
    group ; congr 1 ; omega
  right_inv x := by
    obtain ⟨n, h1, h2⟩ := next_return_iff x (next_return hs' x) hs' |>.mp rfl
    rw [next_return_iff, h1]
    refine ⟨n, by simp, fun m hm => ?_⟩
    rw [← Perm.mul_apply]
    convert h2 (n - m - 1) (by omega) using 3
    group ; congr 1 ; omega
