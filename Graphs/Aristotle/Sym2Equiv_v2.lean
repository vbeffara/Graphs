/-
This file was edited by Aristotle.
This project request had uuid: 33f57c6c-367d-4826-a680-71fb6250c068
This project request had uuid: f4e158ce-8a16-4c2c-8d30-f25200f354fa
-/

import Mathlib

variable {α : Type*} [DecidableEq α]

def FinsetEquivSym2 : {s : Finset α // s.card = 2} ≃ {z : Sym2 α // ¬z.IsDiag} where
  toFun s := ⟨(Sym2.equivMultiset α).symm ⟨s.1.val, s.2⟩,
    by rcases s with ⟨s, hs⟩; rw [Finset.card_eq_two] at hs; aesop⟩
  invFun z := ⟨z.1.toFinset, Sym2.card_toFinset_of_not_isDiag _ z.2⟩
  left_inv := by
    rintro ⟨s, hs⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
    ext a ; simp ; erw [Sym2.mem_iff] ; simp [List.insert, hxy]
  right_inv s := by
    rcases s with ⟨⟨a, b⟩, hs⟩;
    rcases eq_or_ne a b with rfl | h
    · contradiction
    · have h_eq (a b : α) (hab : a ≠ b) : s(a, b).toFinset = {a, b} := by { ext; simp_all }
      simp_all ; rfl
