import Mathlib

open Matrix

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

def ExactlyOneOf (P Q : Prop) : Prop := (P ∧ ¬Q) ∨ (¬P ∧ Q)

theorem exactlyOneOf_iff {P Q : Prop} : ExactlyOneOf P Q ↔ (P ↔ ¬Q) := by
  simp [ExactlyOneOf] ; tauto

theorem exactlyOneOf_iff' {P Q : Prop} : ExactlyOneOf P Q ↔ (¬(P ∧ Q) ∧ (¬P → Q)) := by
  simp [ExactlyOneOf] ; tauto

theorem FarkasLemma (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : ExactlyOneOf
    (∃ x : Fin n → ℝ, (A *ᵥ x = b) ∧ (0 ≤ x))
    (∃ y : Fin m → ℝ, (0 ≤ y ᵥ* A) ∧ (y ⬝ᵥ b < 0)) := by
  rw [exactlyOneOf_iff'] ; constructor
  · rintro ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₁, hy₂⟩⟩
    have := calc 0 ≤ (y ᵥ* A) ⬝ᵥ x := dotProduct_nonneg_of_nonneg hy₁ hx₂
                 _ = y ⬝ᵥ (A *ᵥ x) := (dotProduct_mulVec y A x).symm
                 _ = y ⬝ᵥ b := by rw [hx₁]
                 _ < 0 := hy₂
    linarith
  · sorry
