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
  · intro h
    let K := { y : Fin m → ℝ | ∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = y }
    have s1 : b ∉ K := by grind
    have s2 : IsClosed K := sorry
    have s3 : K.Nonempty := ⟨0, 0, le_rfl, mulVec_zero A⟩
    obtain ⟨p, ⟨w, hw₁, rfl⟩, hp₂⟩ := s2.exists_infDist_eq_dist s3 b
    have s4 : ∀ x ≥ 0, (b - A *ᵥ w) ⬝ᵥ (A *ᵥ x - A *ᵥ w) ≤ 0 := sorry -- Geometric lemma
    let y := A *ᵥ w - b
    have s5 : ∀ x ≥ 0, 0 ≤ y ⬝ᵥ (A *ᵥ (x - w)) := by
      intro x hx
      dsimp [y]
      rw [Matrix.mulVec_sub, ← neg_sub, neg_dotProduct]
      linarith [s4 x hx]
    let e (i : Fin n) : Fin n → ℝ := fun j => if j = i then 1 else 0
    let x (i : Fin n) := w + e i
    have s6 : ∀ i, 0 ≤ y ⬝ᵥ (A *ᵥ e i) := sorry
    have s7 : ∀ i, 0 ≤ (y ᵥ* A) i := sorry
    have s8 : 0 ≤ y ᵥ* A := s7
    have s9 : y ⬝ᵥ b = y ⬝ᵥ (A *ᵥ w) - y ⬝ᵥ y := sorry
    have s10 : y ⬝ᵥ (A *ᵥ w) ≤ 0 := sorry
    have s11 : y ⬝ᵥ (A *ᵥ w) - y ⬝ᵥ y < 0 := sorry
    exact ⟨y, s8, by linarith⟩
