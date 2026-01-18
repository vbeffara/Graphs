import Mathlib

open Matrix Metric

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

def ExactlyOneOf (P Q : Prop) : Prop := (P ∧ ¬Q) ∨ (¬P ∧ Q)

theorem exactlyOneOf_iff {P Q : Prop} : ExactlyOneOf P Q ↔ (P ↔ ¬Q) := by
  simp [ExactlyOneOf] ; tauto

theorem exactlyOneOf_iff' {P Q : Prop} : ExactlyOneOf P Q ↔ (¬(P ∧ Q) ∧ (¬P → Q)) := by
  simp [ExactlyOneOf] ; tauto

@[reducible] def V (n : ℕ) := PiLp 2 (fun _ : Fin n => ℝ)

theorem HB₀ (K : Set (V n)) (b : V n) (hK1 : Convex ℝ K) (hK2 : IsClosed K) (hK3 : K.Nonempty) :
    ∃ p ∈ K, ∀ x ∈ K, inner ℝ (b - p) (x - p) ≤ 0 := by
  obtain ⟨p, hp₁, hp₂⟩ := hK2.exists_infDist_eq_dist hK3 b
  refine ⟨p, hp₁, norm_eq_iInf_iff_real_inner_le_zero hK1 hp₁ |>.mp ?_⟩
  simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp₂.symm

theorem HB (K : Set (Fin n → ℝ)) (b : Fin n → ℝ) (hK1 : Convex ℝ K) (hK2 : IsClosed K)
    (hK3 : K.Nonempty) (hb : b ∉ K) : ∃ p ∈ K, ∀ x ∈ K, (b - p) ⬝ᵥ (x - p) ≤ 0 := by
  let φ : (Fin n → ℝ) → (V n) := WithLp.toLp 2
  let ψ : (V n) → (Fin n → ℝ) := WithLp.ofLp
  have h1 : Convex ℝ (φ '' K) := sorry
  have h2 : IsClosed (φ '' K) := sorry
  have h3 : (φ '' K).Nonempty := sorry
  obtain ⟨q, ⟨p, hp, rfl⟩, hq₂⟩ := HB₀ (φ '' K) (φ b) h1 h2 h3
  refine ⟨p, hp, fun x hx => ?_⟩
  specialize hq₂ (φ x) ⟨x, hx, rfl⟩
  rw [EuclideanSpace.inner_toLp_toLp] at hq₂
  simpa only [WithLp.ofLp_sub, star_trivial, φ, dotProduct_comm] using hq₂

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
    let K := ImgCone A
    have s1 : b ∉ K := by rintro ⟨x, hx1, hx2⟩ ; exact h ⟨x, hx2, hx1⟩
    have s2 : IsClosed K.carrier := K.isClosed
    have s14 : Convex ℝ K.carrier := K.convex
    have s3 : K.carrier.Nonempty := K.nonempty
    obtain ⟨p, ⟨w, hw₁, rfl⟩, hw₂⟩ := HB K b s14 s2 s3 s1
    have s4 : ∀ x ≥ 0, (b - A *ᵥ w) ⬝ᵥ (A *ᵥ x - A *ᵥ w) ≤ 0 := by
      intro x hx
      exact hw₂ (A *ᵥ x) ⟨x, hx, rfl⟩
    let y := A *ᵥ w - b
    have s5 : ∀ x ≥ 0, 0 ≤ y ⬝ᵥ (A *ᵥ (x - w)) := by
      intro x hx
      dsimp [y]
      rw [Matrix.mulVec_sub, ← neg_sub, neg_dotProduct]
      linarith [s4 x hx]
    let e (i : Fin n) : Fin n → ℝ := fun j => if j = i then 1 else 0
    let x (i : Fin n) := w + e i
    have s12 : ∀ i, e i = x i - w := by simp [x]
    have s13 : ∀ i, 0 ≤ x i := by
      intro i j
      simp [x, e]
      split_ifs <;> specialize hw₁ j <;> simp at hw₁ <;> linarith
    have s6 : ∀ i, 0 ≤ y ⬝ᵥ (A *ᵥ e i) := by
      intro i
      rw [s12]
      exact s5 (x i) (s13 i)
    have s7 : ∀ i, 0 ≤ (y ᵥ* A) i := by
      intro i
      convert s6 i
      simp [dotProduct_mulVec]
      simp only [dotProduct, e]
      rw [Finset.sum_eq_single i]
      · simp [↓reduceIte]
      · simp ; grind
      · simp
    have s8 : 0 ≤ y ᵥ* A := s7
    have s9 : y ⬝ᵥ b = y ⬝ᵥ (A *ᵥ w) - y ⬝ᵥ y := by simp [y]
    have s10 : y ⬝ᵥ (A *ᵥ w) ≤ 0 := by
      have := s4 0 le_rfl
      simp at this
      simpa [y]
    have s14 : y ⬝ᵥ y > 0 := by
      have r3 : A *ᵥ w ∈ K := ⟨w, hw₁, rfl⟩
      have r4 : A *ᵥ w ≠ b := by contrapose s1 ; simpa [← s1]
      have r5 : y ≠ 0 := by simp [y, sub_eq_zero, r4]
      exact Matrix.dotProduct_star_self_pos_iff.mpr r5
    have s11 : y ⬝ᵥ (A *ᵥ w) - y ⬝ᵥ y < 0 := by linarith
    exact ⟨y, s8, by linarith⟩

theorem isClosed_cone_of_ball (C : PointedCone ℝ (V n)) (hC : IsClosed (closedBall 0 1 ∩ C.carrier)) :
    IsClosed C.carrier := by
  let C' := (ball 0 1)ᶜ ∩ C.carrier
  suffices h : IsClosed C'
  · convert hC.union h ; ext ; simp [C'] ; grind
  let f : V n → V n := fun x => (1 / ‖x‖) • x
  have h1 : ContinuousOn f (ball 0 1)ᶜ := by
    have s0 : (∀ x ∈ Set.Ici (1 : ℝ), id x ≠ 0) := by grind
    have s1 : ContinuousOn (fun (x : ℝ) ↦ 1 / x) (Set.Ici 1) := by
      have := @ContinuousOn.inv₀ ℝ ℝ _ _ _ _ id (Set.Ici 1) _ continuousOn_id s0
      simp_rw [inv_eq_one_div] at this
      exact this
    have s2 : Set.MapsTo (fun (x : V n) ↦ ‖x‖) (ball 0 1)ᶜ (Set.Ici 1) := by simp [Set.MapsTo]
    exact ContinuousOn.smul (s1.comp continuous_norm.continuousOn s2) continuousOn_id
  have h2 : IsClosed (ball (0 : V n) 1)ᶜ := by simp only [isClosed_compl_iff, isOpen_ball]
  have key := h1.preimage_isClosed_of_isClosed h2 hC
  convert key using 1
  ext x
  simp [C', f, norm_smul]
  intro hx
  have h3 : ‖x‖ ≠ 0 := by linarith
  simp [h3]
  constructor
  · apply C.smul_mem
    positivity
  · intro h
    simpa [smul_smul, h3] using C.smul_mem (r := ‖x‖) (by positivity) h

theorem coneclosed (S : Finset (V n)) : IsClosed (PointedCone.span ℝ (S : Set (V n))).carrier := by
  induction S using Finset.induction with
  | empty => simpa using isClosed_singleton
  | insert a s _ _ =>
    simp [PointedCone.span, Submodule.span_insert]
    sorry






























--
