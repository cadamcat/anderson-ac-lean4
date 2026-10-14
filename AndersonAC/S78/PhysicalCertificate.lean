import AndersonAC.S78.Definitions

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

def activeSchur {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (A : Finset ι) : Matrix A A ℂ :=
  B.submatrix (fun i : A => i.val) (fun i : A => i.val) -
    B.submatrix (fun i : A => i.val) (fun i : {i // i ∉ A} => i.val) *
      (B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val))⁻¹ *
      B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : A => i.val)

/-- Invertible true terminal data and an active Schur inverse supply a full
physical inverse whose retained entries are exactly the active inverse. -/
theorem inverse_from_active_schur {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (A : Finset ι) (g : Matrix A A ℂ)
    (hT : IsUnit (B.submatrix (fun i : {i // i ∉ A} => i.val)
      (fun i : {i // i ∉ A} => i.val)).det)
    (hG : activeSchur B A * g = 1 ∧ g * activeSchur B A = 1) :
    ∃ G : Matrix ι ι ℂ, B * G = 1 ∧ G * B = 1 ∧
      ∀ i j : A, G i.val j.val = g i j := by
  classical
  let T := {i : ι // i ∉ A}
  let U := B.submatrix (fun i : A => i.val) (fun i : A => i.val)
  let V := B.submatrix (fun i : A => i.val) (fun i : T => i.val)
  let W := B.submatrix (fun i : T => i.val) (fun i : A => i.val)
  let D := B.submatrix (fun i : T => i.val) (fun i : T => i.val)
  let S := activeSchur B A
  let e : A ⊕ T ≃ ι := Equiv.Set.sumCompl (A : Set ι)
  have hblock : B.submatrix e e = Matrix.fromBlocks U V W D := by
    ext i j
    cases i <;> cases j <;> rfl
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D hT
  letI : Invertible S := invertibleOfLeftInverse _ _ hG.2
  have hS : U - V * ⅟D * W = S := by
    rw [Matrix.invOf_eq_nonsing_inv]
    rfl
  letI : Invertible (U - V * ⅟D * W) := by rw [hS]; infer_instance
  letI : Invertible (Matrix.fromBlocks U V W D) := Matrix.fromBlocks₂₂Invertible U V W D
  have hunit : IsUnit B := by
    apply (Matrix.isUnit_submatrix_equiv e e).mp
    rw [hblock]
    exact isUnit_of_invertible _
  have hdet := (Matrix.isUnit_iff_isUnit_det B).mp hunit
  refine ⟨B⁻¹, Matrix.mul_nonsing_inv B hdet, Matrix.nonsing_inv_mul B hdet, ?_⟩
  intro i j
  have hinv : (B⁻¹).submatrix e e = (Matrix.fromBlocks U V W D)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv B e e, hblock]
  have htop := congrArg (fun K : Matrix (A ⊕ T) (A ⊕ T) ℂ => K (Sum.inl i) (Sum.inl j))
    (Matrix.invOf_fromBlocks₂₂_eq U V W D)
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.fromBlocks_apply₁₁] at htop
  change (Matrix.fromBlocks U V W D)⁻¹ (Sum.inl i) (Sum.inl j) = S⁻¹ i j at htop
  rw [Matrix.inv_eq_right_inv hG.1] at htop
  have hentry := congrArg (fun K : Matrix (A ⊕ T) (A ⊕ T) ℂ => K (Sum.inl i) (Sum.inl j)) hinv
  change B⁻¹ i.val j.val = (Matrix.fromBlocks U V W D)⁻¹ (Sum.inl i) (Sum.inl j) at hentry
  exact hentry.trans htop

/-- The final physical Schur identity directly yields the frozen bounded
certificate feasibility event. This does not require a measurable choice of
the full inverse or of the certificate witnesses. -/
theorem bounded_certificate_of_active_schur (d n₀ m : ℕ) (u E Cr cp cg : ℝ)
    (ω : OAI.Anderson.TorusConfiguration d m) (A : Finset (Torus d m))
    (r : Torus d m → ℂ) (g : Matrix A A ℂ)
    (hcard : Fintype.card (Torus d m) ≤ 2 * A.card)
    (hr : ∀ i ∈ A, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im)
    (hT : IsUnit ((OAI.Anderson.certificateMatrix n₀ m u E ω A r).submatrix
      (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val)).det)
    (hG : activeSchur (OAI.Anderson.certificateMatrix n₀ m u E ω A r) A * g = 1 ∧
      g * activeSchur (OAI.Anderson.certificateMatrix n₀ m u E ω A r) A = 1)
    (hg : ∀ i : A, cg ≤ (g i i).im) :
    ω ∈ boundedCertificateEvent d n₀ m u E Cr cp cg := by
  obtain ⟨G, hBG, hGB, hentry⟩ := inverse_from_active_schur
    (OAI.Anderson.certificateMatrix n₀ m u E ω A r) A g hT hG
  refine ⟨A, r, G, hcard, hr, hBG, hGB, ?_⟩
  intro i hi
  have he := hentry ⟨i, hi⟩ ⟨i, hi⟩
  rw [he]
  exact hg ⟨i, hi⟩

/-- The last sweep's damped endpoint and diagonal-lag bound give the
certificate once its matrix is the physical active Schur block.
This is the deterministic join in `08-history.tex:378–392`. -/
theorem bounded_certificate_of_final_endpoint (d n₀ m : ℕ) (u E Cr cp cg t : ℝ)
    (ω : OAI.Anderson.TorusConfiguration d m) (s : Endpoint (Torus d m))
    (r : Torus d m → ℂ) (hs : IsDampedEndpoint s r t)
    (hcard : Fintype.card (Torus d m) ≤ 2 * s.active.card)
    (hr : ∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im)
    (hlag : ∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)
    (hT : IsUnit ((OAI.Anderson.certificateMatrix n₀ m u E ω s.active r).submatrix
      (fun i : {i // i ∉ s.active} => i.val)
      (fun i : {i // i ∉ s.active} => i.val)).det)
    (hSchur : activeSchur (OAI.Anderson.certificateMatrix n₀ m u E ω s.active r) s.active =
      s.M.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) -
        (t : ℂ) • Matrix.diagonal (fun i : s.active => r i.val)) :
    ω ∈ boundedCertificateEvent d n₀ m u E Cr cp cg := by
  apply bounded_certificate_of_active_schur d n₀ m u E Cr cp cg ω s.active r
    (s.g.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val)) hcard hr hT
  · rw [hSchur]
    exact hs.2.2
  · intro i
    have him : |(s.g i.val i.val).im - (r i.val).im| ≤ cp - cg := by
      simpa only [Complex.sub_im] using
        (Complex.abs_im_le_norm (s.g i.val i.val - r i.val)).trans
          (hlag i.val i.property)
    have hlow := (abs_le.mp him).1
    have hrim := (hr i.val i.property).2
    change cg ≤ (s.g i.val i.val).im
    linarith

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.inverse_from_active_schur
#print axioms AndersonAC.SolS78.bounded_certificate_of_active_schur
#print axioms AndersonAC.SolS78.bounded_certificate_of_final_endpoint
