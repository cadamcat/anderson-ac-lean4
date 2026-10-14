import AndersonAC.S78Var.NormalizedInverse
import AndersonAC.S78Var.CommutatorBounds
import AndersonAC.S78Var.KernelBound
import AndersonAC.S78Var.WardRows
import AndersonAC.S78.ResetVariation

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix AndersonAC.SolS78Var
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

set_option maxHeartbeats 1000000 in
/-- Constants are chosen before the active set, including the nonconstant Ward weights. -/
theorem reset_variation_proof : ResetVariation := by
  intro hWard c C hc hC
  classical
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let Rh := C / c
  let Rh' := 4 * C / c
  let D := Real.sqrt Rh' / c
  let E := Real.sqrt (Rh' * Rh)
  let K := D * (Real.sqrt Rh' + Real.sqrt Rh)
  let F := Real.sqrt (E * D)
  let Q := (Real.sqrt C * (Real.sqrt c)⁻¹ + 1) / c
  let Ct := 128 * (Q + D + E + K + F + 1)
  have hRh0 : 0 ≤ Rh := by dsimp [Rh]; positivity
  have hRh'0 : 0 ≤ Rh' := by dsimp [Rh']; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hCt0 : 0 < Ct := by dsimp [Ct]; positivity
  have hDCt : D ≤ Ct := by dsimp only [Ct]; linarith
  have hECt : E ≤ Ct := by dsimp only [Ct]; linarith
  have hKCt : K ≤ Ct := by dsimp only [Ct]; linarith
  have hFCt : F ≤ Ct := by dsimp only [Ct]; linarith
  have hQCt : 126 * Q ≤ Ct := by dsimp only [Ct]; linarith
  have hQc : 1 ≤ Q * c := by
    have he : Q * c = Real.sqrt C * (Real.sqrt c)⁻¹ + 1 := by
      dsimp [Q]; field_simp
    rw [he]
    have hh : 0 ≤ Real.sqrt C * (Real.sqrt c)⁻¹ := by positivity
    linarith
  refine ⟨Ct, min (min (c / 2) C) (1 / (2 * Ct)), hCt0, by positivity, ?_⟩
  intro ι _ _ _ M r ζ t ht hsym hdamp hdiag hsmall hfix
  let ρ := ‖ζ‖
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρc : ρ ≤ c / 2 := hsmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρC : ρ ≤ C := hsmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρCt : ρ ≤ 1 / (2 * Ct) := hsmall.trans (min_le_right _ _)
  have hCtρ : Ct * ρ ≤ 1 / 2 := by
    calc Ct * ρ ≤ Ct * (1 / (2 * Ct)) := mul_le_mul_of_nonneg_left hρCt hCt0.le
      _ = 1 / 2 := by field_simp
  have hdamp' : ∀ i, c / 2 ≤ ((r + ζ) i).im ∧ ((r + ζ) i).im ≤ 2 * C := by
    intro i
    have him : |(ζ i).im| ≤ ρ := (Complex.abs_im_le_norm _).trans (norm_le_pi_norm ζ i)
    have hlow := (hdamp i).1
    have hhigh := (hdamp i).2.1
    simp only [Pi.add_apply, Complex.add_im]
    constructor
    · linarith [neg_abs_le (ζ i).im]
    · linarith [le_abs_self (ζ i).im]
  obtain ⟨G, hInv, hSym, hNorm, hWardEq⟩ := wardInverseOn hWard M t r c ht
    (fun i j => (hsym i j).1) (fun i j => (hsym i j).2) hc (fun i => (hdamp i).1)
  obtain ⟨G', hInv', hSym', _, hWardEq'⟩ := wardInverseOn hWard M t (r + ζ) (c / 2) ht
    (fun i j => (hsym i j).1) (fun i j => (hsym i j).2) (by positivity)
    (fun i => (hdamp' i).1)
  have hg : AndersonAC.S78.resetInverse M r t = G := resetInverse_eq_ward M r t G hInv
  have hg' : AndersonAC.S78.resetInverse M (r + ζ) t = G' := resetInverse_eq_ward M (r + ζ) t G' hInv'
  have hfixG : ∀ i, G' i i = (r + ζ) i := by simpa only [hg'] using hfix
  let s := Real.sqrt t
  let h := (s : ℂ) • G
  let h' := (s : ℂ) • G'
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hsnorm : ‖(s : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le]
  have hsymh : h.transpose = h := by simpa only [h, Matrix.transpose_smul, hSym]
  have hsymh' : h'.transpose = h' := by simpa only [h', Matrix.transpose_smul, hSym']
  have hrow : ∀ i, AndersonAC.S78.rowTwo h i ≤ Rh := by
    intro i
    apply ward_rowTwo_bound G t r c C ht hc (fun k => (hdamp k).1) hWardEq i
    simpa only [hg] using hdiag i
  have hrow' : ∀ i, AndersonAC.S78.rowTwo h' i ≤ Rh' := by
    intro i
    calc AndersonAC.S78.rowTwo h' i ≤ (2 * C) / (c / 2) := by
          apply ward_rowTwo_bound G' t (r + ζ) (c / 2) (2 * C) ht (by positivity)
            (fun k => (hdamp' k).1) hWardEq' i
          rw [hfixG i]
          exact (hdamp' i).2
      _ = Rh' := by dsimp [Rh']; field_simp; ring
  have hOp : ‖h‖ ≤ 1 / (s * c) := by
    calc ‖h‖ = s * ‖G‖ := by
          calc ‖h‖ = ‖(s : ℂ)‖ * ‖G‖ := norm_smul (s : ℂ) G
            _ = s * ‖G‖ := by rw [hsnorm]
      _ ≤ s * (t * c)⁻¹ := mul_le_mul_of_nonneg_left hNorm hs.le
      _ = 1 / (s * c) := by
          dsimp [s]
          field_simp
          rw [Real.sq_sqrt ht.le]
  have hRes := resolvent_identity M r ζ t G G' hInv hInv'
  have hΔ := normalized_delta_entries G G' ζ t ht.le hRes
  have hdelta : ∀ i, Real.sqrt (AndersonAC.S78.rowTwo (h' - h) i) ≤ D * ρ := by
    intro i
    calc Real.sqrt (AndersonAC.S78.rowTwo (h' - h) i)
        ≤ (1 / (s * c)) * Real.sqrt Rh' * ρ * s :=
          delta_sqrt_rowTwo_bound h h' ζ t ht hsymh (1 / (s * c)) (by positivity)
            hOp Rh' hRh'0 hrow' hΔ i
      _ = D * ρ := by dsimp [D]; field_simp [ne_of_gt hs]
  have hentry : ∀ i j, ‖(h' - h) i j‖ ≤ E * s * ρ := by
    intro i j
    calc ‖(h' - h) i j‖ ≤ Real.sqrt (Rh' * Rh) * ρ * s :=
          delta_entry_bound h h' ζ t ht hsymh Rh Rh' hRh0 hRh'0 hrow hrow' hΔ i j
      _ = E * s * ρ := by dsimp [E]; ring
  have hfour : ∀ i, (AndersonAC.S78.rowFour (h' - h) i) ^ (1 / 4 : ℝ) ≤ F * t ^ (1 / 4 : ℝ) * ρ :=
    fun i => fourth_root_row_bound (h' - h) i t ρ E D ht.le hρ0 hE0 hD0 (hentry i) (hdelta i)
  have hkernel : AndersonAC.S78.matrixNorm (AndersonAC.S78.squareKernel h' - AndersonAC.S78.squareKernel h) ≤ K * ρ := by
    calc _ ≤ (D * ρ) * (Real.sqrt Rh' + Real.sqrt Rh) :=
          kernel_difference_bound h h' hsymh hsymh' Rh Rh' (D * ρ) hRh0 hRh'0 (by positivity) hrow hrow' hdelta
      _ = K * ρ := by dsimp [K]; ring
  -- Normalize the inverse perturbation before invoking the accepted commutator theorem.
  let z := (s : ℂ) • ζ
  obtain ⟨hh, hnew, heq⟩ := normalized_inverse_pair M G G' r ζ t ht hInv hInv'
  have hZ : ‖Matrix.diagonal z‖ = s * ρ := by
    rw [Matrix.l2_opNorm_diagonal]
    dsimp only [z]
    rw [norm_smul, hsnorm]
  have hK : ‖h * Matrix.diagonal z‖ ≤ ρ / c := by
    calc _ ≤ ‖h‖ * ‖Matrix.diagonal z‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (1 / (s * c)) * (s * ρ) := by rw [hZ]; gcongr
      _ = ρ / c := by field_simp [ne_of_gt hs]
  have hK' : ‖Matrix.diagonal z * h‖ ≤ ρ / c := by
    calc _ ≤ ‖Matrix.diagonal z‖ * ‖h‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (s * ρ) * (1 / (s * c)) := by rw [hZ]; gcongr
      _ = ρ / c := by field_simp [ne_of_gt hs]
  have hdc : ρ / c ≤ 1 / 2 := (div_le_iff₀ hc).mpr (by linarith)
  obtain ⟨L, R, A, B, hcomm, hcomm', hL, hR, hA, hB⟩ :=
    commutator_transport h h' z hh hnew heq (ρ / c) (by positivity) hdc hK hK'
  let p := fun i => (r i).im
  let p' := fun i => ((r + ζ) i).im
  have hp : ∀ i, 0 < p i := fun i => hc.trans_le (hdamp i).1
  have hp' : ∀ i, 0 < p' i := fun i => (by positivity : 0 < c / 2).trans_le (hdamp' i).1
  obtain ⟨hS, hSi⟩ := weight_norm p c C hc (fun i => ⟨(hdamp i).1, (hdamp i).2.1⟩)
  let ε := 2 * Q * ρ
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hεCt : 63 * ε ≤ Ct * ρ := by
    calc 63 * ε = (126 * Q) * ρ := by dsimp [ε]; ring
      _ ≤ Ct * ρ := mul_le_mul_of_nonneg_right hQCt hρ0
  have hε1 : ε ≤ 1 := by linarith only [hεCt, hCtρ]
  have hεc : 2 * ρ ≤ ε * c := by
    calc 2 * ρ = 1 * (2 * ρ) := by ring
      _ ≤ (Q * c) * (2 * ρ) := mul_le_mul_of_nonneg_right hQc (by positivity)
      _ = ε * c := by dsimp [ε]; ring
  have hrel : ∀ i, p' i ≤ (1 + ε) * p i ∧ p i ≤ (1 + ε) * p' i := by
    intro i
    have him : |(ζ i).im| ≤ ρ := (Complex.abs_im_le_norm _).trans (norm_le_pi_norm ζ i)
    have hplus : p' i ≤ p i + ρ := by
      change (r i).im + (ζ i).im ≤ (r i).im + ρ
      linarith only [him, le_abs_self (ζ i).im]
    have hminus : p i ≤ p' i + ρ := by
      change (r i).im ≤ (r i).im + (ζ i).im + ρ
      linarith only [him, neg_abs_le (ζ i).im]
    have hprod := mul_le_mul_of_nonneg_left (hdamp i).1 hε0
    have hprod' := mul_le_mul_of_nonneg_left (hdamp' i).1 hε0
    change ε * c ≤ ε * p i at hprod
    change ε * (c / 2) ≤ ε * p' i at hprod'
    constructor
    · nlinarith only [hplus, hεc, hprod, hρ0]
    · nlinarith only [hminus, hεc, hprod']
  have hcoeff : Real.sqrt C * (Real.sqrt c)⁻¹ * (2 * (ρ / c)) ≤ ε := by
    have he : Real.sqrt C * (Real.sqrt c)⁻¹ * (2 * (ρ / c)) ≤
        (Real.sqrt C * (Real.sqrt c)⁻¹ + 1) * (2 * (ρ / c)) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc _ ≤ (Real.sqrt C * (Real.sqrt c)⁻¹ + 1) * (2 * (ρ / c)) := he
      _ = ε := by dsimp [ε, Q]; ring
  have hdweak : ρ / c ≤ 2 * (ρ / c) := by linarith [div_nonneg hρ0 hc.le]
  have hforms := ward_form_bounds h h' L R A B p p' hp hp'
    (Real.sqrt C) (Real.sqrt c)⁻¹ (2 * (ρ / c)) ε
    (by positivity) (by positivity) (by positivity) hε0 hε1 hS hSi
    hL hR (hA.trans hdweak) (hB.trans hdweak) hcomm hcomm' hcoeff hrel
  have hforms' : ∀ f, (1 - Ct * ρ) * AndersonAC.S78.wardEnergy Finset.univ p h f ≤
      AndersonAC.S78.wardEnergy Finset.univ p' h' f ∧
      AndersonAC.S78.wardEnergy Finset.univ p' h' f ≤
        (1 + Ct * ρ) * AndersonAC.S78.wardEnergy Finset.univ p h f := by
    intro f
    have hD := wardEnergy_nonneg p (fun i => (hp i).le) h f
    have hD' := wardEnergy_nonneg p' (fun i => (hp' i).le) h' f
    have hu := (hforms f).1.trans (mul_le_mul_of_nonneg_right (by linarith : 1 + 63 * ε ≤ 1 + Ct * ρ) hD)
    have hr := (hforms f).2.trans (mul_le_mul_of_nonneg_right (by linarith : 1 + 63 * ε ≤ 1 + Ct * ρ) hD')
    exact signed_relative_of_mutual hD hD' (by positivity) (by linarith) hu hr
  refine ⟨?_, hdamp', hCtρ⟩
  dsimp only [AndersonAC.S78.ResetOutput]
  rw [hg, hg']
  refine ⟨hfixG, ?_, ?_, ?_, ?_, hforms'⟩
  · intro i
    exact (hdelta i).trans (mul_le_mul_of_nonneg_right hDCt hρ0)
  · intro i j
    exact (hentry i j).trans (by gcongr)
  · intro i
    exact (hfour i).trans (by gcongr)
  · exact hkernel.trans (mul_le_mul_of_nonneg_right hKCt hρ0)

#print axioms AndersonAC.SolS78.reset_variation_proof

end AndersonAC.SolS78
