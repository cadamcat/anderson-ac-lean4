import AndersonAC.S45.Definitions

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder
namespace AndersonAC.AgentS45

open AndersonAC.S45

theorem matrixIm_l2_opNorm_le {I : Type*} [Fintype I] [DecidableEq I]
    (A : CMat I) (hA : A.IsSymm) : ‖matrixIm A‖ ≤ ‖A‖ := by
  classical
  have hformula : matrixIm A =
      ((2 * Complex.I : ℂ)⁻¹) • (A - Aᴴ) := by
    ext i j
    have hji : A j i = A i j := by
      have hij := congrFun (congrFun hA.eq i) j
      simpa using hij
    simp only [matrixIm, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.conjTranspose_apply]
    rw [hji, Complex.star_def]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Complex.im_eq_sub_conj (A i j))
  rw [hformula]
  have hscalar : ‖((2 * Complex.I : ℂ)⁻¹)‖ = 1 / 2 := by norm_num
  calc
    ‖((2 * Complex.I : ℂ)⁻¹) • (A - Aᴴ)‖ ≤
        ‖((2 * Complex.I : ℂ)⁻¹)‖ * ‖A - Aᴴ‖ := norm_smul_le _ _
    _ = (1 / 2) * ‖A - Aᴴ‖ := by rw [hscalar]
    _ ≤ (1 / 2) * (‖A‖ + ‖Aᴴ‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le A Aᴴ) (by norm_num)
    _ = ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring

theorem ward_l2_opNorm_bound {I : Type*} [Fintype I] [DecidableEq I]
    (H G : CMat I) (p : I → ℝ) (t c : ℝ)
    (ht : 0 < t) (hc : 0 < c) (hp : ∀ i, c ≤ p i)
    (hward : H * diagonal (fun i => (p i : ℂ)) * Hᴴ = matrixIm G)
    (hGsymm : G.IsSymm) (hH : H = (Real.sqrt t : ℂ) • G) :
    ‖H‖ ≤ 1 / (c * Real.sqrt t) := by
  classical
  let D : CMat I := diagonal (fun i => (p i : ℂ))
  let Dhalf : CMat I := diagonal (fun i => (Real.sqrt (p i) : ℂ))
  let Dinv : CMat I := diagonal (fun i => (((Real.sqrt (p i))⁻¹ : ℝ) : ℂ))
  let B : CMat I := H * Dhalf
  have hp0 (i : I) : 0 < p i := lt_of_lt_of_le hc (hp i)
  have hDhalfH : Dhalfᴴ = Dhalf := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Dhalf, Matrix.diagonal]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Dhalf, Matrix.diagonal, hij, hji]
  have hDhalfSq : Dhalf * Dhalf = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Dhalf, D, Matrix.mul_apply, Matrix.diagonal]
      norm_cast
      simpa [pow_two] using Real.sq_sqrt (le_of_lt (hp0 i))
    · simp [Dhalf, D, Matrix.mul_apply, Matrix.diagonal, hij]
  have hDhalfInv : Dhalf * Dinv = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Dhalf, Dinv, Matrix.mul_apply, Matrix.diagonal,
        Real.sqrt_ne_zero'.mpr (hp0 i)]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Dhalf, Dinv, Matrix.mul_apply, Matrix.diagonal, hij, hji]
  have hBprod : B * Bᴴ = H * D * Hᴴ := by
    dsimp [B]
    rw [Matrix.conjTranspose_mul, hDhalfH]
    calc
      _ = H * (Dhalf * Dhalf) * Hᴴ := by noncomm_ring
      _ = H * D * Hᴴ := by rw [hDhalfSq]
  have hBnorm : ‖B‖ ^ 2 = ‖matrixIm G‖ := by
    calc
      ‖B‖ ^ 2 = ‖B * Bᴴ‖ := by
        simpa [pow_two, Matrix.l2_opNorm_conjTranspose] using
          (Matrix.l2_opNorm_conjTranspose_mul_self Bᴴ).symm
      _ = ‖H * D * Hᴴ‖ := congrArg norm hBprod
      _ = ‖matrixIm G‖ := congrArg norm hward
  have hDinvNorm : ‖Dinv‖ ≤ 1 / Real.sqrt c := by
    let f : I → ℂ := fun i => (((Real.sqrt (p i))⁻¹ : ℝ) : ℂ)
    have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    let bound : NNReal := ⟨1 / Real.sqrt c, by positivity⟩
    rw [Matrix.l2_opNorm_diagonal]
    change ‖f‖ ≤ (bound : ℝ)
    rw [Pi.norm_def]
    rw [NNReal.coe_le_coe, Finset.sup_le_iff]
    intro i hi
    rw [← NNReal.coe_le_coe]
    change ‖f i‖ ≤ 1 / Real.sqrt c
    have hroot : Real.sqrt c ≤ Real.sqrt (p i) := Real.sqrt_le_sqrt (hp i)
    have hsqrtp : 0 < Real.sqrt (p i) := Real.sqrt_pos.2 (hp0 i)
    have hfnorm : ‖f i‖ = (Real.sqrt (p i))⁻¹ := by
      simp [f, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hsqrtp)]
    calc
      ‖f i‖ = (Real.sqrt (p i))⁻¹ := hfnorm
      _ ≤ (Real.sqrt c)⁻¹ := (inv_le_inv₀ hsqrtp hsqrtc).2 hroot
      _ = 1 / Real.sqrt c := by simp [one_div]
  have hHfactor : H = B * Dinv := by
    calc
      H = H * 1 := by simp
      _ = H * (Dhalf * Dinv) := by rw [hDhalfInv]
      _ = (H * Dhalf) * Dinv := (Matrix.mul_assoc _ _ _).symm
      _ = B * Dinv := rfl
  have hHle : ‖H‖ ≤ ‖B‖ * (1 / Real.sqrt c) := by
    calc
      ‖H‖ = ‖B * Dinv‖ := congrArg norm hHfactor
      _ ≤ ‖B‖ * ‖Dinv‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖B‖ * (1 / Real.sqrt c) :=
        mul_le_mul_of_nonneg_left hDinvNorm (norm_nonneg _)
  have hHsq : ‖H‖ ^ 2 ≤ ‖matrixIm G‖ / c := by
    calc
      ‖H‖ ^ 2 ≤ (‖B‖ * (1 / Real.sqrt c)) ^ 2 := by
        nlinarith [hHle, norm_nonneg H, norm_nonneg B]
      _ = ‖B‖ ^ 2 / c := by
        rw [mul_pow]
        have hrecip : (1 / Real.sqrt c) ^ 2 = 1 / c := by
          field_simp [(Real.sqrt_pos.2 hc).ne']
          rw [Real.sq_sqrt (le_of_lt hc)]
        rw [hrecip]
        ring
      _ = _ := by rw [hBnorm]
  have hHnorm : ‖H‖ = Real.sqrt t * ‖G‖ := by
    rw [hH, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 ht)]
  have hbasic : t * ‖G‖ ^ 2 ≤ ‖G‖ / c := by
    calc
      _ = ‖H‖ ^ 2 := by rw [hHnorm]; rw [mul_pow, Real.sq_sqrt ht.le]
      _ ≤ _ := hHsq
      _ ≤ _ := div_le_div_of_nonneg_right
        (matrixIm_l2_opNorm_le G hGsymm) (by positivity)
  by_cases hGzero : ‖G‖ = 0
  · rw [hHnorm, hGzero]
    simpa using (le_of_lt (show 0 < 1 / (c * Real.sqrt t) by positivity))
  · have hGpos : 0 < ‖G‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hGzero)
    have hctG2 : c * (t * ‖G‖ ^ 2) ≤ ‖G‖ := by
      calc
        _ ≤ c * (‖G‖ / c) := mul_le_mul_of_nonneg_left hbasic hc.le
        _ = ‖G‖ := by field_simp [hc.ne']
    have hctG : c * t * ‖G‖ ≤ 1 := by
      have hmul : ‖G‖ * (c * t * ‖G‖) ≤ ‖G‖ * 1 := by
        calc
          ‖G‖ * (c * t * ‖G‖) = c * (t * ‖G‖ ^ 2) := by ring
          _ ≤ ‖G‖ := by nlinarith [hctG2]
          _ = ‖G‖ * 1 := by ring
      exact (mul_le_mul_iff_right₀ hGpos).1 hmul
    have hGle : ‖G‖ ≤ 1 / (c * t) := by
      apply (le_div_iff₀ (mul_pos hc ht)).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hctG
    rw [hHnorm]
    calc
      Real.sqrt t * ‖G‖ ≤ Real.sqrt t * (1 / (c * t)) :=
        mul_le_mul_of_nonneg_left hGle (Real.sqrt_nonneg _)
      _ = 1 / (c * Real.sqrt t) := by
        rw [← (Real.sq_sqrt ht.le)]
        field_simp [hc.ne', (Real.sqrt_pos.2 ht).ne']
        rw [Real.sqrt_sq (Real.sqrt_nonneg t)]

end AndersonAC.AgentS45
