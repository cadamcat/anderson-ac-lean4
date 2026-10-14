import AndersonAC.S6.Commutator
import AndersonAC.S6.Range

/-!
# Damped resolvents: dissipativity and the Combes–Thomas entry bound

For a real symmetric `M` and damping `r` with `c ≤ Im r`, the damped matrix
`𝓜 = M − t diag r` satisfies `‖𝓜 z‖ ≥ t c ‖z‖` (06-clearing.tex:196–200), hence is invertible;
and if `M = J + K` with direct hops `J` (|J| ≤ 1, degree ≤ 2d, `J ≠ 0 ⇒ |Δρ| ≤ 1`) and a
correction `K` constant along `ρ`, the exponential weight argument (06-clearing.tex:214–238)
gives `|𝓜⁻¹ i j| ≤ 4/(3tc) · exp(−a t (ρ i − ρ j))` with `a = localizationRate d c`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false

namespace AndersonAC.AgentS78Geo

variable {R : Type*} [Fintype R] [DecidableEq R]

theorem toEuclideanLin_apply' {S : Type*} [Fintype S] [DecidableEq S] (A : Matrix R S ℂ)
    (x : EuclideanSpace ℂ S) (i : R) :
    (Matrix.toEuclideanLin A x).ofLp i = ∑ j, A i j * x.ofLp j := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    Matrix.mulVec_apply_eq_sum]

/-- Schur test on vectors (generic index type; same proof as `SolS6.schurNormBound_proof`). -/
theorem schur_vec (A : Matrix R R ℂ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ u) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ v) (x : EuclideanSpace ℂ R) :
    ‖Matrix.toEuclideanLin A x‖ ≤ Real.sqrt (u * v) * ‖x‖ := by
  have hC_sq : (Real.sqrt (u * v) * ‖x‖) ^ 2 = (u * v) * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hu hv)]
  have hC_nonneg : 0 ≤ Real.sqrt (u * v) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  suffices hsq : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ (u * v) * ‖x‖ ^ 2 by
    have hsq' : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ (Real.sqrt (u * v) * ‖x‖) ^ 2 := by
      rw [hC_sq]; exact hsq
    exact (sq_le_sq₀ (norm_nonneg _) hC_nonneg).mp hsq'
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hrow_est : ∀ i, ‖(Matrix.toEuclideanLin A x).ofLp i‖ ^ 2 ≤
      u * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
    intro i
    rw [toEuclideanLin_apply']
    have htri : ‖∑ j, A i j * x.ofLp j‖ ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
      calc ‖∑ j, A i j * x.ofLp j‖ ≤ ∑ j, ‖A i j * x.ofLp j‖ := norm_sum_le _ _
        _ = ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by congr 1; ext j; rw [norm_mul]
    have hCS : (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 ≤
        (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ?_ ?_ ?_
      · intro j _; exact norm_nonneg _
      · intro j _; exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
      · intro j _
        exact (by ring : (‖A i j‖ * ‖x.ofLp j‖) ^ 2 =
          ‖A i j‖ * (‖A i j‖ * ‖x.ofLp j‖ ^ 2)).le
    have hsum_nonneg : 0 ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
    have hsq1 : ‖∑ j, A i j * x.ofLp j‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) htri
    exact hsq1.trans (hCS.trans (mul_le_mul_of_nonneg_right (hrow i) hsum_nonneg))
  calc ∑ i, ‖(Matrix.toEuclideanLin A x).ofLp i‖ ^ 2
        ≤ ∑ i, (u * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2)) :=
          Finset.sum_le_sum fun i _ => hrow_est i
      _ = u * (∑ j, ∑ i, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ u * (∑ j, v * ‖x.ofLp j‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hu
          apply Finset.sum_le_sum
          intro j _
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
      _ = (u * v) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
          rw [← Finset.mul_sum, ← mul_assoc]

/-- The imaginary part of the quadratic form of the damped matrix. -/
theorem damped_form_im (M : Matrix R R ℝ) (hM : M.IsSymm) (t : ℝ) (r : R → ℂ) (z : R → ℂ) :
    (∑ i, (starRingEnd ℂ) (z i) * ∑ j, AndersonAC.S6.dampedMatrix M t r i j * z j).im =
      -(t * ∑ i, (r i).im * ‖z i‖ ^ 2) := by
  have hsplit : ∀ i, (starRingEnd ℂ) (z i) * ∑ j, AndersonAC.S6.dampedMatrix M t r i j * z j =
      (∑ j, (starRingEnd ℂ) (z i) * ((M i j : ℂ) * z j)) -
        (t : ℂ) * (r i * ((starRingEnd ℂ) (z i) * z i)) := by
    intro i
    simp only [AndersonAC.S6.dampedMatrix, Matrix.sub_apply, Matrix.map_apply,
      Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Finset.mul_sum, mul_sub]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Complex.sub_im, Complex.im_sum]
  have h1 : ∀ i j, ((starRingEnd ℂ) (z i) * ((M i j : ℂ) * z j)).im =
      M i j * ((z i).re * (z j).im - (z i).im * (z j).re) := by
    intro i j; simp [Complex.mul_im, Complex.mul_re]; ring
  have hzero : ∑ i, (∑ j, (starRingEnd ℂ) (z i) * ((M i j : ℂ) * z j)).im = 0 := by
    simp_rw [Complex.im_sum, h1]
    have h2 : ∑ i, ∑ j, M i j * ((z i).re * (z j).im - (z i).im * (z j).re) =
        -∑ i, ∑ j, M i j * ((z i).re * (z j).im - (z i).im * (z j).re) := by
      conv_rhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM.apply i j]; ring
    linarith
  rw [hzero, Complex.im_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, zero_sub,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : (starRingEnd ℂ) (z i) * z i = ((‖z i‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hz]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Dissipativity: `t c ‖z‖ ≤ ‖𝓜 z‖`. -/
theorem damped_lower (M : Matrix R R ℝ) (hM : M.IsSymm) (t c : ℝ) (ht : 0 ≤ t) (r : R → ℂ)
    (hr : ∀ i, c ≤ (r i).im) (z : EuclideanSpace ℂ R) :
    t * c * ‖z‖ ≤ ‖Matrix.toEuclideanLin (AndersonAC.S6.dampedMatrix M t r) z‖ := by
  set w := Matrix.toEuclideanLin (AndersonAC.S6.dampedMatrix M t r) z
  have hinner : inner ℂ z w =
      ∑ i, (starRingEnd ℂ) (z.ofLp i) * ∑ j, AndersonAC.S6.dampedMatrix M t r i j * z.ofLp j := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, toEuclideanLin_apply', mul_comm]
  have him := damped_form_im M hM t r z.ofLp
  rw [← hinner] at him
  have hlow : t * c * ‖z‖ ^ 2 ≤ -(inner ℂ z w).im := by
    rw [him, neg_neg, EuclideanSpace.norm_sq_eq, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_right (hr i) (sq_nonneg ‖z.ofLp i‖)
    nlinarith
  have hup : -(inner ℂ z w).im ≤ ‖z‖ * ‖w‖ :=
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm z w))
  by_cases hz : ‖z‖ = 0
  · rw [hz, mul_zero]; exact norm_nonneg _
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have : t * c * ‖z‖ * ‖z‖ ≤ ‖w‖ * ‖z‖ := by nlinarith
    exact le_of_mul_le_mul_right this hzpos

theorem damped_isUnit (M : Matrix R R ℝ) (hM : M.IsSymm) (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (r : R → ℂ) (hr : ∀ i, c ≤ (r i).im) :
    IsUnit (AndersonAC.S6.dampedMatrix M t r).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h := damped_lower M hM t c ht.le r hr (WithLp.toLp 2 v)
  have hw : Matrix.toEuclideanLin (AndersonAC.S6.dampedMatrix M t r) (WithLp.toLp 2 v) = 0 := by
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, hv]
  rw [hw, norm_zero] at h
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ R)‖ = 0 := by
    have := mul_pos ht hc
    nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ R)]
  rw [norm_eq_zero] at hn
  apply hv0
  have := congrArg WithLp.ofLp hn
  simpa using this

/-- **Combes–Thomas entry bound** (06-clearing.tex:214–238, entrywise form). -/
theorem combes_thomas_entry (d : ℕ) (J K : Matrix R R ℝ) (hJs : J.IsSymm) (hKs : K.IsSymm)
    (hJ : ∀ i j, |J i j| ≤ 1)
    (hdeg : ∀ i, ((Finset.univ.filter (fun j => J i j ≠ 0)).card : ℝ) ≤ 2 * d)
    (t c : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (r : R → ℂ) (hr : ∀ i, c ≤ (r i).im)
    (ρ : R → ℝ) (hJρ : ∀ i j, J i j ≠ 0 → |ρ i - ρ j| ≤ 1)
    (hKρ : ∀ i j, K i j ≠ 0 → ρ i = ρ j) (i j : R) :
    ‖(AndersonAC.S6.dampedMatrix (J + K) t r)⁻¹ i j‖ ≤
      4 / (3 * (t * c)) * Real.exp (-(AndersonAC.SolS6.localizationRate d c * t * (ρ i - ρ j))) := by
  set a := AndersonAC.SolS6.localizationRate d c
  obtain ⟨ha, hrate⟩ := AndersonAC.SolS6.localization_rate_bound d c hc
  have hsym : (J + K).IsSymm := hJs.add hKs
  set 𝓜 := AndersonAC.S6.dampedMatrix (J + K) t r
  have hunit : IsUnit 𝓜.det := damped_isUnit (J + K) hsym t c ht hc r hr
  set G := 𝓜⁻¹
  set E := AndersonAC.S6.exponentialWeight a t ρ
  set E' := AndersonAC.S6.exponentialWeight (-a) t ρ
  set Err := E * 𝓜 * E' - 𝓜
  obtain ⟨hrows, hcols⟩ :=
    AndersonAC.SolS6.weighted_error_row_column_bounds d a t ρ J K r ha.le ht.le hJs hJ hdeg hJρ hKρ
  have hU := hrate t ht.le ht1
  have hct : 0 ≤ c * t / 4 := by positivity
  have hrows' : ∀ i, ∑ j, ‖Err i j‖ ≤ c * t / 4 := fun i => (hrows i).trans hU
  have hcols' : ∀ j, ∑ i, ‖Err i j‖ ≤ c * t / 4 := fun j => (hcols j).trans hU
  have hE'E : E' * E = 1 := (AndersonAC.SolS6.exponential_weight_inverse a t ρ).2
  have hmat : (𝓜 + Err) * (E * G) = E := by
    have h1 : 𝓜 + Err = E * 𝓜 * E' := by simp [Err]
    rw [h1]
    calc E * 𝓜 * E' * (E * G) = E * 𝓜 * (E' * E) * G := by simp only [Matrix.mul_assoc]
      _ = E * (𝓜 * G) := by rw [hE'E, Matrix.mul_one, Matrix.mul_assoc]
      _ = E := by rw [Matrix.mul_nonsing_inv 𝓜 hunit, Matrix.mul_one]
  set ej : EuclideanSpace ℂ R := EuclideanSpace.single j 1
  set y := Matrix.toEuclideanLin (E * G) ej
  have hlin : ∀ (A B : Matrix R R ℂ) (x : EuclideanSpace ℂ R),
      Matrix.toEuclideanLin (A * B) x = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
    intro A B x
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  have hy : Matrix.toEuclideanLin 𝓜 y + Matrix.toEuclideanLin Err y =
      Matrix.toEuclideanLin E ej := by
    rw [← LinearMap.add_apply, ← map_add, ← hlin, hmat]
  have hEej : ‖Matrix.toEuclideanLin E ej‖ = Real.exp (a * t * ρ j) := by
    have : Matrix.toEuclideanLin E ej = (Real.exp (a * t * ρ j) : ℂ) • ej := by
      ext k
      rw [toEuclideanLin_apply']
      simp only [E, ej, AndersonAC.S6.exponentialWeight, Matrix.diagonal_apply,
        PiLp.single_apply, PiLp.smul_apply, smul_eq_mul]
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [this, norm_smul, PiLp.norm_single, norm_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hErr := schur_vec Err (c * t / 4) (c * t / 4) hct hct hrows' hcols' y
  rw [Real.sqrt_mul_self hct] at hErr
  have hlow := damped_lower (J + K) hsym t c ht.le r hr y
  have hMy : ‖Matrix.toEuclideanLin 𝓜 y‖ ≤ Real.exp (a * t * ρ j) + c * t / 4 * ‖y‖ := by
    have : Matrix.toEuclideanLin 𝓜 y =
        Matrix.toEuclideanLin E ej - Matrix.toEuclideanLin Err y := eq_sub_of_add_eq hy
    rw [this, ← hEej]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hErr)
  have hynorm : ‖y‖ ≤ 4 / (3 * (t * c)) * Real.exp (a * t * ρ j) := by
    have htc : 0 < t * c := mul_pos ht hc
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hyi : y.ofLp i = (Real.exp (a * t * ρ i) : ℂ) * G i j := by
    simp only [y, ej, toEuclideanLin_apply', PiLp.single_apply]
    rw [Finset.sum_eq_single j]
    · simp [E, AndersonAC.S6.exponentialWeight, Matrix.diagonal_mul]
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hcomp := PiLp.norm_apply_le y i
  rw [hyi, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hcomp
  have hfinal : Real.exp (a * t * ρ i) * ‖G i j‖ ≤
      4 / (3 * (t * c)) * Real.exp (a * t * ρ j) := hcomp.trans hynorm
  have hexp : Real.exp (-(a * t * (ρ i - ρ j))) * Real.exp (a * t * ρ i) =
      Real.exp (a * t * ρ j) := by rw [← Real.exp_add]; ring_nf
  calc ‖G i j‖ = Real.exp (-(a * t * ρ i)) * (Real.exp (a * t * ρ i) * ‖G i j‖) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-(a * t * ρ i)) * (4 / (3 * (t * c)) * Real.exp (a * t * ρ j)) :=
        mul_le_mul_of_nonneg_left hfinal (Real.exp_pos _).le
    _ = 4 / (3 * (t * c)) * Real.exp (-(a * t * (ρ i - ρ j))) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

end AndersonAC.AgentS78Geo
