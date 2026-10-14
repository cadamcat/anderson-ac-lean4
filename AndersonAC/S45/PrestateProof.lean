import AndersonAC.S45.Definitions

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

private theorem ward_row_sum {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) (i : Fin n) :
    (∑ j, s.F t i j * s.p j) = s.q i := by
  have hw := hs.ward
  change s.h t * diagonal (fun j => (s.p j : ℂ)) * (s.h t)ᴴ = matrixIm s.g at hw
  have hi := congrFun (congrFun hw i) i
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply] at hi
  have hsum : (∑ j, ((s.h t i j).re * ((s.h t i j).re * s.p j) +
      (s.h t i j).im * ((s.h t i j).im * s.p j))) =
      ∑ j, ((s.h t i j).re ^ 2 + (s.h t i j).im ^ 2) * s.p j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∑ j, ‖s.h t i j‖ ^ 2 * s.p j) =
        ∑ j, ((s.h t i j).re ^ 2 + (s.h t i j).im ^ 2) * s.p j := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (s.g i i).im := by
      rw [← hsum]
      simpa [matrixIm, State.q, State.F, entryAbsSquare, Complex.mul_conj',
        Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using congrArg Complex.re hi

private theorem rawLag_eq_one_sub_K_mulVec {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) :
    s.rawLag = (1 - s.K t) *ᵥ s.lag t := by
  change s.rawLag = (1 - s.K t) *ᵥ ((1 - s.K t)⁻¹ *ᵥ s.rawLag)
  have hmv : (1 - s.K t) *ᵥ ((1 - s.K t)⁻¹ *ᵥ s.rawLag) =
      ((1 - s.K t) * (1 - s.K t)⁻¹) *ᵥ s.rawLag := by
    exact Matrix.mulVec_mulVec s.rawLag (1 - s.K t) ((1 - s.K t)⁻¹)
  letI : Invertible (1 - s.K t) := hs.invertible.invertible
  have hcancel : (1 - s.K t) * (1 - s.K t)⁻¹ = 1 :=
    Matrix.mul_inv_of_invertible (A := 1 - s.K t)
  rw [hmv, hcancel]
  simp

private theorem rawLag_pointwise_le {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) (i : Fin n) :
    ‖s.rawLag i‖ ≤ power t beta * (1 + ∑ j, s.F t i j) := by
  rw [rawLag_eq_one_sub_K_mulVec t C Λ W s hs]
  have hi : ((1 - s.K t) *ᵥ s.lag t) i =
      s.lag t i - ∑ j, s.K t i j * s.lag t j := by
    rw [sub_mulVec, one_mulVec]
    simp [Matrix.mulVec, dotProduct]
  rw [hi]
  calc
    ‖s.lag t i - ∑ j, s.K t i j * s.lag t j‖ ≤
        ‖s.lag t i‖ + ‖∑ j, s.K t i j * s.lag t j‖ := norm_sub_le _ _
    _ ≤ ‖s.lag t i‖ + ∑ j, ‖s.K t i j * s.lag t j‖ :=
      add_le_add (le_rfl) (by
        exact norm_sum_le (Finset.univ : Finset (Fin n))
          (fun j => s.K t i j * s.lag t j))
    _ ≤ power t beta * (1 + ∑ j, s.F t i j) := by
      have hlag := hs.lag_cap
      have hF : ∀ j, ‖s.K t i j‖ = s.F t i j := by
        intro j
        simp [State.K, State.F, entryAbsSquare, AndersonAC.Blueprint.entrywiseSquare,
          norm_pow]
      have hFnonneg : ∀ j, 0 ≤ s.F t i j := fun j => by
        rw [← hF j]
        exact norm_nonneg _
      have hsum := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.univ) => by
        calc
          ‖s.K t i j * s.lag t j‖ ≤ ‖s.K t i j‖ * ‖s.lag t j‖ := norm_mul_le _ _
          _ ≤ s.F t i j * power t beta :=
            mul_le_mul (hF j).le (hlag j) (norm_nonneg _) (hFnonneg j))
      calc
        ‖s.lag t i‖ + ∑ j, ‖s.K t i j * s.lag t j‖ ≤
            power t beta + ∑ j, s.F t i j * power t beta := by
          exact add_le_add (hlag i) hsum
        _ = power t beta * (1 + ∑ j, s.F t i j) := by
          simp_rw [mul_comm (s.F t i _) (power t beta)]
          rw [← Finset.mul_sum]
          ring

private theorem ward_row_bound {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) (hC : 1 ≤ C) (i : Fin n) :
    (∑ j, s.F t i j) ≤ C * s.q i := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hF0 : ∀ j, 0 ≤ s.F t i j := by
    intro j
    simp [State.F, entryAbsSquare]
  calc
    (∑ j, s.F t i j) ≤ ∑ j, C * (s.F t i j * s.p j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hp := (hs.broad j).2.1
      have hCp : 1 ≤ C * s.p j := by
        simpa [mul_comm] using (div_le_iff₀ hCpos).mp hp
      calc
        s.F t i j = s.F t i j * 1 := by ring
        _ ≤ s.F t i j * (C * s.p j) :=
          mul_le_mul_of_nonneg_left hCp (hF0 j)
        _ = C * (s.F t i j * s.p j) := by ring
    _ = C * (∑ j, s.F t i j * s.p j) := by
      rw [← Finset.mul_sum]
    _ = C * s.q i := by rw [ward_row_sum t C Λ W s hs i]

private theorem exists_small_scale {C : ℝ} (hC : 1 ≤ C) :
    ∃ t0 > 0, t0 ≤ 1 ∧ ∀ t, 0 < t → t < t0 →
      C * power t beta ≤ 1 / 2 ∧ 10 * C ^ 4 * power t beta ≤ 1 / 2 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCpow2 : 1 ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
  have hCpow3 : 1 ≤ C ^ 3 := by
    calc
      1 ≤ C ^ 2 := hCpow2
      _ = C ^ 2 * 1 := by ring
      _ ≤ C ^ 2 * C := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
      _ = C ^ 3 := by ring
  have hCpow4 : 1 ≤ C ^ 4 := by
    calc
      1 ≤ C ^ 2 := hCpow2
      _ = 1 * C ^ 2 := by ring
      _ ≤ C ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_right hCpow2 (sq_nonneg C)
      _ = C ^ 4 := by ring
  have hβ : 0 < beta := by norm_num [beta, delta]
  have hβinv : 0 < 1 / beta := one_div_pos.mpr hβ
  let a : ℝ := 1 / (40 * C ^ 4)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha_le : a ≤ 1 := by
    dsimp [a]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hCpow4]
  have ht0pos : 0 < a ^ (1 / beta) := Real.rpow_pos_of_pos ha _
  have ht0le : a ^ (1 / beta) ≤ 1 :=
    Real.rpow_le_one ha.le ha_le (le_of_lt hβinv)
  refine ⟨a ^ (1 / beta), ht0pos, ht0le, ?_⟩
  intro t ht htlt
  have hpoweq : (a ^ (1 / beta)) ^ beta = a := by
    rw [← Real.rpow_mul ha.le]
    have hprod : (1 / beta) * beta = 1 := by field_simp [ne_of_gt hβ]
    rw [hprod, Real.rpow_one]
  have htpow : power t beta < a := by
    dsimp [power]
    calc
      t ^ beta < (a ^ (1 / beta)) ^ beta :=
        Real.rpow_lt_rpow (le_of_lt ht) htlt hβ
      _ = a := hpoweq
  have hmul : C * power t beta < C * a := mul_lt_mul_of_pos_left htpow hCpos
  have hCa : C * a = 1 / (40 * C ^ 3) := by dsimp [a]; field_simp
  have hC4a : 10 * C ^ 4 * a = 1 / 4 := by dsimp [a]; field_simp; ring
  have hfirst : C * power t beta ≤ 1 / 2 := by
    have hbound : 1 / (40 * C ^ 3) ≤ 1 / 40 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [hCpow3]
    rw [hCa] at hmul
    linarith
  have hsecond : 10 * C ^ 4 * power t beta ≤ 1 / 2 := by
    have hmul' : 10 * C ^ 4 * power t beta < 10 * C ^ 4 * a :=
      mul_lt_mul_of_pos_left htpow (by positivity)
    rw [hC4a] at hmul'
    linarith
  exact ⟨hfirst, hsecond⟩

private theorem weighted_young_real (x y u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * x * y ≤ x ^ 2 * v / u + y ^ 2 * u / v := by
  have heq : (x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y) * (u * v) =
      (v * x - u * y) ^ 2 := by
    field_simp
    ring
  have hsquare := sq_nonneg (v * x - u * y)
  rw [← heq] at hsquare
  have hnonneg : 0 ≤ x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y :=
    nonneg_of_mul_nonneg_left hsquare (mul_pos hu hv)
  linarith

private theorem finite_weighted_schur_quadratic {ι : Type*} [Fintype ι]
    (k : ι → ι → ℝ) (w a : ι → ℝ) (R : ℝ)
    (hw : ∀ i, 0 < w i) (hk : ∀ i j, 0 ≤ k i j)
    (hsymm : ∀ i j, k j i = k i j)
    (hrow : ∀ i, (∑ j, k i j * w j) ≤ R * w i) :
    (∑ i, ∑ j, |a i| * |a j| * k i j) ≤ R * ∑ i, a i ^ 2 := by
  let A : ℝ := ∑ i, ∑ j, a i ^ 2 * k i j * w j / w i
  let B : ℝ := ∑ i, ∑ j, a j ^ 2 * k i j * w i / w j
  have hpoint (i j : ι) :
      2 * (|a i| * |a j| * k i j) ≤
        a i ^ 2 * k i j * w j / w i + a j ^ 2 * k i j * w i / w j := by
    have hy := weighted_young_real |a i| |a j| (w i) (w j) (hw i) (hw j)
    simp only [sq_abs] at hy
    calc
      2 * (|a i| * |a j| * k i j) = (2 * |a i| * |a j|) * k i j := by ring
      _ ≤ (a i ^ 2 * w j / w i + a j ^ 2 * w i / w j) * k i j :=
        mul_le_mul_of_nonneg_right hy (hk i j)
      _ = _ := by ring
  have hA : A ≤ R * ∑ i, a i ^ 2 := by
    calc
      A = ∑ i, (a i ^ 2 / w i) * (∑ j, k i j * w j) := by
        dsimp [A]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i, (a i ^ 2 / w i) * (R * w i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i) (div_nonneg (sq_nonneg _) (hw i).le)
      _ = R * ∑ i, a i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [(hw i).ne']
  have hBA : B = A := by
    dsimp [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm j i]
  have hh := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_hj : j ∈ Finset.univ) => hpoint i j))
  have htwo : 2 * (∑ i, ∑ j, |a i| * |a j| * k i j) ≤ A + B := by
    simpa only [A, B, Finset.sum_add_distrib, Finset.mul_sum] using hh
  rw [hBA] at htwo
  nlinarith [hA]

private theorem sum_mul_le_sqrt_mul_sqrt {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    (∑ i, f i * g i) ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  have hcs : (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * ∑ i, g i ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) f g
  have hf2 : 0 ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hg2 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum : 0 ≤ ∑ i, f i * g i := Finset.sum_nonneg fun i _ => mul_nonneg (hf i) (hg i)
  have hroot : (Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2)) ^ 2 =
      (∑ i, f i ^ 2) * ∑ i, g i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hf2, Real.sq_sqrt hg2]
  apply (sq_le_sq₀ hsum (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [hroot]
  exact hcs

private theorem finite_weighted_schur_l2 {ι : Type*} [Fintype ι]
    (k : ι → ι → ℝ) (w : ι → ℝ) (R : ℝ)
    (hw : ∀ i, 0 < w i) (hk : ∀ i j, 0 ≤ k i j)
    (hsymm : ∀ i j, k j i = k i j)
    (hrow : ∀ i, (∑ j, k i j * w j) ≤ R * w i) (hR : 0 ≤ R)
    (u : ι → ℝ) :
    (∑ i, (∑ j, k i j * u j) ^ 2) ≤ R ^ 2 * ∑ j, u j ^ 2 := by
  have hcell (i : ι) : (∑ j, k i j * u j) ^ 2 ≤
      (R * w i) * ∑ j, k i j * u j ^ 2 / w j := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ)
      (r := fun j => k i j * u j)
      (f := fun j => k i j * w j)
      (g := fun j => k i j * u j ^ 2 / w j)
      (fun j _ => mul_nonneg (hk i j) (hw j).le)
      (fun j _ => div_nonneg (mul_nonneg (hk i j) (sq_nonneg _)) (hw j).le)
      (fun j _ => by
        have hjw : w j ≠ 0 := (hw j).ne'
        field_simp [hjw]
        exact le_rfl)
    have hsum0 : 0 ≤ ∑ j, k i j * u j ^ 2 / w j :=
      Finset.sum_nonneg fun j _ => div_nonneg (mul_nonneg (hk i j) (sq_nonneg _)) (hw j).le
    calc
      (∑ j, k i j * u j) ^ 2 ≤
          (∑ j, k i j * w j) * ∑ j, k i j * u j ^ 2 / w j := by simpa using hcs
      _ ≤ (R * w i) * ∑ j, k i j * u j ^ 2 / w j :=
        mul_le_mul_of_nonneg_right (hrow i) hsum0
  calc
    (∑ i, (∑ j, k i j * u j) ^ 2) ≤
        ∑ i, (R * w i) * ∑ j, k i j * u j ^ 2 / w j :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = R * ∑ j, u j ^ 2 / w j * ∑ i, k j i * w i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hsymm j i]
      ring
    _ ≤ R * ∑ j, u j ^ 2 / w j * (R * w j) := by
      apply mul_le_mul_of_nonneg_left _ hR
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hrow j)
        (div_nonneg (sq_nonneg _) (hw j).le)
    _ = R ^ 2 * ∑ j, u j ^ 2 := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp [(hw j).ne']

private theorem matrix_opNorm_le_of_vec_bound {n : ℕ} (B : CMat (Fin n)) (R : ℝ)
    (hR : 0 ≤ R)
    (hvec : ∀ x : Fin n → ℂ,
      ‖WithLp.toLp 2 (B *ᵥ x)‖ ≤ R * ‖WithLp.toLp 2 x‖) :
    ‖B‖ ≤ R := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  rw [← WithLp.toLp_ofLp (p := 2) x, Matrix.toEuclideanCLM_toLp]
  exact hvec (WithLp.ofLp x)

private theorem matrix_weighted_schur_bound {n : ℕ} (B : CMat (Fin n))
    (w : Fin n → ℝ) (R : ℝ) (hw : ∀ i, 0 < w i)
    (hsymm : ∀ i j, ‖B i j‖ = ‖B j i‖)
    (hrow : ∀ i, (∑ j, ‖B i j‖ * w j) ≤ R * w i) (hR : 0 ≤ R) :
    ‖B‖ ≤ R := by
  have hvec (x : Fin n → ℂ) :
      ‖WithLp.toLp 2 (B *ᵥ x)‖ ≤ R * ‖WithLp.toLp 2 x‖ := by
    have hpoint (i : Fin n) :
        ‖(B *ᵥ x) i‖ ≤ ∑ j, ‖B i j‖ * ‖x j‖ := by
      have hsum : ‖∑ j, B i j * x j‖ ≤ ∑ j, ‖B i j * x j‖ :=
        norm_sum_le (Finset.univ : Finset (Fin n)) (fun j => B i j * x j)
      calc
        ‖(B *ᵥ x) i‖ = ‖∑ j, B i j * x j‖ := by simp [Matrix.mulVec, dotProduct]
        _ ≤ ∑ j, ‖B i j * x j‖ := hsum
        _ ≤ ∑ j, ‖B i j‖ * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => norm_mul_le _ _
    have hsum : (∑ i, ‖(B *ᵥ x) i‖ ^ 2) ≤
        R ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
      calc
        (∑ i, ‖(B *ᵥ x) i‖ ^ 2) ≤
            ∑ i, (∑ j, ‖B i j‖ * ‖x j‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun j _ =>
              mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
            exact hpoint i
        _ ≤ R ^ 2 * ∑ j, (‖x j‖) ^ 2 :=
          finite_weighted_schur_l2 (fun i j => ‖B i j‖) w R hw
            (fun _ _ => norm_nonneg _) (fun i j => (hsymm i j).symm)
            hrow hR (fun j => ‖x j‖)
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    calc
      Real.sqrt (∑ i, ‖(B *ᵥ x) i‖ ^ 2) ≤
          Real.sqrt (R ^ 2 * ∑ j, ‖x j‖ ^ 2) := Real.sqrt_le_sqrt hsum
      _ = R * Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq_eq_abs, abs_of_nonneg hR]
  exact matrix_opNorm_le_of_vec_bound B R hR hvec

private def wardKernel {n : ℕ} (h : CMat (Fin n)) (i : Fin n) : CMat (Fin n) :=
  fun j k => h i j * ((h j k).im : ℂ) * star (h i k)

private theorem wardKernel_eq_diagonal {n : ℕ} (h : CMat (Fin n)) (i : Fin n) :
    wardKernel h i = diagonal (h i) * matrixIm h * diagonal (fun k => star (h i k)) := by
  ext j k
  simp [wardKernel, Matrix.mul_apply, Matrix.diagonal, matrixIm, mul_assoc]

private theorem scaled_state_symmetric {n : ℕ} (t : ℝ) (s : State (Fin n))
    (hs : s.g.IsSymm) : (s.h t).IsSymm := by
  rw [State.h]
  exact hs.smul (Real.sqrt t : ℂ)

private theorem matrixIm_scaled_state {n : ℕ} (t : ℝ) (s : State (Fin n)) :
    matrixIm (s.h t) = (Real.sqrt t : ℂ) • matrixIm s.g := by
  ext j k
  simp [State.h, matrixIm, Matrix.smul_apply, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re]

private theorem wardKernel_norm_symmetric {n : ℕ} (h : CMat (Fin n))
    (hsymm : h.IsSymm) (i j k : Fin n) :
    ‖wardKernel h i j k‖ = ‖wardKernel h i k j‖ := by
  have hkj : h k j = h j k := hsymm.apply j k
  simp [wardKernel, hkj, Complex.star_def, mul_comm, mul_left_comm, mul_assoc]

private theorem diag_congruence_entry {n : ℕ} (S : CMat (Fin n))
    (d : Fin n → ℂ) (j k : Fin n) :
    (S * diagonal d * Sᴴ) j k = ∑ m, S j m * d m * star (S k m) := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_assoc]

private theorem sqrt_rowCap_div_sqrt {t : ℝ} (ht : 0 < t) :
    Real.sqrt (rowCap t) / Real.sqrt t = power t (delta / 2) := by
  have hrowpos : 0 < rowCap t := by
    exact Real.rpow_pos_of_pos ht _
  have hrowExp : t ^ (1 + delta) / t = t ^ delta := by
    calc
      t ^ (1 + delta) / t = t ^ (1 + delta) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((1 + delta) - 1) := (Real.rpow_sub ht (1 + delta) 1).symm
      _ = t ^ delta := by congr 1; ring
  have hleftsq : (Real.sqrt (rowCap t) / Real.sqrt t) ^ 2 = power t delta := by
    rw [div_pow, Real.sq_sqrt hrowpos.le, Real.sq_sqrt ht.le, rowCap, power]
    exact hrowExp
  have hrightsq : power t (delta / 2) ^ 2 = power t delta := by
    dsimp [power]
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hleftpos : 0 < Real.sqrt (rowCap t) / Real.sqrt t :=
    div_pos (Real.sqrt_pos.2 hrowpos) (Real.sqrt_pos.2 ht)
  have hrightpos : 0 < power t (delta / 2) :=
    Real.rpow_pos_of_pos ht _
  nlinarith [hleftsq, hrightsq]

private theorem wardKernel_weighted_row {n : ℕ} (h : CMat (Fin n)) (i : Fin n)
    (R0 H : ℝ) (hR0 : 0 ≤ R0) (hH : 0 ≤ H)
    (hrow : ∀ j, (∑ k, ‖h j k‖ ^ 2) ≤ R0)
    (hfourth : (∑ k, ‖h i k‖ ^ 4) ≤ H) :
    ∀ j, (∑ k, ‖wardKernel h i j k‖ * (‖h i k‖ + Real.sqrt H)) ≤
      ((Real.sqrt R0 + R0) * Real.sqrt H) * (‖h i j‖ + Real.sqrt H) := by
  have hr0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
  have hroot : 0 ≤ Real.sqrt H := Real.sqrt_nonneg _
  have hfourth' : (∑ k, (‖h i k‖ ^ 2) ^ 2) ≤ H := by
    calc
      (∑ k, (‖h i k‖ ^ 2) ^ 2) = ∑ k, ‖h i k‖ ^ 4 := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ ≤ H := hfourth
  intro j
  have hcs1 : (∑ k, ‖h j k‖ * ‖h i k‖ ^ 2) ≤ Real.sqrt R0 * Real.sqrt H := by
    calc
      _ ≤ Real.sqrt (∑ k, ‖h j k‖ ^ 2) * Real.sqrt (∑ k, (‖h i k‖ ^ 2) ^ 2) :=
        sum_mul_le_sqrt_mul_sqrt _ _ (fun _ => norm_nonneg _) (fun _ => sq_nonneg _)
      _ ≤ Real.sqrt R0 * Real.sqrt H := by
        exact mul_le_mul (Real.sqrt_le_sqrt (hrow j)) (Real.sqrt_le_sqrt hfourth')
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcs2 : (∑ k, ‖h j k‖ * ‖h i k‖) ≤ R0 := by
    calc
      _ ≤ Real.sqrt (∑ k, ‖h j k‖ ^ 2) * Real.sqrt (∑ k, ‖h i k‖ ^ 2) :=
        sum_mul_le_sqrt_mul_sqrt _ _ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      _ ≤ Real.sqrt R0 * Real.sqrt R0 :=
        mul_le_mul (Real.sqrt_le_sqrt (hrow j)) (Real.sqrt_le_sqrt (hrow i))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = R0 := Real.mul_self_sqrt hR0
  have hentry (k : Fin n) :
      ‖wardKernel h i j k‖ ≤ ‖h i j‖ * ‖h j k‖ * ‖h i k‖ := by
    calc
      ‖wardKernel h i j k‖ =
          ‖h i j * ((h j k).im : ℂ) * star (h i k)‖ := rfl
      _ ≤ ‖h i j‖ * ‖((h j k).im : ℂ)‖ * ‖star (h i k)‖ := norm_mul₃_le
      _ ≤ ‖h i j‖ * ‖h j k‖ * ‖h i k‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_star]
        gcongr
        exact Complex.abs_im_le_norm _
  have hkernelSum :
      (∑ k, ‖wardKernel h i j k‖ * (‖h i k‖ + Real.sqrt H)) ≤
        ‖h i j‖ * (Real.sqrt R0 * Real.sqrt H + Real.sqrt H * R0) := by
    calc
      _ ≤ ∑ k, (‖h i j‖ * ‖h j k‖ * ‖h i k‖) * (‖h i k‖ + Real.sqrt H) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hentry k)
          (by positivity)
      _ = ∑ k, (‖h i j‖ * (‖h j k‖ * ‖h i k‖ ^ 2) +
          ‖h i j‖ * (Real.sqrt H * (‖h j k‖ * ‖h i k‖))) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (∑ k, ‖h i j‖ * (‖h j k‖ * ‖h i k‖ ^ 2)) +
          ∑ k, ‖h i j‖ * (Real.sqrt H * (‖h j k‖ * ‖h i k‖)) :=
        Finset.sum_add_distrib
      _ = ‖h i j‖ * (∑ k, ‖h j k‖ * ‖h i k‖ ^ 2) +
          ‖h i j‖ * (Real.sqrt H * ∑ k, ‖h j k‖ * ‖h i k‖) := by
        have hsum1 : (∑ k, ‖h i j‖ * (‖h j k‖ * ‖h i k‖ ^ 2)) =
            ‖h i j‖ * (∑ k, ‖h j k‖ * ‖h i k‖ ^ 2) := by rw [← Finset.mul_sum]
        have hsum2 : (∑ k, ‖h i j‖ * (Real.sqrt H * (‖h j k‖ * ‖h i k‖))) =
            ‖h i j‖ * (Real.sqrt H * ∑ k, ‖h j k‖ * ‖h i k‖) := by
          calc
            _ = ‖h i j‖ * (∑ k, Real.sqrt H * (‖h j k‖ * ‖h i k‖)) := by
              rw [← Finset.mul_sum]
            _ = ‖h i j‖ * (Real.sqrt H * ∑ k, ‖h j k‖ * ‖h i k‖) := by
              rw [← Finset.mul_sum]
        rw [hsum1, hsum2]
      _ ≤ ‖h i j‖ * (Real.sqrt R0 * Real.sqrt H) +
          ‖h i j‖ * (Real.sqrt H * R0) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcs1 (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcs2 hroot) (norm_nonneg _)
      _ = ‖h i j‖ * (Real.sqrt R0 * Real.sqrt H + Real.sqrt H * R0) := by ring
  calc
    (∑ k, ‖wardKernel h i j k‖ * (‖h i k‖ + Real.sqrt H)) ≤
        ‖h i j‖ * (Real.sqrt R0 * Real.sqrt H + Real.sqrt H * R0) := hkernelSum
    _ = ((Real.sqrt R0 + R0) * Real.sqrt H) * ‖h i j‖ := by ring
    _ ≤ ((Real.sqrt R0 + R0) * Real.sqrt H) * (‖h i j‖ + Real.sqrt H) := by
      exact mul_le_mul_of_nonneg_left (by linarith [hroot]) (by positivity)

private theorem broad_prestate_bounds {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) (hC : 1 ≤ C)
    (hsmall : C * power t beta ≤ 1 / 2) :
    ∀ i, ‖s.rawLag i‖ ≤ 10 * C ^ 3 * power t beta ∧
      |s.q i - s.p i| ≤ 10 * C ^ 3 * power t beta ∧
      (∑ j, s.F t i j) ≤ 10 * C ^ 3 ∧
      ‖s.h t i i‖ ≤ 10 * C ^ 3 * Real.sqrt t := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpow0 : 0 ≤ power t beta := le_of_lt (Real.rpow_pos_of_pos hs.scale.1 beta)
  have hpowle : power t beta ≤ 1 := by
    dsimp [power]
    exact Real.rpow_le_one hs.scale.1.le hs.scale.2.le (by norm_num [beta, delta])
  intro i
  have hrow := ward_row_bound t C Λ W s hs hC i
  have hraw := rawLag_pointwise_le t C Λ W s hs i
  have hF0 : ∀ j, 0 ≤ s.F t i j := by
    intro j
    simp [State.F, entryAbsSquare]
  have hqp_eq : s.q i - s.p i = (s.rawLag i).im := by
    simp [State.q, State.p, State.rawLag, Complex.sub_im]
  have hqp : |s.q i - s.p i| ≤ ‖s.rawLag i‖ := by
    rw [hqp_eq]
    exact Complex.abs_im_le_norm _
  have hq_nonneg : 0 ≤ s.q i := by
    rw [← ward_row_sum t C Λ W s hs i]
    apply Finset.sum_nonneg
    intro j hj
    have hp := (hs.broad j).2.1
    have hp0 : 0 ≤ s.p j := le_trans (by positivity) hp
    exact mul_nonneg (hF0 j) hp0
  have hq_upper : s.q i ≤ 2 * (C + 1) := by
    have hpupper := (hs.broad i).2.2
    have habs : s.q i ≤ s.p i + |s.q i - s.p i| := by
      have h := le_abs_self (s.q i - s.p i)
      linarith
    have hqpupper : |s.q i - s.p i| ≤ power t beta * (1 + C * s.q i) := by
      calc
        |s.q i - s.p i| ≤ ‖s.rawLag i‖ := hqp
        _ ≤ power t beta * (1 + ∑ j, s.F t i j) := hraw
        _ ≤ power t beta * (1 + C * s.q i) :=
          mul_le_mul_of_nonneg_left (by linarith [hrow]) hpow0
    have hineq : s.q i ≤ C + power t beta * (1 + C * s.q i) := by
      calc
        s.q i ≤ s.p i + |s.q i - s.p i| := habs
        _ ≤ C + power t beta * (1 + C * s.q i) := by
          exact add_le_add hpupper hqpupper
    nlinarith [hsmall, hpowle, hq_nonneg]
  have hrowbound : (∑ j, s.F t i j) ≤ 4 * C ^ 2 := by
    have hCnonneg : 0 ≤ C := le_trans zero_le_one hC
    nlinarith [hrow, hq_upper]
  have hrawbound : ‖s.rawLag i‖ ≤ 5 * C ^ 2 * power t beta := by
    calc
      ‖s.rawLag i‖ ≤ power t beta * (1 + ∑ j, s.F t i j) := hraw
      _ ≤ power t beta * (1 + 4 * C ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hrowbound]) hpow0
      _ ≤ 5 * C ^ 2 * power t beta := by
        have hfactor : 1 + 4 * C ^ 2 ≤ 5 * C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
        calc
          power t beta * (1 + 4 * C ^ 2) = (1 + 4 * C ^ 2) * power t beta := by ring
          _ ≤ 5 * C ^ 2 * power t beta := mul_le_mul_of_nonneg_right hfactor hpow0
  have hqpbound : |s.q i - s.p i| ≤ 5 * C ^ 2 * power t beta := hqp.trans hrawbound
  have hg : ‖s.g i i‖ ≤ 6 * C ^ 2 := by
    have hr := (hs.broad i).1
    have hsum : s.g i i = s.r i + s.rawLag i := by
      simp [State.rawLag]
    rw [hsum]
    calc
      ‖s.r i + s.rawLag i‖ ≤ ‖s.r i‖ + ‖s.rawLag i‖ := norm_add_le _ _
      _ ≤ C + 5 * C ^ 2 * power t beta := add_le_add hr hrawbound
      _ ≤ 6 * C ^ 2 := by nlinarith [hpowle, hC]
  have hdiag : ‖s.h t i i‖ ≤ 6 * C ^ 2 * Real.sqrt t := by
    change ‖(Real.sqrt t : ℂ) * s.g i i‖ ≤ 6 * C ^ 2 * Real.sqrt t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt t * ‖s.g i i‖ ≤ Real.sqrt t * (6 * C ^ 2) :=
        mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg _)
      _ = 6 * C ^ 2 * Real.sqrt t := by ring
  have hC2C3 : C ^ 2 ≤ C ^ 3 := by
    calc
      C ^ 2 = C ^ 2 * 1 := by ring
      _ ≤ C ^ 2 * C := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
      _ = C ^ 3 := by ring
  refine ⟨hrawbound.trans ?_, hqpbound.trans ?_, ?_, hdiag.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by nlinarith [hC2C3]) hpow0
  · exact mul_le_mul_of_nonneg_right (by nlinarith [hC2C3]) hpow0
  · nlinarith [hrowbound, hC2C3]
  · exact mul_le_mul_of_nonneg_right (by nlinarith [hC2C3]) (Real.sqrt_nonneg t)

private theorem ward_operator_bound {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) (hC : 1 ≤ C)
    (hsmall : C * power t beta ≤ 1 / 2) :
    ∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤
      20 * C ^ 4 * power t (delta / 2) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hBroad := broad_prestate_bounds t C Λ W s hs hC hsmall
  have hSym : (s.h t).IsSymm := scaled_state_symmetric t s hs.symmetric
  have htroot : 0 < Real.sqrt t := Real.sqrt_pos.2 hs.scale.1
  have hHpos : 0 < rowCap t := Real.rpow_pos_of_pos hs.scale.1 _
  have hH0 : 0 ≤ rowCap t := hHpos.le
  have hR0 : 0 ≤ 10 * C ^ 3 := by positivity
  intro i
  let H : ℝ := rowCap t
  let R0 : ℝ := 10 * C ^ 3
  let h : CMat (Fin n) := s.h t
  let D : CMat (Fin n) := diagonal (h i)
  let S : CMat (Fin n) := D * h
  let P : CMat (Fin n) := diagonal (fun j => (s.p j : ℂ))
  let Q : CMat (Fin n) := S * P * Sᴴ
  let w : Fin n → ℝ := fun j => ‖h i j‖ + Real.sqrt H
  let Rk : ℝ := (Real.sqrt R0 + R0) * Real.sqrt H
  have hHpos' : 0 < H := by exact hHpos
  have hHnonneg : 0 ≤ H := hHpos'.le
  have hrowEnergy : ∀ j, (∑ k, ‖h j k‖ ^ 2) ≤ R0 := by
    intro j
    have hj := (hBroad j).2.2.1
    simpa [h, State.F, entryAbsSquare, R0] using hj
  have hfourth : (∑ k, ‖h i k‖ ^ 4) ≤ H := by
    have hi := hs.row_cap i
    simpa [h, H, State.fourthRow] using hi
  have hSymh : h.IsSymm := by simpa [h] using hSym
  have hKernelSym : ∀ j k, ‖wardKernel h i j k‖ = ‖wardKernel h i k j‖ := by
    intro j k
    exact wardKernel_norm_symmetric h hSymh i j k
  have hKernelRow : ∀ j,
      (∑ k, ‖wardKernel h i j k‖ * w k) ≤ Rk * w j := by
    intro j
    exact wardKernel_weighted_row h i R0 H hR0 hHnonneg hrowEnergy hfourth j
  have hWpos : ∀ j, 0 < w j := by
    intro j
    dsimp [w]
    exact lt_of_lt_of_le (Real.sqrt_pos.2 hHpos')
      (le_add_of_nonneg_left (norm_nonneg _))
  have hRknonneg : 0 ≤ Rk := by
    positivity [R0, H]
  have hsqrtPos : 0 < Real.sqrt t := htroot
  have hDstar : Dᴴ = diagonal (fun j => star (h i j)) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    · simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hjk, eq_comm]
  have hSstar : Sᴴ = hᴴ * diagonal (fun j => star (h i j)) := by
    simp [S, D, Matrix.conjTranspose_mul, hDstar]
  have hWardId : h * P * hᴴ = matrixIm s.g := by
    simpa [h, P, State.ward] using hs.ward
  have hQward : Q = D * matrixIm s.g * diagonal (fun j => star (h i j)) := by
    change ((diagonal (h i) * h) * diagonal (fun j => (s.p j : ℂ))) *
      (diagonal (h i) * h)ᴴ = _
    rw [show (diagonal (h i) * h)ᴴ =
      hᴴ * diagonal (fun j => star (h i j)) by
        rw [Matrix.conjTranspose_mul, hDstar]]
    calc
      ((diagonal (h i) * h) * diagonal (fun j => (s.p j : ℂ))) *
          (hᴴ * diagonal (fun j => star (h i j))) =
          diagonal (h i) * (h * diagonal (fun j => (s.p j : ℂ)) * hᴴ) *
            diagonal (fun j => star (h i j)) := by noncomm_ring
      _ = diagonal (h i) * matrixIm s.g * diagonal (fun j => star (h i j)) := by
        rw [hWardId]
  have hKernelScale : wardKernel h i = (Real.sqrt t : ℂ) • Q := by
    rw [wardKernel_eq_diagonal, matrixIm_scaled_state, hQward]
    ext j k
    simp [D, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      matrixIm, mul_assoc]
  have hsqrtCne : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt htroot
  have hQscale : Q = (Real.sqrt t : ℂ)⁻¹ • wardKernel h i := by
    rw [hKernelScale, smul_smul, inv_mul_cancel₀ hsqrtCne, one_smul]
  have hQscaleNorm : ∀ j k, ‖Q j k‖ = (Real.sqrt t)⁻¹ * ‖wardKernel h i j k‖ := by
    intro j k
    rw [hQscale]
    simp [Matrix.smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hQsym : ∀ j k, ‖Q j k‖ = ‖Q k j‖ := by
    intro j k
    rw [hQscaleNorm, hQscaleNorm, hKernelSym j k]
  have hQrow : ∀ j, (∑ k, ‖Q j k‖ * w k) ≤ (Rk / Real.sqrt t) * w j := by
    intro j
    have hscaleRow : (∑ k, ‖Q j k‖ * w k) =
        (Real.sqrt t)⁻¹ * ∑ k, ‖wardKernel h i j k‖ * w k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hQscaleNorm]
      ring
    rw [hscaleRow]
    calc
      (Real.sqrt t)⁻¹ * ∑ k, ‖wardKernel h i j k‖ * w k ≤
          (Real.sqrt t)⁻¹ * (Rk * w j) :=
        mul_le_mul_of_nonneg_left (hKernelRow j) (inv_nonneg.mpr htroot.le)
      _ = (Rk / Real.sqrt t) * w j := by ring
  have hRop : 0 ≤ Rk / Real.sqrt t := div_nonneg hRknonneg htroot.le
  have hQbound : ‖Q‖ ≤ Rk / Real.sqrt t :=
    matrix_weighted_schur_bound Q w (Rk / Real.sqrt t) hWpos hQsym hQrow hRop
  have hPnonneg : ∀ j, 0 ≤ s.p j := by
    intro j
    exact le_trans (by positivity) (hs.broad j).2.1
  have hdiagP : P.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    change (0 : ℂ) ≤ (s.p j : ℂ)
    exact_mod_cast hPnonneg j
  have hQpos : Q.PosSemidef := by
    exact hdiagP.mul_mul_conjTranspose_same S
  have hCp : ∀ j, 1 ≤ C * s.p j := by
    intro j
    have hp := (hs.broad j).2.1
    simpa [mul_comm] using (div_le_iff₀ hCpos).mp hp
  let E : CMat (Fin n) := diagonal (fun j => ((C * s.p j - 1 : ℝ) : ℂ))
  have hEpos : E.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    change (0 : ℂ) ≤ ((C * s.p j - 1 : ℝ) : ℂ)
    exact_mod_cast sub_nonneg.mpr (hCp j)
  have horderDiff : (C : ℂ) • Q - S * Sᴴ = S * E * Sᴴ := by
    ext j k
    have hQentry : Q j k = ∑ m, S j m * (s.p m : ℂ) * star (S k m) := by
      change (S * diagonal (fun m => (s.p m : ℂ)) * Sᴴ) j k = _
      exact diag_congruence_entry S (fun m => (s.p m : ℂ)) j k
    have hAentry : (S * Sᴴ) j k = ∑ m, S j m * star (S k m) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hEentry : (S * E * Sᴴ) j k =
        ∑ m, S j m * ((C * s.p m - 1 : ℝ) : ℂ) * star (S k m) := by
      change (S * diagonal (fun m => ((C * s.p m - 1 : ℝ) : ℂ)) * Sᴴ) j k = _
      exact diag_congruence_entry S (fun m => ((C * s.p m - 1 : ℝ) : ℂ)) j k
    change (C : ℂ) * Q j k - (S * Sᴴ) j k = (S * E * Sᴴ) j k
    rw [hQentry, hAentry, hEentry]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    ring
  have horder : S * Sᴴ ≤ (C : ℂ) • Q := by
    rw [Matrix.le_iff, horderDiff]
    exact hEpos.mul_mul_conjTranspose_same S
  have hSpos : (S * Sᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose S
  have hnormMono := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder hSpos.nonneg
  have hnormSsq : ‖S * Sᴴ‖ = ‖S‖ ^ 2 := by
    calc
      ‖S * Sᴴ‖ = ‖(Sᴴ)ᴴ * Sᴴ‖ := by simp
      _ = ‖Sᴴ‖ * ‖Sᴴ‖ := Matrix.l2_opNorm_conjTranspose_mul_self Sᴴ
      _ = ‖S‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose]; ring
  have hnormSmul : ‖(C : ℂ) • Q‖ = C * ‖Q‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCpos.le]
  have hSbound : ‖S‖ ^ 2 ≤ C * (Rk / Real.sqrt t) := by
    rw [← hnormSsq]
    exact hnormMono.trans (by rw [hnormSmul]; exact mul_le_mul_of_nonneg_left hQbound hCpos.le)
  have hC2C3 : C ^ 2 ≤ C ^ 3 := by
    calc
      C ^ 2 = C ^ 2 * 1 := by ring
      _ ≤ C ^ 2 * C := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
      _ = C ^ 3 := by ring
  have hC3C4 : C ^ 3 ≤ C ^ 4 := by
    calc
      C ^ 3 = C ^ 3 * 1 := by ring
      _ ≤ C ^ 3 * C := mul_le_mul_of_nonneg_left hC (by positivity)
      _ = C ^ 4 := by ring
  have hR0sqrt : Real.sqrt R0 ≤ 4 * C ^ 2 := by
    have hR0le : R0 ≤ (4 * C ^ 2) ^ 2 := by
      dsimp [R0]
      nlinarith [hC3C4]
    calc
      Real.sqrt R0 ≤ Real.sqrt ((4 * C ^ 2) ^ 2) := Real.sqrt_le_sqrt hR0le
      _ = 4 * C ^ 2 := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hRkernel : Rk ≤ 14 * C ^ 3 * Real.sqrt H := by
    have hcoef : Real.sqrt R0 + R0 ≤ 14 * C ^ 3 := by
      dsimp [R0]
      nlinarith [hR0sqrt, hC2C3]
    dsimp [Rk]
    exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
  have hSfinal : ‖S‖ ^ 2 ≤ 20 * C ^ 4 * power t (delta / 2) := by
    have hratio := sqrt_rowCap_div_sqrt hs.scale.1
    have hRkernel' : Rk ≤ 14 * C ^ 3 * Real.sqrt (rowCap t) := by
      simpa [H] using hRkernel
    have hmul : C * (Rk / Real.sqrt t) ≤ 20 * C ^ 4 * power t (delta / 2) := by
      calc
        C * (Rk / Real.sqrt t) ≤ C * (14 * C ^ 3 * Real.sqrt (rowCap t) / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hRkernel' htroot.le) hCpos.le
        _ = 14 * C ^ 4 * (Real.sqrt (rowCap t) / Real.sqrt t) := by ring
        _ = 14 * C ^ 4 * power t (delta / 2) := by rw [hratio]
        _ ≤ 20 * C ^ 4 * power t (delta / 2) := by
          have hp0 : 0 ≤ power t (delta / 2) := le_of_lt (Real.rpow_pos_of_pos hs.scale.1 _)
          nlinarith
    exact hSbound.trans hmul
  simpa [S, D, h] using hSfinal

private theorem qform_add {n : ℕ} (A B : RMat (Fin n)) (f : Fin n → ℝ) :
    qform (A + B) f = qform A f + qform B f := by
  simp [qform, Matrix.add_mulVec, Finset.sum_add_distrib, mul_add]

private theorem qform_sub_const {n : ℕ} (D : RMat (Fin n)) (f : Fin n → ℝ)
    (c : ℝ) (hDsym : D.IsSymm) (hD1 : D *ᵥ (fun _ : Fin n => 1) = 0) :
    qform D (fun i => f i - c) = qform D f := by
  have hvec : (fun i => f i - c) = f - c • (fun _ : Fin n => 1) := by
    ext i
    simp
  have hmul : D *ᵥ (fun i => f i - c) = D *ᵥ f := by
    rw [hvec, Matrix.mulVec_sub, Matrix.mulVec_smul, hD1]
    simp
  have hsum : ∑ i, (D *ᵥ f) i = 0 := by
    calc
      ∑ i, (D *ᵥ f) i = (fun _ : Fin n => (1 : ℝ)) ⬝ᵥ (D *ᵥ f) := by
        simp [dotProduct]
      _ = f ⬝ᵥ (D *ᵥ (fun _ : Fin n => 1)) := hDsym.dotProduct_mulVec_comm.symm
      _ = 0 := by simp [hD1]
  unfold qform
  rw [hmul]
  calc
    ∑ i, (f i - c) * (D *ᵥ f) i =
        (∑ i, f i * (D *ᵥ f) i) - c * (∑ i, (D *ᵥ f) i) := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = ∑ i, f i * (D *ᵥ f) i := by rw [hsum]; ring

private def onesMatrix {n : ℕ} : RMat (Fin n) := fun _ _ => 1

private theorem qform_ones {n : ℕ} (f : Fin n → ℝ) :
    qform (onesMatrix : RMat (Fin n)) f = (∑ i, f i) ^ 2 := by
  have hone : (onesMatrix : RMat (Fin n)) *ᵥ f = fun _ => ∑ i, f i := by
    ext i
    simp [onesMatrix, Matrix.mulVec, dotProduct]
  unfold qform
  rw [hone]
  rw [← Finset.sum_mul]
  ring

private theorem augmented_matrix_posDef {n : ℕ} (D : RMat (Fin n))
    (hD : constantKernel D) (i : Fin n) :
    (D + onesMatrix).PosDef := by
  have hi : i.val < n := i.isLt
  have hnNat : 0 < n := by omega
  have hn : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast hnNat
  have hJ : (onesMatrix : RMat (Fin n)).IsSymm := by
    apply Matrix.IsSymm.ext
    intro j k
    simp [onesMatrix]
  have hA_sym : (D + onesMatrix).IsSymm := by
    apply Matrix.IsSymm.ext
    intro j k
    simp [hD.1.apply j k, onesMatrix]
  have hA_herm : (D + onesMatrix).IsHermitian := by
    exact Matrix.isHermitian_iff_isSymm.mpr hA_sym
  have hAform (x : Fin n → ℝ) :
      qform (D + onesMatrix) x = qform D x + (∑ j, x j) ^ 2 := by
    rw [qform_add, qform_ones]
  have hA_nonneg (x : Fin n → ℝ) : 0 ≤ qform (D + onesMatrix) x := by
    rw [hAform]
    exact add_nonneg (hD.2.1 x) (sq_nonneg _)
  have hA_strict : ∀ ⦃x : Fin n → ℝ⦄, x ≠ 0 → 0 < qform (D + onesMatrix) x := by
    intro x hx
    have hAnz : qform (D + onesMatrix) x ≠ 0 := by
      intro hzero
      have hDzero : qform D x = 0 := by
        rw [hAform] at hzero
        nlinarith [hD.2.1 x, sq_nonneg (∑ j, x j)]
      obtain ⟨a, ha⟩ := (hD.2.2 x).mp hDzero
      have hsum : (∑ j, x j) = (Fintype.card (Fin n) : ℝ) * a := by
        simp [ha]
      have hsumzero : (∑ j, x j) = 0 := by
        rw [hAform] at hzero
        nlinarith [hD.2.1 x, sq_nonneg (∑ j, x j)]
      have ha0 : a = 0 := by nlinarith [hn, hsum, hsumzero]
      apply hx
      funext j
      rw [ha j, ha0]
      rfl
    exact lt_of_le_of_ne (hA_nonneg x) (Ne.symm hAnz)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA_herm ?_
  intro x hx
  have h := hA_strict hx
  simpa [qform, dotProduct] using h

private theorem qform_sub_identity {n : ℕ} (A : RMat (Fin n)) (x u : Fin n → ℝ) :
    qform A (x - u) = qform A x - (∑ i, x i * (A *ᵥ u) i) -
      (∑ i, u i * (A *ᵥ x) i) + qform A u := by
  unfold qform
  simp only [Matrix.mulVec_sub, Pi.sub_apply]
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

private theorem qform_complete_square_upper {n : ℕ} (A : RMat (Fin n))
    (hAsym : A.IsSymm) (hApos : ∀ v, 0 ≤ qform A v)
    (y u x : Fin n → ℝ) (hu : A *ᵥ u = y) :
    2 * (∑ i, y i * x i) - qform A x ≤ qform A u := by
  have hcross : (∑ i, u i * (A *ᵥ x) i) = ∑ i, x i * y i := by
    have h := (hAsym.dotProduct_mulVec_comm (x := x) (y := u)).symm
    simpa [dotProduct, hu, mul_comm] using h
  have hcomm : (∑ i, y i * x i) = ∑ i, x i * y i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hnonneg := hApos (x - u)
  rw [qform_sub_identity] at hnonneg
  rw [hu, hcross, hcomm.symm] at hnonneg
  nlinarith [hnonneg]

private theorem state_D_mulVec_one_zero {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) :
    s.D t *ᵥ (fun _ : Fin n => 1) = 0 := by
  have hFp : s.F t *ᵥ s.p = s.q := by
    ext i
    simpa [Matrix.mulVec, dotProduct] using ward_row_sum t C Λ W s hs i
  have hp1 : diagonal s.p *ᵥ (fun _ : Fin n => 1) = s.p := by
    ext i
    simp [Matrix.mulVec_diagonal]
  have hpq1 : diagonal (fun i => s.p i * s.q i) *ᵥ
      (fun _ : Fin n => 1) = fun i => s.p i * s.q i := by
    ext i
    simp [Matrix.mulVec_diagonal]
  have hprod : (diagonal s.p * s.F t * diagonal s.p) *ᵥ (fun _ : Fin n => 1) =
      diagonal s.p *ᵥ (s.F t *ᵥ (diagonal s.p *ᵥ (fun _ => 1))) := by
    rw [← Matrix.mulVec_mulVec (fun _ : Fin n => 1) (diagonal s.p * s.F t) (diagonal s.p),
      ← Matrix.mulVec_mulVec (diagonal s.p *ᵥ (fun _ : Fin n => 1)) (diagonal s.p) (s.F t)]
  rw [State.D, Matrix.sub_mulVec, hpq1, hprod, hp1, hFp]
  ext i
  simp [Matrix.mulVec_diagonal]

private theorem dualForm_ge_test {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) (i : Fin n)
    (y f : Fin n → ℝ) (hy : neutral y) :
    2 * (∑ j, y j * f j) - qform (s.D t) f ≤ s.X t y := by
  let D := s.D t
  let A : RMat (Fin n) := D + onesMatrix
  have hApos := augmented_matrix_posDef D hs.kernel i
  have hAsym : A.IsSymm := (Matrix.isHermitian_iff_isSymm.mp hApos.1)
  let u : Fin n → ℝ := A⁻¹ *ᵥ y
  letI : Invertible A := hApos.isUnit.invertible
  have hAu : A *ᵥ u = y := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hA_nonneg : ∀ z, 0 ≤ qform A z := by
    intro z
    have hp := hApos.posSemidef.dotProduct_mulVec_nonneg z
    simpa [qform, dotProduct, A] using hp
  have hD1 : D *ᵥ (fun _ : Fin n => 1) = 0 := by
    simpa [D] using state_D_mulVec_one_zero t C Λ W s hs
  have hObjUpper : ∀ z, 2 * (∑ j, y j * z j) - qform D z ≤ qform A u := by
    intro z
    let c : ℝ := (∑ j, z j) / (Fintype.card (Fin n) : ℝ)
    let x : Fin n → ℝ := fun j => z j - c
    have hn : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
      have hi : i.val < n := i.isLt
      have hnNat : 0 < n := by omega
      rw [Fintype.card_fin]
      exact_mod_cast hnNat
    have hnNat : 0 < n := by
      have hi : i.val < n := i.isLt
      omega
    have hxneutral : neutral x := by
      change (∑ j, x j) = 0
      dsimp [x, c]
      simp [Finset.sum_sub_distrib, Finset.sum_const]
      have hnCast : (n : ℝ) ≠ 0 := by exact_mod_cast hnNat.ne'
      calc
        (∑ j, z j) - (n : ℝ) * ((∑ j, z j) / (n : ℝ)) = 0 := by
          rw [div_eq_mul_inv]
          calc
            (∑ j, z j) - (n : ℝ) * ((∑ j, z j) * (n : ℝ)⁻¹) =
                (∑ j, z j) - (∑ j, z j) * ((n : ℝ) * (n : ℝ)⁻¹) := by ring
            _ = 0 := by rw [mul_inv_cancel₀ hnCast]; ring
        _ = 0 := by ring
    have hyx : (∑ j, y j * x j) = ∑ j, y j * z j := by
      dsimp [x, c]
      calc
        (∑ j, y j * (z j - (∑ k, z k) / (Fintype.card (Fin n) : ℝ))) =
            (∑ j, y j * z j) - ((∑ k, z k) / (Fintype.card (Fin n) : ℝ)) * (∑ j, y j) := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
              ring
        _ = ∑ j, y j * z j := by rw [hy]; ring
    have hDx := qform_sub_const D z c hs.kernel.1 hD1
    have hAx : qform A x = qform D z := by
      change qform (D + onesMatrix) x = qform D z
      rw [qform_add, qform_ones]
      rw [hDx]
      have hxsum : (∑ j, x j) = 0 := hxneutral
      rw [hxsum]
      ring
    calc
      2 * (∑ j, y j * z j) - qform D z =
          2 * (∑ j, y j * x j) - qform A x := by rw [hyx, hAx]
      _ ≤ qform A u :=
        qform_complete_square_upper A hAsym hA_nonneg y u x hAu
  have hbdd : BddAbove {a : ℝ | ∃ z : Fin n → ℝ,
      a = 2 * (∑ j, y j * z j) - qform D z} := by
    refine ⟨qform A u, ?_⟩
    intro a ha
    rcases ha with ⟨z, rfl⟩
    exact hObjUpper z
  change 2 * (∑ j, y j * f j) - qform D f ≤
    sSup {a : ℝ | ∃ z : Fin n → ℝ, a = 2 * (∑ j, y j * z j) - qform D z}
  apply le_csSup hbdd
  exact ⟨f, rfl⟩

private theorem qform_diagonal {n : ℕ} (d f : Fin n → ℝ) :
    qform (diagonal d) f = ∑ i, d i * f i ^ 2 := by
  simp [qform, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem qform_diag_congruence {n : ℕ} (d : Fin n → ℝ)
    (F : RMat (Fin n)) (f : Fin n → ℝ) :
    qform (diagonal d * F * diagonal d) f =
      qform F (fun i => d i * f i) := by
  have hmul : (diagonal d * F * diagonal d) *ᵥ f =
      diagonal d *ᵥ (F *ᵥ (fun i => d i * f i)) := by
    have hdiag : diagonal d *ᵥ f = fun i => d i * f i := by
      ext i
      simp [Matrix.mulVec_diagonal]
    calc
      (diagonal d * F * diagonal d) *ᵥ f =
          (diagonal d * F) *ᵥ (diagonal d *ᵥ f) :=
        (Matrix.mulVec_mulVec f (diagonal d * F) (diagonal d)).symm
      _ = diagonal d *ᵥ (F *ᵥ (diagonal d *ᵥ f)) :=
        (Matrix.mulVec_mulVec (diagonal d *ᵥ f) (diagonal d) F).symm
      _ = diagonal d *ᵥ (F *ᵥ (fun i => d i * f i)) := by
        rw [hdiag]
  unfold qform
  rw [hmul]
  simp [Matrix.mulVec_diagonal, mul_comm, mul_left_comm, mul_assoc]

private theorem qform_sub {n : ℕ} (A B : RMat (Fin n)) (f : Fin n → ℝ) :
    qform (A - B) f = qform A f - qform B f := by
  simp [qform, Matrix.sub_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem qform_row_eq_cube {n : ℕ} (F : RMat (Fin n))
    (hFsym : F.IsSymm) (i : Fin n) :
    qform F (fun j => F i j) = (F ^ 3) i i := by
  have hq : qform F (fun j => F i j) =
      ∑ j, ∑ k, F i j * F j k * F i k := by
    calc
      qform F (fun j => F i j) =
          ∑ j, F i j * (∑ k, F j k * F i k) := by
        simp [qform, Matrix.mulVec, dotProduct]
      _ = ∑ j, ∑ k, F i j * (F j k * F i k) := by
        apply Finset.sum_congr rfl
        intro j _
        simpa using Finset.mul_sum (Finset.univ : Finset (Fin n))
          (fun k => F j k * F i k) (F i j)
      _ = ∑ j, ∑ k, F i j * F j k * F i k := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hpow : (F ^ 3) i i = ∑ j, ∑ k, F i k * F k j * F j i := by
    simp [pow_succ, pow_two, Matrix.mul_apply, Finset.sum_mul, mul_assoc]
  rw [hq, hpow]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [hFsym.apply j i, hFsym.apply k j, hFsym.apply k i]

private theorem qform_D_row_test {n : ℕ} (t : ℝ) (s : State (Fin n))
    (i : Fin n) (hp : ∀ j, s.p j ≠ 0) (hFsym : (s.F t).IsSymm) :
    qform (s.D t) (fun j => s.F t i j / s.p j) =
      (∑ j, s.p j * s.q j * (s.F t i j / s.p j) ^ 2) - (s.F t ^ 3) i i := by
  let f : Fin n → ℝ := fun j => s.F t i j / s.p j
  have hpf : (fun j => s.p j * f j) = fun j => s.F t i j := by
    funext j
    dsimp [f]
    exact mul_div_cancel₀ _ (hp j)
  rw [State.D, qform_sub, qform_diagonal, qform_diag_congruence, hpf,
    qform_row_eq_cube (s.F t) hFsym i]

private theorem q_over_p_bounds {n : ℕ} (t C : ℝ) (s : State (Fin n))
    (ht : 0 < t) (hpAll : ∀ j, 1 / C ≤ s.p j) (hC : 1 ≤ C)
    (hstrong : 10 * C ^ 4 * power t beta ≤ 1 / 2)
    (hBroad : ∀ j, ‖s.rawLag j‖ ≤ 10 * C ^ 3 * power t beta ∧
      |s.q j - s.p j| ≤ 10 * C ^ 3 * power t beta ∧
      (∑ k, s.F t j k) ≤ 10 * C ^ 3 ∧
      ‖s.h t j j‖ ≤ 10 * C ^ 3 * Real.sqrt t)
    (j : Fin n) :
    1 / 2 ≤ s.q j / s.p j ∧ s.q j / s.p j ≤ 3 / 2 ∧
      s.q j / s.p j ≤ 1 + 10 * C ^ 4 * power t beta := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpLower := hpAll j
  have hpPos : 0 < s.p j := lt_of_lt_of_le (by positivity) hpLower
  have hsmallErr : 10 * C ^ 3 * power t beta ≤ 1 / (2 * C) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hstrong]
  have hpHalf : 1 / (2 * C) ≤ s.p j / 2 := by
    calc
      1 / (2 * C) = (1 / C) / 2 := by field_simp
      _ ≤ s.p j / 2 := div_le_div_of_nonneg_right hpLower (by norm_num)
  have hnear : |s.q j - s.p j| ≤ s.p j / 2 :=
    (hBroad j).2.1.trans (hsmallErr.trans hpHalf)
  have hnear' := abs_le.mp hnear
  have hqlo : s.p j / 2 ≤ s.q j := by linarith [hnear'.1]
  have hqhi : s.q j ≤ 3 * s.p j / 2 := by linarith [hnear'.2]
  have hratioLo : 1 / 2 ≤ s.q j / s.p j := by
    apply (le_div_iff₀ hpPos).2
    nlinarith [hqlo]
  have hratioHi : s.q j / s.p j ≤ 3 / 2 := by
    apply (div_le_iff₀ hpPos).2
    nlinarith [hqhi]
  have hCp : 1 ≤ C * s.p j := by
    simpa [mul_comm] using (div_le_iff₀ hCpos).mp hpLower
  have hnum : s.q j - s.p j ≤ 10 * C ^ 3 * power t beta :=
    (le_abs_self _).trans (hBroad j).2.1
  have hmul : 10 * C ^ 3 * power t beta ≤
      10 * C ^ 4 * power t beta * s.p j := by
    calc
      10 * C ^ 3 * power t beta =
          (10 * C ^ 3 * power t beta) * 1 := by ring
      _ ≤ (10 * C ^ 3 * power t beta) * (C * s.p j) :=
        mul_le_mul_of_nonneg_left hCp (by positivity [Real.rpow_pos_of_pos ht beta])
      _ = 10 * C ^ 4 * power t beta * s.p j := by ring
  have hquot : (s.q j - s.p j) / s.p j ≤ 10 * C ^ 4 * power t beta :=
    (div_le_iff₀ hpPos).2 (hnum.trans hmul)
  have hratioEq : s.q j / s.p j = 1 + (s.q j - s.p j) / s.p j := by
    field_simp [hpPos.ne']
    ring
  refine ⟨hratioLo, hratioHi, ?_⟩
  rw [hratioEq]
  linarith [hquot]

private theorem fintype_sum_sub {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, (a i - b i)) = (∑ i, a i) - ∑ i, b i := by
  calc
    (∑ i, (a i - b i)) = ∑ i, (a i + -b i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, a i) + ∑ i, -b i := Finset.sum_add_distrib
    _ = (∑ i, a i) - ∑ i, b i := by
      simp [Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem fintype_sum_mul_const {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    (∑ i, a i * c) = c * ∑ i, a i := by
  calc
    (∑ i, a i * c) = ∑ i, c * a i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = c * ∑ i, a i := by
      simpa using (Finset.mul_sum (Finset.univ : Finset (Fin n)) a c).symm

set_option maxHeartbeats 1000000 in
private theorem cube_row_bound {n : ℕ} (t C : ℝ) (Λ W : Form (Fin n))
    (s : State (Fin n)) (hs : Prestate t C Λ W s) (hC : 1 ≤ C)
    (hstrong : 10 * C ^ 4 * power t beta ≤ 1 / 2) (i : Fin n) :
    (s.F t ^ 3) i i ≤
      (1000 * C ^ 12 + C ^ 2 * power (30 * C ^ 4) (4 / 3) *
        power (4 * C ^ 2) (1 / 3)) * power t kappa * rowCap t := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpowpos : 0 < power t beta := Real.rpow_pos_of_pos hs.scale.1 _
  have hCtoC2 : C ≤ C ^ 2 := by
    calc
      C = C * 1 := by ring
      _ ≤ C * C := mul_le_mul_of_nonneg_left hC (by positivity)
      _ = C ^ 2 := by ring
  have hC2toC3 : C ^ 2 ≤ C ^ 3 := by
    calc
      C ^ 2 = C ^ 2 * 1 := by ring
      _ ≤ C ^ 2 * C := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
      _ = C ^ 3 := by ring
  have hC3toC4 : C ^ 3 ≤ C ^ 4 := by
    calc
      C ^ 3 = C ^ 3 * 1 := by ring
      _ ≤ C ^ 3 * C := mul_le_mul_of_nonneg_left hC (by positivity)
      _ = C ^ 4 := by ring
  have hCcoeff : C ≤ 10 * C ^ 4 := by nlinarith [hCtoC2, hC2toC3, hC3toC4]
  have hsmall : C * power t beta ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hCcoeff hpowpos.le
    nlinarith [hstrong]
  have hBroad := broad_prestate_bounds t C Λ W s hs hC hsmall
  let F := s.F t
  let p := s.p
  let q := s.q
  let H := rowCap t
  let M : Fin n → ℝ := fun j => p j * q j
  let f : Fin n → ℝ := fun j => F i j / p j
  let trM : ℝ := ∑ j, M j
  let num : ℝ := ∑ j, M j * f j
  let varF : ℝ := ∑ j, M j * f j ^ 2
  let bar : ℝ := num / trM
  let y : Fin n → ℝ := fun j => M j * (f j - bar)
  have hpAll : ∀ j, 1 / C ≤ p j := by
    intro j
    exact (hs.broad j).2.1
  have hratios : ∀ j, 1 / 2 ≤ q j / p j ∧ q j / p j ≤ 3 / 2 ∧
      q j / p j ≤ 1 + 10 * C ^ 4 * power t beta := by
    intro j
    have hj := q_over_p_bounds t C s hs.scale.1 hpAll hC hstrong hBroad j
    simpa [p, q] using hj
  have hpPos : ∀ j, 0 < p j := by
    intro j
    exact lt_of_lt_of_le (by positivity) (hpAll j)
  have hqPos : ∀ j, 0 < q j := by
    intro j
    have hq := (hratios j).1
    have hprod' : (1 / 2) * p j ≤ q j := (le_div_iff₀ (hpPos j)).mp hq
    have hprod : p j / 2 ≤ q j := by
      calc
        p j / 2 = (1 / 2) * p j := by ring
        _ ≤ q j := hprod'
    have hp2 : 0 < p j / 2 := div_pos (hpPos j) (by norm_num)
    exact lt_of_lt_of_le hp2 hprod
  have hFnonneg : ∀ j k, 0 ≤ F j k := by
    intro j k
    simp [F, State.F, entryAbsSquare]
  have hSymF := scaled_state_symmetric t s hs.symmetric
  have hFsym : F.IsSymm := by
    apply Matrix.IsSymm.ext
    intro j k
    dsimp [F]
    simp [State.F, entryAbsSquare, hSymF.apply j k]
  have hfourth : (∑ j, (F i j) ^ 2) ≤ H := by
    have hi := hs.row_cap i
    have hi' : (∑ j, ‖s.h t i j‖ ^ 4) ≤ rowCap t := by
      simpa [State.fourthRow] using hi
    calc
      (∑ j, (F i j) ^ 2) = ∑ j, ‖s.h t i j‖ ^ 4 := by
        apply Finset.sum_congr rfl
        intro j _
        simp [F, State.F, entryAbsSquare]
        ring
      _ ≤ H := by simpa [H] using hi'
  have hrow : (∑ j, F i j) ≤ 10 * C ^ 3 := (hBroad i).2.2.1
  have hMpos : ∀ j, 0 < M j := by
    intro j
    dsimp [M]
    exact mul_pos (hpPos j) (hqPos j)
  have hMlo : ∀ j, 1 / (2 * C ^ 2) ≤ M j := by
    intro j
    have hpSq' : (1 / C) ^ 2 ≤ p j ^ 2 :=
      (sq_le_sq₀ (by positivity) (le_of_lt (hpPos j))).2 (hpAll j)
    have hpSq : 1 / C ^ 2 ≤ p j ^ 2 := by
      calc
        1 / C ^ 2 = (1 / C) ^ 2 := by field_simp
        _ ≤ p j ^ 2 := hpSq'
    have hqhalf' : (1 / 2) * p j ≤ q j := (le_div_iff₀ (hpPos j)).mp (hratios j).1
    have hqhalf : p j / 2 ≤ q j := by
      calc
        p j / 2 = (1 / 2) * p j := by ring
        _ ≤ q j := hqhalf'
    dsimp [M]
    calc
      1 / (2 * C ^ 2) = (1 / C ^ 2) / 2 := by field_simp
      _ ≤ p j ^ 2 / 2 := div_le_div_of_nonneg_right hpSq (by norm_num)
      _ = p j * (p j / 2) := by ring
      _ ≤ p j * q j := mul_le_mul_of_nonneg_left hqhalf (hpPos j).le
  have hMhi : ∀ j, M j ≤ 2 * C ^ 2 := by
    intro j
    have hpUpper := (hs.broad j).2.2
    have hpSq : p j ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (le_of_lt (hpPos j)) (by positivity)).2 hpUpper
    have hqUpper : q j ≤ 3 * p j / 2 := by
      have hqUpper' : q j ≤ (3 / 2) * p j :=
        (div_le_iff₀ (hpPos j)).mp (hratios j).2.1
      calc
        q j ≤ (3 / 2) * p j := hqUpper'
        _ = 3 * p j / 2 := by ring
    calc
      M j = p j * q j := rfl
      _ ≤ p j * (3 * p j / 2) := mul_le_mul_of_nonneg_left hqUpper (hpPos j).le
      _ ≤ 2 * C ^ 2 := by nlinarith [hpSq]
  have hnNat : 0 < n := by have hi := i.isLt; omega
  have hn : 0 < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast hnNat
  have hTlo : (Fintype.card (Fin n) : ℝ) / (2 * C ^ 2) ≤ trM := by
    calc
      (Fintype.card (Fin n) : ℝ) / (2 * C ^ 2) =
          (Fintype.card (Fin n) : ℝ) * (1 / (2 * C ^ 2)) := by ring
      _ = ∑ j, 1 / (2 * C ^ 2) := by simp [Finset.sum_const]
      _ ≤ ∑ j, M j := Finset.sum_le_sum fun j _ => hMlo j
  have hTpos : 0 < trM := by
    have hden : 0 < 2 * C ^ 2 := by positivity
    have hcard : 0 < (Fintype.card (Fin n) : ℝ) / (2 * C ^ 2) := div_pos hn hden
    exact lt_of_lt_of_le hcard hTlo
  have hnumEq : num = ∑ j, q j * F i j := by
    dsimp [num, M, f]
    apply Finset.sum_congr rfl
    intro j _
    have hpne := (hpPos j).ne'
    field_simp [hpne]
  have hnumPos : 0 ≤ num := by
    rw [hnumEq]
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (le_of_lt (hqPos j)) (hFnonneg i j)
  have hqBound : ∀ j, q j ≤ 3 * C / 2 := by
    intro j
    have hq := (div_le_iff₀ (hpPos j)).mp (hratios j).2.1
    have hpUpper := (hs.broad j).2.2
    nlinarith [hq]
  have hnumBound : num ≤ 15 * C ^ 4 := by
    rw [hnumEq]
    calc
      (∑ j, q j * F i j) ≤ ∑ j, (3 * C / 2) * F i j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hqBound j) (hFnonneg i j)
      _ = (3 * C / 2) * ∑ j, F i j := by rw [Finset.mul_sum]
      _ ≤ (3 * C / 2) * (10 * C ^ 3) :=
        mul_le_mul_of_nonneg_left hrow (by positivity)
      _ ≤ 15 * C ^ 4 := by ring_nf; nlinarith
  have hbarNonneg : 0 ≤ bar := by
    dsimp [bar]
    exact div_nonneg hnumPos hTpos.le
  have hbarMean : bar * trM = num := by
    dsimp [bar]
    exact div_mul_cancel₀ _ hTpos.ne'
  have hsumMb : (∑ j, M j * bar) = bar * trM := by
    calc
      (∑ j, M j * bar) = ∑ j, bar * M j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = bar * trM := by dsimp [trM]; rw [Finset.mul_sum]
  have hyneutral : neutral y := by
    change (∑ j, y j) = 0
    dsimp [y]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [hsumMb, hbarMean]
    dsimp [num]
    ring
  have hsumYF : (∑ j, y j * f j) = varF - bar ^ 2 * trM := by
    dsimp [y, varF]
    calc
      (∑ j, M j * (f j - bar) * f j) =
          (∑ j, M j * f j ^ 2) - bar * (∑ j, M j * f j) := by
        calc
          (∑ j, M j * (f j - bar) * f j) =
              ∑ j, (M j * f j ^ 2 - bar * (M j * f j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (∑ j, M j * f j ^ 2) - ∑ j, bar * (M j * f j) :=
            fintype_sum_sub (fun j => M j * f j ^ 2) (fun j => bar * (M j * f j))
          _ = (∑ j, M j * f j ^ 2) - bar * (∑ j, M j * f j) := by
            congr 1
            calc
              (∑ j, bar * (M j * f j)) = ∑ j, (M j * f j) * bar := by
                apply Finset.sum_congr rfl
                intro j _
                ring
              _ = bar * (∑ j, M j * f j) := fintype_sum_mul_const _ _
      _ = (∑ j, M j * f j ^ 2) - bar * num := by rfl
      _ = varF - bar ^ 2 * trM := by rw [← hbarMean]; ring
  have hmetric : (∑ j, y j ^ 2 / M j) = varF - bar ^ 2 * trM := by
    calc
      (∑ j, y j ^ 2 / M j) = ∑ j, M j * (f j - bar) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [y]
        field_simp [(hMpos j).ne']
      _ = ∑ j, y j * (f j - bar) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [y]
        ring
      _ = (∑ j, y j * f j) - bar * (∑ j, y j) := by
        simp_rw [mul_sub]
        rw [fintype_sum_sub, fintype_sum_mul_const]
      _ = (∑ j, y j * f j) - bar * 0 := by rw [hyneutral]
      _ = varF - bar ^ 2 * trM := by rw [hsumYF]; ring
  have hmetricNonneg : 0 ≤ ∑ j, y j ^ 2 / M j := by
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (sq_nonneg _) (hMpos j).le
  have hmetricCompare : (∑ j, y j ^ 2 / p j ^ 2) ≤
      (1 + 10 * C ^ 4 * power t beta) * (∑ j, y j ^ 2 / M j) := by
    have hterm : ∀ j, y j ^ 2 / p j ^ 2 =
        (q j / p j) * (y j ^ 2 / M j) := by
      intro j
      dsimp [M]
      have hpne := (hpPos j).ne'
      have hqne := (hqPos j).ne'
      field_simp [hpne, hqne]
    calc
      (∑ j, y j ^ 2 / p j ^ 2) = ∑ j, (q j / p j) * (y j ^ 2 / M j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j
      _ ≤ ∑ j, (1 + 10 * C ^ 4 * power t beta) * (y j ^ 2 / M j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
          (hratios j).2.2 (div_nonneg (sq_nonneg _) (hMpos j).le)
      _ = (1 + 10 * C ^ 4 * power t beta) * (∑ j, y j ^ 2 / M j) := by
        rw [Finset.mul_sum]
  have hdualLower : 2 * (∑ j, y j * f j) -
      (varF - (s.F t ^ 3) i i) ≤ s.X t y := by
    have h := dualForm_ge_test t C Λ W s hs i y f hyneutral
    rw [qform_D_row_test t s i (fun j => (hpPos j).ne') hFsym] at h
    simpa [F, p, q, M, f, varF, State.X] using h
  have hsharp := hs.sharp y hyneutral
  have hκ : 0 ≤ power t kappa := le_of_lt (Real.rpow_pos_of_pos hs.scale.1 _)
  have hκle1 : power t kappa ≤ 1 := by
    dsimp [power]
    exact Real.rpow_le_one hs.scale.1.le hs.scale.2.le (by norm_num [kappa, delta])
  have hβleκ : power t beta ≤ power t kappa := by
    dsimp [power]
    have hexp : kappa ≤ beta := by norm_num [kappa, beta, delta]
    exact Real.rpow_le_rpow_of_exponent_ge hs.scale.1 hs.scale.2.le hexp
  have hC4C5 : C ^ 4 ≤ C ^ 5 := by
    calc
      C ^ 4 = C ^ 4 * 1 := by ring
      _ ≤ C ^ 4 * C := mul_le_mul_of_nonneg_left hC (by positivity)
      _ = C ^ 5 := by ring
  have hCtoC5 : C ≤ C ^ 5 := le_trans hCtoC2 <| le_trans hC2toC3 <| le_trans hC3toC4 hC4C5
  have hcoefSmall :
      (1 + C * power t kappa) * (1 + 10 * C ^ 4 * power t beta) ≤
        1 + 30 * C ^ 5 * power t kappa := by
    have hA : 0 ≤ 1 + C * power t kappa := by positivity
    have hcoef : C + 10 * C ^ 4 + 10 * C ^ 5 ≤ 30 * C ^ 5 := by
      nlinarith [hCtoC5, hC4C5]
    have hκsq : (power t kappa) ^ 2 ≤ power t kappa :=
      by simpa [pow_two] using mul_le_mul_of_nonneg_left hκle1 hκ
    calc
      (1 + C * power t kappa) * (1 + 10 * C ^ 4 * power t beta) ≤
          (1 + C * power t kappa) * (1 + 10 * C ^ 4 * power t kappa) :=
        mul_le_mul_of_nonneg_left (by gcongr) hA
      _ ≤ 1 + 30 * C ^ 5 * power t kappa := by
        nlinarith [hcoef, hκsq]
  have hsharpUpper : s.X t y ≤
      (1 + 30 * C ^ 5 * power t kappa) * (∑ j, y j ^ 2 / M j) +
        C * t * Λ y := by
    calc
      s.X t y ≤ (1 + C * power t kappa) * (∑ j, y j ^ 2 / p j ^ 2) + C * t * Λ y := hsharp
      _ ≤ (1 + C * power t kappa) *
            ((1 + 10 * C ^ 4 * power t beta) * (∑ j, y j ^ 2 / M j)) + C * t * Λ y :=
        add_le_add (mul_le_mul_of_nonneg_left hmetricCompare (by positivity)) le_rfl
      _ = ((1 + C * power t kappa) * (1 + 10 * C ^ 4 * power t beta)) *
            (∑ j, y j ^ 2 / M j) + C * t * Λ y := by ring
      _ ≤ (1 + 30 * C ^ 5 * power t kappa) * (∑ j, y j ^ 2 / M j) + C * t * Λ y := by
        gcongr
  have hvarBound : varF ≤ 2 * H := by
    dsimp [varF]
    calc
      (∑ j, M j * f j ^ 2) ≤ ∑ j, 2 * (F i j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hr := (hratios j).2.1
        have hterm : M j * f j ^ 2 = (q j / p j) * (F i j) ^ 2 := by
          dsimp [M, f]
          field_simp [(hpPos j).ne']
        rw [hterm]
        exact mul_le_mul_of_nonneg_right (le_trans hr (by norm_num)) (sq_nonneg _)
      _ ≤ 2 * H := by
        calc
          (∑ j, 2 * (F i j) ^ 2) = 2 * (∑ j, (F i j) ^ 2) := by rw [Finset.mul_sum]
          _ ≤ 2 * H := mul_le_mul_of_nonneg_left hfourth (by norm_num)
  have hmetricLeVar : (∑ j, y j ^ 2 / M j) ≤ varF := by
    rw [hmetric]
    have hbarT : 0 ≤ bar ^ 2 * trM := mul_nonneg (sq_nonneg _) hTpos.le
    linarith
  have hYFmetric : (∑ j, y j * f j) = ∑ j, y j ^ 2 / M j := by
    rw [hsumYF, hmetric]
  have hmetricId : varF - (∑ j, y j ^ 2 / M j) = bar ^ 2 * trM := by
    rw [hmetric]
    ring
  have hcubeSharp : (s.F t ^ 3) i i ≤
      30 * C ^ 5 * power t kappa * varF + bar ^ 2 * trM + C * t * Λ y := by
    rw [hYFmetric] at hdualLower
    have hcombined := le_trans hdualLower hsharpUpper
    have hcubeMetric : (s.F t ^ 3) i i ≤
        30 * C ^ 5 * power t kappa * (∑ j, y j ^ 2 / M j) +
          bar ^ 2 * trM + C * t * Λ y := by
      linarith [hcombined, hmetricId]
    have hcoef0 : 0 ≤ 30 * C ^ 5 * power t kappa := by positivity
    exact hcubeMetric.trans (by
      gcongr
      )
  have hfnonneg : ∀ j, 0 ≤ f j := by
    intro j
    dsimp [f]
    exact div_nonneg (hFnonneg i j) (hpPos j).le
  have hYl1 : l1 y ≤ 30 * C ^ 4 := by
    unfold l1
    calc
      (∑ j, ‖y j‖) ≤ ∑ j, M j * (f j + bar) := by
        apply Finset.sum_le_sum
        intro j _
        have hf0 : 0 ≤ f j := hfnonneg j
        have habs : |f j - bar| ≤ f j + bar := by
          rw [abs_le]
          constructor <;> nlinarith [hfnonneg j, hbarNonneg]
        have hy' : ‖y j‖ = M j * |f j - bar| := by
          change ‖M j * (f j - bar)‖ = M j * |f j - bar|
          simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hMpos j).le]
        rw [hy']
        exact mul_le_mul_of_nonneg_left habs (hMpos j).le
      _ = num + bar * trM := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hsumMb]
      _ = 2 * num := by rw [hbarMean]; ring
      _ ≤ 30 * C ^ 4 := by nlinarith [hnumBound]
  have hY2 : (∑ j, y j ^ 2) ≤ 4 * C ^ 2 * H := by
    have hYmetric : (∑ j, y j ^ 2) ≤ 2 * C ^ 2 * (∑ j, y j ^ 2 / M j) := by
      calc
        (∑ j, y j ^ 2) = ∑ j, M j * (y j ^ 2 / M j) := by
          apply Finset.sum_congr rfl
          intro j _
          field_simp [(hMpos j).ne']
        _ ≤ ∑ j, (2 * C ^ 2) * (y j ^ 2 / M j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hMhi j)
            (div_nonneg (sq_nonneg _) (hMpos j).le)
        _ = 2 * C ^ 2 * (∑ j, y j ^ 2 / M j) := by rw [Finset.mul_sum]
    calc
      (∑ j, y j ^ 2) ≤ 2 * C ^ 2 * (∑ j, y j ^ 2 / M j) := hYmetric
      _ ≤ 2 * C ^ 2 * varF :=
        mul_le_mul_of_nonneg_left hmetricLeVar (by positivity)
      _ ≤ 4 * C ^ 2 * H := by nlinarith [hvarBound]
  have hYl2 : l2sq y ≤ 4 * C ^ 2 * H := by
    change (∑ j, ‖y j‖ ^ 2) ≤ 4 * C ^ 2 * H
    simpa [Real.norm_eq_abs, sq_abs] using hY2
  have hHnonneg : 0 ≤ H := le_of_lt (Real.rpow_pos_of_pos hs.scale.1 _)
  have hFourierBound : C * t * Λ y ≤
      (C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
        power t (1 + delta + kappa) := by
    have hL1pos : 0 ≤ l1 y := by
      unfold l1
      exact Finset.sum_nonneg fun j _ => norm_nonneg _
    have hL1cap : l1 y ≤ 30 * C ^ 4 := hYl1
    have hL2pos : 0 ≤ l2sq y := by
      unfold l2sq
      exact Finset.sum_nonneg fun j _ => sq_nonneg _
    have hpowVnonneg : 0 ≤ power (l2sq y) (1 / 3) :=
      Real.rpow_nonneg hL2pos _
    have hL2cap : l2sq y ≤ 4 * C ^ 2 * H := hYl2
    have hExp1 : 0 ≤ (4 / 3 : ℝ) := by norm_num
    have hExp2 : 0 ≤ (1 / 3 : ℝ) := by norm_num
    have hpowL : power (l1 y) (4 / 3) ≤ power (30 * C ^ 4) (4 / 3) := by
      exact Real.rpow_le_rpow hL1pos hL1cap hExp1
    have hpowV : power (l2sq y) (1 / 3) ≤ power (4 * C ^ 2 * H) (1 / 3) := by
      exact Real.rpow_le_rpow hL2pos hL2cap hExp2
    have hFourier := hs.fourier y hyneutral
    have hΛ : Λ y ≤ C * power (30 * C ^ 4) (4 / 3) *
        power (4 * C ^ 2 * H) (1 / 3) := by
      calc
        Λ y ≤ C * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3) := hFourier
        _ ≤ C * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2 * H) (1 / 3) := by
          have hpowL' : C * power (l1 y) (4 / 3) ≤ C * power (30 * C ^ 4) (4 / 3) := by
            gcongr
          have hCoeff1 : 0 ≤ C * power (30 * C ^ 4) (4 / 3) :=
            mul_nonneg hCpos.le (Real.rpow_nonneg (by positivity) _)
          calc
            C * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3) =
                (C * power (l1 y) (4 / 3)) * power (l2sq y) (1 / 3) := by ring
            _ ≤ (C * power (30 * C ^ 4) (4 / 3)) * power (l2sq y) (1 / 3) :=
              mul_le_mul_of_nonneg_right hpowL' hpowVnonneg
            _ ≤ (C * power (30 * C ^ 4) (4 / 3)) * power (4 * C ^ 2 * H) (1 / 3) :=
              mul_le_mul_of_nonneg_left hpowV hCoeff1
            _ = C * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2 * H) (1 / 3) := by ring
    have hHPow : power (4 * C ^ 2 * H) (1 / 3) =
        power (4 * C ^ 2) (1 / 3) * power t ((1 + delta) / 3) := by
      change Real.rpow (4 * C ^ 2 * H) (1 / 3) =
        Real.rpow (4 * C ^ 2) (1 / 3) * Real.rpow t ((1 + delta) / 3)
      have hV : 0 ≤ 4 * C ^ 2 := by positivity
      have hmulRpow : Real.rpow (4 * C ^ 2 * H) (1 / 3) =
          Real.rpow (4 * C ^ 2) (1 / 3) * Real.rpow H (1 / 3) := by
        exact Real.mul_rpow hV hHnonneg
      have hbase : Real.rpow H (1 / 3) = Real.rpow t ((1 + delta) / 3) := by
        change Real.rpow (Real.rpow t (1 + delta)) (1 / 3) = _
        calc
          Real.rpow (Real.rpow t (1 + delta)) (1 / 3) =
              Real.rpow t ((1 + delta) * (1 / 3)) :=
            (Real.rpow_mul hs.scale.1.le (1 + delta) (1 / 3)).symm
          _ = Real.rpow t ((1 + delta) / 3) := by congr 1 <;> ring
      calc
        Real.rpow (4 * C ^ 2 * H) (1 / 3) =
            Real.rpow (4 * C ^ 2) (1 / 3) * Real.rpow H (1 / 3) := hmulRpow
        _ = Real.rpow (4 * C ^ 2) (1 / 3) * Real.rpow t ((1 + delta) / 3) := by rw [hbase]
    have hExp : 1 + (1 + delta) / 3 ≥ 1 + delta + kappa := by
      norm_num [delta, kappa]
    have hPowerDecay : power t (1 + (1 + delta) / 3) ≤ power t (1 + delta + kappa) := by
      dsimp [power]
      exact Real.rpow_le_rpow_of_exponent_ge hs.scale.1 hs.scale.2.le hExp
    have hprod : t * power t ((1 + delta) / 3) = power t (1 + (1 + delta) / 3) := by
      dsimp [power]
      simpa [Real.rpow_one] using (Real.rpow_add hs.scale.1 1 ((1 + delta) / 3)).symm
    have htPow : t * power t ((1 + delta) / 3) ≤ power t (1 + delta + kappa) := by
      rw [hprod]
      exact hPowerDecay
    calc
      C * t * Λ y ≤ C ^ 2 * t * power (30 * C ^ 4) (4 / 3) *
          power (4 * C ^ 2 * H) (1 / 3) := by
        calc
          C * t * Λ y ≤ (C * t) *
              (C * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2 * H) (1 / 3)) :=
            mul_le_mul_of_nonneg_left hΛ (mul_nonneg hCpos.le hs.scale.1.le)
          _ = C ^ 2 * t * power (30 * C ^ 4) (4 / 3) *
              power (4 * C ^ 2 * H) (1 / 3) := by ring
      _ = (C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
          (t * power t ((1 + delta) / 3)) := by rw [hHPow]; ring
      _ ≤ (C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
          power t (1 + delta + kappa) :=
        mul_le_mul_of_nonneg_left htPow (by
          apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · exact Real.rpow_nonneg (by positivity) _
          · exact Real.rpow_nonneg (by positivity) _)
  have hTcross : (Fintype.card (Fin n) : ℝ) ≤ 2 * C ^ 2 * trM := by
    have hmul := mul_le_mul_of_nonneg_left hTlo (by positivity : 0 ≤ 2 * C ^ 2)
    have hcancel : 2 * C ^ 2 * ((Fintype.card (Fin n) : ℝ) / (2 * C ^ 2)) =
        (Fintype.card (Fin n) : ℝ) := by
      field_simp
    rw [hcancel] at hmul
    exact hmul
  have hTinv : 1 / trM ≤ (2 * C ^ 2) / (Fintype.card (Fin n) : ℝ) :=
    (div_le_div_iff₀ hTpos hn).2 (by simpa using hTcross)
  have hbarVarEq : bar ^ 2 * trM = num ^ 2 / trM := by
    dsimp [bar]
    field_simp [hTpos.ne']
  have hnumSq : num ^ 2 ≤ (15 * C ^ 4) ^ 2 :=
    (sq_le_sq₀ hnumPos (by positivity)).2 hnumBound
  have hbarVar : bar ^ 2 * trM ≤ 450 * C ^ 10 /
      (Fintype.card (Fin n) : ℝ) := by
    rw [hbarVarEq]
    calc
      num ^ 2 / trM = num ^ 2 * (1 / trM) := by
        rw [div_eq_mul_inv]
        simp [one_div]
      _ ≤ (15 * C ^ 4) ^ 2 * ((2 * C ^ 2) / (Fintype.card (Fin n) : ℝ)) :=
        mul_le_mul hnumSq hTinv (by positivity) (by positivity)
      _ = (450 * C ^ 10) / (Fintype.card (Fin n) : ℝ) := by ring
  have hbarVol : bar ^ 2 * trM ≤ 450 * C ^ 11 * power t (1 + delta + kappa) := by
    calc
      bar ^ 2 * trM ≤ (450 * C ^ 10) / (Fintype.card (Fin n) : ℝ) := hbarVar
      _ ≤ 450 * C ^ 10 * (C * power t (1 + delta + kappa)) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hs.volume (by positivity)
      _ = 450 * C ^ 11 * power t (1 + delta + kappa) := by ring
  have hpowAdd : power t (1 + delta + kappa) = power t kappa * rowCap t := by
    dsimp [power, rowCap]
    have hexp : 1 + delta + kappa = kappa + (1 + delta) := by ring
    rw [hexp, Real.rpow_add hs.scale.1 kappa (1 + delta)]
  have hbarVol' : bar ^ 2 * trM ≤ 450 * C ^ 11 * power t kappa * rowCap t := by
    calc
      bar ^ 2 * trM ≤ 450 * C ^ 11 * power t (1 + delta + kappa) := hbarVol
      _ = 450 * C ^ 11 * power t kappa * rowCap t := by rw [hpowAdd]; ring
  have hFourierFinal : C * t * Λ y ≤
      (C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
        power t kappa * rowCap t := by
    calc
      C * t * Λ y ≤ (C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
          power t (1 + delta + kappa) := hFourierBound
      _ = (C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
          power t kappa * rowCap t := by rw [hpowAdd]; ring
  have hcubeFirst : 30 * C ^ 5 * power t kappa * varF ≤
      60 * C ^ 5 * power t kappa * rowCap t := by
    calc
      30 * C ^ 5 * power t kappa * varF ≤
          30 * C ^ 5 * power t kappa * (2 * H) :=
        mul_le_mul_of_nonneg_left hvarBound (by positivity)
      _ = 60 * C ^ 5 * power t kappa * rowCap t := by dsimp [H]; ring
  have hcubeWithConstants : (s.F t ^ 3) i i ≤
      (60 * C ^ 5 + 450 * C ^ 11 +
        C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
        power t kappa * rowCap t := by
    calc
      (s.F t ^ 3) i i ≤ 30 * C ^ 5 * power t kappa * varF +
          bar ^ 2 * trM + C * t * Λ y := hcubeSharp
      _ ≤ 60 * C ^ 5 * power t kappa * rowCap t +
          450 * C ^ 11 * power t kappa * rowCap t +
          (C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
            power t kappa * rowCap t := by
        linarith [hcubeFirst, hbarVol', hFourierFinal]
      _ = (60 * C ^ 5 + 450 * C ^ 11 +
          C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3)) *
            power t kappa * rowCap t := by ring
  have hC5C12 : C ^ 5 ≤ C ^ 12 := by gcongr <;> norm_num
  have hC11C12 : C ^ 11 ≤ C ^ 12 := by gcongr <;> norm_num
  have hcoefFinal : 60 * C ^ 5 + 450 * C ^ 11 +
      C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3) ≤
      1000 * C ^ 12 + C ^ 2 * power (30 * C ^ 4) (4 / 3) * power (4 * C ^ 2) (1 / 3) := by
    nlinarith [hC5C12, hC11C12]
  have hscaleNonneg : 0 ≤ power t kappa * rowCap t := mul_nonneg hκ hHnonneg
  exact hcubeWithConstants.trans (by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoefFinal hscaleNonneg)

theorem analytic_prestate_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n : ℕ) (t : ℝ) (s : State (Fin n)) (Λplus Wstar : Form (Fin n)),
    t < t0 → Prestate t C Λplus Wstar s →
    (∀ i, ‖s.rawLag i‖ ≤ C' * power t beta ∧ |s.q i - s.p i| ≤ C' * power t beta ∧
      (∑ j, s.F t i j) ≤ C' ∧ ‖s.h t i i‖ ≤ C' * Real.sqrt t) ∧
    (∀ i, ‖diagonal (s.h t i) * s.h t‖^2 ≤ C' * power t (delta / 2)) ∧
    (∀ i, (s.F t ^ 3) i i ≤ C' * power t kappa * rowCap t) := by
  intro C hC
  let K : ℝ := 1000 * C ^ 12 + C ^ 2 * power (30 * C ^ 4) (4 / 3) *
    power (4 * C ^ 2) (1 / 3)
  let C' : ℝ := 1 + 10 * C ^ 3 + 20 * C ^ 4 + K
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    have hpow1 : 0 ≤ power (30 * C ^ 4) (4 / 3) := by
      dsimp [power]
      exact Real.rpow_nonneg (by positivity) _
    have hpow2 : 0 ≤ power (4 * C ^ 2) (1 / 3) := by
      dsimp [power]
      exact Real.rpow_nonneg (by positivity) _
    positivity
  have h10nonneg : 0 ≤ 10 * C ^ 3 := by positivity
  have h20nonneg : 0 ≤ 20 * C ^ 4 := by positivity
  have hC'pos : 0 < C' := by
    dsimp [C']
    linarith [hKnonneg, h10nonneg, h20nonneg]
  have h10le : 10 * C ^ 3 ≤ C' := by
    dsimp [C']
    linarith [hKnonneg, h20nonneg]
  have h20le : 20 * C ^ 4 ≤ C' := by
    dsimp [C']
    linarith [hKnonneg, h10nonneg]
  have hKle : K ≤ C' := by
    dsimp [C']
    linarith [h10nonneg, h20nonneg]
  obtain ⟨t0, ht0pos, _ht0le, hsmallAt⟩ := exists_small_scale hC
  refine ⟨C', hC'pos, t0, ht0pos, ?_⟩
  intro n t s Λplus Wstar ht hs
  obtain ⟨hsmall, hstrong⟩ := hsmallAt t hs.scale.1 ht
  have hBroad := broad_prestate_bounds t C Λplus Wstar s hs hC hsmall
  have hOperator := ward_operator_bound t C Λplus Wstar s hs hC hsmall
  have hCube := cube_row_bound t C Λplus Wstar s hs hC hstrong
  have hpowBeta : 0 ≤ power t beta :=
    le_of_lt (Real.rpow_pos_of_pos hs.scale.1 beta)
  have hpowDelta : 0 ≤ power t (delta / 2) :=
    le_of_lt (Real.rpow_pos_of_pos hs.scale.1 (delta / 2))
  have hpowKappa : 0 ≤ power t kappa :=
    le_of_lt (Real.rpow_pos_of_pos hs.scale.1 kappa)
  have hrowCap : 0 ≤ rowCap t :=
    le_of_lt (Real.rpow_pos_of_pos hs.scale.1 (1 + delta))
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨hraw, hqp, hrow, hdiag⟩ := hBroad i
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hraw.trans (mul_le_mul_of_nonneg_right h10le hpowBeta)
    · exact hqp.trans (mul_le_mul_of_nonneg_right h10le hpowBeta)
    · exact hrow.trans h10le
    · exact hdiag.trans
        (mul_le_mul_of_nonneg_right h10le (Real.sqrt_nonneg t))
  · intro i
    calc
      ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤
          20 * C ^ 4 * power t (delta / 2) := hOperator i
      _ ≤ C' * power t (delta / 2) :=
        mul_le_mul_of_nonneg_right h20le hpowDelta
  · intro i
    calc
      (s.F t ^ 3) i i ≤ K * power t kappa * rowCap t := by
        simpa [K] using (cube_row_bound t C Λplus Wstar s hs hC hstrong i)
      _ ≤ C' * power t kappa * rowCap t := by
        have hscale : 0 ≤ power t kappa * rowCap t := mul_nonneg hpowKappa hrowCap
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hKle hscale

end AndersonAC.AgentS45
