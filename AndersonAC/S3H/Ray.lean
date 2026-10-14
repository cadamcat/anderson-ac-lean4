import AndersonAC.S3.HelperStatements

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace AndersonAC.S3

/-- Helper: norm of `↑a - ↑b - ↑v * I` equals sqrt of sum of squares. -/
private lemma norm_sub_I_eq (a b v : ℝ) :
    ‖((a : ℂ) - (b : ℂ) - (v : ℂ) * Complex.I)‖ = Real.sqrt ((a - b) ^ 2 + v ^ 2) := by
  have hre : (((a : ℂ) - (b : ℂ) - (v : ℂ) * Complex.I)).re = a - b := by
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have him : (((a : ℂ) - (b : ℂ) - (v : ℂ) * Complex.I)).im = -v := by
    simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him, neg_sq]

/-- Quadratic lower bound `c₁r²/2 ≤ h r` from `c₁r ≤ h'`. -/
private lemma quad_lo_aux (c₁ : ℝ) (ρ : ℝ) (h h' : ℝ → ℝ)
    (hh : ∀ r ∈ Set.Icc (0 : ℝ) ρ, HasDerivAt h (h' r) r ∧ c₁ * r ≤ h' r)
    (hh0 : h 0 = 0) (h0leρ : 0 ≤ ρ)
    (hcont : ContinuousOn h (Set.Icc 0 ρ)) :
    ∀ r ∈ Set.Icc (0 : ℝ) ρ, c₁ * r ^ 2 / 2 ≤ h r := by
  have hDconvex : Convex ℝ (Set.Icc (0 : ℝ) ρ) := convex_Icc 0 ρ
  have hcont_g : ContinuousOn (fun r => h r - c₁ / 2 * r ^ 2) (Set.Icc 0 ρ) :=
    hcont.sub ((continuous_const.mul (continuous_pow 2)).continuousOn)
  have hderiv_g : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ),
      HasDerivWithinAt (fun r => h r - c₁ / 2 * r ^ 2)
        (h' x - c₁ * x) (interior (Set.Icc (0 : ℝ) ρ)) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
    obtain ⟨hdh, hlow⟩ := hh x hxIcc
    have hpow : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
      have h2 := hasDerivAt_pow 2 x
      simpa using h2
    have hcm : HasDerivAt (fun r : ℝ => c₁ / 2 * r ^ 2) (c₁ / 2 * (2 * x)) x :=
      hpow.const_mul (c₁ / 2)
    have heq : c₁ / 2 * (2 * x) = c₁ * x := by ring
    rw [heq] at hcm
    exact (hdh.sub hcm).hasDerivWithinAt
  have hnn : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ), 0 ≤ h' x - c₁ * x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
    obtain ⟨_, hlow⟩ := hh x hxIcc
    linarith
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg hDconvex hcont_g hderiv_g hnn
  intro r hr
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) ρ := ⟨le_refl 0, h0leρ⟩
  have hle := hmono h0mem hr hr.1
  simp [hh0] at hle
  linarith

private def rayDen (h : ℝ → ℝ) (β v r : ℝ) : ℂ :=
  (h r : ℂ) - β - v * Complex.I

private lemma rayDen_re (h : ℝ → ℝ) (β v r : ℝ) :
    (rayDen h β v r).re = h r - β := by simp [rayDen]

private lemma rayDen_im (h : ℝ → ℝ) (β v r : ℝ) :
    (rayDen h β v r).im = -v := by simp [rayDen]

private lemma rayDen_ne (h : ℝ → ℝ) (β r : ℝ) {v : ℝ} (hv : 0 < v) :
    rayDen h β v r ≠ 0 := by
  intro he
  have := congrArg Complex.im he
  simp [rayDen] at this
  linarith

private lemma rayDen_slit (h : ℝ → ℝ) (β r : ℝ) {v : ℝ} (hv : 0 < v) :
    rayDen h β v r ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, rayDen_im]
  exact Or.inr (neg_ne_zero.mpr (ne_of_gt hv))

private lemma rayDen_cont {h : ℝ → ℝ} {β v : ℝ} {s : Set ℝ}
    (hh : ContinuousOn h s) : ContinuousOn (rayDen h β v) s :=
  ((Complex.continuous_ofReal.comp_continuousOn hh).sub continuousOn_const).sub
    continuousOn_const

private lemma rayDen_deriv {h : ℝ → ℝ} {hp β v r : ℝ}
    (hh : HasDerivAt h hp r) :
    HasDerivAt (rayDen h β v) (hp : ℂ) r := by
  exact (hh.ofReal_comp.sub_const (β : ℂ)).sub_const ((v : ℂ) * Complex.I)

private lemma inverse_bound {h : ℝ → ℝ} {β v r A r₀ : ℝ}
    (hv : 0 < v) (hA : 0 < A) (hl : A * |r - r₀| ≤ |h r - β|) :
    ‖(rayDen h β v r)⁻¹‖ ≤ 2 / (A * |r - r₀| + v) := by
  have hx := Complex.abs_re_le_norm (rayDen h β v r)
  have hy := Complex.abs_im_le_norm (rayDen h β v r)
  rw [rayDen_re] at hx
  rw [rayDen_im, abs_neg, abs_of_pos hv] at hy
  have hd : 0 < A * |r - r₀| + v := by positivity
  have hn : 0 < ‖rayDen h β v r‖ := norm_pos_iff.mpr (rayDen_ne h β r hv)
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hn hd]
  linarith

private lemma inverse_gap {h : ℝ → ℝ} {β v r m : ℝ}
    (hv : 0 < v) (hm : 0 < m) (hl : m ≤ |h r - β|) :
    ‖(rayDen h β v r)⁻¹‖ ≤ 1 / m := by
  have hx := Complex.abs_re_le_norm (rayDen h β v r)
  rw [rayDen_re] at hx
  rw [norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le hm (hl.trans hx)

private lemma affine_log_integral (k d a b : ℝ) (hk : k ≠ 0)
    (hab : a ≤ b) (hp : ∀ x ∈ Icc a b, 0 < k * x + d) :
    (∫ x in a..b, (k * x + d)⁻¹) =
      (Real.log (k * b + d) - Real.log (k * a + d)) / k := by
  have hi : ContinuousOn (fun x : ℝ => (k * x + d)⁻¹) (Icc a b) :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousOn.inv₀
      (fun x hx => ne_of_gt (hp x hx))
  have hd : ∀ x ∈ uIcc a b,
      HasDerivAt (fun x : ℝ => Real.log (k * x + d) / k) ((k * x + d)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have ht := ((hasDerivAt_id x).const_mul k).add_const d
    have ht' := (ht.log (ne_of_gt (hp x hx))).div_const k
    convert ht' using 1 <;> dsimp <;> field_simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hi.intervalIntegrable_of_Icc hab)
  simpa [sub_div] using he

private lemma kernel_log_bound {A R ρ r₀ v : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hr₀ : r₀ ∈ Icc 0 ρ)
    (hv : 0 < v) (hv1 : v ≤ 1) :
    (∫ r in (0 : ℝ)..ρ, (A * |r - r₀| + v)⁻¹) ≤
      (2 / A * (1 + Real.log (A * R + 1) / Real.log 2)) * Real.log (2 / v) := by
  have hc : Continuous (fun r : ℝ => (A * |r - r₀| + v)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro r; have : 0 < A * |r - r₀| + v := by positivity
      exact ne_of_gt this
  have e1 : (∫ r in (0 : ℝ)..r₀, (A * |r - r₀| + v)⁻¹) =
      (Real.log (A * r₀ + v) - Real.log v) / A := by
    calc _ = ∫ r in (0 : ℝ)..r₀, (-A * r + (A * r₀ + v))⁻¹ := by
           apply intervalIntegral.integral_congr
           intro r hr
           rw [uIcc_of_le hr₀.1] at hr
           dsimp only
           rw [abs_of_nonpos (by linarith [hr.2] : r - r₀ ≤ 0)]
           congr 1; ring
      _ = _ := by
        rw [affine_log_integral (-A) (A * r₀ + v) 0 r₀ (neg_ne_zero.mpr hA.ne') hr₀.1]
        · have he : -A * r₀ + (A * r₀ + v) = v := by ring
          simp only [he, mul_zero, zero_add]
          field_simp <;> ring
        · intro r hr
          have : 0 ≤ A * (r₀ - r) := mul_nonneg hA.le (by linarith [hr.2])
          linarith
  have e2 : (∫ r in r₀..ρ, (A * |r - r₀| + v)⁻¹) =
      (Real.log (A * (ρ - r₀) + v) - Real.log v) / A := by
    calc _ = ∫ r in r₀..ρ, (A * r + (v - A * r₀))⁻¹ := by
           apply intervalIntegral.integral_congr
           intro r hr
           rw [uIcc_of_le hr₀.2] at hr
           dsimp only
           rw [abs_of_nonneg (by linarith [hr.1] : 0 ≤ r - r₀)]
           congr 1; ring
      _ = _ := by
        rw [affine_log_integral A (v - A * r₀) r₀ ρ hA.ne' hr₀.2]
        · congr 2 <;> congr 1 <;> ring
        · intro r hr
          have : 0 ≤ A * (r - r₀) := mul_nonneg hA.le (by linarith [hr.1])
          linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 r₀) (hc.intervalIntegrable r₀ ρ), e1, e2]
  have hl1 : Real.log (A * r₀ + v) ≤ Real.log (A * R + 1) :=
    Real.log_le_log (by have : 0 ≤ A * r₀ := mul_nonneg hA.le hr₀.1; linarith)
      (by nlinarith [hr₀.2])
  have hl2 : Real.log (A * (ρ - r₀) + v) ≤ Real.log (A * R + 1) :=
    Real.log_le_log (by have : 0 ≤ A * (ρ - r₀) := mul_nonneg hA.le (by linarith [hr₀.2]); linarith)
      (by nlinarith [hr₀.1])
  have hl0 : 0 ≤ Real.log (A * R + 1) := Real.log_nonneg (by nlinarith)
  have hlv : Real.log v ≤ 0 := Real.log_nonpos hv.le hv1
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : Real.log (2 / v) = Real.log 2 - Real.log v := by
    rw [Real.log_div (by norm_num) hv.ne']
  have hscaled : Real.log (A * R + 1) ≤
      Real.log (A * R + 1) / Real.log 2 * Real.log (2 / v) := by
    rw [ht]
    have : 0 ≤ Real.log (A * R + 1) / Real.log 2 := div_nonneg hl0 hl2pos.le
    have he : Real.log (A * R + 1) / Real.log 2 * Real.log 2 = Real.log (A * R + 1) :=
      div_mul_cancel₀ _ hl2pos.ne'
    nlinarith
  have hsum : (Real.log (A * r₀ + v) - Real.log v) +
      (Real.log (A * (ρ - r₀) + v) - Real.log v) ≤
      2 * (1 + Real.log (A * R + 1) / Real.log 2) * Real.log (2 / v) := by
    rw [ht] at *; nlinarith
  calc _ = ((Real.log (A * r₀ + v) - Real.log v) +
             (Real.log (A * (ρ - r₀) + v) - Real.log v)) / A := by ring
    _ ≤ (2 * (1 + Real.log (A * R + 1) / Real.log 2) * Real.log (2 / v)) / A :=
      div_le_div_of_nonneg_right hsum hA.le
    _ = _ := by ring

private lemma log_norm_bound {z : ℂ} {m B : ℝ}
    (hm : 0 < m) (hlo : m ≤ ‖z‖) (hhi : ‖z‖ ≤ B) :
    ‖Complex.log z‖ ≤ |Real.log m| + |Real.log B| + Real.pi := by
  have hn : 0 < ‖z‖ := hm.trans_le hlo
  have hb : 0 < B := hn.trans_le hhi
  have h1 := Real.log_le_log hm hlo
  have h2 := Real.log_le_log hn hhi
  have hl : |Real.log ‖z‖| ≤ |Real.log m| + |Real.log B| := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (Real.log B), neg_abs_le (Real.log m),
      abs_nonneg (Real.log B), abs_nonneg (Real.log m)]
  have hi : |z.arg| ≤ Real.pi := abs_le.mpr
    ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
         Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by rw [Complex.log_re, Complex.log_im]; linarith

private lemma inverse_distance_bound {h : ℝ → ℝ} {β v r A r₀ : ℝ}
    (hv : 0 < v) (hA : 0 < A) (hl : A * |r - r₀| ≤ |h r - β|) :
    |r - r₀| * ‖(rayDen h β v r)⁻¹‖ ≤ 1 / A := by
  have hx := Complex.abs_re_le_norm (rayDen h β v r)
  rw [rayDen_re] at hx
  have he : ‖rayDen h β v r‖ * ‖(rayDen h β v r)⁻¹‖ = 1 := by
    rw [norm_inv, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (rayDen_ne h β r hv))]
  have hh := mul_le_mul_of_nonneg_right (hl.trans hx)
    (norm_nonneg ((rayDen h β v r)⁻¹))
  rw [he] at hh
  apply (le_div_iff₀ hA).mpr
  nlinarith

private lemma bounded_deriv_integrable {q : ℝ → ℂ} {a b T : ℝ}
    (hab : a ≤ b) (hq : ∀ x ∈ Icc a b, ‖deriv q x‖ ≤ T) :
    IntervalIntegrable (deriv q) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply IntegrableOn.of_bound (measure_Icc_lt_top) (aestronglyMeasurable_deriv q _) T
  exact (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ hq)

private lemma first_cancellation_bound {h hp : ℝ → ℝ} {q : ℝ → ℂ}
    {a b r₀ β v A L Q T J : ℝ} (hab : a ≤ b) (hr₀ : r₀ ∈ Icc a b)
    (hv : 0 < v) (hA : 0 < A) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hder : ∀ r ∈ Icc a b, HasDerivAt h (hp r) r)
    (hpc : ContinuousOn hp (Icc a b)) (hqc : ContinuousOn q (Icc a b))
    (hqb : ‖q r₀‖ ≤ Q)
    (hql : ∀ r ∈ Icc a b, ‖q r - q r₀‖ ≤ T * |r - r₀|)
    (hpb : ∀ r ∈ Icc a b, |hp r| ≤ L)
    (hsep : ∀ r ∈ Icc a b, A * |r - r₀| ≤ |h r - β|)
    (hla : ‖Complex.log (rayDen h β v a)‖ ≤ J)
    (hlb : ‖Complex.log (rayDen h β v b)‖ ≤ J) :
    ‖∫ r in a..b, q r * (hp r : ℂ) * (rayDen h β v r)⁻¹‖ ≤
      2 * Q * J + T * L / A * (b - a) := by
  have hhc : ContinuousOn h (Icc a b) := fun r hr =>
    (hder r hr).continuousAt.continuousWithinAt
  have hrc := (rayDen_cont hhc).inv₀ (fun r _ => rayDen_ne h β r hv)
  have hc := (Complex.continuous_ofReal.comp_continuousOn hpc).mul hrc
  have hi : IntervalIntegrable (fun r => (hp r : ℂ) * (rayDen h β v r)⁻¹) volume a b := hc.intervalIntegrable_of_Icc hab
  have hec : ContinuousOn (fun r => (q r - q r₀) * ((hp r : ℂ) * (rayDen h β v r)⁻¹)) (Icc a b) := (hqc.sub continuousOn_const).mul hc
  have hei : IntervalIntegrable (fun r => (q r - q r₀) * ((hp r : ℂ) * (rayDen h β v r)⁻¹)) volume a b := hec.intervalIntegrable_of_Icc hab
  have hlog : (∫ r in a..b, (hp r : ℂ) * (rayDen h β v r)⁻¹) =
      Complex.log (rayDen h β v b) - Complex.log (rayDen h β v a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
    intro r hr
    rw [uIcc_of_le hab] at hr
    simpa [div_eq_mul_inv] using
      (rayDen_deriv (hder r hr)).clog_real (rayDen_slit h β r hv)
  have he : (∫ r in a..b, q r * (hp r : ℂ) * (rayDen h β v r)⁻¹) =
      q r₀ * (Complex.log (rayDen h β v b) - Complex.log (rayDen h β v a)) +
        ∫ r in a..b, (q r - q r₀) * ((hp r : ℂ) * (rayDen h β v r)⁻¹) := by
    calc _ = ∫ r in a..b, q r₀ * ((hp r : ℂ) * (rayDen h β v r)⁻¹) +
             (q r - q r₀) * ((hp r : ℂ) * (rayDen h β v r)⁻¹) := by
               apply intervalIntegral.integral_congr; intro r _; ring
      _ = _ := by rw [intervalIntegral.integral_add (hi.const_mul _) hei,
          intervalIntegral.integral_const_mul, hlog]
  have herr : ‖∫ r in a..b, (q r - q r₀) *
      ((hp r : ℂ) * (rayDen h β v r)⁻¹)‖ ≤ T * L / A * (b - a) := by
    have ht := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := T * L / A)
      (f := fun r => (q r - q r₀) * ((hp r : ℂ) * (rayDen h β v r)⁻¹))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at ht
    apply ht
    intro r hr
    rw [uIoc_of_le hab] at hr
    have hr' : r ∈ Icc a b := ⟨hr.1.le, hr.2⟩
    have hd := inverse_distance_bound hv hA (hsep r hr')
    calc ‖(q r - q r₀) * ((hp r : ℂ) * (rayDen h β v r)⁻¹)‖ =
          ‖q r - q r₀‖ * (|hp r| * ‖(rayDen h β v r)⁻¹‖) := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (T * |r - r₀|) * (L * ‖(rayDen h β v r)⁻¹‖) :=
        mul_le_mul (hql r hr')
          (mul_le_mul_of_nonneg_right (hpb r hr') (norm_nonneg _))
          (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (T * L) * (|r - r₀| * ‖(rayDen h β v r)⁻¹‖) := by ring
      _ ≤ (T * L) * (1 / A) := mul_le_mul_of_nonneg_left hd (mul_nonneg hT hL)
      _ = T * L / A := by ring
  have hend : ‖q r₀ * (Complex.log (rayDen h β v b) -
      Complex.log (rayDen h β v a))‖ ≤ 2 * Q * J := by
    rw [norm_mul]
    calc _ ≤ Q * (‖Complex.log (rayDen h β v b)‖ + ‖Complex.log (rayDen h β v a)‖) :=
        mul_le_mul hqb (norm_sub_le _ _) (norm_nonneg _) hQ
      _ ≤ Q * (J + J) := mul_le_mul_of_nonneg_left (add_le_add hlb hla) hQ
      _ = _ := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

private lemma second_parts_bound {h hp : ℝ → ℝ} {q : ℝ → ℂ}
    {a b β v Q T : ℝ} (hab : a ≤ b) (hv : 0 < v) (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hder : ∀ r ∈ Icc a b, HasDerivAt h (hp r) r)
    (hpc : ContinuousOn hp (Icc a b))
    (hqd : ∀ r ∈ Icc a b, DifferentiableAt ℝ q r)
    (hqb : ∀ r ∈ Icc a b, ‖q r‖ ≤ Q)
    (hqdb : ∀ r ∈ Icc a b, ‖deriv q r‖ ≤ T) :
    ‖∫ r in a..b, q r * (hp r : ℂ) * (rayDen h β v r)⁻¹ ^ 2‖ ≤
      Q * (‖(rayDen h β v b)⁻¹‖ + ‖(rayDen h β v a)⁻¹‖) +
        T * (∫ r in a..b, ‖(rayDen h β v r)⁻¹‖) := by
  have hhc : ContinuousOn h (Icc a b) := fun r hr =>
    (hder r hr).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Icc a b) := fun r hr =>
    (hqd r hr).continuousAt.continuousWithinAt
  have hrc := (rayDen_cont hhc).inv₀ (fun r _ => rayDen_ne h β r hv)
  have hdc := ((Complex.continuous_ofReal.comp_continuousOn hpc).mul (hrc.pow 2)).neg
  have hri : IntervalIntegrable (fun r => (rayDen h β v r)⁻¹) volume a b := hrc.intervalIntegrable_of_Icc hab
  have hdi : IntervalIntegrable (fun r => -((hp r : ℂ) * (rayDen h β v r)⁻¹ ^ 2)) volume a b := hdc.intervalIntegrable_of_Icc hab
  have hqi := bounded_deriv_integrable hab hqdb
  have he : (∫ r in a..b, q r * (hp r : ℂ) * (rayDen h β v r)⁻¹ ^ 2) =
      -(q b * (rayDen h β v b)⁻¹ - q a * (rayDen h β v a)⁻¹ -
        ∫ r in a..b, deriv q r * (rayDen h β v r)⁻¹) := by
    have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := q) (v := fun r => (rayDen h β v r)⁻¹)
      (u' := deriv q) (v' := fun r => -((hp r : ℂ) * (rayDen h β v r)⁻¹ ^ 2))
      (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])
      (fun r hr => (hqd r (by simpa [min_eq_left hab, max_eq_right hab] using
        (show r ∈ Icc (min a b) (max a b) from ⟨hr.1.le, hr.2.le⟩) : r ∈ Icc a b)).hasDerivAt)
      (fun r hr => by
        have hr' : r ∈ Icc a b := by
          simpa [min_eq_left hab, max_eq_right hab] using (show r ∈ Icc (min a b) (max a b) from ⟨hr.1.le, hr.2.le⟩)
        convert (rayDen_deriv (hder r hr')).inv (rayDen_ne h β r hv) using 1 <;> simp [div_eq_mul_inv, inv_pow])
      hqi hdi
    rw [← hip, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r _; dsimp; ring
  have herr : ‖∫ r in a..b, deriv q r * (rayDen h β v r)⁻¹‖ ≤
      T * (∫ r in a..b, ‖(rayDen h β v r)⁻¹‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ (hri.norm.const_mul T)
    apply ae_of_all; intro r hr
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hqdb r ⟨hr.1.le, hr.2⟩) (norm_nonneg _)
  have hba : ‖q b * (rayDen h β v b)⁻¹ - q a * (rayDen h β v a)⁻¹‖ ≤
      Q * (‖(rayDen h β v b)⁻¹‖ + ‖(rayDen h β v a)⁻¹‖) := by
    calc _ ≤ ‖q b * (rayDen h β v b)⁻¹‖ + ‖q a * (rayDen h β v a)⁻¹‖ := norm_sub_le _ _
      _ ≤ Q * ‖(rayDen h β v b)⁻¹‖ + Q * ‖(rayDen h β v a)⁻¹‖ := by
        simp only [norm_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hqb b ⟨hab, le_rfl⟩) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hqb a ⟨le_rfl, hab⟩) (norm_nonneg _))
      _ = _ := by ring
  rw [he, norm_neg]
  exact (norm_sub_le _ _).trans (add_le_add hba herr)

private lemma quotient_weight_bounds {n : ℕ} {hp hpp : ℝ → ℝ} {a b R P C₂ : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbR : b ≤ R) (hP : 0 < P) (hC₂ : 0 ≤ C₂)
    (hd : ∀ r ∈ Icc a b, HasDerivAt hp (hpp r) r)
    (hl : ∀ r ∈ Icc a b, P ≤ hp r)
    (hhpp : ∀ r ∈ Icc a b, |hpp r| ≤ C₂) :
    let q : ℝ → ℂ := fun r => ((r ^ n / hp r : ℝ) : ℂ)
    (∀ r ∈ Icc a b, DifferentiableAt ℝ q r) ∧
    (∀ r ∈ Icc a b, ‖q r‖ ≤ R ^ n / P) ∧
    (∀ r ∈ Icc a b, ‖deriv q r‖ ≤ (n : ℝ) * R ^ (n - 1) / P + R ^ n * C₂ / P ^ 2) := by
  dsimp only
  have hpow : ∀ r ∈ Icc a b, ∀ k : ℕ, 0 ≤ r ^ k ∧ r ^ k ≤ R ^ k := by
    intro r hr k
    have hr0 := ha.trans hr.1
    exact ⟨pow_nonneg hr0 _, pow_le_pow_left₀ hr0 (hr.2.trans hbR) _⟩
  have hqd : ∀ r ∈ Icc a b,
      HasDerivAt (fun r => ((r ^ n / hp r : ℝ) : ℂ))
        (((n : ℝ) * r ^ (n - 1) / hp r - r ^ n * hpp r / hp r ^ 2 : ℝ) : ℂ) r := by
    intro r hr
    have hp0 := hP.trans_le (hl r hr)
    have ht := (hasDerivAt_pow n r).div (hd r hr) hp0.ne'
    have he : ((n : ℝ) * r ^ (n - 1) * hp r - r ^ n * hpp r) / hp r ^ 2 =
        (n : ℝ) * r ^ (n - 1) / hp r - r ^ n * hpp r / hp r ^ 2 := by
      field_simp
    rw [he] at ht
    exact ht.ofReal_comp
  refine ⟨fun r hr => (hqd r hr).differentiableAt, ?_, ?_⟩
  · intro r hr
    have hp0 := hP.trans_le (hl r hr)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hpow r hr n).1 hp0.le)]
    exact div_le_div₀ ((hpow r hr n).1.trans (hpow r hr n).2) (hpow r hr n).2 hP (hl r hr)
  · intro r hr
    have hp0 := hP.trans_le (hl r hr)
    have hr0 : 0 ≤ r := ha.trans hr.1
    have hR0 : 0 ≤ R := hr0.trans (hr.2.trans hbR)
    rw [(hqd r hr).deriv, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(n : ℝ) * r ^ (n - 1) / hp r| ≤ (n : ℝ) * R ^ (n - 1) / P := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * r ^ (n - 1) / hp r)]
      exact div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (hpow r hr (n - 1)).2 (Nat.cast_nonneg n)) hP (hl r hr)
    have h2 : |r ^ n * hpp r / hp r ^ 2| ≤ R ^ n * C₂ / P ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (hpow r hr n).1,
        abs_of_nonneg (sq_nonneg (hp r))]
      exact div_le_div₀ (by positivity)
        (mul_le_mul (hpow r hr n).2 (hhpp r hr) (abs_nonneg _) (pow_nonneg hR0 n))
        (sq_pos_of_pos hP) (pow_le_pow_left₀ hP.le (hl r hr) 2)
    exact (abs_sub _ _).trans (add_le_add h1 h2)

private lemma imaginary_lower {n : ℕ} {h : ℝ → ℝ} {ρ r₀ rmin β v μ L : ℝ}
    (hρ : 0 ≤ ρ) (hr₀ : r₀ ∈ Icc 0 ρ) (hmin : 0 < rmin) (hminr : rmin ≤ r₀)
    (hv : 0 < v) (hv1 : v ≤ 1) (hμ : 0 < μ) (hL : 0 < L)
    (hhc : ContinuousOn h (Icc 0 ρ)) (hroot : h r₀ = β)
    (hgap : β + μ ≤ h ρ)
    (hlip : ∀ r ∈ Icc 0 ρ, |h r - h r₀| ≤ L * |r - r₀|) :
    rmin ^ n * min 1 μ / (2 * L) ≤
      ∫ r in (0 : ℝ)..ρ, r ^ n * (v / ((h r - β) ^ 2 + v ^ 2)) := by
  let ℓ := min v μ / L
  have hℓ : 0 < ℓ := div_pos (lt_min hv hμ) hL
  have hℓL : L * ℓ = min v μ := by dsimp [ℓ]; field_simp
  have hℓv : L * ℓ ≤ v := by rw [hℓL]; exact min_le_left _ _
  have hℓρ : r₀ + ℓ ≤ ρ := by
    have ht := hlip ρ ⟨hρ, le_rfl⟩
    rw [hroot, abs_of_nonneg (by linarith : 0 ≤ h ρ - β),
      abs_of_nonneg (by linarith [hr₀.2] : 0 ≤ ρ - r₀)] at ht
    have : ℓ ≤ ρ - r₀ := (div_le_iff₀ hL).mpr ((min_le_right v μ).trans (by linarith))
    linarith
  let f : ℝ → ℝ := fun r => r ^ n * (v / ((h r - β) ^ 2 + v ^ 2))
  have hfc : ContinuousOn f (Icc 0 ρ) := by
    apply (continuous_pow n).continuousOn.mul
    apply continuousOn_const.div (((hhc.sub continuousOn_const).pow 2).add continuousOn_const)
    intro r _; have : 0 < (h r - β) ^ 2 + v ^ 2 := by positivity
    exact ne_of_gt this
  have hfi : IntervalIntegrable f volume 0 ρ := hfc.intervalIntegrable_of_Icc hρ
  have hnon : ∀ r ∈ Icc 0 ρ, 0 ≤ f r := by
    intro r hr; dsimp [f]; exact mul_nonneg (pow_nonneg hr.1 n) (by positivity)
  have hsub : Icc r₀ (r₀ + ℓ) ⊆ Icc 0 ρ := Icc_subset_Icc hr₀.1 hℓρ
  have hpoint : ∀ r ∈ Icc r₀ (r₀ + ℓ), rmin ^ n / (2 * v) ≤ f r := by
    intro r hr
    have hr' := hsub hr
    have ht := hlip r hr'
    rw [hroot, abs_of_nonneg (by linarith [hr.1] : 0 ≤ r - r₀)] at ht
    have hhv : |h r - β| ≤ v := by
      have : L * (r - r₀) ≤ L * ℓ := mul_le_mul_of_nonneg_left (by linarith [hr.2]) hL.le
      exact ht.trans (this.trans hℓv)
    have hden : 0 < (h r - β) ^ 2 + v ^ 2 := by positivity
    have hdenb : (h r - β) ^ 2 + v ^ 2 ≤ 2 * v ^ 2 := by
      nlinarith [sq_abs (h r - β), abs_nonneg (h r - β)]
    have hp : rmin ^ n ≤ r ^ n := pow_le_pow_left₀ hmin.le (hminr.trans hr.1) _
    calc _ = rmin ^ n * v / (2 * v ^ 2) := by field_simp <;> ring
      _ ≤ r ^ n * v / ((h r - β) ^ 2 + v ^ 2) :=
        div_le_div₀ (mul_nonneg (pow_nonneg hr'.1 n) hv.le)
          (mul_le_mul_of_nonneg_right hp hv.le) hden hdenb
      _ = f r := by dsimp [f]; ring
  have hi : rmin ^ n / (2 * v) * ℓ ≤ ∫ r in (0 : ℝ)..ρ, f r := by
    have ht := intervalIntegral.integral_mono_on (μ := volume) (show r₀ ≤ r₀ + ℓ by linarith)
      (intervalIntegrable_const) ((hfc.mono hsub).intervalIntegrable_of_Icc (by linarith)) hpoint
    have hm := intervalIntegral.integral_mono_interval hr₀.1 (show r₀ ≤ r₀ + ℓ by linarith)
      hℓρ ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun r hr =>
        hnon r ⟨hr.1.le, hr.2⟩))) hfi
    have he : (∫ r in r₀..r₀ + ℓ, rmin ^ n / (2 * v)) = rmin ^ n / (2 * v) * ℓ := by
      simp only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul]
      ring
    rw [he] at ht
    exact ht.trans hm
  have hminv : min 1 μ * v ≤ min v μ := by
    apply le_min
    · simpa using mul_le_mul_of_nonneg_right (min_le_left 1 μ) hv.le
    · have hm0 : 0 ≤ min 1 μ := (lt_min one_pos hμ).le
      have hm : min 1 μ * v ≤ min 1 μ := by
        simpa using mul_le_mul_of_nonneg_left hv1 hm0
      exact hm.trans (min_le_right 1 μ)
  have hlast : rmin ^ n * min 1 μ / (2 * L) ≤ rmin ^ n / (2 * v) * ℓ := by
    dsimp [ℓ]
    have hm : min 1 μ ≤ min v μ / v := (le_div_iff₀ hv).mpr hminv
    calc _ = (rmin ^ n / (2 * L)) * min 1 μ := by ring
      _ ≤ (rmin ^ n / (2 * L)) * (min v μ / v) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  exact hlast.trans hi

set_option maxHeartbeats 1000000 in
theorem rayEstimates_proof : RayEstimatesStatement := by
  intro n hn c₁ C₂ ρ₁ ρ₂ β₁ β₂ μ hc₁ hρ₁ hρ₁₂ hβ₁ hβ₁₂ hμ
  by_cases hC : c₁ ≤ C₂
  · have hC₂ : 0 < C₂ := lt_of_lt_of_le hc₁ hC
    have hρ₂ : 0 < ρ₂ := lt_of_lt_of_le hρ₁ hρ₁₂
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hpi : 0 < Real.pi := Real.pi_pos
    have hnR : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hn
    set rmin : ℝ := Real.sqrt (2 * β₁ / C₂) with hrmin
    have h2βC : 0 < 2 * β₁ / C₂ := by positivity
    have hrmin_pos : 0 < rmin := Real.sqrt_pos.mpr h2βC
    set m : ℝ := 3 * c₁ * rmin ^ 2 / 8 with hm
    have hm_pos : 0 < m := by
      rw [hm]
      have h1 : 0 < 3 * c₁ * rmin ^ 2 :=
        mul_pos (mul_pos (by norm_num) hc₁) (pow_pos hrmin_pos 2)
      exact div_pos h1 (by norm_num)
    set clen : ℝ := min (c₁ * rmin / 2) (m / ρ₂) with hclen
    have hclen_pos : 0 < clen := lt_min
      (div_pos (mul_pos hc₁ hrmin_pos) (by norm_num))
      (div_pos hm_pos hρ₂)
    set L : ℝ := C₂ * ρ₂ with hL
    have hL_pos : 0 < L := mul_pos hC₂ hρ₂
    set U : ℝ := C₂ * ρ₂ ^ 2 / 2 + β₂ with hU
    have hU_pos : 0 < U := by
      rw [hU]
      have h1 : 0 < C₂ * ρ₂ ^ 2 / 2 :=
        div_pos (mul_pos hC₂ (pow_pos hρ₂ 2)) (by norm_num)
      linarith [hβ₁]
    let a := rmin / 2
    let d := clen * rmin / 2
    let P := c₁ * a
    let Q := ρ₂ ^ n / P
    let T := (n : ℝ) * ρ₂ ^ (n - 1) / P + ρ₂ ^ n * C₂ / P ^ 2
    let K := 2 * (2 / clen * (1 + Real.log (clen * ρ₂ + 1) / Real.log 2))
    let J := |Real.log (min d μ)| + |Real.log (U + 1)| + Real.pi
    let Cabs := ρ₂ ^ n * K
    let Csec := (ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d)) / Real.log 2 + T * K
    let Cfirst := ρ₂ ^ (n + 1) / d + 2 * Q * J + T * L / clen * ρ₂
    let C := max 1 (max Cabs (max Csec Cfirst))
    have ha0 : 0 < a := by dsimp [a]; positivity
    have hd0 : 0 < d := by dsimp [d]; positivity
    have hP0 : 0 < P := mul_pos hc₁ ha0
    have hQ0 : 0 < Q := div_pos (pow_pos hρ₂ n) hP0
    have hT0 : 0 < T := by dsimp [T]; positivity
    have hJ0 : 0 < J := by dsimp [J]; positivity
    have hK0 : 0 < K := by
      have : 0 < Real.log (clen * ρ₂ + 1) := Real.log_pos (by nlinarith)
      dsimp [K]; positivity
    have hCabs : Cabs ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have hCsec : Csec ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hCfirst : Cfirst ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    refine ⟨C, rmin ^ n * min 1 μ / (2 * L), (lt_of_lt_of_le one_pos (le_max_left _ _)),
      div_pos (mul_pos (pow_pos hrmin_pos _) (lt_min one_pos hμ)) (by positivity), ?_⟩
    intro h h' h'' ρ hρl hρu hh0 hh hρh β hβ v hv0 hv1
    have hρpos : 0 < ρ := lt_of_lt_of_le hρ₁ hρl
    have h0leρ : (0 : ℝ) ≤ ρ := le_of_lt hρpos
    have hcont : ContinuousOn h (Set.Icc 0 ρ) := by
      intro x hx
      obtain ⟨hd, _, _, _, _⟩ := hh x hx
      exact hd.continuousAt.continuousWithinAt
    have hquad : ∀ r ∈ Set.Icc (0 : ℝ) ρ, c₁ * r ^ 2 / 2 ≤ h r :=
      quad_lo_aux c₁ ρ h h' (fun r hr => ⟨(hh r hr).1, (hh r hr).2.2.1⟩) hh0 h0leρ hcont
    -- Upper quadratic bound via monotonicity (similar, with C₂).
    have hquad_hi : ∀ r ∈ Set.Icc (0 : ℝ) ρ, h r ≤ C₂ * r ^ 2 / 2 := by
      have hDconvex : Convex ℝ (Set.Icc (0 : ℝ) ρ) := convex_Icc 0 ρ
      have hcont_g : ContinuousOn (fun r => C₂ / 2 * r ^ 2 - h r) (Set.Icc 0 ρ) :=
        ((continuous_const.mul (continuous_pow 2)).continuousOn).sub hcont
      have hderiv_g : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ),
          HasDerivWithinAt (fun r => C₂ / 2 * r ^ 2 - h r)
            (C₂ * x - h' x) (interior (Set.Icc (0 : ℝ) ρ)) x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
        obtain ⟨hdh, _, _, hup, _⟩ := hh x hxIcc
        have hpow : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
          have h2 := hasDerivAt_pow 2 x
          simpa using h2
        have hcm : HasDerivAt (fun r : ℝ => C₂ / 2 * r ^ 2) (C₂ / 2 * (2 * x)) x :=
          hpow.const_mul (C₂ / 2)
        have heq : C₂ / 2 * (2 * x) = C₂ * x := by ring
        rw [heq] at hcm
        exact (hcm.sub hdh).hasDerivWithinAt
      have hnn : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ), 0 ≤ C₂ * x - h' x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
        obtain ⟨_, _, _, hup, _⟩ := hh x hxIcc
        linarith
      have hmono := monotoneOn_of_hasDerivWithinAt_nonneg hDconvex hcont_g hderiv_g hnn
      intro r hr
      have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) ρ := ⟨le_refl 0, h0leρ⟩
      have hle := hmono h0mem hr hr.1
      simp [hh0] at hle
      linarith
    have hmono_h : MonotoneOn h (Set.Icc 0 ρ) := by
      have hDconvex : Convex ℝ (Set.Icc (0 : ℝ) ρ) := convex_Icc 0 ρ
      have hderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ),
          HasDerivWithinAt h (h' x) (interior (Set.Icc (0 : ℝ) ρ)) x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
        obtain ⟨hdh, _, _, _, _⟩ := hh x hxIcc
        exact hdh.hasDerivWithinAt
      have hnn : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ), 0 ≤ h' x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
        obtain ⟨_, _, hlow, _, _⟩ := hh x hxIcc
        have hxnn : 0 ≤ x := by
          have hxoo : x ∈ Set.Ioo (0 : ℝ) ρ := by rwa [interior_Icc] at hx
          exact le_of_lt hxoo.1
        have hcx : 0 ≤ c₁ * x := mul_nonneg (le_of_lt hc₁) hxnn
        linarith
      exact monotoneOn_of_hasDerivWithinAt_nonneg hDconvex hcont hderiv hnn
    have hβ1le : β₁ ≤ β := hβ.1
    have hβle2 : β ≤ β₂ := hβ.2
    have hβpos : 0 < β := lt_of_lt_of_le hβ₁ hβ1le
    have hβ_le_hρ : β ≤ h ρ := by
      have h1 : β ≤ β₂ := hβle2
      have h2 : β₂ + μ ≤ h ρ := hρh
      linarith
    have hIVT : β ∈ h '' (Set.Icc 0 ρ) := by
      have hsub : Set.Icc (h 0) (h ρ) ⊆ h '' (Set.Icc 0 ρ) :=
        intermediate_value_Icc h0leρ hcont
      have hmem : β ∈ Set.Icc (h 0) (h ρ) := by
        rw [hh0]
        exact ⟨le_of_lt hβpos, hβ_le_hρ⟩
      exact hsub hmem
    obtain ⟨r₀, hr₀mem, hr₀eq⟩ := hIVT
    have hr₀nn : 0 ≤ r₀ := hr₀mem.1
    have hr₀le : r₀ ≤ ρ := hr₀mem.2
    have hr₀pos : 0 < r₀ := by
      by_contra hcon
      push Not at hcon
      have hr0 : r₀ = 0 := le_antisymm hcon hr₀nn
      rw [hr0, hh0] at hr₀eq
      linarith
    have hr₀lt : r₀ < ρ := by
      by_contra hcon
      push Not at hcon
      have hr0 : r₀ = ρ := le_antisymm hr₀le hcon
      rw [hr0] at hr₀eq
      linarith
    have hr₀_ge_rmin : rmin ≤ r₀ := by
      have h1 : β ≤ C₂ * r₀ ^ 2 / 2 := by
        have hq := hquad_hi r₀ hr₀mem
        rw [← hr₀eq]
        exact hq
      have h2 : 2 * β / C₂ ≤ r₀ ^ 2 := by
        rw [div_le_iff₀ hC₂]
        linarith
      have h3 : 2 * β₁ / C₂ ≤ r₀ ^ 2 := by
        have hle : 2 * β₁ / C₂ ≤ 2 * β / C₂ :=
          div_le_div_of_nonneg_right (by linarith) (le_of_lt hC₂)
        linarith
      have h4 : Real.sqrt (2 * β₁ / C₂) ≤ r₀ := by
        rw [Real.sqrt_le_iff]
        exact ⟨hr₀nn, h3⟩
      rwa [← hrmin] at h4
    -- Lipschitz bounds via MVT.
    have hLip_h : ∀ a ∈ Set.Icc (0 : ℝ) ρ, ∀ b ∈ Set.Icc (0 : ℝ) ρ,
        |h a - h b| ≤ L * |a - b| := by
      have hDconvex : Convex ℝ (Set.Icc (0 : ℝ) ρ) := convex_Icc 0 ρ
      have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) ρ,
          HasDerivWithinAt h (h' x) (Set.Icc (0 : ℝ) ρ) x := by
        intro x hx
        obtain ⟨hdh, _, _, _, _⟩ := hh x hx
        exact hdh.hasDerivWithinAt
      have hbound : ∀ x ∈ Set.Icc (0 : ℝ) ρ, ‖h' x‖ ≤ L := by
        intro x hx
        obtain ⟨_, _, _, hup, _⟩ := hh x hx
        have hx0 : 0 ≤ x := hx.1
        have hxρ2 : x ≤ ρ₂ := le_trans hx.2 hρu
        have h1 : h' x ≤ C₂ * ρ₂ := by
          have hup2 : h' x ≤ C₂ * x := hup
          have hle : C₂ * x ≤ C₂ * ρ₂ :=
            mul_le_mul_of_nonneg_left hxρ2 (le_of_lt hC₂)
          linarith
        have h0 : 0 ≤ h' x := by
          have hlow : c₁ * x ≤ h' x := (hh x hx).2.2.1
          have hcx : 0 ≤ c₁ * x := mul_nonneg (le_of_lt hc₁) hx0
          linarith
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        rwa [hL]
      intro a ha b hb
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        hderiv hbound hDconvex ha hb
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (h b) (h a),
        abs_sub_comm b a] at hmvt
      exact hmvt
    have hLip_h' : ∀ a ∈ Set.Icc (0 : ℝ) ρ, ∀ b ∈ Set.Icc (0 : ℝ) ρ,
        |h' a - h' b| ≤ C₂ * |a - b| := by
      have hDconvex : Convex ℝ (Set.Icc (0 : ℝ) ρ) := convex_Icc 0 ρ
      have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) ρ,
          HasDerivWithinAt h' (h'' x) (Set.Icc (0 : ℝ) ρ) x := by
        intro x hx
        obtain ⟨_, hdh, _, _, _⟩ := hh x hx
        exact hdh.hasDerivWithinAt
      have hbound : ∀ x ∈ Set.Icc (0 : ℝ) ρ, ‖h'' x‖ ≤ C₂ := by
        intro x hx
        obtain ⟨_, _, _, _, habs⟩ := hh x hx
        rwa [Real.norm_eq_abs]
      intro a ha b hb
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        hderiv hbound hDconvex ha hb
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (h' b) (h' a),
        abs_sub_comm b a] at hmvt
      exact hmvt
    -- Linear lower bound.
    have hlin_lo : ∀ r ∈ Set.Icc (0 : ℝ) ρ, clen * |r - r₀| ≤ |h r - β| := by
      have hDconvex : Convex ℝ (Set.Icc (0 : ℝ) ρ) := convex_Icc 0 ρ
      have hcont_g1 : ContinuousOn (fun r => h r - c₁ / 2 * r ^ 2) (Set.Icc 0 ρ) :=
        hcont.sub ((continuous_const.mul (continuous_pow 2)).continuousOn)
      have hderiv_g1 : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ),
          HasDerivWithinAt (fun r => h r - c₁ / 2 * r ^ 2)
            (h' x - c₁ * x) (interior (Set.Icc (0 : ℝ) ρ)) x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
        obtain ⟨hdh, _, hlow, _, _⟩ := hh x hxIcc
        have hpow : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
          have h2 := hasDerivAt_pow 2 x
          simpa using h2
        have hcm : HasDerivAt (fun r : ℝ => c₁ / 2 * r ^ 2) (c₁ / 2 * (2 * x)) x :=
          hpow.const_mul (c₁ / 2)
        have heq : c₁ / 2 * (2 * x) = c₁ * x := by ring
        rw [heq] at hcm
        exact (hdh.sub hcm).hasDerivWithinAt
      have hnn_g1 : ∀ x ∈ interior (Set.Icc (0 : ℝ) ρ), 0 ≤ h' x - c₁ * x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) ρ := interior_subset hx
        obtain ⟨_, _, hlow, _, _⟩ := hh x hxIcc
        linarith
      have hmono_g1 := monotoneOn_of_hasDerivWithinAt_nonneg hDconvex hcont_g1 hderiv_g1 hnn_g1
      have hr₀I : r₀ ∈ Set.Icc (0 : ℝ) ρ := hr₀mem
      have hclen1 : clen ≤ c₁ * rmin / 2 := min_le_left _ _
      have hclen2 : clen ≤ m / ρ₂ := min_le_right _ _
      intro r hr
      have hrnn : 0 ≤ r := hr.1
      by_cases hge : r₀ ≤ r
      · have hle := hmono_g1 hr₀I hr hge
        have hdiff : c₁ * (r ^ 2 - r₀ ^ 2) / 2 ≤ h r - h r₀ := by linarith
        rw [hr₀eq] at hdiff
        have hpos1 : 0 ≤ r - r₀ := sub_nonneg.mpr hge
        have h1 : c₁ * r₀ / 2 * (r - r₀) ≤ h r - β := by
          nlinarith [hr₀_ge_rmin, hpos1, hr₀nn, hrnn, hc₁, hrmin_pos, hdiff,
            mul_nonneg hpos1 hrnn, mul_nonneg hr₀nn hpos1]
        have h2 : c₁ * rmin / 2 * (r - r₀) ≤ c₁ * r₀ / 2 * (r - r₀) := by
          apply mul_le_mul_of_nonneg_right _ hpos1
          have : c₁ * rmin ≤ c₁ * r₀ :=
            mul_le_mul_of_nonneg_left hr₀_ge_rmin (le_of_lt hc₁)
          linarith
        have hstep : c₁ * rmin / 2 * (r - r₀) ≤ h r - β := le_trans h2 h1
        have hcl : clen * (r - r₀) ≤ c₁ * rmin / 2 * (r - r₀) :=
          mul_le_mul_of_nonneg_right hclen1 hpos1
        have habs1 : |r - r₀| = r - r₀ := abs_of_nonneg hpos1
        have habs2 : |h r - β| = h r - β := by
          apply abs_of_nonneg
          have : h r₀ ≤ h r := hmono_h hr₀I hr hge
          rw [hr₀eq] at this
          linarith
        rw [habs1, habs2]
        exact le_trans hcl hstep
      · push Not at hge
        have hlt : r < r₀ := hge
        by_cases hmid : r₀ / 2 ≤ r
        · have hle := hmono_g1 hr hr₀I (le_of_lt hlt)
          have hdiff : c₁ * (r₀ ^ 2 - r ^ 2) / 2 ≤ h r₀ - h r := by linarith
          rw [hr₀eq] at hdiff
          have hpos1 : 0 ≤ r₀ - r := sub_nonneg.mpr (le_of_lt hlt)
          have h1 : c₁ * r₀ / 2 * (r₀ - r) ≤ β - h r := by
            nlinarith [hr₀_ge_rmin, hpos1, hr₀nn, hrnn, hc₁, hrmin_pos, hdiff,
              mul_nonneg hpos1 hrnn, mul_nonneg hpos1 hr₀nn]
          have h2 : c₁ * rmin / 2 * (r₀ - r) ≤ c₁ * r₀ / 2 * (r₀ - r) := by
            apply mul_le_mul_of_nonneg_right _ hpos1
            have : c₁ * rmin ≤ c₁ * r₀ :=
              mul_le_mul_of_nonneg_left hr₀_ge_rmin (le_of_lt hc₁)
            linarith
          have hstep : c₁ * rmin / 2 * (r₀ - r) ≤ β - h r := le_trans h2 h1
          have hcl : clen * (r₀ - r) ≤ c₁ * rmin / 2 * (r₀ - r) :=
            mul_le_mul_of_nonneg_right hclen1 hpos1
          have habs1 : |r - r₀| = r₀ - r := by
            rw [abs_sub_comm]
            exact abs_of_nonneg hpos1
          have habs2 : |h r - β| = β - h r := by
            have : h r ≤ h r₀ := hmono_h hr hr₀I (le_of_lt hlt)
            rw [hr₀eq] at this
            rw [abs_sub_comm]
            exact abs_of_nonneg (sub_nonneg.mpr this)
          rw [habs1, habs2]
          exact le_trans hcl hstep
        · push Not at hmid
          have hsmall : r < r₀ / 2 := hmid
          have ha_mem : r₀ / 2 ∈ Set.Icc (0 : ℝ) ρ := ⟨by positivity, by linarith⟩
          have h1 : h r ≤ h (r₀ / 2) := hmono_h hr ha_mem (le_of_lt hsmall)
          have hle_mid := hmono_g1 ha_mem hr₀I (by linarith)
          have hdiff_mid : c₁ * (r₀ ^ 2 - (r₀ / 2) ^ 2) / 2 ≤ h r₀ - h (r₀ / 2) := by linarith
          have hm_le : m ≤ h r₀ - h r := by
            have hsq : (r₀ / 2) ^ 2 = r₀ ^ 2 / 4 := by ring
            rw [hsq] at hdiff_mid
            have hr02 : r₀ ^ 2 ≥ rmin ^ 2 :=
              pow_le_pow_left₀ (le_of_lt hrmin_pos) hr₀_ge_rmin 2
            have hmid2 : 3 * c₁ * r₀ ^ 2 / 8 ≤ h r₀ - h (r₀ / 2) := by linarith
            have hm2 : 3 * c₁ * rmin ^ 2 / 8 ≤ 3 * c₁ * r₀ ^ 2 / 8 := by
              apply div_le_div_of_nonneg_right _ (by norm_num)
              have h1 : c₁ * rmin ^ 2 ≤ c₁ * r₀ ^ 2 :=
                mul_le_mul_of_nonneg_left hr02 (le_of_lt hc₁)
              have h2 : 3 * (c₁ * rmin ^ 2) ≤ 3 * (c₁ * r₀ ^ 2) :=
                mul_le_mul_of_nonneg_left h1 (by norm_num)
              linarith
            have hm_eq : m = 3 * c₁ * rmin ^ 2 / 8 := rfl
            linarith [h1, hmid2, hm2, hm_eq]
          rw [hr₀eq] at hm_le
          have hpos1 : 0 ≤ r₀ - r := by linarith
          have hρ2bd : r₀ - r ≤ ρ₂ := by
            have : r₀ ≤ ρ₂ := le_trans hr₀le hρu
            linarith [hrnn]
          have hmρ : m / ρ₂ * (r₀ - r) ≤ m := by
            have hdiv : (r₀ - r) / ρ₂ ≤ 1 := by
              rw [div_le_one hρ₂]
              exact hρ2bd
            have heq : m / ρ₂ * (r₀ - r) = m * ((r₀ - r) / ρ₂) := by ring
            rw [heq]
            calc m * ((r₀ - r) / ρ₂) ≤ m * 1 :=
                  mul_le_mul_of_nonneg_left hdiv (le_of_lt hm_pos)
              _ = m := mul_one _
          have hcl : clen * (r₀ - r) ≤ m / ρ₂ * (r₀ - r) :=
            mul_le_mul_of_nonneg_right hclen2 hpos1
          have habs1 : |r - r₀| = r₀ - r := by
            rw [abs_sub_comm]
            exact abs_of_nonneg hpos1
          have habs2 : |h r - β| = β - h r := by
            have : h r ≤ β := by
              have hrle : h r ≤ h r₀ := hmono_h hr hr₀I (le_of_lt hlt)
              rwa [hr₀eq] at hrle
            rw [abs_sub_comm]
            exact abs_of_nonneg (sub_nonneg.mpr this)
          rw [habs1, habs2]
          exact le_trans hcl (le_trans hmρ hm_le)
    -- Power upper bound r^n ≤ ρ₂^n on [0,ρ].
    have hpow_le : ∀ r ∈ Set.Icc (0 : ℝ) ρ, r ^ n ≤ ρ₂ ^ n := by
      intro r hr
      apply pow_le_pow_left₀ hr.1 _ n
      exact le_trans hr.2 hρu
    have har₀ : a ≤ r₀ := by dsimp [a]; linarith
    have haρ : a ≤ ρ := har₀.trans hr₀le
    have haρ₂ : a ≤ ρ₂ := haρ.trans hρu
    have hasub : Icc a ρ ⊆ Icc 0 ρ := Icc_subset_Icc ha0.le le_rfl
    have hlasub : Icc 0 a ⊆ Icc 0 ρ := Icc_subset_Icc le_rfl haρ
    have hlowgap : ∀ r ∈ Icc 0 a, d ≤ |h r - β| := by
      intro r hr
      have ht := hlin_lo r (hlasub hr)
      have hrle : r ≤ r₀ := hr.2.trans har₀
      rw [abs_of_nonpos (sub_nonpos.mpr hrle)] at ht
      have hd' : d ≤ clen * (r₀ - r) := by
        dsimp [d, a] at *; nlinarith [hr.2]
      linarith
    have hρgap : μ ≤ |h ρ - β| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hpc : ContinuousOn h' (Icc a ρ) := fun r hr =>
      (hh r (hasub hr)).2.1.continuousAt.continuousWithinAt
    have hhp : ∀ r ∈ Icc a ρ, P ≤ h' r := by
      intro r hr
      exact (mul_le_mul_of_nonneg_left hr.1 hc₁.le).trans (hh r (hasub hr)).2.2.1
    let q : ℝ → ℂ := fun r => ((r ^ n / h' r : ℝ) : ℂ)
    obtain ⟨hqd, hqb, hqdb⟩ := quotient_weight_bounds (n := n) ha0.le haρ hρu hP0 hC₂.le
      (fun r hr => (hh r (hasub hr)).2.1) hhp
      (fun r hr => (hh r (hasub hr)).2.2.2.2)
    have hqc : ContinuousOn q (Icc a ρ) := fun r hr =>
      (hqd r hr).continuousAt.continuousWithinAt
    have hql : ∀ r ∈ Icc a ρ, ‖q r - q r₀‖ ≤ T * |r - r₀| := by
      intro r hr
      have ht := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r hr => (hqd r hr).hasDerivAt.hasDerivWithinAt) hqdb
        (convex_Icc a ρ) (show r₀ ∈ Icc a ρ from ⟨har₀, hr₀le⟩) hr
      simpa [Real.norm_eq_abs, q, T] using ht
    have hpb : ∀ r ∈ Icc a ρ, |h' r| ≤ L := by
      intro r hr
      have ht := hh r (hasub hr)
      rw [abs_of_nonneg (hP0.le.trans (hhp r hr))]
      exact ht.2.2.2.1.trans (mul_le_mul_of_nonneg_left (hr.2.trans hρu) hC₂.le)
    have hDupper : ∀ r ∈ Icc 0 ρ, ‖rayDen h β v r‖ ≤ U + 1 := by
      intro r hr
      have hhn : 0 ≤ h r := by
        have ht := hquad r hr
        have : 0 ≤ c₁ * r ^ 2 / 2 := by positivity
        linarith
      have hhu : h r ≤ C₂ * ρ₂ ^ 2 / 2 := (hquad_hi r hr).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hr.1 (hr.2.trans hρu) 2) hC₂.le) (by norm_num))
      have ht := Complex.norm_le_abs_re_add_abs_im (rayDen h β v r)
      rw [rayDen_re, rayDen_im, abs_neg, abs_of_pos hv0] at ht
      have hdist : |h r - β| ≤ U := by
        have habs := abs_sub (h r) β
        rw [abs_of_nonneg hhn, abs_of_pos hβpos] at habs
        dsimp [U]; linarith
      linarith
    have hlogs : ‖Complex.log (rayDen h β v a)‖ ≤ J ∧
        ‖Complex.log (rayDen h β v ρ)‖ ≤ J := by
      have hdm : 0 < min d μ := lt_min hd0 hμ
      constructor
      · apply log_norm_bound hdm _ (hDupper a ⟨ha0.le, haρ⟩)
        exact (min_le_left d μ).trans ((hlowgap a ⟨ha0.le, le_rfl⟩).trans (by
          simpa [rayDen_re] using Complex.abs_re_le_norm (rayDen h β v a)))
      · apply log_norm_bound hdm _ (hDupper ρ ⟨hρpos.le, le_rfl⟩)
        exact (min_le_right d μ).trans (hρgap.trans (by
          simpa [rayDen_re] using Complex.abs_re_le_norm (rayDen h β v ρ)))
    have hrc := (rayDen_cont hcont).inv₀ (fun r _ => rayDen_ne h β r hv0)
    have hri : IntervalIntegrable (fun r => ‖(rayDen h β v r)⁻¹‖) volume 0 ρ :=
      hrc.norm.intervalIntegrable_of_Icc h0leρ
    have hraw : (∫ r in (0 : ℝ)..ρ, ‖(rayDen h β v r)⁻¹‖) ≤ K * Real.log (2 / v) := by
      have hc : Continuous (fun r : ℝ => (clen * |r - r₀| + v)⁻¹) := by
        apply Continuous.inv₀
        · fun_prop
        · intro r; have : 0 < clen * |r - r₀| + v := by positivity
          exact ne_of_gt this
      have ht := intervalIntegral.integral_mono_on h0leρ hri
        ((hc.const_mul 2).intervalIntegrable 0 ρ)
        (fun r hr => by simpa [div_eq_mul_inv] using inverse_bound hv0 hclen_pos (hlin_lo r hr))
      rw [intervalIntegral.integral_const_mul] at ht
      have hk := kernel_log_bound hclen_pos hρ₂ h0leρ hρu hr₀mem hv0 hv1
      calc _ ≤ 2 * (∫ r in (0 : ℝ)..ρ, (clen * |r - r₀| + v)⁻¹) := ht
        _ ≤ 2 * ((2 / clen * (1 + Real.log (clen * ρ₂ + 1) / Real.log 2)) * Real.log (2 / v)) := by linarith
        _ = _ := by dsimp [K]; ring
    have hhighraw : (∫ r in a..ρ, ‖(rayDen h β v r)⁻¹‖) ≤ K * Real.log (2 / v) := by
      apply (intervalIntegral.integral_mono_interval ha0.le haρ le_rfl _ hri).trans hraw
      exact ae_of_all _ (fun _ => norm_nonneg _)
    have hAbs : (∫ r in (0 : ℝ)..ρ, r ^ n * ‖(rayDen h β v r)⁻¹‖) ≤ Cabs * Real.log (2 / v) := by
      have ht := intervalIntegral.integral_mono_on h0leρ
        (((continuous_pow n).continuousOn.mul hrc.norm).intervalIntegrable_of_Icc h0leρ)
        (hri.const_mul (ρ₂ ^ n)) (fun r hr =>
          mul_le_mul_of_nonneg_right (hpow_le r hr) (norm_nonneg _))
      rw [intervalIntegral.integral_const_mul] at ht
      apply ht.trans
      calc _ ≤ ρ₂ ^ n * (K * Real.log (2 / v)) := mul_le_mul_of_nonneg_left hraw (pow_nonneg hρ₂.le n)
        _ = Cabs * Real.log (2 / v) := by dsimp [Cabs]; ring
    have hsplit (k : ℕ) : (∫ r in (0 : ℝ)..ρ, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k) =
        (∫ r in (0 : ℝ)..a, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k) +
        ∫ r in a..ρ, q r * (h' r : ℂ) * (rayDen h β v r)⁻¹ ^ k := by
      have hc := (Complex.continuous_ofReal.comp_continuousOn (continuous_pow n).continuousOn).mul (hrc.pow k)
      have he : (∫ r in (0 : ℝ)..ρ, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k) =
          (∫ r in (0 : ℝ)..a, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k) +
          ∫ r in a..ρ, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k :=
        (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        ((hc.mono hlasub).intervalIntegrable_of_Icc ha0.le)
        ((hc.mono hasub).intervalIntegrable_of_Icc haρ)).symm
      rw [he]
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le haρ] at hr
      have ht : (h' r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP0.trans_le (hhp r hr)).ne'
      dsimp [q]; push_cast; field_simp
    have hlo (k : ℕ) : ‖∫ r in (0 : ℝ)..a, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k‖ ≤
        ρ₂ ^ (n + 1) / d ^ k := by
      have ht := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a)
        (C := ρ₂ ^ n * (1 / d) ^ k)
        (f := fun r => ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k)
      have hbound : ‖∫ r in (0 : ℝ)..a, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ k‖ ≤
          (ρ₂ ^ n * (1 / d) ^ k) * a := by
        rw [sub_zero, abs_of_pos ha0] at ht
        apply ht
        intro r hr
        rw [uIoc_of_le ha0.le] at hr
        have hr' : r ∈ Icc 0 a := ⟨hr.1.le, hr.2⟩
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.1.le n)]
        exact mul_le_mul (hpow_le r (hlasub hr'))
          (pow_le_pow_left₀ (norm_nonneg _) (inverse_gap hv0 hd0 (hlowgap r hr')) k)
          (pow_nonneg (norm_nonneg _) k) (pow_nonneg hρ₂.le n)
      calc _ ≤ (ρ₂ ^ n * (1 / d) ^ k) * a := hbound
        _ ≤ (ρ₂ ^ n * (1 / d) ^ k) * ρ₂ := mul_le_mul_of_nonneg_left haρ₂ (by positivity)
        _ = _ := by rw [pow_succ, div_pow]; ring
    have hfirst : ‖∫ r in (0 : ℝ)..ρ, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹‖ ≤ Cfirst := by
      have ht := first_cancellation_bound haρ ⟨har₀, hr₀le⟩ hv0 hclen_pos hL_pos.le hQ0.le hT0.le
        (fun r hr => (hh r (hasub hr)).1) hpc hqc (hqb r₀ ⟨har₀, hr₀le⟩)
        hql hpb (fun r hr => hlin_lo r (hasub hr)) hlogs.1 hlogs.2
      have hs := hsplit 1
      simp only [pow_one] at hs
      rw [hs]
      have hl := hlo 1
      simp only [pow_one] at hl
      apply (norm_add_le _ _).trans
      dsimp [Cfirst]
      have hm : T * L / clen * (ρ - a) ≤ T * L / clen * ρ₂ :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith only [hl, ht, hm]
    have hsecond : ‖∫ r in (0 : ℝ)..ρ, ((r ^ n : ℝ) : ℂ) * (rayDen h β v r)⁻¹ ^ 2‖ ≤
        Csec * Real.log (2 / v) := by
      have ht := second_parts_bound (β := β) haρ hv0 hQ0.le hT0.le
        (fun r hr => (hh r (hasub hr)).1) hpc hqd hqb hqdb
      have hb := inverse_gap hv0 hμ hρgap
      have ha := inverse_gap hv0 hd0 (hlowgap a ⟨ha0.le, le_rfl⟩)
      have hlog : Real.log 2 ≤ Real.log (2 / v) := by
        rw [Real.log_div (by norm_num) hv0.ne']; have := Real.log_nonpos hv0.le hv1; linarith
      have hconst : ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d) ≤
          (ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d)) / Real.log 2 * Real.log (2 / v) := by
        have hc0 : 0 ≤ (ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d)) / Real.log 2 := by positivity
        have he := div_mul_cancel₀ (ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d)) hlog2.ne'
        calc _ = (ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d)) / Real.log 2 * Real.log 2 := he.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hlog hc0
      rw [hsplit 2]
      apply (norm_add_le _ _).trans
      have hhi : ‖∫ r in a..ρ, q r * (h' r : ℂ) * (rayDen h β v r)⁻¹ ^ 2‖ ≤
          Q * (1 / μ + 1 / d) + T * (K * Real.log (2 / v)) :=
        ht.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hb ha) hQ0.le)
          (mul_le_mul_of_nonneg_left hhighraw hT0.le))
      calc _ ≤ ρ₂ ^ (n + 1) / d ^ 2 + (Q * (1 / μ + 1 / d) + T * (K * Real.log (2 / v))) :=
            add_le_add (hlo 2) hhi
        _ = (ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d)) + T * K * Real.log (2 / v) := by ring
        _ ≤ (ρ₂ ^ (n + 1) / d ^ 2 + Q * (1 / μ + 1 / d)) / Real.log 2 * Real.log (2 / v) +
            T * K * Real.log (2 / v) := add_le_add hconst le_rfl
        _ = Csec * Real.log (2 / v) := by dsimp [Csec]; ring
    have hlogpos : 0 ≤ Real.log (2 / v) := Real.log_nonneg (by rw [le_div_iff₀ hv0]; linarith)
    refine ⟨?_, ?_, hfirst.trans hCfirst, ?_⟩
    · exact hsecond.trans (mul_le_mul_of_nonneg_right hCsec hlogpos)
    · exact hAbs.trans (mul_le_mul_of_nonneg_right hCabs hlogpos)
    · exact imaginary_lower h0leρ hr₀mem hrmin_pos hr₀_ge_rmin hv0 hv1 hμ hL_pos
        hcont hr₀eq (by linarith only [hρh, hβle2]) (fun r hr => hLip_h r hr r₀ hr₀mem)
  · push Not at hC
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro h h' h'' ρ hρl hρu hh0 hh hρh β hβ v hv0 hv1
    exfalso
    have hρpos : 0 < ρ := lt_of_lt_of_le hρ₁ hρl
    have hmem : ρ ∈ Set.Icc (0 : ℝ) ρ := ⟨le_of_lt hρpos, le_refl ρ⟩
    obtain ⟨_, _, hlow, hup, _⟩ := hh ρ hmem
    have : c₁ ≤ C₂ := le_of_mul_le_mul_right (le_trans hlow hup) hρpos
    linarith


end AndersonAC.S3
