import Mathlib
import Mathlib.Analysis.Complex.JensenFormula

open MeasureTheory Filter Topology Complex Real Set Metric MeromorphicOn

namespace AndersonAC.LunaHinf

/-- The affine Cayley map taking the unit disk to the half-plane above height `η`. -/
noncomputable def diskUpper (x₀ η a : ℝ) (w : ℂ) : ℂ :=
  (x₀ : ℂ) + (η : ℂ) * I + (a : ℂ) * I * ((1 + w) / (1 - w))

theorem diskUpper_zero (x₀ η a : ℝ) :
    diskUpper x₀ η a 0 = (x₀ : ℂ) + (η + a) * I := by
  simp [diskUpper]
  ring

theorem circleMap_zero_scale (r θ : ℝ) :
    circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by
  simp [circleMap]

theorem diskUpper_im_gt (x₀ η a : ℝ) {w : ℂ} (ha : 0 < a) (hw : ‖w‖ < 1) :
    η < (diskUpper x₀ η a w).im := by
  have hkernel : 0 < poissonKernel 0 w 1 := by
    rw [poissonKernel]
    have hnum : 0 < 1 - ‖w‖ ^ 2 := by
      have hn := norm_nonneg w
      nlinarith
    have hden : 0 < ‖(1 : ℂ) - w‖ ^ 2 := by
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro h
      have hw' : w = 1 := (sub_eq_zero.mp h).symm
      rw [hw'] at hw
      simp at hw
    simpa using div_pos hnum hden
  have hreal : ((1 + w) / (1 - w)).re = poissonKernel 0 w 1 := by
    have hh := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := w)) 1
    simpa [herglotzRieszKernel] using hh.symm
  have him : (diskUpper x₀ η a w).im = η + a * ((1 + w) / (1 - w)).re := by
    simp [diskUpper, Complex.add_im, Complex.mul_im]
  rw [him, hreal]
  exact lt_add_of_pos_right η (mul_pos ha hkernel)

theorem diskUpper_im_eq (x₀ η a : ℝ) {w : ℂ} (hw : ‖w‖ = 1) :
    (diskUpper x₀ η a w).im = η := by
  have hreal : ((1 + w) / (1 - w)).re = poissonKernel 0 w 1 := by
    have hh := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := w)) 1
    simpa [herglotzRieszKernel] using hh.symm
  have him : (diskUpper x₀ η a w).im = η + a * ((1 + w) / (1 - w)).re := by
    simp [diskUpper, Complex.add_im, Complex.mul_im]
  have hpk : poissonKernel 0 w 1 = 0 := by simp [poissonKernel, hw]
  rw [him, hreal, hpk, mul_zero, add_zero]

theorem diskUpper_boundary_eq (x₀ η a : ℝ) {w : ℂ} (hw : ‖w‖ = 1) :
    diskUpper x₀ η a w = (diskUpper x₀ 0 a w).re + (η : ℂ) * I := by
  have hshift : diskUpper x₀ η a w = diskUpper x₀ 0 a w + (η : ℂ) * I := by
    simp [diskUpper]
    ring
  rw [hshift]
  apply Complex.ext <;> simp [diskUpper_im_eq x₀ 0 a hw]

noncomputable def diskBoundaryX (x₀ a : ℝ) (θ : ℝ) : ℝ :=
  (diskUpper x₀ 0 a (circleMap 0 1 θ)).re

theorem diskUpper_circleBoundary_eq (x₀ η a θ : ℝ) :
    diskUpper x₀ η a (circleMap 0 1 θ) = (diskBoundaryX x₀ a θ : ℂ) + (η : ℂ) * I := by
  rw [diskUpper_boundary_eq x₀ η a (by simp)]
  simp [diskBoundaryX]

theorem diskUpper_continuousAt {x₀ η a : ℝ} {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    ContinuousAt (diskUpper x₀ η a) w := by
  change ContinuousAt
    (fun z : ℂ => (x₀ : ℂ) + (η : ℂ) * I + (a : ℂ) * I * ((1 + z) / (1 - z))) w
  fun_prop (disch := exact hw)

theorem tendsto_diskUpper_radial {x₀ η a : ℝ} {θ : ℝ} (hθ : circleMap 0 1 θ ≠ 1)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => diskUpper x₀ η a (r n * circleMap 0 1 θ)) atTop
      (𝓝 ((diskBoundaryX x₀ a θ : ℂ) + (η : ℂ) * I)) := by
  let w := circleMap 0 1 θ
  have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).comp hr
  have harg : Tendsto (fun n => (r n : ℂ) * circleMap 0 1 θ) atTop
      (𝓝 (circleMap 0 1 θ)) := by
    have hconst : Tendsto (fun _ : ℕ => circleMap 0 1 θ) atTop
        (𝓝 (circleMap 0 1 θ)) := tendsto_const_nhds
    simpa using hrC.mul hconst
  have hcont : ContinuousAt (diskUpper x₀ η a) (circleMap 0 1 θ) := by
    simpa [w] using (diskUpper_continuousAt (x₀ := x₀) (η := η) (a := a) hden)
  rw [← diskUpper_circleBoundary_eq x₀ η a θ]
  exact hcont.tendsto.comp harg

theorem diskUpper_mapsTo {x₀ η a r : ℝ} (ha : 0 < a) (hr1 : r < 1)
    (hη : 0 ≤ η) :
    Set.MapsTo (diskUpper x₀ η a) (closedBall 0 r) {z : ℂ | 0 < z.im} := by
  intro w hw
  have hn : ‖w‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hw
  exact lt_of_le_of_lt hη (diskUpper_im_gt x₀ η a ha (lt_of_le_of_lt hn hr1))

theorem diskUpper_analyticOnNhd {x₀ η a r : ℝ} (hr1 : r < 1) :
    AnalyticOnNhd ℂ (diskUpper x₀ η a) (closedBall 0 r) := by
  intro w hw
  have hn : ‖w‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hw
  have hlt : ‖w‖ < 1 := lt_of_le_of_lt hn hr1
  have hden : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := (sub_eq_zero.mp h).symm
    rw [hw1] at hlt
    simp at hlt
  change AnalyticAt ℂ
    (fun z : ℂ => (x₀ : ℂ) + (η : ℂ) * I + (a : ℂ) * I * ((1 + z) / (1 - z))) w
  fun_prop (disch := exact hden)

theorem differentiableOn_comp_diskUpper {f : ℂ → ℂ} {x₀ η a r : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (ha : 0 < a)
    (hr1 : r < 1) (hη : 0 ≤ η) :
    AnalyticOnNhd ℂ (f ∘ diskUpper x₀ η a) (closedBall 0 r) := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hfa : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} := hf.analyticOnNhd hopen
  exact hfa.comp (diskUpper_analyticOnNhd hr1) (diskUpper_mapsTo ha hr1 hη)

/-- Jensen's formula implies that the circle average of `log ‖f‖` dominates its value
at the center, whenever `f` is analytic on the closed disk and nonzero at the center. -/
theorem circleAverage_log_norm_ge_center {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c |R|)) (hfc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ circleAverage (fun z : ℂ => Real.log ‖f z‖) c R := by
  let D : ℂ → ℤ := divisor f (closedBall c |R|)
  have hDc : D c = 0 := by
    dsimp [D]
    rw [hf.divisor_apply (by simp : c ∈ closedBall c |R|)]
    rw [(hf c (by simp)).analyticOrderAt_eq_zero.mpr hfc]
    simp
  have hterm (u : ℂ) : 0 ≤ (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    by_cases hu0 : D u = 0
    · simp [hu0]
    have huD : u ∈ (divisor f (closedBall c |R|)).support := by
      simp only [Function.mem_support]
      simpa [D] using hu0
    have huB : u ∈ closedBall c |R| :=
      (divisor f (closedBall c |R|)).supportWithinDomain huD
    have huc : u ≠ c := by
      intro heq
      apply hu0
      rw [heq, hDc]
    have hnorm : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
    have hle : ‖c - u‖ ≤ R := by
      simpa [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using huB
    have hlog : 0 ≤ Real.log (R * ‖c - u‖⁻¹) := by
      rw [← div_eq_mul_inv]
      apply log_nonneg
      rw [one_le_div₀ hnorm]
      exact hle
    exact mul_nonneg (by
      dsimp [D]
      exact_mod_cast hf.divisor_nonneg u) hlog
  have hsum : 0 ≤ ∑ᶠ u : ℂ, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) :=
    finsum_nonneg hterm
  rw [hf.circleAverage_log_norm hR.ne' hfc]
  calc
    Real.log ‖f c‖ ≤ Real.log ‖f c‖ + ∑ᶠ u : ℂ,
        (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := le_add_of_nonneg_right hsum
    _ = ∑ᶠ u : ℂ, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖ := by ring
    _ = ∑ᶠ u : ℂ, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹)
        + Real.log ‖f c‖ := by rfl

theorem circleAverage_eq_inv_mul_toReal_lintegral {g : ℂ → ℝ} {r : ℝ}
    (hCI : CircleIntegrable g 0 r)
    (hNonneg : ∀ z ∈ sphere 0 |r|, 0 ≤ g z) :
    circleAverage g 0 r = (2 * π)⁻¹ * ENNReal.toReal
      (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (g (circleMap 0 r θ)) ∂volume) := by
  have hCI' := (circleIntegrable_def g 0 r).mp hCI
  have hInt : IntegrableOn (fun θ : ℝ => g (circleMap 0 r θ)) (Ioc 0 (2 * π)) volume := hCI'.1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))]
      (fun θ : ℝ => g (circleMap 0 r θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hNonneg _ (circleMap_mem_sphere' 0 r θ)
  have hEq : (∫ θ in Ioc 0 (2 * π), g (circleMap 0 r θ) ∂volume) =
      ENNReal.toReal (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (g (circleMap 0 r θ)) ∂volume) :=
    integral_eq_lintegral_of_nonneg_ae hnn hInt.aestronglyMeasurable
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, hEq]
  simp only [smul_eq_mul]

/-- Jensen on every disk strictly inside the Cayley disk for a function analytic on an upper
half-plane. This is the interior-circle estimate used before taking the boundary limit. -/
theorem diskUpper_circleAverage_log_norm_ge_center {f : ℂ → ℂ} {x₀ η a r : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (ha : 0 < a)
    (hη : 0 ≤ η) (hr : 0 < r) (hr1 : r < 1)
    (hfc : f ((x₀ : ℂ) + (η + a) * I) ≠ 0) :
    Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖ ≤
      circleAverage (fun w : ℂ => Real.log ‖f (diskUpper x₀ η a w)‖) 0 r := by
  have hcomp : AnalyticOnNhd ℂ (f ∘ diskUpper x₀ η a) (closedBall 0 |r|) := by
    simpa [abs_of_pos hr] using differentiableOn_comp_diskUpper hf ha hr1 hη
  have hcenter : (f ∘ diskUpper x₀ η a) 0 ≠ 0 := by
    simpa [Function.comp_def, diskUpper_zero] using hfc
  have hj := circleAverage_log_norm_ge_center (f := f ∘ diskUpper x₀ η a) hr hcomp hcenter
  simpa [Function.comp_def, diskUpper_zero] using hj

/-- The half-plane Poisson--Jensen bound in the angular coordinate of the Cayley map. The
boundary circle parameterizes the horizontal line `Im z = η` with its harmonic measure. -/
theorem halfPlane_poissonJensen_angle {f : ℂ → ℂ} {x₀ η a : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hbdd : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ 1)
    (ha : 0 < a) (hη : 0 < η)
    (hcenter : f ((x₀ : ℂ) + (η + a) * I) ≠ 0)
    (hline : ∀ x : ℝ, f ((x : ℂ) + (η : ℂ) * I) ≠ 0) :
    ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal
      (-Real.log ‖f (diskUpper x₀ η a (circleMap 0 1 θ))‖) ∂volume ≤
      ENNReal.ofReal ((2 * π) * (-Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖)) := by
  let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 2)
  let g : ℂ → ℝ := fun z => -Real.log ‖f (diskUpper x₀ η a z)‖
  let L : ℕ → ENNReal := fun n =>
    ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (g (circleMap 0 (r n) θ)) ∂volume
  let radial : ℕ → ℝ → ENNReal := fun n θ => ENNReal.ofReal (g (circleMap 0 (r n) θ))
  let boundary : ℝ → ENNReal := fun θ => ENNReal.ofReal (g (circleMap 0 1 θ))
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp [r]
    positivity
  have hrlt (n : ℕ) : r n < 1 := by
    dsimp [r]
    rw [div_lt_one (by positivity)]
    norm_num
  have hrT : Tendsto r atTop (𝓝 1) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have heq : r = fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
      funext n
      dsimp [r]
      have hd : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      <;> ring
    rw [heq]
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hconst.sub hinv
  have hcenterPos : 0 < ‖f ((x₀ : ℂ) + (η + a) * I)‖ := norm_pos_iff.mpr hcenter
  have hcenterBound : ‖f ((x₀ : ℂ) + (η + a) * I)‖ ≤ 1 := by
    apply hbdd
    have him : 0 < ((x₀ : ℂ) + (η + a) * I).im := by simp; linarith
    exact him
  have hC : 0 ≤ -Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖ :=
    neg_nonneg.mpr (Real.log_nonpos hcenterPos.le hcenterBound)
  have hLbound (n : ℕ) : L n ≤ ENNReal.ofReal
      ((2 * π) * (-Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖)) := by
    have hcomp : AnalyticOnNhd ℂ (f ∘ diskUpper x₀ η a) (closedBall 0 |r n|) := by
      simpa [abs_of_pos (hrpos n)] using
        differentiableOn_comp_diskUpper hf ha (hrlt n) hη.le
    have hCIlog : CircleIntegrable
        (fun z : ℂ => Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) := by
      exact (hcomp.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    have hCI : CircleIntegrable g 0 (r n) := by
      have hCI' : CircleIntegrable
          (fun z : ℂ => -Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) := by
        convert hCIlog.neg using 1
      simpa [g] using hCI'
    have hnonneg : ∀ z ∈ sphere 0 |r n|, 0 ≤ g z := by
      intro z hz
      have hnorm : ‖z‖ = r n := by
        simpa [mem_sphere, dist_eq_norm, abs_of_pos (hrpos n)] using hz
      have hzlt : ‖z‖ < 1 := hnorm ▸ hrlt n
      have hIm : 0 < (diskUpper x₀ η a z).im :=
        lt_trans hη (diskUpper_im_gt x₀ η a ha hzlt)
      have hval := hbdd (diskUpper x₀ η a z) hIm
      by_cases hz0 : f (diskUpper x₀ η a z) = 0
      · simp [g, hz0]
      · exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hval)
    have hj := diskUpper_circleAverage_log_norm_ge_center hf ha hη.le
      (hrpos n) (hrlt n) hcenter
    have hneg : circleAverage g 0 (r n) =
        -circleAverage (fun z : ℂ => Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) := by
      calc
        circleAverage g 0 (r n) = circleAverage
            (fun z : ℂ => (-1 : ℝ) • Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) := by
              congr 1
              funext z
              simp [g]
        _ = (-1 : ℝ) • circleAverage
            (fun z : ℂ => Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) :=
              circleAverage_fun_smul
        _ = -circleAverage
            (fun z : ℂ => Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) := by simp
    have hAvg : circleAverage g 0 (r n) ≤
        -Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖ := by
      rw [hneg]
      exact neg_le_neg hj
    have hformula := circleAverage_eq_inv_mul_toReal_lintegral hCI hnonneg
    have hAvg' : (2 * π)⁻¹ * ENNReal.toReal (L n) ≤
        -Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖ := by
      rw [hformula] at hAvg
      simpa [L, g] using hAvg
    have hCI' := (circleIntegrable_def g 0 (r n)).mp hCI
    have hLfinite : L n < ⊤ := by
      simpa [L, g] using hCI'.1.setLIntegral_lt_top
    have hdiv : ENNReal.toReal (L n) / (2 * π) ≤
        -Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖ := by
      simpa [div_eq_mul_inv, mul_comm] using hAvg'
    have hreal := (div_le_iff₀ two_pi_pos).mp hdiv
    have hle : ENNReal.ofReal (ENNReal.toReal (L n)) ≤ ENNReal.ofReal
        ((2 * π) * (-Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖)) :=
      ENNReal.ofReal_le_ofReal (by simpa [mul_comm] using hreal)
    rw [ENNReal.ofReal_toReal (ne_of_lt hLfinite)] at hle
    exact hle
  have hRadialMeas (n : ℕ) : AEMeasurable (radial n) μ := by
    have hcomp : AnalyticOnNhd ℂ (f ∘ diskUpper x₀ η a) (closedBall 0 |r n|) := by
      simpa [abs_of_pos (hrpos n)] using
        differentiableOn_comp_diskUpper hf ha (hrlt n) hη.le
    have hCIlog : CircleIntegrable
        (fun z : ℂ => Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) := by
      exact (hcomp.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    have hCI : CircleIntegrable g 0 (r n) := by
      have hCI' : CircleIntegrable
          (fun z : ℂ => -Real.log ‖f (diskUpper x₀ η a z)‖) 0 (r n) := by
        convert hCIlog.neg using 1
      simpa [g] using hCI'
    have hCI' := (circleIntegrable_def g 0 (r n)).mp hCI
    simpa [radial, μ] using hCI'.1.aemeasurable.ennreal_ofReal
  have hbad : volume {θ : ℝ | circleMap 0 1 θ = (1 : ℂ)} = 0 := by
    have hs : {θ : ℝ | circleMap 0 1 θ = (1 : ℂ)}.Countable := by
      simpa [Set.preimage] using (countable_singleton (1 : ℂ)).preimage_circleMap 0
        (by norm_num : (1 : ℝ) ≠ 0)
    exact hs.measure_zero _
  have hbadμ : ∀ᵐ θ ∂μ, circleMap 0 1 θ ≠ (1 : ℂ) := by
    have hae : ∀ᵐ θ ∂volume, circleMap 0 1 θ ≠ (1 : ℂ) :=
      measure_eq_zero_iff_ae_notMem.mp hbad
    exact hae.filter_mono ae_restrict_le
  have hpoint : boundary ≤ᵐ[μ]
      (fun θ => liminf (fun n => radial n θ) atTop) := by
    filter_upwards [hbadμ] with θ hθ
    have hrad := tendsto_diskUpper_radial (x₀ := x₀) (η := η) (a := a) hθ hrT
    have hrad' : Tendsto (fun n => diskUpper x₀ η a (circleMap 0 (r n) θ)) atTop
        (𝓝 (diskUpper x₀ η a (circleMap 0 1 θ))) := by
      convert hrad using 1
      · funext n
        rw [circleMap_zero_scale]
      · rw [← diskUpper_circleBoundary_eq x₀ η a θ]
    have hlineval : f (diskUpper x₀ η a (circleMap 0 1 θ)) ≠ 0 := by
      rw [diskUpper_circleBoundary_eq]
      exact hline (diskBoundaryX x₀ a θ)
    have him : 0 < (diskUpper x₀ η a (circleMap 0 1 θ)).im := by
      rw [diskUpper_circleBoundary_eq]
      simpa using hη
    have hfunCont : ContinuousAt
        (fun z : ℂ => ENNReal.ofReal (-Real.log ‖f z‖))
        (diskUpper x₀ η a (circleMap 0 1 θ)) := by
      let b := diskUpper x₀ η a (circleMap 0 1 θ)
      have hnorm : 0 < ‖f b‖ := norm_pos_iff.mpr hlineval
      have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
      have hfAn : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} := hf.analyticOnNhd hopen
      have hnormCont : ContinuousAt (fun z : ℂ => ‖z‖) (f b) :=
        continuous_norm.continuousAt
      have hlogCont : ContinuousAt
          (fun z : ℝ => ENNReal.ofReal (-Real.log z)) (‖f b‖) :=
        ENNReal.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_log hnorm.ne').neg
      have hphiCont : ContinuousAt
          (fun z : ℂ => ENNReal.ofReal (-Real.log ‖z‖)) (f b) :=
        hlogCont.comp hnormCont
      simpa [b, Function.comp_def] using hphiCont.comp ((hfAn b him).continuousAt)
    have hval := hfunCont.tendsto.comp hrad'
    have hliminf := hval.liminf_eq.symm.le
    simpa [boundary, radial, g, Function.comp_def] using hliminf
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop) hRadialMeas
  have hfreq : ∃ᶠ n in atTop, L n ≤ ENNReal.ofReal
      ((2 * π) * (-Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖)) :=
    Filter.Eventually.frequently (Filter.Eventually.of_forall hLbound)
  calc
    ∫⁻ θ in Ioc 0 (2 * π), boundary θ ∂volume
        ≤ ∫⁻ θ, liminf (fun n => radial n θ) atTop ∂μ := by
          simpa [μ] using lintegral_mono_ae hpoint
    _ ≤ liminf (fun n => ∫⁻ θ, radial n θ ∂μ) atTop := hfatou
    _ ≤ ENNReal.ofReal
        ((2 * π) * (-Real.log ‖f ((x₀ : ℂ) + (η + a) * I)‖)) := by
          apply liminf_le_of_frequently_le'
          exact hfreq.mono fun n hn => by simpa [L, radial, μ] using hn

end AndersonAC.LunaHinf
