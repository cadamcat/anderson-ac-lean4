import AndersonAC.S3.ShellGeometry

/-! A global convex extension obtained by integrating the clamped coordinate curvature. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace AndersonAC.S3

def shellClamp (u : ℝ) : ℝ := max (-(1 / 4)) (min u (1 / 4))
def extendedCoordinateSecond (ζ u : ℝ) : ℝ := slicedCoordinateSecond ζ (shellClamp u)
def extendedCoordinateDeriv (sign ζ u : ℝ) : ℝ :=
  slicedCoordinateDeriv sign ζ 0 + ∫ v : ℝ in (0 : ℝ)..u, extendedCoordinateSecond ζ v
def extendedCoordinate (sign ζ u : ℝ) : ℝ :=
  slicedCoordinate sign ζ 0 + ∫ v : ℝ in (0 : ℝ)..u, extendedCoordinateDeriv sign ζ v

theorem shell_clamp_bounds (u : ℝ) : |shellClamp u| ≤ 1 / 4 := by
  unfold shellClamp
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem shell_clamp_eq {u : ℝ} (hu : |u| ≤ 1 / 4) : shellClamp u = u := by
  have h := abs_le.mp hu
  unfold shellClamp
  rw [min_eq_left h.2, max_eq_right h.1]

theorem extended_coordinate_second_continuous (ζ : ℝ) : Continuous (extendedCoordinateSecond ζ) := by
  have hc : Continuous shellClamp := by unfold shellClamp; fun_prop
  have hden : Continuous (fun u => Real.sqrt (1 - shellClamp u ^ 2) ^ 3) := by fun_prop
  apply continuous_const.div hden
  intro u
  have h := abs_le.mp (shell_clamp_bounds u)
  have hq : 0 < 1 - shellClamp u ^ 2 := by nlinarith
  exact pow_ne_zero 3 (Real.sqrt_pos.mpr hq).ne'

theorem extended_coordinate_second_bounds (ζ u : ℝ) (hζ : |ζ| ≤ 1 / 2) :
    1 ≤ extendedCoordinateSecond ζ u ∧ extendedCoordinateSecond ζ u ≤ 8 :=
  sliced_coordinate_second_bounds ζ (shellClamp u) hζ (shell_clamp_bounds u)

theorem extended_coordinate_deriv_hasDerivAt (sign ζ u : ℝ) :
    HasDerivAt (extendedCoordinateDeriv sign ζ) (extendedCoordinateSecond ζ u) u := by
  have hc := extended_coordinate_second_continuous ζ
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_add (slicedCoordinateDeriv sign ζ 0)

theorem extended_coordinate_deriv_continuous (sign ζ : ℝ) : Continuous (extendedCoordinateDeriv sign ζ) :=
  (show Differentiable ℝ (extendedCoordinateDeriv sign ζ) from
    fun u => (extended_coordinate_deriv_hasDerivAt sign ζ u).differentiableAt).continuous

theorem extended_coordinate_hasDerivAt (sign ζ u : ℝ) :
    HasDerivAt (extendedCoordinate sign ζ) (extendedCoordinateDeriv sign ζ u) u := by
  have hc := extended_coordinate_deriv_continuous sign ζ
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_add (slicedCoordinate sign ζ 0)

theorem shell_interval_bounds {u v : ℝ} (hu : |u| ≤ 1 / 4) (hv : v ∈ uIcc 0 u) :
    |v| ≤ 1 / 4 := by
  have h := abs_le.mp hu
  change min (0 : ℝ) u ≤ v ∧ v ≤ max (0 : ℝ) u at hv
  rw [abs_le]
  exact ⟨(le_min (by norm_num) h.1).trans hv.1,
    hv.2.trans (max_le (by norm_num) h.2)⟩

theorem extended_coordinate_deriv_eq (sign ζ u : ℝ) (hu : |u| ≤ 1 / 4) :
    extendedCoordinateDeriv sign ζ u = slicedCoordinateDeriv sign ζ u := by
  have hi : (∫ v : ℝ in (0 : ℝ)..u, extendedCoordinateSecond ζ v) =
      slicedCoordinateDeriv sign ζ u - slicedCoordinateDeriv sign ζ 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro v hv
      have hv' := shell_interval_bounds hu hv
      have hv₁ : |v| < 1 := by linarith
      simpa only [extendedCoordinateSecond, shell_clamp_eq hv'] using
        sliced_coordinate_deriv_hasDerivAt sign ζ v hv₁
    · exact (extended_coordinate_second_continuous ζ).intervalIntegrable 0 u
  unfold extendedCoordinateDeriv
  rw [hi]
  ring

theorem extended_coordinate_eq (sign ζ u : ℝ) (hu : |u| ≤ 1 / 4) :
    extendedCoordinate sign ζ u = slicedCoordinate sign ζ u := by
  have hi : (∫ v : ℝ in (0 : ℝ)..u, extendedCoordinateDeriv sign ζ v) =
      slicedCoordinate sign ζ u - slicedCoordinate sign ζ 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro v hv
      have hv' := shell_interval_bounds hu hv
      rw [extended_coordinate_deriv_eq sign ζ v hv']
      exact sliced_coordinate_hasDerivAt sign ζ v (by linarith)
    · exact (extended_coordinate_deriv_continuous sign ζ).intervalIntegrable 0 u
  unfold extendedCoordinate
  rw [hi]
  ring

theorem extended_coordinate_continuous (sign ζ : ℝ) : Continuous (extendedCoordinate sign ζ) :=
  (show Differentiable ℝ (extendedCoordinate sign ζ) from
    fun u => (extended_coordinate_hasDerivAt sign ζ u).differentiableAt).continuous

theorem extended_coordinate_derivative_growth (sign ζ : ℝ) (hζ : |ζ| ≤ 1 / 2)
    {u v : ℝ} (huv : u ≤ v) :
    v - u ≤ extendedCoordinateDeriv sign ζ v - extendedCoordinateDeriv sign ζ u := by
  have hf : Differentiable ℝ (extendedCoordinateDeriv sign ζ) :=
    fun u => (extended_coordinate_deriv_hasDerivAt sign ζ u).differentiableAt
  have hge : ∀ u, (1 : ℝ) ≤ deriv (extendedCoordinateDeriv sign ζ) u := by
    intro u
    rw [(extended_coordinate_deriv_hasDerivAt sign ζ u).deriv]
    exact (extended_coordinate_second_bounds ζ u hζ).1
  simpa only [one_mul] using mul_sub_le_image_sub_of_le_deriv hf hge huv

theorem extended_coordinate_strongConvex (sign ζ : ℝ) (hζ : |ζ| ≤ 1 / 2) :
    StrongConvexOn (Set.univ : Set ℝ) 1 (extendedCoordinate sign ζ) := by
  have hf : ConvexOn ℝ (Set.univ : Set ℝ)
      (fun u => extendedCoordinate sign ζ u - u ^ 2 / 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun u => extendedCoordinateDeriv sign ζ u - u)
      (f'' := fun u => extendedCoordinateSecond ζ u - 1) convex_univ
    · exact ((extended_coordinate_continuous sign ζ).sub ((continuous_pow 2).div_const 2)).continuousOn
    · intro u _
      have h := (extended_coordinate_hasDerivAt sign ζ u).sub (((hasDerivAt_id u).pow 2).div_const 2)
      have h' : HasDerivAt (fun u => extendedCoordinate sign ζ u - u ^ 2 / 2)
          (extendedCoordinateDeriv sign ζ u - u) u := by
        convert h using 1
        · rfl
        · simp
      exact h'.hasDerivWithinAt
    · intro u _
      exact ((extended_coordinate_deriv_hasDerivAt sign ζ u).sub (hasDerivAt_id u)).hasDerivWithinAt
    · intro u _
      have h := (extended_coordinate_second_bounds ζ u hζ).1
      linarith
  rw [strongConvexOn_iff_convex]
  simpa only [Real.norm_eq_abs, sq_abs, one_div, div_eq_mul_inv, one_mul, mul_comm] using hf

def extendedDispersion {d : ℕ} (sign : ℝ) (ζ : Frequency d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ j, extendedCoordinate sign (ζ j) (x j)

theorem extended_dispersion_eq {d : ℕ} (sign : ℝ) (ζ : Frequency d)
    (x : EuclideanSpace ℝ (Fin d)) (hx : ∀ j, |x j| ≤ 1 / 4) :
    extendedDispersion sign ζ x = slicedDispersion sign ζ (fun j => x j) := by
  unfold extendedDispersion
  simp_rw [extended_coordinate_eq sign _ _ (hx _)]
  unfold slicedCoordinate slicedDispersion
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]

theorem extended_dispersion_strongConvex {d : ℕ} (sign : ℝ) (ζ : Frequency d)
    (hζ : ∀ j, |ζ j| ≤ 1 / 2) :
    StrongConvexOn (Set.univ : Set (EuclideanSpace ℝ (Fin d))) 1 (extendedDispersion sign ζ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun j _ =>
    (extended_coordinate_strongConvex sign (ζ j) (hζ j)).2
      (x := x j) (y := y j) (by trivial) (by trivial) ha hb hab)
  simpa only [extendedDispersion, smul_eq_mul, Real.norm_eq_abs, sq_abs, one_div,
    EuclideanSpace.real_norm_sq_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply] using hs

end AndersonAC.S3
