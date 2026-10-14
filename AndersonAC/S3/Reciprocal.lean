import Mathlib

/-! Feynman reciprocal-product identity (§3, lines 553–558).
Proved without placeholders; imports only Mathlib (never `Statements`). -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace AndersonAC.S3

/-- Feynman identity: `(A*B)⁻¹ = ∫₀¹ ((1-u)A + uB)⁻¹² du` when `A,B` share
a common negative imaginary part (so the segment never hits zero). -/
theorem reciprocal_product_identity_proof (A B : ℂ) (hA : A.im < 0) (hB : B.im = A.im) :
    (A * B)⁻¹ = ∫ u : ℝ in (0 : ℝ)..1, (((1 - u : ℝ) : ℂ) * A + (u : ℂ) * B)⁻¹ ^ 2 := by
  -- The affine segment and its basic properties.
  set g : ℝ → ℂ := fun u => (((1 - u : ℝ) : ℂ) * A + (u : ℂ) * B) with hgdef
  have hAne : A ≠ 0 := by
    intro h
    rw [h] at hA
    simp at hA
  have hBne : B ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hB
    linarith
  have hgIm : ∀ u : ℝ, (g u).im = A.im := by
    intro u
    simp only [hgdef, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    rw [hB]
    ring
  have hgNe : ∀ u : ℝ, g u ≠ 0 := by
    intro u h
    have him := hgIm u
    rw [h, Complex.zero_im] at him
    linarith
  have hgCont : Continuous g := by
    unfold g
    fun_prop
  -- Derivative of the segment: identically `B - A`, via `g = A + (·)*(B-A)`.
  have hU : ∀ u : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) u :=
    fun u => (hasDerivAt_id ((u : ℝ) : ℂ)).comp_ofReal
  have hMul : ∀ u : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ) * (B - A)) (1 * (B - A)) u :=
    fun u => (hU u).mul_const (B - A)
  have hgDeriv : ∀ u : ℝ, HasDerivAt g (B - A) u := by
    intro u
    have h := (hasDerivAt_const u A).add (hMul u)
    have hfun : (fun _ => A) + (fun y : ℝ => (y : ℂ) * (B - A)) = g := by
      funext y
      simp only [hgdef, Pi.add_apply]
      push_cast
      ring
    rw [hfun] at h
    simpa using h
  -- Antiderivative `F = g⁻¹` and its derivative.
  set F : ℝ → ℂ := fun u => (g u)⁻¹ with hFdef
  have hFDeriv : ∀ u : ℝ, HasDerivAt F (-(B - A) / g u ^ 2) u := by
    intro u
    have h := (hgDeriv u).inv (hgNe u)
    have hfun : g⁻¹ = F := rfl
    rw [hfun] at h
    exact h
  -- Reformulate the derivative as a constant multiple of the integrand.
  have hFDerivEq : ∀ u : ℝ, (-(B - A) / g u ^ 2) = -(B - A) * ((g u)⁻¹ ^ 2) := by
    intro u
    rw [div_eq_mul_inv, inv_pow]
  -- Continuity / integrability.
  have hFDerivCont : Continuous (fun u => (-(B - A) / g u ^ 2)) := by
    apply Continuous.mul continuous_const
    apply Continuous.inv₀
    · exact hgCont.pow 2
    · intro u
      exact pow_ne_zero 2 (hgNe u)
  have hIntCont : Continuous (fun u => ((g u)⁻¹ ^ 2)) := by
    apply Continuous.pow
    exact hgCont.inv₀ hgNe
  have hFDerivInt : IntervalIntegrable (fun u => (-(B - A) / g u ^ 2)) volume 0 1 :=
    hFDerivCont.intervalIntegrable 0 1
  have hIntInt : IntervalIntegrable (fun u => ((g u)⁻¹ ^ 2)) volume 0 1 :=
    hIntCont.intervalIntegrable 0 1
  -- FTC applied to `F`.
  have hFTC : ∫ u : ℝ in (0 : ℝ)..1, (-(B - A) / g u ^ 2) = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFDeriv x) hFDerivInt
  -- Factor the constant out of the integral.
  have hFactor : (∫ u : ℝ in (0 : ℝ)..1, (-(B - A) / g u ^ 2))
      = -(B - A) * (∫ u : ℝ in (0 : ℝ)..1, ((g u)⁻¹ ^ 2)) := by
    simp_rw [hFDerivEq]
    rw [intervalIntegral.integral_const_mul]
  -- Endpoint values.
  have hg0 : g 0 = A := by
    show ((((1 - (0 : ℝ) : ℝ)) : ℂ) * A + (((0 : ℝ)) : ℂ) * B) = A
    simp
  have hg1 : g 1 = B := by
    show ((((1 - (1 : ℝ) : ℝ)) : ℂ) * A + (((1 : ℝ)) : ℂ) * B) = B
    simp
  have hF0 : F 0 = A⁻¹ := by
    show (g 0)⁻¹ = A⁻¹
    rw [hg0]
  have hF1 : F 1 = B⁻¹ := by
    show (g 1)⁻¹ = B⁻¹
    rw [hg1]
  -- Case split on `A = B`.
  rcases eq_or_ne A B with hAB | hAB
  · subst hAB
    have hSeg : ∀ u : ℝ, g u = A := by
      intro u
      show ((((1 - u : ℝ)) : ℂ) * A + (u : ℂ) * A) = A
      have hcast : ((((1 - u : ℝ)) : ℂ) + (u : ℂ)) = 1 := by
        rw [← Complex.ofReal_add]
        simp
      calc ((((1 - u : ℝ)) : ℂ) * A + (u : ℂ) * A)
          = ((((1 - u : ℝ)) : ℂ) + (u : ℂ)) * A := by ring
        _ = A := by rw [hcast, one_mul]
    have hconst : ∀ u : ℝ, ((g u)⁻¹ ^ 2) = (A⁻¹ ^ 2) := by
      intro u
      rw [hSeg u]
    have hFin : (A * A)⁻¹ = A⁻¹ ^ 2 := by rw [pow_two, mul_inv]
    show (A * A)⁻¹ = ∫ u : ℝ in (0 : ℝ)..1, (g u)⁻¹ ^ 2
    rw [hFin]
    simp_rw [hconst]
    rw [intervalIntegral.integral_const]
    simp
  · have hBA : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
    have hnegBA : -(B - A) ≠ 0 := neg_ne_zero.mpr hBA
    rw [hFactor, hF0, hF1] at hFTC
    -- `B⁻¹ - A⁻¹ = (-(B-A)) * (A*B)⁻¹`.
    have hAlg : B⁻¹ - A⁻¹ = -(B - A) * (A * B)⁻¹ := by
      field_simp
      ring
    rw [hAlg] at hFTC
    have hI : (∫ u : ℝ in (0 : ℝ)..1, ((g u)⁻¹ ^ 2)) = (A * B)⁻¹ :=
      mul_left_cancel₀ hnegBA hFTC
    exact hI.symm

end AndersonAC.S3
