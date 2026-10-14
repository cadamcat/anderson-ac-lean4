import AndersonAC.S9.Core
import Mathlib.Probability.Distributions.Cauchy

/-! Poisson-kernel and rank-one averaging ingredients for Lemma 9.1. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace AndersonAC.SolS9

def cauchyKernel (a v s : ℝ) : ℝ := v / ((s - a) ^ 2 + v ^ 2)

theorem integral_cauchyKernel (a v : ℝ) (hv : 0 < v) :
    ∫ s : ℝ, cauchyKernel a v s = Real.pi := by
  let γ : ℝ≥0 := ⟨v, hv.le⟩
  have hγ : γ ≠ 0 := by
    intro h
    have : v = 0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
    exact hv.ne' this
  have heq : cauchyKernel a v = fun s => Real.pi * ProbabilityTheory.cauchyPDFReal a γ s := by
    funext s
    change v / ((s - a) ^ 2 + v ^ 2) =
      Real.pi * (Real.pi⁻¹ * v * ((s - a) ^ 2 + v ^ 2)⁻¹)
    simp [div_eq_mul_inv, ← mul_assoc, Real.pi_ne_zero]
  rw [heq, integral_const_mul, ProbabilityTheory.integral_cauchyPDFReal_eq_one a hγ, mul_one]

/-- The finite-height averaging bound in Lemma 9.1, before taking a
spectral boundary limit. Only the essential density bound enters. -/
theorem weighted_cauchyKernel_bound (ρ : ℝ → ℝ) (C a v : ℝ)
    (hρ : Measurable ρ) (hρnonneg : ∀ᵐ s ∂volume, 0 ≤ ρ s)
    (hρbound : ∀ᵐ s ∂volume, ρ s ≤ C) (hC : 0 ≤ C) (hv : 0 < v) :
    ∫ s : ℝ, ρ s * cauchyKernel a v s ≤ Real.pi * C := by
  have hk : Integrable (cauchyKernel a v) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_cauchyKernel a v hv]
    exact Real.pi_ne_zero
  have hkm : Measurable (cauchyKernel a v) := by
    unfold cauchyKernel
    fun_prop
  have hkzero : ∀ s : ℝ, 0 ≤ cauchyKernel a v s := by
    intro s
    exact div_nonneg hv.le (by positivity)
  have hdom : ∀ᵐ s ∂volume, ‖ρ s * cauchyKernel a v s‖ ≤ C * cauchyKernel a v s := by
    filter_upwards [hρnonneg, hρbound] with s hsnonneg hsbound
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsnonneg (hkzero s))]
    exact mul_le_mul_of_nonneg_right hsbound (hkzero s)
  have hint : Integrable (fun s => ρ s * cauchyKernel a v s) :=
    (hk.const_mul C).mono' (hρ.mul hkm).aestronglyMeasurable hdom
  calc
    (∫ s, ρ s * cauchyKernel a v s) ≤ ∫ s, C * cauchyKernel a v s := by
      apply integral_mono_ae hint (hk.const_mul C)
      filter_upwards [hρbound] with s hs
      exact mul_le_mul_of_nonneg_right hs (hkzero s)
    _ = C * Real.pi := by rw [integral_const_mul, integral_cauchyKernel a v hv]
    _ = Real.pi * C := mul_comm _ _

end AndersonAC.SolS9
