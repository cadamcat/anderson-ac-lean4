import Mathlib
import AndersonAC.S78.Definitions

open MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section

namespace AndersonAC.SolS78

theorem final_tail_update_proof (η : ℝ) (ξ r : ℂ) :
    (Real.sqrt (1 / 2 : ℝ) : ℂ) * (ξ / (Real.sqrt (1 / 2 : ℝ) : ℂ) +
      (2 * η : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) * r) = ξ + (η : ℂ) * r := by
  let s : ℝ := Real.sqrt (1 / 2 : ℝ)
  have hs_sq : s ^ 2 = 1 / 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by norm_num)
  have hs0 : (s : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hs_pos)
  have hcsq : (s : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    calc
      (s : ℂ) ^ 2 = ((s ^ 2 : ℝ) : ℂ) := by norm_cast
      _ = ((1 / 2 : ℝ) : ℂ) := by rw [hs_sq]
      _ = (1 / 2 : ℂ) := by norm_num
  calc
    (s : ℂ) * (ξ / (s : ℂ) + (2 * η : ℂ) * (s : ℂ) * r) =
        ξ + (2 * η : ℂ) * (s : ℂ) ^ 2 * r := by
      field_simp [hs0]
    _ = ξ + (η : ℂ) * r := by
      rw [hcsq]
      ring

theorem final_tail_moments_proof {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hmean : ∫ ω, ξ ω ∂μ = 0) (hvar : ∫ ω, (ξ ω) ^ 2 ∂μ = η)
    (hbound : ∀ᵐ ω ∂μ, |ξ ω| ≤ Real.sqrt (3 * η)) :
    (∫ ω, ξ ω / Real.sqrt (1 / 2 : ℝ) ∂μ) = 0 ∧
    (∫ ω, (ξ ω / Real.sqrt (1 / 2 : ℝ)) ^ 2 ∂μ) = 2 * η ∧
    (∀ᵐ ω ∂μ, |ξ ω / Real.sqrt (1 / 2 : ℝ)| ≤ Real.sqrt (3 * (2 * η))) := by
  let s : ℝ := Real.sqrt (1 / 2 : ℝ)
  have hs_sq : s ^ 2 = 1 / 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by norm_num)
  have hs_inv_sq : s⁻¹ ^ 2 = 2 := by
    calc
      s⁻¹ ^ 2 = (s ^ 2)⁻¹ := by rw [inv_pow]
      _ = (1 / 2 : ℝ)⁻¹ := by rw [hs_sq]
      _ = 2 := by norm_num
  have hroot : Real.sqrt (3 * η) = Real.sqrt (3 * (2 * η)) * s := by
    calc
      Real.sqrt (3 * η) = Real.sqrt (3 * (2 * η) * (1 / 2 : ℝ)) := by
        congr 1
        ring
      _ = Real.sqrt (3 * (2 * η)) * Real.sqrt (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul (by positivity)]
      _ = Real.sqrt (3 * (2 * η)) * s := by rfl
  have hfirst :
      (∫ ω, ξ ω / s ∂μ) = s⁻¹ * (∫ ω, ξ ω ∂μ) := by
    calc
      (∫ ω, ξ ω / s ∂μ) = ∫ ω, s⁻¹ * ξ ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [div_eq_mul_inv, mul_comm]
      _ = s⁻¹ * (∫ ω, ξ ω ∂μ) := by rw [integral_const_mul]
  have hsecond :
      (∫ ω, (ξ ω / s) ^ 2 ∂μ) = (s⁻¹) ^ 2 * (∫ ω, (ξ ω) ^ 2 ∂μ) := by
    calc
      (∫ ω, (ξ ω / s) ^ 2 ∂μ) =
          ∫ ω, (s⁻¹) ^ 2 * (ξ ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [div_eq_mul_inv, mul_pow, mul_comm]
      _ = (s⁻¹) ^ 2 * (∫ ω, (ξ ω) ^ 2 ∂μ) := by rw [integral_const_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfirst, hmean]
    simp
  · rw [hsecond, hs_inv_sq, hvar]
  · filter_upwards [hbound] with ω hω
    rw [abs_div, abs_of_pos hs_pos]
    rw [hroot] at hω
    exact (div_le_iff₀ hs_pos).2 hω

end AndersonAC.SolS78
