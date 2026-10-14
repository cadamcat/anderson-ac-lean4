import AndersonAC.AgentS6.CondHeat

/-! A masked, scalar form of the checked conditional heat-coefficient estimate. -/

noncomputable section
open MeasureTheory Filter
open AndersonAC.S6

namespace AndersonAC.AgentS6Budget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem masked_heatCoefficient_mean_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (k : ℕ) (A : Set Ω) (hA : MeasurableSet[F k] A)
    (t C : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hC : 1 ≤ C)
    (hsmall : AndersonAC.L64.Small t C) (ρ γ : Ω → ℂ) (ξ η : Ω → ℝ)
    (hρ : StronglyMeasurable[F k] ρ) (hγ : StronglyMeasurable[F k] γ)
    (hξm : Measurable ξ) (hξI : Integrable ξ μ)
    (hξ2I : Integrable (fun ω => ξ ω ^ 2) μ)
    (hρbound : ∀ ω ∈ A, ‖ρ ω‖ ≤ C)
    (hγbound : ∀ ω ∈ A, ‖γ ω‖ ≤ C)
    (hξbound : ∀ ω ∈ A, |ξ ω| ≤ C * Real.sqrt t)
    (hmean : ∀ᵐ ω ∂μ, ω ∈ A → μ[ξ | F k] ω = 0)
    (hsecond : ∀ᵐ ω ∂μ, ω ∈ A → μ[(fun ω => ξ ω ^ 2) | F k] ω = t - η ω)
    (hη : ∀ ω ∈ A, |η ω| ≤ C * t ^ 2)
    (hlag : ∀ ω ∈ A, ‖γ ω - ρ ω‖ ≤ C * t ^ betaW) :
    ∀ᵐ ω ∂μ, ω ∈ A →
      ‖μ[A.indicator (fun ω => heatCoefficient t (ρ ω) (γ ω) (ξ ω)) | F k] ω‖ ≤
        20 * C ^ 5 * Real.sqrt t * t ^ betaW := by
  have hcoef := AndersonAC.AgentS6.condExp_heatCoeff_mean μ F k hA hsmall hρ hγ hξm
    hρbound hγbound hξbound hξI hξ2I hmean hsecond hη
  have hcoef' : ∀ᵐ ω ∂μ, ω ∈ A →
      ‖μ[A.indicator (fun ω => heatCoefficient t (ρ ω) (γ ω) (ξ ω)) | F k] ω -
          (Real.sqrt t : ℂ) * (γ ω - ρ ω)‖ ≤ (C ^ 2 + C ^ 3 + 16 * C ^ 5) * t := by
    simpa [heatCoefficient, AndersonAC.L64.hc] using hcoef
  have hpow : t ≤ Real.sqrt t * t ^ betaW := by
    have h1 : Real.sqrt t ≤ t ^ betaW := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num [betaW, delta])
    calc
      t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht.le).symm
      _ ≤ Real.sqrt t * t ^ betaW := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg t)
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hC2 : 1 ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - 1)]
  have hC3 : 1 ≤ C ^ 3 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ C * C ^ 2 := mul_le_mul hC hC2 (by norm_num) hC0
      _ = C ^ 3 := by ring
  have hC4 : 1 ≤ C ^ 4 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ C ^ 2 * C ^ 2 := mul_le_mul hC2 hC2 (by norm_num) (by positivity)
      _ = C ^ 4 := by ring
  have hC5 : C ≤ C ^ 5 := by
    calc C = C * 1 := by ring
      _ ≤ C * C ^ 4 := mul_le_mul_of_nonneg_left hC4 hC0
      _ = C ^ 5 := by ring
  have hC2to5 : C ^ 2 ≤ C ^ 5 := by
    calc C ^ 2 = C ^ 2 * 1 := by ring
      _ ≤ C ^ 2 * C ^ 3 := mul_le_mul_of_nonneg_left hC3 (sq_nonneg C)
      _ = C ^ 5 := by ring
  have hC3to5 : C ^ 3 ≤ C ^ 5 := by
    calc C ^ 3 = C ^ 3 * 1 := by ring
      _ ≤ C ^ 3 * C ^ 2 := mul_le_mul_of_nonneg_left hC2 (by positivity)
      _ = C ^ 5 := by ring
  have hM : C ^ 2 + C ^ 3 + 16 * C ^ 5 ≤ 18 * C ^ 5 := by
    nlinarith [hC2to5, hC3to5]
  have hscale : 0 ≤ Real.sqrt t * t ^ betaW :=
    mul_nonneg (Real.sqrt_nonneg t) (Real.rpow_nonneg ht.le _)
  filter_upwards [hcoef'] with ω hω
  intro hωA
  let b : ℂ := (Real.sqrt t : ℂ) * (γ ω - ρ ω)
  have hb : ‖b‖ ≤ Real.sqrt t * (C * t ^ betaW) := by
    dsimp [b]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
    exact mul_le_mul_of_nonneg_left (hlag ω hωA) (Real.sqrt_nonneg t)
  calc
    ‖μ[A.indicator (fun ω => heatCoefficient t (ρ ω) (γ ω) (ξ ω)) | F k] ω‖ =
        ‖(μ[A.indicator (fun ω => heatCoefficient t (ρ ω) (γ ω) (ξ ω)) | F k] ω - b) + b‖ := by
          congr 1
          dsimp [b]
          ring
    _ ≤ ‖μ[A.indicator (fun ω => heatCoefficient t (ρ ω) (γ ω) (ξ ω)) | F k] ω - b‖ + ‖b‖ :=
          norm_add_le _ _
    _ ≤ (C ^ 2 + C ^ 3 + 16 * C ^ 5) * t + Real.sqrt t * (C * t ^ betaW) :=
          add_le_add (hω hωA) hb
    _ ≤ 18 * C ^ 5 * t + C * (Real.sqrt t * t ^ betaW) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hM ht.le
          · exact le_of_eq (by ring)
    _ ≤ 18 * C ^ 5 * (Real.sqrt t * t ^ betaW) + C ^ 5 * (Real.sqrt t * t ^ betaW) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hpow (by positivity)
          · exact mul_le_mul_of_nonneg_right hC5 hscale
    _ ≤ 20 * C ^ 5 * Real.sqrt t * t ^ betaW := by
          nlinarith [mul_nonneg (pow_nonneg hC0 5) hscale]

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.masked_heatCoefficient_mean_bound
