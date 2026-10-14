import AndersonAC.AgentS6Row.Bounds

noncomputable section
open Matrix ComplexConjugate MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.L64

variable {ι B Ω : Type*} [Fintype B] [DecidableEq B] [MeasurableSpace Ω]

/-- One-row mean after the cancellation of the unit second moment.
All hypotheses refer to the same normalized heat and coefficient law. -/
theorem row_integral_bound (H : NHeat ι B) (i : ι) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℂ) (hcm : Measurable c)
    (C R B₁ B₂ : ℝ) (hcb : ∀ᵐ ω ∂μ, ‖c ω‖ ≤ C)
    (hF : ∀ z : ℂ, ‖z‖ ≤ C → fro (H.D z) ≤ 1 / 4)
    (hR : ∀ z : ℂ, ‖z‖ ≤ C → |rowRem H i z| ≤ R)
    (hmean : ‖∫ ω, c ω ∂μ‖ ≤ B₁)
    (hsecond : |(∫ ω, ‖c ω‖ ^ 2 ∂μ) - 1| ≤ B₂) :
    Integrable (fun ω => H.lev' (c ω) i - H.lev i) μ ∧
      |∫ ω, (H.lev' (c ω) i - H.lev i) ∂μ| ≤
        R + H.m * ‖H.v i‖ ^ 2 * (∫ ω, ‖c ω‖ ^ 2 ∂μ) +
        ‖rowS H i‖ ^ 2 * (|H.vn - 1| + H.vn * B₂) +
        2 * B₁ * (‖H.v i‖ * ‖rowS H i‖ +
          ‖rowS H i‖ * Real.sqrt (H.lev i) * Real.sqrt (nsq H.b)) := by
  let a0 := ‖rowS H i‖ ^ 2
  let a2 := ‖H.v i‖ ^ 2 * H.m - H.vn * ‖rowS H i‖ ^ 2
  let κ := 2 * (H.v i * rowS H i - rowS H i * (H.u i ⬝ᵥ H.b))
  have hf : Measurable (fun z : ℂ => H.lev' z i - H.lev i) :=
    (H.measurable_lev' i).sub measurable_const
  obtain ⟨hI, hbound⟩ := integral_affine_bound hcm hcb hf a0 a2 κ
    (ρ := R) (fun z hz => by
      rw [row_change_eq_affine_add_rem H z (hF z hz) i]
      have he : rowAff H i z = a0 + a2 * ‖z‖ ^ 2 + (z * κ).re := by
        simp only [a0, a2, κ, rowAff, Complex.mul_re, Complex.mul_im]
        norm_num
        ring
      rw [he, add_sub_cancel_left]
      exact hR z hz)
  refine ⟨hI, ?_⟩
  set E2 := ∫ ω, ‖c ω‖ ^ 2 ∂μ
  set Ec := ∫ ω, c ω ∂μ
  have hE2 : 0 ≤ E2 := integral_nonneg (fun ω => sq_nonneg _)
  have hB1 : 0 ≤ B₁ := (norm_nonneg Ec).trans hmean
  have hVN := H.vn_nonneg
  have h1 : |1 - H.vn * E2| ≤ |H.vn - 1| + H.vn * B₂ := by
    have he : 1 - H.vn * E2 = -(H.vn - 1) - H.vn * (E2 - 1) := by ring
    rw [he]
    calc
      _ ≤ |-(H.vn - 1)| + |H.vn * (E2 - 1)| := abs_sub _ _
      _ = |H.vn - 1| + H.vn * |E2 - 1| := by rw [abs_neg, abs_mul, abs_of_nonneg hVN]
      _ ≤ _ := by gcongr
  have h2 : ‖κ‖ ≤ 2 * (‖H.v i‖ * ‖rowS H i‖ +
        ‖rowS H i‖ * Real.sqrt (H.lev i) * Real.sqrt (nsq H.b)) := by
    simp only [κ, norm_mul, Complex.norm_ofNat]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by norm_num)
    rw [norm_mul, norm_mul]
    have hd : ‖H.u i ⬝ᵥ H.b‖ ≤ Real.sqrt (H.lev i) * Real.sqrt (nsq H.b) :=
      norm_dotProduct_le _ _
    have hh := mul_le_mul_of_nonneg_left hd (norm_nonneg (rowS H i))
    nlinarith
  have hmain :
      |a0 + a2 * E2 + (Ec * κ).re| ≤
        H.m * ‖H.v i‖ ^ 2 * E2 +
        ‖rowS H i‖ ^ 2 * (|H.vn - 1| + H.vn * B₂) +
        2 * B₁ * (‖H.v i‖ * ‖rowS H i‖ +
          ‖rowS H i‖ * Real.sqrt (H.lev i) * Real.sqrt (nsq H.b)) := by
    have he : a0 + a2 * E2 = H.m * ‖H.v i‖ ^ 2 * E2 + ‖rowS H i‖ ^ 2 * (1 - H.vn * E2) := by
      dsimp [a0, a2]
      ring
    rw [he]
    calc
      _ ≤ |H.m * ‖H.v i‖ ^ 2 * E2 + ‖rowS H i‖ ^ 2 * (1 - H.vn * E2)| + |(Ec * κ).re| :=
        abs_add_le _ _
      _ ≤ |H.m * ‖H.v i‖ ^ 2 * E2| + |‖rowS H i‖ ^ 2 * (1 - H.vn * E2)| + ‖Ec * κ‖ := by
        exact add_le_add (abs_add_le _ _) (Complex.abs_re_le_norm _)
      _ = H.m * ‖H.v i‖ ^ 2 * E2 + ‖rowS H i‖ ^ 2 * |1 - H.vn * E2| + ‖Ec‖ * ‖κ‖ := by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg H.m_nn (sq_nonneg _)) hE2), abs_mul, abs_of_nonneg (sq_nonneg _), norm_mul]
      _ ≤ _ := by
        have hx := mul_le_mul hmean h2 (norm_nonneg κ) hB1
        have hy := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖rowS H i‖)
        nlinarith
  calc
    |∫ ω, (H.lev' (c ω) i - H.lev i) ∂μ|
      ≤ |(∫ ω, (H.lev' (c ω) i - H.lev i) ∂μ) - (a0 + a2 * E2 + (Ec * κ).re)| +
        |a0 + a2 * E2 + (Ec * κ).re| := by
          calc
            _ = |((∫ ω, (H.lev' (c ω) i - H.lev i) ∂μ) -
                (a0 + a2 * E2 + (Ec * κ).re)) + (a0 + a2 * E2 + (Ec * κ).re)| := by
              congr 1; ring
            _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

end AndersonAC.AgentS6Row

#print axioms AndersonAC.AgentS6Row.row_integral_bound
