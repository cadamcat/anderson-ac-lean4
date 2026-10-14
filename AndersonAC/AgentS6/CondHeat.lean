import AndersonAC.L64.Residual
import AndersonAC.S6.Statements

/-! Conditional mean of the heat coefficient (06-clearing.tex:442–447, 905–911): on a
predictable event where the residual has conditional mean `0`, conditional second moment
`t - η`, and `|ξ| ≤ C√t`, with predictable `ρ = r_x`, `γ = g_xx` bounded by `C`,
`‖E[c_x | F] - √t (γ - ρ)‖ ≤ (C² + C³ + 16C⁵) t`. Proof by the second-order expansion of
`c_x` (`norm_hc_sub_le`), linearity and pull-out; no regular conditional law. -/

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem condExp_heatCoeff_mean (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (k : ℕ) {E : Set Ω} (hE : MeasurableSet[F k] E) {t C : ℝ}
    (hsmall : AndersonAC.L64.Small t C) {ρ γ : Ω → ℂ} (hρm : StronglyMeasurable[F k] ρ)
    (hγm : StronglyMeasurable[F k] γ) {ξ η : Ω → ℝ} (hξm : Measurable ξ)
    (hρ : ∀ ω ∈ E, ‖ρ ω‖ ≤ C) (hγ : ∀ ω ∈ E, ‖γ ω‖ ≤ C) (hξb : ∀ ω ∈ E, |ξ ω| ≤ C * Real.sqrt t)
    (hξI : Integrable ξ μ) (hξ2I : Integrable (fun ω => ξ ω ^ 2) μ)
    (hmean : ∀ᵐ ω ∂μ, ω ∈ E → μ[ξ | F k] ω = 0)
    (hsec : ∀ᵐ ω ∂μ, ω ∈ E → μ[(fun ω => ξ ω ^ 2) | F k] ω = t - η ω)
    (hη : ∀ ω ∈ E, |η ω| ≤ C * t ^ 2) :
    ∀ᵐ ω ∂μ, ω ∈ E →
      ‖μ[E.indicator (fun ω => AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω)) | F k] ω -
        (Real.sqrt t : ℂ) * (γ ω - ρ ω)‖ ≤ (C ^ 2 + C ^ 3 + 16 * C ^ 5) * t := by
  have hm : F k ≤ mΩ := F.le k
  have hEm : MeasurableSet E := hm _ hE
  have hC := hsmall.C_nonneg
  have hs := hsmall.sqrt_pos
  have hs' : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  set st : ℂ := ((Real.sqrt t : ℝ) : ℂ)
  -- masked predictable factors
  set ρE : Ω → ℂ := E.indicator ρ
  set γE : Ω → ℂ := E.indicator γ
  have hρEm : StronglyMeasurable[F k] ρE := hρm.indicator hE
  have hγEm : StronglyMeasurable[F k] γE := hγm.indicator hE
  have hρEb : ∀ ω, ‖ρE ω‖ ≤ C := fun ω => by
    by_cases h : ω ∈ E
    · simp only [ρE, Set.indicator_of_mem h]; exact hρ ω h
    · simp only [ρE, Set.indicator_of_notMem h, norm_zero]; exact hC
  have hγEb : ∀ ω, ‖γE ω‖ ≤ C := fun ω => by
    by_cases h : ω ∈ E
    · simp only [γE, Set.indicator_of_mem h]; exact hγ ω h
    · simp only [γE, Set.indicator_of_notMem h, norm_zero]; exact hC
  set ξE : Ω → ℝ := E.indicator ξ
  set ξ2E : Ω → ℝ := E.indicator (fun ω => ξ ω ^ 2)
  have hξEI : Integrable ξE μ := hξI.indicator hEm
  have hξ2EI : Integrable ξ2E μ := hξ2I.indicator hEm
  -- the remainder
  set T : Ω → ℂ := fun ω => -((ξ ω : ℂ) + (t : ℂ) * ρ ω) / st +
    ((ξ ω : ℂ) + (t : ℂ) * ρ ω) ^ 2 * γ ω / st
  set RE : Ω → ℂ := E.indicator (fun ω => AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω) - T ω)
  have hRb : ∀ ω, ‖RE ω‖ ≤ 16 * C ^ 5 * t := fun ω => by
    by_cases h : ω ∈ E
    · simp only [RE, Set.indicator_of_mem h]
      exact AndersonAC.L64.norm_hc_sub_le hsmall (hρ ω h) (hγ ω h) (hξb ω h)
    · simp only [RE, Set.indicator_of_notMem h, norm_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC 5)) hsmall.pos.le
  -- measurability of the remainder
  have hρmeas : Measurable ρ := (hρm.mono hm).measurable
  have hγmeas : Measurable γ := (hγm.mono hm).measurable
  have hhcm : Measurable (fun ω => AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω)) := by
    unfold AndersonAC.L64.hc
    have ha : Measurable (fun ω => (ξ ω : ℂ) + (t : ℂ) * ρ ω) :=
      (Complex.measurable_ofReal.comp hξm).add (measurable_const.mul hρmeas)
    exact ha.neg.div (measurable_const.mul (measurable_const.add (ha.mul hγmeas)))
  have hTm : Measurable T := by
    have ha : Measurable (fun ω => (ξ ω : ℂ) + (t : ℂ) * ρ ω) :=
      (Complex.measurable_ofReal.comp hξm).add (measurable_const.mul hρmeas)
    exact (ha.neg.div_const _).add (((ha.pow_const 2).mul hγmeas).div_const _)
  have hREm : Measurable RE := (hhcm.sub hTm).indicator hEm
  have hREI : Integrable RE μ :=
    (integrable_const (16 * C ^ 5 * t : ℝ)).mono' hREm.aestronglyMeasurable
      (Filter.Eventually.of_forall hRb)
  -- pointwise decomposition of the masked coefficient
  set A1 : Ω → ℂ := ξE • (fun _ => -(1 / st))
  set A2 : Ω → ℂ := fun ω => -(st * ρE ω) + ((t : ℂ) ^ 2 / st) * (ρE ω) ^ 2 * γE ω
  set A3 : Ω → ℂ := ξ2E • (fun ω => γE ω / st)
  set A4 : Ω → ℂ := ξE • (fun ω => 2 * (t : ℂ) * ρE ω * γE ω / st)
  have hdecomp : E.indicator (fun ω => AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω)) =
      A1 + A2 + A3 + A4 + RE := by
    funext ω
    have hst : st * st = (t : ℂ) := by
      simp only [st]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt hsmall.pos.le]
    by_cases h : ω ∈ E
    · simp only [Pi.add_apply, A1, A2, A3, A4, RE, ρE, γE, ξE, ξ2E, T, Pi.smul_apply',
        Set.indicator, h, if_true, Complex.real_smul]
      rw [← hst]
      field_simp
      push_cast
      ring
    · simp [A1, A2, A3, A4, RE, ρE, γE, ξE, ξ2E, Pi.smul_apply', Set.indicator, h]
  -- integrability and conditional expectations of the pieces
  have hstn : ‖st‖ = Real.sqrt t := by simp [st, Real.sqrt_nonneg]
  have hγEmeas : Measurable γE := (hγEm.mono hm).measurable
  have hρEmeas : Measurable ρE := (hρEm.mono hm).measurable
  have hb3 : ∀ ω, ‖γE ω / st‖ ≤ C / Real.sqrt t := fun ω => by
    rw [norm_div, hstn]; exact div_le_div_of_nonneg_right (hγEb ω) hs.le
  have hb4 : ∀ ω, ‖2 * (t : ℂ) * ρE ω * γE ω / st‖ ≤ 2 * t * C * C / Real.sqrt t := fun ω => by
    rw [norm_div, hstn, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hsmall.pos.le]
    apply div_le_div_of_nonneg_right _ hs.le
    have := mul_le_mul (hρEb ω) (hγEb ω) (norm_nonneg _) hC
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, mul_assoc (2 * t), mul_assoc (2 * t)]
    exact mul_le_mul_of_nonneg_left this (by linarith [hsmall.pos])
  have hm3 : AEStronglyMeasurable[F k] (fun ω => γE ω / st) μ := by
    have : (fun ω => γE ω / st) = fun ω => γE ω * st⁻¹ := by funext ω; rw [div_eq_mul_inv]
    rw [this]; exact (hγEm.mul stronglyMeasurable_const).aestronglyMeasurable
  have hm4 : AEStronglyMeasurable[F k] (fun ω => 2 * (t : ℂ) * ρE ω * γE ω / st) μ := by
    have : (fun ω => 2 * (t : ℂ) * ρE ω * γE ω / st) =
        fun ω => 2 * (t : ℂ) * ρE ω * γE ω * st⁻¹ := by funext ω; rw [div_eq_mul_inv]
    rw [this]
    exact (((stronglyMeasurable_const.mul hρEm).mul hγEm).mul
      stronglyMeasurable_const).aestronglyMeasurable
  have hA1I : Integrable A1 μ := hξEI.smul_bdd ‖-(1 / st)‖ aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => le_rfl)
  have hA3I : Integrable A3 μ := hξ2EI.smul_bdd (C / Real.sqrt t)
    (hm3.mono hm) (Filter.Eventually.of_forall hb3)
  have hA4I : Integrable A4 μ := hξEI.smul_bdd (2 * t * C * C / Real.sqrt t)
    (hm4.mono hm) (Filter.Eventually.of_forall hb4)
  have hA2m : StronglyMeasurable[F k] A2 :=
    (stronglyMeasurable_const.mul hρEm).neg.add
      ((stronglyMeasurable_const.mul (hρEm.pow 2)).mul hγEm)
  have hA2b : ∀ ω, ‖A2 ω‖ ≤ Real.sqrt t * C + t ^ 2 / Real.sqrt t * C ^ 2 * C := fun ω => by
    simp only [A2]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg, norm_mul, hstn]; exact mul_le_mul_of_nonneg_left (hρEb ω) hs.le
    · rw [norm_mul, norm_mul, norm_div, hstn, norm_pow, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hsmall.pos.le]
      have h1 : ‖ρE ω‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hρEb ω) 2
      have h2 := hγEb ω
      have h0 : 0 ≤ t ^ 2 / Real.sqrt t := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h0) h2 (norm_nonneg _) (by positivity)
  have hA2I : Integrable A2 μ :=
    (integrable_const (Real.sqrt t * C + t ^ 2 / Real.sqrt t * C ^ 2 * C)).mono'
      (hA2m.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hA2b)
  have c1 := condExp_smul_of_aestronglyMeasurable_right (m := F k) hξEI hA1I
    (aestronglyMeasurable_const (b := -(1 / st)))
  have c2 : μ[A2 | F k] = A2 := condExp_of_stronglyMeasurable hm hA2m hA2I
  have c3 := condExp_smul_of_aestronglyMeasurable_right (m := F k) hξ2EI hA3I hm3
  have c4 := condExp_smul_of_aestronglyMeasurable_right (m := F k) hξEI hA4I hm4
  have cadd1 := condExp_add (m := F k) hA1I hA2I
  have cadd2 := condExp_add (m := F k) (hA1I.add hA2I) hA3I
  have cadd3 := condExp_add (m := F k) ((hA1I.add hA2I).add hA3I) hA4I
  have cadd4 := condExp_add (m := F k) (((hA1I.add hA2I).add hA3I).add hA4I) hREI
  have hξEc := condExp_indicator (m := F k) hξI hE
  have hξ2Ec := condExp_indicator (m := F k) hξ2I hE
  -- remainder bound
  have hRc : ∀ᵐ ω ∂μ, ‖μ[RE | F k] ω‖ ≤ 16 * C ^ 5 * t := by
    have h1 := norm_condExp_le (m := F k) (μ := μ) RE
    have h2 := condExp_mono (m := F k) hREI.norm (integrable_const (16 * C ^ 5 * t))
      (Filter.Eventually.of_forall hRb)
    rw [condExp_const hm] at h2
    filter_upwards [h1, h2] with ω h1 h2
    exact h1.trans h2
  rw [hdecomp]
  filter_upwards [c1, c3, c4, cadd1, cadd2, cadd3, cadd4, hξEc, hξ2Ec, hmean, hsec, hRc]
    with ω e1 e3 e4 a1 a2 a3 a4 x1 x2 hm1 hm2 hr hω
  rw [a4, Pi.add_apply, a3, Pi.add_apply, a2, Pi.add_apply, a1, Pi.add_apply, e1, e3, e4, c2]
  simp only [Pi.smul_apply', Complex.real_smul]
  rw [x1, x2, Set.indicator_of_mem hω, Set.indicator_of_mem hω, hm1 hω, hm2 hω]
  simp only [A2, ρE, γE, Set.indicator_of_mem hω]
  have hst : st * st = (t : ℂ) := by
    simp only [st]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt hsmall.pos.le]
  have hkey : (0 : ℂ) * -(1 / st) + (-(st * ρ ω) + (t : ℂ) ^ 2 / st * ρ ω ^ 2 * γ ω) +
      ((t - η ω : ℝ) : ℂ) * (γ ω / st) + (0 : ℂ) * (2 * (t : ℂ) * ρ ω * γ ω / st) +
        μ[RE | F k] ω - st * (γ ω - ρ ω) =
      ((t : ℂ) ^ 2 * ρ ω ^ 2 - (η ω : ℂ)) * γ ω / st + μ[RE | F k] ω := by
    push_cast; field_simp; linear_combination (-(γ ω)) * hst
  push_cast at hkey ⊢
  rw [hkey]
  have hmain : ‖((t : ℂ) ^ 2 * ρ ω ^ 2 - (η ω : ℂ)) * γ ω / st‖ ≤ (C ^ 2 + C ^ 3) * t := by
    rw [norm_div, hstn, norm_mul]
    have hρω := hρ ω hω
    have hγω := hγ ω hω
    have hηω := hη ω hω
    have h1 : ‖(t : ℂ) ^ 2 * ρ ω ^ 2 - (η ω : ℂ)‖ ≤ t ^ 2 * C ^ 2 + C * t ^ 2 := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hsmall.pos.le]
        gcongr
      · rw [Complex.norm_real, Real.norm_eq_abs]; exact hηω
    have h2 : ‖(t : ℂ) ^ 2 * ρ ω ^ 2 - (η ω : ℂ)‖ * ‖γ ω‖ ≤ (t ^ 2 * C ^ 2 + C * t ^ 2) * C :=
      mul_le_mul h1 hγω (norm_nonneg _) (by positivity)
    rw [div_le_iff₀ hs]
    have ht2 : t ^ 2 ≤ t * Real.sqrt t := by
      have := hsmall.t_le_sqrt
      nlinarith [hsmall.pos]
    nlinarith [mul_nonneg hC hC, pow_nonneg hC 3]
  calc ‖((t : ℂ) ^ 2 * ρ ω ^ 2 - (η ω : ℂ)) * γ ω / st + μ[RE | F k] ω‖
      ≤ ‖((t : ℂ) ^ 2 * ρ ω ^ 2 - (η ω : ℂ)) * γ ω / st‖ + ‖μ[RE | F k] ω‖ := norm_add_le _ _
    _ ≤ (C ^ 2 + C ^ 3) * t + 16 * C ^ 5 * t := add_le_add hmain hr
    _ = (C ^ 2 + C ^ 3 + 16 * C ^ 5) * t := by ring

end AndersonAC.AgentS6
#print axioms AndersonAC.AgentS6.condExp_heatCoeff_mean
