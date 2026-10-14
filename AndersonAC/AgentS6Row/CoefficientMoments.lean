import AndersonAC.AgentS6.CondHeat
import AndersonAC.AgentS6Row.HeatMoments

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6Row

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Conditional second moment of the heat coefficient on a predictable event. -/
theorem condExp_heatCoeff_second (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (k : ℕ) {E : Set Ω} (hE : MeasurableSet[F k] E)
    {t C : ℝ} (hs : AndersonAC.L64.Small t C) {ρ γ : Ω → ℂ}
    (hρm : StronglyMeasurable[F k] ρ) (hγm : StronglyMeasurable[F k] γ)
    {ξ η : Ω → ℝ} (hξm : Measurable ξ)
    (hρ : ∀ ω ∈ E, ‖ρ ω‖ ≤ C) (hγ : ∀ ω ∈ E, ‖γ ω‖ ≤ C)
    (hξb : ∀ ω ∈ E, |ξ ω| ≤ C * Real.sqrt t)
    (hξI : Integrable ξ μ) (hξ2I : Integrable (fun ω => ξ ω ^ 2) μ)
    (hmean : ∀ᵐ ω ∂μ, ω ∈ E → μ[ξ | F k] ω = 0)
    (hsec : ∀ᵐ ω ∂μ, ω ∈ E → μ[(fun ω => ξ ω ^ 2) | F k] ω = t - η ω)
    (hη : ∀ᵐ ω ∂μ, ω ∈ E → |η ω| ≤ C * t ^ 2) :
    ∀ᵐ ω ∂μ, ω ∈ E →
      |μ[E.indicator (fun ω => ‖AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω)‖ ^ 2) | F k] ω - 1|
        ≤ (C + C ^ 2 + 96 * C ^ 4) * Real.sqrt t := by
  have hm : F k ≤ mΩ := F.le k
  have hEm : MeasurableSet E := hm _ hE
  have hC := hs.C_nonneg
  have ht := hs.pos
  set ρE : Ω → ℂ := E.indicator ρ
  set ξE : Ω → ℝ := E.indicator ξ
  set ξ2E : Ω → ℝ := E.indicator (fun ω => ξ ω ^ 2)
  set f : Ω → ℝ := E.indicator (fun ω => ‖AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω)‖ ^ 2)
  set A : Ω → ℝ := fun ω => ξ2E ω / t
  set B : Ω → ℝ := fun ω => (2 * (ρE ω).re) * ξE ω
  set D : Ω → ℝ := fun ω => t * ‖ρE ω‖ ^ 2
  set R : Ω → ℝ := fun ω => f ω - (A ω + B ω + D ω)
  have hρEm : StronglyMeasurable[F k] ρE := hρm.indicator hE
  have hρEb : ∀ ω, ‖ρE ω‖ ≤ C := fun ω => by
    by_cases h : ω ∈ E
    · simpa only [ρE, Set.indicator_of_mem h] using hρ ω h
    · simpa [ρE, h] using hC
  have hξEI : Integrable ξE μ := hξI.indicator hEm
  have hξ2EI : Integrable ξ2E μ := hξ2I.indicator hEm
  have hAI : Integrable A μ := hξ2EI.div_const t
  have hbm : StronglyMeasurable[F k] (fun ω => 2 * (ρE ω).re) :=
    stronglyMeasurable_const.mul (Complex.reCLM.continuous.comp_stronglyMeasurable hρEm)
  have hbb : ∀ ω, ‖2 * (ρE ω).re‖ ≤ 2 * C := fun ω => by
    calc
      _ = 2 * |(ρE ω).re| := by simp [Real.norm_eq_abs, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans (hρEb ω)) (show (0 : ℝ) ≤ 2 by norm_num)
  have hBI : Integrable B μ := by
    have hi := hξEI.bdd_mul (hbm.mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall hbb)
    simpa [B, mul_comm] using hi
  have hDm : StronglyMeasurable[F k] D :=
    stronglyMeasurable_const.mul (hρEm.norm.pow 2)
  have hDb : ∀ ω, ‖D ω‖ ≤ t * C ^ 2 := fun ω => by
    simp only [D, norm_mul, Real.norm_eq_abs, abs_of_nonneg ht.le,
      abs_of_nonneg (sq_nonneg ‖ρE ω‖)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hρEb ω) 2) ht.le
  have hDI : Integrable D μ := (integrable_const (t * C ^ 2)).mono'
    (hDm.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hDb)
  have hfm : Measurable f := by
    have hr : Measurable ρ := (hρm.mono hm).measurable
    have hg : Measurable γ := (hγm.mono hm).measurable
    have ha : Measurable (fun ω => (ξ ω : ℂ) + (t : ℂ) * ρ ω) :=
      (Complex.measurable_ofReal.comp hξm).add (measurable_const.mul hr)
    have hc : Measurable (fun ω => AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω)) :=
      ha.neg.div (measurable_const.mul (measurable_const.add (ha.mul hg)))
    exact (hc.norm.pow_const 2).indicator hEm
  have hfb : ∀ ω, ‖f ω‖ ≤ (4 * C) ^ 2 := fun ω => by
    by_cases h : ω ∈ E
    · simp only [f, Set.indicator_of_mem h]
      rw [Real.norm_of_nonneg (sq_nonneg (‖AndersonAC.L64.hc t (ρ ω) (γ ω) (ξ ω)‖ : ℝ))]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (AndersonAC.L64.norm_hc_le hs (hρ ω h) (hγ ω h) (hξb ω h)) 2
    · simp only [f, Set.indicator_of_notMem h, norm_zero]
      positivity
  have hfI : Integrable f μ := (integrable_const ((4 * C) ^ 2)).mono'
    hfm.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hRb : ∀ ω, |R ω| ≤ 96 * C ^ 4 * Real.sqrt t := fun ω => by
    by_cases h : ω ∈ E
    · have he : ‖(ξ ω : ℂ) + (t : ℂ) * ρ ω‖ ^ 2 / t =
          ξ ω ^ 2 / t + 2 * (ρ ω).re * ξ ω + t * ‖ρ ω‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im]
        field_simp
        ring
      simpa only [R, f, A, B, D, ρE, ξE, ξ2E, Set.indicator_of_mem h, he] using
        AndersonAC.L64.abs_norm_hc_sq_sub_le hs (hρ ω h) (hγ ω h) (hξb ω h)
    · simp only [R, f, A, B, D, ρE, ξE, ξ2E, Set.indicator_of_notMem h,
        Complex.zero_re, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
        mul_zero, zero_add, sub_self, abs_zero]
      positivity
  have hRI : Integrable R μ := hfI.sub ((hAI.add hBI).add hDI)
  have hRc : ∀ᵐ ω ∂μ, |μ[R | F k] ω| ≤ 96 * C ^ 4 * Real.sqrt t :=
    ae_bdd_abs_condExp_of_ae_bdd_abs (Filter.Eventually.of_forall hRb)
  have ca : μ[A | F k] =ᵐ[μ] fun ω => μ[ξ2E | F k] ω / t := by
    have hh := condExp_smul (μ := μ) (t⁻¹ : ℝ) ξ2E (F k)
    have he : A = (t⁻¹ : ℝ) • ξ2E := by
      funext ω
      simp [A, div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [he]
    filter_upwards [hh] with ω hω
    simpa only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hω
  have cb : μ[B | F k] =ᵐ[μ] fun ω => (2 * (ρE ω).re) * μ[ξE | F k] ω :=
    condExp_mul_of_stronglyMeasurable_left hbm hBI hξEI
  have cd := condExp_of_stronglyMeasurable hm hDm hDI
  have cx := condExp_indicator (m := F k) hξI hE
  have cx2 := condExp_indicator (m := F k) hξ2I hE
  have cab := condExp_add (m := F k) hAI hBI
  have cabd := condExp_add (m := F k) (hAI.add hBI) hDI
  have cr := condExp_add (m := F k) ((hAI.add hBI).add hDI) hRI
  have heq : f = A + B + D + R := by funext ω; simp only [R, Pi.add_apply]; ring
  rw [heq]
  filter_upwards [ca, cb, cx, cx2, cab, cabd, cr, hmean, hsec, hη, hRc]
    with ω ha hb hx hx2 hab habd hr hme hse hηω hrc hω
  rw [hr, Pi.add_apply, habd, Pi.add_apply, hab, Pi.add_apply, ha, hb, cd,
    hx, hx2, Set.indicator_of_mem hω, Set.indicator_of_mem hω, hme hω, hse hω]
  simp only [ρE, D, Set.indicator_of_mem hω, mul_zero, add_zero]
  have hηb : |η ω / t| ≤ C * t := by
    rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
    calc |η ω| ≤ C * t ^ 2 := hηω hω
      _ = C * t * t := by ring
  have hρb : t * ‖ρ ω‖ ^ 2 ≤ t * C ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hρ ω hω) 2) ht.le
  calc
    |(t - η ω) / t + t * ‖ρ ω‖ ^ 2 + μ[R | F k] ω - 1|
        = |-(η ω / t) + t * ‖ρ ω‖ ^ 2 + μ[R | F k] ω| := by
          congr 1
          field_simp
          ring
    _ ≤ |η ω / t| + t * ‖ρ ω‖ ^ 2 + |μ[R | F k] ω| := by
      calc
        _ ≤ |-(η ω / t) + t * ‖ρ ω‖ ^ 2| + |μ[R | F k] ω| := abs_add_le _ _
        _ ≤ |η ω / t| + t * ‖ρ ω‖ ^ 2 + |μ[R | F k] ω| := by
          gcongr
          have h0 : 0 ≤ t * ‖ρ ω‖ ^ 2 := mul_nonneg ht.le (sq_nonneg _)
          calc
            _ ≤ |-(η ω / t)| + |t * ‖ρ ω‖ ^ 2| := abs_add_le _ _
            _ = _ := by rw [abs_neg, abs_of_nonneg h0]
    _ ≤ C * t + t * C ^ 2 + 96 * C ^ 4 * Real.sqrt t := by gcongr
    _ ≤ (C + C ^ 2 + 96 * C ^ 4) * Real.sqrt t := by
      have h1 := mul_le_mul_of_nonneg_left hs.t_le_sqrt hC
      have h2 := mul_le_mul_of_nonneg_left hs.t_le_sqrt (sq_nonneg C)
      nlinarith

end AndersonAC.AgentS6Row

#print axioms AndersonAC.AgentS6Row.condExp_heatCoeff_second
