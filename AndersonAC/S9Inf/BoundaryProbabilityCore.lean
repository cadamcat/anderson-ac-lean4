import AndersonAC.S9Inf.AndersonGreen
import AndersonAC.S9Inf.PotentialContinuous

/-! Bounded convergence detects a positive imaginary boundary value.
The contradiction proof needs no choice of a measurable boundary value. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology

namespace AndersonAC.SolS9Inf

theorem positive_boundary_probability_of_liminf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ → ℂ) (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝[>] 0))
    (hmeas : ∀ n, Measurable (fun ω => f ω (η n)))
    (hnonneg : ∀ n ω, 0 ≤ (f ω (η n)).im)
    (hfinite : ∀ᵐ ω ∂μ, ∃ w : ℂ, Tendsto (f ω) (𝓝[>] 0) (𝓝 w))
    (C K l : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hl : 0 < l)
    (hlower : l ≤ liminf (fun n => ∫ ω, min (K * (f ω (η n)).im) C ∂μ) atTop) :
    0 < μ {ω | ∃ w : ℂ, Tendsto (f ω) (𝓝[>] 0) (𝓝 w) ∧ 0 < w.im} := by
  by_contra hpos
  have hzero : μ {ω | ∃ w : ℂ,
      Tendsto (f ω) (𝓝[>] 0) (𝓝 w) ∧ 0 < w.im} = 0 := le_zero_iff.mp (not_lt.mp hpos)
  have hnot : ∀ᵐ ω ∂μ, ¬ ∃ w : ℂ,
      Tendsto (f ω) (𝓝[>] 0) (𝓝 w) ∧ 0 < w.im := by
    simpa only [ae_iff, not_not] using hzero
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun n => min (K * (f ω (η n)).im) C) atTop (𝓝 0) := by
    filter_upwards [hfinite, hnot] with ω hω hn
    obtain ⟨w, hw⟩ := hω
    have hseq := hw.comp hη
    have him := Complex.continuous_im.continuousAt.tendsto.comp hseq
    have hw0 : w.im = 0 := by
      apply le_antisymm
      · exact not_lt.mp (fun hp => hn ⟨w, hw, hp⟩)
      · exact ge_of_tendsto him (Eventually.of_forall (fun n => hnonneg n ω))
    have h := ((tendsto_const_nhds (x := K)).mul him).min
      (tendsto_const_nhds (x := C))
    simpa only [Function.comp_apply, hw0, mul_zero, min_eq_left hC] using h
  have hbound (n : ℕ) (ω : Ω) : ‖min (K * (f ω (η n)).im) C‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (mul_nonneg hK (hnonneg n ω)) hC)]
    exact min_le_right _ _
  have hi := tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    (fun n => (((Complex.measurable_im.comp (hmeas n)).const_mul K).min
      measurable_const).aestronglyMeasurable)
    (integrable_const C) (fun n => ae_of_all _ (hbound n)) hlim
  simp only [integral_zero] at hi
  simp only [Function.comp_apply] at hi
  rw [hi.liminf_eq] at hlower
  exact (not_le_of_gt hl) hlower

theorem comparable_heights_tendsto
    (η : ℕ → ℝ)
    (hη : (∀ m, 0 < η m) ∧ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ m in atTop, a / (4 : ℝ) ^ m ≤ η m ∧ η m ≤ c / (4 : ℝ) ^ m) :
    Tendsto η atTop (𝓝[>] 0) := by
  obtain ⟨a, c, ha, hc, hbounds⟩ := hη.2
  have h4 : Tendsto (fun m : ℕ => (4 : ℝ) ^ m) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).comp
      tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun m : ℕ => c / (4 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      ((tendsto_const_nhds (x := c)).mul (tendsto_inv_atTop_zero.comp h4))
  exact tendsto_nhdsWithin_iff.mpr
    ⟨squeeze_zero' (Eventually.of_forall (fun m => (hη.1 m).le))
      (hbounds.mono (fun _ h => h.2)) hb,
      Eventually.of_forall hη.1⟩

end AndersonAC.SolS9Inf
