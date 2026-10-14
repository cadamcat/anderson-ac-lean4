import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.ContinuousMap.Weierstrass

/-! Measurability of a compactly supported probability measure family from its moments. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace AndersonAC.SolS9

private theorem integrable_pow_of_compact_support {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {M : ℝ} (hM : 0 ≤ M) (hsupp : μ (Set.Icc (-M) M)ᶜ = 0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ := by
  have hsupport : ∀ᵐ x ∂μ, x ∈ Set.Icc (-M) M := by
    apply ae_iff.mpr
    have hset : {x : ℝ | ¬ x ∈ Set.Icc (-M) M} = (Set.Icc (-M) M)ᶜ := by
      ext x
      simp
    rw [hset]
    exact hsupp
  have hpow : ∀ᵐ x ∂μ, x ^ n ∈ Set.Icc (-(M ^ n)) (M ^ n) := by
    filter_upwards [hsupport] with x hx
    have hxnorm : ‖x‖ ≤ M := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    have hpowNorm : ‖x ^ n‖ ≤ M ^ n := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg x) hxnorm n
    have hpowAbs : |x ^ n| ≤ M ^ n := by
      simpa only [Real.norm_eq_abs] using hpowNorm
    exact abs_le.mp hpowAbs
  exact Integrable.of_mem_Icc (-(M ^ n)) (M ^ n)
    (measurable_id.pow_const n).aemeasurable hpow

private theorem integrable_polynomial_of_compact_support {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 ≤ M)
    (hsupp : μ (Set.Icc (-M) M)ᶜ = 0) (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x) μ := by
  classical
  have hpow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) μ :=
    integrable_pow_of_compact_support hM hsupp n
  have hpoint (x : ℝ) : p.eval x = ∑ n ∈ p.support, p.coeff n * x ^ n := by
    conv_lhs => rw [← p.sum_monomial_eq]
    rw [Polynomial.eval_sum]
    simp only [Polynomial.sum_def, Polynomial.eval_monomial]
  rw [show (fun x : ℝ => p.eval x) =
      (fun x => ∑ n ∈ p.support, p.coeff n * x ^ n) from funext hpoint]
  exact integrable_finsetSum p.support fun n hn => (hpow n).const_mul (p.coeff n)

private theorem measurable_integral_polynomial {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Ξ → Measure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hprob : ∀ ξ, IsProbabilityMeasure (μ ξ))
    (hsupp : ∀ ξ, μ ξ (Set.Icc (-M) M)ᶜ = 0)
    (hmom : ∀ n : ℕ, Measurable (fun ξ => ∫ t : ℝ, t ^ n ∂μ ξ))
    (p : Polynomial ℝ) : Measurable (fun ξ => ∫ x : ℝ, p.eval x ∂μ ξ) := by
  classical
  have hpow (ξ : Ξ) (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (μ ξ) := by
    letI : IsProbabilityMeasure (μ ξ) := hprob ξ
    exact integrable_pow_of_compact_support hM (hsupp ξ) n
  have hsum (ξ : Ξ) :
      ∫ x : ℝ, p.eval x ∂μ ξ =
        ∑ n ∈ p.support, p.coeff n * (∫ x : ℝ, x ^ n ∂μ ξ) := by
    have hpoint (x : ℝ) : p.eval x = ∑ n ∈ p.support, p.coeff n * x ^ n := by
      conv_lhs => rw [← p.sum_monomial_eq]
      rw [Polynomial.eval_sum]
      simp only [Polynomial.sum_def, Polynomial.eval_monomial]
    rw [integral_congr_ae (ae_of_all (μ ξ) hpoint),
      integral_finsetSum p.support (fun n hn => (hpow ξ n).const_mul (p.coeff n))]
    simp only [integral_const_mul]
  have hsum_meas :
      Measurable (fun ξ : Ξ => ∑ n ∈ p.support, p.coeff n * (∫ x : ℝ, x ^ n ∂μ ξ)) := by
    exact Finset.measurable_fun_sum _ fun n hn => (hmom n).const_mul (p.coeff n)
  rw [show (fun ξ : Ξ => ∫ x : ℝ, p.eval x ∂μ ξ) =
      (fun ξ => ∑ n ∈ p.support, p.coeff n * (∫ x : ℝ, x ^ n ∂μ ξ)) from funext hsum]
  exact hsum_meas

private theorem measurable_integral_boundedContinuousReal {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Ξ → Measure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hprob : ∀ ξ, IsProbabilityMeasure (μ ξ))
    (hsupp : ∀ ξ, μ ξ (Set.Icc (-M) M)ᶜ = 0)
    (hmom : ∀ n : ℕ, Measurable (fun ξ => ∫ t : ℝ, t ^ n ∂μ ξ))
    (f : ℝ →ᵇ ℝ) : Measurable (fun ξ => ∫ x : ℝ, f x ∂μ ξ) := by
  classical
  let p : ℕ → Polynomial ℝ := fun n => Classical.choose <|
    exists_polynomial_near_of_continuousOn (-M) M (fun x => f x) f.continuous.continuousOn
      (1 / (n + 1 : ℝ)) (by positivity)
  have hp (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-M) M) :
      |(p n).eval x - f x| < 1 / (n + 1 : ℝ) :=
    Classical.choose_spec (exists_polynomial_near_of_continuousOn (-M) M
      (fun x => f x) f.continuous.continuousOn (1 / (n + 1 : ℝ)) (by positivity)) x hx
  have hpolyMeas (n : ℕ) := measurable_integral_polynomial μ M hM hprob hsupp hmom (p n)
  apply measurable_of_tendsto_metrizable hpolyMeas
  rw [tendsto_pi_nhds]
  intro ξ
  letI : IsProbabilityMeasure (μ ξ) := hprob ξ
  have hsupport : ∀ᵐ x ∂μ ξ, x ∈ Set.Icc (-M) M := by
    apply ae_iff.mpr
    have hset : {x : ℝ | ¬ x ∈ Set.Icc (-M) M} = (Set.Icc (-M) M)ᶜ := by
      ext x
      simp
    rw [hset]
    exact hsupp ξ
  have herror (n : ℕ) :
      ‖(∫ x : ℝ, (p n).eval x ∂μ ξ) - ∫ x : ℝ, f x ∂μ ξ‖ ≤ 1 / (n + 1 : ℝ) := by
    have hpInt : Integrable (fun x : ℝ => (p n).eval x) (μ ξ) :=
      integrable_polynomial_of_compact_support hM (hsupp ξ) (p n)
    have hfInt : Integrable f (μ ξ) := f.integrable (μ ξ)
    have hdiff : ∀ᵐ x ∂μ ξ, ‖(p n).eval x - f x‖ ≤ 1 / (n + 1 : ℝ) := by
      filter_upwards [hsupport] with x hx
      rw [Real.norm_eq_abs]
      exact (hp n x hx).le
    rw [← integral_sub hpInt hfInt]
    calc
      ‖∫ x : ℝ, ((p n).eval x - f x) ∂μ ξ‖ ≤
          (1 / (n + 1 : ℝ)) * (μ ξ).real Set.univ := norm_integral_le_of_norm_le_const hdiff
      _ = 1 / (n + 1 : ℝ) := by simp
  have hrecip : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < ε :=
    hrecip.eventually (Iio_mem_nhds hε)
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact (herror n).trans_lt (hN n hn)

private theorem measurable_lintegral_boundedContinuous {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Ξ → Measure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hprob : ∀ ξ, IsProbabilityMeasure (μ ξ))
    (hsupp : ∀ ξ, μ ξ (Set.Icc (-M) M)ᶜ = 0)
    (hmom : ∀ n : ℕ, Measurable (fun ξ => ∫ t : ℝ, t ^ n ∂μ ξ))
    (f : ℝ →ᵇ ℝ≥0) : Measurable (fun ξ => ∫⁻ x : ℝ, (f x : ℝ≥0∞) ∂μ ξ) := by
  classical
  let fBound : ℝ := (nndist (0 : ℝ →ᵇ ℝ≥0) f : ℝ)
  let fR : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (f x : ℝ)) (NNReal.continuous_coe.comp f.continuous) fBound (by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (f x : ℝ) by exact_mod_cast (f x).property)]
      exact_mod_cast BoundedContinuousFunction.apply_le_nndist_zero f x)
  have hmeasR := measurable_integral_boundedContinuousReal μ M hM hprob hsupp hmom fR
  have heq (ξ : Ξ) :
      ∫⁻ x : ℝ, (f x : ℝ≥0∞) ∂μ ξ =
        ENNReal.ofReal (∫ x : ℝ, fR x ∂μ ξ) := by
    letI : IsProbabilityMeasure (μ ξ) := hprob ξ
    calc
      ∫⁻ x : ℝ, (f x : ℝ≥0∞) ∂μ ξ =
          ∫⁻ x : ℝ, ENNReal.ofReal (fR x) ∂μ ξ := by
            apply lintegral_congr_ae
            exact ae_of_all (μ ξ) fun x => by simp [fR]
      _ = ENNReal.ofReal (∫ x : ℝ, fR x ∂μ ξ) :=
        (ofReal_integral_eq_lintegral_ofReal (fR.integrable (μ ξ))
          (Eventually.of_forall fun x => (f x).property)).symm
  have h := ENNReal.measurable_ofReal.comp hmeasR
  rw [show (fun ξ : Ξ => ∫⁻ x : ℝ, (f x : ℝ≥0∞) ∂μ ξ) =
      (fun ξ => ENNReal.ofReal (∫ x : ℝ, fR x ∂μ ξ)) from funext heq]
  exact h

theorem CompactMomentKernelInput_proof :
    ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Ξ → Measure ℝ) (M : ℝ), 0 ≤ M →
      (∀ ξ, IsProbabilityMeasure (μ ξ)) →
      (∀ ξ, μ ξ (Set.Icc (-M) M)ᶜ = 0) →
      (∀ n : ℕ, Measurable (fun ξ => ∫ t : ℝ, t ^ n ∂μ ξ)) →
      ∀ A : Set ℝ, MeasurableSet A → Measurable (fun ξ => μ ξ A) := by
  intro Ξ _ μ M hM hprob hsupp hmom A hA
  have hμ : Measurable μ := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    intro F hF
    let hclosed : IsClosed F := hF
    have hseq : ∀ n, Measurable (fun ξ =>
        ∫⁻ x : ℝ, (hclosed.apprSeq n x : ℝ≥0∞) ∂μ ξ) := by
      intro n
      exact measurable_lintegral_boundedContinuous μ M hM hprob hsupp hmom (hclosed.apprSeq n)
    apply ENNReal.measurable_of_tendsto hseq
    rw [tendsto_pi_nhds]
    intro ξ
    letI : IsProbabilityMeasure (μ ξ) := hprob ξ
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hclosed (μ ξ)
  exact (Measure.measurable_coe hA).comp hμ

end AndersonAC.SolS9

end
