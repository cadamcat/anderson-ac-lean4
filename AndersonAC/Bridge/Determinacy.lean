import AndersonAC.Blueprint.Target
import AndersonAC.Challenge

noncomputable section

open MeasureTheory OAI.Anderson
open Filter
open scoped ENNReal lp
open scoped Topology
open AndersonAC.Blueprint AndersonChallenge

namespace AndersonAC.LunaBridge

/-- The even moments of a scalar spectral measure are controlled by the operator norm. -/
lemma spectralMeasure_evenMoment_le {d : ℕ} {T : Operator d} (v : StateSpace d)
    {μ : Measure ℝ} (hμ : IsSpectralMeasure T v μ) (k : ℕ) :
    ∫ t : ℝ, t ^ (2 * k) ∂μ ≤ ‖v‖ ^ 2 * ‖T‖ ^ (2 * k) := by
  rw [(hμ.2 (2 * k)).2]
  have hpow : ∀ n : ℕ, ‖T ^ n‖ ≤ ‖T‖ ^ n := by
    intro n
    induction n with
    | zero =>
      change ‖ContinuousLinearMap.id ℂ (StateSpace d)‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      rw [pow_succ]
      calc
        ‖T ^ n * T‖ ≤ ‖T ^ n‖ * ‖T‖ := norm_mul_le _ _
        _ ≤ ‖T‖ ^ n * ‖T‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ‖T‖ ^ (n + 1) := by rw [pow_succ]
  have hinner : ‖inner ℂ v ((T ^ (2 * k)) v)‖ ≤
      ‖v‖ ^ 2 * ‖T‖ ^ (2 * k) := by
    calc
      ‖inner ℂ v ((T ^ (2 * k)) v)‖ ≤ ‖v‖ * ‖(T ^ (2 * k)) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖T ^ (2 * k)‖ * ‖v‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖v‖ * (‖T‖ ^ (2 * k) * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hpow (2 * k)) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖v‖ ^ 2 * ‖T‖ ^ (2 * k) := by ring
  calc
    (inner ℂ v ((T ^ (2 * k)) v)).re ≤ |(inner ℂ v ((T ^ (2 * k)) v)).re| := le_abs_self _
    _ ≤ ‖inner ℂ v ((T ^ (2 * k)) v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖v‖ ^ 2 * ‖T‖ ^ (2 * k) := hinner

/-- Moment growth forces every spectral measure in the challenge to have no mass
beyond any radius strictly larger than the operator norm. -/
lemma spectralMeasure_tail_zero {d : ℕ} {T : Operator d} (v : StateSpace d)
    {μ : Measure ℝ} (hμ : IsSpectralMeasure T v μ) {r : ℝ} (hr : ‖T‖ < r) :
    μ {x : ℝ | r ≤ |x|} = 0 := by
  let C : ℝ := ‖v‖ ^ 2
  let q : ℝ := ‖T‖ / r
  have hR : 0 ≤ ‖T‖ := norm_nonneg _
  have hrpos : 0 < r := lt_of_le_of_lt hR hr
  have hq0 : 0 ≤ q := div_nonneg hR hrpos.le
  have hq1 : q < 1 := (div_lt_one₀ hrpos).2 hr
  have hq2 : q ^ 2 < 1 := by nlinarith [sq_nonneg q]
  have hC : 0 ≤ C := by positivity
  have hpow_tendsto : Tendsto (fun n : ℕ => (q ^ 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg q) hq2
  have hbound_tendsto : Tendsto
      (fun n : ℕ => ENNReal.ofReal (C * q ^ (2 * (n + 1)))) atTop (𝓝 0) := by
    have hmul : Tendsto (fun n : ℕ => (q ^ 2) ^ n * (C * q ^ 2)) atTop (𝓝 0) :=
      by simpa using Tendsto.mul_const (C * q ^ 2) hpow_tendsto
    have hreal : Tendsto (fun n : ℕ => C * q ^ (2 * (n + 1))) atTop (𝓝 0) := by
      convert hmul using 1 <;> ext n <;> simp [pow_mul, pow_succ] <;> ring
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have htail_bound (n : ℕ) :
      μ {x : ℝ | r ≤ |x|} ≤ ENNReal.ofReal (C * q ^ (2 * (n + 1))) := by
    let m : ℕ := 2 * (n + 1)
    have hm : m = 2 * (n + 1) := rfl
    have hmEven : Even m := by dsimp [m]; exact even_two_mul _
    have hrm : 0 < r ^ m := pow_pos hrpos _
    have hInt : Integrable (fun x : ℝ => x ^ m / r ^ m) μ := by
      have h := (hμ.2 m).1.mul_const ((r ^ m)⁻¹)
      convert h using 1 <;> ext x <;> simp [div_eq_mul_inv]
    have hnonneg : 0 ≤ᵐ[μ] fun x : ℝ => x ^ m / r ^ m := by
      filter_upwards with x
      apply div_nonneg
      · exact hmEven.pow_nonneg x
      · exact pow_nonneg hrpos.le _
    have hlarge : ∀ x ∈ {x : ℝ | r ≤ |x|},
        1 ≤ x ^ m / r ^ m := by
      intro x hx
      change r ≤ |x| at hx
      have hxpow : r ^ m ≤ x ^ m := by
        calc
          r ^ m ≤ |x| ^ m := by gcongr
          _ = x ^ m := hmEven.pow_abs x
      exact (le_div_iff₀ hrm).2 (by simpa using hxpow)
    have hmoment := spectralMeasure_evenMoment_le v hμ (n + 1)
    have hinter : ∫ x : ℝ, x ^ m / r ^ m ∂μ ≤ C * q ^ m := by
      have heq : (fun x : ℝ => x ^ m / r ^ m) = fun x => x ^ m * (r ^ m)⁻¹ := by
        ext x
        simp [div_eq_mul_inv]
      rw [heq, integral_mul_const]
      have hmoment' : ∫ x : ℝ, x ^ m ∂μ ≤ C * ‖T‖ ^ m := by
        simpa [m, C] using hmoment
      calc
        (∫ x : ℝ, x ^ m ∂μ) * (r ^ m)⁻¹ ≤
            (C * ‖T‖ ^ m) * (r ^ m)⁻¹ :=
          mul_le_mul_of_nonneg_right hmoment' (inv_nonneg.mpr hrm.le)
        _ = C * q ^ m := by
          dsimp [q]
          rw [div_pow]
          simp only [div_eq_mul_inv]
          ring
    have hmarkov := hInt.measure_le_integral hnonneg hlarge
    exact hmarkov.trans (ENNReal.ofReal_le_ofReal hinter)
  have hmass : μ {x : ℝ | r ≤ |x|} ≤ 0 := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hbound_tendsto
    intro n
    exact htail_bound n
  exact le_antisymm hmass bot_le

/-- The moment characterization in the challenge implies the same compact support
as the OAI spectral resolution. -/
lemma spectralMeasure_supported {d : ℕ} {T : Operator d} (v : StateSpace d)
    {μ : Measure ℝ} (hμ : IsSpectralMeasure T v μ) :
    μ (Set.Icc (-‖T‖) ‖T‖)ᶜ = 0 := by
  have hsubset : μ.support ⊆ Set.Icc (-‖T‖) ‖T‖ := by
    intro x hx
    by_contra hnot
    have hR : 0 ≤ ‖T‖ := norm_nonneg _
    have hxabs : ‖T‖ < |x| := by
      have hnot' : ¬ (-‖T‖ ≤ x ∧ x ≤ ‖T‖) := by simpa using hnot
      rcases not_and_or.mp hnot' with hleft | hright
      · have hxlt : x < -‖T‖ := lt_of_not_ge hleft
        rw [abs_of_neg (lt_of_lt_of_le hxlt (neg_nonpos.mpr hR))]
        linarith
      · have hxgt : ‖T‖ < x := lt_of_not_ge hright
        rw [abs_of_pos (lt_of_le_of_lt hR hxgt)]
        exact hxgt
    let r := (‖T‖ + |x|) / 2
    have hr : ‖T‖ < r := by dsimp [r]; linarith
    have hrx : r < |x| := by dsimp [r]; linarith
    have htail := spectralMeasure_tail_zero v hμ hr
    have hball : Metric.ball x (|x| - r) ⊆ {y : ℝ | r ≤ |y|} := by
      intro y hy
      have hdist : |y - x| < |x| - r := by simpa [Real.dist_eq] using hy
      have habs : |(|y| - |x|)| ≤ |y - x| := by
        simpa [Real.norm_eq_abs] using norm_abs_sub_abs y x
      have hlow : r < |y| := by
        have h := neg_le_abs (|y| - |x|)
        linarith
      exact le_of_lt hlow
    have hball0 : μ (Metric.ball x (|x| - r)) = 0 := measure_mono_null hball htail
    have hxnot : x ∉ μ.support :=
      (Measure.notMem_support_iff_exists).2
        ⟨Metric.ball x (|x| - r), Metric.ball_mem_nhds _ (sub_pos.mpr hrx), hball0⟩
    exact hxnot hx
  have hcompsupport : μ μ.supportᶜ = 0 := by simp
  apply measure_mono_null (Set.compl_subset_compl.mpr hsubset) hcompsupport

end AndersonAC.LunaBridge
