import AndersonAC.S78.Definitions
import AndersonAC.S78.QuantitativeReset
import AndersonAC.S78Taylor.Taylor

open scoped Topology Matrix.Norms.L2Operator
open Filter
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

/-- A positive power fits in any prescribed fixed ball at a uniform cutoff. -/
theorem reset_radius_small (s a : ℝ) (hs : 0 < s) (ha : 0 < a) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → t ^ s ≤ a := by
  have hlim : Tendsto (fun t : ℝ => t ^ s) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hs.ne'] using
      (Real.continuous_rpow_const hs.le).tendsto 0
  obtain ⟨ε, hε, hbound⟩ := Metric.mem_nhds_iff.mp
    (hlim.eventually (eventually_lt_nhds ha))
  refine ⟨ε, hε, ?_⟩
  intro t ht hsmall
  exact (hbound (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
      using hsmall)).le

/-- The small square-kernel hypothesis supplies the genuine matrix inverse
needed by the contraction, in the Euclidean operator norm. -/
theorem reset_linear_inverse {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : Matrix ι ι ℂ)
    (hK : AndersonAC.S78.matrixNorm K < 1 / 2) :
    (1 - K) * (1 - K)⁻¹ = 1 := by
  have hnorm : ‖K‖ < 1 / 2 := hK
  have hu : IsUnit (1 - K) :=
    isUnit_one_sub_of_norm_lt_one (hnorm.trans (by norm_num))
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- Proposition 7.4's matrix fixed point. The cutoff precedes the active type,
and the solution can be required to lie in any additional fixed small ball.
Row and relative-form estimates are the separate ResetVariation obligation. -/
theorem diagonal_reset_exists (c C a : ℝ) (hc : 0 < c) (hC : 1 ≤ C)
    (ha : 0 < a) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ),
      0 < t → t < t₀ → (∀ i j, M i j = M j i ∧ (M i j).im = 0) →
      (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ ‖r i‖ ≤ C) →
      (∀ i, (AndersonAC.S78.resetInverse M r t i i).im ≤ C) →
      AndersonAC.S78.matrixNorm (AndersonAC.S78.squareKernel
        ((Real.sqrt t : ℂ) • AndersonAC.S78.resetInverse M r t)) < 1 / 2 →
      (∀ v : ι → ℂ, ‖((1 - AndersonAC.S78.squareKernel
        ((Real.sqrt t : ℂ) • AndersonAC.S78.resetInverse M r t))⁻¹).mulVec v‖ ≤
        C * Real.log (1 / t) * ‖v‖) →
      ‖AndersonAC.S78.resetLag M r t‖ ≤ t ^ (0.36 * AndersonAC.S78.delta) →
      ∃ ζ : ι → ℂ, ‖ζ‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) ∧ ‖ζ‖ ≤ a ∧
        (∀ i, AndersonAC.S78.resetInverse M (r + ζ) t i i = (r + ζ) i) ∧
        (∀ i, c / 2 ≤ ((r + ζ) i).im ∧ ((r + ζ) i).im ≤ 2 * C) := by
  obtain ⟨CT, aT, hCT, haT, htaylor⟩ := reset_taylor_proof c C hc hC
  let B := max C CT
  have hB : 1 ≤ B := hC.trans (le_max_left _ _)
  have hδ : 0 < AndersonAC.S78.delta := by norm_num [AndersonAC.S78.delta]
  obtain ⟨tB, htB, hreset⟩ := reset_from_uniform_taylor B AndersonAC.S78.delta hB hδ
  let cap := min a (min aT (min (c / 2) C))
  have hcap : 0 < cap := by dsimp [cap]; positivity
  obtain ⟨tA, htA, hsmall⟩ := reset_radius_small
    (0.35 * AndersonAC.S78.delta) cap (by positivity) hcap
  refine ⟨min tB (min tA 1), lt_min htB (lt_min htA (by norm_num)), ?_⟩
  intro ι _ _ _ M r t ht hlt hM hr hdiag hK hP hlag
  have htB' : t < tB := hlt.trans_le (min_le_left _ _)
  have htA' : t < tA := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht1 : t < 1 := hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrad : t ^ (0.35 * AndersonAC.S78.delta) ≤ cap := hsmall t ht htA'
  have hradA : t ^ (0.35 * AndersonAC.S78.delta) ≤ a := hrad.trans (min_le_left _ _)
  have hradT : t ^ (0.35 * AndersonAC.S78.delta) ≤ aT :=
    hrad.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hradc : t ^ (0.35 * AndersonAC.S78.delta) ≤ c / 2 :=
    hrad.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hradC : t ^ (0.35 * AndersonAC.S78.delta) ≤ C :=
    hrad.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨R, hRexp, hRnorm, hRlip⟩ :=
    htaylor ι M r t ht hM (fun i => ⟨(hr i).1, (hr i).2.1, hdiag i⟩)
  let diagonal := fun z : ι → ℂ => fun i => AndersonAC.S78.resetInverse M (r + z) t i i
  let K := AndersonAC.S78.squareKernel ((Real.sqrt t : ℂ) • AndersonAC.S78.resetInverse M r t)
  have hlog : 0 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos ht.le ht1.le)
  obtain ⟨ζ, hζ, hfixed⟩ := hreset ι diagonal r K (1 - K)⁻¹ R t ht htB'
    (reset_linear_inverse K hK)
    (fun v => (hP v).trans (by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C CT) hlog) (norm_nonneg v)))
    (fun z hz => by
      dsimp only [diagonal]
      rw [add_zero]
      exact hRexp z (hz.trans hradT))
    (fun z hz => (hRnorm z (hz.trans hradT)).trans
      (mul_le_mul_of_nonneg_right (le_max_right C CT) (sq_nonneg _)))
    (fun z w hz hw => (hRlip (t ^ (0.35 * AndersonAC.S78.delta)) z w
      (Real.rpow_nonneg ht.le _) hradT hz hw).trans (by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_max_right C CT) (Real.rpow_nonneg ht.le _)))
    (by
      dsimp only [diagonal]
      rw [add_zero]
      exact hlag)
  refine ⟨ζ, hζ, hζ.trans hradA, (fun i => congrFun hfixed i), ?_⟩
  intro i
  have hzi : |(ζ i).im| ≤ ‖ζ‖ :=
    (Complex.abs_im_le_norm _).trans (norm_le_pi_norm ζ i)
  have hi := hr i
  have hzc := hζ.trans hradc
  have hzC := hζ.trans hradC
  simp only [Pi.add_apply, Complex.add_im]
  constructor <;> linarith [neg_abs_le (ζ i).im, le_abs_self (ζ i).im]

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.reset_radius_small
#print axioms AndersonAC.SolS78.reset_linear_inverse
#print axioms AndersonAC.SolS78.diagonal_reset_exists
