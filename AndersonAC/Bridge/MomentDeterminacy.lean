import AndersonAC.Bridge.Determinacy

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace AndersonAC.LunaBridge

/-- Almost every point of a finite Borel measure supported in `Icc (-R) R` lies there. -/
lemma ae_mem_Icc_of_supported {μ : Measure ℝ} {R : ℝ}
    (h : μ (Set.Icc (-R) R)ᶜ = 0) :
    ∀ᵐ x ∂μ, x ∈ Set.Icc (-R) R :=
  MeasureTheory.mem_ae_iff.mpr h

/-- Monomials are integrable against a finite measure supported in `Icc (-R) R`. -/
lemma integrable_pow_of_supported {μ : Measure ℝ} [IsFiniteMeasure μ] {R : ℝ}
    (_hR : 0 ≤ R) (hsupp : μ (Set.Icc (-R) R)ᶜ = 0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) μ := by
  refine Integrable.of_bound (continuous_pow k).aestronglyMeasurable (R ^ k) ?_
  filter_upwards [ae_mem_Icc_of_supported hsupp] with x hx
  simp only [Real.norm_eq_abs]
  have habs : |x| ≤ R := by
    rw [Set.mem_Icc] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  calc |x ^ k| = |x| ^ k := abs_pow x k
    _ ≤ R ^ k := by gcongr

/-- Polynomial evaluations are integrable against a finite supported measure. -/
lemma integrable_poly_of_supported {μ : Measure ℝ} [IsFiniteMeasure μ] {R : ℝ}
    (hR : 0 ≤ R) (hsupp : μ (Set.Icc (-R) R)ᶜ = 0) (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x) μ := by
  have hfun : (fun x : ℝ => p.eval x)
      = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
    ext x
    exact Polynomial.eval_eq_sum_range x
  rw [hfun]
  apply integrable_finsetSum _ fun i _ => ?_
  exact (integrable_pow_of_supported hR hsupp i).const_mul _

/-- Equal moments imply equal polynomial integrals for supported measures. -/
lemma integral_poly_eq_of_moments_eq {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {R : ℝ} (hR : 0 ≤ R)
    (hμsupp : μ (Set.Icc (-R) R)ᶜ = 0) (hνsupp : ν (Set.Icc (-R) R)ᶜ = 0)
    (hmom : ∀ k : ℕ, ∫ x : ℝ, x ^ k ∂μ = ∫ x : ℝ, x ^ k ∂ν)
    (p : Polynomial ℝ) :
    ∫ x : ℝ, p.eval x ∂μ = ∫ x : ℝ, p.eval x ∂ν := by
  have hμint : ∀ i ∈ Finset.range (p.natDegree + 1),
      Integrable (fun x : ℝ => p.coeff i * x ^ i) μ := by
    intro i _
    exact (integrable_pow_of_supported hR hμsupp i).const_mul _
  have hνint : ∀ i ∈ Finset.range (p.natDegree + 1),
      Integrable (fun x : ℝ => p.coeff i * x ^ i) ν := by
    intro i _
    exact (integrable_pow_of_supported hR hνsupp i).const_mul _
  have heq1 : ∫ x : ℝ, p.eval x ∂μ
      = ∑ i ∈ Finset.range (p.natDegree + 1), ∫ x : ℝ, p.coeff i * x ^ i ∂μ := by
    have hfun : (fun x : ℝ => p.eval x)
        = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
      ext x
      exact Polynomial.eval_eq_sum_range x
    rw [hfun, integral_finsetSum _ hμint]
  have heq2 : ∫ x : ℝ, p.eval x ∂ν
      = ∑ i ∈ Finset.range (p.natDegree + 1), ∫ x : ℝ, p.coeff i * x ^ i ∂ν := by
    have hfun : (fun x : ℝ => p.eval x)
        = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
      ext x
      exact Polynomial.eval_eq_sum_range x
    rw [hfun, integral_finsetSum _ hνint]
  rw [heq1, heq2]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul, hmom i]

/-- Compact moment determinacy on the line: two finite Borel measures supported in a
common compact interval with identical moments coincide. Moments are compared as
Bochner integrals; polynomial integrability follows from the support bound. -/
theorem measure_eq_of_moments_eq_of_supported {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {R : ℝ} (hR : 0 ≤ R)
    (hμsupp : μ (Set.Icc (-R) R)ᶜ = 0) (hνsupp : ν (Set.Icc (-R) R)ᶜ = 0)
    (hmom : ∀ k : ℕ, ∫ x : ℝ, x ^ k ∂μ = ∫ x : ℝ, x ^ k ∂ν) :
    μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hfμ : Integrable (fun x => f x) μ :=
    BoundedContinuousFunction.integrable μ f
  have hfν : Integrable (fun x => f x) ν :=
    BoundedContinuousFunction.integrable ν f
  have hpoly := integral_poly_eq_of_moments_eq hR hμsupp hνsupp hmom
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ ε * (μ.real Set.univ + ν.real Set.univ) := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R (fun x => f x)
      f.continuous.continuousOn ε hε
    have hpeq := hpoly p
    have hμpoly : Integrable (fun x => p.eval x) μ :=
      integrable_poly_of_supported hR hμsupp p
    have hνpoly : Integrable (fun x => p.eval x) ν :=
      integrable_poly_of_supported hR hνsupp p
    have hboundμ : ∀ᵐ x ∂μ, ‖f x - p.eval x‖ ≤ ε := by
      filter_upwards [ae_mem_Icc_of_supported hμsupp] with x hx
      have hlt := hp x hx
      rw [Real.norm_eq_abs]
      have : |f x - p.eval x| = |p.eval x - f x| := abs_sub_comm _ _
      rw [this]
      exact le_of_lt hlt
    have hboundν : ∀ᵐ x ∂ν, ‖f x - p.eval x‖ ≤ ε := by
      filter_upwards [ae_mem_Icc_of_supported hνsupp] with x hx
      have hlt := hp x hx
      rw [Real.norm_eq_abs]
      have : |f x - p.eval x| = |p.eval x - f x| := abs_sub_comm _ _
      rw [this]
      exact le_of_lt hlt
    have hdiffμ : ‖(∫ x, f x ∂μ) - (∫ x, p.eval x ∂μ)‖ ≤ ε * μ.real Set.univ := by
      have hsub : (∫ x, f x ∂μ) - (∫ x, p.eval x ∂μ) = ∫ x, (f x - p.eval x) ∂μ := by
        rw [← integral_sub hfμ hμpoly]
      rw [hsub]
      exact norm_integral_le_of_norm_le_const hboundμ
    have hdiffν : ‖(∫ x, f x ∂ν) - (∫ x, p.eval x ∂ν)‖ ≤ ε * ν.real Set.univ := by
      have hsub : (∫ x, f x ∂ν) - (∫ x, p.eval x ∂ν) = ∫ x, (f x - p.eval x) ∂ν := by
        rw [← integral_sub hfν hνpoly]
      rw [hsub]
      exact norm_integral_le_of_norm_le_const hboundν
    calc ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖
        = ‖((∫ x, f x ∂μ) - (∫ x, p.eval x ∂μ))
          - ((∫ x, f x ∂ν) - (∫ x, p.eval x ∂ν))‖ := by rw [hpeq]; ring_nf
      _ ≤ ‖(∫ x, f x ∂μ) - (∫ x, p.eval x ∂μ)‖
          + ‖(∫ x, f x ∂ν) - (∫ x, p.eval x ∂ν)‖ := norm_sub_le _ _
      _ ≤ ε * μ.real Set.univ + ε * ν.real Set.univ := add_le_add hdiffμ hdiffν
      _ = ε * (μ.real Set.univ + ν.real Set.univ) := by ring
  apply eq_of_forall_dist_le
  intro δ hδ
  have hC_nonneg : 0 ≤ μ.real Set.univ + ν.real Set.univ :=
    add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  by_cases hC0 : μ.real Set.univ + ν.real Set.univ = 0
  · have hbound := key 1 one_pos
    rw [hC0, mul_zero] at hbound
    have hzero : (∫ x, f x ∂μ) - (∫ x, f x ∂ν) = 0 :=
      norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
    have hdist : dist (∫ x, f x ∂μ) (∫ x, f x ∂ν) = 0 := by
      rw [dist_eq_norm, hzero, norm_zero]
    rw [hdist]
    exact le_of_lt hδ
  · have hCpos : 0 < μ.real Set.univ + ν.real Set.univ :=
      lt_of_le_of_ne hC_nonneg (Ne.symm hC0)
    have hεpos : 0 < δ / (μ.real Set.univ + ν.real Set.univ) :=
      div_pos hδ hCpos
    have hbound := key _ hεpos
    have hle : ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ δ := by
      calc ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖
          ≤ (δ / (μ.real Set.univ + ν.real Set.univ))
            * (μ.real Set.univ + ν.real Set.univ) := hbound
        _ = δ := div_mul_cancel₀ δ (ne_of_gt hCpos)
    rwa [dist_eq_norm]

end AndersonAC.LunaBridge
