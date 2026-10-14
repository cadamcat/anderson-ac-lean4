import AndersonAC.AgentS6Budget.VectorTail

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A bounded scalar query multiplying a predictable vector. The total predictable norms
control the bias, and the total squared norms control the variance envelope. -/
theorem scalar_vector_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (c : ℝ) (hconc : VectorConcentrationInput μ F c)
    (D N : ℕ) (A : ℕ → Ω → ℂ) (U : ℕ → Ω → EuclideanSpace ℂ (Fin D))
    (L M R S H a : ℝ) (hL : 0 < L) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hS : 0 < S) (hH : 0 < H) (ha : 0 < a)
    (hAm : ∀ k, StronglyMeasurable[F (k + 1)] (A k))
    (hUm : ∀ k, StronglyMeasurable[F k] (U k))
    (hAL : ∀ k ω, ‖A k ω‖ ≤ L) (hUH : ∀ k ω, ‖U k ω‖ ≤ H)
    (hAM : ∀ k, ∀ᵐ ω ∂μ, ‖μ[A k | F k] ω‖ ≤ M)
    (hUR : ∀ ω, ∑ k ∈ Finset.range N, ‖U k ω‖ ≤ R)
    (hUS : ∀ ω, ∑ k ∈ Finset.range N, ‖U k ω‖ ^ 2 ≤ S)
    (hbias : M * R ≤ a / 2) :
    ∀ᵐ ω ∂μ,
      conditionalProbability μ (F 0)
        {ω | ∃ m ≤ N, a < ‖∑ k ∈ Finset.range m, A k ω • U k ω‖} ω ≤
      2 * (D + 1) * Real.exp
        (-c * min ((a / 2) ^ 2 / (4 * (L ^ 2 * S))) ((a / 2) / (2 * (L * H)))) := by
  let X : ℕ → Ω → EuclideanSpace ℂ (Fin D) := fun k ω => A k ω • U k ω
  have hAI : ∀ k, Integrable (A k) μ := fun k =>
    (integrable_const L).mono' ((hAm k).mono (F.le _)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hAL k))
  have hXI : ∀ k, Integrable (X k) μ := fun k =>
    (integrable_const (L * H)).mono'
      (((hAm k).mono (F.le _)).smul ((hUm k).mono (F.le _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        dsimp [X]
        rw [norm_smul]
        exact mul_le_mul (hAL k ω) (hUH k ω) (norm_nonneg _) hL.le)
  have hpull : ∀ k, μ[X k | F k] =ᵐ[μ] fun ω => μ[A k | F k] ω • U k ω := by
    intro k
    exact condExp_bilin_of_stronglyMeasurable_right (ContinuousLinearMap.lsmul ℝ ℂ)
      (hUm k) (hXI k) (hAI k)
  have hmean : ∀ k, ∀ᵐ ω ∂μ, ‖μ[X k | F k] ω‖ ≤ M * ‖U k ω‖ := by
    intro k
    filter_upwards [hpull k, hAM k] with ω hp hm
    rw [hp, norm_smul]
    exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
  have hmean_all : ∀ᵐ ω ∂μ, ∀ k, ‖μ[X k | F k] ω‖ ≤ M * ‖U k ω‖ :=
    ae_all_iff.mpr hmean
  apply vector_tail_of_increment_bounds μ F c hconc D N X (fun k ω => L * ‖U k ω‖)
    (L * H) (L ^ 2 * S) a (by positivity) (by positivity) ha
    (fun k => (hAm k).smul ((hUm k).mono (F.mono (by omega))))
    (fun k => stronglyMeasurable_const.mul (hUm k).norm)
    (fun k ω => mul_nonneg hL.le (norm_nonneg _))
    (fun k ω => mul_le_mul_of_nonneg_left (hUH k ω) hL.le)
    (fun k ω => by
      dsimp [X]
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hAL k ω) (norm_nonneg _))
    (fun ω => by
      simp only [mul_pow, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hUS ω) (sq_nonneg L))
  filter_upwards [hmean_all] with ω hm
  intro m hmn
  calc
    ‖∑ k ∈ Finset.range m, μ[X k | F k] ω‖
        ≤ ∑ k ∈ Finset.range m, ‖μ[X k | F k] ω‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, M * ‖U k ω‖ := Finset.sum_le_sum fun k _ => hm k
    _ = M * ∑ k ∈ Finset.range m, ‖U k ω‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ M * R := mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
        (fun k _ _ => norm_nonneg _)).trans (hUR ω)) hM
    _ ≤ a / 2 := hbias

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.scalar_vector_tail
