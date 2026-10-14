import AndersonAC.AgentS6.Decomposition

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
/-- Centering costs factors two and four in the jump and square envelopes. -/
theorem vector_tail_of_increment_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (c : ℝ) (hconc : VectorConcentrationInput μ F c)
    (D N : ℕ) (X : ℕ → Ω → EuclideanSpace ℂ (Fin D)) (B : ℕ → Ω → ℝ)
    (J V a : ℝ) (hJ : 0 < J) (hV : 0 < V) (ha : 0 < a)
    (hXm : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (hBm : ∀ k, StronglyMeasurable[F k] (B k))
    (hB0 : ∀ k ω, 0 ≤ B k ω) (hBJ : ∀ k ω, B k ω ≤ J)
    (hXB : ∀ k ω, ‖X k ω‖ ≤ B k ω)
    (hBV : ∀ ω, ∑ k ∈ Finset.range N, (B k ω) ^ 2 ≤ V)
    (hbias : ∀ᵐ ω ∂μ, ∀ m ≤ N,
      ‖∑ k ∈ Finset.range m, μ[X k | F k] ω‖ ≤ a / 2) :
    ∀ᵐ ω ∂μ,
      conditionalProbability μ (F 0)
        {ω | ∃ m ≤ N, a < ‖∑ k ∈ Finset.range m, X k ω‖} ω ≤
      2 * (D + 1) * Real.exp (-c * min ((a / 2) ^ 2 / (4 * V)) ((a / 2) / (2 * J))) := by
  let M : ℕ → Ω → EuclideanSpace ℂ (Fin D) := fun k => μ[X k | F k]
  let Y : ℕ → Ω → EuclideanSpace ℂ (Fin D) := fun k ω => X k ω - M k ω
  have hXI : ∀ k, Integrable (X k) μ := fun k =>
    (integrable_const J).mono' ((hXm k).mono (F.le _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => (hXB k ω).trans (hBJ k ω))
  have hBI : ∀ k, Integrable (B k) μ := fun k =>
    (integrable_const J).mono' ((hBm k).mono (F.le _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hB0 k ω)]; exact hBJ k ω)
  have hB2I : ∀ k, Integrable (fun ω => (B k ω) ^ 2) μ := fun k =>
    (integrable_const (J ^ 2)).mono'
      (((hBm k).mono (F.le _)).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hB0 k ω) (hBJ k ω) 2)
  have hMm : ∀ k, StronglyMeasurable[F k] (M k) := fun _ => stronglyMeasurable_condExp
  have hMI : ∀ k, Integrable (M k) μ := fun _ => integrable_condExp
  have hMB : ∀ k, ∀ᵐ ω ∂μ, ‖M k ω‖ ≤ B k ω := by
    intro k
    have hn := norm_condExp_le (μ := μ) (m := F k) (X k)
    have hmono := condExp_mono (m := F k) (hXI k).norm (hBI k)
      (Filter.Eventually.of_forall (hXB k))
    rw [condExp_of_stronglyMeasurable (F.le k) (hBm k) (hBI k)] at hmono
    filter_upwards [hn, hmono] with ω hn hm
    exact hn.trans hm
  have hYI : ∀ k, Integrable (Y k) μ := fun k => (hXI k).sub (hMI k)
  have hYm : ∀ k, StronglyMeasurable[F (k + 1)] (Y k) := fun k =>
    (hXm k).sub ((hMm k).mono (F.mono (by omega)))
  have hYB : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ 2 * B k ω := by
    intro k
    filter_upwards [hMB k] with ω hm
    exact (norm_sub_le _ _).trans (by linarith [hXB k ω])
  have hY2I : ∀ k, Integrable (fun ω => ‖Y k ω‖ ^ 2) μ := by
    intro k
    apply (integrable_const ((2 * J) ^ 2)).mono'
      ((((hYm k).mono (F.le _)).norm).pow 2).aestronglyMeasurable
    filter_upwards [hYB k] with ω hb
    change ‖‖Y k ω‖ ^ 2‖ ≤ (2 * J) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb.trans (by gcongr; exact hBJ k ω)) 2
  have hYzero : ∀ k, μ[Y k | F k] =ᵐ[μ] 0 := by
    intro k
    have h := condExp_sub (hXI k) (hMI k) (F k)
    rw [condExp_of_stronglyMeasurable (F.le k) (hMm k) (hMI k)] at h
    have h' : μ[Y k | F k] =ᵐ[μ] μ[X k | F k] - M k := by
      change μ[X k - M k | F k] =ᵐ[μ] μ[X k | F k] - M k
      exact h
    filter_upwards [h'] with ω hω
    simpa only [Pi.sub_apply, M, sub_self, Pi.zero_apply] using hω
  have hYvar : ∀ k, ∀ᵐ ω ∂μ,
      μ[(fun ω => ‖Y k ω‖ ^ 2) | F k] ω ≤ 4 * (B k ω) ^ 2 := by
    intro k
    have hbound : (fun ω => ‖Y k ω‖ ^ 2) ≤ᵐ[μ] fun ω => 4 * (B k ω) ^ 2 := by
      filter_upwards [hYB k] with ω hb
      calc ‖Y k ω‖ ^ 2 ≤ (2 * B k ω) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = _ := by ring
    have hi : Integrable (fun ω => 4 * (B k ω) ^ 2) μ := (hB2I k).const_mul 4
    have hm : StronglyMeasurable[F k] (fun ω => 4 * (B k ω) ^ 2) :=
      stronglyMeasurable_const.mul ((hBm k).pow 2)
    have h := condExp_mono (m := F k) (hY2I k) hi hbound
    rwa [condExp_of_stronglyMeasurable (F.le k) hm hi] at h
  have htail := hconc D N Y (fun k ω => 4 * (B k ω) ^ 2)
    (2 * J) (4 * V) (a / 2) (by positivity) (by positivity) (by positivity)
    hYm hYI hYzero
    (fun k => stronglyMeasurable_const.mul ((hBm k).pow 2))
    (fun k ω => by positivity)
    (fun k => (hYB k).mono fun ω hb => hb.trans (by gcongr; exact hBJ k ω)) hYvar
    (Filter.Eventually.of_forall fun ω => by rw [← Finset.mul_sum]; nlinarith [hBV ω])
  let E : Set Ω := {ω | ∃ m ≤ N, a < ‖∑ k ∈ Finset.range m, X k ω‖}
  let G : Set Ω := {ω | ∃ m ≤ N, a / 2 < ‖∑ k ∈ Finset.range m, Y k ω‖}
  have hEm : MeasurableSet E := by
    have heq : E = ⋃ m : ℕ, ⋃ (_ : m ≤ N),
        {ω | a < ‖∑ k ∈ Finset.range m, X k ω‖} := by
      ext ω
      simp [E]
    rw [heq]
    apply MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => ?_
    have hm : StronglyMeasurable (fun ω => ∑ k ∈ Finset.range m, X k ω) := by
      have he : (fun ω => ∑ k ∈ Finset.range m, X k ω) = ∑ k ∈ Finset.range m, X k := by
        funext ω
        simp
      rw [he]
      exact Finset.stronglyMeasurable_sum _ (fun k _ => (hXm k).mono (F.le _))
    exact measurableSet_lt measurable_const hm.norm.measurable
  have hGm : MeasurableSet G := by
    have heq : G = ⋃ m : ℕ, ⋃ (_ : m ≤ N),
        {ω | a / 2 < ‖∑ k ∈ Finset.range m, Y k ω‖} := by
      ext ω
      simp [G]
    rw [heq]
    apply MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => ?_
    have hm : StronglyMeasurable (fun ω => ∑ k ∈ Finset.range m, Y k ω) := by
      have he : (fun ω => ∑ k ∈ Finset.range m, Y k ω) = ∑ k ∈ Finset.range m, Y k := by
        funext ω
        simp
      rw [he]
      exact Finset.stronglyMeasurable_sum _ (fun k _ => (hYm k).mono (F.le _))
    exact measurableSet_lt measurable_const hm.norm.measurable
  have hcover : E.indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ] G.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hbias] with ω hb
    by_cases he : ω ∈ E
    · obtain ⟨m, hm, hx⟩ := he
      have hEω : ω ∈ E := ⟨m, hm, hx⟩
      have hsum : ∑ k ∈ Finset.range m, X k ω =
          (∑ k ∈ Finset.range m, Y k ω) + ∑ k ∈ Finset.range m, M k ω := by
        simp [Y, Finset.sum_sub_distrib]
      have hnorm := norm_add_le (∑ k ∈ Finset.range m, Y k ω)
        (∑ k ∈ Finset.range m, M k ω)
      have hy : a / 2 < ‖∑ k ∈ Finset.range m, Y k ω‖ := by
        rw [hsum] at hx
        have hb' := hb m hm
        change ‖∑ k ∈ Finset.range m, M k ω‖ ≤ a / 2 at hb'
        linarith
      simp only [Set.indicator_of_mem hEω, Set.indicator_of_mem (show ω ∈ G from ⟨m, hm, hy⟩)]
      exact le_rfl
    · rw [Set.indicator_of_notMem he]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hp := condExp_mono (m := F 0) ((integrable_const (1 : ℝ)).indicator hEm)
    ((integrable_const (1 : ℝ)).indicator hGm) hcover
  filter_upwards [hp, htail] with ω hp ht
  exact hp.trans ht

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.vector_tail_of_increment_bounds
