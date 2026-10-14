import AndersonAC.S6.Statements

set_option maxHeartbeats 1000000

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace AndersonAC.AgentS6Stream

private def streamEmbedding : ℝ →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  (PiLp.equivOfUnique (p := 2) ℝ (fun _ : Fin 1 => ℂ)).symm.toContinuousLinearMap.comp
    Complex.ofRealCLM

private theorem streamEmbedding_apply (x : ℝ) :
    streamEmbedding x = EuclideanSpace.single 0 (x : ℂ) := by
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [streamEmbedding]

private theorem streamEmbedding_norm (x : ℝ) : ‖streamEmbedding x‖ = |x| := by
  rw [streamEmbedding_apply]
  simp [EuclideanSpace.single, PiLp.norm_single]

end AndersonAC.AgentS6Stream

namespace AndersonAC.S6

theorem two_sided_stream_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (c l J V : ℝ) (N : ℕ)
    (Z v : ℕ → Ω → ℝ) (hl : 0 < l) (hJ : 0 < J) (hV : 0 < V)
    (hconc : VectorConcentrationInput μ F c)
    (hadapted : ∀ k, StronglyMeasurable[F (k + 1)] (Z k))
    (hint : ∀ k, Integrable (Z k) μ)
    (hbias : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range N, |μ[Z k | F k] ω| ≤ l / 4)
    (hv : ∀ k, StronglyMeasurable[F k] (v k)) (hvpos : ∀ k ω, 0 ≤ v k ω)
    (hjump : ∀ k, ∀ᵐ ω ∂μ, |Z k ω - μ[Z k | F k] ω| ≤ J)
    (hvar : ∀ k, ∀ᵐ ω ∂μ,
      μ[(fun ω => (Z k ω - μ[Z k | F k] ω) ^ 2) | F k] ω ≤ v k ω)
    (hbudget : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range N, v k ω ≤ V) :
    Planned.two_sided_stream_tail μ F c l J V N Z v hl hJ hV hconc hadapted hint hbias
      hv hvpos hjump hvar hbudget := by
  let Y : ℕ → Ω → EuclideanSpace ℂ (Fin 1) := fun k ω =>
    AndersonAC.AgentS6Stream.streamEmbedding (Z k ω - μ[Z k | F k] ω)
  let A : Set Ω := {ω | ∃ n ≤ N, l / 2 < |∑ k ∈ Finset.range n, Z k ω|}
  let G : Set Ω := {ω | ∃ n ≤ N,
    l / 4 < ‖∑ k ∈ Finset.range n, Y k ω‖}

  have hZsm : ∀ k, StronglyMeasurable (Z k) := by
    intro k
    exact (hadapted k).mono (F.le (k + 1))

  have hYsm : ∀ k, StronglyMeasurable[F (k + 1)] (Y k) := by
    intro k
    have hcond : StronglyMeasurable[F k] (μ[Z k | F k]) := stronglyMeasurable_condExp
    have hcond' : StronglyMeasurable[F (k + 1)] (μ[Z k | F k]) :=
      hcond.mono (F.mono (Nat.le_succ k))
    have hdiff : StronglyMeasurable[F (k + 1)]
        (fun ω => Z k ω - μ[Z k | F k] ω) := (hadapted k).sub hcond'
    exact AndersonAC.AgentS6Stream.streamEmbedding.continuous.comp_stronglyMeasurable hdiff

  have hYint : ∀ k, Integrable (Y k) μ := by
    intro k
    have hdiff : Integrable (fun ω => Z k ω - μ[Z k | F k] ω) μ :=
      (hint k).sub integrable_condExp
    exact AndersonAC.AgentS6Stream.streamEmbedding.integrable_comp hdiff

  have hYmean : ∀ k, μ[Y k | F k] =ᵐ[μ] 0 := by
    intro k
    have hcondInt : Integrable (μ[Z k | F k]) μ := integrable_condExp
    have hsub := condExp_sub (hint k) hcondInt (F k)
    have hself := condExp_of_stronglyMeasurable (F.le k) stronglyMeasurable_condExp hcondInt
    have hzero :
        μ[(fun ω => Z k ω - μ[Z k | F k] ω) | F k] =ᵐ[μ] 0 := by
      change μ[Z k - μ[Z k | F k] | F k] =ᵐ[μ] 0
      rw [hself] at hsub
      simpa using hsub
    have hdiffInt : Integrable (fun ω => Z k ω - μ[Z k | F k] ω) μ :=
      (hint k).sub hcondInt
    have hcomm :=
      AndersonAC.AgentS6Stream.streamEmbedding.comp_condExp_comm (m := F k) hdiffInt
    have hcomm' : μ[Y k | F k] =ᵐ[μ]
        (fun ω => AndersonAC.AgentS6Stream.streamEmbedding
          (μ[(fun ω => Z k ω - μ[Z k | F k] ω) | F k] ω)) := by
      filter_upwards [hcomm.symm] with ω hω
      change μ[(fun x => AndersonAC.AgentS6Stream.streamEmbedding
          (Z k x - μ[Z k | F k] x)) | F k] ω =
        AndersonAC.AgentS6Stream.streamEmbedding
          (μ[(fun x => Z k x - μ[Z k | F k] x) | F k] ω)
      exact hω
    filter_upwards [hzero, hcomm'] with ω hzeroω hcommω
    calc
      μ[Y k | F k] ω =
          AndersonAC.AgentS6Stream.streamEmbedding
            (μ[(fun ω => Z k ω - μ[Z k | F k] ω) | F k] ω) := hcommω
      _ = 0 := by rw [hzeroω]; simp

  have hYjump : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ J := by
    intro k
    filter_upwards [hjump k] with ω hω
    simpa only [Y, AndersonAC.AgentS6Stream.streamEmbedding_norm] using hω

  have hYvar : ∀ k, ∀ᵐ ω ∂μ,
      μ[(fun ω => ‖Y k ω‖ ^ 2) | F k] ω ≤ v k ω := by
    intro k
    have hfun : (fun ω => ‖Y k ω‖ ^ 2) =
        (fun ω => (Z k ω - μ[Z k | F k] ω) ^ 2) := by
      funext ω
      simp only [Y, AndersonAC.AgentS6Stream.streamEmbedding_norm, sq_abs]
    rw [hfun]
    exact hvar k

  have ha : 0 < l / 4 := by linarith
  have htail := hconc 1 N Y v J V (l / 4) hJ hV ha hYsm hYint hYmean hv hvpos hYjump
    hYvar hbudget
  have hscale₁ : (l / 4) ^ 2 / V = l ^ 2 / (16 * V) := by
    field_simp
    <;> ring
  have hscale₂ : (l / 4) / J = l / (4 * J) := by
    field_simp
  have htail' : ∀ᵐ ω ∂μ,
      conditionalProbability μ (F 0) G ω ≤
        4 * Real.exp (-c * min (l ^ 2 / (16 * V)) (l / (4 * J))) := by
    filter_upwards [htail] with ω hω
    have hω' : conditionalProbability μ (F 0) G ω ≤
        2 * (1 + 1) * Real.exp (-c * min ((l / 4) ^ 2 / V) ((l / 4) / J)) := by
      simpa [conditionalProbability, G] using hω
    calc
      conditionalProbability μ (F 0) G ω ≤
          2 * (1 + 1) * Real.exp (-c * min ((l / 4) ^ 2 / V) ((l / 4) / J)) := hω'
      _ = 4 * Real.exp (-c * min (l ^ 2 / (16 * V)) (l / (4 * J))) := by
        rw [hscale₁, hscale₂]
        norm_num

  have hGsm : ∀ k, StronglyMeasurable (Y k) := by
    intro k
    exact (hYsm k).mono (F.le (k + 1))

  have hAeq : A = ⋃ n : Fin (N + 1),
      {ω | l / 2 < |∑ k ∈ Finset.range n.val, Z k ω|} := by
    ext ω
    simp only [A, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn, hω⟩
      exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, hω⟩
    · rintro ⟨n, hω⟩
      exact ⟨n.val, Nat.le_of_lt_succ n.isLt, hω⟩

  have hAmeas : MeasurableSet A := by
    rw [hAeq]
    apply MeasurableSet.iUnion
    intro n
    have hsum : StronglyMeasurable
        (fun ω => ∑ k ∈ Finset.range n.val, Z k ω) :=
      Finset.stronglyMeasurable_fun_sum _ (fun k hk => hZsm k)
    exact measurableSet_Ioi.preimage (measurable_abs.comp hsum.measurable)

  have hGeq : G = ⋃ n : Fin (N + 1),
      {ω | l / 4 < ‖∑ k ∈ Finset.range n.val, Y k ω‖} := by
    ext ω
    simp only [G, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn, hω⟩
      exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, hω⟩
    · rintro ⟨n, hω⟩
      exact ⟨n.val, Nat.le_of_lt_succ n.isLt, hω⟩

  have hGmeas : MeasurableSet G := by
    rw [hGeq]
    apply MeasurableSet.iUnion
    intro n
    have hsum : StronglyMeasurable
        (fun ω => ∑ k ∈ Finset.range n.val, Y k ω) :=
      Finset.stronglyMeasurable_fun_sum _ (fun k hk => hGsm k)
    exact measurableSet_Ioi.preimage (continuous_norm.measurable.comp hsum.measurable)

  have hsumY_norm (n : ℕ) (ω : Ω) :
      ‖∑ k ∈ Finset.range n, Y k ω‖ =
        |∑ k ∈ Finset.range n, (Z k ω - μ[Z k | F k] ω)| := by
    have hsum : (∑ k ∈ Finset.range n, Y k ω) =
        AndersonAC.AgentS6Stream.streamEmbedding
          (∑ k ∈ Finset.range n, (Z k ω - μ[Z k | F k] ω)) := by
      simp [Y, map_sum]
    rw [hsum, AndersonAC.AgentS6Stream.streamEmbedding_norm]

  have hA_indicator_le :
      A.indicator (fun _ : Ω => (1 : ℝ)) ≤ᵐ[μ]
        G.indicator (fun _ : Ω => (1 : ℝ)) := by
    filter_upwards [hbias] with ω hb
    by_cases hmemb : ω ∈ A
    · have hmemb' := hmemb
      rcases hmemb with ⟨n, hn, hZ⟩
      have hsmall :
          ∑ k ∈ Finset.range n, |μ[Z k | F k] ω| ≤ l / 4 := by
        calc
          ∑ k ∈ Finset.range n, |μ[Z k | F k] ω| ≤
              ∑ k ∈ Finset.range N, |μ[Z k | F k] ω| :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
                  (fun _ _ _ => abs_nonneg _)
          _ ≤ l / 4 := hb
      have hbiasAbs :
          |∑ k ∈ Finset.range n, μ[Z k | F k] ω| ≤ l / 4 := by
        calc
          |∑ k ∈ Finset.range n, μ[Z k | F k] ω| ≤
              ∑ k ∈ Finset.range n, |μ[Z k | F k] ω| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ l / 4 := hsmall
      have hsum :
          (∑ k ∈ Finset.range n, Z k ω) =
            (∑ k ∈ Finset.range n, (Z k ω - μ[Z k | F k] ω)) +
              ∑ k ∈ Finset.range n, μ[Z k | F k] ω := by
        rw [Finset.sum_sub_distrib]
        ring
      have hcenter :
          l / 4 < |∑ k ∈ Finset.range n, (Z k ω - μ[Z k | F k] ω)| := by
        have htriangle :
            |∑ k ∈ Finset.range n, Z k ω| ≤
              |∑ k ∈ Finset.range n, (Z k ω - μ[Z k | F k] ω)| +
                |∑ k ∈ Finset.range n, μ[Z k | F k] ω| := by
          rw [hsum]
          exact abs_add_le _ _
        linarith
      have hG : ω ∈ G := by
        refine ⟨n, hn, ?_⟩
        rw [hsumY_norm n ω]
        exact hcenter
      simp [Set.indicator, hmemb', hG]
    · simp only [Set.indicator, hmemb]
      by_cases hG : ω ∈ G
      · simp [hG]
      · simp [hG]

  have hAint : Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hAmeas
  have hGint : Integrable (G.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hGmeas
  have hcondMono := condExp_mono (m := F 0) hAint hGint hA_indicator_le
  filter_upwards [hcondMono, htail'] with ω hmono htailω
  have hfinal := hmono.trans htailω
  simpa [conditionalProbability, A] using hfinal

end AndersonAC.S6

end
