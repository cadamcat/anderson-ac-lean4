import AndersonAC.S6.UniformModes

/-! Proposition 6.6 with the scale threshold chosen before the probability space and measure,
composed from the three uniform failure-mode tails exactly as `S6.preparation_of_modes`
(AgentS6/Decomposition.lean) composes the non-uniform ones. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace AndersonAC.S6

open AndersonAC.AgentS6

/-- Proposition 6.6, uniform in the probability space, with both conclusions. -/
theorem preparationUniformFull_proof : PreparationUniformFullStatement := by
  intro d hd c K Cloc cConc hc hK hCloc hConc qlag ε hqlag hε hεpos
  have hWard : AndersonAC.Blueprint.WardInput := AndersonAC.Blueprint.Packages.ward
  obtain ⟨t1, ht1, h1⟩ :=
    countTailUniform_proof d hd c K Cloc cConc qlag ε hε hεpos hWard
  obtain ⟨t2, ht2, h2⟩ :=
    budgetTailUniform_proof d hd c K Cloc cConc hc hK hCloc hConc qlag ε hqlag hWard
  obtain ⟨t3, ht3, h3⟩ :=
    capTailUniform_proof d hd c K Cloc cConc hc hK hCloc hConc qlag ε hqlag hWard
  refine ⟨clearingExponent_pos d hd, min t1 (min t2 t3), lt_min ht1 (lt_min ht2 ht3), ?_⟩
  intro Ω _ μ _ n core t r g0 order q dist collapsed ell ht htt hcore1 hcore hb hfourth hlag
    hloc hconc hdrift
  have hyp : PrepHyp d c K Cloc cConc μ qlag ε core t r g0 order q dist collapsed ell :=
    ⟨ht, hcore1, hcore, hb, hfourth, hlag, hloc, hconc, hdrift⟩
  have htt1 : t < t1 := lt_of_lt_of_le htt (min_le_left _ _)
  have htt2 : t < t2 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt3 : t < t3 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨G1, hG1, hm1, hp1⟩ := h1 μ n core t r g0 order q dist collapsed ell htt1 hyp
  obtain ⟨G2, hG2, hm2, hp2⟩ := h2 μ n core t r g0 order q dist collapsed ell htt2 hyp
  obtain ⟨G3, hG3, hm3, hp3⟩ := h3 μ n core t r g0 order q dist collapsed ell htt3 hyp
  refine ⟨?_, ?_⟩
  · have hA : MeasurableSet {ω | q.outcome ω = .fail} :=
      q.outcome_measurable (MeasurableSpace.measurableSet_top (s := {TrialOutcome.fail}))
    have hcover : {ω | q.outcome ω = .fail} ⊆ G1 ∪ G2 ∪ G3 := by
      intro ω hω
      rcases q.fail_reason ω hω with h | h | h
      · exact Or.inl (Or.inl (hm1 ω h))
      · exact Or.inl (Or.inr (hm2 ω h))
      · exact Or.inr (hm3 ω h)
    filter_upwards [condProb_le_three μ q.history 0 hG1 hG2 hG3 hA hcover, hp1, hp2, hp3]
      with ω h h1 h2 h3
    linarith
  · intro ω hdone
    obtain ⟨hs, hbud, hproj⟩ := (q.done_iff ω).mp hdone
    exact ⟨hs, hbud, hproj, removed_card q ω⟩

/-- Proposition 6.6 in the consumer's uniform form (`AgentS78.PreparationUniformStatement`). -/
theorem preparationUniform_proof : PreparationUniformStatement := by
  intro d hd c K Cloc cConc hc hK hCloc hConc qlag ε hqlag hε hεpos
  obtain ⟨-, t0, ht0, h⟩ :=
    preparationUniformFull_proof d hd c K Cloc cConc hc hK hCloc hConc qlag ε hqlag hε hεpos
  refine ⟨t0, ht0, ?_⟩
  intro Ω _ μ _ n core t r g0 order q dist collapsed ell ht htt hcore1 hcore hb hfourth hlag
    hloc hconc hdrift
  exact (h μ n core t r g0 order q dist collapsed ell ht htt hcore1 hcore hb hfourth hlag hloc
    hconc hdrift).1

/-- Sanity check: the uniform form implies the planned (non-uniform) Proposition 6.6. -/
theorem preparation_of_small_component_of_uniform {Ω : Type} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    Planned.preparation_of_small_component d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε
      hqlag hε hεpos := by
  obtain ⟨hκ, t0, ht0, h⟩ :=
    preparationUniformFull_proof d hd c K Cloc cConc hc hK hCloc hConc qlag ε hqlag hε hεpos
  exact ⟨hκ, t0, ht0, fun n core t r g0 order q dist collapsed ell => h μ n core t r g0 order q
    dist collapsed ell⟩

end AndersonAC.S6

#print axioms AndersonAC.S6.preparationUniformFull_proof
#print axioms AndersonAC.S6.preparationUniform_proof
#print axioms AndersonAC.S6.preparation_of_small_component_of_uniform
