import AndersonAC.AgentS6.Decomposition

/-! Conditional probability bookkeeping for the finite union of coordinate tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6Budget

variable {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]

/-- Conditional probability is subadditive over a finite family of measurable events. -/
theorem condProb_iUnion_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (k : ℕ) (E : α → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) :
    ∀ᵐ ω ∂μ,
      @AndersonAC.S6.conditionalProbability Ω mΩ μ (F k) (⋃ i, E i) ω ≤
        ∑ i, @AndersonAC.S6.conditionalProbability Ω mΩ μ (F k) (E i) ω := by
  classical
  let U : Set Ω := ⋃ i, E i
  have hU : MeasurableSet U := MeasurableSet.iUnion hE
  have hI : ∀ i, Integrable ((E i).indicator (fun _ => (1 : ℝ))) μ := by
    intro i
    exact (integrable_const (1 : ℝ)).indicator (hE i)
  have hUI : Integrable (U.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hU
  have hsumI : Integrable (fun ω => ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω) μ := by
    simpa using (integrable_finsetSum Finset.univ (fun i _ => hI i))
  have hpoint : U.indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ]
      fun ω => ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω := by
    refine Filter.Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ U
    · have hmem : ∃ i, ω ∈ E i := by simpa [U] using hω
      obtain ⟨i, hi⟩ := hmem
      have hterm : (E i).indicator (fun _ => (1 : ℝ)) ω = 1 :=
        Set.indicator_of_mem hi (fun _ => (1 : ℝ))
      rw [Set.indicator_of_mem hω]
      change (1 : ℝ) ≤ ∑ j, (E j).indicator (fun _ => (1 : ℝ)) ω
      calc
        1 = (E i).indicator (fun _ => (1 : ℝ)) ω := hterm.symm
        _ ≤ ∑ j, (E j).indicator (fun _ => (1 : ℝ)) ω :=
          Finset.single_le_sum
            (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one)
              (s := E j) (f := fun _ => (1 : ℝ)) ω) (Finset.mem_univ i)
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one)
        (s := E i) (f := fun _ => (1 : ℝ)) ω
  have hmono := condExp_mono (m := F k) hUI hsumI hpoint
  have hsum :
      μ[(fun ω => ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω) | F k] =ᵐ[μ]
        fun ω => ∑ i, μ[(E i).indicator (fun _ => (1 : ℝ)) | F k] ω := by
    have hleft : (fun ω => ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω) =
        ∑ i, (E i).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simp
    have hright : (fun ω => ∑ i, μ[(E i).indicator (fun _ => (1 : ℝ)) | F k] ω) =
        ∑ i, μ[(E i).indicator (fun _ => (1 : ℝ)) | F k] := by
      funext ω
      simp
    rw [hleft, hright]
    have h := condExp_finsetSum (s := Finset.univ)
      (f := fun i ω => (E i).indicator (fun _ => (1 : ℝ)) ω) (fun i _ => hI i) (F k)
    simpa using h
  filter_upwards [hmono, hsum] with ω hω hsumω
  change μ[U.indicator (fun _ => (1 : ℝ)) | (F k)] ω ≤
    ∑ i, μ[(E i).indicator (fun _ => (1 : ℝ)) | F k] ω
  rw [hsumω] at hω
  exact hω

end AndersonAC.AgentS6Budget
