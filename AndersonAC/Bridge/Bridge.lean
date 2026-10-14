import AndersonAC.Bridge.Determinacy
import AndersonAC.Bridge.MomentDeterminacy
import AndersonAC.Bridge.Characterization
import AndersonAC.Bridge.ProjectionUniqueness
import AndersonAC.Bridge.Operator
import AndersonAC.Bridge.Law
import AndersonAC.Blueprint.Transport
import AndersonAC.Blueprint.Target
import AndersonAC.Challenge

noncomputable section

open MeasureTheory ProbabilityTheory OAI.Anderson
open scoped ENNReal
open AndersonAC.Blueprint AndersonChallenge
open AndersonAC.LunaBridge AndersonAC.MuseBridge

namespace AndersonAC.Blueprint.Packages

/-- The Simon problem implies the independent
Mathlib-only Anderson challenge statement. Uses compact moment determinacy
(phase), operator identification (phase), and iid uniform transport (phase).
No other package hole is used. -/
theorem challengeBridge : SimonProblem → AndersonChallenge.Statement := by
  intro hSimon d hd
  obtain ⟨widthBound, E₁, E₂, hWpos, hE₁₂, hSimonAE⟩ := hSimon d hd
  refine ⟨widthBound, hWpos, ?_⟩
  intro a b hab hwidth
  have hSimon_ab := hSimonAE a b hab hwidth
  refine ⟨intervalCenter a b + E₁, intervalCenter a b + E₂,
    by linarith, ?_⟩
  intro Ω _ _ V hmeas hiid huni
  have hTrans : ∀ᵐ ω ∂(volume : Measure Ω),
      ∃ (M : ℝ) (hM : 0 ≤ M) (hV : ∀ x, |((fun n => V n ω) x)| ≤ M),
        ACRegion (simonHamiltonian (fun n => V n ω) M hM hV)
          (translateWindow (intervalCenter a b) (Set.Ioo E₁ E₂)) :=
    ae_of_intervalLaw_ae (d := d) (a := a) (b := b) hmeas hiid huni hSimon_ab
  have hMem : ∀ᵐ ω ∂(volume : Measure Ω), ∀ n, V n ω ∈ Set.Icc a b :=
    ae_forall_mem_Icc hmeas huni
  filter_upwards [hTrans, hMem] with ω hAC hmem
  obtain ⟨M₁, hM₁, hV₁, hAC₁⟩ := hAC
  have hM₀ : (0 : ℝ) ≤ |a| + |b| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hV₀ : ∀ x, |((fun n => V n ω) x)| ≤ |a| + |b| :=
    fun x => abs_le_of_mem_Icc (hmem x)
  have hEx : ∃ T, IsAndersonOperator (fun n => V n ω) T :=
    ⟨simonHamiltonian _ _ hM₀ hV₀,
      simonHamiltonian_isAndersonOperator _ _ hM₀ hV₀⟩
  refine ⟨hEx, ?_⟩
  intro T hT
  have hT₁ : T = simonHamiltonian (fun n => V n ω) M₁ hM₁ hV₁ :=
    isAndersonOperator_eq_simonHamiltonian _ _ hM₁ hV₁ hT
  have hAC_T : ACRegion T (translateWindow (intervalCenter a b) (Set.Ioo E₁ E₂)) := by
    rw [hT₁]
    exact hAC₁
  have hWin : translateWindow (intervalCenter a b) (Set.Ioo E₁ E₂)
      = Set.Ioo (intervalCenter a b + E₁) (intervalCenter a b + E₂) :=
    translateWindow_Ioo _ _ _
  rw [hWin] at hAC_T
  obtain ⟨hσ, S, hRange, hNe⟩ := hAC_T
  have hMeas : MeasurableSet (Set.Ioo (intervalCenter a b + E₁) (intervalCenter a b + E₂)) :=
    measurableSet_Ioo
  have hPure : S.purelyACOn (Set.Ioo (intervalCenter a b + E₁) (intervalCenter a b + E₂)) :=
    (S.range_subset_acVectors_iff hMeas).mp hRange
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    exact hσ hE
  · intro v μ hμ
    have hEq : μ = S.vectorMeasure v := spectralMeasure_eq_vectorMeasure S v hμ
    rw [hEq]
    exact hPure v
  · have hNe' : S.projection (Set.Ioo (intervalCenter a b + E₁) (intervalCenter a b + E₂)) ≠ 0 :=
      hNe
    have hex : ∃ v₀, S.projection (Set.Ioo (intervalCenter a b + E₁) (intervalCenter a b + E₂)) v₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hNe'
      apply ContinuousLinearMap.ext
      intro v₀
      exact hcon v₀
    obtain ⟨v₀, hv₀⟩ := hex
    refine ⟨v₀, ⟨_, vectorMeasure_isSpectralMeasure S v₀⟩, ?_⟩
    intro μ hμ
    have hEq : μ = S.vectorMeasure v₀ := spectralMeasure_eq_vectorMeasure S v₀ hμ
    rw [hEq, S.vectorMeasure_apply v₀ _ hMeas]
    have hpos : (0 : ℝ) < ‖S.projection (Set.Ioo (intervalCenter a b + E₁) (intervalCenter a b + E₂)) v₀‖ :=
      norm_pos_iff.mpr hv₀
    have hsqpos : (0 : ℝ) < ‖S.projection (Set.Ioo (intervalCenter a b + E₁) (intervalCenter a b + E₂)) v₀‖ ^ 2 :=
      pow_pos hpos 2
    exact ENNReal.ofReal_ne_zero_iff.mpr hsqpos


end AndersonAC.Blueprint.Packages
