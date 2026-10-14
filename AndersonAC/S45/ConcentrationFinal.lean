import AndersonAC.S45.OneTrialProof
import AndersonAC.S45.TraceHelpersProof

/-! Lemma 5.6 and its consumers from the deterministic trace facts and
Golden–Thompson. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

/-- Builds `ConcentrationInput` from `OpusS45.GTStatement` and the trace helpers. -/
theorem concentration_of_gt (hGT : AndersonAC.OpusS45.GTStatement) :
    AndersonAC.Blueprint.ConcentrationInput :=
  AndersonAC.OpusS45.concentrationInput_of hGT AndersonAC.OpusS45.traceHelpers_proof

theorem matrix_concentration_proof (hGT : GoldenThompson) :
    ∃ c > 0, ∀ (n Ω : Type) [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : ℕ → Ω → CMat n) (v : ℕ → Ω → ℝ) (J V a : ℝ),
    0 < J → 0 < V → 0 < a → MatrixDiffHyp μ ℱ Y v J V →
    μ {ω | ∃ N : ℕ, a < ‖partialSum Y N ω‖} ≤
      ENNReal.ofReal (2 * (Fintype.card n : ℝ) *
        Real.exp (-c * min (a^2 / V) (a / J))) :=
  matrix_concentration_of AndersonAC.OpusS45.traceHelpers_proof hGT

theorem concentrationInput_proof (hGT : GoldenThompson) : ConcentrationInput :=
  concentrationInput_of AndersonAC.OpusS45.traceHelpers_proof hGT

theorem one_trial_proof (hGT : GoldenThompson) : ∀ (d : ℕ) (C : ℝ), 1 ≤ C →
    ∃ c > 0, ∃ t0 > 0, ∀ (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (s : ℕ) (t : ℝ) (a : TrialInputs μ ℱ s d t C) (failure : Set Ω),
    0 < t → t < t0 → failure ⊆ a.crossing →
    μ failure ≤ ENNReal.ofReal (Real.exp (-power t (-c))) :=
  one_trial_of AndersonAC.OpusS45.traceHelpers_proof hGT

end AndersonAC.AgentS45
