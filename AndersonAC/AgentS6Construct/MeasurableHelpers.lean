import AndersonAC.AgentS6Construct.HeatFormula
import AndersonAC.AgentS6.LeverageFacts
import AndersonAC.S6.RidgeSelection

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6
open MeasureTheory

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [mΩ : MeasurableSpace Ω]

theorem measurable_activeInverse {F0 : MeasurableSpace Ω} (t : ℝ)
    (M0 : Ω → Matrix ι ι ℝ) (r : Ω → ι → ℂ) (hF : F0 ≤ mΩ)
    (hM0 : @StronglyMeasurable Ω (Matrix ι ι ℝ) _ F0 M0)
    (hr0 : @StronglyMeasurable Ω (ι → ℂ) _ F0 r) :
    Measurable[mΩ] fun ω => activeInverse (M0 ω) t (r ω) := by
  letI : MeasurableSpace Ω := mΩ
  have hD : Measurable[mΩ] (fun ω => dampedMatrix (M0 ω) t (r ω)) := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    have hEval : (fun ω => dampedMatrix (M0 ω) t (r ω) i j) =
        fun ω => (M0 ω i j : ℂ) - if i = j then (t : ℂ) * r ω i else 0 := by
      funext ω
      exact AndersonAC.AgentS6.damped_apply (M0 ω) t (r ω) i j
    rw [hEval]
    have hMijSM : StronglyMeasurable[F0] (fun ω => M0 ω i j) :=
      (continuous_apply j).comp_stronglyMeasurable
        ((continuous_apply i).comp_stronglyMeasurable hM0)
    have hMijF0 : Measurable[F0] (fun ω => M0 ω i j) := by
      letI : MeasurableSpace Ω := F0
      exact hMijSM.measurable
    have hMij : Measurable[mΩ] (fun ω => M0 ω i j) := hMijF0.mono hF le_rfl
    have hriSM : StronglyMeasurable[F0] (fun ω => r ω i) :=
      (continuous_apply i).comp_stronglyMeasurable hr0
    have hriF0 : Measurable[F0] (fun ω => r ω i) := by
      letI : MeasurableSpace Ω := F0
      exact hriSM.measurable
    have hri : Measurable[mΩ] (fun ω => r ω i) := hriF0.mono hF le_rfl
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl]
      exact (Complex.measurable_ofReal.comp hMij).sub (measurable_const.mul hri)
    · simp [hij]
      exact Complex.measurable_ofReal.comp hMij
  exact AndersonAC.AgentS6.measurable_matrix_inv.comp hD

theorem measurable_trialCrossFromHatG {core : Finset ι} {α : Type*}
    [MeasurableSpace α] (t : ℝ) (r : α → ι → ℂ) (active : α → Finset ι)
    (H : α → Matrix ι ι ℂ)
    (hactive : ∀ i, MeasurableSet {a | i ∈ active a})
    (hr : Measurable r) (hH : Measurable H) :
    Measurable fun a => trialCrossFromHatG (core := core) t (r a) (active a) (H a) := by
  classical
  refine Measurable.of_eval_matrix
    (fun a => trialCrossFromHatG (core := core) t (r a) (active a) (H a)) ?_
  intro i b
  by_cases hc : i ∈ core
  · simp [trialCrossFromHatG, hc]
  · have hri : Measurable fun a => (r a i).im :=
      Complex.measurable_im.comp ((measurable_pi_apply i).comp hr)
    have hrb : Measurable fun a => (r a (b : ι)).im :=
      Complex.measurable_im.comp ((measurable_pi_apply (b : ι)).comp hr)
    have hsqi : Measurable fun a => (Real.sqrt ((r a i).im) : ℂ) := by
      exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hri)
    have hsqb : Measurable fun a => (Real.sqrt ((r a (b : ι)).im) : ℂ) := by
      exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hrb)
    have hHij : Measurable fun a => H a i (b : ι) := hH.eval_matrix
    have hconst : Measurable fun _ : α => (2 * Complex.I * (t : ℂ)) := measurable_const
    have hformula : Measurable fun a =>
        (2 * Complex.I * (t : ℂ)) * (Real.sqrt ((r a i).im) : ℂ) *
          H a i (b : ι) * (Real.sqrt ((r a (b : ι)).im) : ℂ) := by
      exact ((hconst.mul hsqi).mul hHij).mul hsqb
    simpa [trialCrossFromHatG, hc] using
      (Measurable.ite (hactive i) hformula measurable_const)

end AndersonAC.AgentS6Construct
