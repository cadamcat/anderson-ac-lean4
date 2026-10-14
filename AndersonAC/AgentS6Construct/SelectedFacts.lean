import AndersonAC.AgentS6Construct.RunFacts
import AndersonAC.AgentS6.LeverageFacts

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

theorem runAt_selected_pivot_properties (core : Finset ι) (t : ℝ) (ht : 0 < t)
    (r : Ω → ι → ℂ) (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (k : ℕ)
    (hk : k < stopAt core t r M0 hM ξ order ω) :
    let s := stateAt core t r M0 hM ξ order k ω
    let ρ := ridgeAt core t r M0 hM ξ order k ω
    let p := pivotAt core t r M0 hM ξ order k ω
    0 < ρ ∧ p ∈ s.active ∧ p ∉ core ∧
      2 * leverageScale t ≤ maxWeight (trialWeights t (r ω) s ρ) ∧
      maxWeight (trialWeights t (r ω) s ρ) ≤ 4 * leverageScale t ∧
      trialWeights t (r ω) s ρ p = maxWeight (trialWeights t (r ω) s ρ) ∧
      ∀ i, trialWeights t (r ω) s ρ i =
        maxWeight (trialWeights t (r ω) s ρ) → order p ≤ order i := by
  classical
  let q := runAt core t r M0 hM ξ order ω k
  have hstep := runAt_successful_step core t r M0 hM ξ order ω k hk
  have hprev := runAt_previousRidge_pos core t ht r M0 hM ξ order ω k
    (runAt_running_before_stop core t r M0 hM ξ order ω k hk)
  have hselected := selectedPivot_active_exterior t (leverageScale t) (r ω) q.state
    q.previousRidge order (Real.rpow_pos_of_pos ht _) rfl hprev
    (le_of_not_gt hstep.2.2.1) hstep.2.1
  have hρ : 0 < selectedRidge t (r ω) q.state q.previousRidge := hselected.2.2.1
  have hmax : 2 * leverageScale t ≤
      maxWeight (trialWeights t (r ω) q.state (selectedRidge t (r ω) q.state q.previousRidge)) :=
    hselected.2.2.2.1
  have hcap : maxWeight (trialWeights t (r ω) q.state
      (selectedRidge t (r ω) q.state q.previousRidge)) ≤ 4 * leverageScale t :=
    hselected.2.2.2.2
  have hnonneg : ∀ i, 0 ≤ trialWeights t (r ω) q.state
      (selectedRidge t (r ω) q.state q.previousRidge) i := by
    intro i
    change 0 ≤ leverage (trialCross t (r ω) q.state)
      (selectedRidge t (r ω) q.state q.previousRidge) i
    exact AndersonAC.AgentS6.leverage_nonneg _ hρ.le i
  obtain ⟨hpmax, hptie⟩ := leastMaximizerTotal_spec order
    (trialWeights t (r ω) q.state (selectedRidge t (r ω) q.state q.previousRidge)) hnonneg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ridgeAt, q, selectedRidge]
  · simpa [pivotAt, ridgeAt, stateAt, q, selectedRidge] using hselected.1
  · simpa [pivotAt, ridgeAt, stateAt, q, selectedRidge] using hselected.2.1
  · simpa [ridgeAt, stateAt, q, selectedRidge] using hmax
  · simpa [ridgeAt, stateAt, q, selectedRidge] using hcap
  · simpa [pivotAt, ridgeAt, stateAt, q, selectedRidge] using hpmax
  · intro i hi
    exact hptie i hi

end AndersonAC.AgentS6Construct
