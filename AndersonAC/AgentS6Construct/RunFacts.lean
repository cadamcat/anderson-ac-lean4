import AndersonAC.AgentS6Construct.InitialFacts
import AndersonAC.AgentS6Construct.RunInvariant

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

theorem runAt_successful_step (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (k : ℕ)
    (hk : k < stopAt core t r M0 hM ξ order ω) :
    let q := runAt core t r M0 hM ξ order ω k
    BudgetsHold t (activeInverse (M0 ω) t (r ω)) q.state.hatG ∧
    ¬ projectionReady t (r ω) q.state ∧
    ¬ 4 * leverageScale t < maxWeight (trialWeights t (r ω) q.state q.previousRidge) ∧
    k ≠ heatLimit t ∧
    runAt core t r M0 hM ξ order ω (k + 1) =
      { q with
        state := heatStateTotal t (r ω) q.state
          (leastMaximizerTotal order
            (trialWeights t (r ω) q.state
              (selectedRidge t (r ω) q.state q.previousRidge)))
          (ξ (leastMaximizerTotal order
            (trialWeights t (r ω) q.state
              (selectedRidge t (r ω) q.state q.previousRidge))) ω)
        previousRidge := selectedRidge t (r ω) q.state q.previousRidge } := by
  classical
  let q0 := initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)
  let N := heatLimit t
  have hstopbound := runAt_stop_le core t r M0 hM ξ order ω
  have hkN : k < N := by dsimp [N] at *; omega
  have hkstep : k + 1 ≤ N + 1 := by omega
  have hnext :
      (runAt core t r M0 hM ξ order ω (k + 1)).running = true := by
    by_contra hfalse
    have hfalse' : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (k + 1)).running = false := by
      change ¬ (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (k + 1)).running = true at hfalse
      cases hrun' : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (k + 1)).running <;>
        simp_all
    have hfreeze := runCursor_eq_of_not_running t (leverageScale t) N (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 hkstep hfalse'
    have hstoplt := runCursor_stop_lt_of_not_running t (leverageScale t) N (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 rfl (k + 1) hfalse'
    have hstopEq : stopAt core t r M0 hM ξ order ω =
        (runAt core t r M0 hM ξ order ω (k + 1)).stop := by
      simpa [stopAt, runAt, q0, N] using congrArg TrialCursor.stop hfreeze
    have hstopFinalLt : stopAt core t r M0 hM ξ order ω < k + 1 := by
      rw [hstopEq]
      simpa [runAt, N] using hstoplt
    omega
  have hrun : (runAt core t r M0 hM ξ order ω k).running = true :=
    runAt_running_before_stop core t r M0 hM ξ order ω k hk
  have hbudget : BudgetsHold t (activeInverse (M0 ω) t (r ω))
      (runAt core t r M0 hM ξ order ω k).state.hatG := by
    by_contra hbad
    have hfail := cursorStep_budget_fail t (leverageScale t) N (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k
      (runAt core t r M0 hM ξ order ω k) hrun hbad
    have : (runAt core t r M0 hM ξ order ω (k + 1)).running = false := by
      simpa [runAt, runCursor] using hfail.1
    exact (Bool.noConfusion (hnext.symm.trans this))
  have hcutoff : k ≠ N := by dsimp [N]; omega
  have hcap : ¬ 4 * leverageScale t < maxWeight (trialWeights t (r ω)
      (runAt core t r M0 hM ξ order ω k).state
      (runAt core t r M0 hM ξ order ω k).previousRidge) := by
    intro hbad
    have hfail := cursorStep_cap_fail t (leverageScale t) N (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k
      (runAt core t r M0 hM ξ order ω k) hrun hbudget hcutoff hbad
    have : (runAt core t r M0 hM ξ order ω (k + 1)).running = false := by
      simpa [runAt, runCursor] using hfail.1
    exact (Bool.noConfusion (hnext.symm.trans this))
  have hready : ¬ projectionReady t (r ω)
      (runAt core t r M0 hM ξ order ω k).state := by
    intro hready
    have hdone := cursorStep_ready_done t (leverageScale t) N (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k
      (runAt core t r M0 hM ξ order ω k) hrun hbudget hcutoff hcap hready
    have : (runAt core t r M0 hM ξ order ω (k + 1)).running = false := by
      simpa [runAt, runCursor] using hdone.1
    exact (Bool.noConfusion (hnext.symm.trans this))
  have hstep := cursorStep_heat_eq t (leverageScale t) N (r ω)
    (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k
    (runAt core t r M0 hM ξ order ω k) hrun hbudget hcutoff hcap hready
  refine ⟨hbudget, hready, hcap, hcutoff, ?_⟩
  simpa [runAt, runCursor, stopAt, N, pivotAt, residualAt, ridgeAt,
    selectedRidge] using hstep

end AndersonAC.AgentS6Construct
