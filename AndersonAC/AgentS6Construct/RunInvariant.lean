import AndersonAC.AgentS6Construct.Data
import AndersonAC.AgentS6Construct.TerminalInvariant
import AndersonAC.AgentS6Construct.SelectionFacts

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem cursorStep_preserves_terminalInvariant {core : Finset ι}
    (t l : ℝ) (N : ℕ) (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hInv : allPrincipalMinorUnits q.state (fun i => ξ i.1))
    (hlegal : ∀ (hr : q.running = true) (hbudget : BudgetsHold t g0 q.state.hatG)
      (hcutoff : k ≠ N)
      (hcap : ¬ 4 * l < maxWeight (trialWeights t r q.state q.previousRidge))
      (hready : ¬ projectionReady t r q.state),
      let p := leastMaximizerTotal order
        (trialWeights t r q.state (selectedRidge t r q.state q.previousRidge))
      p ∈ q.state.active ∧ p ∉ core) :
    allPrincipalMinorUnits (cursorStep t l N r g0 ξ order k q).state
      (fun i => ξ i.1) := by
  classical
  cases hr : q.running
  · rw [cursorStep_eq_of_not_running t l N r g0 ξ order k q hr]
    exact hInv
  · by_cases hbudget : BudgetsHold t g0 q.state.hatG
    · by_cases hcutoff : k = N
      · subst k
        rw [cursorStep_state_eq_of_limit t l N r g0 ξ order q hr]
        exact hInv
      · by_cases hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge)
        · rw [cursorStep_state_eq_of_cap_fail t l N r g0 ξ order k q
            hr hbudget hcutoff hcap]
          exact hInv
        · by_cases hready : projectionReady t r q.state
          · rw [cursorStep_state_eq_of_ready t l N r g0 ξ order k q
              hr hbudget hcutoff hcap hready]
            exact hInv
          · let p := leastMaximizerTotal order
              (trialWeights t r q.state (selectedRidge t r q.state q.previousRidge))
            obtain ⟨hpActive, hpCore⟩ := hlegal hr hbudget hcutoff hcap hready
            have hden := pivot_denominator_ne_zero q.state (fun i => ξ i.1)
              ⟨p, hpActive⟩ hInv
            have hheat := heatState_allPrincipalMinorUnits q.state t r ξ p
              hpActive hpCore hden hInv
            rw [cursorStep_heat_eq t l N r g0 ξ order k q hr hbudget
              hcutoff hcap hready]
            change allPrincipalMinorUnits
              (heatStateTotal t r q.state p (ξ p)) (fun i => ξ i.1)
            have htotal : heatStateTotal t r q.state p (ξ p) =
                heatState t r q.state p hpActive hpCore (ξ p) := by
              unfold heatStateTotal
              rw [dif_pos hpActive, dif_pos hpCore]
            rw [htotal]
            exact hheat
    · rw [cursorStep_state_eq_of_budget_fail t l N r g0 ξ order k q hr hbudget]
      exact hInv

theorem runAt_previousRidge_pos {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (core : Finset ι) (t : ℝ) (ht : 0 < t) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    ∀ k, (runAt core t r M0 hM ξ order ω k).running = true →
      0 < (runAt core t r M0 hM ξ order ω k).previousRidge := by
  intro k
  induction k with
  | zero =>
      intro _
      exact zpow_pos (Real.rpow_pos_of_pos ht _) _
  | succ k ih =>
      intro hnext
      let q := runAt core t r M0 hM ξ order ω k
      have hnext' : (cursorStep t (leverageScale t) (heatLimit t) (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q).running = true := by
        simpa [runAt, runCursor, q] using hnext
      have hrun : q.running = true := by
        cases hq : q.running
        · have hfalse : False := by
            simpa [cursorStep, hq] using hnext'
          exact hfalse.elim
        · rfl
      have hprev := ih hrun
      have hchoose : ∀ (hrun' : q.running = true)
          (hbudget : BudgetsHold t (activeInverse (M0 ω) t (r ω)) q.state.hatG)
          (hcutoff : k ≠ heatLimit t)
          (hcap : ¬ 4 * leverageScale t <
            maxWeight (trialWeights t (r ω) q.state q.previousRidge))
          (hready : ¬ projectionReady t (r ω) q.state),
          0 < selectedRidge t (r ω) q.state q.previousRidge := by
        intro hrun' hbudget hcutoff hcap hready
        exact selectedRidge_pos_of_not_ready t ht (r ω) q.state q.previousRidge hprev hready
      have hstep := cursorStep_previousRidge_pos_of_running t (leverageScale t)
        (heatLimit t) (r ω) (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω)
        order k q hchoose hnext'
      simpa [runAt, runCursor, q] using hstep

theorem runAt_allPrincipalMinorUnits_of_legal {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (core : Finset ι) (t : ℝ) (ht : 0 < t) (r : Ω → ι → ℂ) (M0 : Ω → Matrix ι ι ℝ)
    (hM : ∀ ω, (M0 ω).IsSymm) (ξ : ι → Ω → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det)) :
    ∀ k, allPrincipalMinorUnits (stateAt core t r M0 hM ξ order k ω)
      (fun i => ξ i.1 ω) := by
  intro k
  induction k with
  | zero =>
      rw [stateAt_zero]
      exact initialState_allPrincipalMinorUnits core (M0 ω)
        (activeInverse (M0 ω) t (r ω)) (hM ω) (fun i => ξ i ω) hterminal
  | succ k ih =>
      let q := runAt core t r M0 hM ξ order ω k
      have hstep := cursorStep_preserves_terminalInvariant
        t (leverageScale t) (heatLimit t) (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q ih
        (by
          intro hr hbudget hcutoff hcap hready
          have hτ := runAt_previousRidge_pos core t ht r M0 hM ξ order ω k hr
          have hcap' : maxWeight (trialWeights t (r ω) q.state q.previousRidge) ≤
              4 * leverageScale t := le_of_not_gt hcap
          obtain ⟨hpActive, hpCore, -, -, -⟩ := selectedPivot_active_exterior
            t (leverageScale t) (r ω) q.state q.previousRidge order
            (Real.rpow_pos_of_pos ht _) rfl hτ hcap' hready
          exact ⟨hpActive, hpCore⟩)
      change allPrincipalMinorUnits
        (runAt core t r M0 hM ξ order ω (k + 1)).state (fun i => ξ i.1 ω)
      simpa [runAt, runCursor, q] using hstep

end AndersonAC.AgentS6Construct
