import AndersonAC.AgentS6Construct.ObsRun

/-! The stop index as a predictable event, and the outcome at the stop. -/

noncomputable section

open scoped Matrix

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

theorem stopAt_le_iff (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (i : ℕ) :
    stopAt core t r M0 hM ξ order ω ≤ i ↔
      (runAt core t r M0 hM ξ order ω (i + 1)).running = false := by
  constructor
  · intro hs
    cases h : (runAt core t r M0 hM ξ order ω (i + 1)).running
    · rfl
    · have := runAt_le_stop_of_running core t r M0 hM ξ order ω (i + 1) h
      omega
  · intro h
    have hsN := runAt_stop_le core t r M0 hM ξ order ω
    by_cases hi : i + 1 ≤ heatLimit t + 1
    · have hfreeze := runCursor_eq_of_not_running t (leverageScale t) (heatLimit t) (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
        (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)) hi h
      have hlt := runCursor_stop_lt_of_not_running t (leverageScale t) (heatLimit t) (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
        (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)) rfl (i + 1) h
      have hEq : stopAt core t r M0 hM ξ order ω =
          (runAt core t r M0 hM ξ order ω (i + 1)).stop :=
        congrArg TrialCursor.stop hfreeze
      have hlt' : (runAt core t r M0 hM ξ order ω (i + 1)).stop < i + 1 := hlt
      omega
    · omega

theorem runAt_final_step (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    (runAt core t r M0 hM ξ order ω (stopAt core t r M0 hM ξ order ω)).running = true ∧
      (runAt core t r M0 hM ξ order ω (stopAt core t r M0 hM ξ order ω + 1)).running = false ∧
      runAt core t r M0 hM ξ order ω (heatLimit t + 1) =
        runAt core t r M0 hM ξ order ω (stopAt core t r M0 hM ξ order ω + 1) := by
  have hrun : (runAt core t r M0 hM ξ order ω (stopAt core t r M0 hM ξ order ω)).running =
      true :=
    runCursor_running_at_final_stop t (leverageScale t) (heatLimit t) (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
      (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)) rfl rfl
  have hnext : (runAt core t r M0 hM ξ order ω
      (stopAt core t r M0 hM ξ order ω + 1)).running = false :=
    (stopAt_le_iff core t r M0 hM ξ order ω _).1 le_rfl
  have hsN := runAt_stop_le core t r M0 hM ξ order ω
  refine ⟨hrun, hnext, ?_⟩
  exact runCursor_eq_of_not_running t (leverageScale t) (heatLimit t) (r ω)
    (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
    (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω))
    (show stopAt core t r M0 hM ξ order ω + 1 ≤ heatLimit t + 1 by omega) hnext

theorem maxWeight_trialWeights_le_of_ready {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (s : TrialState core) (τ : ℝ) (hτ : 0 < τ) (hl : 0 < leverageScale t)
    (hready : projectionReady t r s) :
    maxWeight (trialWeights t r s τ) ≤ 2 * leverageScale t := by
  have hrc := AndersonAC.S6.ridge_calculus (trialCross t r s) τ hτ
  unfold Planned.ridge_calculus at hrc
  obtain ⟨-, -, -, -, hlev, -⟩ := hrc
  apply AndersonAC.AgentS6.maxWeight_le (by linarith)
  intro i
  exact (hlev i).2.trans (hready i)

set_option maxHeartbeats 1000000 in
theorem outcome_spec (core : Finset ι) (t : ℝ) (ht : 0 < t) (hlt2 : leverageScale t < 2)
    (c K : ℝ) (r : Ω → ι → ℂ) (hr : ∀ ω, BroadBounds c K (r ω))
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    (outcomeAt core t r M0 hM ξ order ω = .done ↔
      stopAt core t r M0 hM ξ order ω < heatLimit t ∧
        BudgetsHold t (activeInverse (M0 ω) t (r ω))
          (stateAt core t r M0 hM ξ order (stopAt core t r M0 hM ξ order ω) ω).hatG ∧
        projectionReady t (r ω)
          (stateAt core t r M0 hM ξ order (stopAt core t r M0 hM ξ order ω) ω)) ∧
    (outcomeAt core t r M0 hM ξ order ω = .fail →
      stopAt core t r M0 hM ξ order ω = heatLimit t ∨
        ¬ BudgetsHold t (activeInverse (M0 ω) t (r ω))
          (stateAt core t r M0 hM ξ order (stopAt core t r M0 hM ξ order ω) ω).hatG ∨
        4 * leverageScale t < maxWeight (trialWeights t (r ω)
          (stateAt core t r M0 hM ξ order (stopAt core t r M0 hM ξ order ω) ω)
          (ridgeAt core t r M0 hM ξ order (stopAt core t r M0 hM ξ order ω - 1) ω))) := by
  classical
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  obtain ⟨hrun, hnext, hfinal⟩ := runAt_final_step core t r M0 hM ξ order ω
  have hsN := runAt_stop_le core t r M0 hM ξ order ω
  set s := stopAt core t r M0 hM ξ order ω with hs
  set q := runAt core t r M0 hM ξ order ω s with hq
  have hout : outcomeAt core t r M0 hM ξ order ω =
      (cursorStep t (leverageScale t) (heatLimit t) (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order s q).outcome := by
    change (runAt core t r M0 hM ξ order ω (heatLimit t + 1)).outcome = _
    rw [hfinal]
    rfl
  have hnext' : (cursorStep t (leverageScale t) (heatLimit t) (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order s q).running = false := hnext
  have hstate : stateAt core t r M0 hM ξ order s ω = q.state := rfl
  rw [hout, hstate]
  have hprev := runAt_previousRidge_pos core t ht r M0 hM ξ order ω s hrun
  by_cases hb : BudgetsHold t (activeInverse (M0 ω) t (r ω)) q.state.hatG
  · by_cases hk : s = heatLimit t
    · have hf := cursorStep_limit_fail t (leverageScale t) (heatLimit t) (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q hrun
      rw [hk]
      rw [hf.2.2]
      refine ⟨?_, fun _ => Or.inl rfl⟩
      constructor
      · intro h
        exact absurd h (by decide)
      · intro h
        exact absurd h.1 (lt_irrefl _)
    · by_cases hcap : 4 * leverageScale t <
          maxWeight (trialWeights t (r ω) q.state q.previousRidge)
      · have hf := cursorStep_cap_fail t (leverageScale t) (heatLimit t) (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order s q hrun hb hk hcap
        rw [hf.2.2]
        refine ⟨?_, fun _ => Or.inr (Or.inr ?_)⟩
        · constructor
          · intro h
            exact absurd h (by decide)
          · intro h
            have hle := maxWeight_trialWeights_le_of_ready t (r ω) q.state q.previousRidge
              hprev hl h.2.2
            linarith
        · rcases Nat.eq_zero_or_pos s with hs0 | hspos
          · exfalso
            have hcap0 := initial_previous_cap core t ht hlt2 c K r M0 hM hr ω
            have hq0 : q = runAt core t r M0 hM ξ order ω 0 := by rw [hq, hs0]
            have : 4 * leverageScale t < maxWeight (trialWeights t (r ω)
                (initialState core (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω))
                ((leverageScale t) ^ (-2 : ℤ))) := by
              rw [hq0] at hcap
              exact hcap
            linarith
          · obtain ⟨j, hj⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
            have hjs : j < stopAt core t r M0 hM ξ order ω := by omega
            have hstep := (runAt_successful_step core t r M0 hM ξ order ω j hjs).2.2.2.2
            have hqj : q = runAt core t r M0 hM ξ order ω (j + 1) := by rw [hq, hj]
            have hprevEq : q.previousRidge = ridgeAt core t r M0 hM ξ order j ω := by
              rw [hqj, hstep]
              rfl
            rw [hj, Nat.add_sub_cancel, ← hprevEq]
            exact hcap
      · by_cases hready : projectionReady t (r ω) q.state
        · have hd := cursorStep_ready_done t (leverageScale t) (heatLimit t) (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order s q hrun hb hk hcap hready
          rw [hd.2.2]
          refine ⟨⟨fun _ => ⟨by omega, hb, hready⟩, fun _ => rfl⟩, fun h => ?_⟩
          exact absurd h (by decide)
        · exfalso
          have hh := cursorStep_heat_eq t (leverageScale t) (heatLimit t) (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order s q hrun hb hk hcap hready
          rw [hh] at hnext'
          change q.running = false at hnext'
          rw [hrun] at hnext'
          exact Bool.noConfusion hnext'
  · have hf := cursorStep_budget_fail t (leverageScale t) (heatLimit t) (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order s q hrun hb
    rw [hf.2.2]
    refine ⟨⟨fun h => absurd h (by decide), fun h => absurd h.2.1 hb⟩,
      fun _ => Or.inr (Or.inl hb)⟩

end AndersonAC.AgentS6Construct
