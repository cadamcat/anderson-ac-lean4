import AndersonAC.AgentS6Construct.Data

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {core : Finset ι}

theorem runCursor_index_le_finalStop (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (q0 : TrialCursor core) (k : ℕ) (hk : k ≤ N + 1)
    (hrun : (runCursor t l N r g0 ξ order q0 k).running = true)
    (hfinal : ¬ (runCursor t l N r g0 ξ order q0 (N + 1)).running) :
    k ≤ (runCursor t l N r g0 ξ order q0 (N + 1)).stop := by
  have aux : ∀ d k, N + 1 - k = d → k ≤ N + 1 →
      (runCursor t l N r g0 ξ order q0 k).running = true →
      k ≤ (runCursor t l N r g0 ξ order q0 (N + 1)).stop := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro k hrem hbound hrun
      by_cases hkfinal : k = N + 1
      · subst k
        exact (hfinal hrun).elim
      · have hbound' : k + 1 ≤ N + 1 := by omega
        let q := runCursor t l N r g0 ξ order q0 k
        let q' := cursorStep t l N r g0 ξ order k q
        have hqrun : q.running = true := by simpa [q] using hrun
        by_cases hqstop : q'.running = false
        · have hstepStop := cursorStep_stop_eq_of_running_to_stopped t l N r g0 ξ
            order k q hqrun hqstop
          have hfreeze := runCursor_eq_of_not_running t l N r g0 ξ order q0
            hbound' hqstop
          have hfreeze' : runCursor t l N r g0 ξ order q0 (N + 1) = q' := by
            simpa [q', q, runCursor] using hfreeze
          have hstopEq :
              (runCursor t l N r g0 ξ order q0 (N + 1)).stop = k := by
            rw [hfreeze']
            exact hstepStop
          omega
        · have hqrun' : q'.running = true := by
            cases h : q'.running <;> simp_all
          have hrun' :
              (runCursor t l N r g0 ξ order q0 (k + 1)).running = true := by
            simpa [runCursor, q', q] using hqrun'
          have hrem' : N + 1 - (k + 1) < d := by omega
          have hnext := ih (N + 1 - (k + 1)) hrem' (k + 1) rfl hbound' hrun'
          omega
  exact aux (N + 1 - k) k rfl hk hrun

theorem stateAt_eq_stop_of_le (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (k : ℕ)
    (hk : stopAt core t r M0 hM ξ order ω ≤ k) :
    stateAt core t r M0 hM ξ order k ω =
      stateAt core t r M0 hM ξ order (stopAt core t r M0 hM ξ order ω) ω := by
  classical
  let N := heatLimit t
  let q0 := initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)
  let s := stopAt core t r M0 hM ξ order ω
  have hsN : s ≤ N := runAt_stop_le core t r M0 hM ξ order ω
  by_cases hsk : s = k
  · subst k
    rfl
  · have hsk' : s < k := by omega
    have hsplusK : s + 1 ≤ k := Nat.succ_le_of_lt hsk'
    have hsplusN : s + 1 ≤ N + 1 := by omega
    have hfinal : ¬ (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1)).running := by
      exact runCursor_not_running_after_limit t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0
    have hfinalEq : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1)).running = false := by
      cases h : (runCursor t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1)).running <;>
        simp_all
    have hsrun : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 s).running = true := by
      simpa [s, stopAt, runAt, N, q0] using
        runCursor_running_at_final_stop t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 rfl rfl
    have hsplusFalse : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1)).running = false := by
      by_contra hnot
      have hsplusRun : (runCursor t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1)).running = true := by
        cases h : (runCursor t (leverageScale t) N (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1)).running <;>
          simp_all
      have hle := runCursor_index_le_finalStop t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1)
        (by omega) hsplusRun hfinal
      have hstopDef : s = (runCursor t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1)).stop := by
        rfl
      omega
    have hsstate : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1)).state =
        (runCursor t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 s).state := by
      have hstep := cursorStep_state_eq_of_running_to_stopped t (leverageScale t) N
        (r ω) (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order s
        (runCursor t (leverageScale t) N (r ω) (activeInverse (M0 ω) t (r ω))
          (fun i => ξ i ω) order q0 s) hsrun hsplusFalse
      simpa [runCursor] using hstep
    have hstateFinal : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1)).state =
        (runCursor t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 s).state := by
      have hfreeze := runCursor_eq_of_not_running t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0
        (k := s + 1) (m := N + 1) hsplusN hsplusFalse
      have hfreeze' : runCursor t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1) =
          runCursor t (leverageScale t) N (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1) := by
        simpa using hfreeze
      calc
        _ = (runCursor t (leverageScale t) N (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1)).state :=
              congrArg TrialCursor.state hfreeze'
        _ = _ := hsstate
    have hstateK : (runCursor t (leverageScale t) N (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 k).state =
        (runCursor t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 s).state := by
      by_cases hkN : k ≤ N + 1
      · have hfreeze := runCursor_eq_of_not_running t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0
          (k := s + 1) (m := k) hsplusK hsplusFalse
        have hfreeze' : runCursor t (leverageScale t) N (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 k =
            runCursor t (leverageScale t) N (r ω)
              (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1) := by
          simpa using hfreeze
        calc
          _ = (runCursor t (leverageScale t) N (r ω)
              (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (s + 1)).state :=
                congrArg TrialCursor.state hfreeze'
          _ = _ := hsstate
      · have hfreeze := runCursor_eq_of_not_running t (leverageScale t) N (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0
          (k := N + 1) (m := k) (by omega) hfinalEq
        have hfreeze' : runCursor t (leverageScale t) N (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 k =
            runCursor t (leverageScale t) N (r ω)
              (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1) := by
          simpa using hfreeze
        calc
          _ = (runCursor t (leverageScale t) N (r ω)
              (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order q0 (N + 1)).state :=
                congrArg TrialCursor.state hfreeze'
          _ = _ := hstateFinal
    simpa [stateAt, runAt, s, stopAt, N, q0] using hstateK

end AndersonAC.AgentS6Construct
