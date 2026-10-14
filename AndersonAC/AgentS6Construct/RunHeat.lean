import AndersonAC.AgentS6Construct.SelectedFacts
import AndersonAC.AgentS6Construct.RunInvariant

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

theorem runAt_heatTransition (core : Finset ι) (t : ℝ) (ht : 0 < t)
    (r : Ω → ι → ℂ) (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (k : ℕ)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det))
    (hk : k < stopAt core t r M0 hM ξ order ω) :
    HeatTransition t (r ω)
      (stateAt core t r M0 hM ξ order k ω)
      (stateAt core t r M0 hM ξ order (k + 1) ω)
      (pivotAt core t r M0 hM ξ order k ω)
      (residualAt core t r M0 hM ξ order k ω) := by
  classical
  let q := runAt core t r M0 hM ξ order ω k
  obtain ⟨_, _, _, _, hstep⟩ := runAt_successful_step core t r M0 hM ξ order ω k hk
  obtain ⟨hρ, hpActive, hpCore, _, _, _, _⟩ :=
    runAt_selected_pivot_properties core t ht r M0 hM ξ order ω k hk
  have hpActive' : pivotAt core t r M0 hM ξ order k ω ∈ q.state.active := by
    simpa [q, stateAt] using hpActive
  have hInv := runAt_allPrincipalMinorUnits_of_legal core t ht r M0 hM ξ order ω
    hterminal k
  have hden : q.state.M ⟨pivotAt core t r M0 hM ξ order k ω, hpActive⟩
      ⟨pivotAt core t r M0 hM ξ order k ω, hpActive⟩ +
        ξ (pivotAt core t r M0 hM ξ order k ω) ω ≠ 0 := by
    exact pivot_denominator_ne_zero q.state (fun i => ξ i.1 ω)
      ⟨pivotAt core t r M0 hM ξ order k ω, hpActive⟩ hInv
  have hstateNext :
      stateAt core t r M0 hM ξ order (k + 1) ω =
        heatState t (r ω) q.state (pivotAt core t r M0 hM ξ order k ω)
          hpActive hpCore (ξ (pivotAt core t r M0 hM ξ order k ω) ω) := by
    have hcursor :
        (runAt core t r M0 hM ξ order ω (k + 1)).state =
          heatStateTotal t (r ω) q.state (pivotAt core t r M0 hM ξ order k ω)
            (ξ (pivotAt core t r M0 hM ξ order k ω) ω) := by
      rw [hstep]
      rfl
    have htotal :
        heatStateTotal t (r ω) q.state (pivotAt core t r M0 hM ξ order k ω)
          (ξ (pivotAt core t r M0 hM ξ order k ω) ω) =
        heatState t (r ω) q.state (pivotAt core t r M0 hM ξ order k ω)
          hpActive hpCore (ξ (pivotAt core t r M0 hM ξ order k ω) ω) := by
      unfold heatStateTotal
      rw [dif_pos hpActive', dif_pos hpCore]
    simpa [stateAt, q] using hcursor.trans htotal
  rw [stateAt, hstateNext]
  simpa [stateAt, q, residualAt] using
    heatState_transition t (r ω) q.state (pivotAt core t r M0 hM ξ order k ω)
      hpActive hpCore (ξ (pivotAt core t r M0 hM ξ order k ω) ω) hden

end AndersonAC.AgentS6Construct
