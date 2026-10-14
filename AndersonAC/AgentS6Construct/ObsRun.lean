import AndersonAC.AgentS6Construct.Obs
import AndersonAC.AgentS6Construct.HatGInvariant

/-! The observable part of the reached cursor follows `obsStep`. -/

noncomputable section

open scoped Matrix

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

theorem runAt_le_limit_of_running (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (m : ℕ)
    (h : (runAt core t r M0 hM ξ order ω m).running = true) : m ≤ heatLimit t := by
  by_contra hlt
  push_neg at hlt
  have hN : (runAt core t r M0 hM ξ order ω (heatLimit t + 1)).running = false := by
    have := runCursor_not_running_after_limit t (leverageScale t) (heatLimit t) (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
      (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω))
    simpa [runAt] using this
  have hfreeze := runCursor_eq_of_not_running t (leverageScale t) (heatLimit t) (r ω)
    (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
    (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω))
    (show heatLimit t + 1 ≤ m by omega) hN
  have h' : (runAt core t r M0 hM ξ order ω m).running =
      (runAt core t r M0 hM ξ order ω (heatLimit t + 1)).running :=
    congrArg TrialCursor.running hfreeze
  rw [h, hN] at h'
  exact Bool.noConfusion h'

theorem runAt_le_stop_of_running (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (m : ℕ)
    (h : (runAt core t r M0 hM ξ order ω m).running = true) :
    m ≤ stopAt core t r M0 hM ξ order ω := by
  have hm := runAt_le_limit_of_running core t r M0 hM ξ order ω m h
  exact runCursor_index_le_finalStop t (leverageScale t) (heatLimit t) (r ω)
    (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
    (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)) m (by omega) h
    (runCursor_not_running_after_limit t (leverageScale t) (heatLimit t) (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
      (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)))

theorem runAt_trialCross_eq_obsCross (core : Finset ι) (t : ℝ) (ht : 0 < t)
    (r : Ω → ι → ℂ) (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det)) (k : ℕ) :
    trialCross t (r ω) (runAt core t r M0 hM ξ order ω k).state =
      obsCross core t (r ω) (runAt core t r M0 hM ξ order ω k).obs := by
  have hmatch := runAt_hatGMatches core t ht r M0 hM ξ order ω hterminal k
  exact trialCross_eq_trialCrossFromHatG t (r ω) _ (fun i j => hmatch i.1 j.1 i.2 j.2)

theorem runAt_ridge_eq_obsRidge (core : Finset ι) (t : ℝ) (ht : 0 < t)
    (r : Ω → ι → ℂ) (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det)) (k : ℕ) :
    ridgeAt core t r M0 hM ξ order k ω =
      obsRidge core t (r ω) (runAt core t r M0 hM ξ order ω k).obs := by
  have hcross := runAt_trialCross_eq_obsCross core t ht r M0 hM ξ order ω hterminal k
  change chooseRidge (trialCross t (r ω) (runAt core t r M0 hM ξ order ω k).state)
    (leverageScale t) (runAt core t r M0 hM ξ order ω k).previousRidge = _
  rw [hcross]
  rfl

theorem runAt_pivot_eq_obsPivot (core : Finset ι) (t : ℝ) (ht : 0 < t)
    (r : Ω → ι → ℂ) (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det)) (k : ℕ) :
    pivotAt core t r M0 hM ξ order k ω =
      obsPivot core t (r ω) order (runAt core t r M0 hM ξ order ω k).obs := by
  have hcross := runAt_trialCross_eq_obsCross core t ht r M0 hM ξ order ω hterminal k
  have hridge := runAt_ridge_eq_obsRidge core t ht r M0 hM ξ order ω hterminal k
  change leastMaximizerTotal order (leverage
    (trialCross t (r ω) (runAt core t r M0 hM ξ order ω k).state)
    (ridgeAt core t r M0 hM ξ order k ω)) = _
  rw [hcross, hridge]
  rfl

set_option maxHeartbeats 1000000 in
theorem runAt_obs_succ (core : Finset ι) (t : ℝ) (ht : 0 < t) (r : Ω → ι → ℂ)
    (hrpos : ∀ ω i, 0 < (r ω i).im)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm) (ξ : ι → Ω → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det)) (k : ℕ) :
    (runAt core t r M0 hM ξ order ω (k + 1)).obs =
      obsStep core t (heatLimit t) (r ω) (activeInverse (M0 ω) t (r ω)) order k
        (runAt core t r M0 hM ξ order ω k).obs (residualAt core t r M0 hM ξ order k ω) := by
  classical
  have hmatch := runAt_hatGMatches core t ht r M0 hM ξ order ω hterminal k
  have hcross := runAt_trialCross_eq_obsCross core t ht r M0 hM ξ order ω hterminal k
  have hpiv := runAt_pivot_eq_obsPivot core t ht r M0 hM ξ order ω hterminal k
  have hridge := runAt_ridge_eq_obsRidge core t ht r M0 hM ξ order ω hterminal k
  set q := runAt core t r M0 hM ξ order ω k with hqdef
  have hW : ∀ τ, trialWeights t (r ω) q.state τ =
      leverage (obsCross core t (r ω) q.obs) τ := by
    intro τ
    unfold trialWeights
    rw [hcross]
  have hready : projectionReady t (r ω) q.state ↔
      ∀ i, projectionWeight (obsCross core t (r ω) q.obs) i ≤ 2 * leverageScale t := by
    unfold projectionReady
    rw [hcross]
  have hstep : runAt core t r M0 hM ξ order ω (k + 1) =
      cursorStep t (leverageScale t) (heatLimit t) (r ω)
        (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q := rfl
  cases hrun : q.running
  · rw [hstep, cursorStep_eq_of_not_running _ _ _ _ _ _ _ _ _ hrun]
    unfold obsStep
    rw [if_neg (by simp [TrialCursor.obs, hrun])]
  · have hrun' : q.obs.running = true := hrun
    by_cases hb : BudgetsHold t (activeInverse (M0 ω) t (r ω)) q.state.hatG
    · have hb' : BudgetsHold t (activeInverse (M0 ω) t (r ω)) q.obs.H := hb
      by_cases hk : k = heatLimit t
      · have hc : cursorStep t (leverageScale t) (heatLimit t) (r ω)
            (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q =
            { q with running := false, stop := k, outcome := .fail } := by
          simp [cursorStep, hrun, hb, hk]
        rw [hstep, hc]
        unfold obsStep
        rw [if_pos hrun', if_pos hb', if_pos hk]
        rfl
      · by_cases hcap : 4 * leverageScale t <
            maxWeight (trialWeights t (r ω) q.state q.previousRidge)
        · have hcap' : 4 * leverageScale t <
              maxWeight (leverage (obsCross core t (r ω) q.obs) q.obs.τ) := by
            rw [← hW]
            exact hcap
          have hc : cursorStep t (leverageScale t) (heatLimit t) (r ω)
              (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q =
              { q with running := false, stop := k, outcome := .fail } := by
            simp [cursorStep, hrun, hb, hk, hcap]
          rw [hstep, hc]
          unfold obsStep
          rw [if_pos hrun', if_pos hb', if_neg hk, if_pos hcap']
          rfl
        · have hcap' : ¬ 4 * leverageScale t <
              maxWeight (leverage (obsCross core t (r ω) q.obs) q.obs.τ) := by
            rw [← hW]
            exact hcap
          by_cases hr : projectionReady t (r ω) q.state
          · have hr' := hready.1 hr
            have hc : cursorStep t (leverageScale t) (heatLimit t) (r ω)
                (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q =
                { q with running := false, stop := k, outcome := .done } := by
              simp [cursorStep, hrun, hb, hk, hcap, hr]
            rw [hstep, hc]
            unfold obsStep
            rw [if_pos hrun', if_pos hb', if_neg hk, if_neg hcap', if_pos hr']
            rfl
          · have hr' : ¬ ∀ i, projectionWeight (obsCross core t (r ω) q.obs) i ≤
                2 * leverageScale t := fun h => hr (hready.2 h)
            have hc := cursorStep_heat_eq t (leverageScale t) (heatLimit t) (r ω)
              (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q hrun hb hk hcap hr
            have hrun1 : (runAt core t r M0 hM ξ order ω (k + 1)).running = true := by
              rw [hstep, hc]
              exact hrun
            have hlt : k < stopAt core t r M0 hM ξ order ω := by
              have := runAt_le_stop_of_running core t r M0 hM ξ order ω (k + 1) hrun1
              omega
            have hheat := runAt_heatTransition core t ht r M0 hM ξ order ω k hterminal hlt
            have hformula := heatTransition_hatG_entry_formula t ht (r ω) (hrpos ω) _ _ _ _
              hheat (fun i j => hmatch i.1 j.1 i.2 j.2)
            obtain ⟨hx, hxc, hact, -, -, -⟩ := hheat
            unfold obsStep
            rw [if_pos hrun', if_pos hb', if_neg hk, if_neg hcap', if_neg hr', ← hpiv,
              ← hridge]
            refine Obs.ext ?_ ?_ ?_ ?_ ?_
            · exact hact
            · funext i j
              have hf := hformula i j
              change (stateAt core t r M0 hM ξ order (k + 1) ω).hatG i j = _
              rw [hf]
              unfold heatH
              simp only [hact, dite_eq_ite]
              rfl
            · change (runAt core t r M0 hM ξ order ω (k + 1)).previousRidge = _
              rw [hstep, hc]
              rfl
            · exact hrun1
            · change (runAt core t r M0 hM ξ order ω (k + 1)).outcome = _
              rw [hstep, hc]
              rfl
    · have hb' : ¬ BudgetsHold t (activeInverse (M0 ω) t (r ω)) q.obs.H := hb
      have hc : cursorStep t (leverageScale t) (heatLimit t) (r ω)
          (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order k q =
          { q with running := false, stop := k, outcome := .fail } := by
        simp [cursorStep, hrun, hb]
      rw [hstep, hc]
      unfold obsStep
      rw [if_pos hrun', if_neg hb']
      rfl

end AndersonAC.AgentS6Construct
