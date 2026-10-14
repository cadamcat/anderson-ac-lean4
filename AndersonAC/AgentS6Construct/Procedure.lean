import AndersonAC.AgentS6Construct.Core

/-! A finite, totalized version of the deterministic trial rule. The proofs later
show that the fallback cases of `heatStateTotal` are never used on a running heat. -/

noncomputable section

open scoped BigOperators

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

def orderedMaximizers (order : ι ≃ Fin (Fintype.card ι)) (m : ι → ℝ) :
    Finset (Fin (Fintype.card ι)) :=
  Finset.univ.filter (fun j => m (order.symm j) = maxWeight m)

noncomputable def leastMaximizerTotal (order : ι ≃ Fin (Fintype.card ι)) (m : ι → ℝ) : ι :=
  if h : (orderedMaximizers order m).Nonempty then
    order.symm ((orderedMaximizers order m).min' h)
  else Classical.choice ‹Nonempty ι›

theorem leastMaximizerTotal_spec (order : ι ≃ Fin (Fintype.card ι))
    (m : ι → ℝ) (hnonneg : ∀ i, 0 ≤ m i) :
    m (leastMaximizerTotal order m) = maxWeight m ∧
      ∀ i, m i = maxWeight m → order (leastMaximizerTotal order m) ≤ order i := by
  classical
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι)
    (Finset.univ_nonempty) (fun i => Real.toNNReal (m i))
  have hval : maxWeight m = m i := by
    unfold maxWeight
    rw [hsup]
    exact Real.coe_toNNReal (m i) (hnonneg i)
  let S := orderedMaximizers order m
  have hS : S.Nonempty := by
    refine ⟨order i, ?_⟩
    simp [S, orderedMaximizers, hval]
  let p := leastMaximizerTotal order m
  have hp : order p = S.min' hS := by
    simp [p, leastMaximizerTotal, S, hS]
  have hminmem : S.min' hS ∈ S := Finset.min'_mem S hS
  have hmaxp' : m (order.symm (S.min' hS)) = maxWeight m := by
    simpa [S, orderedMaximizers] using hminmem
  have hmaxp : m p = maxWeight m := by
    simpa [p, leastMaximizerTotal, S, hS] using hmaxp'
  refine ⟨hmaxp, ?_⟩
  intro j hj
  have hjS : order j ∈ S := by simp [S, orderedMaximizers, hj]
  have hle := Finset.min'_le S (order j) hjS
  simpa [p, leastMaximizerTotal, S, hS] using hle

def heatStateTotal {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (s : TrialState core) (x : ι) (ξ : ℝ) : TrialState core :=
  if hx : x ∈ s.active then
    if hxc : x ∉ core then heatState t r s x hx hxc ξ else s
  else s

structure TrialCursor (core : Finset ι) where
  state : TrialState core
  previousRidge : ℝ
  running : Bool
  stop : ℕ
  outcome : TrialOutcome

def initialCursor (core : Finset ι) (t : ℝ) (M : Matrix ι ι ℝ)
    (G : Matrix ι ι ℂ) (hM : M.IsSymm) : TrialCursor core where
  state := initialState core M G hM
  previousRidge := (leverageScale t) ^ (-2 : ℤ)
  running := true
  stop := 0
  outcome := .fail

def selectedRidge {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (τ : ℝ) : ℝ := chooseRidge (trialCross t r s) (leverageScale t) τ

def selectedPivot {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (τ : ℝ) (order : ι ≃ Fin (Fintype.card ι)) : ι :=
  leastMaximizerTotal order (trialWeights t r s (selectedRidge t r s τ))

noncomputable def cursorStep {core : Finset ι} (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (k : ℕ) (q : TrialCursor core) : TrialCursor core := by
  classical
  exact match q.running with
    | false => q
    | true =>
      if hbudget : BudgetsHold t g0 q.state.hatG then
        if hcutoff : k = N then
          { q with running := false, stop := k, outcome := .fail }
        else if hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge) then
          { q with running := false, stop := k, outcome := .fail }
        else if hready : projectionReady t r q.state then
          { q with running := false, stop := k, outcome := .done }
        else
          let τ := selectedRidge t r q.state q.previousRidge
          let x := leastMaximizerTotal order (trialWeights t r q.state τ)
          let s' := heatStateTotal t r q.state x (ξ x)
          { q with state := s', previousRidge := τ }
      else
        { q with running := false, stop := k, outcome := .fail }

theorem cursorStep_heat_eq {core : Finset ι} (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (k : ℕ) (q : TrialCursor core)
    (hr : q.running = true) (hbudget : BudgetsHold t g0 q.state.hatG)
    (hcutoff : k ≠ N)
    (hcap : ¬ 4 * l < maxWeight (trialWeights t r q.state q.previousRidge))
    (hready : ¬ projectionReady t r q.state) :
    cursorStep t l N r g0 ξ order k q =
      { q with
        state := heatStateTotal t r q.state
          (leastMaximizerTotal order
            (trialWeights t r q.state (selectedRidge t r q.state q.previousRidge)))
          (ξ (leastMaximizerTotal order
            (trialWeights t r q.state (selectedRidge t r q.state q.previousRidge))))
        previousRidge := selectedRidge t r q.state q.previousRidge } := by
  classical
  simp [cursorStep, hr, hbudget, hcutoff, hcap, hready]

theorem cursorStep_budget_fail {core : Finset ι} (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (k : ℕ) (q : TrialCursor core) (hr : q.running = true)
    (hbudget : ¬ BudgetsHold t g0 q.state.hatG) :
    (cursorStep t l N r g0 ξ order k q).running = false ∧
      (cursorStep t l N r g0 ξ order k q).stop = k ∧
      (cursorStep t l N r g0 ξ order k q).outcome = .fail := by
  classical
  simp [cursorStep, hr, hbudget]

theorem cursorStep_state_eq_of_budget_fail {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hr : q.running = true) (hbudget : ¬ BudgetsHold t g0 q.state.hatG) :
    (cursorStep t l N r g0 ξ order k q).state = q.state := by
  classical
  simp [cursorStep, hr, hbudget]

theorem cursorStep_state_eq_of_limit {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q : TrialCursor core)
    (hr : q.running = true) :
    (cursorStep t l N r g0 ξ order N q).state = q.state := by
  classical
  simp [cursorStep, hr]

theorem cursorStep_state_eq_of_cap_fail {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hr : q.running = true) (hbudget : BudgetsHold t g0 q.state.hatG)
    (hcutoff : k ≠ N)
    (hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge)) :
    (cursorStep t l N r g0 ξ order k q).state = q.state := by
  classical
  simp [cursorStep, hr, hbudget, hcutoff, hcap]

theorem cursorStep_state_eq_of_ready {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hr : q.running = true) (hbudget : BudgetsHold t g0 q.state.hatG)
    (hcutoff : k ≠ N)
    (hcap : ¬ 4 * l < maxWeight (trialWeights t r q.state q.previousRidge))
    (hready : projectionReady t r q.state) :
    (cursorStep t l N r g0 ξ order k q).state = q.state := by
  classical
  simp [cursorStep, hr, hbudget, hcutoff, hcap, hready]

theorem cursorStep_limit_fail {core : Finset ι} (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (q : TrialCursor core) (hr : q.running = true) :
    (cursorStep t l N r g0 ξ order N q).running = false ∧
      (cursorStep t l N r g0 ξ order N q).stop = N ∧
      (cursorStep t l N r g0 ξ order N q).outcome = .fail := by
  classical
  simp [cursorStep, hr]

theorem cursorStep_cap_fail {core : Finset ι} (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (k : ℕ) (q : TrialCursor core) (hr : q.running = true)
    (hbudget : BudgetsHold t g0 q.state.hatG) (hcutoff : k ≠ N)
    (hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge)) :
    (cursorStep t l N r g0 ξ order k q).running = false ∧
      (cursorStep t l N r g0 ξ order k q).stop = k ∧
      (cursorStep t l N r g0 ξ order k q).outcome = .fail := by
  classical
  simp [cursorStep, hr, hbudget, hcutoff, hcap]

theorem cursorStep_ready_done {core : Finset ι} (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (k : ℕ) (q : TrialCursor core) (hr : q.running = true)
    (hbudget : BudgetsHold t g0 q.state.hatG) (hcutoff : k ≠ N)
    (hcap : ¬ 4 * l < maxWeight (trialWeights t r q.state q.previousRidge))
    (hready : projectionReady t r q.state) :
    (cursorStep t l N r g0 ξ order k q).running = false ∧
      (cursorStep t l N r g0 ξ order k q).stop = k ∧
      (cursorStep t l N r g0 ξ order k q).outcome = .done := by
  classical
  simp [cursorStep, hr, hbudget, hcutoff, hcap, hready]

theorem cursorStep_previousRidge_pos_of_running {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hchoose : ∀ (hr : q.running = true) (hbudget : BudgetsHold t g0 q.state.hatG)
      (hcutoff : k ≠ N)
      (hcap : ¬ 4 * l < maxWeight (trialWeights t r q.state q.previousRidge))
      (hready : ¬ projectionReady t r q.state),
      0 < selectedRidge t r q.state q.previousRidge)
    (hnext : (cursorStep t l N r g0 ξ order k q).running = true) :
    0 < (cursorStep t l N r g0 ξ order k q).previousRidge := by
  classical
  cases hr : q.running
  · simp [cursorStep, hr] at hnext
  · by_cases hbudget : BudgetsHold t g0 q.state.hatG
    · by_cases hcutoff : k = N
      · subst k
        have hfail := (cursorStep_limit_fail t l N r g0 ξ order q hr).1
        rw [hfail] at hnext
        simp at hnext
      · by_cases hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge)
        · have hfail := (cursorStep_cap_fail t l N r g0 ξ order k q hr hbudget hcutoff hcap).1
          rw [hfail] at hnext
          simp at hnext
        · by_cases hready : projectionReady t r q.state
          · have hdone := (cursorStep_ready_done t l N r g0 ξ order k q hr
              hbudget hcutoff hcap hready).1
            rw [hdone] at hnext
            simp at hnext
          · have hρ := hchoose hr hbudget hcutoff hcap hready
            rw [cursorStep_heat_eq t l N r g0 ξ order k q hr hbudget
              hcutoff hcap hready]
            simpa using hρ
    · have hfail := (cursorStep_budget_fail t l N r g0 ξ order k q hr hbudget).1
      rw [hfail] at hnext
      simp at hnext

def runCursor {core : Finset ι} (t l : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (q0 : TrialCursor core) : ℕ → TrialCursor core
  | 0 => q0
  | k + 1 => cursorStep t l N r g0 ξ order k (runCursor t l N r g0 ξ order q0 k)

theorem cursorStep_not_running_at_limit {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q : TrialCursor core) :
    ¬ (cursorStep t l N r g0 ξ order N q).running := by
  classical
  cases hr : q.running <;> simp [cursorStep, hr]

theorem runCursor_not_running_after_limit {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q0 : TrialCursor core) :
    ¬ (runCursor t l N r g0 ξ order q0 (N + 1)).running := by
  simpa only [runCursor] using
    cursorStep_not_running_at_limit t l N r g0 ξ order
      (runCursor t l N r g0 ξ order q0 N)

theorem cursorStep_stop_le {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hq : q.stop ≤ k) : (cursorStep t l N r g0 ξ order k q).stop ≤ k := by
  classical
  by_cases hr : q.running
  · by_cases hbudget : BudgetsHold t g0 q.state.hatG
    · by_cases hcutoff : k = N
      · simp [cursorStep, hr, hbudget, hcutoff]
      · by_cases hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge)
        · simp [cursorStep, hr, hbudget, hcutoff, hcap]
        · by_cases hready : projectionReady t r q.state
          · simp [cursorStep, hr, hbudget, hcutoff, hcap, hready]
          · simpa [cursorStep, hr, hbudget, hcutoff, hcap, hready] using hq
    · simp [cursorStep, hr, hbudget]
  · simpa [cursorStep, hr] using hq

theorem cursorStep_stop_le_at_limit {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q : TrialCursor core)
    (hq : q.stop ≤ N) : (cursorStep t l N r g0 ξ order N q).stop ≤ N := by
  classical
  by_cases hr : q.running
  · by_cases hbudget : BudgetsHold t g0 q.state.hatG
    · simp [cursorStep, hr, hbudget]
    · simp [cursorStep, hr, hbudget]
  · simpa [cursorStep, hr] using hq

theorem runCursor_stop_le {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q0 : TrialCursor core)
    (hq0 : q0.stop = 0) (k : ℕ) :
    (runCursor t l N r g0 ξ order q0 k).stop ≤ k := by
  induction k with
  | zero => simpa [runCursor, hq0]
  | succ k ih =>
      have hs := cursorStep_stop_le t l N r g0 ξ order k
        (runCursor t l N r g0 ξ order q0 k) ih
      simp only [runCursor]
      omega

theorem runCursor_stop_le_limit {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q0 : TrialCursor core)
    (hq0 : q0.stop = 0) :
    (runCursor t l N r g0 ξ order q0 (N + 1)).stop ≤ N := by
  have hN := runCursor_stop_le t l N r g0 ξ order q0 hq0 N
  simpa only [runCursor] using
    cursorStep_stop_le_at_limit t l N r g0 ξ order
      (runCursor t l N r g0 ξ order q0 N) hN

theorem cursorStep_eq_of_not_running {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hq : q.running = false) : cursorStep t l N r g0 ξ order k q = q := by
  classical
  simp [cursorStep, hq]

theorem cursorStep_stop_eq_of_running_to_stopped {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hr : q.running = true)
    (hstop : (cursorStep t l N r g0 ξ order k q).running = false) :
    (cursorStep t l N r g0 ξ order k q).stop = k := by
  classical
  by_cases hbudget : BudgetsHold t g0 q.state.hatG
  · by_cases hcutoff : k = N
    · simp [cursorStep, hr, hbudget, hcutoff]
    · by_cases hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge)
      · simp [cursorStep, hr, hbudget, hcutoff, hcap]
      · by_cases hready : projectionReady t r q.state
        · simp [cursorStep, hr, hbudget, hcutoff, hcap, hready]
        · simp [cursorStep, hr, hbudget, hcutoff, hcap, hready] at hstop
  · simp [cursorStep, hr, hbudget]

theorem cursorStep_state_eq_of_running_to_stopped {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (q : TrialCursor core)
    (hr : q.running = true)
    (hstop : (cursorStep t l N r g0 ξ order k q).running = false) :
    (cursorStep t l N r g0 ξ order k q).state = q.state := by
  classical
  by_cases hbudget : BudgetsHold t g0 q.state.hatG
  · by_cases hcutoff : k = N
    · simp [cursorStep, hr, hbudget, hcutoff]
    · by_cases hcap : 4 * l < maxWeight (trialWeights t r q.state q.previousRidge)
      · simp [cursorStep, hr, hbudget, hcutoff, hcap]
      · by_cases hready : projectionReady t r q.state
        · simp [cursorStep, hr, hbudget, hcutoff, hcap, hready]
        · simp [cursorStep, hr, hbudget, hcutoff, hcap, hready] at hstop
  · simp [cursorStep, hr, hbudget]

theorem runCursor_stop_lt_of_not_running {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q0 : TrialCursor core)
    (hq0 : q0.running = true) (k : ℕ)
    (hk : (runCursor t l N r g0 ξ order q0 k).running = false) :
    (runCursor t l N r g0 ξ order q0 k).stop < k := by
  induction k with
  | zero => simp [runCursor, hq0] at hk
  | succ k ih =>
      let q := runCursor t l N r g0 ξ order q0 k
      cases hr : q.running with
      | false =>
          have hqstop := ih hr
          have hfreeze : runCursor t l N r g0 ξ order q0 (k + 1) = q := by
            simp [runCursor, q, cursorStep_eq_of_not_running, hr]
          rw [hfreeze]
          exact lt_trans hqstop (Nat.lt_succ_self k)
      | true =>
          change (cursorStep t l N r g0 ξ order k q).running = false at hk
          have hqstop := cursorStep_stop_eq_of_running_to_stopped
            t l N r g0 ξ order k q hr hk
          have hqstop' :
              (cursorStep t l N r g0 ξ order k
                (runCursor t l N r g0 ξ order q0 k)).stop = k := by
            simpa [q] using hqstop
          simp only [runCursor]
          omega

theorem runCursor_eq_of_not_running {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q0 : TrialCursor core)
    {k m : ℕ} (hkm : k ≤ m) (hk : (runCursor t l N r g0 ξ order q0 k).running = false) :
    runCursor t l N r g0 ξ order q0 m = runCursor t l N r g0 ξ order q0 k := by
  induction hkm with
  | refl => rfl
  | @step m hkm ih =>
      have hm : (runCursor t l N r g0 ξ order q0 m).running = false := by
        rw [ih]
        exact hk
      change cursorStep t l N r g0 ξ order m
        (runCursor t l N r g0 ξ order q0 m) = runCursor t l N r g0 ξ order q0 k
      rw [cursorStep_eq_of_not_running t l N r g0 ξ order m
        (runCursor t l N r g0 ξ order q0 m) hm, ih]

theorem runCursor_running_of_lt_stop {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q0 : TrialCursor core)
    (hq0 : q0.stop = 0) (k : ℕ)
    (hk : k < (runCursor t l N r g0 ξ order q0 (N + 1)).stop) :
    (runCursor t l N r g0 ξ order q0 k).running = true := by
  have hN := runCursor_stop_le_limit t l N r g0 ξ order q0 hq0
  have hkN : k ≤ N + 1 := by omega
  cases hr : (runCursor t l N r g0 ξ order q0 k).running with
  | false =>
      have hfreeze := runCursor_eq_of_not_running t l N r g0 ξ order q0 hkN hr
      have hstopEq : (runCursor t l N r g0 ξ order q0 (N + 1)).stop =
          (runCursor t l N r g0 ξ order q0 k).stop :=
        congrArg (fun q : TrialCursor core => q.stop) hfreeze
      have hbound := runCursor_stop_le t l N r g0 ξ order q0 hq0 k
      omega
  | true => rfl

theorem runCursor_running_at_final_stop {core : Finset ι} (t l : ℝ) (N : ℕ)
    (r : ι → ℂ) (g0 : Matrix ι ι ℂ) (ξ : ι → ℝ)
    (order : ι ≃ Fin (Fintype.card ι)) (q0 : TrialCursor core)
    (hq0 : q0.running = true) (hqStop : q0.stop = 0) :
    (runCursor t l N r g0 ξ order q0
      (runCursor t l N r g0 ξ order q0 (N + 1)).stop).running = true := by
  have hbound := runCursor_stop_le_limit t l N r g0 ξ order q0 hqStop
  let k := (runCursor t l N r g0 ξ order q0 (N + 1)).stop
  have hk : k ≤ N + 1 := by dsimp [k]; omega
  cases hr : (runCursor t l N r g0 ξ order q0 k).running with
  | true => rfl
  | false =>
      have hlt := runCursor_stop_lt_of_not_running t l N r g0 ξ order q0 hq0 k hr
      have hfreeze := runCursor_eq_of_not_running t l N r g0 ξ order q0 hk hr
      have hstopEq : (runCursor t l N r g0 ξ order q0 (N + 1)).stop =
          (runCursor t l N r g0 ξ order q0 k).stop :=
        congrArg (fun q : TrialCursor core => q.stop) hfreeze
      dsimp [k] at hlt hstopEq
      omega

end AndersonAC.AgentS6Construct
