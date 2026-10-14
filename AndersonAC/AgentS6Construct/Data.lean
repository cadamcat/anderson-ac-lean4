import AndersonAC.AgentS6Construct.Procedure

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

def runAt (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    ℕ → TrialCursor core :=
  runCursor t (leverageScale t) (heatLimit t) (r ω)
    (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
    (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω))

def stateAt (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (ω : Ω) :
    TrialState core := runAt core t r M0 hM ξ order ω k |>.state

def ridgeAt (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (ω : Ω) : ℝ :=
  selectedRidge t (r ω) (stateAt core t r M0 hM ξ order k ω)
    (runAt core t r M0 hM ξ order ω k).previousRidge

def pivotAt (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (ω : Ω) : ι :=
  leastMaximizerTotal order
    (trialWeights t (r ω) (stateAt core t r M0 hM ξ order k ω)
      (ridgeAt core t r M0 hM ξ order k ω))

def residualAt (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (ω : Ω) : ℝ :=
  ξ (pivotAt core t r M0 hM ξ order k ω) ω

def stopAt (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) : ℕ :=
  (runAt core t r M0 hM ξ order ω (heatLimit t + 1)).stop

def outcomeAt (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) : TrialOutcome :=
  (runAt core t r M0 hM ξ order ω (heatLimit t + 1)).outcome

theorem stateAt_zero (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    stateAt core t r M0 hM ξ order 0 ω =
      initialState core (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω) := rfl

theorem ridgeAt_zero (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    ridgeAt core t r M0 hM ξ order 0 ω =
      chooseRidge (trialCross t (r ω)
        (initialState core (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)))
        (leverageScale t) ((leverageScale t) ^ (-2 : ℤ)) := rfl

theorem stateAt_zero_active (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    (stateAt core t r M0 hM ξ order 0 ω).active = Finset.univ := by
  rw [stateAt_zero]
  exact initialState_active _ _ _ _

theorem stateAt_zero_entries (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    (stateAt core t r M0 hM ξ order 0 ω).hatG = activeInverse (M0 ω) t (r ω) := by
  rw [stateAt_zero]
  exact initialState_entries _ _ _ _

theorem stateAt_zero_inverse (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω)
    (i j : {i // i ∈ (stateAt core t r M0 hM ξ order 0 ω).active}) :
    trialInverse t (r ω) (stateAt core t r M0 hM ξ order 0 ω) i j =
      activeInverse (M0 ω) t (r ω) i j := by
  simpa [stateAt, runAt, runCursor, initialCursor] using
    initialState_inverse core (M0 ω) (activeInverse (M0 ω) t (r ω))
      (hM ω) t (r ω) i j

theorem runAt_stop_le (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) :
    stopAt core t r M0 hM ξ order ω ≤ heatLimit t := by
  simpa [stopAt, runAt, initialCursor] using
    runCursor_stop_le_limit t (leverageScale t) (heatLimit t) (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
      (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)) rfl

theorem runAt_running_before_stop (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω) (k : ℕ)
    (hk : k < stopAt core t r M0 hM ξ order ω) :
    (runAt core t r M0 hM ξ order ω k).running = true := by
  simpa [stopAt, runAt, initialCursor] using
    runCursor_running_of_lt_stop t (leverageScale t) (heatLimit t) (r ω)
      (activeInverse (M0 ω) t (r ω)) (fun i => ξ i ω) order
      (initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)) rfl k hk

end AndersonAC.AgentS6Construct
