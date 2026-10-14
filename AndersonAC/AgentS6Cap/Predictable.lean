import AndersonAC.AgentS6Cap.Envelope
import AndersonAC.AgentS6Cap.LocalInput

/-! Predictable row-energy terms indexed by the adapted pivot. -/

noncomputable section
open scoped BigOperators

namespace AndersonAC.AgentS6

open AndersonAC.S6 MeasureTheory

def pivotEntrySq
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (i : Fin n) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin n, if q.pivot k ω = j then
    ‖scaledInverse t (g0 ω) i j‖ ^ 2 else 0

theorem pivotEntrySq_eq
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (i : Fin n) (k : ℕ) (ω : Ω) :
    pivotEntrySq q i k ω = ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 := by
  classical
  unfold pivotEntrySq
  rw [Finset.sum_eq_single (q.pivot k ω)]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem pivotEntrySq_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (i : Fin n) (k : ℕ) :
    StronglyMeasurable[q.history k] (pivotEntrySq q i k) := by
  classical
  have hpiv : Measurable[q.history k] (q.pivot k) := q.pivot_predictable k
  have hentry : ∀ j : Fin n,
      Measurable[q.history k] (fun ω => ‖scaledInverse t (g0 ω) i j‖ ^ 2) := by
    intro j
    have hg0sm : StronglyMeasurable[q.history 0] (fun ω => g0 ω i j) := by
      simpa only [q.start_entries] using (q.entries_adapted 0 i j)
    have hg0 : Measurable[q.history k] (fun ω => g0 ω i j) :=
      (hg0sm.mono (q.history.mono (Nat.zero_le k))).measurable
    have hscaled : Measurable[q.history k]
        (fun ω => scaledInverse t (g0 ω) i j) := by
      change Measurable[q.history k]
        (fun ω => (Real.sqrt t : ℂ) * g0 ω i j)
      exact measurable_const.mul hg0
    exact (measurable_norm.comp hscaled).pow_const 2
  have hmeas : Measurable[q.history k] (pivotEntrySq q i k) := by
    unfold pivotEntrySq
    apply Finset.measurable_sum
    intro j hj
    have hset : MeasurableSet[q.history k] {ω | q.pivot k ω = j} :=
      (measurableSet_singleton j).preimage hpiv
    exact Measurable.ite hset (hentry j) measurable_const
  exact hmeas.stronglyMeasurable

def rowActiveRun
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (i : Fin n) (k : ℕ) : Set Ω :=
  {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active ∧ i ∉ core}

theorem rowActiveRun_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (i : Fin n) (k : ℕ) :
    MeasurableSet[q.history k] (rowActiveRun q i k) := by
  by_cases hcore : i ∈ core
  · simp [rowActiveRun, hcore]
  · simpa [rowActiveRun, hcore] using measurableSet_running_active q k i

theorem recordedIncrement_rowActiveRun
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (i : Fin n) (k : ℕ) :
    (fun ω => recordedLeverageIncrement q k ω i) =
      (rowActiveRun q i k).indicator (fun ω => recordedLeverageIncrement q k ω i) := by
  funext ω
  by_cases hcore : i ∈ core
  · simp [recordedLeverageIncrement, rowActiveRun, hcore]
  · by_cases hrun : k < q.stop ω
    · by_cases hi : i ∈ (q.state k ω).active
      · simp [recordedLeverageIncrement, rowActiveRun, hcore, hrun, hi]
      · have hpost : i ∉ (q.state (k + 1) ω).active := by
          intro hpost
          have hsub := active_succ_subset q k ω hrun
          exact hi (hsub hpost)
        simp [recordedLeverageIncrement, rowActiveRun, hcore, hrun, hi, hpost]
    · simp [recordedLeverageIncrement, rowActiveRun, hcore, hrun]

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.pivotEntrySq_eq
#print axioms AndersonAC.AgentS6.pivotEntrySq_stronglyMeasurable
#print axioms AndersonAC.AgentS6.rowActiveRun_measurable
#print axioms AndersonAC.AgentS6.recordedIncrement_rowActiveRun
