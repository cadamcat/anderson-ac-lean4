import AndersonAC.AgentS6Cap.Energy
import AndersonAC.AgentS6Stream.TwoSidedStreamTail

/-! Predictability and measurability facts for each recorded row stream. -/

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

theorem active_iff_past_pivots
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω)
    (k : ℕ) (hk : k ≤ q.stop ω) (i : Fin n) :
    i ∈ (q.state k ω).active ↔
      ∀ j ∈ Finset.range k, q.pivot j ω ≠ i := by
  induction k with
  | zero =>
      simp [q.initial_active ω]
  | succ k ih =>
      have hrun : k < q.stop ω := by omega
      obtain ⟨hx, -, hact, -, -⟩ := q.heat k ω hrun
      rw [hact, Finset.mem_erase, ih (by omega)]
      constructor
      · rintro ⟨hneq, hpast⟩ j hj
        have hj' : j < k + 1 := Finset.mem_range.mp hj
        by_cases hjk : j = k
        · subst j
          exact hneq.symm
        · exact hpast j (Finset.mem_range.mpr (by omega))
      · intro hpast
        constructor
        · exact (hpast k (Finset.mem_range.mpr (by omega))).symm
        · intro j hj
          have hjlt : j < k := Finset.mem_range.mp hj
          exact hpast j (Finset.mem_range.mpr (by omega))

theorem measurableSet_running_active
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    MeasurableSet[q.history k]
      {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active} := by
  have hrun : MeasurableSet[q.history k] {ω | k < q.stop ω} := by
    convert (q.stopping k).compl using 1 <;> ext ω <;> simp
  have hpast : MeasurableSet[q.history k]
      {ω | ∀ j ∈ Finset.range k, q.pivot j ω ≠ i} := by
    rw [show {ω | ∀ j ∈ Finset.range k, q.pivot j ω ≠ i} =
      ⋂ j ∈ Finset.range k, {ω | q.pivot j ω ≠ i} by ext; simp]
    apply Finset.measurableSet_biInter
    intro j hj
    have hjlt : j < k := Finset.mem_range.mp hj
    have hpiv : Measurable[q.history k] (q.pivot j) :=
      (q.pivot_predictable j).mono (q.history.mono hjlt.le) le_rfl
    exact ((measurableSet_singleton i).preimage hpiv).compl
  have hEq : {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active} =
      {ω | k < q.stop ω ∧ ∀ j ∈ Finset.range k, q.pivot j ω ≠ i} := by
    ext ω
    constructor
    · rintro ⟨hrunω, hi⟩
      exact ⟨hrunω, (active_iff_past_pivots q ω k (Nat.le_of_lt hrunω) i).1 hi⟩
    · rintro ⟨hrunω, hp⟩
      exact ⟨hrunω, (active_iff_past_pivots q ω k (Nat.le_of_lt hrunω) i).2 hp⟩
  rw [hEq]
  exact hrun.inter hpast

/-- The active-row mask after heat `k` is predictable at time `k+1`. -/
theorem measurableSet_running_active_after
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    MeasurableSet[q.history (k + 1)]
      {ω | k < q.stop ω ∧ i ∈ (q.state (k + 1) ω).active} := by
  have hrun0 : MeasurableSet[q.history k] {ω | k < q.stop ω} := by
    convert (q.stopping k).compl using 1 <;> ext ω <;> simp
  have hrun : MeasurableSet[q.history (k + 1)] {ω | k < q.stop ω} :=
    q.history.mono (Nat.le_succ k) _ hrun0
  have hpast : MeasurableSet[q.history (k + 1)]
      {ω | ∀ j ∈ Finset.range (k + 1), q.pivot j ω ≠ i} := by
    rw [show {ω | ∀ j ∈ Finset.range (k + 1), q.pivot j ω ≠ i} =
      ⋂ j ∈ Finset.range (k + 1), {ω | q.pivot j ω ≠ i} by ext; simp]
    apply Finset.measurableSet_biInter
    intro j hj
    have hjk : j ≤ k + 1 := by
      have hj' : j < k + 1 := Finset.mem_range.mp hj
      omega
    have hpiv : Measurable[q.history (k + 1)] (q.pivot j) :=
      (q.pivot_predictable j).mono (q.history.mono hjk) le_rfl
    exact ((measurableSet_singleton i).preimage hpiv).compl
  have hEq : {ω | k < q.stop ω ∧ i ∈ (q.state (k + 1) ω).active} =
      {ω | k < q.stop ω ∧ ∀ j ∈ Finset.range (k + 1), q.pivot j ω ≠ i} := by
    ext ω
    constructor
    · rintro ⟨hrunω, hi⟩
      refine ⟨hrunω, ?_⟩
      exact (active_iff_past_pivots q ω (k + 1) (Nat.succ_le_of_lt hrunω) i).1 hi
    · rintro ⟨hrunω, hp⟩
      refine ⟨hrunω, ?_⟩
      exact (active_iff_past_pivots q ω (k + 1) (Nat.succ_le_of_lt hrunω) i).2 hp
  rw [hEq]
  exact hrun.inter hpast

theorem trialWeight_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    StronglyMeasurable[q.history k]
      (fun ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i) := by
  have hcross : Measurable[q.history k] (fun ω => trialCross t (r ω) (q.state k ω)) := by
    refine @Measurable.of_eval_matrix (Fin n) {b // b ∈ core} ℂ _ Ω (q.history k) _
      (fun a b => ?_)
    exact ((continuous_id.matrix_elem a b).comp_stronglyMeasurable
      (q.cross_adapted k)).measurable
  have hridge : Measurable[q.history k] (q.ridge k) := (q.ridge_predictable k).measurable
  have hpair : Measurable[q.history k]
      (fun ω => (trialCross t (r ω) (q.state k ω), q.ridge k ω)) :=
    Measurable.prodMk hcross hridge
  change StronglyMeasurable[q.history k]
    (fun ω => AndersonAC.S6.leverage
      (trialCross t (r ω) (q.state k ω)) (q.ridge k ω) i)
  exact ((AndersonAC.AgentS6.measurable_leverage i).comp hpair).stronglyMeasurable

/-- A recorded leverage increment is revealed by the next history. -/
theorem recordedLeverageIncrement_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    StronglyMeasurable[q.history (k + 1)] (fun ω => recordedLeverageIncrement q k ω i) := by
  by_cases hcore : i ∈ core
  · have hzero : (fun ω => recordedLeverageIncrement q k ω i) = fun _ => 0 := by
      funext ω
      simp [recordedLeverageIncrement, hcore]
    rw [hzero]
    exact stronglyMeasurable_const
  · let E : Set Ω := {ω | k < q.stop ω ∧ i ∈ (q.state (k + 1) ω).active}
    have hE : MeasurableSet[q.history (k + 1)] E := measurableSet_running_active_after q k i
    have hpost : StronglyMeasurable[q.history (k + 1)]
        (fun ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω) i) := by
      have hcross : Measurable[q.history (k + 1)]
          (fun ω => trialCross t (r ω) (q.state (k + 1) ω)) := by
        refine @Measurable.of_eval_matrix (Fin n) {b // b ∈ core} ℂ _ Ω
          (q.history (k + 1)) _ (fun a b => ?_)
        exact ((continuous_id.matrix_elem a b).comp_stronglyMeasurable
          (q.cross_adapted (k + 1))).measurable
      have hridge : StronglyMeasurable[q.history (k + 1)] (q.ridge k) :=
        (q.ridge_predictable k).mono (q.history.mono (Nat.le_succ k))
      have hpair : Measurable[q.history (k + 1)]
          (fun ω => (trialCross t (r ω) (q.state (k + 1) ω), q.ridge k ω)) :=
        Measurable.prodMk hcross hridge.measurable
      change StronglyMeasurable[q.history (k + 1)]
        (fun ω => AndersonAC.S6.leverage
          (trialCross t (r ω) (q.state (k + 1) ω)) (q.ridge k ω) i)
      exact ((AndersonAC.AgentS6.measurable_leverage i).comp hpair).stronglyMeasurable
    have hpre : StronglyMeasurable[q.history (k + 1)]
        (fun ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i) :=
      (trialWeight_stronglyMeasurable q k i).mono (q.history.mono (Nat.le_succ k))
    have hdiff := hpost.sub hpre
    have hEq : (fun ω => recordedLeverageIncrement q k ω i) =
        E.indicator (fun ω =>
          trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω) i -
            trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i) := by
      funext ω
      by_cases hω : ω ∈ E
      · obtain ⟨hrunω, hactiveω⟩ := hω
        simp [recordedLeverageIncrement, E, hcore, hrunω, hactiveω]
      · by_cases hrunω : k < q.stop ω
        · by_cases hactiveω : i ∈ (q.state (k + 1) ω).active
          · exact (hω ⟨hrunω, hactiveω⟩).elim
          · simp [recordedLeverageIncrement, E, hcore, hrunω, hactiveω]
        · simp [recordedLeverageIncrement, E, hrunω]
    rw [hEq]
    exact StronglyMeasurable.ite hE hdiff stronglyMeasurable_const

theorem rowCrossing_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t l : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (N : ℕ) (i : Fin n) :
    MeasurableSet {ω | ∃ s ≤ N,
      l / 2 < |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i|} := by
  have hz : ∀ k, Measurable (fun ω => recordedLeverageIncrement q k ω i) := by
    intro k
    exact ((recordedLeverageIncrement_stronglyMeasurable q k i).mono
      (q.history.le (k + 1))).measurable
  have hsum : ∀ s, Measurable
      (fun ω => ∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i) := by
    intro s
    exact Finset.measurable_sum _ fun k _ => hz k
  let U : Set Ω := ⋃ s ∈ Finset.range (N + 1),
    {ω | l / 2 < |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i|}
  have hEq : {ω | ∃ s ≤ N,
      l / 2 < |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i|} = U := by
    ext ω
    simp [U, Nat.lt_succ_iff]
  rw [hEq]
  apply Finset.measurableSet_biUnion
  intro s hs
  exact measurableSet_lt measurable_const ((measurable_abs.comp (hsum s)))

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.active_iff_past_pivots
#print axioms AndersonAC.AgentS6.measurableSet_running_active_after
#print axioms AndersonAC.AgentS6.trialWeight_stronglyMeasurable
#print axioms AndersonAC.AgentS6.recordedLeverageIncrement_stronglyMeasurable
