import AndersonAC.AgentS6Budget.PivotEnergy
import AndersonAC.AgentS6.Decomposition

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

theorem active_iff_no_pivot (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (hk : k ≤ q.stop ω) (i : Fin n) :
    i ∈ (q.state k ω).active ↔ ∀ j < k, q.pivot j ω ≠ i := by
  induction k with
  | zero => simp [q.initial_active ω]
  | succ k ih =>
    obtain ⟨-, -, hact, -⟩ := q.heat k ω (by omega)
    rw [hact, Finset.mem_erase, ih (by omega)]
    constructor
    · rintro ⟨hne, hprev⟩ j hj
      by_cases hjk : j < k
      · exact hprev j hjk
      · have : j = k := by omega
        subst j
        exact Ne.symm hne
    · intro h
      exact ⟨Ne.symm (h k (by omega)), fun j hj => h j (by omega)⟩

def survivorEvent (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) : Set Ω :=
  {ω | k < q.stop ω ∧ ∀ j ≤ k, q.pivot j ω ≠ i}

theorem mem_survivorEvent (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (i : Fin n) :
    ω ∈ survivorEvent q k i ↔ k < q.stop ω ∧ i ∈ (q.state (k + 1) ω).active := by
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, (active_iff_no_pivot q (k + 1) ω (by omega) i).mpr
      (fun j hj => h j (by omega))⟩
  · rintro ⟨hk, hi⟩
    exact ⟨hk, fun j hj => (active_iff_no_pivot q (k + 1) ω (by omega) i).mp hi j (by omega)⟩

theorem survivorEvent_measurable (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (i : Fin n) : MeasurableSet[q.history k] (survivorEvent q k i) := by
  have hall : MeasurableSet[q.history k]
      (⋂ j : ℕ, ⋂ (_ : j ≤ k), {ω | q.pivot j ω ≠ i}) := by
    apply MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => ?_
    exact (measurableSet_eq_fun ((q.pivot_predictable j).mono (q.history.mono hj) le_rfl)
      measurable_const).compl
  have hall' : MeasurableSet[q.history k] {ω | ∀ j ≤ k, q.pivot j ω ≠ i} := by
    convert hall using 1
    ext ω
    simp
  exact (running_measurableSet q k).inter hall'

theorem stronglyMeasurable_select_fin {m : MeasurableSpace Ω} (x : Ω → Fin n)
    (hx : Measurable[m] x) (f : Fin n → Ω → ℂ)
    (hf : ∀ i, StronglyMeasurable[m] (f i)) :
    StronglyMeasurable[m] (fun ω => f (x ω) ω) := by
  classical
  have h : StronglyMeasurable[m]
      (fun ω => ∑ i : Fin n, if x ω = i then f i ω else 0) := by
    have he : (fun ω => ∑ i : Fin n, if x ω = i then f i ω else 0) =
        ∑ i : Fin n, (fun ω => if x ω = i then f i ω else 0) := by
      funext ω
      simp
    rw [he]
    apply Finset.stronglyMeasurable_sum
    intro i _
    exact (hf i).ite (measurableSet_eq_fun hx measurable_const) stronglyMeasurable_const
  simpa using h

theorem pivot_left_adapted (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    StronglyMeasurable[q.history k] (fun ω => (q.state k ω).hatG i (q.pivot k ω)) :=
  stronglyMeasurable_select_fin (q.pivot k) (q.pivot_predictable k)
    (fun j ω => (q.state k ω).hatG i j) (q.entries_adapted k i)

theorem pivot_right_adapted (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (j : Fin n) :
    StronglyMeasurable[q.history k] (fun ω => (q.state k ω).hatG (q.pivot k ω) j) :=
  stronglyMeasurable_select_fin (q.pivot k) (q.pivot_predictable k)
    (fun i ω => (q.state k ω).hatG i j) (fun i => q.entries_adapted k i j)

theorem pivot_diagonal_adapted (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    StronglyMeasurable[q.history k]
      (fun ω => (q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)) :=
  stronglyMeasurable_select_fin (q.pivot k) (q.pivot_predictable k)
    (fun i ω => (q.state k ω).hatG i i) (fun i => q.entries_adapted k i i)

theorem pivot_damping_adapted (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    StronglyMeasurable[q.history k] (fun ω => r ω (q.pivot k ω)) := by
  apply stronglyMeasurable_select_fin (q.pivot k) (q.pivot_predictable k)
    (fun i ω => r ω i)
  intro i
  exact (continuous_apply i).comp_stronglyMeasurable
    (q.damping_adapted.mono (q.history.mono (Nat.zero_le k)))

open Classical in
def entryFactor (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i j : Fin n) : Ω → ℂ :=
  (survivorEvent q k i ∩ survivorEvent q k j).indicator
    (fun ω => (Real.sqrt t : ℂ) *
      (q.state k ω).hatG i (q.pivot k ω) * (q.state k ω).hatG (q.pivot k ω) j)

theorem entryFactor_adapted (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (i j : Fin n) : StronglyMeasurable[q.history k] (entryFactor q k i j) :=
  ((stronglyMeasurable_const.mul (pivot_left_adapted q k i)).mul
    (pivot_right_adapted q k j)).indicator
      ((survivorEvent_measurable q k i).inter (survivorEvent_measurable q k j))

theorem coefficient_times_entryFactor (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (i j : Fin n) :
    heatCoefficient t (r ω (q.pivot k ω)) ((q.state k ω).hatG (q.pivot k ω) (q.pivot k ω))
      (q.residual k ω) * entryFactor q k i j ω =
      if k < q.stop ω then hatIncrement q k ω i j else 0 := by
  classical
  unfold entryFactor hatIncrement
  by_cases hk : k < q.stop ω
  · rw [if_pos hk]
    by_cases hij : i ∈ (q.state (k + 1) ω).active ∧ j ∈ (q.state (k + 1) ω).active
    · rw [if_pos hij, Set.indicator_of_mem
        (show ω ∈ survivorEvent q k i ∩ survivorEvent q k j from
          ⟨(mem_survivorEvent q k ω i).mpr ⟨hk, hij.1⟩,
            (mem_survivorEvent q k ω j).mpr ⟨hk, hij.2⟩⟩)]
      ring
    · rw [if_neg hij, Set.indicator_of_notMem]
      · simp
      · rintro ⟨hi, hj⟩
        exact hij ⟨((mem_survivorEvent q k ω i).mp hi).2,
          ((mem_survivorEvent q k ω j).mp hj).2⟩
  · rw [if_neg hk, Set.indicator_of_notMem]
    · simp
    · exact fun h => hk h.1.1

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.survivorEvent_measurable
#print axioms AndersonAC.AgentS6Budget.entryFactor_adapted
#print axioms AndersonAC.AgentS6Budget.coefficient_times_entryFactor
