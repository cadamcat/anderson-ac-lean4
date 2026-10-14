import AndersonAC.AgentS6Row.TrialBridge
import AndersonAC.AgentS6.CapTelescope

noncomputable section
open Matrix ComplexConjugate MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.S6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma stronglyMeasurable_fin_select {m : MeasurableSpace Ω} {n : ℕ}
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    (x : Ω → Fin n) (hx : Measurable[m] x) (f : Fin n → Ω → E)
    (hf : ∀ j, StronglyMeasurable[m] (f j)) :
    StronglyMeasurable[m] (fun ω => f (x ω) ω) := by
  classical
  have he : (fun ω => f (x ω) ω) = fun ω => ∑ j : Fin n, if x ω = j then f j ω else 0 := by
    funext ω
    rw [Finset.sum_eq_single (x ω)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  rw [he]
  refine Finset.stronglyMeasurable_fun_sum (Finset.univ : Finset (Fin n)) fun j _ => ?_
  exact StronglyMeasurable.ite (hx (MeasurableSet.singleton j))
    (hf j) stronglyMeasurable_const

variable {n : ℕ} {core : Finset (Fin n)} {t : ℝ} {r : Ω → Fin n → ℂ}
  {g0 : Ω → Matrix (Fin n) (Fin n) ℂ} {order : Fin n ≃ Fin (Fintype.card (Fin n))}

/-- A row survives a running heat precisely when it is active, exterior and distinct from the pivot. -/
def survivorEvent (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) : Set Ω :=
  {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active ∧ i ≠ q.pivot k ω ∧ i ∉ core}

lemma survivorEvent_measurable (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (i : Fin n) : MeasurableSet[q.history k] (survivorEvent q k i) := by
  have ha := stoppedTrial_running_active_measurable q k i
  have hp : MeasurableSet[q.history k] {ω | i ≠ q.pivot k ω} := by
    have hh := (q.pivot_predictable k) (MeasurableSet.singleton i)
    have he : {ω | i ≠ q.pivot k ω} = {ω | q.pivot k ω = i}ᶜ := by ext ω; simp [eq_comm]
    rw [he]
    exact hh.compl
  by_cases hic : i ∈ core
  · have he : survivorEvent q k i = ∅ := by ext ω; simp [survivorEvent, hic]
    rw [he]
    exact @MeasurableSet.empty Ω (q.history k)
  · have he : survivorEvent q k i = {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active} ∩
        {ω | i ≠ q.pivot k ω} := by ext ω; simp [survivorEvent, hic, and_assoc]
    rw [he]
    exact ha.inter hp

lemma recordedIncrement_eq_indicator (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (i : Fin n) :
    (fun ω => recordedLeverageIncrement q k ω i) = (survivorEvent q k i).indicator
      (fun ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω) i -
        trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i) := by
  classical
  funext ω
  unfold recordedLeverageIncrement
  by_cases hk : k < q.stop ω
  · obtain ⟨_, _, hact, _, _, _⟩ := q.heat k ω hk
    have he : i ∈ (q.state (k + 1) ω).active ↔ i ∈ (q.state k ω).active ∧ i ≠ q.pivot k ω := by
      rw [hact, Finset.mem_erase]
      exact and_comm
    simp only [he]
    by_cases hi : i ∈ (q.state k ω).active <;> by_cases hx : i = q.pivot k ω <;>
      by_cases hc : i ∈ core <;> simp [hk, hi, hx, hc, survivorEvent]
  · simp [hk, survivorEvent]

/-- Restriction of `heatV` to running prestates is history-measurable. -/
lemma heatV_running_stronglyMeasurable (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (i : Fin n) :
    StronglyMeasurable[q.history k] (fun ω => if k < q.stop ω then heatV q k ω i else 0) := by
  classical
  have hrj : ∀ j : Fin n, StronglyMeasurable[q.history k] (fun ω => r ω j) := fun j =>
    (continuous_apply j).comp_stronglyMeasurable
      (q.damping_adapted.mono (q.history.mono (Nat.zero_le k)))
  have hrx := stronglyMeasurable_fin_select (q.pivot k) (q.pivot_predictable k)
    (fun j ω => r ω j) hrj
  have hgix := stronglyMeasurable_fin_select (q.pivot k) (q.pivot_predictable k)
    (fun j ω => (q.state k ω).hatG i j) (q.entries_adapted k i)
  have hpi := Complex.imCLM.continuous.comp_stronglyMeasurable (hrj i)
  have hpx := Complex.imCLM.continuous.comp_stronglyMeasurable hrx
  have hroot : StronglyMeasurable[q.history k]
      (fun ω => (Real.sqrt ((r ω i).im / (r ω (q.pivot k ω)).im) : ℂ)) := by
    exact Complex.continuous_ofReal.comp_stronglyMeasurable
      (Real.continuous_sqrt.comp_stronglyMeasurable (hpi.div hpx))
  have hval : StronglyMeasurable[q.history k]
      (fun ω => (Real.sqrt t : ℂ) * (q.state k ω).hatG i (q.pivot k ω) *
        (Real.sqrt ((r ω i).im / (r ω (q.pivot k ω)).im) : ℂ)) :=
    (stronglyMeasurable_const.mul hgix).mul hroot
  have hE := stoppedTrial_running_active_measurable q k i
  have hmask := hval.indicator hE
  convert hmask using 1
  funext ω
  by_cases hk : k < q.stop ω
  · obtain ⟨hx, _, _, _, _, _⟩ := q.heat k ω hk
    by_cases hi : i ∈ (q.state k ω).active
    · rw [if_pos hk, Set.indicator_of_mem (show ω ∈ {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active} from ⟨hk, hi⟩)]
      unfold heatV
      rw [dif_pos hi, dif_pos hx]
      simp only [scaledInverse, Matrix.smul_apply, smul_eq_mul]
      rw [← AndersonAC.AgentS6.hatG_eq_trialInverse q k ω hk.le ⟨i, hi⟩ ⟨_, hx⟩]
    · simp [hk, hi, heatV]
  · simp [hk]

end AndersonAC.AgentS6Row
