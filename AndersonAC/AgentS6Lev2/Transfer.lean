import AndersonAC.AgentS6Lev2.Kernel

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Matrix

namespace AndersonAC.AgentS6Lev2
open AndersonAC.S6 AndersonAC.AgentS6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
  {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

abbrev TrialIndex (n : ℕ) := Σ A : Finset (Fin n), A

def coreOn (core A : Finset (Fin n)) : Finset A := A.attach.filter (fun i => i.val ∈ core)

def prestateEvent (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ)
    (j : TrialIndex n) : Set Ω :=
  {ω | k < q.stop ω ∧ (q.state k ω).active = j.1 ∧ q.pivot k ω = j.2.val}

theorem measurable_prestateEvent (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (j : TrialIndex n) : MeasurableSet[q.history k] (prestateEvent q k j) := by
  have hA : MeasurableSet[q.history k]
      {ω | ∀ i, (k < q.stop ω ∧ i ∈ (q.state k ω).active) ↔ i ∈ j.1} := by
    rw [show {ω | ∀ i, (k < q.stop ω ∧ i ∈ (q.state k ω).active) ↔ i ∈ j.1} =
      ⋂ i : Fin n, {ω | (k < q.stop ω ∧ i ∈ (q.state k ω).active) ↔ i ∈ j.1} by ext; simp]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ j.1
    · simpa [hi] using AndersonAC.AgentS6Row.stoppedTrial_running_active_measurable q k i
    · have heq : {ω | (k < q.stop ω ∧ i ∈ (q.state k ω).active) ↔ i ∈ j.1} =
          {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active}ᶜ := by ext ω; simp [hi]
      rw [heq]
      exact (AndersonAC.AgentS6Row.stoppedTrial_running_active_measurable q k i).compl
  have hEq : prestateEvent q k j = {ω | k < q.stop ω} ∩
      {ω | ∀ i, (k < q.stop ω ∧ i ∈ (q.state k ω).active) ↔ i ∈ j.1} ∩
      {ω | q.pivot k ω = j.2.val} := by
    ext ω
    simp only [prestateEvent, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.ext_iff]
    by_cases hk : k < q.stop ω <;> simp [hk, and_assoc]
  rw [hEq]
  exact ((running_measurableSet q k).inter hA).inter
    ((measurableSet_singleton j.2.val).preimage (q.pivot_predictable k))

open Classical in
def kernelFn (square : Bool) (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (p : Ω × ℝ) : ℝ :=
  ∑ j : TrialIndex n, if p.1 ∈ prestateEvent q k j then
    l64Delta square (recoveredM q k j.1 p.1) t (fun i : j.1 => r p.1 i)
      (coreOn core j.1) j.2 (q.ridge k p.1) p.2 else 0

theorem stronglyMeasurable_kernelFn (square : Bool)
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    StronglyMeasurable[(q.history k).prod (borel ℝ)] (kernelFn square q k) := by
  classical
  letI : MeasurableSpace (Ω × ℝ) := (q.history k).prod (borel ℝ)
  have hfst : @Measurable (Ω × ℝ) Ω ((q.history k).prod (borel ℝ)) (q.history k) Prod.fst :=
    @measurable_fst Ω ℝ (q.history k) (borel ℝ)
  have hsnd : Measurable (Prod.snd : Ω × ℝ → ℝ) :=
    @measurable_snd Ω ℝ (q.history k) (borel ℝ)
  have hr : Measurable[q.history k] (r : Ω → Fin n → ℂ) :=
    (q.damping_adapted.mono (q.history.mono (Nat.zero_le k))).measurable
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro j _
  have hrestrict : Continuous (fun v : Fin n → ℂ => fun i : j.1 => v i.val) :=
    continuous_pi fun i => continuous_apply i.val
  apply Measurable.ite ((measurable_prestateEvent q k j).preimage hfst)
  · exact measurable_l64Delta square t (coreOn core j.1) j.2
      ((measurable_recoveredM q k j.1).comp hfst)
      ((hrestrict.measurable.comp hr).comp hfst)
      ((q.ridge_predictable k).measurable.comp hfst) hsnd
  · exact measurable_const

theorem kernelFn_eq_running (square : Bool)
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) (hk : k < q.stop ω)
    (hx : q.pivot k ω ∈ (q.state k ω).active) (ht : 0 < t)
    (hr : ∀ i, 0 < (r ω i).im) (y : ℝ) :
    kernelFn square q k (ω, y) = l64Delta square (q.state k ω).M t
      (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω))
      ⟨q.pivot k ω, hx⟩ (q.ridge k ω) y := by
  classical
  let j0 : TrialIndex n := ⟨(q.state k ω).active, ⟨q.pivot k ω, hx⟩⟩
  have hgate : ω ∈ prestateEvent q k j0 := ⟨hk, rfl, rfl⟩
  unfold kernelFn
  rw [Finset.sum_eq_single j0]
  · rw [if_pos hgate]
    dsimp [j0]
    rw [recoveredM_eq q k ω hk.le ht hr]
    rfl
  · intro j _ hj
    have hnot : ω ∉ prestateEvent q k j := by
      intro h
      apply hj
      rcases j with ⟨A, x⟩
      rcases h with ⟨_, hA, hxval⟩
      dsimp at hA hxval
      subst A
      dsimp [j0]
      congr 1
      exact Subtype.ext hxval.symm
    rw [if_neg hnot]
  · simp

theorem kernelFn_eq_stopped (square : Bool)
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω)
    (hk : ¬ k < q.stop ω) (y : ℝ) : kernelFn square q k (ω, y) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (fun h => hk h.1)]

def trialDelta (square : Bool) (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) : ℝ :=
  if square then
    squareWeight (onRunning (fun k => {ω | k < q.stop ω}) (postW q) k ω) -
      squareWeight (onRunning (fun k => {ω | k < q.stop ω}) (preW q) k ω)
  else totalWeight (onRunning (fun k => {ω | k < q.stop ω}) (postW q) k ω) -
      totalWeight (onRunning (fun k => {ω | k < q.stop ω}) (preW q) k ω)

theorem integrable_trialDelta (square : Bool) (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    Integrable (trialDelta square q k) μ := by
  cases square
  · exact (integrable_total_onRunning_post q μ k).sub (integrable_total_onRunning_pre q μ k)
  · exact (integrable_square_onRunning_post q μ k).sub (integrable_square_onRunning_pre q μ k)

theorem kernelFn_at_residual (square : Bool)
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t)
    (hr : ∀ ω i, 0 < (r ω i).im) (k : ℕ) :
    (fun ω => kernelFn square q k (ω, q.residual k ω)) = trialDelta square q k := by
  funext ω
  by_cases hk : k < q.stop ω
  · have hheat := q.heat k ω hk
    obtain ⟨hx, hxcore, -⟩ := q.heat k ω hk
    rw [kernelFn_eq_running square q k ω hk hx ht (hr ω)]
    have hA := postA_eq_sum (q.state k ω) (q.state (k + 1) ω) (r ω)
      (q.pivot k ω) (q.residual k ω) (hr ω) ht hheat hx hxcore (q.ridge k ω)
    have hP := postP_eq_sum (q.state k ω) (q.state (k + 1) ω) (r ω)
      (q.pivot k ω) (q.residual k ω) (hr ω) ht hheat hx hxcore (q.ridge k ω)
    cases square <;> simp only [l64Delta, trialDelta, Bool.false_eq_true, ↓reduceIte,
      hA, hP, preA_eq_sum, preP_eq_sum, onRunning, Set.mem_setOf_eq, hk, preW, postW]
  · rw [kernelFn_eq_stopped square q k ω hk]
    cases square <;> simp [trialDelta, onRunning, hk, totalWeight, squareWeight]

theorem condExp_trialDelta (square : Bool) (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t)
    (hr : ∀ ω i, 0 < (r ω i).im) (k : ℕ) :
    μ[trialDelta square q k | q.history k] =ᵐ[μ]
      fun ω => ∫ y, kernelFn square q k (ω, y) ∂residualLaw μ q k ω := by
  have hid : @Measurable Ω Ω mΩ (q.history k) id := by
    apply Measurable.of_comap_le
    simpa only [MeasurableSpace.comap_id] using q.history.le k
  have h := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
    (μ := μ) (X := (id : Ω → Ω)) (Y := q.residual k) (mβ := q.history k)
    hid ((q.residual_revealed k).measurable.mono (q.history.le (k + 1)) le_rfl).aemeasurable
    (stronglyMeasurable_kernelFn square q k)
    (by rw [show (fun ω => kernelFn square q k (id ω, q.residual k ω)) =
        trialDelta square q k from kernelFn_at_residual square q ht hr k]
        exact integrable_trialDelta square μ q k)
  simpa only [MeasurableSpace.comap_id, id_eq, residualLaw, kernelFn_at_residual square q ht hr k] using h

end AndersonAC.AgentS6Lev2

#print axioms AndersonAC.AgentS6Lev2.condExp_trialDelta
