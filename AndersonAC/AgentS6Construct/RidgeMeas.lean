import AndersonAC.AgentS6Construct.MeasurableHelpers
import AndersonAC.AgentS6Construct.Procedure

/-! Measurability of the finite selection rules: the maximal weight, projection
readiness, the least maximizer and the ridge choice. -/

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6 MeasureTheory

variable {ι R B α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
  [mα : MeasurableSpace α]

omit [Nonempty ι] in
theorem continuous_maxWeight : Continuous (fun m : ι → ℝ => maxWeight m) := by
  classical
  have hsup : Continuous
      (fun m : ι → ℝ => (Finset.univ : Finset ι).sup (fun i => Real.toNNReal (m i))) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty =>
        simp only [Finset.sup_empty]
        exact continuous_const
    | @insert a s ha ih =>
        simp only [Finset.sup_insert]
        exact (continuous_real_toNNReal.comp (continuous_apply a)).sup ih
  unfold maxWeight
  exact NNReal.continuous_coe.comp hsup

omit [Nonempty ι] in
theorem measurable_maxWeight (m : α → ι → ℝ)
    (hm : ∀ i, Measurable fun a => m a i) :
    Measurable fun a => maxWeight (m a) :=
  continuous_maxWeight.measurable.comp (measurable_pi_iff.2 hm)

theorem measurableSet_projectionReady {C : α → Matrix R B ℂ} (hC : Measurable C)
    (l : ℝ) (hl : 0 < l) :
    MeasurableSet {a | ∀ i, projectionWeight (C a) i ≤ 2 * l} := by
  have hrange : Measurable fun a => rangeProjection (C a) := by
    exact (AndersonAC.S6.ridge_threshold_measurable (B := B) (R := R) l hl).2.comp hC
  have hrow : ∀ i, Measurable fun a => projectionWeight (C a) i := by
    intro i
    change Measurable fun a => (rangeProjection (C a) i i).re
    exact Complex.measurable_re.comp (hrange.eval_matrix)
  have hset : ∀ i, MeasurableSet {a | projectionWeight (C a) i ≤ 2 * l} := by
    intro i
    exact measurableSet_le (hrow i) measurable_const
  have hInter : MeasurableSet (⋂ i : R, {a | projectionWeight (C a) i ≤ 2 * l}) :=
    MeasurableSet.iInter hset
  simpa only [Set.ofPred_forall] using hInter

noncomputable def chooseLeastMaximizerFromSet {ι : Type*} [Fintype ι]
    [Nonempty ι] (order : ι ≃ Fin (Fintype.card ι))
    (S : Finset (Fin (Fintype.card ι))) : ι :=
  if h : S.Nonempty then order.symm (S.min' h) else Classical.choice ‹Nonempty ι›

theorem measurable_leastMaximizerTotal {C : α → ι → ℝ}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (hC : ∀ i, Measurable fun a => C a i) :
    Measurable fun a => leastMaximizerTotal order (C a) := by
  classical
  have hmax : Measurable fun a => maxWeight (C a) := measurable_maxWeight C hC
  have hS : Measurable fun a => orderedMaximizers order (C a) := by
    rw [measurable_finset_iff]
    intro j
    have hval : Measurable fun a => C a (order.symm j) := hC (order.symm j)
    have hset : MeasurableSet {a | C a (order.symm j) = maxWeight (C a)} :=
      measurableSet_eq_fun hval hmax
    have hEq : (fun a => j ∈ orderedMaximizers order (C a)) =
        fun a => a ∈ {a | C a (order.symm j) = maxWeight (C a)} := by
      funext a
      simp [orderedMaximizers]
    rw [hEq]
    exact measurableSet_setOfPred.mp (by simpa using hset)
  have hchoose : Measurable (chooseLeastMaximizerFromSet order) :=
    measurable_of_countable _
  have hEq : (fun a => leastMaximizerTotal order (C a)) =
      chooseLeastMaximizerFromSet order ∘ fun a => orderedMaximizers order (C a) := by
    funext a
    simp [leastMaximizerTotal, chooseLeastMaximizerFromSet]
  rw [hEq]
  exact hchoose.comp hS

theorem measurable_leverage_comp {C : α → Matrix R B ℂ} {τ : α → ℝ}
    (hC : Measurable C) (hτ : Measurable τ) (i : R) :
    Measurable fun a => leverage (C a) (τ a) i := by
  have h := Measurable.comp (AndersonAC.AgentS6.measurable_leverage (R := R) (B := B) i)
    (hC.prodMk hτ)
  exact h

theorem measurable_chooseRidge {C : α → Matrix R B ℂ} {τ : α → ℝ}
    (l : ℝ) (hl : 0 < l) (hC : Measurable C) (hτ : Measurable τ) :
    Measurable fun a => chooseRidge (C a) l (τ a) := by
  have hmax : Measurable fun a => maxWeight (leverage (C a) (τ a)) :=
    measurable_maxWeight _ (measurable_leverage_comp hC hτ)
  have hlow : MeasurableSet {a | maxWeight (leverage (C a) (τ a)) < 2 * l} :=
    measurableSet_lt hmax measurable_const
  have hthreshold : Measurable fun a => ridgeThreshold (C a) l :=
    (AndersonAC.S6.ridge_threshold_measurable (B := B) (R := R) l hl).1.comp hC
  exact Measurable.ite hlow hthreshold hτ

end AndersonAC.AgentS6Construct
