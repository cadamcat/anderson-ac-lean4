import AndersonAC.AgentS6.RidgeStep
import AndersonAC.AgentS6.Decomposition

/-! The stopped potential `Φ = 𝒫 - 10 l_* 𝒜` of a trial (06-clearing.tex:650–720) satisfies
`StoppedPotentialInput`, the hypothesis of Lemma 6.5. Heats drift down by Lemma 6.4
(`PrepHyp.drift`, via `heat_potential_drift`); ridge lowerings are pathwise nonincreasing
(`ridge_step`); after the stop `Φ` is frozen at the last heat ridge. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set

namespace AndersonAC.AgentS6

open AndersonAC.S6

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ} {core : Finset (Fin n)} {t : ℝ} {r : Ω → Fin n → ℂ}
  {g0 : Ω → Matrix (Fin n) (Fin n) ℂ} {order : Fin n ≃ Fin (Fintype.card (Fin n))}

/-- Prestate weights at the heat ridge. -/
abbrev preW (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) : Fin n → ℝ :=
  trialWeights t (r ω) (q.state k ω) (q.ridge k ω)

/-- Poststate weights at the same ridge. -/
abbrev postW (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) : Fin n → ℝ :=
  trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω)

open Classical in
/-- The stopped potential, written as a finite sum of indicator pieces. -/
def phi (q : StoppedTrial (Ω := Ω) core t r g0 order) (l : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  {ω | k < q.stop ω}.indicator (fun ω => potential l (preW q k ω)) ω +
    ∑ j ∈ Finset.range k,
      {ω | q.stop ω = j + 1}.indicator (fun ω => potential l (postW q j ω)) ω

theorem phi_eval (q : StoppedTrial (Ω := Ω) core t r g0 order) (l : ℝ) (k : ℕ) (ω : Ω) :
    phi q l k ω = if k < q.stop ω then potential l (preW q k ω)
      else if q.stop ω = 0 then 0 else potential l (postW q (q.stop ω - 1) ω) := by
  unfold phi
  by_cases hk : k < q.stop ω
  · rw [if_pos hk, Set.indicator_of_mem (show ω ∈ {ω | k < q.stop ω} from hk)]
    have : ∑ j ∈ Finset.range k,
        {ω | q.stop ω = j + 1}.indicator (fun ω => potential l (postW q j ω)) ω = 0 := by
      refine Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem ?_ _
      simp only [Set.mem_setOf_eq]
      have := Finset.mem_range.mp hj
      omega
    rw [this, add_zero]
  · rw [if_neg hk, Set.indicator_of_notMem (show ω ∉ {ω | k < q.stop ω} from hk), zero_add]
    by_cases h0 : q.stop ω = 0
    · rw [if_pos h0]
      refine Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem ?_ _
      simp only [Set.mem_setOf_eq]; omega
    · rw [if_neg h0]
      have hmem : q.stop ω - 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · apply Set.indicator_of_mem
        show q.stop ω = q.stop ω - 1 + 1
        omega
      · intro j _ hj
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_setOf_eq]; omega

theorem potential_onRunning (l : ℝ) (run : ℕ → Set Ω) (w : ℕ → Ω → Fin n → ℝ) (k : ℕ) :
    (fun ω => potential l (onRunning run w k ω)) =
      (run k).indicator (fun ω => potential l (w k ω)) := by
  funext ω
  by_cases h : ω ∈ run k
  · simp [onRunning, h]
  · simp [onRunning, h, potential, squareWeight, totalWeight]

theorem measurable_potential {α : Type*} {m : MeasurableSpace α} (l : ℝ) {f : α → Fin n → ℝ}
    (hf : ∀ i, Measurable[m] (fun x => f x i)) :
    Measurable[m] (fun x => potential l (f x)) := by
  unfold potential squareWeight totalWeight
  exact (Finset.measurable_sum _ fun i _ => (hf i).pow_const 2).sub
    ((Finset.measurable_sum _ fun i _ => hf i).const_mul _)

theorem measurable_weights (q : StoppedTrial (Ω := Ω) core t r g0 order) {k j : ℕ}
    (hjk : j ≤ k) (i : Fin n) :
    @Measurable Ω ℝ (q.history k) _
      (fun ω => leverage (trialCross t (r ω) (q.state k ω)) (q.ridge j ω) i) := by
  have hC : Measurable[q.history k] (fun ω => trialCross t (r ω) (q.state k ω)) := by
    refine @Measurable.of_eval_matrix (Fin n) {b // b ∈ core} ℂ _ Ω (q.history k) _
      (fun a b => ?_)
    exact ((continuous_id.matrix_elem a b).comp_stronglyMeasurable (q.cross_adapted k)).measurable
  have hτ : Measurable[q.history k] (q.ridge j) :=
    ((q.ridge_predictable j).mono (q.history.mono hjk)).measurable
  have hp : @Measurable Ω _ (q.history k) _
      (fun ω => (trialCross t (r ω) (q.state k ω), q.ridge j ω)) := hC.prodMk hτ
  have hl := measurable_leverage (R := Fin n) (B := {b // b ∈ core}) i
  have h2 := hl.comp hp
  exact h2

theorem stop_eq_measurableSet (q : StoppedTrial (Ω := Ω) core t r g0 order) (j : ℕ) :
    MeasurableSet[q.history (j + 1)] {ω | q.stop ω = j + 1} := by
  have h1 := q.stopping (j + 1)
  have h2 := q.history.mono (Nat.le_succ j) _ (q.stopping j)
  convert h1.diff h2 using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_sdiff]
  constructor
  · intro h
    exact ⟨WithTop.coe_le_coe.mpr (show q.stop ω ≤ j + 1 by omega), fun h' => by
      have := (WithTop.coe_le_coe.mp h' : q.stop ω ≤ j); omega⟩
  · rintro ⟨h1, h2⟩
    have a1 : q.stop ω ≤ j + 1 := WithTop.coe_le_coe.mp h1
    have a2 : ¬ q.stop ω ≤ j := fun h' => h2 (WithTop.coe_le_coe.mpr h')
    omega

theorem phi_measurable (q : StoppedTrial (Ω := Ω) core t r g0 order) (l : ℝ) (k : ℕ) :
    Measurable[q.history k] (phi q l k) := by
  unfold phi
  refine Measurable.add ?_ (Finset.measurable_sum _ fun j hj => ?_)
  · exact (measurable_potential l fun i => measurable_weights q le_rfl i).indicator
      (running_measurableSet q k)
  · have hj' : j + 1 ≤ k := Finset.mem_range.mp hj
    have hpost : Measurable[q.history (j + 1)] (fun ω => potential l (postW q j ω)) :=
      measurable_potential l fun i => measurable_weights q (k := j + 1) (j := j) (by omega) i
    exact (hpost.mono (q.history.mono hj') le_rfl).indicator
      (q.history.mono hj' _ (stop_eq_measurableSet q j))

theorem potential_lower {B : Type*} [Fintype B] [DecidableEq B] {R : Type*} [Fintype R]
    [DecidableEq R] (C : Matrix R B ℂ) {l τ : ℝ} (hl : 0 ≤ l) (hτ : 0 < τ) :
    -10 * l * (Fintype.card B : ℝ) ≤ potential l (leverage C τ) := by
  have h1 := totalWeight_leverage_le C hτ
  have h2 : 0 ≤ squareWeight (leverage C τ) := Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold potential
  nlinarith

theorem potential_cap {R : Type*} [Fintype R] [DecidableEq R] {l : ℝ} (m : R → ℝ) (hl : 0 ≤ l)
    (hm : ∀ i, 0 ≤ m i) (hcap : maxWeight m ≤ 4 * l) : potential l m ≤ 0 := by
  have hsq : squareWeight m ≤ 4 * l * totalWeight m := by
    unfold squareWeight totalWeight
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := (le_maxWeight m i).trans hcap
    nlinarith [hm i]
  have htot : 0 ≤ totalWeight m := Finset.sum_nonneg fun i _ => hm i
  unfold potential
  nlinarith

theorem onRunning_of_mem {ι : Type*} {run : ℕ → Set Ω} {w : ℕ → Ω → ι → ℝ} {k : ℕ} {ω : Ω}
    (h : ω ∈ run k) : onRunning run w k ω = w k ω := by
  simp [onRunning, h]

theorem onRunning_of_not_mem {ι : Type*} {run : ℕ → Set Ω} {w : ℕ → Ω → ι → ℝ} {k : ℕ} {ω : Ω}
    (h : ω ∉ run k) : onRunning run w k ω = 0 := by
  simp [onRunning, h]

theorem potential_zero {ι : Type*} [Fintype ι] (l : ℝ) : potential l (0 : ι → ℝ) = 0 := by
  simp [potential, squareWeight, totalWeight]

/-- Lemma 6.5's hypothesis for the trial potential (06-clearing.tex:650–720). -/
theorem stoppedPotential {d : ℕ} {c K Cloc cConc : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {qlag ε : ℝ → ℝ} (q : StoppedTrial (Ω := Ω) core t r g0 order)
    {dist : Fin n → Fin n → ℝ} {collapsed : ℕ → Ω → Fin n → Fin n → ℝ} {ell : ℝ}
    (hyp : PrepHyp d c K Cloc cConc μ qlag ε core t r g0 order q dist collapsed ell)
    (hε0 : 0 ≤ ε t) (hε1 : ε t ≤ 1 / 20) :
    StoppedPotentialInput μ q.history (leverageScale t) (coreCap d t) (heatLimit t) q.stop
      (phi q (leverageScale t)) := by
  set l := leverageScale t with hldef
  set rr := coreCap d t
  have ht := hyp.t_pos
  have hl : 0 < l := Real.rpow_pos_of_pos ht _
  have hrr : 0 < rr := Real.rpow_pos_of_pos ht _
  set run : ℕ → Set Ω := fun k => {ω | k < q.stop ω} with hrun
  have hrunm : ∀ k, MeasurableSet (run k) := fun k =>
    q.history.le k _ (running_measurableSet q k)
  have hcard : (Fintype.card {b // b ∈ core} : ℝ) ≤ rr := by
    rw [Fintype.card_coe]; exact hyp.core_cap
  -- integrability of the restricted potentials
  have hpreI : ∀ k, Integrable (fun ω => potential l (onRunning run (preW q) k ω)) μ := by
    intro k
    have := (hyp.drift.integrable_preP k).sub ((hyp.drift.integrable_preA k).const_mul (10 * l))
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, potential]; ring
  have hpostI : ∀ k, Integrable (fun ω => potential l (onRunning run (postW q) k ω)) μ := by
    intro k
    have := (hyp.drift.integrable_postP k).sub ((hyp.drift.integrable_postA k).const_mul (10 * l))
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, potential]; ring
  refine ⟨q.stopping, q.finite_stop, fun k => (phi_measurable q l k).stronglyMeasurable,
    fun k => ?_, fun k ω => ?_, fun k ω hk => ?_, fun k ω hk => ?_, fun k => ?_⟩
  · -- integrable
    have hA : Integrable (fun ω => {ω | k < q.stop ω}.indicator
        (fun ω => potential l (preW q k ω)) ω) μ := by
      rw [← potential_onRunning l run (preW q) k]; exact hpreI k
    have hB : ∀ j ∈ Finset.range k, Integrable (fun ω => {ω | q.stop ω = j + 1}.indicator
        (fun ω => potential l (postW q j ω)) ω) μ := by
      intro j _
      have hsub : {ω | q.stop ω = j + 1} ∩ run j = {ω | q.stop ω = j + 1} := by
        ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hrun]; omega
      have hm : MeasurableSet {ω | q.stop ω = j + 1} :=
        q.history.le (j + 1) _ (stop_eq_measurableSet q j)
      have := (hpostI j).indicator hm
      rw [potential_onRunning l run (postW q) j, Set.indicator_indicator, hsub] at this
      exact this
    exact hA.add (integrable_finset_sum _ hB)
  · -- lower
    rw [phi_eval]
    have hl0 : 0 ≤ l := hl.le
    split_ifs with h1 h2
    · have := potential_lower (trialCross t (r ω) (q.state k ω)) hl0 (q.running_ridge k ω h1)
      unfold preW trialWeights; nlinarith
    · nlinarith
    · have hs : q.stop ω - 1 < q.stop ω := by omega
      have := potential_lower (trialCross t (r ω) (q.state (q.stop ω - 1 + 1) ω)) hl0
        (q.running_ridge _ ω hs)
      unfold postW trialWeights; nlinarith
  · -- pre_cap
    rw [phi_eval, if_pos hk]
    exact potential_cap _ hl.le (fun i => leverage_nonneg _ (q.running_ridge k ω hk).le i)
      (q.running_cap k ω hk).2
  · -- stopped
    simp only [phi_eval, show ¬ (k + 1 < q.stop ω) by omega, show ¬ (k < q.stop ω) by omega,
      if_false]
  · -- drift
    set H : Ω → ℝ := fun ω => potential l (onRunning run (postW q) k ω) -
      potential l (onRunning run (preW q) k ω) with hH
    set R : Ω → ℝ := {ω | k + 1 < q.stop ω}.indicator (fun ω =>
      potential l (onRunning run (preW q) (k + 1) ω) -
        potential l (onRunning run (postW q) k ω)) with hR
    have hHI : Integrable H μ := (hpostI k).sub (hpreI k)
    have hRI : Integrable R μ :=
      ((hpreI (k + 1)).sub (hpostI k)).indicator (hrunm (k + 1))
    have hsplit : (fun ω => phi q l (k + 1) ω - phi q l k ω) = H + R := by
      funext ω
      simp only [Pi.add_apply, hH, hR]
      rw [phi_eval, phi_eval]
      by_cases h1 : k + 1 < q.stop ω
      · have h0 : k < q.stop ω := by omega
        rw [if_pos h1, if_pos h0, Set.indicator_of_mem (show ω ∈ {ω | k + 1 < q.stop ω} from h1),
          onRunning_of_mem (show ω ∈ run k from h0), onRunning_of_mem (show ω ∈ run k from h0),
          onRunning_of_mem (show ω ∈ run (k + 1) from h1)]
        ring
      · rw [if_neg h1, Set.indicator_of_notMem (show ω ∉ {ω | k + 1 < q.stop ω} from h1)]
        by_cases h0 : k < q.stop ω
        · have hs : q.stop ω = k + 1 := by omega
          rw [if_pos h0, if_neg (by omega), onRunning_of_mem (show ω ∈ run k from h0),
            onRunning_of_mem (show ω ∈ run k from h0), hs]
          simp
        · rw [if_neg h0, onRunning_of_not_mem (show ω ∉ run k from h0),
            onRunning_of_not_mem (show ω ∉ run k from h0), potential_zero]
          simp
    have hRle : ∀ ω, R ω ≤ 0 := by
      intro ω
      simp only [hR]
      by_cases h1 : k + 1 < q.stop ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | k + 1 < q.stop ω} from h1),
          onRunning_of_mem (show ω ∈ run (k + 1) from h1),
          onRunning_of_mem (show ω ∈ run k from (by simp only [hrun, Set.mem_setOf_eq]; omega))]
        have hτ := q.running_ridge k ω (by omega)
        have hτ' := q.running_ridge (k + 1) ω h1
        have hrule := q.ridge_rule k ω h1
        rw [hrule] at hτ'
        have := ridge_step (trialCross t (r ω) (q.state (k + 1) ω)) hl hτ hτ'
        unfold preW postW trialWeights
        rw [hrule]
        linarith
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | k + 1 < q.stop ω} from h1)]
    have hHind : H = (run k).indicator H := by
      funext ω
      by_cases h0 : ω ∈ run k
      · rw [Set.indicator_of_mem h0]
      · rw [Set.indicator_of_notMem h0]
        simp only [hH, onRunning_of_not_mem h0, potential_zero, sub_self]
    have hmax : ∀ k ω, ω ∈ run k → 2 * l ≤ maxWeight (onRunning run (preW q) k ω) := by
      intro k ω h
      rw [onRunning_of_mem h]
      exact (q.running_cap k ω h).1
    have hdrift := heat_potential_drift μ q.history (ε t) l run (onRunning run (preW q))
      (onRunning run (postW q)) hl ⟨hε0, hε1⟩ hyp.drift hmax k
    have hind := condExp_indicator (m := q.history k) hHI (running_measurableSet q k)
    have hRneg : μ[R | q.history k] ≤ᵐ[μ] 0 := by
      have := condExp_mono (m := q.history k) hRI (integrable_zero Ω ℝ μ)
        (Eventually.of_forall hRle)
      rwa [condExp_zero] at this
    have hadd := condExp_add hHI hRI (q.history k)
    rw [hsplit]
    filter_upwards [hdrift, hind, hRneg, hadd] with ω h1 h2 h3 h4
    rw [h4, Pi.add_apply]
    have h3' : μ[R | q.history k] ω ≤ 0 := h3
    by_cases h0 : k < q.stop ω
    · rw [if_pos h0]
      have hm := h1 h0
      have hmw : 2 * l ≤ maxWeight (onRunning run (preW q) k ω) := hmax k ω h0
      have hl2 : (2 * l) ^ 2 ≤ (maxWeight (onRunning run (preW q) k ω)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hmw 2
      have : μ[H | q.history k] ω ≤ -(1 / 2) * (maxWeight (onRunning run (preW q) k ω)) ^ 2 := hm
      nlinarith
    · rw [if_neg h0]
      have : μ[H | q.history k] ω = 0 := by
        rw [← hHind] at h2
        rw [h2, Set.indicator_of_notMem (show ω ∉ run k from h0)]
      linarith

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.stoppedPotential
