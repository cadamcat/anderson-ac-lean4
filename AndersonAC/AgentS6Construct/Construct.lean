import AndersonAC.AgentS6Construct.StopOutcome
import AndersonAC.AgentS6Construct.QueryHistory
import AndersonAC.S6.Statements

/-! Existence and measurability of the stopped trial (06-clearing.tex:788–850,
1115–1118). -/

noncomputable section

open scoped Matrix
open MeasureTheory

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem stronglyMeasurable_matrix {κ : Type*} [Fintype κ] {m : MeasurableSpace Ω}
    {f : Ω → Matrix ι κ ℂ} (hf : Measurable f) : StronglyMeasurable f := by
  have hf' : Measurable (fun ω => (Matrix.of.symm (f ω) : ι → κ → ℂ)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hf.eval_matrix
  have hc : Continuous (fun v : ι → κ → ℂ => Matrix.of v) := continuous_id
  have := hc.comp_stronglyMeasurable hf'.stronglyMeasurable
  simpa using this

theorem stronglyMeasurable_of_measurable' {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (m : MeasurableSpace Ω) {f : Ω → β}
    (hf : Measurable[m] f) : StronglyMeasurable[m] f := by
  let _ := m
  exact hf.stronglyMeasurable

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem measurable_obs_H_entry (m : MeasurableSpace Ω) {o : Ω → Obs ι}
    (ho : Measurable[m] o) (i j : ι) : Measurable[m] (fun ω => (o ω).H i j) := by
  letI := m
  exact (Obs.measurable_H.comp ho).eval_matrix

/-- The observables of the reached cursor are measurable for any increasing family of
σ-algebras that contains the initial data and reveals each residual one step later. -/
theorem runAt_obs_measurable_of [MeasurableSpace Ω] (core : Finset ι) (t : ℝ)
    (ht : 0 < t) (r : Ω → ι → ℂ) (hrpos : ∀ ω i, 0 < (r ω i).im)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm) (ξ : ι → Ω → ℝ)
    (order : ι ≃ Fin (Fintype.card ι))
    (hterminal : ∀ ω (T : Finset ι), IsUnit
      (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι)) (fun i : {i // i ∈ T} => (i : ι))).det))
    (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m) (hR : ∀ k, Measurable[m k] r)
    (hG : ∀ k, Measurable[m k] (fun ω => activeInverse (M0 ω) t (r ω)))
    (hres : ∀ k, Measurable[m k] (fun ω => (runAt core t r M0 hM ξ order ω k).obs) →
      Measurable[m (k + 1)] (residualAt core t r M0 hM ξ order k)) :
    ∀ k, Measurable[m k] (fun ω => (runAt core t r M0 hM ξ order ω k).obs) := by
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  intro k
  induction k with
  | zero =>
      have h0 : (fun ω => (runAt core t r M0 hM ξ order ω 0).obs) =
          fun ω => (⟨Finset.univ, activeInverse (M0 ω) t (r ω),
            (leverageScale t) ^ (-2 : ℤ), true, .fail⟩ : Obs ι) := rfl
      rw [h0]
      exact @Obs.measurable_mk ι Ω (m 0) _ _ _ _ _ measurable_const (hG 0)
        measurable_const measurable_const measurable_const
  | succ k ih =>
      have heq : (fun ω => (runAt core t r M0 hM ξ order ω (k + 1)).obs) =
          fun ω => obsStep core t (heatLimit t) (r ω) (activeInverse (M0 ω) t (r ω)) order k
            (runAt core t r M0 hM ξ order ω k).obs (residualAt core t r M0 hM ξ order k ω) :=
        funext fun ω => runAt_obs_succ core t ht r hrpos M0 hM ξ order ω (hterminal ω) k
      rw [heq]
      exact measurable_obsStep_top (mα := m (k + 1)) core t (heatLimit t) order k hl
        (ih.mono (hmono k.le_succ) le_rfl) (hR (k + 1)) (hG (k + 1)) (hres k ih)

theorem pivotAt_measurable_top [MeasurableSpace Ω] (core : Finset ι) (t : ℝ)
    (ht : 0 < t) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm) (ξ : ι → Ω → ℝ)
    (order : ι ≃ Fin (Fintype.card ι))
    (hterminal : ∀ ω (T : Finset ι), IsUnit
      (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι)) (fun i : {i // i ∈ T} => (i : ι))).det))
    (m : MeasurableSpace Ω) (k : ℕ)
    (ho : Measurable[m] (fun ω => (runAt core t r M0 hM ξ order ω k).obs))
    (hR : Measurable[m] r) :
    @Measurable Ω ι m ⊤ (pivotAt core t r M0 hM ξ order k) := by
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have heq : pivotAt core t r M0 hM ξ order k =
      fun ω => obsPivot core t (r ω) order (runAt core t r M0 hM ξ order ω k).obs :=
    funext fun ω => runAt_pivot_eq_obsPivot core t ht r M0 hM ξ order ω (hterminal ω) k
  rw [heq]
  exact measurable_obsPivot_top (mα := m) core t hl order ho hR

theorem residualAt_measurable [MeasurableSpace Ω] (core : Finset ι) (t : ℝ)
    (ht : 0 < t) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm) (ξ : ι → Ω → ℝ)
    (order : ι ≃ Fin (Fintype.card ι))
    (hterminal : ∀ ω (T : Finset ι), IsUnit
      (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι)) (fun i : {i // i ∈ T} => (i : ι))).det))
    (hξ : ∀ i, Measurable (ξ i)) (k : ℕ)
    (ho : Measurable (fun ω => (runAt core t r M0 hM ξ order ω k).obs))
    (hR : Measurable r) :
    Measurable (residualAt core t r M0 hM ξ order k) := by
  have hp := pivotAt_measurable_top core t ht r M0 hM ξ order hterminal _ k ho hR
  exact measurable_eval_at_top (f := fun ω y => ξ y ω) (fun y => hξ y) hp

end AndersonAC.AgentS6Construct

namespace AndersonAC.S6

open AndersonAC.AgentS6Construct

set_option maxHeartbeats 1000000 in
/-- Proposition 6.6, construction part: the adaptive stopped trial exists and is adapted
to the query history (06-clearing.tex:788–850, 1115–1118). -/
theorem construct_stopped_trial {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace ι] [Nonempty ι] (core : Finset ι) (t c K : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (ξ : ι → Ω → ℝ) (F0 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (order : ι ≃ Fin (Fintype.card ι)) (ht : 0 < t)
    (hl : leverageScale t < 2) (hN : 1 ≤ heatLimit t) (hr : ∀ ω, BroadBounds c K (r ω))
    (hM : ∀ ω, (M0 ω).IsSymm) (hM0 : StronglyMeasurable[F0] M0)
    (hr0 : StronglyMeasurable[F0] r) (hξ : ∀ i, Measurable (ξ i)) (hF : F0 ≤ mΩ)
    (hterminal : ∀ ω (T : Finset ι), IsUnit
      (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι)) (fun i : {i // i ∈ T} => (i : ι))).det)) :
    Planned.construct_stopped_trial core t c K r M0 ξ F0 order ht hl hN hr hM hM0 hr0 hξ hF
      hterminal := by
  classical
  unfold Planned.construct_stopped_trial
  have hrpos : ∀ ω i, 0 < (r ω i).im := fun ω i =>
    lt_of_lt_of_le (hr ω).1 ((hr ω).2 i).2.1
  have hlpos : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hrF0 : Measurable[F0] r := hr0.measurable
  have hgF0 : Measurable[F0] (fun ω => activeInverse (M0 ω) t (r ω)) :=
    measurable_activeInverse (mΩ := F0) (F0 := F0) t M0 r le_rfl hM0 hr0
  -- Ambient measurability of the observables.
  have hA : ∀ k, Measurable (fun ω => (runAt core t r M0 hM ξ order ω k).obs) :=
    runAt_obs_measurable_of core t ht r hrpos M0 hM ξ order hterminal (fun _ => mΩ)
      monotone_const (fun _ => hrF0.mono hF le_rfl) (fun _ => hgF0.mono hF le_rfl)
      (fun k hk => residualAt_measurable core t ht r M0 hM ξ order hterminal hξ k hk
        (hrF0.mono hF le_rfl))
  -- The query history.
  let hist : ℕ → MeasurableSpace Ω := fun k =>
    queryHistory F0 (pivotAt core t r M0 hM ξ order) (residualAt core t r M0 hM ξ order) k
  have hF0hist : ∀ k, F0 ≤ hist k := fun k =>
    le_queryHistory F0 (pivotAt core t r M0 hM ξ order) (residualAt core t r M0 hM ξ order) k
  have hmono : Monotone hist :=
    queryHistory_mono F0 (pivotAt core t r M0 hM ξ order) (residualAt core t r M0 hM ξ order)
  have hresHist : ∀ k, Measurable[hist (k + 1)] (residualAt core t r M0 hM ξ order k) :=
    fun k => measurable_residual_queryHistory F0 (pivotAt core t r M0 hM ξ order)
      (residualAt core t r M0 hM ξ order) k
  have hRhist : ∀ k, Measurable[hist k] r := fun k => hrF0.mono (hF0hist k) le_rfl
  have hB : ∀ k, Measurable[hist k] (fun ω => (runAt core t r M0 hM ξ order ω k).obs) :=
    runAt_obs_measurable_of core t ht r hrpos M0 hM ξ order hterminal hist hmono hRhist
      (fun k => hgF0.mono (hF0hist k) le_rfl) (fun k _ => hresHist k)
  have hpivA : ∀ k, Measurable (pivotAt core t r M0 hM ξ order k) := fun k =>
    (pivotAt_measurable_top core t ht r M0 hM ξ order hterminal mΩ k (hA k)
      (hrF0.mono hF le_rfl)).mono le_rfl le_top
  have hresA : ∀ k, Measurable (residualAt core t r M0 hM ξ order k) := fun k =>
    residualAt_measurable core t ht r M0 hM ξ order hterminal hξ k (hA k)
      (hrF0.mono hF le_rfl)
  have hle : ∀ k, hist k ≤ mΩ := fun k =>
    queryHistory_le F0 mΩ (pivotAt core t r M0 hM ξ order) (residualAt core t r M0 hM ξ order)
      hF hpivA hresA k
  let H : Filtration ℕ mΩ := ⟨hist, hmono, hle⟩
  have hstop : ∀ i, MeasurableSet[hist i]
      {ω | ((stopAt core t r M0 hM ξ order ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ)} := by
    intro i
    have hset : {ω | ((stopAt core t r M0 hM ξ order ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ)} =
        (fun ω => (obsStep core t (heatLimit t) (r ω) (activeInverse (M0 ω) t (r ω)) order i
          (runAt core t r M0 hM ξ order ω i).obs 0).running) ⁻¹' {false} := by
      ext ω
      have hcoe : ((stopAt core t r M0 hM ξ order ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ) ↔
          stopAt core t r M0 hM ξ order ω ≤ i := by norm_cast
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [hcoe, stopAt_le_iff, ← obsStep_running_indep core t (heatLimit t) (r ω)
        (activeInverse (M0 ω) t (r ω)) order i _ (residualAt core t r M0 hM ξ order i ω),
        ← runAt_obs_succ core t ht r hrpos M0 hM ξ order ω (hterminal ω) i]
      rfl
    rw [hset]
    have hmeas := measurable_obsStep_top (mα := hist i) core t (heatLimit t) order i hlpos
      (hB i) (hRhist i) (hgF0.mono (hF0hist i) le_rfl) (measurable_const (a := (0 : ℝ)))
    exact (Obs.measurable_running.comp hmeas) (measurableSet_singleton false)
  refine ⟨{
    state := stateAt core t r M0 hM ξ order
    ridge := ridgeAt core t r M0 hM ξ order
    pivot := pivotAt core t r M0 hM ξ order
    residual := residualAt core t r M0 hM ξ order
    stop := stopAt core t r M0 hM ξ order
    outcome := outcomeAt core t r M0 hM ξ order
    history := H
    damping_adapted := hr0.mono (hF0hist 0)
    initial_active := stateAt_zero_active core t r M0 hM ξ order
    start_entries := stateAt_zero_entries core t r M0 hM ξ order
    start_ridge := ridgeAt_zero core t r M0 hM ξ order
    initial_inverse := stateAt_zero_inverse core t r M0 hM ξ order
    finite_stop := runAt_stop_le core t r M0 hM ξ order
    stopping := hstop
    running_budgets := fun k ω hk =>
      (runAt_successful_step core t r M0 hM ξ order ω k hk).1
    running_ridge := fun k ω hk =>
      (runAt_selected_pivot_properties core t ht r M0 hM ξ order ω k hk).1
    pivot_max := fun k ω hk =>
      (runAt_selected_pivot_properties core t ht r M0 hM ξ order ω k hk).2.2.2.2.2.1
    pivot_tie := fun k ω i hk hi =>
      (runAt_selected_pivot_properties core t ht r M0 hM ξ order ω k hk).2.2.2.2.2.2 i
        (hi.trans (runAt_selected_pivot_properties core t ht r M0 hM ξ order ω k hk).2.2.2.2.2.1)
    running_cap := fun k ω hk =>
      ⟨(runAt_selected_pivot_properties core t ht r M0 hM ξ order ω k hk).2.2.2.1,
        (runAt_selected_pivot_properties core t ht r M0 hM ξ order ω k hk).2.2.2.2.1⟩
    heat := fun k ω hk => runAt_heatTransition core t ht r M0 hM ξ order ω k
      (hterminal ω) hk
    ridge_rule := ?_
    done_iff := fun ω => (outcome_spec core t ht hl c K r hr M0 hM ξ order ω).1
    fail_reason := fun ω => (outcome_spec core t ht hl c K r hr M0 hM ξ order ω).2
    entries_adapted := fun k i j =>
      stronglyMeasurable_of_measurable' (hist k)
        (measurable_obs_H_entry (hist k) (hB k) i j)
    cross_adapted := ?_
    ridge_predictable := ?_
    pivot_predictable := fun k =>
      (pivotAt_measurable_top core t ht r M0 hM ξ order hterminal (hist k) k (hB k)
        (hRhist k)).mono le_rfl le_top
    residual_revealed := fun k => stronglyMeasurable_of_measurable' (hist (k + 1)) (hresHist k)
    outcome_measurable := Obs.measurable_outcome.comp (hA (heatLimit t + 1)) },
    fun k => rfl, fun ω i j => rfl, fun k ω _ => rfl,
    fun k ω hk => stateAt_eq_stop_of_le core t r M0 hM ξ order ω k hk⟩
  · intro k ω hk
    have hs := (runAt_successful_step core t r M0 hM ξ order ω k (by omega)).2.2.2.2
    have hprev : (runAt core t r M0 hM ξ order ω (k + 1)).previousRidge =
        ridgeAt core t r M0 hM ξ order k ω := by
      rw [hs]
      rfl
    change chooseRidge (trialCross t (r ω) (stateAt core t r M0 hM ξ order (k + 1) ω))
      (leverageScale t) (runAt core t r M0 hM ξ order ω (k + 1)).previousRidge = _
    rw [hprev]
  · intro k
    have heq : (fun ω => trialCross t (r ω) (stateAt core t r M0 hM ξ order k ω)) =
        fun ω => obsCross core t (r ω) (runAt core t r M0 hM ξ order ω k).obs :=
      funext fun ω => runAt_trialCross_eq_obsCross core t ht r M0 hM ξ order ω
        (hterminal ω) k
    change StronglyMeasurable[hist k]
      (fun ω => trialCross t (r ω) (stateAt core t r M0 hM ξ order k ω))
    rw [heq]
    exact stronglyMeasurable_matrix (measurable_obsCross (mα := hist k) core t (hB k) (hRhist k))
  · intro k
    have heq : ridgeAt core t r M0 hM ξ order k =
        fun ω => obsRidge core t (r ω) (runAt core t r M0 hM ξ order ω k).obs :=
      funext fun ω => runAt_ridge_eq_obsRidge core t ht r M0 hM ξ order ω (hterminal ω) k
    change StronglyMeasurable[hist k] (ridgeAt core t r M0 hM ξ order k)
    rw [heq]
    exact stronglyMeasurable_of_measurable' (hist k)
      (measurable_obsRidge (mα := hist k) core t hlpos (hB k) (hRhist k))

end AndersonAC.S6
