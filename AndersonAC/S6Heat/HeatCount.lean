import AndersonAC.S6.CoreHeatStatements

/-! Finite stopped-potential estimate used by the Section 6 heat-count lemma. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace AndersonAC.SolS6Heat

def remaining {Ω : Type*} (stop : Ω → ℕ) (m : ℕ) (ω : Ω) : ℝ :=
  ((stop ω - m : ℕ) : ℝ)

def increment {Ω : Type*} (Φ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  Φ (k + 1) ω - Φ k ω

private theorem nat_measurable_of_stopping {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration ℕ ‹MeasurableSpace Ω›} {stop : Ω → ℕ}
    (hstop : IsStoppingTime F (fun ω => (stop ω : WithTop ℕ))) : Measurable stop := by
  have h := Measurable.untopD 0 hstop.measurable'
  convert h using 1
  funext ω
  rfl

private theorem remaining_nonneg {Ω : Type*} (stop : Ω → ℕ) (m : ℕ) (ω : Ω) :
    0 ≤ remaining stop m ω := by
  simp [remaining]

private theorem remaining_le_of_stop_le {Ω : Type*} {stop : Ω → ℕ} {m N : ℕ}
    (hstop : ∀ ω, stop ω ≤ N) (ω : Ω) : remaining stop m ω ≤ (N : ℝ) := by
  unfold remaining
  exact_mod_cast (Nat.sub_le (stop ω) m).trans (hstop ω)

private theorem remaining_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {stop : Ω → ℕ} {N m : ℕ} (hstopTime : IsStoppingTime F (fun ω => (stop ω : WithTop ℕ)))
    (hstop : ∀ ω, stop ω ≤ N) : Integrable (remaining stop m) μ := by
  have hstopMeas := nat_measurable_of_stopping hstopTime
  have hm : Measurable (remaining stop m) := by
    unfold remaining
    fun_prop
  refine (integrable_const (N : ℝ)).mono hm.stronglyMeasurable.aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (remaining_nonneg stop m ω), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg N)]
  exact remaining_le_of_stop_le hstop ω

private theorem phi_stable_after {Ω : Type*} {Φ : ℕ → Ω → ℝ} {stop : Ω → ℕ}
    (hstop : ∀ k ω, stop ω ≤ k → Φ (k + 1) ω = Φ k ω) :
    ∀ ω n, stop ω ≤ n → Φ n ω = Φ (stop ω) ω := by
  intro ω n
  induction n with
  | zero =>
      intro h
      have hs : stop ω = 0 := by omega
      simp [hs]
  | succ n ih =>
      intro h
      by_cases hs : stop ω ≤ n
      · rw [hstop n ω hs]
        exact ih hs
      · have hs' : stop ω = n + 1 := by omega
        simp [hs']

/-- Expected remaining count, tested against any event known at deterministic time `m`. -/
private theorem mean_at_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {l r : ℝ} {N m : ℕ} {stop : Ω → ℕ} {Φ : ℕ → Ω → ℝ}
    (hl : 0 < l) (hr : 0 < r)
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (B : Set Ω) (hB : MeasurableSet[F m] B) :
    ∫ ω in B, remaining stop m ω ∂μ ≤ (5 * r / l) * μ.real B := by
  have hstopMeas := nat_measurable_of_stopping hinput.stopping
  have hremInt : Integrable (remaining stop m) μ :=
    remaining_integrable (μ := μ) hinput.stopping hinput.finite_stop
  have hstable := phi_stable_after hinput.stopped
  have hBμ : MeasurableSet B := (F.le m) _ hB
  by_cases hmN : m ≤ N
  · let s := Finset.Ico m N
    let active : ℕ → Set Ω := fun k => {ω | k < stop ω}
    have hactiveMeas (k : ℕ) : MeasurableSet[F k] (active k) := by
      simpa [active] using hinput.stopping.measurableSet_gt k
    have hactiveMeas' (k : ℕ) : MeasurableSet (active k) :=
      (F.le k) _ (hactiveMeas k)
    have htel (ω : Ω) :
        (∑ k ∈ s, increment Φ k ω) = Φ N ω - Φ m ω := by
      simp only [increment]
      calc
        (∑ k ∈ s, (Φ (k + 1) ω - Φ k ω)) =
            (∑ k ∈ Finset.range N, (Φ (k + 1) ω - Φ k ω)) -
              ∑ k ∈ Finset.range m, (Φ (k + 1) ω - Φ k ω) :=
          Finset.sum_Ico_eq_sub _ hmN
        _ = (Φ N ω - Φ 0 ω) - (Φ m ω - Φ 0 ω) := by
          rw [Finset.sum_range_sub (fun j => Φ j ω) N,
            Finset.sum_range_sub (fun j => Φ j ω) m]
        _ = Φ N ω - Φ m ω := by ring
    have hcount (ω : Ω) :
        (∑ k ∈ s, if k < stop ω then (1 : ℝ) else 0) = remaining stop m ω := by
      have hfilter : s.filter (fun k => k < stop ω) = Finset.Ico m (stop ω) := by
        have hstopN := hinput.finite_stop ω
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ico, s]
        omega
      rw [← Finset.sum_filter, hfilter]
      simp [remaining, Nat.card_Ico]
    have hphiBound (ω : Ω) : Φ m ω - Φ N ω ≤ 10 * l * r := by
      by_cases hrun : m < stop ω
      · have hpre := hinput.pre_cap m ω hrun
        have hterm := hinput.lower (stop ω) ω
        rw [hstable ω N (hinput.finite_stop ω)]
        linarith
      · have hs : stop ω ≤ m := by omega
        rw [hstable ω m hs, hstable ω N (hinput.finite_stop ω)]
        simp
        positivity
    have hpotIntegral :
        ∫ ω in B, Φ m ω - Φ N ω ∂μ ≤ (10 * l * r) * μ.real B := by
      calc
        ∫ ω in B, Φ m ω - Φ N ω ∂μ ≤ ∫ ω in B, (10 * l * r) ∂μ :=
          setIntegral_mono_on
            ((hinput.integrable m).sub (hinput.integrable N)).integrableOn
            (integrable_const _).integrableOn hBμ (fun ω _ => hphiBound ω)
        _ = (10 * l * r) * μ.real B := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hdeltaInt (k : ℕ) : Integrable (increment Φ k) μ :=
      (hinput.integrable (k + 1)).sub (hinput.integrable k)
    have hdriftIntegral (k : ℕ) (hk : k ∈ s) :
        ∫ ω in B, increment Φ k ω ∂μ ≤
          -(2 * l ^ 2) * μ.real (B ∩ active k) := by
      have hmk : m ≤ k := (Finset.mem_Ico.mp hk).1
      have hBk : MeasurableSet[F k] B := F.mono hmk _ hB
      have hBA : MeasurableSet[F k] (B ∩ active k) := hBk.inter (hactiveMeas k)
      have hBA' : MeasurableSet (B ∩ active k) := (F.le k) _ hBA
      have hzero : ∀ ω, ω ∉ active k → increment Φ k ω = 0 := by
        intro ω hω
        have hsk : stop ω ≤ k := by
          simp [active] at hω
          omega
        simp [increment, hinput.stopped k ω hsk]
      calc
        ∫ ω in B, increment Φ k ω ∂μ =
            ∫ ω in B ∩ active k, increment Φ k ω ∂μ := by
          calc
            ∫ ω in B, increment Φ k ω ∂μ =
                ∫ ω in B, (active k).indicator (increment Φ k) ω ∂μ := by
              apply setIntegral_congr_fun hBμ
              intro ω _
              by_cases hω : ω ∈ active k
              · simp [hω]
              · simp [hω, hzero ω hω]
            _ = ∫ ω in B ∩ active k, increment Φ k ω ∂μ := by
              rw [setIntegral_indicator (hactiveMeas' k)]
        _ = ∫ ω in B ∩ active k,
              μ[increment Φ k | F k] ω ∂μ := by
          symm
          exact setIntegral_condExp (F.le k) (hdeltaInt k) hBA
        _ ≤ ∫ ω in B ∩ active k, (-(2 * l ^ 2)) ∂μ := by
          have hceInt : Integrable (fun ω => μ[increment Φ k | F k] ω) μ :=
            integrable_condExp
          apply setIntegral_mono_on_ae hceInt.integrableOn
            (integrable_const (-(2 * l ^ 2))).integrableOn hBA'
          filter_upwards [hinput.drift k] with ω hω hmem
          have hrun : k < stop ω := by simpa [active] using hmem.2
          change μ[(fun ω => Φ (k + 1) ω - Φ k ω) | F k] ω ≤ -(2 * l ^ 2)
          simpa [hrun] using hω
        _ = -(2 * l ^ 2) * μ.real (B ∩ active k) := by
          rw [setIntegral_const, smul_eq_mul]
          ring
    have hsumDelta :
        ∫ ω in B, Φ N ω - Φ m ω ∂μ =
          ∑ k ∈ s, ∫ ω in B, increment Φ k ω ∂μ := by
      calc
        ∫ ω in B, Φ N ω - Φ m ω ∂μ =
            ∫ ω in B, (∑ k ∈ s, increment Φ k ω) ∂μ := by
              apply setIntegral_congr_fun hBμ
              intro ω _
              exact (htel ω).symm
        _ = ∑ k ∈ s, ∫ ω in B, increment Φ k ω ∂μ := by
          change ∫ ω, (∑ k ∈ s, increment Φ k ω) ∂μ.restrict B = _
          rw [integral_finsetSum s (fun k hk =>
            (hdeltaInt k).mono_measure Measure.restrict_le_self)]
    have hsumActive :
        ∫ ω in B, remaining stop m ω ∂μ =
          ∑ k ∈ s, μ.real (B ∩ active k) := by
      have hindicatorInt (k : ℕ) :
          Integrable ((active k).indicator (fun _ => (1 : ℝ))) μ :=
        (integrable_const (1 : ℝ)).indicator (hactiveMeas' k)
      calc
        ∫ ω in B, remaining stop m ω ∂μ =
            ∫ ω in B, (∑ k ∈ s, (active k).indicator (fun _ => (1 : ℝ)) ω) ∂μ := by
              apply setIntegral_congr_fun hBμ
              intro ω _
              simpa [active, Set.indicator_apply] using (hcount ω).symm
        _ = ∑ k ∈ s, ∫ ω in B, (active k).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
          change ∫ ω, (∑ k ∈ s, (active k).indicator (fun _ => (1 : ℝ)) ω) ∂μ.restrict B = _
          rw [integral_finsetSum s (fun k hk =>
            (hindicatorInt k).mono_measure Measure.restrict_le_self)]
        _ = ∑ k ∈ s, μ.real (B ∩ active k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [setIntegral_indicator (hactiveMeas' k), setIntegral_const]
          simp [smul_eq_mul]
    have henergy :
        2 * l ^ 2 * (∫ ω in B, remaining stop m ω ∂μ) ≤
          ∫ ω in B, Φ m ω - Φ N ω ∂μ := by
      calc
        2 * l ^ 2 * (∫ ω in B, remaining stop m ω ∂μ) =
            ∑ k ∈ s, (2 * l ^ 2 * μ.real (B ∩ active k)) := by
              rw [hsumActive, Finset.mul_sum]
        _ ≤ ∑ k ∈ s, (-(∫ ω in B, increment Φ k ω ∂μ)) := by
              apply Finset.sum_le_sum
              intro k hk
              calc
                2 * l ^ 2 * μ.real (B ∩ active k) =
                    -(-(2 * l ^ 2) * μ.real (B ∩ active k)) := by ring
                _ ≤ -(∫ ω in B, increment Φ k ω ∂μ) :=
                    neg_le_neg (hdriftIntegral k hk)
        _ = -(∑ k ∈ s, ∫ ω in B, increment Φ k ω ∂μ) := by
              rw [Finset.sum_neg_distrib]
        _ = -(∫ ω in B, Φ N ω - Φ m ω ∂μ) := by rw [hsumDelta]
        _ = ∫ ω in B, Φ m ω - Φ N ω ∂μ := by
              change -(∫ ω, (Φ N ω - Φ m ω) ∂μ.restrict B) =
                ∫ ω, (Φ m ω - Φ N ω) ∂μ.restrict B
              rw [integral_sub
                    ((hinput.integrable N).mono_measure Measure.restrict_le_self)
                    ((hinput.integrable m).mono_measure Measure.restrict_le_self),
                  integral_sub
                    ((hinput.integrable m).mono_measure Measure.restrict_le_self)
                    ((hinput.integrable N).mono_measure Measure.restrict_le_self)]
              ring
    have hcombined := henergy.trans hpotIntegral
    have hden : 0 < 2 * l ^ 2 := by positivity
    have hraw :
        ∫ ω in B, remaining stop m ω ∂μ ≤
          ((10 * l * r) * μ.real B) / (2 * l ^ 2) :=
      (le_div_iff₀ hden).2 (by
        convert hcombined using 1 <;> ring)
    calc
      ∫ ω in B, remaining stop m ω ∂μ ≤
          ((10 * l * r) * μ.real B) / (2 * l ^ 2) := hraw
      _ = (5 * r / l) * μ.real B := by field_simp; ring
  · have hzero : ∀ ω, remaining stop m ω = 0 := by
      intro ω
      apply Nat.cast_eq_zero.mpr
      apply Nat.sub_eq_zero_of_le
      exact (hinput.finite_stop ω).trans (Nat.le_of_not_ge hmN)
    have hfun : remaining stop m = fun _ => (0 : ℝ) := funext hzero
    rw [hfun]
    simp
    positivity

private def sigmaAtom {Ω : Type*} (σ : Ω → ℕ) (i : ℕ) : Set Ω := {ω | σ ω = i}

private theorem atom_measure_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›} {N : ℕ}
    {σ : Ω → ℕ} (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ)))
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E) :
    (∑ i ∈ Finset.range (N + 1), μ.real (E ∩ sigmaAtom σ i)) ≤ μ.real E := by
  have hEiFi (i : ℕ) : MeasurableSet[F i] (E ∩ sigmaAtom σ i) := by
    have hEiStop : MeasurableSet[hσ.measurableSpace]
        (E ∩ {ω | (σ ω : WithTop ℕ) = i}) :=
      hE.inter (hσ.measurableSet_eq' i)
    have hEi := (hσ.measurableSet_inter_eq_iff E i).mp hEiStop
    simpa [sigmaAtom] using hEi
  have hEiMeas (i : ℕ) : MeasurableSet (E ∩ sigmaAtom σ i) :=
    (F.le i) _ (hEiFi i)
  have hpair : Set.PairwiseDisjoint (Finset.range (N + 1) : Set ℕ)
      (fun i => E ∩ sigmaAtom σ i) := by
    intro i hi j hj hij
    refine Set.disjoint_left.mpr ?_
    intro ω hωi hωj
    simp only [Set.mem_inter_iff] at hωi hωj
    have hσi : σ ω = i := by simpa [sigmaAtom] using hωi.2
    have hσj : σ ω = j := by simpa [sigmaAtom] using hωj.2
    exact hij (hσi.symm.trans hσj)
  have hunion : (⋃ i ∈ Finset.range (N + 1), E ∩ sigmaAtom σ i) ⊆ E := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    rcases hω with ⟨i, hi, hωi⟩
    change ω ∈ E ∩ sigmaAtom σ i at hωi
    simp only [Set.mem_inter_iff] at hωi
    exact hωi.1
  calc
    (∑ i ∈ Finset.range (N + 1), μ.real (E ∩ sigmaAtom σ i)) =
        μ.real (⋃ i ∈ Finset.range (N + 1), E ∩ sigmaAtom σ i) := by
          symm
          exact measureReal_biUnion_finset hpair (fun i hi => hEiMeas i)
    _ ≤ μ.real E := measureReal_mono hunion

private theorem random_remaining_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {N : ℕ} {stop σ : Ω → ℕ} {Φ : ℕ → Ω → ℝ} {l r : ℝ}
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ))) :
    Integrable (fun ω => remaining stop (σ ω) ω) μ := by
  have hstopMeas := nat_measurable_of_stopping hinput.stopping
  have hσMeas := nat_measurable_of_stopping hσ
  have hm : Measurable (fun ω => remaining stop (σ ω) ω) := by
    unfold remaining
    fun_prop
  have hbound (ω : Ω) : ‖remaining stop (σ ω) ω‖ ≤ ‖(N : ℝ)‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (remaining_nonneg (stop := stop) (m := σ ω) ω), Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg N)]
    exact remaining_le_of_stop_le (stop := stop) (m := σ ω) (N := N)
      hinput.finite_stop ω
  exact (integrable_const (N : ℝ)).mono hm.stronglyMeasurable.aestronglyMeasurable
    (ae_of_all μ hbound)

private theorem remaining_atom_decomp {Ω : Type*} {N : ℕ} {stop σ : Ω → ℕ}
    (hstop : ∀ ω, stop ω ≤ N) :
    ∀ ω, remaining stop (σ ω) ω =
      ∑ i ∈ Finset.range (N + 1), (sigmaAtom σ i).indicator (remaining stop i) ω := by
  intro ω
  by_cases hσN : σ ω ≤ N
  · have hi : σ ω ∈ Finset.range (N + 1) := by simp [Finset.mem_range]; omega
    rw [Finset.sum_eq_single (σ ω)]
    · simp [sigmaAtom]
    · intro i hi' hne
      have hnot : ω ∉ sigmaAtom σ i := by
        intro hωi
        have heq : σ ω = i := by simpa [sigmaAtom] using hωi
        exact hne heq.symm
      simp [hnot]
    · intro hnone
      exact (hnone hi).elim
  · have hNσ : N < σ ω := Nat.lt_of_not_ge hσN
    have hstopσ : stop ω ≤ σ ω := (hstop ω).trans hNσ.le
    have hrem : remaining stop (σ ω) ω = 0 := by
      simp [remaining, Nat.sub_eq_zero_of_le hstopσ]
    have hsum :
        (∑ i ∈ Finset.range (N + 1), (sigmaAtom σ i).indicator (remaining stop i) ω) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : σ ω ≠ i := by
        have : i ≤ N := by
          have := Finset.mem_range.mp hi
          omega
        intro heq
        subst i
        exact hσN this
      have hnot : ω ∉ sigmaAtom σ i := by
        intro hωi
        exact hne (by simpa [sigmaAtom] using hωi)
      simp [hnot]
    simp [hrem, hsum]

private theorem mean_at_stopping_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {l r : ℝ} {N : ℕ} {stop σ : Ω → ℕ} {Φ : ℕ → Ω → ℝ}
    (hl : 0 < l) (hr : 0 < r)
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ)))
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E) :
    ∫ ω in E, remaining stop (σ ω) ω ∂μ ≤ (5 * r / l) * μ.real E := by
  have hEμ : MeasurableSet E := hσ.measurableSpace_le _ hE
  have hremInt := random_remaining_integrable hinput hσ
  have hAtomMeas (i : ℕ) : MeasurableSet (sigmaAtom σ i) := by
    have hi : MeasurableSet[F i] (sigmaAtom σ i) := by
      simpa [sigmaAtom] using hσ.measurableSet_eq_of_countable i
    exact (F.le i) _ hi
  have hAtomInt (i : ℕ) :
      Integrable ((sigmaAtom σ i).indicator (remaining stop i)) μ :=
    (remaining_integrable (μ := μ) hinput.stopping hinput.finite_stop).indicator (hAtomMeas i)
  have hdecomp := remaining_atom_decomp (σ := σ) hinput.finite_stop
  have hsumInt :
      ∫ ω in E, remaining stop (σ ω) ω ∂μ =
        ∑ i ∈ Finset.range (N + 1),
          ∫ ω in E ∩ sigmaAtom σ i, remaining stop i ω ∂μ := by
    calc
      ∫ ω in E, remaining stop (σ ω) ω ∂μ =
          ∫ ω in E,
            (∑ i ∈ Finset.range (N + 1), (sigmaAtom σ i).indicator
              (remaining stop i) ω) ∂μ := by
            apply setIntegral_congr_fun hEμ
            intro ω _
            exact hdecomp ω
      _ = ∑ i ∈ Finset.range (N + 1),
            ∫ ω in E, (sigmaAtom σ i).indicator (remaining stop i) ω ∂μ := by
            change ∫ ω, (∑ i ∈ Finset.range (N + 1),
              (sigmaAtom σ i).indicator (remaining stop i) ω) ∂μ.restrict E = _
            rw [integral_finsetSum (Finset.range (N + 1)) (fun i hi =>
              (hAtomInt i).mono_measure Measure.restrict_le_self)]
      _ = ∑ i ∈ Finset.range (N + 1),
            ∫ ω in E ∩ sigmaAtom σ i, remaining stop i ω ∂μ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [setIntegral_indicator (hAtomMeas i)]
  have hmean (i : ℕ) :
      ∫ ω in E ∩ sigmaAtom σ i, remaining stop i ω ∂μ ≤
        (5 * r / l) * μ.real (E ∩ sigmaAtom σ i) := by
    have hEiStop : MeasurableSet[hσ.measurableSpace]
        (E ∩ {ω | (σ ω : WithTop ℕ) = i}) := hE.inter (hσ.measurableSet_eq' i)
    have hEiFi : MeasurableSet[F i] (E ∩ sigmaAtom σ i) := by
      have h := (hσ.measurableSet_inter_eq_iff E i).mp hEiStop
      simpa [sigmaAtom] using h
    exact mean_at_event hl hr hinput (E ∩ sigmaAtom σ i) hEiFi
  have hAtoms := atom_measure_sum_le (μ := μ) (N := N) hσ E hE
  have hC : 0 ≤ 5 * r / l := by positivity
  calc
    ∫ ω in E, remaining stop (σ ω) ω ∂μ =
        ∑ i ∈ Finset.range (N + 1),
          ∫ ω in E ∩ sigmaAtom σ i, remaining stop i ω ∂μ := hsumInt
    _ ≤ ∑ i ∈ Finset.range (N + 1),
          (5 * r / l) * μ.real (E ∩ sigmaAtom σ i) :=
          Finset.sum_le_sum fun i hi => hmean i
    _ = (5 * r / l) *
          ∑ i ∈ Finset.range (N + 1), μ.real (E ∩ sigmaAtom σ i) := by
          rw [← Finset.mul_sum]
    _ ≤ (5 * r / l) * μ.real E :=
          mul_le_mul_of_nonneg_left hAtoms hC

private def survives {Ω : Type*} (C : Set Ω) (stop : Ω → ℕ) (m : ℕ) : Set Ω :=
  C ∩ {ω | m ≤ stop ω}

private theorem block_tail_atom {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {l r : ℝ} {N : ℕ} {stop : Ω → ℕ} {Φ : ℕ → Ω → ℝ}
    (hl : 0 < l) (hr : 0 < r)
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (i : ℕ) (C : Set Ω) (hC : MeasurableSet[F i] C)
    (L : ℕ) (hL : 0 < L) (hceil : 10 * r / l ≤ (L : ℝ)) :
    ∀ q : ℕ,
      μ.real (survives C stop (i + q * L)) ≤ (1 / 2 : ℝ) ^ q * μ.real C := by
  have hratio : 10 * r / l = 2 * (5 * r / l) := by ring
  have hCL : 5 * r / l ≤ (L : ℝ) / 2 := by
    have hceil' : 2 * (5 * r / l) ≤ (L : ℝ) := by nlinarith [hceil, hratio]
    nlinarith [hceil']
  intro q
  induction q with
  | zero =>
      have hsub : survives C stop (i + 0 * L) ⊆ C := by
        intro ω hω
        exact hω.1
      simpa [survives] using (measureReal_mono hsub)
  | succ q ih =>
      let m := i + q * L
      let B := survives C stop m
      let Bnext := survives C stop (m + L)
      have hindex : m + L = i + (q + 1) * L := by
        dsimp [m]
        rw [Nat.succ_mul]
        omega
      have hBm : MeasurableSet[F m] B := by
        have hCi : MeasurableSet[F m] C := F.mono (by dsimp [m]; omega) _ hC
        have hStopGe : MeasurableSet[F m] {ω | m ≤ stop ω} := by
          simpa using hinput.stopping.measurableSet_ge_of_countable m
        exact hCi.inter hStopGe
      have hBnextMeas : MeasurableSet Bnext := by
        have hCm : MeasurableSet[F (m + L)] C :=
          F.mono (by dsimp [m]; omega) _ hC
        have hStopNext : MeasurableSet[F (m + L)] {ω | m + L ≤ stop ω} := by
          convert hinput.stopping.measurableSet_ge_of_countable (m + L) using 1
          ext ω
          simp only [Set.mem_setOf_eq]
          exact WithTop.coe_le_coe.symm
        exact (F.le (m + L)) _ (hCm.inter hStopNext)
      have hremInt : Integrable (remaining stop m) μ :=
        remaining_integrable (μ := μ) hinput.stopping hinput.finite_stop
      have hmean := mean_at_event hl hr hinput B hBm
      have hBsub : Bnext ⊆ B := by
        intro ω hω
        constructor
        · exact hω.1
        · exact le_trans (Nat.le_add_right m L) hω.2
      have hremLower :
          (L : ℝ) * μ.real Bnext ≤ ∫ ω in Bnext, remaining stop m ω ∂μ := by
        calc
          (L : ℝ) * μ.real Bnext = ∫ ω in Bnext, (L : ℝ) ∂μ := by
            rw [setIntegral_const, smul_eq_mul]
            ring
          _ ≤ ∫ ω in Bnext, remaining stop m ω ∂μ := by
            apply setIntegral_mono_on (integrable_const (L : ℝ)).integrableOn
              hremInt.integrableOn hBnextMeas
            intro ω hω
            have hmn : m + L ≤ stop ω := hω.2
            have hnat : L ≤ stop ω - m := by omega
            unfold remaining
            exact_mod_cast hnat
      have hremSubset :
          ∫ ω in Bnext, remaining stop m ω ∂μ ≤ ∫ ω in B, remaining stop m ω ∂μ := by
        have hnonneg : 0 ≤ᵐ[μ.restrict B] remaining stop m :=
          ae_of_all _ (remaining_nonneg stop m)
        exact setIntegral_mono_set
          (hremInt.integrableOn.mono_set (Set.subset_univ B)) hnonneg
          (ae_of_all _ hBsub)
      have hstep : (L : ℝ) * μ.real Bnext ≤ (5 * r / l) * μ.real B :=
        hremLower.trans (hremSubset.trans hmean)
      have hstep' : (L : ℝ) * μ.real Bnext ≤ (L : ℝ) * ((1 / 2 : ℝ) * μ.real B) := by
        calc
          (L : ℝ) * μ.real Bnext ≤ (5 * r / l) * μ.real B := hstep
          _ ≤ (L : ℝ) / 2 * μ.real B :=
            mul_le_mul_of_nonneg_right hCL (measureReal_nonneg)
          _ = (L : ℝ) * ((1 / 2 : ℝ) * μ.real B) := by ring
      have hstep'' : μ.real Bnext ≤ (1 / 2 : ℝ) * μ.real B := by
        exact le_of_mul_le_mul_left hstep' (by exact_mod_cast hL)
      calc
        μ.real (survives C stop (i + (q + 1) * L)) = μ.real Bnext := by
          congr 1
          simp [Bnext, hindex]
        _ ≤ (1 / 2 : ℝ) * μ.real B := hstep''
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ q * μ.real C) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (q + 1) * μ.real C := by
          rw [pow_succ]
          ring

private def tailEvent {Ω : Type*} (stop σ : Ω → ℕ) (n : ℕ) : Set Ω :=
  {ω | n ≤ stop ω - σ ω}

private theorem block_exp_bound (n L : ℕ) (hL : 0 < L) :
    (1 / 2 : ℝ) ^ (n / L) ≤
      2 * Real.exp (-Real.log 2 * (n : ℝ) / (L : ℝ)) := by
  let q := n / L
  have hqdecomp : q * L + n % L = n := by
    simpa [q, Nat.mul_comm] using Nat.div_add_mod n L
  have hmod : n % L < L := Nat.mod_lt n hL
  have hlt : n < (q + 1) * L := by
    calc
      n = q * L + n % L := hqdecomp.symm
      _ < q * L + L := Nat.add_lt_add_left hmod _
      _ = (q + 1) * L := by rw [Nat.succ_mul]
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hfrac : (n : ℝ) / (L : ℝ) < (q : ℝ) + 1 := by
    apply (div_lt_iff₀ hLreal).2
    exact_mod_cast hlt
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : -Real.log 2 * (q : ℝ) ≤
      Real.log 2 - Real.log 2 * ((n : ℝ) / (L : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_left hfrac hlog
    nlinarith [hmul]
  have hexpneg : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
    norm_num
  have hpow : (1 / 2 : ℝ) ^ q = Real.exp (-Real.log 2 * (q : ℝ)) := by
    calc
      (1 / 2 : ℝ) ^ q = (Real.exp (-Real.log 2)) ^ q := by rw [hexpneg]
      _ = Real.exp ((q : ℝ) * (-Real.log 2)) := by
        symm
        exact Real.exp_nat_mul (-Real.log 2) q
      _ = Real.exp (-Real.log 2 * (q : ℝ)) := by congr 1 <;> ring
  calc
    (1 / 2 : ℝ) ^ (n / L) = Real.exp (-Real.log 2 * (q : ℝ)) := by simpa [q] using hpow
    _ ≤ Real.exp (Real.log 2 - Real.log 2 * ((n : ℝ) / (L : ℝ))) :=
          Real.exp_le_exp.mpr harg
    _ = 2 * Real.exp (-Real.log 2 * (n : ℝ) / (L : ℝ)) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
          ring

private theorem tail_at_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {l r : ℝ} {N : ℕ} {stop σ : Ω → ℕ} {Φ : ℕ → Ω → ℝ}
    (hl : 0 < l) (hr : 0 < r)
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ)))
    (n : ℕ) (hn : 1 ≤ n) (L : ℕ) (hL : 0 < L)
    (hceil : 10 * r / l ≤ (L : ℝ))
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E) :
    μ.real (E ∩ tailEvent stop σ n) ≤
      (2 * Real.exp (-Real.log 2 * (n : ℝ) / (L : ℝ))) * μ.real E := by
  let q := n / L
  let p0 : ℝ := (1 / 2 : ℝ) ^ q
  let Bi : ℕ → Set Ω := fun i => E ∩ sigmaAtom σ i ∩ {ω | i + n ≤ stop ω}
  have hqL : q * L ≤ n := by simpa [q] using Nat.div_mul_le_self n L
  have hAtoms : (∑ i ∈ Finset.range (N + 1), μ.real (E ∩ sigmaAtom σ i)) ≤ μ.real E :=
    atom_measure_sum_le (μ := μ) (N := N) hσ E hE
  have htailSub : E ∩ tailEvent stop σ n ⊆
      ⋃ i ∈ Finset.range (N + 1), Bi i := by
    intro ω hω
    simp only [Set.mem_inter_iff] at hω
    have hplus : σ ω + n ≤ stop ω := by
      dsimp [tailEvent] at hω
      have hσlt : σ ω < stop ω := by
        apply (Nat.sub_pos_iff_lt).mp
        exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hn hω.2)
      calc
        σ ω + n ≤ σ ω + (stop ω - σ ω) := Nat.add_le_add_left hω.2 _
        _ = stop ω := Nat.add_sub_of_le hσlt.le
    have hiN : σ ω ≤ N :=
      (Nat.le_add_right (σ ω) n).trans (hplus.trans (hinput.finite_stop ω))
    have hi : σ ω ∈ Finset.range (N + 1) := by simp [Finset.mem_range]; omega
    have hBi : ω ∈ Bi (σ ω) := by
      simp [Bi, sigmaAtom, hω.1, hplus]
    simp only [Set.mem_iUnion]
    exact ⟨σ ω, hi, hBi⟩
  have hBiBound (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
      μ.real (Bi i) ≤ p0 * μ.real (E ∩ sigmaAtom σ i) := by
    have hEiStop : MeasurableSet[hσ.measurableSpace]
        (E ∩ {ω | (σ ω : WithTop ℕ) = i}) := hE.inter (hσ.measurableSet_eq' i)
    have hEiFi : MeasurableSet[F i] (E ∩ sigmaAtom σ i) := by
      have h := (hσ.measurableSet_inter_eq_iff E i).mp hEiStop
      simpa [sigmaAtom] using h
    have hsub : Bi i ⊆ survives (E ∩ sigmaAtom σ i) stop (i + q * L) := by
      intro ω hω
      refine ⟨hω.1, ?_⟩
      exact (Nat.add_le_add_left hqL i).trans hω.2
    calc
      μ.real (Bi i) ≤ μ.real (survives (E ∩ sigmaAtom σ i) stop (i + q * L)) :=
        measureReal_mono hsub
      _ ≤ p0 * μ.real (E ∩ sigmaAtom σ i) := by
        simpa [p0, q] using
          (block_tail_atom hl hr hinput i (E ∩ sigmaAtom σ i) hEiFi L hL hceil q)
  calc
    μ.real (E ∩ tailEvent stop σ n) ≤
        μ.real (⋃ i ∈ Finset.range (N + 1), Bi i) := by
          exact measureReal_mono htailSub
            (measure_ne_top_of_subset (Set.subset_univ _) (by simp))
    _ ≤ ∑ i ∈ Finset.range (N + 1), μ.real (Bi i) :=
        measureReal_biUnion_finset_le (Finset.range (N + 1)) Bi
    _ ≤ ∑ i ∈ Finset.range (N + 1), p0 * μ.real (E ∩ sigmaAtom σ i) :=
        Finset.sum_le_sum fun i hi => hBiBound i hi
    _ = p0 * ∑ i ∈ Finset.range (N + 1), μ.real (E ∩ sigmaAtom σ i) := by
        rw [← Finset.mul_sum]
    _ ≤ p0 * μ.real E :=
        mul_le_mul_of_nonneg_left hAtoms (by positivity)
    _ ≤ (2 * Real.exp (-Real.log 2 * (n : ℝ) / (L : ℝ))) * μ.real E := by
        apply mul_le_mul_of_nonneg_right
          (block_exp_bound n L hL) (measureReal_nonneg)

private theorem conditional_tail_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {l r : ℝ} {N : ℕ} {stop σ : Ω → ℕ} {Φ : ℕ → Ω → ℝ}
    (hl : 0 < l) (hr : 0 < r)
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ)))
    (n : ℕ) (hn : 1 ≤ n) (L : ℕ) (hL : 0 < L)
    (hceil : 10 * r / l ≤ (L : ℝ)) :
    ∀ᵐ ω ∂μ,
      AndersonAC.S6.conditionalProbability μ hσ.measurableSpace
        (tailEvent stop σ n) ω ≤ 2 * Real.exp (-Real.log 2 * (n : ℝ) / (L : ℝ)) := by
  let p := 2 * Real.exp (-Real.log 2 * (n : ℝ) / (L : ℝ))
  let f := AndersonAC.S6.conditionalProbability μ hσ.measurableSpace (tailEvent stop σ n)
  let A := {ω | p < f ω}
  have hstopMeas := nat_measurable_of_stopping hinput.stopping
  have hσMeas := nat_measurable_of_stopping hσ
  have hdiffMeas : Measurable (fun ω => stop ω - σ ω) := hstopMeas.sub hσMeas
  have hTailMeas : MeasurableSet (tailEvent stop σ n) := by
    dsimp [tailEvent]
    exact measurableSet_le measurable_const hdiffMeas
  have hindInt : Integrable ((tailEvent stop σ n).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hTailMeas
  have hceInt : Integrable f μ := by
    dsimp [f, AndersonAC.S6.conditionalProbability]
    exact integrable_condExp
  have hA : MeasurableSet[hσ.measurableSpace] A := by
    dsimp [A, f, p, AndersonAC.S6.conditionalProbability]
    exact measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable
  have hAupper : ∫ ω in A, f ω ∂μ ≤ p * μ.real A := by
    calc
      ∫ ω in A, f ω ∂μ =
          ∫ ω in A,
            μ[(tailEvent stop σ n).indicator (fun _ => (1 : ℝ)) | hσ.measurableSpace] ω ∂μ := by
              rfl
      _ = ∫ ω in A, (tailEvent stop σ n).indicator (fun _ => (1 : ℝ)) ω ∂μ :=
          setIntegral_condExp hσ.measurableSpace_le hindInt hA
      _ = μ.real (A ∩ tailEvent stop σ n) := by
          rw [setIntegral_indicator hTailMeas, setIntegral_const]
          simp [smul_eq_mul]
      _ ≤ p * μ.real A := tail_at_event hl hr hinput hσ n hn L hL hceil A hA
  have hA0 : μ A = 0 := by
    by_contra hAne
    have hp : 0 ≤ p := by positivity
    have hstrict := setIntegral_gt_gt hp
      (hceInt.integrableOn.mono_set (Set.subset_univ A)) hAne
    have hstrict' : p * μ.real A < ∫ ω in A, f ω ∂μ := by
      nlinarith [hstrict]
    exact (not_lt_of_ge hAupper) hstrict'
  rw [ae_iff]
  simpa [A, f, p, not_le, AndersonAC.S6.conditionalProbability] using hA0

private theorem conditional_mean_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ ‹MeasurableSpace Ω›}
    {l r : ℝ} {N : ℕ} {stop σ : Ω → ℕ} {Φ : ℕ → Ω → ℝ}
    (hl : 0 < l) (hr : 0 < r)
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ))) :
    ∀ᵐ ω ∂μ,
      μ[(fun ω => remaining stop (σ ω) ω) | hσ.measurableSpace] ω ≤ 5 * r / l := by
  have hremInt := random_remaining_integrable hinput hσ
  have hceInt : Integrable
      (fun ω => μ[(fun ω => remaining stop (σ ω) ω) | hσ.measurableSpace] ω) μ :=
    integrable_condExp
  let f := fun ω => μ[(fun ω => remaining stop (σ ω) ω) | hσ.measurableSpace] ω
  let A := {ω | 5 * r / l < f ω}
  have hA : MeasurableSet[hσ.measurableSpace] A := by
    dsimp [A, f]
    exact measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable
  have hAupper : ∫ ω in A, f ω ∂μ ≤ (5 * r / l) * μ.real A := by
    calc
      ∫ ω in A, f ω ∂μ = ∫ ω in A, remaining stop (σ ω) ω ∂μ := by
        dsimp [f]
        exact setIntegral_condExp hσ.measurableSpace_le hremInt hA
      _ ≤ (5 * r / l) * μ.real A := mean_at_stopping_event hl hr hinput hσ A hA
  have hA0 : μ A = 0 := by
    by_contra hAne
    have hstrict := setIntegral_gt_gt (by positivity : 0 ≤ 5 * r / l)
      (hceInt.integrableOn.mono_set (Set.subset_univ A)) hAne
    have hstrict' : (5 * r / l) * μ.real A < ∫ ω in A, f ω ∂μ := by
      nlinarith [hstrict]
    exact (not_lt_of_ge hAupper) hstrict'
  rw [ae_iff]
  simpa [A, f, not_le] using hA0

end AndersonAC.SolS6Heat

namespace AndersonAC.SolS6

theorem heatCount_proof : HeatCountStatement := by
  unfold HeatCountStatement
  intro Ω mΩ μ hμ F l r N stop σ Φ hl hr hinput hσ
  change AndersonAC.S6.Planned.heat_count μ F l r N stop σ Φ hl hr hinput hσ
  unfold AndersonAC.S6.Planned.heat_count
  constructor
  · exact AndersonAC.SolS6Heat.conditional_mean_bound hl hr hinput hσ
  · intro n hn
    let L : ℕ := ⌈10 * r / l⌉₊
    have hL : 0 < L := by
      apply Nat.ceil_pos.mpr
      positivity
    have hceil : 10 * r / l ≤ (L : ℝ) := by
      dsimp [L]
      exact Nat.le_ceil _
    simpa [L, AndersonAC.SolS6Heat.tailEvent] using
      (AndersonAC.SolS6Heat.conditional_tail_bound hl hr hinput hσ n hn L hL hceil)

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.heatCount_proof

end
