import AndersonAC.AgentS78.Construction.ClearingTrialZNull

/-!
# the residual law with an exceptional set

`Residual` (ClearingTrialResidual.lean) with the residual identity required only off a
measurable null set `Z` invariant under the site and digit flips, on which the trial's data are
constant (as for `compTrial φ` with `φ` constant on `Z`).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.ResidualZ

open AndersonAC.S6
open AndersonAC.AgentS78.Residual (siteSuffix siteMask siteSuffix_measurable siteSuffix_bound
  siteDigits_flip_other integral_indicator_siteSuffix integral_indicator_siteSuffix_sq
  integrable_indicator_bounded siteSuffix_abs_le piece piece_measurable indicator_decomp
  trunc_residual_eq trunc_sq_eq residual_measurable)

section Trial

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ} {g0 : Ω → Matrix ι ι ℂ}
  {order : ι ≃ Fin (Fintype.card ι)}

theorem history_agreeZ (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (hhist : ∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k)
    (R : ι → Ω → ℝ) (Z : Set Ω)
    (hres : ∀ k ω, ω ∉ Z → k < q.stop ω → q.residual k ω = R (q.pivot k ω) ω)
    (y : ι) (F : Ω → Ω) (hF : ∀ i, i ≠ y → ∀ ω, R i (F ω) = R i ω)
    (hFZ : ∀ ω, ω ∉ Z → F ω ∉ Z) :
    ∀ k ω, ω ∉ Z → (∀ j < k, j < q.stop ω ∧ q.pivot j ω ≠ y) →
      ∀ j < k, q.pivot j (F ω) = q.pivot j ω ∧ q.residual j (F ω) = q.residual j ω ∧
        j < q.stop (F ω) := by
  intro k
  induction k with
  | zero => intro ω _ _ j hj; omega
  | succ k ih =>
    intro ω hωZ hω j hj
    have hprev := ih ω hωZ (fun j hj => hω j (by omega))
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hprev j hj
    have hsat : q.history j ≤ Residual.satSpace ω (F ω) := by
      rw [hhist j]
      exact Residual.queryHistory_sat _ _ j ω (F ω)
        (fun i hi => ⟨(hprev i hi).1.symm, (hprev i hi).2.1.symm⟩)
    have hpiv : q.pivot j (F ω) = q.pivot j ω := by
      have hm : MeasurableSet[q.history j] (q.pivot j ⁻¹' {q.pivot j ω}) :=
        q.pivot_predictable j (measurableSet_singleton _)
      have := (hsat _ hm).mp rfl
      exact this
    have hstop : j < q.stop (F ω) := by
      have hm : MeasurableSet[q.history j] {ω | ((q.stop ω : ℕ) : WithTop ℕ) ≤ (j : WithTop ℕ)} :=
        q.stopping j
      have h1 := hsat _ hm
      have h2 : ¬ ((q.stop ω : WithTop ℕ) ≤ (j : WithTop ℕ)) := by
        exact_mod_cast (not_le.mpr (hω j hj).1)
      have h3 : ¬ ((q.stop (F ω) : WithTop ℕ) ≤ (j : WithTop ℕ)) := fun h => h2 (h1.mpr h)
      have h4 : ¬ q.stop (F ω) ≤ j := by exact_mod_cast h3
      omega
    refine ⟨hpiv, ?_, hstop⟩
    rw [hres j (F ω) (hFZ ω hωZ) hstop, hres j ω hωZ (hω j hj).1, hpiv]
    exact hF _ (hω j hj).2 ω

/-- Events of the history on `{k < stop, pivot k = y}` are invariant under such maps. -/
theorem event_invariantZ (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (hhist : ∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k)
    (R : ι → Ω → ℝ) (Z : Set Ω)
    (hres : ∀ k ω, ω ∉ Z → k < q.stop ω → q.residual k ω = R (q.pivot k ω) ω)
    (y : ι) (F : Ω → Ω) (hF : ∀ i, i ≠ y → ∀ ω, R i (F ω) = R i ω)
    (hFZ : ∀ ω, ω ∉ Z → F ω ∉ Z)
    (k : ℕ) (E : Set Ω) (hE : MeasurableSet[q.history k] E) (ω : Ω) (hωZ : ω ∉ Z)
    (hk : k < q.stop ω) (hy : q.pivot k ω = y) : F ω ∈ E ↔ ω ∈ E := by
  have hω : ∀ j < k, j < q.stop ω ∧ q.pivot j ω ≠ y :=
    fun j hj => ⟨by omega, hy ▸ Residual.pivot_ne q ω hj hk⟩
  have hagree := history_agreeZ q hhist R Z hres y F hF hFZ k ω hωZ hω
  have hsat : q.history k ≤ Residual.satSpace ω (F ω) := by
    rw [hhist k]
    exact Residual.queryHistory_sat _ _ k ω (F ω)
      (fun i hi => ⟨(hagree i hi).1.symm, (hagree i hi).2.1.symm⟩)
  exact (hsat E hE).symm


end Trial

section TrialLaw

open AndersonAC.S2 AndersonAC.SolS2

variable {S : Type} [Fintype S] [DecidableEq S] {M : ℕ → ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {core : Finset ι} {t : ℝ} {r : RandomSources S M → ι → ℂ}
  {g0 : RandomSources S M → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}

/-- The residual identity off a measurable flip-invariant null set on which the trial's data
are constant. -/
structure LawHypZ (q : StoppedTrial (Ω := RandomSources S M) core t r g0 order) (v : ι → S)
    (lam : ℝ) (hgt : ι → ℕ) (Z : Set (RandomSources S M)) : Prop where
  hist : ∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k
  inj : Function.Injective v
  res : ∀ k ω, ω ∉ Z → k < q.stop ω →
    q.residual k ω = siteSuffix S lam (hgt (q.pivot k ω)) (v (q.pivot k ω)) ω
  null : sourcesLaw S M Z = 0
  site : ∀ y ω, signFlip S (siteMask S y) ω ∈ Z ↔ ω ∈ Z
  digit : ∀ y n ω, signFlip S {Sum.inl (y, n)} ω ∈ Z ↔ ω ∈ Z
  const : ∀ ω ω', ω ∈ Z → ω' ∈ Z → q.stop ω = q.stop ω' ∧
    ∀ k, q.pivot k ω = q.pivot k ω' ∧ q.residual k ω = q.residual k ω'

variable {q : StoppedTrial (Ω := RandomSources S M) core t r g0 order} {v : ι → S} {lam : ℝ}
  {hgt : ι → ℕ} {Z : Set (RandomSources S M)}

theorem LawHypZ.ae_notMem (hq : LawHypZ q v lam hgt Z) : ∀ᵐ ω ∂sourcesLaw S M, ω ∉ Z :=
  measure_eq_zero_iff_ae_notMem.mp hq.null

theorem piece_invZ (hq : LawHypZ q v lam hgt Z) (k : ℕ) {s : Set (RandomSources S M)}
    (hs : MeasurableSet[q.history k] s) (y : ι) {mask : Set (SignIndex S)}
    (hmask : mask ⊆ siteMask S (v y)) (hmZ : ∀ ω, signFlip S mask ω ∈ Z ↔ ω ∈ Z)
    (ω : RandomSources S M) :
    signFlip S mask ω ∈ piece q k s y ↔ ω ∈ piece q k s y := by
  let R : ι → RandomSources S M → ℝ := fun i ω => siteSuffix S lam (hgt i) (v i) ω
  have hF : ∀ i, i ≠ y → ∀ ω, R i (signFlip S mask ω) = R i ω := by
    intro i hi ω
    simp only [R, siteSuffix]
    rw [siteDigits_flip_other S hmask (hq.inj.ne hi)]
  have hFZ : ∀ ω, ω ∉ Z → signFlip S mask ω ∉ Z := fun ω h h' => h ((hmZ ω).mp h')
  have key : ∀ ω, ω ∈ piece q k s y → (signFlip S mask ω ∈ piece q k s y ↔ ω ∈ piece q k s y) := by
    intro ω hω
    by_cases hωZ : ω ∈ Z
    · have hFω : signFlip S mask ω ∈ Z := (hmZ ω).mpr hωZ
      obtain ⟨-, hpr⟩ := hq.const ω (signFlip S mask ω) hωZ hFω
      have hsat : q.history k ≤ Residual.satSpace ω (signFlip S mask ω) := by
        rw [hq.hist k]
        exact Residual.queryHistory_sat _ _ k _ _ (fun i _ => hpr i)
      exact (hsat _ (piece_measurable k hs y)).symm
    · exact event_invariantZ q hq.hist R Z hq.res y _ hF hFZ k _ (piece_measurable k hs y) ω
        hωZ hω.1.2 (by simpa using hω.2)
  constructor
  · intro h
    have h3 := (key _ h).mpr h
    rwa [signFlip_involutive S mask ω] at h3
  · intro h
    exact (key ω h).mpr h

theorem residual_indicator_eqZ (hq : LawHypZ q v lam hgt Z) (k : ℕ) (s : Set (RandomSources S M))
    (f : ℝ → ℝ) :
    (s ∩ {ω | k < q.stop ω}).indicator (fun ω => f (q.residual k ω)) =ᵐ[sourcesLaw S M]
      (s ∩ {ω | k < q.stop ω}).indicator
        (fun ω => f (siteSuffix S lam (hgt (q.pivot k ω)) (v (q.pivot k ω)) ω)) := by
  filter_upwards [hq.ae_notMem] with ω hωZ
  by_cases hω : ω ∈ s ∩ {ω | k < q.stop ω}
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hq.res k ω hωZ hω.2]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]

theorem setIntegral_residualZ (hq : LawHypZ q v lam hgt Z) (k : ℕ) {s : Set (RandomSources S M)}
    (hs : MeasurableSet[q.history k] s) :
    ∫ ω, (s ∩ {ω | k < q.stop ω}).indicator (q.residual k) ω ∂sourcesLaw S M = 0 := by
  have h1 := residual_indicator_eqZ hq k s id
  simp only [id] at h1
  rw [integral_congr_ae h1, indicator_decomp k _ (fun y ω => siteSuffix S lam (hgt y) (v y) ω)]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun y _ => ?_
    have hE := q.history.le k _ (piece_measurable k hs y)
    exact integral_indicator_siteSuffix lam (hgt y) (v y) _ hE
      (piece_invZ hq k hs y le_rfl (hq.site (v y)))
  · intro y _
    exact integrable_indicator_bounded (siteSuffix_measurable S lam (hgt y) (v y)) |lam|
      (siteSuffix_abs_le (v y) (hgt y)) _ (q.history.le k _ (piece_measurable k hs y))

theorem setIntegral_residual_sqZ (hq : LawHypZ q v lam hgt Z) (k : ℕ) {s : Set (RandomSources S M)}
    (hs : MeasurableSet[q.history k] s) :
    ∫ ω, (s ∩ {ω | k < q.stop ω}).indicator (fun ω => q.residual k ω ^ 2) ω ∂sourcesLaw S M =
      ∫ ω, (s ∩ {ω | k < q.stop ω}).indicator
        (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω))) ω ∂sourcesLaw S M := by
  rw [integral_congr_ae (residual_indicator_eqZ hq k s (fun x => x ^ 2)),
    indicator_decomp k _ (fun y ω => siteSuffix S lam (hgt y) (v y) ω ^ 2),
    indicator_decomp k _ (fun y _ => lam ^ 2 / (3 * 4 ^ hgt y))]
  have hEm : ∀ y, MeasurableSet ((s ∩ {ω | k < q.stop ω}) ∩ q.pivot k ⁻¹' {y}) :=
    fun y => q.history.le k _ (piece_measurable k hs y)
  rw [integral_finset_sum, integral_finset_sum]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_indicator_siteSuffix_sq lam (hgt y) (v y) _ (hEm y)
      (fun n => piece_invZ hq k hs y (by rintro _ rfl; exact ⟨n, rfl⟩) (hq.digit (v y) n)),
      integral_indicator_const _ (hEm y), smul_eq_mul, mul_comm]
  · intro y _
    exact (integrable_const _).indicator (hEm y)
  · intro y _
    refine integrable_indicator_bounded
      ((siteSuffix_measurable S lam (hgt y) (v y)).pow_const 2) (|lam| ^ 2) (fun ω => ?_) _ (hEm y)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (siteSuffix_abs_le (v y) (hgt y) ω) 2

theorem integrable_truncZ (hq : LawHypZ q v lam hgt Z) (k : ℕ) (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |x| ≤ |lam| → |f x| ≤ C) :
    Integrable ({ω | k < q.stop ω}.indicator (fun ω => f (q.residual k ω))) (sourcesLaw S M) := by
  have hG : MeasurableSet {ω | k < q.stop ω} :=
    q.history.le k _ (stopping_lt_measurableSet q k)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (by simp))
  refine Integrable.of_bound ((hf.comp (residual_measurable k)).indicator hG).aestronglyMeasurable
    C ?_
  filter_upwards [hq.ae_notMem] with ω hωZ
  by_cases hω : ω ∈ {ω | k < q.stop ω}
  · rw [Set.indicator_of_mem hω, Real.norm_eq_abs]
    apply hC
    rw [hq.res k ω hωZ hω]
    exact siteSuffix_abs_le _ _ ω
  · rw [Set.indicator_of_notMem hω, norm_zero]; exact hC0

/-- The revealed residual is centered given the history. -/
theorem condExp_trunc_residualZ (hq : LawHypZ q v lam hgt Z) (k : ℕ) :
    (sourcesLaw S M)[(truncTrial q).residual k | q.history k] =ᵐ[sourcesLaw S M] 0 := by
  rw [trunc_residual_eq]
  have hY := integrable_truncZ hq k id measurable_id |lam| (fun x hx => hx)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (q.history.le k) hY
    (fun s _ _ => integrableOn_zero) (fun s hs _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [integral_zero, ← integral_indicator (q.history.le k _ hs), Set.indicator_indicator]
  exact (setIntegral_residualZ hq k hs).symm

/-- The conditional second moment of the revealed residual given the history. -/
theorem condExp_trunc_residual_sqZ (hq : LawHypZ q v lam hgt Z) (k : ℕ) :
    (sourcesLaw S M)[fun ω => (truncTrial q).residual k ω ^ 2 | q.history k] =ᵐ[sourcesLaw S M]
      {ω | k < q.stop ω}.indicator (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω))) := by
  have hsq : (fun ω => (truncTrial q).residual k ω ^ 2) =
      {ω | k < q.stop ω}.indicator (fun ω => q.residual k ω ^ 2) := by
    rw [trunc_residual_eq]
    funext ω
    by_cases hω : ω ∈ {ω | k < q.stop ω}
    · simp only [Set.indicator_of_mem hω]
    · simp only [Set.indicator_of_notMem hω]; ring
  rw [hsq]
  have hY := integrable_truncZ hq k (fun x => x ^ 2) (measurable_id.pow_const 2) (|lam| ^ 2)
    (fun x hx => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  have hGH := stopping_lt_measurableSet q k
  have hσ : StronglyMeasurable[q.history k] (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω))) :=
    ((measurable_of_countable (fun i : ι => lam ^ 2 / (3 * 4 ^ hgt i))).comp
      (q.pivot_predictable k)).stronglyMeasurable
  have hg : StronglyMeasurable[q.history k]
      ({ω | k < q.stop ω}.indicator (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω)))) :=
    hσ.indicator hGH
  have hgint : Integrable ({ω | k < q.stop ω}.indicator
      (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω)))) (sourcesLaw S M) := by
    refine Integrable.of_bound (hg.mono (q.history.le k)).aestronglyMeasurable (lam ^ 2)
      (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ {ω | k < q.stop ω}
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_self (sq_nonneg _) (by
        have : (1 : ℝ) ≤ 4 ^ hgt (q.pivot k ω) := one_le_pow₀ (by norm_num)
        linarith)
    · rw [Set.indicator_of_notMem hω, norm_zero]; positivity
  refine (ae_eq_condExp_of_forall_setIntegral_eq (q.history.le k) hY
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => ?_) hg.aestronglyMeasurable).symm
  rw [← integral_indicator (q.history.le k _ hs), ← integral_indicator (q.history.le k _ hs),
    Set.indicator_indicator, Set.indicator_indicator]
  exact (setIntegral_residual_sqZ hq k hs).symm

end TrialLaw

/-! ## The clearing trial -/

section Clearing

open AndersonAC.S78 AndersonAC.S2 AndersonAC.AgentS78
open AndersonAC.AgentS78.Residual (scaleCoupling_sq near_coupled)

/-- The residual input of the clearing trial, with the residual identity off an exceptional
set `Z` on which the trial repeats its data at a sample off `Z`. -/
theorem clearingResidualZ {d m n₀ : ℕ} {cP CP : ℝ} {qlag : ℝ → ℝ} {u : ℝ} {j : ℕ} {M : ℕ → ℕ}
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : n₀ < j) (hsched : clearingScheduled j m)
    {x : RunRecord d m} (hxg : ClearingGoodAt cP CP qlag n₀ u j x) {B : Finset (ActiveSite x)}
    (hB : B.Nonempty) (hBmem : B.map (Function.Embedding.subtype _) ∈ x.components)
    (hsep : ∀ z ∈ x.pending, z ∉ B.map (Function.Embedding.subtype _) →
      ∀ y ∈ B.map (Function.Embedding.subtype _),
        separationRadius j - inspectionRadius j / 2 < physicalDistance d m z y)
    {order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x))}
    (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (S78.Torus d m) M) B (stageScale u j m)
      (fun _ i => x.r i) (fun _ => trialG0 x) order)
    {Z : Set (RandomSources (S78.Torus d m) M)}
    (hq : LawHypZ q Subtype.val (OAI.Anderson.scaleCoupling n₀ u)
      (fun i => x.prefixLength i.val) Z)
    (hrep : ∀ ω, ∃ ω', (∀ k, k < q.stop ω' → q.residual k ω' =
        siteSuffix (S78.Torus d m) (OAI.Anderson.scaleCoupling n₀ u)
          (x.prefixLength (q.pivot k ω').val) (q.pivot k ω').val ω') ∧
      q.stop ω = q.stop ω' ∧ ∀ k, q.pivot k ω = q.pivot k ω' ∧ q.residual k ω = q.residual k ω') :
    TrialResidualInput (truncTrial q) (sourcesLaw (S78.Torus d m) M) 4
      (fun a b => physicalDistance d m a.val b.val) (inspectionRadius j) := by
  have hj1 : 1 ≤ j := by omega
  have hjm : j ≤ m := (Nat.div_le_self m 2).trans' hsched
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have h4j : (0 : ℝ) < 4 ^ j := by positivity
  have h4m : (0 : ℝ) < 4 ^ m := by positivity
  have htu : u / 4 ^ j ≤ (stageScale u j m) := by
    unfold stageScale; have : 0 ≤ u / 4 ^ m := by positivity
    linarith
  have htpos : 0 < (stageScale u j m) := lt_of_lt_of_le (by positivity) htu
  -- coupled pivots: the variance and the size of the residual
  have hσ : ∀ i : ActiveSite x, x.prefixLength i.val + n₀ = j →
      (OAI.Anderson.scaleCoupling n₀ u) ^ 2 / (3 * 4 ^ x.prefixLength i.val) = u / 4 ^ j := by
    intro i hi
    rw [scaleCoupling_sq n₀ hu0.le, ← hi, pow_add]
    field_simp
  have hbound : ∀ i : ActiveSite x, x.prefixLength i.val + n₀ = j →
      |(OAI.Anderson.scaleCoupling n₀ u)| / 2 ^ x.prefixLength i.val ≤ 4 * Real.sqrt (stageScale u j m) := by
    intro i hi
    have hsq : (|(OAI.Anderson.scaleCoupling n₀ u)| / 2 ^ x.prefixLength i.val) ^ 2 = 3 * (u / 4 ^ j) := by
      have h2 : ((2 : ℝ) ^ x.prefixLength i.val) ^ 2 = 4 ^ x.prefixLength i.val := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [div_pow, sq_abs, h2, ← hσ i hi]
      field_simp
    have h1 : |(OAI.Anderson.scaleCoupling n₀ u)| / 2 ^ x.prefixLength i.val ≤ Real.sqrt (4 * (stageScale u j m)) := by
      apply Real.le_sqrt_of_sq_le
      rw [hsq]; linarith
    have h2 : Real.sqrt (4 * (stageScale u j m)) = 2 * Real.sqrt (stageScale u j m) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have h3 : 0 ≤ Real.sqrt (stageScale u j m) := Real.sqrt_nonneg (stageScale u j m)
    linarith
  have hcoupled : ∀ k ω, k < q.stop ω →
      distanceToCore (fun a b : ActiveSite x => physicalDistance d m a.val b.val) B
        (q.pivot k ω) < inspectionRadius j / 2 →
      x.prefixLength (q.pivot k ω).val + n₀ = j := by
    intro k ω hk hnear
    obtain ⟨_, hnotcore, -⟩ := q.heat k ω hk
    exact near_coupled hxg hB hBmem hsep hj1 hnotcore hnear
  refine
    { residual_bound := fun k ω hk hnear => ?_
      residual_integrable := fun k => ?_
      residual_square_integrable := fun k => ?_
      residual_mean := fun k => ?_
      residual_variance := fun k => ?_ }
  · have hk' : k < q.stop ω := hk
    obtain ⟨ω', hres', hst, hpr⟩ := hrep ω
    have he : (truncTrial q).residual k ω = (truncTrial q).residual k ω' := by
      show (if k < q.stop ω then q.residual k ω else 0) =
        (if k < q.stop ω' then q.residual k ω' else 0)
      rw [hst, (hpr k).2]
    have hk'' : k < q.stop ω' := hst ▸ hk'
    have hnear' := (hpr k).1 ▸ hnear
    rw [he, trunc_residual_eq, Set.indicator_of_mem (show ω' ∈ {ω | k < q.stop ω} from hk''),
      hres' k hk'']
    exact (siteSuffix_bound _ (OAI.Anderson.scaleCoupling n₀ u) _ _ ω').trans
      (hbound _ (hcoupled k ω' hk'' hnear'))
  · rw [trunc_residual_eq]
    exact integrable_truncZ hq k id measurable_id |(OAI.Anderson.scaleCoupling n₀ u)| (fun x hx => hx)
  · rw [trunc_sq_eq]
    exact integrable_truncZ hq k (fun x => x ^ 2) (measurable_id.pow_const 2) (|(OAI.Anderson.scaleCoupling n₀ u)| ^ 2)
      (fun x hx => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  · filter_upwards [condExp_trunc_residualZ hq k] with ω hω _ _
    exact hω
  · refine ⟨fun ω => (stageScale u j m) - (OAI.Anderson.scaleCoupling n₀ u) ^ 2 / (3 * 4 ^ x.prefixLength (q.pivot k ω).val), ?_, ?_⟩
    · exact (stronglyMeasurable_const.sub
        ((measurable_of_countable (fun i : ActiveSite x =>
          (OAI.Anderson.scaleCoupling n₀ u) ^ 2 / (3 * 4 ^ x.prefixLength i.val))).comp
          (q.pivot_predictable k)).stronglyMeasurable)
    · filter_upwards [condExp_trunc_residual_sqZ hq k] with ω hω hk hnear
      have hk' : k < q.stop ω := hk
      have hc := hcoupled k ω hk' hnear
      rw [hσ _ hc]
      have hη : (stageScale u j m) - u / 4 ^ j = u / 4 ^ m := by unfold stageScale; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hη]; positivity
      · rw [hη, div_le_iff₀ htpos]
        have h2j : 2 * j ≤ m := by unfold clearingScheduled at hsched; omega
        have hpow : (4 : ℝ) ^ (2 * j) ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) h2j
        have hsq : (u / 4 ^ j) ^ 2 ≤ (stageScale u j m) * (stageScale u j m) := by
          have h0 : 0 ≤ u / 4 ^ j := by positivity
          nlinarith
        have : u / 4 ^ m ≤ 4 * (u / 4 ^ j) ^ 2 := by
          rw [div_pow, ← pow_mul, mul_comm j 2]
          rw [div_le_iff₀ h4m]
          have h4u : 1 ≤ 4 * u := by linarith [hu.1]
          have : 4 * (u ^ 2 / 4 ^ (2 * j)) * 4 ^ m ≥ 4 * (u ^ 2 / 4 ^ m) * 4 ^ m := by
            have : u ^ 2 / 4 ^ m ≤ u ^ 2 / 4 ^ (2 * j) :=
              div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) hpow
            nlinarith
          have h5 : 4 * (u ^ 2 / 4 ^ m) * 4 ^ m = 4 * u ^ 2 := by field_simp
          nlinarith
        nlinarith
      · show (sourcesLaw (S78.Torus d m) M)[fun ω => (truncTrial q).residual k ω ^ 2 | q.history k] ω = _
        rw [hω, Set.indicator_of_mem (show ω ∈ {ω | k < q.stop ω} from hk'), hσ _ hc]
        ring


end Clearing

end AndersonAC.AgentS78.ResidualZ
