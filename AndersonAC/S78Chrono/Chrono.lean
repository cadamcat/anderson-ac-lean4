import AndersonAC.S78Chrono.Defs

/-! Reverse chronological induction for the finite birth-product bound.

Lead request: prove the exact finite deterministic-label product bound from
the filtration conditional-indicator bounds and event adaptedness, using the
conditional set integral and reverse chronological induction, not independence.
All binders and hypotheses are retained. -/

open scoped BigOperators ENNReal Topology MeasureTheory
open MeasureTheory Filter
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

theorem chronological_joint_proof {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : BirthProcess Ω) (c : ℝ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ,
      μ[(B.event n).indicator (fun _ => (1 : ℝ)) | B.history n] ω ≤ birthBound c (B.scale n))
    (S : Finset ℕ) :
    μ (⋂ n ∈ S, B.event n) ≤ ENNReal.ofReal (∏ n ∈ S, birthBound c (B.scale n)) := by
  -- Ambient measurability of each birth event, from adaptedness.
  have hE_meas : ∀ n, MeasurableSet (B.event n) := fun n =>
    measurableSet_of_filtration (B.adapted n)
  -- Nonnegativity of the scalar bounds.
  have hb_nonneg : ∀ n, 0 ≤ birthBound c (B.scale n) := fun n => by
    unfold birthBound
    exact Real.exp_nonneg _
  -- Single events are filtration-measurable at any strictly later index.
  have hE_F : ∀ {n j : ℕ}, n < j → MeasurableSet[B.history j] (B.event n) := by
    intro n j hlt
    have hle : n + 1 ≤ j := by omega
    exact (B.history.mono hle) _ (B.adapted n)
  -- Finite intersections of earlier events are filtration-measurable.
  have hInter_F : ∀ (T : Finset ℕ) (j : ℕ), (∀ n ∈ T, n < j) →
      MeasurableSet[B.history j] (⋂ n ∈ T, B.event n) := by
    intro T j hT
    exact Finset.measurableSet_biInter T (fun n hn => hE_F (hT n hn))
  -- Integrability of each conditional indicator.
  have hInt : ∀ n, Integrable ((B.event n).indicator (fun _ => (1 : ℝ))) μ := by
    intro n
    exact (integrable_const (1 : ℝ)).indicator (hE_meas n)
  -- One-step conditional bound, in ENNReal form.
  have step : ∀ (T : Finset ℕ) (j : ℕ), j ∉ T → (∀ n ∈ T, n < j) →
      μ ((⋂ n ∈ T, B.event n) ∩ B.event j) ≤
        ENNReal.ofReal (birthBound c (B.scale j)) * μ (⋂ n ∈ T, B.event n) := by
    intro T j hjT hlt
    set I : Set Ω := ⋂ n ∈ T, B.event n with hI_def
    set E : Set Ω := B.event j with hE_def
    have hI_F : MeasurableSet[B.history j] I := hInter_F T j hlt
    have hI : MeasurableSet I := measurableSet_of_filtration hI_F
    have hE : MeasurableSet E := hE_meas j
    have hf_int : Integrable (E.indicator (fun _ => (1 : ℝ))) μ := hInt j
    -- Conditional set integral over the earlier intersection.
    have hcond : ∫ x in I, μ[E.indicator (fun _ => (1 : ℝ)) | B.history j] x ∂μ
        = ∫ x in I, E.indicator (fun _ => (1 : ℝ)) x ∂μ :=
      setIntegral_condExp (B.history.le j) hf_int hI_F
    -- Right-hand side equals the real measure of the joint intersection.
    have hRHS : ∫ x in I, E.indicator (fun _ => (1 : ℝ)) x ∂μ
        = (μ (I ∩ E)).toReal := by
      rw [setIntegral_indicator hE]
      have h1 : ∫ _ in I ∩ E, (1 : ℝ) ∂μ = μ.real (I ∩ E) := by simp
      rw [h1, measureReal_def]
    -- Left-hand side is bounded by the deterministic label times the real
    -- measure of the earlier intersection.
    have hLHS_le : ∫ x in I, μ[E.indicator (fun _ => (1 : ℝ)) | B.history j] x ∂μ
        ≤ (μ I).toReal * birthBound c (B.scale j) := by
      have hmono : ∫ x in I, μ[E.indicator (fun _ => (1 : ℝ)) | B.history j] x ∂μ
          ≤ ∫ _ in I, birthBound c (B.scale j) ∂μ := by
        apply setIntegral_mono_ae integrable_condExp.integrableOn
          (integrable_const _).integrableOn (hbound j)
      rw [setIntegral_const] at hmono
      simp only [measureReal_def, smul_eq_mul] at hmono
      linarith [hmono]
    have hreal : (μ (I ∩ E)).toReal ≤ (μ I).toReal * birthBound c (B.scale j) := by
      rw [← hRHS, ← hcond]
      exact hLHS_le
    -- Lift the real inequality to ENNReal.
    have hfin1 : μ (I ∩ E) ≠ ∞ := measure_ne_top μ _
    have hfin2 : μ I ≠ ∞ := measure_ne_top μ _
    have hI_toReal_nonneg : 0 ≤ (μ I).toReal := ENNReal.toReal_nonneg
    calc μ (I ∩ E) = ENNReal.ofReal (μ (I ∩ E)).toReal :=
          (ENNReal.ofReal_toReal hfin1).symm
      _ ≤ ENNReal.ofReal ((μ I).toReal * birthBound c (B.scale j)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (μ I).toReal * ENNReal.ofReal (birthBound c (B.scale j)) :=
          ENNReal.ofReal_mul hI_toReal_nonneg
      _ = μ I * ENNReal.ofReal (birthBound c (B.scale j)) := by
          rw [ENNReal.ofReal_toReal hfin2]
      _ = ENNReal.ofReal (birthBound c (B.scale j)) * μ I := mul_comm _ _
  -- Reverse chronological induction on the cardinality.
  suffices hall : ∀ k : ℕ, ∀ T : Finset ℕ, T.card ≤ k →
      μ (⋂ n ∈ T, B.event n) ≤ ENNReal.ofReal (∏ n ∈ T, birthBound c (B.scale n)) by
    exact hall S.card S le_rfl
  intro k
  induction k with
  | zero =>
    intro T hT
    have hTe : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    subst hTe
    simp only [Finset.prod_empty]
    rw [ENNReal.ofReal_one]
    calc μ (⋂ n ∈ ∅, B.event n) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  | succ k ih =>
    intro T hT
    by_cases hTe : T = ∅
    · subst hTe
      simp only [Finset.prod_empty]
      rw [ENNReal.ofReal_one]
      calc μ (⋂ n ∈ ∅, B.event n) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · -- Peel off the chronological maximum.
      have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTe
      have hj_mem : T.max' hne ∈ T := Finset.max'_mem T hne
      have hj_not : T.max' hne ∉ T.erase (T.max' hne) :=
        Finset.notMem_erase _ _
      have hT_eq : T = insert (T.max' hne) (T.erase (T.max' hne)) :=
        (Finset.insert_erase hj_mem).symm
      have hT'_card : (T.erase (T.max' hne)).card ≤ k := by
        have hcard : (T.erase (T.max' hne)).card + 1 = T.card :=
          Finset.card_erase_add_one hj_mem
        omega
      have hlt : ∀ n ∈ T.erase (T.max' hne), n < T.max' hne := by
        intro n hn
        have hnT : n ∈ T := Finset.mem_of_mem_erase hn
        have hle : n ≤ T.max' hne := Finset.le_max' T n hnT
        have hne' : n ≠ T.max' hne := Finset.ne_of_mem_erase hn
        omega
      have hInter_eq : (⋂ n ∈ T, B.event n)
          = (⋂ n ∈ T.erase (T.max' hne), B.event n) ∩ B.event (T.max' hne) := by
        conv_lhs => rw [hT_eq]
        rw [Finset.set_biInter_insert, Set.inter_comm]
      have hprod_eq : (∏ n ∈ T, birthBound c (B.scale n))
          = birthBound c (B.scale (T.max' hne)) *
            ∏ n ∈ T.erase (T.max' hne), birthBound c (B.scale n) := by
        conv_lhs => rw [hT_eq]
        rw [Finset.prod_insert hj_not]
      have hstep := step _ _ hj_not hlt
      have hih := ih _ hT'_card
      calc μ (⋂ n ∈ T, B.event n)
          = μ ((⋂ n ∈ T.erase (T.max' hne), B.event n) ∩ B.event (T.max' hne)) := by
            rw [hInter_eq]
        _ ≤ ENNReal.ofReal (birthBound c (B.scale (T.max' hne))) *
            μ (⋂ n ∈ T.erase (T.max' hne), B.event n) := hstep
        _ ≤ ENNReal.ofReal (birthBound c (B.scale (T.max' hne))) *
            ENNReal.ofReal (∏ n ∈ T.erase (T.max' hne), birthBound c (B.scale n)) := by
            gcongr
        _ = ENNReal.ofReal (birthBound c (B.scale (T.max' hne)) *
            ∏ n ∈ T.erase (T.max' hne), birthBound c (B.scale n)) :=
            (ENNReal.ofReal_mul (hb_nonneg _)).symm
        _ = ENNReal.ofReal (∏ n ∈ T, birthBound c (B.scale n)) := by
            rw [hprod_eq]

end AndersonAC.SolS78
