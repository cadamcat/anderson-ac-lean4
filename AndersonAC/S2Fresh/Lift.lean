import AndersonAC.S2.Definitions
import AndersonAC.S2.Retained
import AndersonAC.S2.RetainedMeasurable
import AndersonAC.S2.SignFreshness
import AndersonAC.S2.StoppedFreshnessStatement
import Mathlib

/-! Stopped freshness lift: fixed-time `FreshAt` implies stopped identities.

Route: slice `D` by `{τ=q}`, apply `FreshAt`, sum the countable partition.
WithTop case discards the null `{τ=⊤}` slice.
-/

noncomputable section
open MeasureTheory ProbabilityTheory AndersonAC.S2 AndersonAC.SolS2
open scoped ENNReal

universe u

namespace AndersonAC.SolS2

variable (ι : Type u) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

-- Ambient measurability of sign cylinders.
theorem signCylinder_measurable (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool) :
    MeasurableSet (signCylinder (M := M) ι s a) := by
  classical
  simp only [signCylinder, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro _hx
  have hf : Measurable (fun ω : RandomSources ι M => ω.1 x) :=
    (measurable_pi_apply x).comp measurable_fst
  exact hf (measurableSet_singleton (a x))

-- Slice {τ = q} is retained-q measurable from IsRetainedStoppingTime + mono.
theorem slice_eq_measurable {Q : ℕ → RandomSources ι M → Query ι}
    (_hQ : ObeysQueryRules ι Q) (τ : RandomSources ι M → ℕ)
    (hτ : IsRetainedStoppingTime ι Q τ) (q : ℕ) :
    MeasurableSet[retained ι Q q] {ω | τ ω = q} := by
  have hle : MeasurableSet[retained ι Q q] {ω | τ ω ≤ q} := hτ q
  cases q with
  | zero =>
    simpa only [Nat.le_zero] using hle
  | succ q =>
    have hprev : MeasurableSet[retained ι Q q] {ω | τ ω ≤ q} := hτ q
    have hprev' : MeasurableSet[retained ι Q (q + 1)] {ω | τ ω ≤ q} :=
      (retained_mono ι Q (Nat.le_succ q)) _ hprev
    have hdiff : MeasurableSet[retained ι Q (q + 1)]
        ({ω | τ ω ≤ q + 1} \ {ω | τ ω ≤ q}) := hle.diff hprev'
    have heq : ({ω | τ ω ≤ q + 1} \ {ω | τ ω ≤ q}) = {ω | τ ω = q + 1} := by
      ext ω
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
      omega
    rwa [heq] at hdiff

-- Ambient version.
theorem slice_eq_measurable_ambient {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (τ : RandomSources ι M → ℕ)
    (hτ : IsRetainedStoppingTime ι Q τ) (q : ℕ) :
    MeasurableSet {ω : RandomSources ι M | τ ω = q} :=
  (retained_le ι hQ q) _ (slice_eq_measurable ι hQ τ hτ q)

-- D ∩ {τ=q} is retained-q measurable when D is stopped-measurable.
theorem stopped_slice_measurable {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (τ : RandomSources ι M → ℕ)
    (hτ : IsRetainedStoppingTime ι Q τ)
    (D : Set (RandomSources ι M))
    (hD : MeasurableSet[stoppedRetained ι Q τ] D) (q : ℕ) :
    MeasurableSet[retained ι Q q] (D ∩ {ω | τ ω = q}) := by
  classical
  have hDq : MeasurableSet[((retained ι Q q).comap
      (fun ω : {ω // τ ω = q} => (ω.val : RandomSources ι M))).map
      (fun ω : {ω // τ ω = q} => (ω.val : RandomSources ι M))] D :=
    (MeasurableSpace.measurableSet_iInf.mp hD) q
  rw [MeasurableSpace.map_def] at hDq
  rw [MeasurableSpace.measurableSet_comap] at hDq
  obtain ⟨T, hT, hpre⟩ := hDq
  have hS := slice_eq_measurable ι hQ τ hτ q
  have hinter : MeasurableSet[retained ι Q q] (T ∩ {ω | τ ω = q}) := hT.inter hS
  have heq : D ∩ {ω | τ ω = q} = T ∩ {ω | τ ω = q} := by
    ext ω
    constructor
    · rintro ⟨hDω, hq⟩
      have hmem : (⟨ω, hq⟩ : {ω // τ ω = q}) ∈
          (fun ω : {ω // τ ω = q} => (ω.val : RandomSources ι M)) ⁻¹' D := hDω
      rw [← hpre] at hmem
      exact ⟨hmem, hq⟩
    · rintro ⟨hTω, hq⟩
      have hmem : (⟨ω, hq⟩ : {ω // τ ω = q}) ∈
          (fun ω : {ω // τ ω = q} => (ω.val : RandomSources ι M)) ⁻¹' T := hTω
      rw [hpre] at hmem
      exact ⟨hmem, hq⟩
  exact heq ▸ hinter

-- Ambient measurability of the adaptive query policy.
theorem query_measurable_ambient {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (j : ℕ) : Measurable (Q j) :=
  ((hQ.1 j).mono (retained_le ι hQ j) le_rfl)

-- Evaluation at an order entry is ambient-measurable.
theorem orderEval_measurable (o : ℕ) (j : Fin (M o)) :
    Measurable (fun ω : RandomSources ι M => ω.2 o j) := by
  classical
  have h1 : Measurable (fun ω : RandomSources ι M => ω.2 o) :=
    (measurable_pi_apply o).comp measurable_snd
  have h2 : Measurable (fun p : Order (M o) => p j) := measurable_from_top
  exact h2.comp h1

-- The prefix-match set for one order coordinate is ambient-measurable.
theorem prefixMatch_measurable {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q o : ℕ) (b : (o : ℕ) → Order (M o)) :
    MeasurableSet {ω : RandomSources ι M |
      ∀ j : Fin (M o), j.val < orderCount ι Q q ω o → b o j = ω.2 o j} := by
  classical
  have hcount : Measurable (fun ω : RandomSources ι M => orderCount ι Q q ω o) :=
    orderCount_measurable ι Q q o (fun j _ => query_measurable_ambient ι hQ j)
  have hfin : ∀ j : Fin (M o), MeasurableSet
      ({ω : RandomSources ι M | j.val < orderCount ι Q q ω o}ᶜ ∪
        {ω : RandomSources ι M | b o j = ω.2 o j}) := by
    intro j
    apply MeasurableSet.union
    · exact (hcount (MeasurableSet.of_discrete)).compl
    · have heq2 : {ω : RandomSources ι M | b o j = ω.2 o j} =
          (fun ω : RandomSources ι M => ω.2 o j) ⁻¹' {b o j} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, eq_comm]
      rw [heq2]
      exact (orderEval_measurable (ι := ι) (M := M) o j) (measurableSet_singleton _)
  have heq : {ω : RandomSources ι M |
        ∀ j : Fin (M o), j.val < orderCount ι Q q ω o → b o j = ω.2 o j} =
      ⋂ j : Fin (M o), ({ω : RandomSources ι M | j.val < orderCount ι Q q ω o}ᶜ ∪
        {ω : RandomSources ι M | b o j = ω.2 o j}) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · intro h j
      by_cases hj : j.val < orderCount ι Q q ω o
      · exact Or.inr (h j hj)
      · exact Or.inl hj
    · intro h j hj
      rcases h j with h | h
      · exact absurd hj h
      · exact h
  rw [heq]
  exact MeasurableSet.iInter fun j => hfin j

-- One order factor of the completion weight is measurable.
theorem weightFactor_measurable {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q o : ℕ) (b : (o : ℕ) → Order (M o)) :
    Measurable (fun ω : RandomSources ι M =>
      (if (∀ j : Fin (M o), j.val < orderCount ι Q q ω o → b o j = ω.2 o j)
        then ((M o - orderCount ι Q q ω o).factorial : ℝ)⁻¹ else 0)) := by
  classical
  apply Measurable.ite (prefixMatch_measurable ι hQ q o b)
  · exact (measurable_of_countable
      (f := fun n : ℕ => ((M o - n).factorial : ℝ)⁻¹)).comp
      (orderCount_measurable ι Q q o (fun j _ => query_measurable_ambient ι hQ j))
  · exact measurable_const

-- The full completion weight is ambient-measurable.
theorem completionWeight_measurable {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    Measurable (completionWeight ι Q q O b) := by
  classical
  unfold completionWeight
  exact Finset.measurable_prod O (fun o _ => weightFactor_measurable ι hQ q o b)

-- Each factor is nonnegative, hence the weight is nonnegative.
theorem completionWeight_nonneg (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) (ω : RandomSources ι M) :
    0 ≤ completionWeight ι Q q O b ω := by
  classical
  unfold completionWeight
  apply Finset.prod_nonneg
  intro o _
  split_ifs with _
  · positivity
  · exact le_rfl

-- Each factor is at most 1, hence the weight is at most 1.
theorem weightFactor_nonneg {Q : ℕ → RandomSources ι M → Query ι}
    (q o : ℕ) (b : (o : ℕ) → Order (M o)) (ω : RandomSources ι M) :
    0 ≤ (if (∀ j : Fin (M o), j.val < orderCount ι Q q ω o → b o j = ω.2 o j)
      then ((M o - orderCount ι Q q ω o).factorial : ℝ)⁻¹ else 0) := by
  split_ifs with _
  · positivity
  · exact le_rfl

theorem weightFactor_le_one {Q : ℕ → RandomSources ι M → Query ι}
    (q o : ℕ) (b : (o : ℕ) → Order (M o)) (ω : RandomSources ι M) :
    (if (∀ j : Fin (M o), j.val < orderCount ι Q q ω o → b o j = ω.2 o j)
      then ((M o - orderCount ι Q q ω o).factorial : ℝ)⁻¹ else 0) ≤ 1 := by
  split_ifs with _
  · have h1 : (1 : ℝ) ≤ ((M o - orderCount ι Q q ω o).factorial : ℝ) := by
      have hnat : 1 ≤ (M o - orderCount ι Q q ω o).factorial :=
        Nat.succ_le_of_lt (Nat.factorial_pos _)
      exact_mod_cast hnat
    exact inv_le_one_of_one_le₀ h1
  · exact zero_le_one

theorem completionWeight_le_one (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) (ω : RandomSources ι M) :
    completionWeight ι Q q O b ω ≤ 1 := by
  classical
  unfold completionWeight
  induction O using Finset.induction with
  | empty => simp
  | insert a s has IH =>
    rw [Finset.prod_insert has]
    have hprod0 : 0 ≤ ∏ o ∈ s,
        (if (∀ j : Fin (M o), j.val < orderCount ι Q q ω o → b o j = ω.2 o j)
          then ((M o - orderCount ι Q q ω o).factorial : ℝ)⁻¹ else 0) := by
      apply Finset.prod_nonneg
      intro o _
      exact weightFactor_nonneg ι q o b ω
    exact (mul_le_of_le_one_left hprod0 (weightFactor_le_one ι q a b ω)).trans IH

theorem completionWeight_norm_le_one (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) (ω : RandomSources ι M) :
    ‖completionWeight ι Q q O b ω‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (completionWeight_nonneg ι Q q O b ω)]
  exact completionWeight_le_one ι Q q O b ω

-- Fixed-time lift to a finite-valued retained stopping time.
theorem natTime_aux {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (hFresh : ∀ q, FreshAt ι Q q)
    (τ : RandomSources ι M → ℕ) (hτ : IsRetainedStoppingTime ι Q τ)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[stoppedRetained ι Q τ] D)
    (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        ∫ ω in {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s},
          completionWeight ι Q (τ ω) O b ω ∂sourcesLaw ι M := by
  classical
  let μ := sourcesLaw ι M
  have hDq : ∀ q, MeasurableSet[retained ι Q q] (D ∩ {ω | τ ω = q}) :=
    fun q => stopped_slice_measurable ι hQ τ hτ D hD q
  -- Per-slice FreshAt identities.
  have hslice : ∀ q,
      (μ ((D ∩ {ω | τ ω = q}) ∩ signsUnqueried ι Q q s ∩
        signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        ∫ ω in (D ∩ {ω | τ ω = q}) ∩ signsUnqueried ι Q q s,
          completionWeight ι Q q O b ω ∂μ := by
    intro q
    exact hFresh q _ (hDq q) s a O b
  -- Stopped weight function.
  let wStar : RandomSources ι M → ℝ :=
    fun ω => completionWeight ι Q (τ ω) O b ω
  have hwStar_meas : Measurable wStar := by
    intro t ht
    have heq : wStar ⁻¹' t =
        ⋃ q, ({ω : RandomSources ι M | τ ω = q} ∩
          completionWeight ι Q q O b ⁻¹' t) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      constructor
      · intro h
        refine ⟨τ ω, rfl, ?_⟩
        have : wStar ω = completionWeight ι Q (τ ω) O b ω := rfl
        rwa [this] at h
      · rintro ⟨q, hq, hmem⟩
        have : wStar ω = completionWeight ι Q q O b ω := by
          simp only [wStar, hq]
        rw [this]
        exact hmem
    rw [heq]
    apply MeasurableSet.iUnion
    intro q
    exact (slice_eq_measurable_ambient ι hQ τ hτ q).inter
      ((completionWeight_measurable ι hQ q O b) ht)
  have hwStar_bound : ∀ ω, ‖wStar ω‖ ≤ 1 := fun ω =>
    completionWeight_norm_le_one ι Q (τ ω) O b ω
  have hwStar_int : Integrable wStar μ :=
    Integrable.of_bound hwStar_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => hwStar_bound ω)
  -- Slice sets and their ambient measurability.
  let Fq : ℕ → Set (RandomSources ι M) :=
    fun q => (D ∩ {ω | τ ω = q}) ∩ signsUnqueried ι Q q s
  let Eq : ℕ → Set (RandomSources ι M) :=
    fun q => Fq q ∩ signCylinder ι s a ∩ orderCylinder ι O b
  have hFq_meas : ∀ q, MeasurableSet (Fq q) := by
    intro q
    exact (((retained_le ι hQ q) _ (hDq q)).inter
      (signsUnqueried_measurable ι hQ q s))
  have hEq_meas : ∀ q, MeasurableSet (Eq q) := by
    intro q
    exact ((hFq_meas q).inter (signCylinder_measurable ι s a)).inter
      (orderCylinder_measurable ι O b)
  -- Global sets as countable unions.
  have hR_eq : {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s} = ⋃ q, Fq q := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Fq, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro ⟨hDω, hfresh⟩
      exact ⟨τ ω, ⟨hDω, rfl⟩, hfresh⟩
    · rintro ⟨q, ⟨hDω, hq⟩, hfresh⟩
      exact ⟨hDω, hq.symm ▸ hfresh⟩
  have hL_eq : ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b) = ⋃ q, Eq q := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Eq, Fq,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨hDω, hfresh⟩, hcyl⟩, hord⟩
      exact ⟨τ ω, ⟨⟨⟨hDω, rfl⟩, hfresh⟩, hcyl⟩, hord⟩
    · rintro ⟨q, ⟨⟨⟨⟨hDω, hq⟩, hfresh⟩, hcyl⟩, hord⟩⟩
      exact ⟨⟨⟨hDω, hq.symm ▸ hfresh⟩, hcyl⟩, hord⟩
  have hdisjF : Pairwise (Function.onFun Disjoint Fq) := by
    intro i j hij
    simp only [Function.onFun]
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨_, hi⟩, -⟩ ⟨⟨_, hj⟩, -⟩
    exact hij (hi.symm.trans hj)
  have hdisjE : Pairwise (Function.onFun Disjoint Eq) := by
    intro i j hij
    simp only [Function.onFun]
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨⟨⟨_, hi⟩, -⟩, -⟩, -⟩ ⟨⟨⟨⟨_, hj⟩, -⟩, -⟩, -⟩
    exact hij (hi.symm.trans hj)
  -- Integrability on the countable unions.
  have hIntF : IntegrableOn wStar (⋃ q, Fq q) μ := hwStar_int.integrableOn
  have hIntE : IntegrableOn (fun _ : RandomSources ι M => (1 : ℝ)) (⋃ q, Eq q) μ :=
    integrableOn_const (measure_ne_top μ _)
  -- HasSum over slices.
  have hHasF : HasSum (fun q => ∫ ω in Fq q, wStar ω ∂μ)
      (∫ ω in ⋃ q, Fq q, wStar ω ∂μ) :=
    MeasureTheory.hasSum_integral_iUnion hFq_meas hdisjF hIntF
  have hHasE : HasSum (fun _q : ℕ => ∫ _ω in Eq _q, (1 : ℝ) ∂μ)
      (∫ _ω in ⋃ q, Eq q, (1 : ℝ) ∂μ) :=
    MeasureTheory.hasSum_integral_iUnion hEq_meas hdisjE hIntE
  -- wStar agrees with the fixed-time weight on each slice.
  have hwEq : ∀ q, Set.EqOn wStar (completionWeight ι Q q O b) (Fq q) := by
    intro q ω hω
    obtain ⟨⟨_, hq⟩, -⟩ := hω
    have hqq : τ ω = q := hq
    simp only [wStar, hqq]
  have hIntFq : ∀ q, ∫ ω in Fq q, wStar ω ∂μ =
      ∫ ω in Fq q, completionWeight ι Q q O b ω ∂μ := by
    intro q
    exact MeasureTheory.setIntegral_congr_fun (hFq_meas q) (hwEq q)
  -- Per-slice identities as integrals of 1.
  have hFq_eq : ∀ q, Fq q = (D ∩ {ω | τ ω = q}) ∩ signsUnqueried ι Q q s :=
    fun q => rfl
  have hEq_eq : ∀ q, Eq q = (D ∩ {ω | τ ω = q}) ∩ signsUnqueried ι Q q s ∩
      signCylinder ι s a ∩ orderCylinder ι O b := fun q => rfl
  have hslice1 : ∀ q, ∫ _ω in Eq q, (1 : ℝ) ∂μ =
      (2 : ℝ) ^ (-(s.card : ℤ)) * ∫ ω in Fq q, wStar ω ∂μ := by
    intro q
    have hq := hslice q
    rw [hIntFq q, hEq_eq q, hFq_eq q]
    have h1 : (∫ _ω in (D ∩ {ω | τ ω = q}) ∩ signsUnqueried ι Q q s ∩
        signCylinder ι s a ∩ orderCylinder ι O b, (1 : ℝ) ∂μ) =
        (μ ((D ∩ {ω | τ ω = q}) ∩ signsUnqueried ι Q q s ∩
          signCylinder ι s a ∩ orderCylinder ι O b)).toReal :=
      MeasureTheory.setIntegral_one_eq_measureReal
    rw [h1]
    exact hq
  -- Combine.
  have hHasE' : HasSum (fun q => ∫ _ω in Eq q, (1 : ℝ) ∂μ)
      ((2 : ℝ) ^ (-(s.card : ℤ)) * ∫ ω in ⋃ q, Fq q, wStar ω ∂μ) := by
    have hmul := hHasF.mul_left ((2 : ℝ) ^ (-(s.card : ℤ)))
    exact hmul.congr_fun (fun q => hslice1 q)
  have hEqUnion : (∫ _ω in ⋃ q, Eq q, (1 : ℝ) ∂μ) =
      (2 : ℝ) ^ (-(s.card : ℤ)) * ∫ ω in ⋃ q, Fq q, wStar ω ∂μ :=
    hHasE.unique hHasE'
  -- Transfer back to stopped sets.
  have hLrw : (μ ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      ∫ _ω in ⋃ q, Eq q, (1 : ℝ) ∂μ := by
    rw [← hL_eq, MeasureTheory.setIntegral_one_eq_measureReal]
    rfl
  have hRrw : (∫ ω in {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s},
        wStar ω ∂μ) = ∫ ω in ⋃ q, Fq q, wStar ω ∂μ := by
    rw [hR_eq]
  rw [hLrw, hRrw]
  exact hEqUnion

-- WithTop lift: slice by {τ = ↑q}, discard the null {τ = ⊤} slice.
theorem aeTime_aux {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (hFresh : ∀ q, FreshAt ι Q q)
    (F : Filtration ℕ (inferInstance : MeasurableSpace (RandomSources ι M)))
    (hF : ∀ q, F q = retained ι Q q)
    (τ : RandomSources ι M → WithTop ℕ) (hτ : IsStoppingTime F τ)
    (hfinite : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[hτ.measurableSpace] D)
    (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        ∫ ω in {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s},
          completionWeight ι Q ((τ ω).untopD 0) O b ω ∂sourcesLaw ι M := by
  classical
  let μ := sourcesLaw ι M
  -- Finite slices are retained-measurable.
  have hSq : ∀ q : ℕ, MeasurableSet[retained ι Q q]
      {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)} := by
    intro q
    rw [← hF q]
    exact hτ.measurableSet_eq q
  have hSq_amb : ∀ q : ℕ,
      MeasurableSet {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)} := by
    intro q
    exact (retained_le ι hQ q) _ (hSq q)
  have hDq : ∀ q : ℕ, MeasurableSet[retained ι Q q]
      (D ∩ {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) := by
    intro q
    have hSq_stop : MeasurableSet[hτ.measurableSpace]
        {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)} := hτ.measurableSet_eq' q
    have hcap : MeasurableSet[hτ.measurableSpace]
        (D ∩ {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) :=
      hD.inter hSq_stop
    have hiff := hτ.measurableSet_inter_eq_iff D q
    rw [← hF q]
    exact hiff.mp hcap
  have hslice : ∀ q : ℕ,
      (μ ((D ∩ {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) ∩
        signsUnqueried ι Q q s ∩
        signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        ∫ ω in (D ∩ {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) ∩
          signsUnqueried ι Q q s,
          completionWeight ι Q q O b ω ∂μ := by
    intro q
    exact hFresh q _ (hDq q) s a O b
  -- Stopped weight with untopD.
  let wStar : RandomSources ι M → ℝ :=
    fun ω => completionWeight ι Q ((τ ω).untopD 0) O b ω
  have hTop_amb : MeasurableSet {ω : RandomSources ι M | τ ω = ⊤} := by
    have hunion : MeasurableSet (⋃ q : ℕ,
        {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) :=
      MeasurableSet.iUnion fun q => hSq_amb q
    have heq : {ω : RandomSources ι M | τ ω = ⊤} =
        (⋃ q : ℕ, {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro htop
        rintro ⟨q, hq⟩
        rw [htop] at hq
        exact WithTop.coe_ne_top hq.symm
      · intro hmem
        by_contra hne
        have hne' : τ ω ≠ ⊤ := hne
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne'
        exact hmem ⟨q, hq⟩
    rw [heq]
    exact hunion.compl
  have hwStar_meas : Measurable wStar := by
    intro t ht
    have heq : wStar ⁻¹' t =
        (⋃ q : ℕ, ({ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)} ∩
          completionWeight ι Q q O b ⁻¹' t)) ∪
        ({ω : RandomSources ι M | τ ω = ⊤} ∩
          completionWeight ι Q 0 O b ⁻¹' t) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        by_cases htop : τ ω = ⊤
        · refine Or.inr ⟨htop, ?_⟩
          have htop0 : (τ ω).untopD 0 = 0 := htop.symm ▸ rfl
          have hws : wStar ω = completionWeight ι Q 0 O b ω := by
            show completionWeight ι Q ((τ ω).untopD 0) O b ω = _
            rw [htop0]
          rwa [hws] at h
        · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp htop
          refine Or.inl ⟨q, hq, ?_⟩
          have htop0 : (τ ω).untopD 0 = q := hq.symm ▸ rfl
          have hws : wStar ω = completionWeight ι Q q O b ω := by
            show completionWeight ι Q ((τ ω).untopD 0) O b ω = _
            rw [htop0]
          rwa [hws] at h
      · rintro (⟨q, hq, hmem⟩ | ⟨htop, hmem⟩)
        · have htop0 : (τ ω).untopD 0 = q := hq.symm ▸ rfl
          have hws : wStar ω = completionWeight ι Q q O b ω := by
            show completionWeight ι Q ((τ ω).untopD 0) O b ω = _
            rw [htop0]
          rw [hws]
          exact hmem
        · have htop0 : (τ ω).untopD 0 = 0 := htop.symm ▸ rfl
          have hws : wStar ω = completionWeight ι Q 0 O b ω := by
            show completionWeight ι Q ((τ ω).untopD 0) O b ω = _
            rw [htop0]
          rw [hws]
          exact hmem
    rw [heq]
    apply MeasurableSet.union
    · exact MeasurableSet.iUnion fun q =>
        (hSq_amb q).inter ((completionWeight_measurable ι hQ q O b) ht)
    · exact hTop_amb.inter ((completionWeight_measurable ι hQ 0 O b) ht)
  have hwStar_bound : ∀ ω, ‖wStar ω‖ ≤ 1 := fun ω =>
    completionWeight_norm_le_one ι Q ((τ ω).untopD 0) O b ω
  have hwStar_int : Integrable wStar μ :=
    Integrable.of_bound hwStar_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => hwStar_bound ω)
  -- Slice sets.
  let Fq : ℕ → Set (RandomSources ι M) := fun q =>
    (D ∩ {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) ∩
      signsUnqueried ι Q q s
  let Eq : ℕ → Set (RandomSources ι M) := fun q =>
    Fq q ∩ signCylinder ι s a ∩ orderCylinder ι O b
  have hFq_meas : ∀ q : ℕ, MeasurableSet (Fq q) := by
    intro q
    exact (((retained_le ι hQ q) _ (hDq q)).inter
      (signsUnqueried_measurable ι hQ q s))
  have hEq_meas : ∀ q : ℕ, MeasurableSet (Eq q) := by
    intro q
    exact ((hFq_meas q).inter (signCylinder_measurable ι s a)).inter
      (orderCylinder_measurable ι O b)
  have hdisjF : Pairwise (Function.onFun Disjoint Fq) := by
    intro i j hij
    simp only [Function.onFun]
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨_, hi⟩, -⟩ ⟨⟨_, hj⟩, -⟩
    have : (↑i : WithTop ℕ) = (↑j : WithTop ℕ) := hi.symm.trans hj
    exact hij (WithTop.coe_eq_coe.mp this)
  have hdisjE : Pairwise (Function.onFun Disjoint Eq) := by
    intro i j hij
    simp only [Function.onFun]
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨⟨⟨_, hi⟩, -⟩, -⟩, -⟩ ⟨⟨⟨⟨_, hj⟩, -⟩, -⟩, -⟩
    have : (↑i : WithTop ℕ) = (↑j : WithTop ℕ) := hi.symm.trans hj
    exact hij (WithTop.coe_eq_coe.mp this)
  -- AE identifications, discarding the null infinite slice.
  have hR_ae : ({ω : RandomSources ι M |
      ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} : Set _) =ᵐ[μ]
      (⋃ q, Fq q) := by
    filter_upwards [hfinite] with ω hfin
    obtain ⟨q0, hq0⟩ := Option.ne_none_iff_exists'.mp hfin
    have htop0 : (τ ω).untopD 0 = q0 := hq0.symm ▸ rfl
    apply propext
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Fq, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro ⟨hDω, hfresh⟩
      rw [htop0] at hfresh
      exact ⟨q0, ⟨hDω, hq0⟩, hfresh⟩
    · rintro ⟨q, ⟨hDω, hq⟩, hfresh⟩
      have htopq : (τ ω).untopD 0 = q := hq.symm ▸ rfl
      rw [htopq]
      exact ⟨hDω, hfresh⟩
  have hL_ae : (({ω : RandomSources ι M |
      ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b : Set _)) =ᵐ[μ]
      (⋃ q, Eq q) := by
    filter_upwards [hfinite] with ω hfin
    obtain ⟨q0, hq0⟩ := Option.ne_none_iff_exists'.mp hfin
    have htop0 : (τ ω).untopD 0 = q0 := hq0.symm ▸ rfl
    apply propext
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Eq, Fq,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨hDω, hfresh⟩, hcyl⟩, hord⟩
      rw [htop0] at hfresh
      exact ⟨q0, ⟨⟨⟨hDω, hq0⟩, hfresh⟩, hcyl⟩, hord⟩
    · rintro ⟨q, ⟨⟨⟨⟨hDω, hq⟩, hfresh⟩, hcyl⟩, hord⟩⟩
      have htopq : (τ ω).untopD 0 = q := hq.symm ▸ rfl
      have hfresh' : ω ∈ signsUnqueried ι Q q s := hfresh
      have hgoal : ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s :=
        htopq.symm ▸ hfresh'
      exact ⟨⟨⟨hDω, hgoal⟩, hcyl⟩, hord⟩
  -- HasSum over finite slices.
  have hIntF : IntegrableOn wStar (⋃ q, Fq q) μ := hwStar_int.integrableOn
  have hIntE : IntegrableOn (fun _ : RandomSources ι M => (1 : ℝ)) (⋃ q, Eq q) μ :=
    integrableOn_const (measure_ne_top μ _)
  have hHasF : HasSum (fun q : ℕ => ∫ ω in Fq q, wStar ω ∂μ)
      (∫ ω in ⋃ q, Fq q, wStar ω ∂μ) :=
    MeasureTheory.hasSum_integral_iUnion hFq_meas hdisjF hIntF
  have hHasE : HasSum (fun q : ℕ => ∫ _ω in Eq q, (1 : ℝ) ∂μ)
      (∫ _ω in ⋃ q, Eq q, (1 : ℝ) ∂μ) :=
    MeasureTheory.hasSum_integral_iUnion hEq_meas hdisjE hIntE
  have hwEq : ∀ q : ℕ, Set.EqOn wStar (completionWeight ι Q q O b) (Fq q) := by
    intro q ω hω
    obtain ⟨⟨_, hq⟩, -⟩ := hω
    have htop : (τ ω).untopD 0 = q := hq.symm ▸ rfl
    show completionWeight ι Q ((τ ω).untopD 0) O b ω = _
    rw [htop]
  have hIntFq : ∀ q : ℕ, ∫ ω in Fq q, wStar ω ∂μ =
      ∫ ω in Fq q, completionWeight ι Q q O b ω ∂μ := by
    intro q
    exact MeasureTheory.setIntegral_congr_fun (hFq_meas q) (hwEq q)
  have hFq_eq : ∀ q : ℕ, Fq q = (D ∩
      {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) ∩
      signsUnqueried ι Q q s := fun q => rfl
  have hEq_eq : ∀ q : ℕ, Eq q = (D ∩
      {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) ∩
      signsUnqueried ι Q q s ∩
      signCylinder ι s a ∩ orderCylinder ι O b := fun q => rfl
  have hslice1 : ∀ q : ℕ, ∫ _ω in Eq q, (1 : ℝ) ∂μ =
      (2 : ℝ) ^ (-(s.card : ℤ)) * ∫ ω in Fq q, wStar ω ∂μ := by
    intro q
    have hq := hslice q
    rw [hIntFq q, hEq_eq q, hFq_eq q]
    have h1 : (∫ _ω in (D ∩
        {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) ∩
        signsUnqueried ι Q q s ∩
        signCylinder ι s a ∩ orderCylinder ι O b, (1 : ℝ) ∂μ) =
        (μ ((D ∩ {ω : RandomSources ι M | τ ω = (↑q : WithTop ℕ)}) ∩
          signsUnqueried ι Q q s ∩
          signCylinder ι s a ∩ orderCylinder ι O b)).toReal :=
      MeasureTheory.setIntegral_one_eq_measureReal
    rw [h1]
    exact hq
  have hHasE' : HasSum (fun q : ℕ => ∫ _ω in Eq q, (1 : ℝ) ∂μ)
      ((2 : ℝ) ^ (-(s.card : ℤ)) * ∫ ω in ⋃ q, Fq q, wStar ω ∂μ) := by
    have hmul := hHasF.mul_left ((2 : ℝ) ^ (-(s.card : ℤ)))
    exact hmul.congr_fun (fun q => hslice1 q)
  have hEqUnion : (∫ _ω in ⋃ q, Eq q, (1 : ℝ) ∂μ) =
      (2 : ℝ) ^ (-(s.card : ℤ)) * ∫ ω in ⋃ q, Fq q, wStar ω ∂μ :=
    hHasE.unique hHasE'
  -- Transfer back, discarding the null slice.
  have hLrw : (μ ({ω : RandomSources ι M |
      ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      ∫ _ω in ⋃ q, Eq q, (1 : ℝ) ∂μ := by
    have hmeas : (μ ({ω : RandomSources ι M |
        ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} ∩
        signCylinder ι s a ∩ orderCylinder ι O b)) =
        μ (⋃ q, Eq q) :=
      MeasureTheory.measure_congr hL_ae
    rw [hmeas, MeasureTheory.setIntegral_one_eq_measureReal]
    rfl
  have hRrw : (∫ ω in {ω : RandomSources ι M |
      ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s},
        wStar ω ∂μ) = ∫ ω in ⋃ q, Fq q, wStar ω ∂μ :=
    MeasureTheory.setIntegral_congr_set hR_ae
  rw [hLrw, hRrw]
  exact hEqUnion

-- The frozen helper, assembled from the two lifts.
theorem StoppedFreshnessLift_proof : StoppedFreshnessLift where
  natTime := fun _ _ _ _ _ hQ hFresh τ hτ D hD s a O b =>
    natTime_aux _ hQ hFresh τ hτ D hD s a O b
  aeTime := fun _ _ _ _ _ hQ hFresh F hF τ hτ hfinite D hD s a O b =>
    aeTime_aux _ hQ hFresh F hF τ hτ hfinite D hD s a O b

end AndersonAC.SolS2
