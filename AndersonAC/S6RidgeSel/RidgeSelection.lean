import AndersonAC.S6.RidgeStatements
import AndersonAC.S6.RidgeThresholdStatement
import AndersonAC.S6RidgeThresh.Check
import AndersonAC.S6.Projection
import AndersonAC.S6.Ridge
import AndersonAC.AgentS6.LeverageFacts

noncomputable section

set_option maxHeartbeats 400000

open scoped Matrix ComplexConjugate
open Filter MeasureTheory

namespace AndersonAC.SolS6

universe u v

variable {B : Type u} {R : Type v} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

private theorem measurable_finset_sup {α ι : Type*} [MeasurableSpace α]
    [DecidableEq ι] (s : Finset ι) (f : ι → α → NNReal)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => s.sup fun i => f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using (measurable_const : Measurable (fun _ : α => (⊥ : NNReal)))
  | @insert a t ha ih =>
    simp only [Finset.sup_insert]
    exact (hf a).sup ih

private theorem measurable_ridgeProjection (τ : ℝ) :
    Measurable (fun C : Matrix R B ℂ => AndersonAC.S6.ridgeProjection C τ) := by
  have hC : Measurable (fun C : Matrix R B ℂ => C) := measurable_id
  have hCt : Measurable (fun C : Matrix R B ℂ => Cᴴ) :=
    continuous_id.matrix_conjTranspose.measurable
  have hGc : Continuous (fun C : Matrix R B ℂ =>
      Cᴴ * C + (τ : ℂ) • (1 : Matrix B B ℂ)) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).add continuous_const
  have hG : Measurable (fun C : Matrix R B ℂ => AndersonAC.S6.ridgeGram C τ) := by
    simpa only [AndersonAC.S6.ridgeGram, AndersonAC.S6.gram] using hGc.measurable
  have hInv := AndersonAC.AgentS6.measurable_matrix_inv.comp hG
  have hM := AndersonAC.AgentS6.measurable_matrix_mul
    (AndersonAC.AgentS6.measurable_matrix_mul hC hInv) hCt
  simpa only [AndersonAC.S6.ridgeProjection, Function.comp_def] using hM


private theorem measurable_maxLeverage (τ : ℝ) :
    Measurable (fun C : Matrix R B ℂ =>
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ)) := by
  have hpair : Measurable (fun C : Matrix R B ℂ => (C, τ)) :=
    measurable_id.prodMk measurable_const
  have hlev (i : R) : Measurable (fun C : Matrix R B ℂ => AndersonAC.S6.leverage C τ i) := by
    have h := (AndersonAC.AgentS6.measurable_leverage (B := B) (R := R) i).comp hpair
    simpa only [Function.comp_def] using h
  have hnn (i : R) : Measurable (fun C : Matrix R B ℂ =>
      Real.toNNReal (AndersonAC.S6.leverage C τ i)) := by
    with_reducible_and_instances exact (hlev i).real_toNNReal
  have hmax : Measurable (fun C : Matrix R B ℂ =>
      Finset.univ.sup fun i => Real.toNNReal (AndersonAC.S6.leverage C τ i)) := by
    with_reducible_and_instances exact (measurable_finset_sup Finset.univ
      (fun i (C : Matrix R B ℂ) => Real.toNNReal (AndersonAC.S6.leverage C τ i)) hnn)
  unfold AndersonAC.S6.maxWeight
  with_reducible_and_instances exact hmax.coe_nnreal_real


private theorem maxWeight_nonneg (m : R → ℝ) :
    0 ≤ AndersonAC.S6.maxWeight m := by
  unfold AndersonAC.S6.maxWeight
  exact NNReal.coe_nonneg _

private theorem maxLeverage_antitone (C : Matrix R B ℂ) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t) ≤
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C s) := by
  apply AndersonAC.AgentS6.maxWeight_le (maxWeight_nonneg _)
  intro i
  exact ((AndersonAC.S6.ridge_continuous_monotone C i).2.1 hs ht hst).trans
    (AndersonAC.AgentS6.le_maxWeight _ i)

private theorem exists_maxLeverage_row (C : Matrix R B ℂ) {t : ℝ} (ht : 0 < t)
    (hpos : 0 < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t)) :
    ∃ i, AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t) =
      AndersonAC.S6.leverage C t i := by
  classical
  have hne : (Finset.univ : Finset R).Nonempty := by
    by_contra h
    have hEq : (Finset.univ : Finset R) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [AndersonAC.S6.maxWeight, hEq] at hpos
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset R) hne
    (fun i => Real.toNNReal (AndersonAC.S6.leverage C t i))
  refine ⟨i, ?_⟩
  unfold AndersonAC.S6.maxWeight
  rw [heq, Real.coe_toNNReal _ (AndersonAC.AgentS6.leverage_nonneg C ht.le i)]

private theorem row_nonzero_of_pos (C : Matrix R B ℂ) (t : ℝ) (i : R)
    (hpos : 0 < AndersonAC.S6.leverage C t i) : ∃ b, C i b ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hz : AndersonAC.S6.ridgeProjection C t i i = 0 := by
    simp [AndersonAC.S6.ridgeProjection, Matrix.mul_apply, h]
  change 0 < (AndersonAC.S6.ridgeProjection C t i i).re at hpos
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

private theorem maxLeverage_strict (C : Matrix R B ℂ) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s < t)
    (hpos : 0 < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t)) :
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t) <
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C s) := by
  obtain ⟨i, hi⟩ := exists_maxLeverage_row C ht hpos
  have hrowpos : 0 < AndersonAC.S6.leverage C t i := by rw [← hi]; exact hpos
  have hstrict := (AndersonAC.S6.ridge_continuous_monotone C i).2.2
    (row_nonzero_of_pos C t i hrowpos)
  calc
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t) =
        AndersonAC.S6.leverage C t i := hi
    _ < AndersonAC.S6.leverage C s i := hstrict hs ht hst
    _ ≤ AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C s) :=
      AndersonAC.AgentS6.le_maxWeight _ i

private theorem large_of_ridge_level (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l)
    {t : ℝ} (ht : 0 < t)
    (hlevel : 2 * l ≤ AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t)) :
    2 * l < AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C) := by
  have hpos : 0 < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t) := by linarith
  have hhalf : 0 < t / 2 := by positivity
  have hhalf_lt : t / 2 < t := by linarith
  have hstrict := maxLeverage_strict C hhalf ht hhalf_lt hpos
  have hbound : AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C (t / 2)) ≤
      AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C) := by
    apply AndersonAC.AgentS6.maxWeight_le (maxWeight_nonneg _)
    intro i
    have hcal := AndersonAC.S6.ridge_calculus C (t / 2) hhalf
    rcases hcal with ⟨_, _, _, _, hlev, _⟩
    exact (hlev i).2.trans (AndersonAC.AgentS6.le_maxWeight _ i)
  exact lt_of_le_of_lt hlevel (hstrict.trans_le hbound)

private theorem ridge_level_bddAbove (hscalar : RidgeThresholdStatement.{u, v})
    (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l) :
    BddAbove {t : ℝ | 0 < t ∧ 2 * l ≤
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t)} := by
  classical
  by_cases hne : {t : ℝ | 0 < t ∧ 2 * l ≤
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t)}.Nonempty
  · obtain ⟨t, ht, hlevel⟩ := hne
    have hlarge := large_of_ridge_level C l hl ht hlevel
    obtain ⟨hroot, hvalue, _⟩ := hscalar B R C l hl hlarge
    refine ⟨AndersonAC.S6.ridgeThreshold C l, ?_⟩
    intro s hs
    by_contra h
    have hlt : AndersonAC.S6.ridgeThreshold C l < s := lt_of_not_ge h
    have hpos : 0 < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C s) := by
      linarith [hs.2]
    have hstrict := maxLeverage_strict C hroot hs.1 hlt hpos
    rw [hvalue] at hstrict
    exact not_lt_of_ge hs.2 hstrict
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact bddAbove_empty

private theorem ridgeThreshold_nonneg (hscalar : RidgeThresholdStatement.{u, v})
    (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l) :
    0 ≤ AndersonAC.S6.ridgeThreshold C l := by
  classical
  unfold AndersonAC.S6.ridgeThreshold
  by_cases hne : {t : ℝ | 0 < t ∧ 2 * l ≤
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t)}.Nonempty
  · obtain ⟨t, ht⟩ := hne
    exact ht.1.le.trans (le_csSup (ridge_level_bddAbove hscalar C l hl) ht)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

private theorem ridgeThreshold_gt_iff_rat (hscalar : RidgeThresholdStatement.{u, v})
    (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l) (a : ℝ) (ha : 0 ≤ a) :
    a < AndersonAC.S6.ridgeThreshold C l ↔
      ∃ q : ℚ, a < (q : ℝ) ∧ 2 * l ≤
        AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C q) := by
  classical
  have hbdd := ridge_level_bddAbove hscalar C l hl
  constructor
  · intro h
    have hne : {t : ℝ | 0 < t ∧ 2 * l ≤
        AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C t)}.Nonempty := by
      by_contra hn
      have hz : AndersonAC.S6.ridgeThreshold C l = 0 := by
        unfold AndersonAC.S6.ridgeThreshold
        rw [Set.not_nonempty_iff_eq_empty.mp hn, Real.sSup_empty]
      rw [hz] at h
      exact not_lt_of_ge ha h
    obtain ⟨t, ht, hat⟩ := (lt_csSup_iff hbdd hne).mp h
    obtain ⟨q, haq, hqt⟩ := exists_rat_btwn hat
    have hqpos : 0 < (q : ℝ) := lt_of_le_of_lt ha haq
    exact ⟨q, haq, ht.2.trans (maxLeverage_antitone C hqpos ht.1 hqt.le)⟩
  · rintro ⟨q, haq, hlevel⟩
    exact lt_csSup_of_lt hbdd ⟨lt_of_le_of_lt ha haq, hlevel⟩ haq

/-- Threshold measurability, with the separately owned scalar contract explicit. -/
theorem measurable_ridgeThreshold_of (hscalar : RidgeThresholdStatement.{u, v})
    (l : ℝ) (hl : 0 < l) :
    Measurable (fun C : Matrix R B ℂ => AndersonAC.S6.ridgeThreshold C l) := by
  classical
  apply measurable_of_Ioi
  intro a
  by_cases ha : a < 0
  · have heq : (fun C : Matrix R B ℂ => AndersonAC.S6.ridgeThreshold C l) ⁻¹'
        Set.Ioi a = Set.univ := by
      ext C
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le ha (ridgeThreshold_nonneg hscalar C l hl)
    rw [heq]
    exact MeasurableSet.univ
  · have ha' : 0 ≤ a := le_of_not_gt ha
    have heq : (fun C : Matrix R B ℂ => AndersonAC.S6.ridgeThreshold C l) ⁻¹'
        Set.Ioi a = ⋃ q : ℚ, {C : Matrix R B ℂ | a < (q : ℝ) ∧ 2 * l ≤
          AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C q)} := by
      ext C
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ridgeThreshold_gt_iff_rat hscalar C l hl a ha'
    rw [heq]
    apply MeasurableSet.iUnion
    intro q
    exact (if hq : a < (q : ℝ) then by
      simpa only [hq, true_and] using
        (measurableSet_le measurable_const (measurable_maxLeverage (B := B) (R := R) q))
      else by simp only [hq, false_and, Set.ofPred_false]; exact MeasurableSet.empty)


open scoped Matrix.Norms.L2Operator in
/-- The range projection is a pointwise limit of measurable positive-ridge projections. -/
theorem measurable_rangeProjection :
    Measurable (fun C : Matrix R B ℂ => AndersonAC.S6.rangeProjection C) := by
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    simp
  apply measurable_of_tendsto_metrizable' (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun τ => measurable_ridgeProjection (B := B) (R := R) τ)
  exact tendsto_pi_nhds.mpr fun C => AndersonAC.S6.ridge_limit C


/-- Join the measurable selector with the separately owned scalar threshold contract. -/
theorem ridgeSelection_of_threshold (hscalar : RidgeThresholdStatement.{u, v}) :
    RidgeSelectionStatement.{u, v} := by
  intro B R instB instDecB instR instDecR l hl
  refine ⟨⟨measurable_ridgeThreshold_of hscalar l hl, measurable_rangeProjection⟩, ?_⟩
  exact fun C hlarge => hscalar B R C l hl hlarge

/-- The frozen ridge selection contract, including both measurable matrix functions. -/
theorem ridgeSelection_proof : RidgeSelectionStatement.{u, v} :=
  ridgeSelection_of_threshold ridgeThreshold_proof

end AndersonAC.SolS6
