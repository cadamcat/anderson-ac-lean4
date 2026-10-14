import AndersonAC.AgentS6Budget.Telescope
import AndersonAC.AgentS6Budget.Stream
import AndersonAC.AgentS6Budget.BiasBounds
import AndersonAC.AgentS6Budget.ConcentrationMargins
import AndersonAC.AgentS6Budget.Probability

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6
universe u

set_option maxHeartbeats 2000000 in
theorem compressed_budget_event (C c cConc : ℝ) (hC : 1 ≤ C) (hc : 0 < c) (hcConc : 0 < cConc) :
    ∃ b : ℝ, 0 < b ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order) (d : ℕ) (K Cloc : ℝ)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ)
      (Q : Finset (Fin n)),
      0 < t → t ≤ 1 → 1 ≤ heatLimit t → K ≤ C → AndersonAC.L64.Small t C →
      (∀ ω i, c ≤ (r ω i).im) →
      (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
      (∀ k ω, k < q.stop ω → HeatPrestate t C
        (fun i : {i // i ∈ (q.state k ω).active} => r ω i) (trialInverse t (r ω) (q.state k ω))) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      (∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2) →
      VectorConcentrationInput μ q.history cConc →
      (80 * C ^ 5 * t ^ ((21 / 100) * delta) ≤ 1 / 4) →
      (40 * C ^ 5 * Real.sqrt (C / c) * t ^ ((14 / 100) * delta) ≤ 1 / 4) →
      (20 * C ^ 5 * (C / c) * t ^ ((135 / 1000) * delta) ≤ 1 / 4) →
      ∃ G : Set Ω, MeasurableSet G ∧
        (∀ ω, ω ∉ G →
          (∀ i ∈ Q, ∀ j ∈ Q, ‖scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) i j‖ ≤
            Real.sqrt t * entryBudget t / 2) ∧
          (∀ i ∈ Q, ‖packVector (fun j : {j // j ∈ Q} =>
            scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) i j)‖ ≤ Real.sqrt (rowBudget t) / 2) ∧
          ‖packVector (fun ij : {i // i ∈ Q} × {j // j ∈ Q} =>
            scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) ij.1 ij.2)‖ ≤ Real.sqrt (frobeniusBudget t) / 2) ∧
        (∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) G ω ≤
          (8 * (Q.card : ℝ) ^ 2 + 2 * Q.card + 2) *
            Real.exp (-cConc * b * t ^ (-budgetConcentrationExponent))) := by
  classical
  let L : ℝ := 4 * C
  let W : ℝ := C / c
  have hC0 : 0 < C := by linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  obtain ⟨b, hb, hmargin⟩ := distortion_concentration_margins L W hL hW
  refine ⟨b, hb, ?_⟩
  intro Ω _ μ _ n core t r g0 order q d K Cloc dist collapsed ell Q ht ht1 hN hKC hsmall
    hr hstart hpre hlocal hpiv hconc hbe hbr hbf
  let N := heatLimit t
  let u := heatColumn q
  let A := runningCoefficient q
  let M : ℝ := 20 * C ^ 5 * Real.sqrt t * t ^ betaW
  let T : ℝ := Real.exp (-cConc * b * t ^ (-budgetConcentrationExponent))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < heatLimit t)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hH : 0 < fourthCap t := Real.rpow_pos_of_pos ht _
  have hrow : 0 < rowBudget t := Real.rpow_pos_of_pos ht _
  have hfrob : 0 < frobeniusBudget t := by unfold frobeniusBudget; positivity
  have hri : ∀ ω i, 0 < (r ω i).im := fun ω i => hc.trans_le (hr ω i)
  have hcoef := runningCoefficient_bounds μ q d c K Cloc C dist collapsed ell hlocal hC hKC hsmall hpre hpiv
  have hfourth : ∀ k ω i, ‖u k ω i‖ ^ 4 ≤ fourthCap t := heatColumn_fourth_le q ht C hpre
  have hmass : ∀ k ω, ∑ i, ‖u k ω i‖ ^ 2 ≤ W := heatColumn_square_sum_le q ht c C hc hC0.le hr hpre
  have h4time : ∀ ω i, ∑ k ∈ Finset.range N, ‖u k ω i‖ ^ 4 ≤ 16 * fourthCap t :=
    heatColumn_fourth_sum_le q ht ht1 hstart
  have h2time : ∀ ω i, ∑ k ∈ Finset.range N, ‖u k ω i‖ ^ 2 ≤ 4 * t ^ ((27 / 100) * delta) :=
    heatColumn_square_time_sum_le q ht ht1 hstart
  have hmeans := bias_below_quarter C W hC0.le hW.le ht hbe hbr hbf
  have hratios := hmargin t ht ht1 hN
  have htransfer : ∀ (D : ℕ) (S : Set Ω) (m : ℝ),
      (∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) S ω ≤
        2 * (D + 1) * Real.exp (-cConc * m)) →
      b * t ^ (-budgetConcentrationExponent) ≤ m →
      ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) S ω ≤ 2 * (D + 1) * T := by
    intro D S m h hm
    have hexp : Real.exp (-cConc * m) ≤ T := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hm hcConc.le
      nlinarith
    exact h.mono fun ω hω => hω.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  let EE : Fin n → Fin n → Set Ω := fun i j => streamEvent N (entryBudget t / 2)
    (fun k ω => A k ω • entryVector u t i j k ω)
  let ER : Fin n → Set Ω := fun i => streamEvent N (Real.sqrt (rowBudget t) / 2)
    (fun k ω => A k ω • rowVector u Q i k ω)
  let EF : Set Ω := streamEvent N (Real.sqrt (frobeniusBudget t) / 2)
    (fun k ω => A k ω • matrixVector u Q k ω)
  have hpE : ∀ i j, ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) (EE i j) ω ≤ 4 * T := by
    intro i j
    have hU := entryVector_bounds u ht N (fourthCap t) hfourth h4time i j
    have h := scalar_vector_tail_of_squares μ q.history cConc hconc (Fintype.card Unit) N A
      (entryVector u t i j) L M (16 * fourthCap t / t) (Real.sqrt (fourthCap t / t)) (entryBudget t / 2)
      hL hM (by positivity) (by positivity) (by unfold entryBudget; positivity)
      (runningCoefficient_adapted q) (entryVector_adapted q.history u (heatColumn_adapted q) t i j)
      hcoef.1 hU.1 hcoef.2 hU.2 hmeans.1
    have h' := htransfer (Fintype.card Unit) (EE i j) _ h hratios.1
    norm_num only [Fintype.card_unit, Nat.cast_one, one_add_one_eq_two, show (2 : ℝ) * 2 = 4 by norm_num] at h'
    exact h'
  have hpR : ∀ i, ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) (ER i) ω ≤
      2 * ((Q.card : ℝ) + 1) * T := by
    intro i
    have hU := rowVector_bounds u Q N (fourthCap t) W (4 * t ^ ((27 / 100) * delta)) hW.le hfourth hmass h2time i
    have h := scalar_vector_tail_of_squares μ q.history cConc hconc (Fintype.card {i // i ∈ Q}) N A
      (rowVector u Q i) L M (W * (4 * t ^ ((27 / 100) * delta))) (Real.sqrt (W * Real.sqrt (fourthCap t)))
      (Real.sqrt (rowBudget t) / 2) hL hM (by positivity) (by positivity) (by positivity)
      (runningCoefficient_adapted q) (rowVector_adapted q.history u (heatColumn_adapted q) Q i)
      hcoef.1 hU.1 hcoef.2 hU.2 hmeans.2.1
    have h' := htransfer (Fintype.card {i // i ∈ Q}) (ER i) _ h hratios.2.1
    simpa only [Fintype.card_coe] using h'
  have hpF : ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) EF ω ≤
      2 * ((Q.card : ℝ) ^ 2 + 1) * T := by
    have hU := matrixVector_bounds u Q N W hmass
    have h := scalar_vector_tail_of_squares μ q.history cConc hconc
      (Fintype.card ({i // i ∈ Q} × {j // j ∈ Q})) N A (matrixVector u Q) L M ((N : ℝ) * W ^ 2) W
      (Real.sqrt (frobeniusBudget t) / 2) hL hM (by positivity) hW (by positivity)
      (runningCoefficient_adapted q) (matrixVector_adapted q.history u (heatColumn_adapted q) Q)
      hcoef.1 hU.1 hcoef.2 hU.2 hmeans.2.2
    have h' := htransfer (Fintype.card ({i // i ∈ Q} × {j // j ∈ Q})) EF _ h hratios.2.2
    simpa only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, pow_two] using h'
  let I := ({i // i ∈ Q} × {j // j ∈ Q}) ⊕ ({i // i ∈ Q} ⊕ Unit)
  let E : I → Set Ω := fun z => match z with
    | .inl ij => EE ij.1 ij.2
    | .inr (.inl i) => ER i
    | .inr (.inr _) => EF
  let p : I → ℝ := fun z => match z with
    | .inl _ => 4
    | .inr (.inl _) => 2 * ((Q.card : ℝ) + 1)
    | .inr (.inr _) => 2 * ((Q.card : ℝ) ^ 2 + 1)
  let G := ⋃ z : I, E z
  have hEm : ∀ z, MeasurableSet (E z) := by
    intro z
    rcases z with ij | z
    · exact streamEvent_measurable _ _ _ (fun k =>
        ((runningCoefficient_adapted q k).mono (q.history.le _)).smul
          ((entryVector_adapted q.history u (heatColumn_adapted q) t ij.1 ij.2 k).mono (q.history.le _)))
    · rcases z with i | _
      · exact streamEvent_measurable _ _ _ (fun k =>
          ((runningCoefficient_adapted q k).mono (q.history.le _)).smul
            ((rowVector_adapted q.history u (heatColumn_adapted q) Q i k).mono (q.history.le _)))
      · exact streamEvent_measurable _ _ _ (fun k =>
          ((runningCoefficient_adapted q k).mono (q.history.le _)).smul
            ((matrixVector_adapted q.history u (heatColumn_adapted q) Q k).mono (q.history.le _)))
  refine ⟨G, MeasurableSet.iUnion hEm, ?_, ?_⟩
  · intro ω hω
    have hz : ∀ z : I, ω ∉ E z := fun z h => hω (Set.mem_iUnion.mpr ⟨z, h⟩)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi j hj
      have hnot : ¬ entryBudget t / 2 < ‖∑ k ∈ Finset.range N, A k ω • entryVector u t i j k ω‖ :=
        fun h => hz (.inl (⟨i, hi⟩, ⟨j, hj⟩)) ⟨N, le_rfl, h⟩
      rw [stop_entryVector_norm q ht ω (hri ω) i j] at hnot
      calc
        _ = Real.sqrt t * ‖(q.state (q.stop ω) ω).hatG i j - g0 ω i j‖ := by
          simp [scaledInverse, Matrix.sub_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
        _ ≤ Real.sqrt t * (entryBudget t / 2) := mul_le_mul_of_nonneg_left (not_lt.mp hnot) (Real.sqrt_nonneg t)
        _ = _ := by ring
    · intro i hi
      have hnot : ¬ Real.sqrt (rowBudget t) / 2 < ‖∑ k ∈ Finset.range N, A k ω • rowVector u Q i k ω‖ :=
        fun h => hz (.inr (.inl ⟨i, hi⟩)) ⟨N, le_rfl, h⟩
      rw [← stop_rowVector_eq_sum q ht ω (hri ω) Q i] at hnot
      exact not_lt.mp hnot
    · have hnot : ¬ Real.sqrt (frobeniusBudget t) / 2 < ‖∑ k ∈ Finset.range N, A k ω • matrixVector u Q k ω‖ :=
        fun h => hz (.inr (.inr ())) ⟨N, le_rfl, h⟩
      rw [← stop_matrixVector_eq_sum q ht ω (hri ω) Q] at hnot
      exact not_lt.mp hnot
  · have hp : ∀ z : I, ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) (E z) ω ≤ p z * T := by
      intro z
      rcases z with ij | z
      · exact hpE ij.1 ij.2
      · rcases z with i | _
        · exact hpR i
        · exact hpF
    have hpall := ae_all_iff.mpr hp
    have hsum := condProb_iUnion_le μ q.history 0 E hEm
    have hcount : ∑ z : I, p z = 8 * (Q.card : ℝ) ^ 2 + 2 * Q.card + 2 := by
      simp only [I, p, Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_coe, Fintype.card_unit, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_one, one_mul]
      ring
    filter_upwards [hsum, hpall] with ω hsum hp
    calc
      conditionalProbability μ (q.history 0) G ω ≤ ∑ z : I, conditionalProbability μ (q.history 0) (E z) ω := hsum
      _ ≤ ∑ z : I, p z * T := Finset.sum_le_sum fun z _ => hp z
      _ = _ := by rw [← Finset.sum_mul, hcount]

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.compressed_budget_event
