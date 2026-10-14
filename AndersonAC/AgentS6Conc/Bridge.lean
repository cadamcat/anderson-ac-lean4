import AndersonAC.S6.Definitions
import AndersonAC.AgentS6Conc.VectorDilation
import AndersonAC.AgentS6Conc.DilationLinear
import AndersonAC.AgentS6Conc.Restriction
import AndersonAC.AgentS6Conc.Normalized
import AndersonAC.AgentS6Conc.Variance
import AndersonAC.AgentS6Conc.MatrixVariance
import AndersonAC.S45.MatrixConcentrationProof

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder ENNReal NNReal

namespace AndersonAC.AgentS6Conc

def vectorBadEvent {Ω : Type*} [MeasurableSpace Ω] {D : ℕ}
    (N : ℕ) (a : ℝ) (Y : ℕ → Ω → EuclideanSpace ℂ (Fin D)) : Set Ω :=
  {ω | ∃ n ≤ N, a < ‖∑ k ∈ Finset.range n, Y k ω‖}

theorem vectorBadEvent_measurable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ}
    (N : ℕ) (a : ℝ) (Y : ℕ → Ω → EuclideanSpace ℂ (Fin D))
    (hY : ∀ k, StronglyMeasurable (Y k)) :
    MeasurableSet (vectorBadEvent N a Y) := by
  have hEq : vectorBadEvent N a Y = ⋃ n : Fin (N + 1),
      {ω | a < ‖∑ k ∈ Finset.range n.val, Y k ω‖} := by
    ext ω
    simp only [vectorBadEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn, hω⟩
      exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, hω⟩
    · rintro ⟨n, hω⟩
      exact ⟨n.val, Nat.le_of_lt_succ n.isLt, hω⟩
  rw [hEq]
  apply MeasurableSet.iUnion
  intro n
  have hsum : StronglyMeasurable
      (fun ω => ∑ k ∈ Finset.range n.val, Y k ω) :=
    Finset.stronglyMeasurable_fun_sum _ (fun k hk => hY k)
  exact measurableSet_Ioi.preimage (continuous_norm.measurable.comp hsum.measurable)

def truncatedMatrixIncrement {Ω : Type*} {D : ℕ} (N : ℕ)
    (Y : ℕ → Ω → EuclideanSpace ℂ (Fin D)) :
    ℕ → Ω → Matrix (Fin (Fintype.card (Unit ⊕ Fin D))) (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ :=
  fun k ω => if k < N then vectorDilation (Y k ω) else 0

def truncatedMatrixVariance {Ω : Type*} (N : ℕ) (v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k ω => if k < N then v k ω else 0

theorem truncatedVariance_sum_le {Ω : Type*} (N n : ℕ) (v : ℕ → Ω → ℝ)
    (hv : ∀ k ω, 0 ≤ v k ω) (ω : Ω) :
    (∑ k ∈ Finset.range n, truncatedMatrixVariance N v k ω) ≤
      ∑ k ∈ Finset.range N, v k ω := by
  let s := (Finset.range n).filter (fun k => k < N)
  have hsum : (∑ k ∈ Finset.range n, truncatedMatrixVariance N v k ω) =
      ∑ k ∈ s, v k ω := by
    simp [truncatedMatrixVariance, s, Finset.sum_filter]
  rw [hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  · intro k hk hnot
    exact hv k ω

theorem truncatedMatrixIncrement_sum {Ω : Type*} {D : ℕ} (N n : ℕ)
    (hn : n ≤ N) (Y : ℕ → Ω → EuclideanSpace ℂ (Fin D)) (ω : Ω) :
    (∑ k ∈ Finset.range n, truncatedMatrixIncrement N Y k ω) =
      vectorDilation (∑ k ∈ Finset.range n, Y k ω) := by
  calc
    (∑ k ∈ Finset.range n, truncatedMatrixIncrement N Y k ω) =
        ∑ k ∈ Finset.range n, vectorDilation (Y k ω) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [truncatedMatrixIncrement, Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) hn]
    _ = vectorDilation (∑ k ∈ Finset.range n, Y k ω) := by
      change ∑ k ∈ Finset.range n, vectorDilationCLM D (Y k ω) =
        vectorDilationCLM D (∑ k ∈ Finset.range n, Y k ω)
      exact (map_sum (vectorDilationCLM D) (fun k => Y k ω) (Finset.range n)).symm

theorem blueprint_opNorm_eq_matrixNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : AndersonAC.Blueprint.opNorm A = ‖A‖ := by
  change ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ = ‖A‖
  exact Matrix.l2_opNorm_toEuclideanCLM A

/-- The unconditional, truncated vector tail follows from the matrix maximal
inequality after Hermitian dilation. -/
theorem vector_maximal_unconditional (hinput : AndersonAC.Blueprint.ConcentrationInput)
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (D N : ℕ)
    (Y : ℕ → Ω → EuclideanSpace ℂ (Fin D)) (v : ℕ → Ω → ℝ)
    (J V a : ℝ) (hJ : 0 < J) (hV : 0 < V) (ha : 0 < a)
    (hYsm : ∀ k, StronglyMeasurable[F (k + 1)] (Y k))
    (hYint : ∀ k, Integrable (Y k) μ)
    (hYmean : ∀ k, μ[Y k | F k] =ᵐ[μ] 0)
    (hvsm : ∀ k, StronglyMeasurable[F k] (v k))
    (hvpos : ∀ k ω, 0 ≤ v k ω)
    (hYbound : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ J)
    (hvar : ∀ k, ∀ᵐ ω ∂μ,
      μ[(fun ω => ‖Y k ω‖ ^ 2) | F k] ω ≤ v k ω)
    (hbudget : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range N, v k ω ≤ V) :
    μ (vectorBadEvent N a Y) ≤ ENNReal.ofReal
      (2 * (Fintype.card (Unit ⊕ Fin D) : ℝ) *
        Real.exp (-Classical.choose hinput.maximal * min (a ^ 2 / V) (a / J))) := by
  let W := truncatedMatrixIncrement N Y
  let Wv := truncatedMatrixVariance N v
  have hWsm : ∀ k, StronglyMeasurable[F (k + 1)] (W k) := by
    intro k
    change StronglyMeasurable[F (k + 1)]
      (fun ω => if k < N then vectorDilation (Y k ω) else 0)
    by_cases hk : k < N
    · simpa [hk, vectorDilationCLM_apply] using
        (vectorDilationCLM D).continuous.comp_stronglyMeasurable (hYsm k)
    · simpa [hk] using
        (stronglyMeasurable_const : StronglyMeasurable[F (k + 1)]
          (fun _ : Ω => (0 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D)))
            (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ)))
  have hWint : ∀ k, Integrable (W k) μ := by
    intro k
    change Integrable (fun ω => if k < N then vectorDilation (Y k ω) else 0) μ
    by_cases hk : k < N
    · simpa [hk, vectorDilationCLM_apply] using
        (vectorDilationCLM D).integrable_comp (hYint k)
    · simp [hk]
  have hWmean : ∀ k, AndersonAC.Blueprint.matrixCondExp μ (F k) (W k) =ᵐ[μ] 0 := by
    intro k
    have hZmean : μ[(fun ω => vectorDilation (Y k ω)) | F k] =ᵐ[μ] 0 := by
      have hcomp := (vectorDilationCLM D).comp_condExp_comm (m := F k) (hYint k)
      filter_upwards [hcomp, hYmean k] with ω hc hm
      calc
        μ[(fun ω => vectorDilation (Y k ω)) | F k] ω =
            vectorDilationCLM D (μ[Y k | F k] ω) := by
              simpa [Function.comp_def, vectorDilationCLM_apply] using hc.symm
        _ = 0 := by
          rw [hm]
          simpa [vectorDilationCLM_apply] using (vectorDilationCLM D).map_zero
    have hmean : μ[W k | F k] =ᵐ[μ] 0 := by
      change μ[(fun ω => if k < N then vectorDilation (Y k ω) else 0) | F k] =ᵐ[μ] 0
      by_cases hk : k < N
      · simpa [hk] using hZmean
      · filter_upwards with ω
        simp [hk]
    exact (AndersonAC.AgentS45.matrixCondExp_ae_eq (m := F k) μ (W k) (hWint k)).trans hmean
  have hWvsm : ∀ k, StronglyMeasurable[F k] (Wv k) := by
    intro k
    change StronglyMeasurable[F k] (fun ω => if k < N then v k ω else 0)
    by_cases hk : k < N
    · simpa [hk] using hvsm k
    · simpa [hk] using
        (stronglyMeasurable_const : StronglyMeasurable[F k] (fun _ : Ω => (0 : ℝ)))
  have hWvpos : ∀ k ω, 0 ≤ Wv k ω := by
    intro k ω
    by_cases hk : k < N <;> simp [Wv, truncatedMatrixVariance, hk, hvpos k ω]
  have hWjump : ∀ k, ∀ᵐ ω ∂μ, AndersonAC.Blueprint.opNorm (W k ω) ≤ J := by
    intro k
    by_cases hk : k < N
    · filter_upwards [hYbound k] with ω hω
      calc
        AndersonAC.Blueprint.opNorm (W k ω) = ‖W k ω‖ := blueprint_opNorm_eq_matrixNorm _
        _ = ‖vectorDilation (Y k ω)‖ := by simp [W, truncatedMatrixIncrement, hk]
        _ = ‖Y k ω‖ := vectorDilation_norm _
        _ ≤ J := hω
    · filter_upwards with ω
      calc
        AndersonAC.Blueprint.opNorm (W k ω) = ‖W k ω‖ := blueprint_opNorm_eq_matrixNorm _
        _ = 0 := by simp [W, truncatedMatrixIncrement, hk]
        _ ≤ J := by exact le_of_lt hJ
  have hWherm : ∀ k, ∀ᵐ ω ∂μ, (W k ω).IsHermitian ∧
      AndersonAC.Blueprint.opNorm (W k ω) ≤ J := by
    intro k
    filter_upwards [hWjump k] with ω hω
    by_cases hk : k < N
    · refine ⟨?_, hω⟩
      simpa [W, truncatedMatrixIncrement, hk] using vectorDilation_hermitian (Y k ω)
    · have hzero : W k ω = 0 := by simp [W, truncatedMatrixIncrement, hk]
      have h0bound : AndersonAC.Blueprint.opNorm
          (0 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D)))
            (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ) ≤ J := by
        rw [blueprint_opNorm_eq_matrixNorm]
        simpa using hJ.le
      exact ⟨hzero ▸ Matrix.isHermitian_zero, by simpa [hzero] using h0bound⟩
  have hWvariance : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ Wv k ω ∧
      ((Wv k ω : ℂ) • (1 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D)))
          (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ) -
        AndersonAC.Blueprint.matrixCondExp μ (F k) (fun ω => W k ω * W k ω) ω).PosSemidef := by
    intro k
    by_cases hk : k < N
    · have h := vectorDilation_condVariance μ F (Y k) (v k) k J hJ (hYint k) (hYsm k)
        (hYbound k) (hvar k) (hvpos k)
      simpa [W, Wv, truncatedMatrixIncrement, truncatedMatrixVariance, hk] using h
    · have hWzero : W k = fun _ => 0 := by
        funext ω
        simp [W, truncatedMatrixIncrement, hk]
      have hVzero : Wv k = fun _ => 0 := by
        funext ω
        simp [Wv, truncatedMatrixVariance, hk]
      have hCEzero : AndersonAC.Blueprint.matrixCondExp μ (F k)
          (fun ω => W k ω * W k ω) = 0 := by
        ext i j
        simp [hWzero, AndersonAC.Blueprint.matrixCondExp]
      filter_upwards [ae_of_all μ (fun ω => congrFun hCEzero ω)] with ω hce
      constructor
      · simp [hVzero]
      · rw [hVzero, hce]
        simpa using (Matrix.PosSemidef.zero :
          (0 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D)))
            (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ).PosSemidef)
  have hWbudget : ∀ᵐ ω ∂μ, ∀ n,
      (∑ k ∈ Finset.range n, Wv k ω) ≤ V := by
    filter_upwards [hbudget] with ω hω
    intro n
    exact (truncatedVariance_sum_le N n v hvpos ω).trans hω
  let cConc := Classical.choose hinput.maximal
  have hmax := (Classical.choose_spec hinput.maximal).2
  have hmatTail := hmax Ω μ inferInstance (Fintype.card (Unit ⊕ Fin D)) F W Wv J V hJ hV
    (fun k => hWsm k)
    (fun k i j => AndersonAC.AgentS45.entry_integrable (hWint k) i j)
    hWherm hWmean (fun k => (hWvsm k).measurable) hWvariance hWbudget a ha
  have hsubset : vectorBadEvent N a Y ⊆
      {ω | ∃ n : ℕ, a < AndersonAC.Blueprint.opNorm
        (∑ k ∈ Finset.range n, W k ω)} := by
    intro ω hω
    rcases hω with ⟨n, hn, hlarge⟩
    refine ⟨n, ?_⟩
    rw [truncatedMatrixIncrement_sum N n hn Y ω]
    have hnorm : AndersonAC.Blueprint.opNorm
        (vectorDilation (∑ k ∈ Finset.range n, Y k ω)) =
        ‖∑ k ∈ Finset.range n, Y k ω‖ := by
      rw [blueprint_opNorm_eq_matrixNorm, vectorDilation_norm]
    simpa [hnorm] using hlarge
  exact (measure_mono hsubset).trans hmatTail

end AndersonAC.AgentS6Conc

namespace AndersonAC.AgentS6

set_option maxHeartbeats 0

open MeasureTheory ProbabilityTheory Filter Topology
open AndersonAC.Blueprint
open AndersonAC.S6
open AndersonAC.AgentS6Conc

/-- Vector Lemma 5.6 follows from the blueprint's Hermitian matrix maximal
inequality by dilation and conditioning on the initial sigma-algebra. -/
theorem vectorConcentrationBridge_proof :
    AndersonAC.Blueprint.ConcentrationInput →
      ∃ c : ℝ, 0 < c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (F : Filtration ℕ ‹MeasurableSpace Ω›),
        VectorConcentrationInput μ F c := by
  intro hinput
  let c : ℝ := Classical.choose hinput.maximal
  have hc : 0 < c := Classical.choose_spec hinput.maximal |>.1
  refine ⟨c, hc, ?_⟩
  intro Ω mΩ μ hμ F
  intro D N Y v J V a hJ hV ha hYsm hYint hYmean hvsm hvpos hYbound hvar hbudget
  let E : Set Ω := vectorBadEvent N a Y
  let B : ℝ := 2 * (Fintype.card (Unit ⊕ Fin D) : ℝ) *
    Real.exp (-c * min (a ^ 2 / V) (a / J))
  have hYambient : ∀ k, StronglyMeasurable (Y k) := by
    intro k
    exact (hYsm k).mono (F.le (k + 1))
  have hEmeas : MeasurableSet E := by
    exact vectorBadEvent_measurable N a Y hYambient
  have hEint : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hEmeas
  have hBnonneg : 0 ≤ B := by positivity
  have hnormsqint : ∀ k, Integrable (fun ω => ‖Y k ω‖ ^ 2) μ := by
    intro k
    have hsm : StronglyMeasurable (fun ω => ‖Y k ω‖ ^ 2) :=
      (continuous_norm.pow 2).comp_stronglyMeasurable (hYambient k)
    have hbd : ∀ᵐ ω ∂μ, ‖‖Y k ω‖ ^ 2‖ ≤ J ^ 2 := by
      filter_upwards [hYbound k] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) hJ.le).2 hω
    exact Integrable.of_bound hsm.aestronglyMeasurable (J ^ 2) hbd
  have hset : ∀ A, MeasurableSet[F 0] A →
      μ.real (E ∩ A) ≤ B * μ.real A := by
    intro A hA
    have hAambient : MeasurableSet A := F.le 0 A hA
    by_cases hApos : μ A = 0
    · have hEAzero : μ (E ∩ A) = 0 := by
        apply le_antisymm
        · exact (measure_mono Set.inter_subset_right).trans (by simpa [hApos])
        · exact bot_le
      simp [Measure.real, hEAzero, hApos]
    · let ν : Measure Ω := normalizedRestrict μ A
      have hνprob : IsProbabilityMeasure ν := by
        simpa [ν] using isProbabilityMeasure_normalizedRestrict hAambient hApos
      letI : IsProbabilityMeasure ν := hνprob
      have hYintν : ∀ k, Integrable (Y k) ν := by
        intro k
        change Integrable (Y k) (((μ A).toNNReal)⁻¹ • μ.restrict A)
        exact (hYint k).restrict.smul_measure_nnreal
      have hmeanν : ∀ k, ν[Y k | F k] =ᵐ[ν] 0 := by
        intro k
        have hAk : MeasurableSet[F k] A := F.mono (Nat.zero_le k) A hA
        have hCE := condExp_scaledRestrict_ae_eq (μ := μ) (m := F k) (mΩ := mΩ)
          (hm := F.le k) (A := A) (hA := hAk)
          (c := (μ A).toNNReal⁻¹) (hf := hYint k)
        have hCEnu : ν[Y k | F k] =ᵐ[ν] μ[Y k | F k] := by
          simpa [ν, normalizedRestrict] using hCE
        have hzero := by
          simpa [ν] using ae_normalizedRestrict_of_ae μ A (hYmean k)
        filter_upwards [hCEnu, hzero] with ω hce hz
        rw [hce]
        exact hz
      have hYboundν : ∀ k, ∀ᵐ ω ∂ν, ‖Y k ω‖ ≤ J := by
        intro k
        simpa [ν] using ae_normalizedRestrict_of_ae μ A (hYbound k)
      have hvarν : ∀ k, ∀ᵐ ω ∂ν,
          ν[(fun ω => ‖Y k ω‖ ^ 2) | F k] ω ≤ v k ω := by
        intro k
        have hCE := condExp_scaledRestrict_ae_eq (μ := μ) (m := F k) (mΩ := mΩ)
          (hm := F.le k) (A := A) (hA := F.mono (Nat.zero_le k) A hA)
          (c := (μ A).toNNReal⁻¹) (hf := hnormsqint k)
        have hCEnu : ν[(fun ω => ‖Y k ω‖ ^ 2) | F k] =ᵐ[ν]
            μ[(fun ω => ‖Y k ω‖ ^ 2) | F k] := by
          simpa [ν, normalizedRestrict] using hCE
        have hvar' : ∀ᵐ ω ∂ν,
            μ[(fun ω => ‖Y k ω‖ ^ 2) | F k] ω ≤ v k ω := by
          simpa [ν] using ae_normalizedRestrict_of_ae μ A (hvar k)
        filter_upwards [hCEnu, hvar'] with ω hce hv
        rw [hce]
        exact hv
      have hbudgetν : ∀ᵐ ω ∂ν, ∑ k ∈ Finset.range N, v k ω ≤ V := by
        simpa [ν] using ae_normalizedRestrict_of_ae μ A hbudget
      have htail := vector_maximal_unconditional hinput ν F D N Y v J V a hJ hV ha
        hYsm hYintν hmeanν hvsm hvpos hYboundν hvarν hbudgetν
      simpa [B, c] using normalizedRestrict_event_le_real hAambient hEmeas hApos hBnonneg htail
  have hm0 : F 0 ≤ ‹MeasurableSpace Ω› := F.le 0
  have htrimFinite : IsFiniteMeasure (μ.trim hm0) := by
    refine ⟨?_⟩
    rw [trim_measurableSet_eq hm0 MeasurableSet.univ]
    exact measure_lt_top μ Set.univ
  letI : IsFiniteMeasure (μ.trim hm0) := htrimFinite
  let p : Ω → ℝ := conditionalProbability μ (F 0) E
  have hpInt : Integrable p μ := by
    change Integrable (μ[E.indicator (fun _ : Ω => (1 : ℝ)) | F 0]) μ
    exact integrable_condExp
  have hpSM : StronglyMeasurable[F 0] p := by
    change StronglyMeasurable[F 0] (μ[E.indicator (fun _ : Ω => (1 : ℝ)) | F 0])
    exact stronglyMeasurable_condExp
  have hpTrim : Integrable p (μ.trim hm0) := hpInt.trim hm0 hpSM
  have hBTrim : Integrable (fun _ : Ω => B) (μ.trim hm0) := integrable_const B
  have hsetIntegral : ∀ s, MeasurableSet[F 0] s → (μ.trim hm0) s < ∞ →
      ∫ x in s, p x ∂(μ.trim hm0) ≤ ∫ x in s, B ∂(μ.trim hm0) := by
    intro s hs hsTop
    change ∫ x in s, (μ[E.indicator (fun _ : Ω => (1 : ℝ)) | F 0]) x ∂(μ.trim hm0) ≤
      ∫ x in s, B ∂(μ.trim hm0)
    calc
      ∫ x in s, (μ[E.indicator (fun _ : Ω => (1 : ℝ)) | F 0]) x ∂(μ.trim hm0) =
          ∫ x in s, (μ[E.indicator (fun _ : Ω => (1 : ℝ)) | F 0]) x ∂μ :=
        (setIntegral_trim hm0 hpSM hs).symm
      _ ≤ ∫ x in s, B ∂μ := by
        rw [setIntegral_condExp hm0 hEint hs, setIntegral_indicator hEmeas]
        have hprob := hset s hs
        rw [Set.inter_comm] at hprob
        simpa [setIntegral_const, Measure.real, smul_eq_mul, mul_comm] using hprob
      _ = ∫ x in s, B ∂(μ.trim hm0) :=
        setIntegral_trim hm0 stronglyMeasurable_const hs
  have hpLe : p ≤ᵐ[μ.trim hm0] fun _ => B :=
    ae_le_of_forall_setIntegral_le hpTrim hBTrim hsetIntegral
  have hpLeμ : p ≤ᵐ[μ] fun _ => B := ae_of_ae_trim hm0 hpLe
  have hcard : (Fintype.card (Unit ⊕ Fin D) : ℝ) = (D + 1 : ℝ) := by
    simp [Fintype.card_sum]
    ring
  filter_upwards [hpLeμ] with ω hω
  change conditionalProbability μ (F 0) E ω ≤
    2 * (D + 1 : ℝ) * Real.exp (-c * min (a ^ 2 / V) (a / J))
  calc
    conditionalProbability μ (F 0) E ω ≤ B := by simpa [p] using hω
    _ = 2 * (D + 1 : ℝ) * Real.exp (-c * min (a ^ 2 / V) (a / J)) := by
      simp [B]
      ring

end AndersonAC.AgentS6

end
