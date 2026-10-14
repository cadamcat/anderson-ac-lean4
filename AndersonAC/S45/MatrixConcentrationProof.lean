import AndersonAC.S45.ConcentrationPackage
import AndersonAC.S45.Definitions
import AndersonAC.S45.Deletion

/-! The S45 form of Lemma 5.6 (`AndersonAC.S45.matrix_concentration`, Bochner
matrix conditional expectations, Loewner order, arbitrary finite index type)
from the blueprint form `maximal_of` (entrywise conditional expectations,
`Fin N` index). Also `matrixCondExp_eq`. Sorry-free; the only inputs are the
hypotheses `GoldenThompson` and `TraceHelpers`. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

/-- The `(i, j)` entry as a continuous real-linear map. -/
def entryCLM {n : Type*} [Fintype n] [DecidableEq n] (i j : n) : Matrix n n ℂ →L[ℝ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_id.matrix_elem i j

theorem entry_condExp {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {n : Type*} [Fintype n] [DecidableEq n]
    {Y : Ω → Matrix n n ℂ} (hY : Integrable Y μ) (i j : n) :
    (fun ω => μ[Y | m] ω i j) =ᵐ[μ] μ[fun ω => Y ω i j | m] :=
  (entryCLM i j).comp_condExp_comm hY

theorem entry_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {n : Type*} [Fintype n] [DecidableEq n]
    {Y : Ω → Matrix n n ℂ} (hY : Integrable Y μ) (i j : n) :
    Integrable (fun ω => Y ω i j) μ :=
  (entryCLM i j).integrable_comp hY

/-- `matrixCondExp` (entrywise) agrees a.e. with the Bochner conditional expectation. -/
theorem matrixCondExp_ae_eq {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {N : ℕ} (μ : Measure Ω) (Y : Ω → CMat (Fin N)) (hY : Integrable Y μ) :
    matrixCondExp μ m Y =ᵐ[μ] μ[Y | m] := by
  have h : ∀ᵐ ω ∂μ, ∀ i j, μ[fun ω => Y ω i j | m] ω = μ[Y | m] ω i j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      (entry_condExp (m := m) hY i j).mono fun ω h => h.symm
  filter_upwards [h] with ω hω
  ext i j
  exact hω i j

theorem matrixCondExp_eq_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (k : ℕ) (Y : Ω → CMat (Fin N)) (hY : Integrable Y μ) :
    matrixCondExp μ (ℱ k) Y =ᵐ[μ] μ[Y | ℱ k] :=
  matrixCondExp_ae_eq (m := ℱ k) μ Y hY

/-- Reindexing as a star-algebra equivalence. -/
def reindexStar {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ :=
  { reindexAlgEquiv ℂ ℂ e with
    map_smul' := fun r A => by ext; simp [reindexAlgEquiv, reindexRingEquiv]
    map_star' := fun A => by
      simp [reindexAlgEquiv, reindexRingEquiv, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_submatrix] }

theorem reindexStar_apply {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (A : Matrix n n ℂ) : reindexStar e A = reindex e e A := rfl

theorem norm_reindex {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (A : Matrix n n ℂ) : ‖reindex e e A‖ = ‖A‖ := by
  rw [← reindexStar_apply]
  exact StarAlgEquiv.norm_map (reindexStar e) A

/-- The S45 matrix concentration (Lemma 5.6) from the trace helpers and Golden–Thompson. -/
theorem matrix_concentration_of (hT : AndersonAC.OpusS45.TraceHelpers)
    (hGT : GoldenThompson) :
    ∃ c > 0, ∀ (n Ω : Type) [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : ℕ → Ω → CMat n) (v : ℕ → Ω → ℝ) (J V a : ℝ),
    0 < J → 0 < V → 0 < a → MatrixDiffHyp μ ℱ Y v J V →
    μ {ω | ∃ N : ℕ, a < ‖partialSum Y N ω‖} ≤
      ENNReal.ofReal (2 * (Fintype.card n : ℝ) *
        Real.exp (-c * min (a^2 / V) (a / J))) := by
  have hGT' : AndersonAC.OpusS45.GTStatement := fun N A B hA hB => hGT N A B hA hB
  obtain ⟨c, hc, hmax⟩ := AndersonAC.OpusS45.maximal_of hGT' hT
  refine ⟨c, hc, ?_⟩
  intro n Ω _ _ mΩ μ _ ℱ Y v J V a hJ hV ha hY
  set e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n with he
  set Y' : ℕ → Ω → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    fun k ω => reindex e e (Y (k + 1) ω) with hY'
  have hcont : Continuous (fun A : Matrix n n ℂ => reindex e e A) :=
    continuous_id.matrix_reindex e e
  have hsq : ∀ k ω, Y' k ω * Y' k ω = reindex e e ((Y (k + 1) ω) ^ 2) := by
    intro k ω
    rw [pow_two]
    simp only [hY', reindex_apply, submatrix_mul_equiv]
  -- entrywise conditional expectations of reindexed matrices
  have hreidx : ∀ (k : ℕ) (Z : Ω → Matrix n n ℂ), Integrable Z μ →
      AndersonAC.Blueprint.matrixCondExp μ (ℱ k) (fun ω => reindex e e (Z ω)) =ᵐ[μ]
        fun ω => reindex e e (μ[Z | ℱ k] ω) := by
    intro k Z hZ
    have h : ∀ᵐ ω ∂μ, ∀ i j : Fin (Fintype.card n),
        μ[fun ω => Z ω (e.symm i) (e.symm j) | ℱ k] ω = μ[Z | ℱ k] ω (e.symm i) (e.symm j) :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
        (entry_condExp (m := ℱ k) hZ (e.symm i) (e.symm j)).mono fun ω h => h.symm
    filter_upwards [h] with ω hω
    ext i j
    exact hω i j
  have hmax' := hmax Ω μ inferInstance (Fintype.card n) ℱ Y' v J V hJ hV
    (fun k => hcont.comp_stronglyMeasurable (hY.adapted (k + 1)))
    (fun k i j => by
      have := entry_integrable (hY.integrable (k + 1)) (e.symm i) (e.symm j)
      simpa [hY', reindex_apply] using this)
    (fun k => by
      filter_upwards [hY.hermitian k, hY.jump k] with ω h1 h2
      refine ⟨?_, ?_⟩
      · simpa [hY', reindex_apply] using h1.submatrix e.symm
      · show ‖reindex e e (Y (k + 1) ω)‖ ≤ J
        rw [norm_reindex]; exact h2)
    (fun k => by
      filter_upwards [hreidx k (Y (k + 1)) (hY.integrable (k + 1)), hY.centered k]
        with ω h1 h2
      show AndersonAC.Blueprint.matrixCondExp μ (ℱ k) (fun ω => reindex e e (Y (k + 1) ω)) ω = 0
      rw [h1, h2]
      simp)
    (fun k => (hY.predictable k).measurable)
    (fun k => by
      have hint : Integrable (fun ω => (Y (k + 1) ω) ^ 2) μ := hY.square_integrable (k + 1)
      have e1 : (fun ω => Y' k ω * Y' k ω) = fun ω => reindex e e ((Y (k + 1) ω) ^ 2) :=
        funext fun ω => hsq k ω
      filter_upwards [hreidx k _ hint, hY.variance k, hY.variance_nonneg k] with ω h1 h2 h3
      refine ⟨h3, ?_⟩
      rw [e1, h1]
      have h2' := Matrix.le_iff.1 h2
      have : ((v k ω : ℂ) • (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) -
          reindex e e (μ[fun ω => (Y (k + 1) ω) ^ 2 | ℱ k] ω)) =
          ((v k ω • (1 : Matrix n n ℂ)) -
            μ[fun ω => (Y (k + 1) ω) ^ 2 | ℱ k] ω).submatrix e.symm e.symm := by
        ext i j
        simp [reindex_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply,
          Complex.real_smul]
      rw [this]
      exact h2'.submatrix e.symm)
    (ae_all_iff.2 hY.total_variance) a ha
  have hset : {ω | ∃ N : ℕ, a < ‖partialSum Y N ω‖} =
      {ω | ∃ N : ℕ, a < AndersonAC.Blueprint.opNorm (∑ k ∈ Finset.range N, Y' k ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun N => ?_
    have hs : (∑ k ∈ Finset.range N, Y' k ω) = reindex e e (partialSum Y N ω) := by
      simp only [hY', partialSum]
      rw [← reindexStar_apply, map_sum]
      rfl
    rw [hs]
    show a < ‖partialSum Y N ω‖ ↔ a < ‖reindex e e (partialSum Y N ω)‖
    rw [norm_reindex]
  rw [hset]
  simpa [Fintype.card_fin] using hmax'

/-- `AndersonAC.S45.concentrationInput` from the trace helpers. -/
theorem concentrationInput_of (hT : AndersonAC.OpusS45.TraceHelpers) (hGT : GoldenThompson) :
    ConcentrationInput :=
  AndersonAC.OpusS45.concentrationInput_of (fun N A B hA hB => hGT N A B hA hB) hT

theorem deletionInput_proof : DeletionInput := AndersonAC.OpusS45.deletion_proof

end AndersonAC.AgentS45
