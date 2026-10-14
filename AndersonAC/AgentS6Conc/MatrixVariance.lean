import AndersonAC.AgentS6Conc.DilationLinear
import AndersonAC.AgentS6Conc.Variance
import AndersonAC.S45.MatrixConcentrationProof

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS6Conc

open AndersonAC.S45

/-- Conditional second moments of the vector dilation are bounded by the
scalar predictable variance in Loewner order. -/
theorem vectorDilation_condVariance {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {D : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (Y : Ω → EuclideanSpace ℂ (Fin D))
    (v : Ω → ℝ) (k : ℕ) (J : ℝ) (hJ : 0 < J)
    (hYint : Integrable Y μ)
    (hYsm : StronglyMeasurable[F (k + 1)] Y)
    (hYbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ J)
    (hvar : ∀ᵐ ω ∂μ, μ[(fun ω => ‖Y ω‖ ^ 2) | F k] ω ≤ v ω)
    (hvpos : ∀ ω, 0 ≤ v ω) :
    ∀ᵐ ω ∂μ,
      0 ≤ v ω ∧
        (((v ω : ℂ) • (1 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D)))
          (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ) -
            matrixCondExp μ (F k) (fun ω => vectorDilation (Y ω) * vectorDilation (Y ω)) ω).PosSemidef) := by
  let M := Fin (Fintype.card (Unit ⊕ Fin D))
  let Z : Ω → Matrix M M ℂ := fun ω => vectorDilation (Y ω)
  let q : Ω → ℝ := fun ω => ‖Y ω‖ ^ 2
  let Q : Ω → Matrix M M ℂ := fun ω => scalarIdentityCLM M (q ω)
  let S : Ω → Matrix M M ℂ := fun ω => Z ω * Z ω
  let G : Ω → Matrix M M ℂ := fun ω => Q ω - S ω
  have hYsm' : StronglyMeasurable (Y) := hYsm.mono (F.le (k + 1))
  have hZsm : StronglyMeasurable Z := by
    exact (vectorDilationCLM D).continuous.comp_stronglyMeasurable hYsm'
  have hZint : Integrable Z μ := by
    exact (vectorDilationCLM D).integrable_comp hYint
  have hqsm : StronglyMeasurable q := by
    exact (continuous_norm.pow 2).comp_stronglyMeasurable hYsm'
  have hqbound : ∀ᵐ ω ∂μ, ‖q ω‖ ≤ J ^ 2 := by
    filter_upwards [hYbound] with ω hω
    dsimp [q]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hJ.le).2 hω
  have hqint : Integrable q μ := by
    apply Integrable.of_bound hqsm.aestronglyMeasurable (J ^ 2)
    exact hqbound
  have hQsm : StronglyMeasurable Q := by
    exact (scalarIdentityCLM M).continuous.comp_stronglyMeasurable hqsm
  have hQint : Integrable Q μ := by
    exact (scalarIdentityCLM M).integrable_comp hqint
  have hSsm : StronglyMeasurable S := hZsm.mul hZsm
  have hSbound : ∀ᵐ ω ∂μ, ‖S ω‖ ≤ J ^ 2 := by
    filter_upwards [hYbound] with ω hω
    dsimp [S, Z]
    calc
      ‖vectorDilation (Y ω) * vectorDilation (Y ω)‖ ≤
          ‖vectorDilation (Y ω)‖ * ‖vectorDilation (Y ω)‖ := norm_mul_le _ _
      _ ≤ J * J := mul_le_mul (by rw [vectorDilation_norm]; exact hω)
        (by rw [vectorDilation_norm]; exact hω) (norm_nonneg _) hJ.le
      _ = J ^ 2 := by ring
  have hSint : Integrable S μ := by
    exact Integrable.of_bound hSsm.aestronglyMeasurable (J ^ 2) hSbound
  have hGint : Integrable G μ := by
    exact hQint.sub hSint
  have hGpos : ∀ ω, (G ω).PosSemidef := by
    intro ω
    have h := vectorDilation_square_le (Y ω)
    rw [Matrix.le_iff] at h
    simpa [G, Q, S, Z, q, scalarIdentityCLM_apply, pow_two,
      RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_mul] using h
  have hGce := condExp_posSemidef_ae (m := F k) (F.le k) G hGint
    (ae_of_all μ hGpos)
  have hGsub : μ[G | F k] =ᵐ[μ] μ[Q | F k] - μ[S | F k] :=
    condExp_sub hQint hSint (F k)
  have hQce : μ[Q | F k] =ᵐ[μ]
      (fun ω => scalarIdentityCLM M (μ[q | F k] ω)) := by
    have htmp := (scalarIdentityCLM M).comp_condExp_comm (m := F k) hqint
    simpa [Q, Function.comp_def] using htmp.symm
  have hSQce := AndersonAC.AgentS45.matrixCondExp_ae_eq (m := F k) μ S hSint
  have hOrder1 : ∀ᵐ ω ∂μ,
      matrixCondExp μ (F k) S ω ≤ scalarIdentityCLM M (μ[q | F k] ω) := by
    filter_upwards [hGce, hGsub, hQce, hSQce] with ω hG hsub hq hSQ
    rw [hSQ]
    have hEq : μ[G | F k] ω =
        scalarIdentityCLM M (μ[q | F k] ω) - μ[S | F k] ω := by
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [hq]
    rw [Matrix.le_iff]
    simpa only [← hEq] using hG
  have hOrder2 : ∀ᵐ ω ∂μ,
      scalarIdentityCLM M (μ[q | F k] ω) ≤ (v ω : ℂ) • (1 : Matrix M M ℂ) := by
    filter_upwards [hvar] with ω hω
    rw [Matrix.le_iff]
    have hpsd := scalarIdentity_posSemidef (n := M) (sub_nonneg.mpr hω)
    simpa [scalarIdentityCLM_apply, sub_smul] using hpsd
  have hOrder : ∀ᵐ ω ∂μ,
      matrixCondExp μ (F k) S ω ≤ (v ω : ℂ) • (1 : Matrix M M ℂ) := by
    filter_upwards [hOrder1, hOrder2] with ω h1 h2
    exact h1.trans h2
  filter_upwards [hOrder] with ω hω
  refine ⟨hvpos ω, ?_⟩
  rw [Matrix.le_iff] at hω
  simpa [S, Z] using hω

end AndersonAC.AgentS6Conc

end
