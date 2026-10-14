import AndersonAC.S6.Definitions
import AndersonAC.S45.Definitions

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder ENNReal NNReal

namespace AndersonAC.AgentS6Conc

def vecColumn {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) : Matrix (Fin D) Unit ℂ :=
  fun i _ => y.ofLp i

theorem vecColumn_norm {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) :
    ‖vecColumn y‖ = ‖y‖ := by
  rw [Matrix.l2_opNorm_def]
  let T : EuclideanSpace ℂ Unit →L[ℂ] EuclideanSpace ℂ (Fin D) :=
    (Matrix.toEuclideanLin (vecColumn y)).toContinuousLinearMap
  change ‖T‖ = ‖y‖
  have hTx (x : EuclideanSpace ℂ Unit) : T x = (x.ofLp () : ℂ) • y := by
    ext i
    simp [T, vecColumn, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec]
    ring
  have hxnorm (x : EuclideanSpace ℂ Unit) : ‖x‖ = ‖x.ofLp ()‖ := by
    simp [EuclideanSpace.norm_eq]
  have hnormTx (x : EuclideanSpace ℂ Unit) : ‖T x‖ = ‖x.ofLp ()‖ * ‖y‖ := by
    rw [hTx, norm_smul]
  have hupper : ‖T‖ ≤ ‖y‖ := by
    apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg y)
    intro x
    rw [hnormTx x, hxnorm x, mul_comm]
  let e1 : EuclideanSpace ℂ Unit := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have he1 : ‖e1‖ = 1 := by simp [e1, EuclideanSpace.norm_eq]
  have he1coord : e1.ofLp () = 1 := rfl
  have hlower : ‖y‖ ≤ ‖T‖ := by
    have hval : ‖T e1‖ = ‖y‖ := by rw [hnormTx, he1coord, norm_one, one_mul]
    rw [← hval]
    calc
      ‖T e1‖ ≤ ‖T‖ * ‖e1‖ := T.le_opNorm e1
      _ = ‖T‖ := by rw [he1, mul_one]
  exact le_antisymm hupper hlower

/-- Conditional expectation is unchanged on a positive scalar multiple of the measure.
The equality is understood almost everywhere for the scaled measure. -/
theorem condExp_smulMeasure_ae_eq {Ω E : Type*} {m mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {f : Ω → E} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {c : ℝ≥0} (hf : Integrable f μ) :
    (c • μ)[f | m] =ᵐ[c • μ] μ[f | m] := by
  let ν : Measure Ω := c • μ
  have hνf : Integrable f ν := by simpa [ν] using hf.smul_measure_nnreal
  have hνg : Integrable (μ[f | m]) ν := by
    simpa [ν] using (integrable_condExp : Integrable (μ[f | m]) μ).smul_measure_nnreal
  have htrim : ν.trim hm = c • μ.trim hm := by
    rw [show ν = c • μ from rfl]
    refine @Measure.ext Ω m _ _ (fun s hs => ?_)
    simp [trim_measurableSet_eq hm hs]
  have hνσ : SigmaFinite (ν.trim hm) := by rw [htrim]; infer_instance
  letI := hνσ
  have hEq : ∀ s, @MeasurableSet Ω m s → ν s < ∞ →
      ∫ x in s, μ[f | m] x ∂ν = ∫ x in s, f x ∂ν := by
    intro s hs hsTop
    calc
      ∫ x in s, μ[f | m] x ∂ν = (c : ℝ) • ∫ x in s, μ[f | m] x ∂μ := by
        change ∫ x, μ[f | m] x ∂ν.restrict s = _
        rw [show ν = c • μ from rfl, Measure.restrict_smul, integral_smul_nnreal_measure]
        simp [NNReal.smul_def]
      _ = (c : ℝ) • ∫ x in s, f x ∂μ := by rw [setIntegral_condExp hm hf hs]
      _ = ∫ x in s, f x ∂ν := by
        change _ = ∫ x, f x ∂ν.restrict s
        rw [show ν = c • μ from rfl, Measure.restrict_smul, integral_smul_nnreal_measure]
        simp [NNReal.smul_def]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hνf
    (fun s hs hsTop => hνg.integrableOn)
    hEq stronglyMeasurable_condExp.aestronglyMeasurable).symm

end AndersonAC.AgentS6Conc

end
