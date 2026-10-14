import Mathlib
import AndersonAC.S9Fin.Core
import AndersonAC.S9Fin.ProbabilityStatements
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

noncomputable section

open MeasureTheory Topology Filter
open AndersonAC.S9
open scoped Matrix.Norms.L2Operator

namespace AndersonAC.SolS9

universe u v

variable {n : Type u} [Fintype n] [DecidableEq n]

private lemma windowRank_eq_card (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E δ : ℝ) :
    windowRank H hH E δ =
      (Finset.univ.filter fun i => |hH.eigenvalues i - E| ≤ δ).card := by
  classical
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal
    (fun i => if |hH.eigenvalues i - E| ≤ δ then (1 : ℂ) else 0)
  have hUU : star U * U = 1 := by
    simp [U]
  have hrank : Matrix.rank (U * D * star U) = Matrix.rank D := by
    apply le_antisymm
    · calc
        Matrix.rank ((U * D) * star U) ≤ Matrix.rank (U * D) :=
          Matrix.rank_mul_le_left _ _
        _ ≤ Matrix.rank D := Matrix.rank_mul_le_right _ _
    · have hconj : star U * (U * D * star U) * U = D := by
        calc
          star U * (U * D * star U) * U = (star U * U) * D * (star U * U) := by
            simp only [Matrix.mul_assoc]
          _ = D := by simp [hUU]
      calc
        Matrix.rank D = Matrix.rank (star U * (U * D * star U) * U) :=
          congrArg Matrix.rank hconj.symm
        _ ≤
            Matrix.rank (star U * (U * D * star U)) := Matrix.rank_mul_le_left _ _
        _ ≤ Matrix.rank (U * D * star U) := Matrix.rank_mul_le_right _ _
  unfold windowRank windowProjection
  change Matrix.rank (U * D * star U) = _
  rw [hrank, Matrix.rank_diagonal]
  simp [Fintype.card_subtype]

private lemma trace_cfc_re_eq_sum (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (f : ℝ → ℝ) (_hf : Continuous f) :
    ((cfc f H).trace).re = ∑ i, f (hH.eigenvalues i) := by
  rw [hH.cfc_eq f]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (f (hH.eigenvalues i) : ℂ))
  have hUU : star U * U = 1 := by
    simp [U]
  have htrace : (U * D * star U).trace = D.trace := by
    rw [Matrix.trace_mul_cycle]
    simp [U, hUU]
  change (U * D * star U).trace.re = _
  rw [htrace, Matrix.trace_diagonal]
  simp [Complex.ofReal_re]

private def intervalApprox (E δ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (1 + (k : ℝ) * max 0 (|x - E| - δ))⁻¹

private lemma continuous_intervalApprox (E δ : ℝ) (k : ℕ) :
    Continuous (intervalApprox E δ k) := by
  unfold intervalApprox
  have hc : Continuous (fun x : ℝ => 1 + (k : ℝ) * max 0 (|x - E| - δ)) := by
    fun_prop
  apply hc.inv₀
  intro x
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : 0 ≤ max 0 (|x - E| - δ) := le_max_left _ _
  have hmul := mul_nonneg hk hd
  linarith

private lemma tendsto_intervalApprox (E δ x : ℝ) :
    Tendsto (fun k : ℕ => intervalApprox E δ k x) atTop
      (𝓝 (if |x - E| ≤ δ then 1 else 0)) := by
  by_cases h : |x - E| ≤ δ
  · have hd : max 0 (|x - E| - δ) = 0 := by
      rw [max_eq_left]
      linarith
    simp [intervalApprox, h, hd]
  · have hδ : δ < |x - E| := lt_of_not_ge h
    have hd0 : 0 < |x - E| - δ := by linarith
    let d : ℝ := max 0 (|x - E| - δ)
    have hd : 0 < d := by
      dsimp [d]
      rw [max_eq_right hd0.le]
      exact hd0
    have ht : Tendsto (fun k : ℕ => 1 + (k : ℝ) * d) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro b
      obtain ⟨N, hN⟩ := exists_nat_gt ((b - 1) / d)
      filter_upwards [eventually_ge_atTop N] with k hk
      have hN' : (b - 1) / d < (N : ℝ) := by exact_mod_cast hN
      have hk' : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hmul : b - 1 < (N : ℝ) * d := (div_lt_iff₀ hd).mp hN'
      have hmul' : (N : ℝ) * d ≤ (k : ℝ) * d :=
        mul_le_mul_of_nonneg_right hk' hd.le
      exact le_of_lt (by linarith)
    have hinv := tendsto_inv_atTop_zero.comp ht
    have hinv' : Tendsto (fun k : ℕ => (1 + (k : ℝ) * d)⁻¹) atTop (𝓝 0) := by
      change Tendsto ((fun r : ℝ => r⁻¹) ∘ (fun k : ℕ => 1 + (k : ℝ) * d))
        atTop (𝓝 0)
      exact hinv
    have heq : (fun k : ℕ => intervalApprox E δ k x) =
        fun k : ℕ => (1 + (k : ℝ) * d)⁻¹ := by
      funext k
      simp [intervalApprox, d]
    rw [heq]
    simpa [h] using hinv'

private lemma trace_cfc_intervalApprox_tendsto (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (E δ : ℝ) :
    Tendsto
      (fun k : ℕ =>
        ((cfc (intervalApprox E δ k) H).trace).re)
      atTop (𝓝 (windowRank H hH E δ : ℝ)) := by
  rw [windowRank_eq_card]
  have hsum : ∀ k : ℕ,
      ((cfc (intervalApprox E δ k) H).trace).re =
        ∑ i, intervalApprox E δ k (hH.eigenvalues i) := by
    intro k
    exact trace_cfc_re_eq_sum H hH _ (continuous_intervalApprox E δ k)
  simp_rw [hsum]
  have hsummable : Tendsto
      (fun k : ℕ => ∑ i, intervalApprox E δ k (hH.eigenvalues i))
      atTop (𝓝 (∑ i, if |hH.eigenvalues i - E| ≤ δ then (1 : ℝ) else 0)) := by
    apply tendsto_finsetSum Finset.univ
    intro i hi
    exact tendsto_intervalApprox E δ (hH.eigenvalues i)
  convert hsummable using 1
  simp

private lemma measurable_trace_cfc {Ξ : Type v} [MeasurableSpace Ξ]
    (H : Ξ → Matrix n n ℂ) (hH : ∀ ξ, (H ξ).IsHermitian)
    (hHm : Measurable H) (f : ℝ → ℝ) (hf : Continuous f) :
    Measurable (fun ξ => ((cfc f (H ξ)).trace).re) := by
  let HermitianMatrix := {A : Matrix n n ℂ // A.IsHermitian}
  let hs : Set (Matrix n n ℂ) := {A | IsSelfAdjoint A}
  have hcfc : ContinuousOn (fun A : Matrix n n ℂ => cfc f A) hs := by
    refine ContinuousOn.cfc_of_mem_nhdsSet (𝕜 := ℝ) f (s := Set.univ)
      (a := fun A : Matrix n n ℂ => A) (t := hs)
      univ_mem continuousOn_id ?_ hf.continuousOn
    intro A hA
    exact hA
  have hcfcSub : Continuous (fun A : HermitianMatrix => cfc f (A : Matrix n n ℂ)) := by
    apply hcfc.comp_continuous continuous_subtype_val
    intro A
    exact A.property
  have htrace : Continuous (fun A : Matrix n n ℂ => (A.trace).re) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  have hreadout : Continuous
      (fun A : HermitianMatrix => ((cfc f (A : Matrix n n ℂ)).trace).re) :=
    htrace.comp hcfcSub
  let H' : Ξ → HermitianMatrix := fun ξ => ⟨H ξ, hH ξ⟩
  have hH'm : Measurable H' := hHm.subtype_mk
  exact hreadout.measurable.comp hH'm

theorem windowRankMeasurable_proof : WindowRankMeasurableStatement.{u, v} := by
  intro n _ _ Ξ _ H hH hHm E δ
  let f : ℕ → Ξ → ℝ := fun k ξ => ((cfc (intervalApprox E δ k) (H ξ)).trace).re
  have hf : ∀ k, Measurable (f k) := by
    intro k
    exact measurable_trace_cfc H hH hHm (intervalApprox E δ k)
      (continuous_intervalApprox E δ k)
  have hlim : ∀ ξ, Tendsto (fun k => f k ξ) atTop
      (𝓝 (windowRank (H ξ) (hH ξ) E δ : ℝ)) := by
    intro ξ
    exact trace_cfc_intervalApprox_tendsto (H ξ) (hH ξ) E δ
  exact measurable_of_tendsto_metrizable' atTop hf (tendsto_pi_nhds.2 hlim)

#print axioms windowRankMeasurable_proof

end AndersonAC.SolS9
