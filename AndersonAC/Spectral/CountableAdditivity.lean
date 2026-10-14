import AndersonAC.Spectral.ProjValMeasure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Normed.Group.InfiniteSum

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology
open ContinuousLinearMap

namespace AndersonAC.Spectral

private theorem norm_sq_sum_pairwise_orthogonal
    {ι : Type*} [DecidableEq ι] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (s : Finset ι) (f : ι → H)
    (horth : Pairwise fun i j => inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hinner : inner ℂ (∑ i ∈ s, f i) (∑ j ∈ s, f j) =
      ∑ i ∈ s, inner ℂ (f i) (f i) := by
    rw [sum_inner]
    simp_rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      exact horth (Ne.symm hji)
    · intro hnot
      exact (hnot hi).elim
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem proj_iUnion_hasSum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : TauCeti.ProjValMeasure H) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) (v : H) :
    HasSum (fun n => P.proj (B n) (hB n) v)
      (P.proj (⋃ n, B n) (MeasurableSet.iUnion hB) v) := by
  classical
  let μ : Measure ℝ := P.diag v
  haveI : IsFiniteMeasure μ := P.diag_finite v
  let U : Set ℝ := ⋃ n, B n
  let hU : MeasurableSet U := MeasurableSet.iUnion hB
  let Q : H →L[ℂ] H := P.proj U hU
  let f : ℕ → H := fun n => P.proj (B n) (hB n) v
  have horth : Pairwise fun i j => inner ℂ (f i) (f j) = 0 := by
    intro i j hij
    have hset : B i ∩ B j = ∅ := Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)
    let piOp : H →L[ℂ] H := P.proj (B i) (hB i)
    let pjOp : H →L[ℂ] H := P.proj (B j) (hB j)
    have hmul : piOp * pjOp = 0 := by
      calc
        piOp * pjOp = P.proj (B i ∩ B j) ((hB i).inter (hB j)) := P.proj_inter (B i) (B j) (hB i) (hB j)
        _ = P.proj ∅ MeasurableSet.empty := P.proj_congr hset ((hB i).inter (hB j)) MeasurableSet.empty
        _ = 0 := P.proj_empty
    have hPi : IsSelfAdjoint piOp := P.isSelfAdjoint_proj (B i) (hB i)
    calc
      inner ℂ (f i) (f j) = inner ℂ (piOp v) (pjOp v) := rfl
      _ = inner ℂ ((ContinuousLinearMap.adjoint piOp) v) (pjOp v) := by rw [hPi.adjoint_eq]
      _ = inner ℂ v (piOp (pjOp v)) := by rw [adjoint_inner_left]
      _ = 0 := by
        rw [← mul_apply_eq_comp, hmul]
        simp
  have hnormTerm (n : ℕ) : ‖f n‖ ^ 2 = (μ (B n)).toReal := by
    exact P.norm_sq_proj_apply (B n) (hB n) v
  have hnorms : Summable fun n => ‖f n‖ ^ 2 := by
    simpa only [measureReal_def, hnormTerm] using
      (MeasureTheory.summable_measure_toReal (μ := μ) hB hdisj)
  have hsummable : Summable f := by
    apply (summable_iff_vanishing_norm).2
    intro ε hε
    obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm).1 hnorms (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨s, fun t hts => ?_⟩
    have htail : ‖∑ i ∈ t, ‖f i‖ ^ 2‖ < ε ^ 2 := hs t hts
    have hnonneg : 0 ≤ ∑ i ∈ t, ‖f i‖ ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at htail
    have hsq := norm_sq_sum_pairwise_orthogonal t f horth
    rw [← hsq] at htail
    nlinarith [norm_nonneg (∑ i ∈ t, f i)]
  let partials : ℕ → H := fun n => ∑ i ∈ Finset.range n, f i
  have hQPi (n : ℕ) : Q * P.proj (B n) (hB n) = P.proj (B n) (hB n) := by
    have hsub : B n ⊆ U := Set.subset_iUnion B n
    have hset : U ∩ B n = B n := by
      ext x
      constructor
      · exact fun hx => hx.2
      · intro hx
        exact ⟨hsub hx, hx⟩
    calc
      Q * P.proj (B n) (hB n) = P.proj (U ∩ B n) (hU.inter (hB n)) := P.proj_inter U (B n) hU (hB n)
      _ = P.proj (B n) (hB n) := P.proj_congr hset (hU.inter (hB n)) (hB n)
  have hQf (n : ℕ) : inner ℂ (Q v) (f n) = ((μ (B n)).toReal : ℂ) := by
    let Pn := P.proj (B n) (hB n)
    have hQ : IsSelfAdjoint Q := P.isSelfAdjoint_proj U hU
    calc
      inner ℂ (Q v) (Pn v) = inner ℂ ((ContinuousLinearMap.adjoint Q) v) (Pn v) := by rw [hQ.adjoint_eq]
      _ = inner ℂ v (Q (Pn v)) := by rw [adjoint_inner_left]
      _ = inner ℂ v (Pn v) := by rw [← mul_apply_eq_comp, hQPi n]
      _ = ((μ (B n)).toReal : ℂ) := P.inner_proj (B n) (hB n) v
  have hfnQ (n : ℕ) : inner ℂ (f n) (Q v) = ((μ (B n)).toReal : ℂ) := by
    rw [← inner_conj_symm, hQf, Complex.conj_ofReal]
  have hQnorm : ‖Q v‖ ^ 2 = (μ U).toReal := P.norm_sq_proj_apply U hU v
  have hreal_sum : (μ U).toReal = ∑' n, (μ (B n)).toReal := by
    rw [MeasureTheory.measure_iUnion hdisj hB]
    exact ENNReal.tsum_toReal_eq fun n => measure_ne_top _ _
  have hreal_hasSum : HasSum (fun n => (μ (B n)).toReal) (μ U).toReal := by
    rw [hreal_sum]
    exact (MeasureTheory.summable_measure_toReal (μ := μ) hB hdisj).hasSum
  have hpartialReal : Tendsto (fun n => ∑ i ∈ Finset.range n, (μ (B i)).toReal)
      atTop (𝓝 (μ U).toReal) := by
    simpa using hreal_hasSum.tendsto_sum_nat
  have hgap : Tendsto
      (fun n => (μ U).toReal - ∑ i ∈ Finset.range n, (μ (B i)).toReal)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (μ U).toReal) atTop (𝓝 (μ U).toReal) := tendsto_const_nhds
    simpa using hconst.sub hpartialReal
  have hnormdiff (n : ℕ) :
      ‖partials n - Q v‖ ^ 2 = (μ U).toReal - ∑ i ∈ Finset.range n, (μ (B i)).toReal := by
    let s : H := partials n
    have hsumNorm : ‖s‖ ^ 2 = ∑ i ∈ Finset.range n, (μ (B i)).toReal := by
      rw [norm_sq_sum_pairwise_orthogonal (Finset.range n) f horth]
      simp_rw [hnormTerm]
    have hsumQ : inner ℂ s (Q v) = ∑ i ∈ Finset.range n, ((μ (B i)).toReal : ℂ) := by
      simp only [s, partials, sum_inner]
      simp_rw [hfnQ]
    have hQsum : inner ℂ (Q v) s = ∑ i ∈ Finset.range n, ((μ (B i)).toReal : ℂ) := by
      simp only [s, partials, inner_sum]
      simp_rw [hQf]
    have hinnerdiff : inner ℂ (s - Q v) (s - Q v) =
        ((‖s‖ ^ 2 : ℝ) : ℂ) -
          (∑ i ∈ Finset.range n, ((μ (B i)).toReal : ℂ)) -
          ((∑ i ∈ Finset.range n, ((μ (B i)).toReal : ℂ)) - ((‖Q v‖ ^ 2 : ℝ) : ℂ)) := by
      simp only [inner_sub_left, inner_sub_right]
      rw [hsumQ, hQsum, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have hsumRe : ∀ t : Finset ℕ,
        (∑ i ∈ t, ((μ (B i)).toReal : ℂ)).re = ∑ i ∈ t, (μ (B i)).toReal := by
      intro t
      rw [← Complex.reCLM_apply, map_sum]
      simp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinnerdiff, hsumNorm, hQnorm]
    rw [RCLike.re_eq_complex_re]
    simp only [Complex.sub_re, Complex.ofReal_re, hsumRe]
    ring
  have hnormsq : Tendsto (fun n => ‖partials n - Q v‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnormdiff] using hgap
  have hnorm : Tendsto (fun n => ‖partials n - Q v‖) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (‖partials n - Q v‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hnormsq
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hpartial : Tendsto partials atTop (𝓝 (Q v)) := by
    exact (tendsto_iff_dist_tendsto_zero).2 (by simpa [dist_eq_norm] using hnorm)
  have htsum := hsummable.hasSum.tendsto_sum_nat
  have heq : (∑' n, f n) = Q v := tendsto_nhds_unique htsum hpartial
  have hseries : HasSum f (∑' n, f n) := hsummable.hasSum
  rw [heq] at hseries
  exact hseries

end AndersonAC.Spectral
