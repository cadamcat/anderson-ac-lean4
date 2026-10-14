import Mathlib
import AndersonAC.S9Fin.Core
import AndersonAC.S9Fin.NormStatements

noncomputable section

open AndersonAC.S9
open scoped Matrix ComplexOrder ComplexConjugate InnerProduct

namespace AndersonAC.SolS9

universe u

/-- Rank bounds Hilbert–Schmidt mass by rank times squared Euclidean operator
norm, via the eigenvalues of `Gᴴ * G`. -/
theorem rankHilbertSchmidt_proof : RankHilbertSchmidtStatement.{u} := by
  intro n _ _ G
  classical
  have hHerm : (Gᴴ * G).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self G
  -- Hilbert–Schmidt norm squared equals the sum of eigenvalues of `Gᴴ * G`.
  have hHS : hilbertSchmidtSq G = ∑ i, hHerm.eigenvalues i := by
    have htrace : (Gᴴ * G).trace = ∑ i, ((hHerm.eigenvalues i : ℝ) : ℂ) :=
      hHerm.trace_eq_sum_eigenvalues
    have hterm : ∀ i j : n,
        RCLike.re (star (G j i) * G j i) = ‖G j i‖ ^ 2 := by
      intro i j
      rw [← starRingEnd_apply, RCLike.conj_mul, RCLike.re_ofReal_pow]
    have hre : hilbertSchmidtSq G = RCLike.re (Gᴴ * G).trace := by
      have h1 : (Gᴴ * G).trace = ∑ i, ∑ j, (star (G j i) * G j i) := by
        unfold Matrix.trace
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [Matrix.conjTranspose_apply]
      rw [h1, ← RCLike.reLm_coe, map_sum]
      unfold hilbertSchmidtSq columnNormSq
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [RCLike.reLm_coe]
      exact (hterm i j).symm
    rw [hre, htrace, ← RCLike.reLm_coe, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [RCLike.reLm_coe]
  -- Each eigenvalue lies in `[0, ‖G‖²]`.
  have hle : ∀ i, hHerm.eigenvalues i ≤ matrixOpNorm G ^ 2 := by
    intro i
    have hnorm : matrixOpNorm G
        = ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G‖ := rfl
    rw [hnorm]
    have hv : ‖hHerm.eigenvectorBasis i‖ = 1 :=
      hHerm.eigenvectorBasis.orthonormal.1 i
    have hmul := hHerm.mulVec_eigenvectorBasis i
    have hTv : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (Gᴴ * G)
          (hHerm.eigenvectorBasis i)
        = (hHerm.eigenvalues i) • (hHerm.eigenvectorBasis i) := by
      rw [Matrix.toEuclideanCLM_toLp, hmul, WithLp.toLp_smul]
    have hTA : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (Gᴴ * G)
        = ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G)†
          ∘L ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G) := by
      have h1 : Gᴴ = star G := rfl
      rw [h1, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.mul_def]
    have hnorm2 : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G
          (hHerm.eigenvectorBasis i)‖ ^ 2 = hHerm.eigenvalues i := by
      have h1 := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G)
        (hHerm.eigenvectorBasis i)
      rw [← hTA, hTv] at h1
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) _ _] at h1
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
      simp [hv] at h1
      exact h1
    rw [← hnorm2]
    calc ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G
            (hHerm.eigenvectorBasis i)‖ ^ 2
        ≤ (‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G‖
            * ‖hHerm.eigenvectorBasis i‖) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _) _ 2
          exact ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G).le_opNorm _
      _ = ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) G‖ ^ 2 := by
          simp [hv]
  -- Sum over nonzero eigenvalues, bounded by rank times `‖G‖²`.
  have hrank : (Gᴴ * G).rank = G.rank := Matrix.rank_conjTranspose_mul_self G
  have hrank2 : (Gᴴ * G).rank = Fintype.card {i // hHerm.eigenvalues i ≠ 0} :=
    hHerm.rank_eq_card_non_zero_eigs
  have hsum : (∑ i, hHerm.eigenvalues i)
      = ∑ i ∈ Finset.univ.filter (fun i => hHerm.eigenvalues i ≠ 0),
        hHerm.eigenvalues i := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _ hx
    simp at hx
    exact hx
  have hle_sum : ∑ i ∈ Finset.univ.filter
        (fun i => hHerm.eigenvalues i ≠ 0), hHerm.eigenvalues i
      ≤ ((Finset.univ.filter (fun i => hHerm.eigenvalues i ≠ 0)).card : ℝ)
        * matrixOpNorm G ^ 2 := by
    have hle' := Finset.sum_le_card_nsmul
      (Finset.univ.filter (fun i => hHerm.eigenvalues i ≠ 0))
      (fun i => hHerm.eigenvalues i) (matrixOpNorm G ^ 2)
      (fun i _ => hle i)
    rwa [nsmul_eq_mul] at hle'
  have hcard : (Finset.univ.filter
      (fun i => hHerm.eigenvalues i ≠ 0)).card = Matrix.rank G := by
    rw [← hrank, hrank2, Fintype.card_subtype]
  rw [hHS, hsum, ← hcard]
  exact hle_sum

#print axioms rankHilbertSchmidt_proof

end AndersonAC.SolS9
