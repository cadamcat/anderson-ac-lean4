import AndersonAC.S6.Definitions

/-! Concrete Euclidean projection identities for the full scattering range. -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem matrix_single_apply (A : Matrix R R ℂ) (i j : R) :
    (Matrix.toEuclideanLin A (EuclideanSpace.single i 1)) j = A j i := by
  change (A *ᵥ Pi.single i 1) j = A j i
  simp

theorem projection_apply (C : Matrix R B ℂ) (v : EuclideanSpace ℂ R) :
    Matrix.toEuclideanLin (AndersonAC.S6.rangeProjection C) v =
      (AndersonAC.S6.matrixRange C).starProjection v := by
  change ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
    (AndersonAC.S6.rangeProjection C)) v = _
  simp [AndersonAC.S6.rangeProjection]

theorem projection_weight_eq (C : Matrix R B ℂ) (i : R) :
    AndersonAC.S6.projectionWeight C i =
      ‖(AndersonAC.S6.matrixRange C).starProjection (EuclideanSpace.single i 1)‖ ^ 2 := by
  let e : EuclideanSpace ℂ R := EuclideanSpace.single i 1
  let K := AndersonAC.S6.matrixRange C
  have hcoord : AndersonAC.S6.projectionWeight C i = (K.starProjection e i).re := by
    rw [← projection_apply]
    exact congrArg Complex.re (matrix_single_apply (AndersonAC.S6.rangeProjection C) i i).symm
  calc
    AndersonAC.S6.projectionWeight C i = (inner ℂ e (K.starProjection e)).re := by
      simpa [e, EuclideanSpace.inner_single_left] using hcoord
    _ = ‖K.starProjection e‖ ^ 2 := by
      rw [← K.inner_starProjection_left_eq_right]
      exact K.re_inner_starProjection_eq_normSq e

end AndersonAC.SolS6

namespace AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem projection_coordinate (C : Matrix R B ℂ) (i : R) :
    0 ≤ projectionWeight C i ∧
    (∀ v ∈ matrixRange C, ‖v i‖ ^ 2 ≤ projectionWeight C i * ‖v‖ ^ 2) ∧
    (0 < projectionWeight C i → ∃ v ∈ matrixRange C,
      ‖v‖ = 1 ∧ ‖v i‖ ^ 2 = projectionWeight C i) := by
  let K := matrixRange C
  let e : EuclideanSpace ℂ R := EuclideanSpace.single i 1
  let u := K.starProjection e
  have hweight : projectionWeight C i = ‖u‖ ^ 2 :=
    AndersonAC.SolS6.projection_weight_eq C i
  have humem : u ∈ K := K.starProjection_apply_mem e
  refine ⟨by rw [hweight]; positivity, ?_, ?_⟩
  · intro v hv
    have hvfixed : K.starProjection v = v := K.starProjection_eq_self_iff.mpr hv
    have hinner : inner ℂ u v = v i := by
      change inner ℂ (K.starProjection e) v = v i
      rw [K.inner_starProjection_left_eq_right, hvfixed]
      simp [e, EuclideanSpace.inner_single_left]
    have hcs := norm_inner_le_norm (𝕜 := ℂ) u v
    rw [hinner] at hcs
    have hsquare := mul_self_le_mul_self (norm_nonneg (v i)) hcs
    rw [hweight]
    nlinarith [hsquare]
  · intro hpos
    have hunorm : 0 < ‖u‖ := by rw [hweight] at hpos; nlinarith [norm_nonneg u]
    have hune : ‖u‖ ≠ 0 := ne_of_gt hunorm
    let v : EuclideanSpace ℂ R := ((‖u‖ : ℂ)⁻¹) • u
    have hufixed : K.starProjection u = u := K.starProjection_eq_self_iff.mpr humem
    have hui : u i = (‖u‖ : ℂ) ^ 2 := by
      calc
        u i = inner ℂ e u := by simp [e, EuclideanSpace.inner_single_left]
        _ = inner ℂ e (K.starProjection u) := by rw [hufixed]
        _ = inner ℂ (K.starProjection e) u := (K.inner_starProjection_left_eq_right e u).symm
        _ = (‖u‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K u
    refine ⟨v, K.smul_mem _ humem, ?_, ?_⟩
    · simp [v, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg u), hune]
    · change ‖(‖u‖ : ℂ)⁻¹ * u i‖ ^ 2 = _
      rw [hui, hweight, norm_mul, norm_inv, norm_pow]
      simp only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg u)]
      field_simp

end AndersonAC.S6

#print axioms AndersonAC.SolS6.projection_weight_eq
#print axioms AndersonAC.S6.projection_coordinate
