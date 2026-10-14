import AndersonAC.S78.Definitions

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

private theorem weighted_cauchy_sum {ι : Type} (s : Finset ι)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, a i * b i ^ 2) := by
  classical
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (a i) * b i)
  have hleft :
      (∑ i ∈ s, Real.sqrt (a i) * (Real.sqrt (a i) * b i)) =
        ∑ i ∈ s, a i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      Real.sqrt (a i) * (Real.sqrt (a i) * b i) =
          (Real.sqrt (a i)) ^ 2 * b i := by ring
      _ = a i * b i := by rw [Real.sq_sqrt (ha i hi)]
  have hfirst :
      (∑ i ∈ s, Real.sqrt (a i) ^ 2) = ∑ i ∈ s, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.sq_sqrt (ha i hi)]
  have hsecond :
      (∑ i ∈ s, (Real.sqrt (a i) * b i) ^ 2) =
        ∑ i ∈ s, a i * b i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (ha i hi)]
  rw [hleft, hfirst, hsecond] at hcs
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, a i * b i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (hb i hi)
  have hsqrtA : 0 ≤ Real.sqrt (∑ i ∈ s, a i) := Real.sqrt_nonneg _
  have hsqrtB : 0 ≤ Real.sqrt (∑ i ∈ s, a i * b i ^ 2) := Real.sqrt_nonneg _
  have hsq :
      (∑ i ∈ s, a i * b i) ^ 2 ≤
        (Real.sqrt (∑ i ∈ s, a i) * Real.sqrt (∑ i ∈ s, a i * b i ^ 2)) ^ 2 :=
    (sq_le_sq₀ hsum_nonneg (mul_nonneg hsqrtA hsqrtB)).2 hcs
  have hrootA : (Real.sqrt (∑ i ∈ s, a i)) ^ 2 = ∑ i ∈ s, a i :=
    Real.sq_sqrt (Finset.sum_nonneg fun i hi => ha i hi)
  have hrootB : (Real.sqrt (∑ i ∈ s, a i * b i ^ 2)) ^ 2 =
      ∑ i ∈ s, a i * b i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))
  nlinarith [hsq, hrootA, hrootB]

/-- Euclidean Schur test: uniform absolute row and column sums bound the
operator norm by their geometric mean. -/
theorem euclidean_schur_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ R)
    (hcol : ∀ j, (∑ i, ‖A i j‖) ≤ C) :
    matrixNorm A ≤ Real.sqrt (R * C) := by
  classical
  change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)‖ ≤ Real.sqrt (R * C)
  apply ContinuousLinearMap.opNorm_le_bound
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (Real.sqrt_nonneg _)
  intro x
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  have hcoord (i : ι) :
      (T x) i = ∑ j, A i j * x j := by
    change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x) i = _
    rw [← WithLp.toLp_ofLp 2 x]
    simp [Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct]
  have hweighted (i : ι) :
      (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 ≤
        R * (∑ j, ‖A i j‖ * ‖x j‖ ^ 2) := by
    have hcs := weighted_cauchy_sum (Finset.univ : Finset ι)
      (fun j => ‖A i j‖) (fun j => ‖x j‖)
      (fun j hj => norm_nonneg _) (fun j hj => norm_nonneg _)
    have hrowi := hrow i
    have hweightedNonneg : 0 ≤ ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 :=
      Finset.sum_nonneg fun j hj => mul_nonneg (norm_nonneg _) (sq_nonneg _)
    calc
      (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 ≤
          (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖x j‖ ^ 2) := hcs
      _ ≤ R * (∑ j, ‖A i j‖ * ‖x j‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hrowi hweightedNonneg
  have hpoint (i : ι) :
      ‖(T x) i‖ ^ 2 ≤
        R * (∑ j, ‖A i j‖ * ‖x j‖ ^ 2) := by
    have htriangle :
        ‖(T x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
      calc
        _ = ‖∑ j, A i j * x j‖ := by rw [hcoord]
        _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
        _ = ∑ j, ‖A i j‖ * ‖x j‖ := by simp [norm_mul]
    have hnonneg : 0 ≤ ‖(T x) i‖ := norm_nonneg _
    have hsumNonneg : 0 ≤ ∑ j, ‖A i j‖ * ‖x j‖ :=
      Finset.sum_nonneg fun j hj => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq := (sq_le_sq₀ hnonneg hsumNonneg).2 htriangle
    exact hsq.trans (hweighted i)
  have hnormSq :
      ‖T x‖ ^ 2 ≤ R * C * ‖x‖ ^ 2 := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
      fun i hi => hpoint i
    have hweightedTotal :
        (∑ i, ∑ j, ‖A i j‖ * ‖x j‖ ^ 2) ≤ C * (∑ j, ‖x j‖ ^ 2) := by
      rw [Finset.sum_comm]
      calc
        (∑ j, ∑ i, ‖A i j‖ * ‖x j‖ ^ 2) =
            ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [← Finset.sum_mul]
        _ ≤ ∑ j, C * ‖x j‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
        _ = C * (∑ j, ‖x j‖ ^ 2) := by rw [Finset.mul_sum]
    have hnormT : ‖T x‖ ^ 2 = ∑ i, ‖(T x) i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
    have hnormX : ‖x‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := EuclideanSpace.norm_sq_eq _
    calc
      ‖T x‖ ^ 2 = ∑ i, ‖(T x) i‖ ^ 2 := hnormT
      _ ≤ R * ∑ i, ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact hsum
      _ ≤ R * (C * ∑ j, ‖x j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hweightedTotal hR
      _ = R * C * ‖x‖ ^ 2 := by rw [hnormX]; ring
  have hbound : ‖T x‖ ≤ Real.sqrt (R * C) * ‖x‖ := by
    have hsq : (Real.sqrt (R * C) * ‖x‖) ^ 2 = (R * C) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hR hC)]
    have hnonnegT := norm_nonneg (T x)
    have hnonnegB : 0 ≤ Real.sqrt (R * C) * ‖x‖ :=
      mul_nonneg (Real.sqrt_nonneg (R * C)) (norm_nonneg x)
    have hsqBound : ‖T x‖ ^ 2 ≤ (Real.sqrt (R * C) * ‖x‖) ^ 2 := by
      calc
        ‖T x‖ ^ 2 ≤ R * C * ‖x‖ ^ 2 := hnormSq
        _ = (Real.sqrt (R * C) * ‖x‖) ^ 2 := hsq.symm
    exact (sq_le_sq₀ hnonnegT hnonnegB).1 hsqBound
  exact hbound

/-- Submultiplicativity of the Euclidean matrix operator norm used by the
assembly comparison. -/
theorem matrixNorm_mul_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) : matrixNorm (A * B) ≤ matrixNorm A * matrixNorm B := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A * B)‖ ≤ _
  calc
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A * B)‖ =
        ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A *
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B‖ := by simp
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖ *
          ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B‖ := norm_mul_le _ _
    _ = matrixNorm A * matrixNorm B := by rfl

/-- An indicator diagonal is a contraction in the Euclidean matrix norm. -/
theorem matrixNorm_activeProjection_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) :
    matrixNorm (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)) ≤ 1 := by
  classical
  let f : ι → ℂ := fun i => if i ∈ A then 1 else 0
  have hnorm : matrixNorm (Matrix.diagonal f) = ‖f‖ := by
    change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Matrix.diagonal f)‖ = ‖f‖
    calc
      _ = ‖(Matrix.diagonal f : Matrix ι ι ℂ)‖ := Matrix.l2_opNorm_toEuclideanCLM _
      _ = ‖f‖ := Matrix.l2_opNorm_diagonal f
  have hf : ‖f‖ ≤ 1 := by
    change (↑(Finset.univ.sup fun i => ‖f i‖₊) : ℝ) ≤ 1
    have hsup : Finset.univ.sup (fun i => ‖f i‖₊) ≤ 1 := by
      apply Finset.sup_le
      intro i hi
      by_cases hiA : i ∈ A <;> simp [f, hiA]
    exact_mod_cast hsup
  simpa [f] using hnorm.le.trans hf

/-- Principal two-sided compression cannot increase the Euclidean operator norm. -/
theorem matrixNorm_compress_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (S : Finset ι) :
    matrixNorm
      (Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) * A *
        Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0)) ≤ matrixNorm A := by
  let P : Matrix ι ι ℂ := Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0)
  have hP : matrixNorm P ≤ 1 := by simpa [P] using matrixNorm_activeProjection_le_one S
  have hPA : matrixNorm (P * A) ≤ matrixNorm P * matrixNorm A := matrixNorm_mul_le P A
  have hPA0 : 0 ≤ matrixNorm (P * A) := norm_nonneg _
  have hA0 : 0 ≤ matrixNorm A := norm_nonneg _
  have hP0 : 0 ≤ matrixNorm P := norm_nonneg _
  have hP2 : (matrixNorm P) ^ 2 ≤ 1 := by nlinarith
  calc
    matrixNorm (P * A * P) ≤ matrixNorm (P * A) * matrixNorm P := matrixNorm_mul_le (P * A) P
    _ ≤ (matrixNorm P * matrixNorm A) * matrixNorm P :=
      mul_le_mul_of_nonneg_right hPA hP0
    _ = matrixNorm A * (matrixNorm P) ^ 2 := by ring
    _ ≤ matrixNorm A * 1 := mul_le_mul_of_nonneg_left hP2 hA0
    _ = matrixNorm A := by ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.euclidean_schur_bound
#print axioms AndersonAC.SolS78.matrixNorm_mul_le
#print axioms AndersonAC.SolS78.matrixNorm_activeProjection_le_one
#print axioms AndersonAC.SolS78.matrixNorm_compress_le
