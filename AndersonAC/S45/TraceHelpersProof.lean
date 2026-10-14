import AndersonAC.S45.ConcentrationHelpers
import Mathlib.Basic.Complex.BigOperators

set_option maxHeartbeats 1000000

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder BigOperators

namespace AndersonAC.OpusS45

open AndersonAC.Blueprint

private theorem opNorm_eq_norm {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    opNorm X = ‖X‖ := by
  simpa [opNorm] using (Matrix.cstar_norm_def X).symm

private theorem hermitian_spectral_form {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.IsHermitian) :
    S = (hS.eigenvectorUnitary : Matrix _ _ ℂ) *
      Matrix.diagonal (fun i => (hS.eigenvalues i : ℂ)) *
      (hS.eigenvectorUnitary : Matrix _ _ ℂ)ᴴ := by
  simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]
    using hS.spectral_theorem

private theorem hermitian_exp_spectral_form {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.IsHermitian) :
    NormedSpace.exp S = (hS.eigenvectorUnitary : Matrix _ _ ℂ) *
      Matrix.diagonal (fun i => (Real.exp (hS.eigenvalues i) : ℂ)) *
      (hS.eigenvectorUnitary : Matrix _ _ ℂ)ᴴ := by
  let U := (hS.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  let D := Matrix.diagonal (fun i => (hS.eigenvalues i : ℂ))
  have hU : IsUnit U := by
    dsimp [U]
    exact Unitary.isUnit_coe
  have hUinv : U⁻¹ = Uᴴ := by
    let u : (Matrix (Fin N) (Fin N) ℂ)ˣ := hU.unit
    have huval : (u : Matrix (Fin N) (Fin N) ℂ) = U := hU.unit_spec
    have hmatrixInv : U⁻¹ = (u⁻¹ : Matrix (Fin N) (Fin N) ℂ) := by
      rw [← huval]
    have hstar : Uᴴ * (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
      rw [huval]
      simpa [U, Matrix.star_eq_conjTranspose] using
        (Unitary.coe_star_mul_self hS.eigenvectorUnitary)
    have hstarInv : Uᴴ = (u⁻¹ : Matrix (Fin N) (Fin N) ℂ) := by
      calc
        Uᴴ = ↑(u⁻¹) := Units.eq_inv_of_mul_eq_one_right hstar
        _ = (u : Matrix (Fin N) (Fin N) ℂ)⁻¹ := by simp
    exact hmatrixInv.trans hstarInv.symm
  have hspec : S = U * D * Uᴴ := by
    simpa [U, D] using hermitian_spectral_form S hS
  have hexpD : NormedSpace.exp D = Matrix.diagonal
      (fun i => (Real.exp (hS.eigenvalues i) : ℂ)) := by
    rw [Matrix.exp_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply, if_pos rfl]
      have hpoint : NormedSpace.exp (fun j : Fin N => (hS.eigenvalues j : ℂ)) i =
          NormedSpace.exp ((hS.eigenvalues i : ℂ)) := by
        simpa using NormedSpace.map_exp (Pi.evalRingHom ℂ i) (continuous_apply i)
          (fun j : Fin N => (hS.eigenvalues j : ℂ))
      rw [hpoint, ← NormedSpace.ofReal_exp_ℝ_ℝ, Real.exp_eq_exp_ℝ]
    · simp [hij]
  calc
    NormedSpace.exp S = NormedSpace.exp (U * D * Uᴴ) := congrArg NormedSpace.exp hspec
    _ = NormedSpace.exp (U * D * U⁻¹) :=
      congrArg NormedSpace.exp (by rw [← hUinv])
    _ = U * NormedSpace.exp D * U⁻¹ := Matrix.exp_conj U D hU
    _ = U * Matrix.diagonal (fun i => (Real.exp (hS.eigenvalues i) : ℂ)) * Uᴴ := by
      rw [hexpD]
      rw [hUinv]

private theorem trace_diagonal_mul_eq {N : Type*} [Fintype N] [DecidableEq N]
    (d : N → ℂ) (M : Matrix N N ℂ) :
    Matrix.trace (Matrix.diagonal d * M) = ∑ i, d i * M i i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

private theorem re_trace_diagonal_mul_nonneg {N : Type*} [Fintype N] [DecidableEq N]
    (d : N → ℝ) (hd : ∀ i, 0 ≤ d i) (M : Matrix N N ℂ) (hM : M.PosSemidef) :
    0 ≤ (Matrix.trace (Matrix.diagonal (fun i => (d i : ℂ)) * M)).re := by
  rw [trace_diagonal_mul_eq]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i hi
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  exact mul_nonneg (hd i) ((Complex.nonneg_iff.mp (hM.diag_nonneg (i := i))).1)

private theorem trace_unitary_conj {N : Type*} [Fintype N] [DecidableEq N]
    (U : Matrix N N ℂ) (hU : Uᴴ * U = 1) (M : Matrix N N ℂ) :
    Matrix.trace (U * M * Uᴴ) = Matrix.trace M := by
  calc
    Matrix.trace (U * M * Uᴴ) = Matrix.trace (Uᴴ * U * M) :=
      Matrix.trace_mul_cycle U M Uᴴ
    _ = Matrix.trace M := by rw [hU]; simp

private theorem unitary_inv_eq_conjTranspose {N : Type*} [Fintype N] [DecidableEq N]
    (U : Matrix.unitaryGroup N ℂ) :
    (U : Matrix N N ℂ)⁻¹ = (U : Matrix N N ℂ)ᴴ := by
  let A := (U : Matrix N N ℂ)
  have hA : IsUnit A := by
    dsimp [A]
    exact Unitary.isUnit_coe
  let v : (Matrix N N ℂ)ˣ := hA.unit
  have hv : (v : Matrix N N ℂ) = A := hA.unit_spec
  have hmatrixInv : A⁻¹ = (v⁻¹ : Matrix N N ℂ) := by
    rw [← hv]
  have hstar : Aᴴ * (v : Matrix N N ℂ) = 1 := by
    rw [hv]
    dsimp [A]
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hstarInv : Aᴴ = (v⁻¹ : Matrix N N ℂ) := by
    calc
      Aᴴ = ↑(v⁻¹) := Units.eq_inv_of_mul_eq_one_right hstar
      _ = (v : Matrix N N ℂ)⁻¹ := by simp
  exact hmatrixInv.trans hstarInv.symm

private theorem unitary_exp_diagonal {N : Type*} [Fintype N] [DecidableEq N]
    (U : Matrix.unitaryGroup N ℂ) (d : N → ℝ) :
    NormedSpace.exp ((U : Matrix N N ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix N N ℂ)ᴴ) =
      (U : Matrix N N ℂ) * Matrix.diagonal (fun i => (Real.exp (d i) : ℂ)) *
        (U : Matrix N N ℂ)ᴴ := by
  let Um := (U : Matrix N N ℂ)
  let D := Matrix.diagonal (fun i => (d i : ℂ))
  have hunit : IsUnit Um := by
    dsimp [Um]
    exact Unitary.isUnit_coe
  have hinv : Um⁻¹ = Umᴴ := by
    exact unitary_inv_eq_conjTranspose U
  have hexpD : NormedSpace.exp D = Matrix.diagonal
      (fun i => (Real.exp (d i) : ℂ)) := by
    rw [Matrix.exp_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply, if_pos rfl]
      have hpoint : NormedSpace.exp (fun j : N => (d j : ℂ)) i =
          NormedSpace.exp ((d i : ℂ)) := by
        simpa using NormedSpace.map_exp (Pi.evalRingHom ℂ i) (continuous_apply i)
          (fun j : N => (d j : ℂ))
      rw [hpoint, ← NormedSpace.ofReal_exp_ℝ_ℝ, Real.exp_eq_exp_ℝ]
    · simp [hij]
  calc
    NormedSpace.exp (Um * D * Umᴴ) = NormedSpace.exp (Um * D * Um⁻¹) :=
      congrArg NormedSpace.exp (by rw [← hinv])
    _ = Um * NormedSpace.exp D * Um⁻¹ := Matrix.exp_conj Um D hunit
    _ = Um * Matrix.diagonal (fun i => (Real.exp (d i) : ℂ)) * Umᴴ := by
      rw [hexpD, hinv]

private theorem trace_unitary_diagonal {N : Type*} [Fintype N] [DecidableEq N]
    (U : Matrix.unitaryGroup N ℂ) (d : N → ℝ) :
    (Matrix.trace ((U : Matrix N N ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix N N ℂ)ᴴ)).re = ∑ i, d i := by
  let Um := (U : Matrix N N ℂ)
  have hUstarU : Umᴴ * Um = 1 := by
    dsimp [Um]
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  calc
    _ = (Matrix.trace (Matrix.diagonal (fun i => (d i : ℂ)))).re := by
      rw [trace_unitary_conj Um hUstarU]
    _ = ∑ i, d i := by
      simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]

private theorem trace_unitary_exp_diagonal {N : Type*} [Fintype N] [DecidableEq N]
    (U : Matrix.unitaryGroup N ℂ) (d : N → ℝ) :
    (Matrix.trace (NormedSpace.exp ((U : Matrix N N ℂ) *
      Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix N N ℂ)ᴴ))).re =
      ∑ i, Real.exp (d i) := by
  calc
    _ = (Matrix.trace ((U : Matrix N N ℂ) *
        Matrix.diagonal (fun i => (Real.exp (d i) : ℂ)) *
        (U : Matrix N N ℂ)ᴴ)).re := by rw [unitary_exp_diagonal]
    _ = ∑ i, Real.exp (d i) := trace_unitary_diagonal U (fun i => Real.exp (d i))

private theorem hermitian_exp_trace {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.IsHermitian) :
    (Matrix.trace (NormedSpace.exp S)).re = ∑ i, Real.exp (hS.eigenvalues i) := by
  have hform := hermitian_exp_spectral_form S hS
  calc
    (Matrix.trace (NormedSpace.exp S)).re =
        (Matrix.trace ((hS.eigenvectorUnitary : Matrix _ _ ℂ) *
          Matrix.diagonal (fun i => (Real.exp (hS.eigenvalues i) : ℂ)) *
          (hS.eigenvectorUnitary : Matrix _ _ ℂ)ᴴ)).re :=
      congrArg (fun z : ℂ => z.re) (congrArg Matrix.trace hform)
    _ = ∑ i, Real.exp (hS.eigenvalues i) :=
      trace_unitary_diagonal hS.eigenvectorUnitary (fun i => Real.exp (hS.eigenvalues i))

private theorem hermitian_opNorm_eq_eigenvalues_norm {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℂ) (hS : S.IsHermitian) :
    opNorm S = ‖hS.eigenvalues‖ := by
  calc
    opNorm S = ‖S‖ := opNorm_eq_norm S
    _ = ‖Unitary.conjStarAlgAut ℂ (Matrix (Fin N) (Fin N) ℂ) hS.eigenvectorUnitary
          (Matrix.diagonal (Complex.ofReal ∘ hS.eigenvalues))‖ :=
      congrArg (fun X : Matrix (Fin N) (Fin N) ℂ => ‖X‖) hS.spectral_theorem
    _ = ‖hS.eigenvalues‖ := by
      simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rw [((algebraMap_isometry ℝ ℂ).postcomp_pi).norm_map_of_map_zero (by ext; simp)]

private theorem hermitian_neg_exp_trace {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.IsHermitian) :
    (Matrix.trace (NormedSpace.exp (-S))).re =
      ∑ i, Real.exp (-(hS.eigenvalues i)) := by
  let U := (hS.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  let d := hS.eigenvalues
  have hspec := hermitian_spectral_form S hS
  have hneg : -S = U * Matrix.diagonal (fun i => ((-d i : ℝ) : ℂ)) * Uᴴ := by
    calc
      -S = -(U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) := congrArg Neg.neg hspec
      _ = U * (-(Matrix.diagonal (fun i => (d i : ℂ))) * Uᴴ) := by
        rw [Matrix.mul_assoc, neg_mul_eq_mul_neg, neg_mul_eq_neg_mul]
      _ = U * Matrix.diagonal (fun i => ((-d i : ℝ) : ℂ)) * Uᴴ := by
        rw [← Matrix.mul_assoc, Matrix.diagonal_neg]
        simp
  calc
    (Matrix.trace (NormedSpace.exp (-S))).re =
        (Matrix.trace (NormedSpace.exp
          (U * Matrix.diagonal (fun i => ((-d i : ℝ) : ℂ)) * Uᴴ))).re :=
      congrArg (fun z : ℂ => z.re)
        (congrArg Matrix.trace (congrArg NormedSpace.exp hneg))
    _ = ∑ i, Real.exp (-d i) :=
      trace_unitary_exp_diagonal hS.eigenvectorUnitary (fun i => -d i)

private theorem real_exp_abs_le_two_sides (u x : ℝ) (hu : 0 ≤ u) :
    Real.exp (u * |x|) ≤ Real.exp (u * x) + Real.exp (-(u * x)) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx, show u * -x = -(u * x) by ring]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

private theorem trace_mul_diagonal_eq {N : Type*} [Fintype N] [DecidableEq N]
    (M : Matrix N N ℂ) (d : N → ℂ) :
    Matrix.trace (M * Matrix.diagonal d) = ∑ i, M i i * d i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

private theorem re_trace_mul_diagonal_eq {N : Type*} [Fintype N] [DecidableEq N]
    (M : Matrix N N ℂ) (d : N → ℝ) :
    (Matrix.trace (M * Matrix.diagonal (fun i => (d i : ℂ)))).re =
      ∑ i, (M i i).re * d i := by
  rw [trace_mul_diagonal_eq, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]

private theorem trace_mul_unitary_conj_diagonal {N : Type*} [Fintype N] [DecidableEq N]
    (A U : Matrix N N ℂ) (d : N → ℂ) :
    Matrix.trace (A * (U * Matrix.diagonal d * Uᴴ)) =
      Matrix.trace ((Uᴴ * A * U) * Matrix.diagonal d) := by
  simpa [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle (A * U) (Matrix.diagonal d) Uᴴ)

private theorem re_trace_eq_sum_diag {N : Type*} [Fintype N] [DecidableEq N]
    (M : Matrix N N ℂ) : (Matrix.trace M).re = ∑ i, (M i i).re := by
  simp [Matrix.trace, Complex.re_sum]

private theorem hermitian_square_spectral_form {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.IsHermitian) :
    S * S = (hS.eigenvectorUnitary : Matrix _ _ ℂ) *
      Matrix.diagonal (fun i => ((hS.eigenvalues i ^ 2 : ℝ) : ℂ)) *
      (hS.eigenvectorUnitary : Matrix _ _ ℂ)ᴴ := by
  let U := (hS.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  let D := Matrix.diagonal (fun i => (hS.eigenvalues i : ℂ))
  have hspec := hermitian_spectral_form S hS
  have hUstarU : Uᴴ * U = 1 := by
    dsimp [U]
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hmiddle : Uᴴ * (U * (D * Uᴴ)) = D * Uᴴ := by
    rw [← Matrix.mul_assoc, hUstarU, one_mul]
  calc
    S * S = (U * D * Uᴴ) * (U * D * Uᴴ) := congrArg (fun X => X * X) hspec
    _ = U * D * (D * Uᴴ) := by
      simp only [Matrix.mul_assoc]
      rw [hmiddle]
    _ = U * (D * D) * Uᴴ := by simp [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => ((hS.eigenvalues i ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 2
      ext i
      simp [D, pow_two]

private theorem trace_exp_quadratic_unit {N : ℕ} (A Z : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.PosSemidef) (hZ : Z.IsHermitian)
    (hbound : ∀ i, |hZ.eigenvalues i| ≤ 1) :
    (Matrix.trace (A * NormedSpace.exp Z)).re ≤
      (Matrix.trace A).re + (Matrix.trace (A * Z)).re +
        (Matrix.trace (A * (Z * Z))).re := by
  let U := (hZ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  let d := hZ.eigenvalues
  let B := Uᴴ * A * U
  have hB : B.PosSemidef := by
    dsimp [B]
    exact hA.conjTranspose_mul_mul_same U
  have htraceBA : Matrix.trace B = Matrix.trace A := by
    calc
      Matrix.trace B = Matrix.trace (Uᴴ * A * U) := rfl
      _ = Matrix.trace (U * Uᴴ * A) := Matrix.trace_mul_cycle Uᴴ A U
      _ = Matrix.trace A := by
        have hUU : U * Uᴴ = 1 := by
          dsimp [U]
          simpa [Matrix.star_eq_conjTranspose] using
            Unitary.coe_mul_star_self hZ.eigenvectorUnitary
        rw [hUU]
        simp
  have htraceA : (Matrix.trace A).re = ∑ i, (B i i).re := by
    calc
      _ = (Matrix.trace B).re := congrArg Complex.re htraceBA.symm
      _ = ∑ i, (B i i).re := re_trace_eq_sum_diag B
  have hspecZ := hermitian_spectral_form Z hZ
  have hspecExp := hermitian_exp_spectral_form Z hZ
  have hspecSq := hermitian_square_spectral_form Z hZ
  have htraceExp : Matrix.trace (A * NormedSpace.exp Z) =
      Matrix.trace (B * Matrix.diagonal (fun i => (Real.exp (d i) : ℂ))) := by
    calc
      _ = Matrix.trace (A * (U * Matrix.diagonal (fun i => (Real.exp (d i) : ℂ)) * Uᴴ)) :=
        congrArg (fun X => Matrix.trace (A * X)) hspecExp
      _ = Matrix.trace (B * Matrix.diagonal (fun i => (Real.exp (d i) : ℂ))) := by
        exact trace_mul_unitary_conj_diagonal A U
          (fun i => (Real.exp (d i) : ℂ))
  have htraceZ : Matrix.trace (A * Z) = Matrix.trace
      (B * Matrix.diagonal (fun i => (d i : ℂ))) := by
    calc
      _ = Matrix.trace (A * (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)) :=
        congrArg (fun X => Matrix.trace (A * X)) hspecZ
      _ = Matrix.trace (B * Matrix.diagonal (fun i => (d i : ℂ))) := by
        exact trace_mul_unitary_conj_diagonal A U (fun i => (d i : ℂ))
  have htraceSq : Matrix.trace (A * (Z * Z)) = Matrix.trace
      (B * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ))) := by
    calc
      _ = Matrix.trace
          (A * (U * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * Uᴴ)) :=
        congrArg (fun X => Matrix.trace (A * X)) hspecSq
      _ = Matrix.trace (B * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ))) := by
        exact trace_mul_unitary_conj_diagonal A U
          (fun i => ((d i ^ 2 : ℝ) : ℂ))
  have hscalar (i : Fin N) : Real.exp (d i) ≤ 1 + d i + d i ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (hbound i)
    have h' : Real.exp (d i) - 1 - d i ≤ d i ^ 2 := (le_abs_self _).trans h
    linarith
  have hweighted : (∑ i, (B i i).re * Real.exp (d i)) ≤
      ∑ i, (B i i).re * (1 + d i + d i ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hscalar i)
      ((Complex.nonneg_iff.mp (hB.diag_nonneg (i := i))).1)
  have hTraceExp : (Matrix.trace (A * NormedSpace.exp Z)).re =
      ∑ i, (B i i).re * Real.exp (d i) := by
    rw [htraceExp]
    exact re_trace_mul_diagonal_eq B (fun i => Real.exp (d i))
  have hTraceZ : (Matrix.trace (A * Z)).re =
      ∑ i, (B i i).re * d i := by
    rw [htraceZ]
    exact re_trace_mul_diagonal_eq B d
  have hTraceSq : (Matrix.trace (A * (Z * Z))).re =
      ∑ i, (B i i).re * d i ^ 2 := by
    rw [htraceSq]
    exact re_trace_mul_diagonal_eq B (fun i => d i ^ 2)
  calc
    (Matrix.trace (A * NormedSpace.exp Z)).re =
        ∑ i, (B i i).re * Real.exp (d i) := hTraceExp
    _ ≤ ∑ i, (B i i).re * (1 + d i + d i ^ 2) := hweighted
    _ = (Matrix.trace A).re + (Matrix.trace (A * Z)).re +
        (Matrix.trace (A * (Z * Z))).re := by
      rw [htraceA, hTraceZ, hTraceSq]
      simp [mul_add, Finset.sum_add_distrib]

theorem traceExpQuadratic_proof : TraceExpQuadratic := by
  intro N A Y u J hA hY hnormY hu huJ
  let Z := u • Y
  have hZ : Z.IsHermitian := by
    dsimp [Z]
    exact hY.smul (IsSelfAdjoint.all u)
  have hnormZ : opNorm Z = u * opNorm Y := by
    dsimp [Z]
    rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu]
  have hnormZle : opNorm Z ≤ 1 := by
    rw [hnormZ]
    exact (mul_le_mul_of_nonneg_left hnormY hu).trans huJ
  have hbound : ∀ i, |hZ.eigenvalues i| ≤ 1 := by
    intro i
    calc
      |hZ.eigenvalues i| = ‖hZ.eigenvalues i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖hZ.eigenvalues‖ := norm_le_pi_norm _ _
      _ = opNorm Z := (hermitian_opNorm_eq_eigenvalues_norm Z hZ).symm
      _ ≤ 1 := hnormZle
  have hquad := trace_exp_quadratic_unit A Z hA hZ hbound
  have htraceZ : (Matrix.trace (A * Z)).re = u * (Matrix.trace (A * Y)).re := by
    have hprod : A * Z = u • (A * Y) := by
      dsimp [Z]
      exact mul_smul_comm u A Y
    rw [hprod, Matrix.trace_smul]
    simp [Complex.real_smul, Complex.re_ofReal_mul]
  have hZsq : Z * Z = u ^ 2 • (Y * Y) := by
    dsimp [Z]
    calc
      (u • Y) * (u • Y) = u • (Y * (u • Y)) := by rw [smul_mul_assoc]
      _ = u • (u • (Y * Y)) := by congr 2; exact mul_smul_comm u Y Y
      _ = (u * u) • (Y * Y) := smul_smul u u (Y * Y)
      _ = u ^ 2 • (Y * Y) := by rw [pow_two]
  have htraceZsq : (Matrix.trace (A * (Z * Z))).re =
      u ^ 2 * (Matrix.trace (A * (Y * Y))).re := by
    have hprod : A * (Z * Z) = u ^ 2 • (A * (Y * Y)) := by
      rw [hZsq]
      exact mul_smul_comm (u ^ 2) A (Y * Y)
    rw [hprod, Matrix.trace_smul]
    rw [Complex.real_smul]
    exact Complex.re_ofReal_mul _ _
  calc
    (Matrix.trace (A * NormedSpace.exp (u • Y))).re =
        (Matrix.trace (A * NormedSpace.exp Z)).re := rfl
    _ ≤ (Matrix.trace A).re + (Matrix.trace (A * Z)).re +
        (Matrix.trace (A * (Z * Z))).re := hquad
    _ = (Matrix.trace A).re + u * (Matrix.trace (A * Y)).re +
        u ^ 2 * (Matrix.trace (A * (Y * Y))).re := by rw [htraceZ, htraceZsq]

private theorem norm_pow_le_op {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) :
    ‖X ^ n‖ ≤ ‖X‖ ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun i => by simp)
  | succ n ih =>
      rw [pow_succ]
      calc
        ‖X ^ n * X‖ ≤ ‖X ^ n‖ * ‖X‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖X‖ ^ n * ‖X‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ‖X‖ ^ (n + 1) := by rw [pow_succ]

private theorem norm_exp_le_exp_norm {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  have hsR : Summable fun n : ℕ =>
      ((Nat.factorial n : ℝ)⁻¹) • (‖X‖ ^ n : ℝ) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖X‖
  have hterm (n : ℕ) :
      ‖((Nat.factorial n : ℝ)⁻¹) • (X ^ n)‖ ≤
        ((Nat.factorial n : ℝ)⁻¹) • (‖X‖ ^ n : ℝ) := by
    have hc : 0 ≤ (Nat.factorial n : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le_op X n) hc
  have hrealterm (n : ℕ) :
      ‖((Nat.factorial n : ℝ)⁻¹) • (‖X‖ ^ n : ℝ)‖ =
        ((Nat.factorial n : ℝ)⁻¹) • (‖X‖ ^ n : ℝ) := by
    apply Real.norm_of_nonneg
    exact smul_nonneg (inv_nonneg.mpr (by positivity)) (pow_nonneg (norm_nonneg _) _)
  have hsNorm : Summable fun n : ℕ => ‖((Nat.factorial n : ℝ)⁻¹) • (X ^ n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => hterm n) hsR
  calc
    ‖NormedSpace.exp X‖ = ‖∑' n : ℕ, ((Nat.factorial n : ℝ)⁻¹) • (X ^ n)‖ := by
      rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
    _ ≤ ∑' n : ℕ, ‖((Nat.factorial n : ℝ)⁻¹) • (X ^ n)‖ :=
      norm_tsum_le_tsum_norm hsNorm
    _ ≤ ∑' n : ℕ, ((Nat.factorial n : ℝ)⁻¹) • (‖X‖ ^ n : ℝ) :=
      Summable.tsum_le_tsum hterm hsNorm hsR
    _ = NormedSpace.exp ‖X‖ := by
      rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
    _ = Real.exp ‖X‖ := (Real.exp_eq_exp_ℝ).symm ▸ rfl

private theorem entry_norm_le_opNorm {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) : ‖X i j‖ ≤ opNorm X := by
  let v := EuclideanSpace.single j (1 : ℂ)
  have hcoord : ‖X i j‖ ≤
      ‖(EuclideanSpace.equiv (Fin N) ℂ).symm (X *ᵥ v.ofLp)‖ := by
    have h := PiLp.norm_apply_le
      ((EuclideanSpace.equiv (Fin N) ℂ).symm (X *ᵥ v.ofLp)) i
    simpa [v] using h
  have hmul := Matrix.l2_opNorm_mulVec X v
  have hv : ‖v‖ = 1 := by simp [v]
  calc
    ‖X i j‖ ≤ ‖(EuclideanSpace.equiv (Fin N) ℂ).symm (X *ᵥ v.ofLp)‖ := hcoord
    _ ≤ ‖X‖ * ‖v‖ := hmul
    _ = ‖X‖ := by rw [hv, mul_one]
    _ = opNorm X := (opNorm_eq_norm X).symm

theorem opNormBounds_proof : OpNormBounds := by
  constructor
  · intro N X
    calc
      opNorm (NormedSpace.exp X) = ‖NormedSpace.exp X‖ := opNorm_eq_norm _
      _ ≤ Real.exp ‖X‖ := norm_exp_le_exp_norm X
      _ = Real.exp (opNorm X) := by rw [(opNorm_eq_norm X).symm]
  · intro N X i j
    exact entry_norm_le_opNorm X i j

theorem expOpNormLeTrace_proof : ExpOpNormLeTrace := by
  intro N S u hN hS hu
  let T := u • S
  have hT : T.IsHermitian := by
    dsimp [T]
    exact hS.smul (IsSelfAdjoint.all u)
  have hnormT : opNorm T = u * opNorm S := by
    dsimp [T]
    rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu]
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin N))
      (fun j => |hT.eigenvalues j|) hne
  have hcoord : ∀ j, ‖hT.eigenvalues j‖ ≤ ‖hT.eigenvalues i‖ := by
    intro j
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hmax j (Finset.mem_univ j)
  have hnormEig : ‖hT.eigenvalues‖ = ‖hT.eigenvalues i‖ := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hcoord
    · exact norm_le_pi_norm _ _
  have hnormi : opNorm T = ‖hT.eigenvalues i‖ :=
    (hermitian_opNorm_eq_eigenvalues_norm T hT).trans hnormEig
  have hsum₁ : Real.exp (hT.eigenvalues i) ≤
      ∑ j, Real.exp (hT.eigenvalues j) := by
    exact Finset.single_le_sum (f := fun j => Real.exp (hT.eigenvalues j))
      (fun j hj => Real.exp_nonneg _) (Finset.mem_univ i)
  have hsum₂ : Real.exp (-(hT.eigenvalues i)) ≤
      ∑ j, Real.exp (-(hT.eigenvalues j)) := by
    exact Finset.single_le_sum (f := fun j => Real.exp (-(hT.eigenvalues j)))
      (fun j hj => Real.exp_nonneg _) (Finset.mem_univ i)
  calc
    Real.exp (u * opNorm S) = Real.exp (opNorm T) := congrArg Real.exp hnormT.symm
    _ = Real.exp (‖hT.eigenvalues i‖) := congrArg Real.exp hnormi
    _ = Real.exp (|hT.eigenvalues i|) := by rw [Real.norm_eq_abs]
    _ ≤ Real.exp (hT.eigenvalues i) + Real.exp (-(hT.eigenvalues i)) := by
      simpa using real_exp_abs_le_two_sides 1 (hT.eigenvalues i) (by norm_num)
    _ ≤ (∑ j, Real.exp (hT.eigenvalues j)) +
        (∑ j, Real.exp (-(hT.eigenvalues j))) := add_le_add hsum₁ hsum₂
    _ = (Matrix.trace (NormedSpace.exp T)).re +
        (Matrix.trace (NormedSpace.exp (-T))).re := by
      rw [hermitian_exp_trace T hT, hermitian_neg_exp_trace T hT]

theorem expPosSemidef_proof : ExpPosSemidef := by
  intro N S hS
  let U := (hS.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  let d := fun i => Real.exp (hS.eigenvalues i)
  have hdiag : (Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact Complex.nonneg_iff.mpr ⟨Real.exp_nonneg _, by simp⟩
  have hform := hermitian_exp_spectral_form S hS
  have hpos := hdiag.mul_mul_conjTranspose_same U
  have hUstar : Uᴴ = star U := by simp [U, Matrix.star_eq_conjTranspose]
  simpa [U, d, hUstar] using hform ▸ hpos

theorem tracePairNonneg_proof : TracePairNonneg := by
  intro N A M hA hM
  let U := (hA.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  let d := hA.1.eigenvalues
  let D := Matrix.diagonal (fun i => (d i : ℂ))
  let M' := Uᴴ * M * U
  have hM' : M'.PosSemidef := by
    dsimp [M']
    exact hM.conjTranspose_mul_mul_same U
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact (hA.1.posSemidef_iff_eigenvalues_nonneg.mp hA) i
  have hspec := hermitian_spectral_form A hA.1
  have hrot : Matrix.trace (A * M) = Matrix.trace (D * M') := by
    calc
      Matrix.trace (A * M) = Matrix.trace ((U * D * Uᴴ) * M) :=
        congrArg (fun X : Matrix (Fin N) (Fin N) ℂ => Matrix.trace (X * M)) hspec
      _ = Matrix.trace (U * D * (Uᴴ * M)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((Uᴴ * M) * U * D) := Matrix.trace_mul_cycle U D (Uᴴ * M)
      _ = Matrix.trace (D * (Uᴴ * M * U)) := by
        rw [Matrix.trace_mul_comm ((Uᴴ * M) * U) D]
      _ = Matrix.trace (D * M') := rfl
  rw [hrot]
  exact re_trace_diagonal_mul_nonneg d hd M' hM'

theorem traceHelpers_proof : TraceHelpers :=
  ⟨expPosSemidef_proof, tracePairNonneg_proof, traceExpQuadratic_proof,
    expOpNormLeTrace_proof, opNormBounds_proof⟩

#print axioms traceHelpers_proof

end AndersonAC.OpusS45
