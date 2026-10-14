import AndersonAC.S78.Definitions
import AndersonAC.S78.ResetVariation
import AndersonAC.Blueprint.FiniteInputs
import AndersonAC.S78Comm.Commutator

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem wardInverseOn
    (hWard : AndersonAC.Blueprint.WardInput)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (t : ℝ) (r : ι → ℂ) (c : ℝ)
    (ht : 0 < t)
    (hsym : ∀ i j, M i j = M j i)
    (hreal : ∀ i j, (M i j).im = 0)
    (hc : 0 < c) (hlow : ∀ i, c ≤ (r i).im) :
    ∃ G : Matrix ι ι ℂ,
      AndersonAC.Blueprint.twoSidedInverse (M - (t : ℂ) • Matrix.diagonal r) G ∧
      G.transpose = G ∧
      (‖G‖ ≤ (t * c)⁻¹) ∧
      (t : ℂ) • (G * Matrix.diagonal (fun i => ((r i).im : ℂ)) * G.conjTranspose) =
        AndersonAC.Blueprint.matrixImag G := by
  classical
  let N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι
  let Mfin : Matrix (Fin N) (Fin N) ℂ := M.submatrix e.symm e.symm
  let rfin : Fin N → ℂ := r ∘ e.symm
  have hMfin_trans : Mfin.transpose = Mfin := by
    ext a b
    simp only [Mfin, Matrix.transpose_apply, Matrix.submatrix_apply]
    exact hsym _ _
  have hMfin_real : ∀ i j, (Mfin i j).im = 0 := by
    intro a b
    simp only [Mfin, Matrix.submatrix_apply]
    exact hreal _ _
  have hlow_fin : ∀ i, c ≤ (rfin i).im := fun a => hlow _
  obtain ⟨Gfin, hInvFin, hSymFin, hNormFin, hWardFin⟩ :=
    hWard N Mfin hMfin_trans hMfin_real t ht rfin c hc hlow_fin
  let G : Matrix ι ι ℂ := Gfin.submatrix e e
  have hGfin_norm : ‖Gfin‖ ≤ (t * c)⁻¹ := by
    have : AndersonAC.Blueprint.opNorm Gfin ≤ (t * c)⁻¹ := hNormFin
    rwa [show AndersonAC.Blueprint.opNorm Gfin = ‖Gfin‖ from rfl] at this
  have hAfin : (M - (t : ℂ) • Matrix.diagonal r).submatrix e.symm e.symm
      = Mfin - (t : ℂ) • Matrix.diagonal rfin := by
    ext a b
    simp only [Mfin, rfin, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  have hG_back : G.submatrix e.symm e.symm = Gfin := by
    ext a b
    simp only [G, Matrix.submatrix_apply]
    simp
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · constructor
    · have hfin : (Mfin - (t : ℂ) • Matrix.diagonal rfin) * Gfin = 1 := hInvFin.1
      have hsub : ((M - (t : ℂ) • Matrix.diagonal r) * G).submatrix e.symm e.symm
          = (1 : Matrix (Fin N) (Fin N) ℂ) := by
        have hmul := Matrix.submatrix_mul_equiv (M - (t : ℂ) • Matrix.diagonal r) G
          (⇑e.symm) e.symm (⇑e.symm)
        rw [← hmul, hAfin, hG_back, hfin]
      ext i j
      have h := congrFun (congrFun hsub (e i)) (e j)
      simp only [Matrix.submatrix_apply] at h
      simpa [Matrix.one_apply, e.symm_apply_apply] using h
    · have hfin : Gfin * (Mfin - (t : ℂ) • Matrix.diagonal rfin) = 1 := hInvFin.2
      have hsub : (G * (M - (t : ℂ) • Matrix.diagonal r)).submatrix e.symm e.symm
          = (1 : Matrix (Fin N) (Fin N) ℂ) := by
        have hmul := Matrix.submatrix_mul_equiv G (M - (t : ℂ) • Matrix.diagonal r)
          (⇑e.symm) e.symm (⇑e.symm)
        rw [← hmul, hG_back, hAfin, hfin]
      ext i j
      have h := congrFun (congrFun hsub (e i)) (e j)
      simp only [Matrix.submatrix_apply] at h
      simpa [Matrix.one_apply, e.symm_apply_apply] using h
  · ext i j
    simp only [G, Matrix.transpose_apply, Matrix.submatrix_apply]
    have h := congrFun (congrFun hSymFin (e j)) (e i)
    simpa [Matrix.transpose_apply] using h.symm
  · have hle : ‖G‖ ≤ ‖Gfin‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      let v : ι → ℂ := WithLp.ofLp x
      have hx : x = WithLp.toLp 2 v := by simp [v]
      let vfin : Fin N → ℂ := v ∘ e.symm
      have hmul : G *ᵥ v = (Gfin *ᵥ vfin) ∘ e :=
        Matrix.submatrix_mulVec_equiv Gfin v (⇑e) e
      have hG : ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) G) x
          = WithLp.toLp 2 (G *ᵥ v) := by rw [hx]; rfl
      have hGfin : ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) Gfin)
            (WithLp.toLp 2 vfin) = WithLp.toLp 2 (Gfin *ᵥ vfin) := rfl
      have hsq : ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) G) x‖ ^ 2
          = ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) Gfin)
            (WithLp.toLp 2 vfin)‖ ^ 2 := by
        rw [hG, hGfin, hmul]
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        simp only [Function.comp_apply]
        exact e.sum_comp (fun a => ‖(Gfin *ᵥ vfin) a‖ ^ 2)
      have hnorm_eq : ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) G) x‖
          = ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) Gfin)
            (WithLp.toLp 2 vfin)‖ :=
        (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
      rw [hnorm_eq]
      calc ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) Gfin)
              (WithLp.toLp 2 vfin)‖
          ≤ ‖Gfin‖ * ‖(WithLp.toLp 2 vfin : EuclideanSpace ℂ (Fin N))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖Gfin‖ * ‖x‖ := by
            congr 1
            have hsq2 : ‖(WithLp.toLp 2 vfin : EuclideanSpace ℂ (Fin N))‖ ^ 2
                = ‖x‖ ^ 2 := by
              rw [hx, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
              simp only [vfin, Function.comp_apply]
              exact e.symm.sum_comp (fun i => ‖v i‖ ^ 2)
            exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq2
    exact le_trans hle hGfin_norm
  · have hWardFin_eq : (t : ℂ) • (Gfin * Matrix.diagonal (fun a => ((rfin a).im : ℂ)) *
        Gfin.conjTranspose) = AndersonAC.Blueprint.matrixImag Gfin := hWardFin
    have hLHS : ((t : ℂ) • (G * Matrix.diagonal (fun i => ((r i).im : ℂ)) *
        G.conjTranspose)).submatrix e.symm e.symm
        = (t : ℂ) • (Gfin * Matrix.diagonal (fun a => ((rfin a).im : ℂ)) *
          Gfin.conjTranspose) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Matrix.conjTranspose_apply, G, rfin,
        Function.comp_apply, smul_eq_mul, e.apply_symm_apply,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      congr 1
      simpa [e.symm_apply_apply] using e.sum_comp (fun k => Gfin a k *
        ((r (e.symm k)).im : ℂ) * star (Gfin b k))
    have hRHS : (AndersonAC.Blueprint.matrixImag G).submatrix e.symm e.symm
        = AndersonAC.Blueprint.matrixImag Gfin := by
      ext a b
      simp only [AndersonAC.Blueprint.matrixImag, Matrix.submatrix_apply,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, G]
      simp
    have hsub_eq : ((t : ℂ) • (G * Matrix.diagonal (fun i => ((r i).im : ℂ)) *
        G.conjTranspose)).submatrix e.symm e.symm
        = (AndersonAC.Blueprint.matrixImag G).submatrix e.symm e.symm := by
      rw [hLHS, hRHS, hWardFin_eq]
    ext i j
    have h := congrFun (congrFun hsub_eq (e i)) (e j)
    simp only [Matrix.submatrix_apply] at h
    simpa using h

end AndersonAC.SolS78Var
