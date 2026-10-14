import AndersonAC.AgentS78.Construction.StagePhaseSchurDet
import AndersonAC.AgentS78.Construction.Exceptional
import AndersonAC.AgentS78.Construction.PhysicalIdentity

/-!
# Invertible eliminated blocks off the exceptional set

agent-s78phase2 (route R2, part (3)). Off `exceptionalSet` every principal block of the true
matrix `trueShifted = H_λ(ω) − E` is invertible; a matrix that agrees with it on the complement of
`A` therefore has an invertible eliminated block `offB B A`. For a record whose sites outside `A`
carry their true values `λ V`, this is the block of `installedShifted E x`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-- **The eliminated block is invertible off the exceptional set.** -/
theorem offB_unit_of_true {M : ℕ → ℕ} (n₀ : ℕ) (u E : ℝ) (ω : RandomSources (Torus d m) M)
    (hω : ω ∉ exceptionalSet n₀ u E M) (B : Matrix (Torus d m) (Torus d m) ℂ)
    (A : Finset (Torus d m))
    (hB : ∀ i j, i ∉ A → j ∉ A → B i j = trueShifted n₀ u E (trueConfig ω) i j) :
    IsUnit (offB B A).det := by
  classical
  have hall : ∀ U : Finset (Torus d m), IsUnit ((trueShifted n₀ u E (trueConfig ω)).submatrix
      (fun i : {i // i ∈ U} => i.val) (fun i : {i // i ∈ U} => i.val)) := by
    by_contra h; exact hω h
  have h := hall (Finset.univ \ A)
  rw [Matrix.isUnit_iff_isUnit_det] at h
  let e : {i // i ∉ A} ≃ {i // i ∈ Finset.univ \ A} :=
    Equiv.subtypeEquivRight (fun i => by simp)
  have heq : offB B A = ((trueShifted n₀ u E (trueConfig ω)).submatrix
      (fun i : {i // i ∈ Finset.univ \ A} => i.val)
      (fun i : {i // i ∈ Finset.univ \ A} => i.val)).submatrix e e := by
    ext a b
    simp only [offB, Matrix.submatrix_apply]
    exact hB a.val b.val a.2 b.2
  rw [heq, Matrix.det_submatrix_equiv_self]
  exact h

/-- `installedShifted` agrees with the true matrix wherever the installed values are true. -/
theorem installedShifted_eq_true_on {M : ℕ → ℕ} (n₀ : ℕ) (u E : ℝ)
    (ω : RandomSources (Torus d m) M) (inst : Torus d m → ℝ) (x : RunRecord d m)
    (hx : x.installed = inst) (i j : Torus d m)
    (hi : inst i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)) :
    installedShifted E x i j = trueShifted n₀ u E (trueConfig ω) i j := by
  subst hx
  simp only [installedShifted, trueShifted, Matrix.sub_apply, Matrix.add_apply,
    OAI.Anderson.periodicHamiltonian, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp [hi]
  · simp [hij]

end AndersonAC.AgentS78
