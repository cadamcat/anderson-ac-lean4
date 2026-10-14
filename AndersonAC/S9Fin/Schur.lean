import AndersonAC.S9Fin.Algebra
import AndersonAC.S9Fin.SchurStatements

noncomputable section
open AndersonAC.S9

namespace AndersonAC.SolS9

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

lemma scalar_damping_inverse (S : Matrix n n ℂ) (hS : IsUnit S) (η : ℝ) :
    (S - (η * Complex.I) • 1)⁻¹ = dampingFunction η S⁻¹ := by
  have hfac : S - (η * Complex.I) • 1 = (1 - (η * Complex.I) • S⁻¹) * S := by
    rw [sub_mul, one_mul, Matrix.smul_mul,
      Matrix.nonsing_inv_mul S (S.isUnit_iff_isUnit_det.mp hS)]
  rw [hfac, Matrix.mul_inv_rev]
  rfl

lemma allPrincipalInvertible_isUnit (H : Matrix n n ℂ) (E : ℝ)
    (hprincipal : allPrincipalInvertible H E) : IsUnit (H - (E : ℂ) • 1) := by
  let e : (Finset.univ : Finset n) ≃ n := Equiv.ofBijective
    (fun x : (Finset.univ : Finset n) => (x : n))
    ⟨Subtype.coe_injective, fun x => ⟨⟨x, Finset.mem_univ x⟩, rfl⟩⟩
  have hu := hprincipal Finset.univ
  change IsUnit ((H - (E : ℂ) • 1).submatrix e e) at hu
  exact (Matrix.isUnit_submatrix_equiv e e).mp hu

set_option linter.unusedVariables false in
theorem active_resolvent_compression_of_schur (hK : SchurCompressionStatement.{u})
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n) :
    (activeSchur H E A - (η * Complex.I) • 1)⁻¹ =
      dampingFunction η (compress A ((H - (E : ℂ) • 1)⁻¹)) := by
  obtain ⟨hS, hSinv⟩ := hK n H E A
    (allPrincipalInvertible_isUnit H E hprincipal) (hprincipal (Finset.univ \ A))
  rw [scalar_damping_inverse (activeSchur H E A) hS η, hSinv]

end AndersonAC.SolS9
