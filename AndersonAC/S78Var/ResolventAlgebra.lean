import AndersonAC.S78Var.WardTransport
import AndersonAC.S78.Definitions
import AndersonAC.Blueprint.FiniteInputs

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

/-- The concrete inverse equals Ward's inverse when the latter exists. -/
theorem resetInverse_eq_ward {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ)
    (G : Matrix ι ι ℂ)
    (hInv : AndersonAC.Blueprint.twoSidedInverse (M - (t : ℂ) • Matrix.diagonal r) G) :
    AndersonAC.S78.resetInverse M r t = G :=
  Matrix.inv_eq_right_inv hInv.1

/-- Exact resolvent identity from two-sided inverses. -/
theorem resolvent_identity {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (r ζ : ι → ℂ) (t : ℝ)
    (G G' : Matrix ι ι ℂ)
    (hInv : AndersonAC.Blueprint.twoSidedInverse (M - (t : ℂ) • Matrix.diagonal r) G)
    (hInv' : AndersonAC.Blueprint.twoSidedInverse
      (M - (t : ℂ) • Matrix.diagonal (r + ζ)) G') :
    G' - G = G' * ((t : ℂ) • Matrix.diagonal ζ) * G := by
  have hA_sub : (M - (t : ℂ) • Matrix.diagonal r)
      - (M - (t : ℂ) • Matrix.diagonal (r + ζ))
      = (t : ℂ) • Matrix.diagonal ζ := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Pi.add_apply]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      ring
    · simp only [hij, ite_false]
      ring
  have hAG : (M - (t : ℂ) • Matrix.diagonal r) * G = 1 := hInv.1
  have hG'A' : G' * (M - (t : ℂ) • Matrix.diagonal (r + ζ)) = 1 := hInv'.2
  calc G' - G
      = G' * ((M - (t : ℂ) • Matrix.diagonal r) * G)
        - (G' * (M - (t : ℂ) • Matrix.diagonal (r + ζ))) * G := by
        rw [hAG, hG'A']
        simp
    _ = G' * ((t : ℂ) • Matrix.diagonal ζ) * G := by
        have hmid : G' * ((M - (t : ℂ) • Matrix.diagonal r) * G)
            - (G' * (M - (t : ℂ) • Matrix.diagonal (r + ζ))) * G
            = G' * (((M - (t : ℂ) • Matrix.diagonal r)
              - (M - (t : ℂ) • Matrix.diagonal (r + ζ)))) * G := by
          noncomm_ring
        rw [hmid, hA_sub]

end AndersonAC.SolS78Var
