import AndersonAC.GT.Golden
import AndersonAC.Blueprint.FiniteInputs

/-! Exact interface for the Golden–Thompson field of `ConcentrationInput`. -/

open scoped Matrix.Norms.L2Operator

namespace AndersonAC.MuseGT

/-- The Golden–Thompson input used by the scalar-envelope concentration proof. -/
theorem goldenThompson_proof :
    ∀ (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ),
      A.IsHermitian → B.IsHermitian →
      (Matrix.trace (NormedSpace.exp (A + B))).re ≤
        (Matrix.trace (NormedSpace.exp A * NormedSpace.exp B)).re := by
  intro N A B hA hB
  exact goldenThompson A B hA hB

example : type_of% @AndersonAC.Blueprint.ConcentrationInput.goldenThompson :=
  fun _ => goldenThompson_proof

#print axioms goldenThompson_proof

end AndersonAC.MuseGT
