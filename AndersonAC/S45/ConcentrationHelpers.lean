import AndersonAC.Blueprint.FiniteInputs

/-! Deterministic finite-matrix facts used by the trace-exponential
supermartingale in Lemma 5.6 (`ConcentrationInput.maximal`). Each is a `Prop`;
a helper module proves
`AndersonAC.OpusS45.<name>_proof : <name>` without changing the statement.
Matrix norms are Euclidean operator norms (`AndersonAC.Blueprint.opNorm`). -/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace AndersonAC.OpusS45

open AndersonAC.Blueprint

/-- The exponential of a Hermitian matrix is positive semidefinite. -/
def ExpPosSemidef : Prop :=
  ∀ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℂ), S.IsHermitian → (NormedSpace.exp S).PosSemidef

/-- The trace pairing of two positive semidefinite matrices is nonnegative. -/
def TracePairNonneg : Prop :=
  ∀ (N : ℕ) (A M : Matrix (Fin N) (Fin N) ℂ), A.PosSemidef → M.PosSemidef →
    0 ≤ (Matrix.trace (A * M)).re

/-- Paper 05-local-sweeps.tex:704: `e^{uY} ≤ 1 + uY + C u² Y²` for `uJ ≤ 1`,
in the trace-pairing form against a positive semidefinite `A` (here `C = 1`,
from `|e^x - 1 - x| ≤ x²` for `|x| ≤ 1`, applied on the spectrum of `Y`). -/
def TraceExpQuadratic : Prop :=
  ∀ (N : ℕ) (A Y : Matrix (Fin N) (Fin N) ℂ) (u J : ℝ),
    A.PosSemidef → Y.IsHermitian → opNorm Y ≤ J → 0 ≤ u → u * J ≤ 1 →
      (Matrix.trace (A * NormedSpace.exp (u • Y))).re ≤
        (Matrix.trace A).re + u * (Matrix.trace (A * Y)).re +
          u ^ 2 * (Matrix.trace (A * (Y * Y))).re

/-- Two-sided eigenvalue crossing: `e^{u‖S‖} ≤ Tr e^{uS} + Tr e^{-uS}` for
Hermitian `S` in positive dimension and `u ≥ 0`. -/
def ExpOpNormLeTrace : Prop :=
  ∀ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℂ) (u : ℝ), 0 < N → S.IsHermitian → 0 ≤ u →
    Real.exp (u * opNorm S) ≤
      (Matrix.trace (NormedSpace.exp (u • S))).re +
        (Matrix.trace (NormedSpace.exp (-(u • S)))).re

/-- Size bounds used for integrability. -/
def OpNormBounds : Prop :=
  (∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ),
      opNorm (NormedSpace.exp X) ≤ Real.exp (opNorm X)) ∧
  (∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N), ‖X i j‖ ≤ opNorm X)

/-- The five deterministic inputs together (one helper package). -/
def TraceHelpers : Prop :=
  ExpPosSemidef ∧ TracePairNonneg ∧ TraceExpQuadratic ∧ ExpOpNormLeTrace ∧ OpNormBounds

end AndersonAC.OpusS45
