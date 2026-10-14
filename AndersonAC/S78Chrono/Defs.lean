import Mathlib

/-! Sorry-free copies of the §8 birth definitions for the chronological-joint
helper. Bodies are verbatim copies of `AndersonAC.S78` definitions at
`AndersonAC/S78/Statements.lean:247,255-260`, placed in `AndersonAC.SolS78`
so the proof module does not import the sorry-carrying Statements file.
`birthBound` (a `def`) is defeq to the S78 version via `rfl` (see Check.lean);
`BirthProcess` (a `structure`) is a distinct inductive, so Check.lean bridges
it by explicit field-wise conversion. -/

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

def birthBound (c : ℝ) (j : ℕ) : ℝ := Real.exp (-(4 : ℝ) ^ (c * (j : ℝ)))

structure BirthProcess (Ω : Type) [MeasurableSpace Ω] where
  history : Filtration ℕ ‹MeasurableSpace Ω›
  event : ℕ → Set Ω
  scale : ℕ → ℕ
  adapted : ∀ n, MeasurableSet[history (n + 1)] (event n)

end AndersonAC.SolS78
