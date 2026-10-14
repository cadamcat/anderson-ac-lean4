import Mathlib

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

/-- Copied verbatim from `AndersonAC.S78` (Statements.lean:29-31). Do not import
that file here (it carries `sorry`s); the lead bridges by `rfl`. -/
def pathCost {ι : Type} (T : Finset ι) (xs : List ι) : ℕ := by
  classical
  exact ((xs.zip xs.tail).map fun e => if e.1 ∈ T ∨ e.2 ∈ T then 0 else 1).sum

/-- Copied verbatim from `AndersonAC.S78` (Statements.lean:33-35). -/
def terminalDistance {ι : Type} (G : SimpleGraph ι) (T : Finset ι) (u v : ι) : ℝ :=
  ((sInf {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧
    xs.getLast? = some v ∧ pathCost T xs = n} : ℕ) : ℝ)

end AndersonAC.SolS78
