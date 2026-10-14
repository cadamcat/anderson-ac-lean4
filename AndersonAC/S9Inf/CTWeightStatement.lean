import AndersonAC.S9Inf.HelperStatements

/-! Frozen scalar weight bounds for infinite-lattice Combes–Thomas. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

def ctWeight {d : ℕ} (y : Site d) (N : ℕ) (a : ℝ) (x : Site d) : ℝ :=
  Real.exp (a * (min (latticeDistance x y) N : ℕ))

def CTWeightBoundsStatement : Prop :=
  ∀ {d : ℕ} (y : Site d) (N : ℕ) (a : ℝ), 0 ≤ a →
    ctWeight y N a y = 1 ∧
    (∀ x : Site d, 1 ≤ ctWeight y N a x ∧ ctWeight y N a x ≤ Real.exp (a * N)) ∧
    ∀ (x : Site d) (j : Fin d),
      |ctWeight y N a x / ctWeight y N a (x + basisVector j) - 1| ≤ Real.exp a - 1 ∧
      |ctWeight y N a x / ctWeight y N a (x - basisVector j) - 1| ≤ Real.exp a - 1

end AndersonAC.SolS9Inf
