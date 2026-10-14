import AndersonAC.S9Fin.Core

noncomputable section
open AndersonAC.S9

namespace AndersonAC.SolS9

universe u

/-- Rank bounds Hilbert–Schmidt mass by rank times squared Euclidean operator norm. -/
def RankHilbertSchmidtStatement : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n] (G : Matrix n n ℂ),
    hilbertSchmidtSq G ≤ (Matrix.rank G : ℝ) * matrixOpNorm G ^ 2

end AndersonAC.SolS9
