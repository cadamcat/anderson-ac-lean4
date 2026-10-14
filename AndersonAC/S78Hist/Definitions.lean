import Mathlib

set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78hist

def delta : ℝ := 1 / 100
def nu (d : ℕ) : ℝ := delta / (100000 * (d : ℝ))
def birthBound (c : ℝ) (j : ℕ) : ℝ := Real.exp (-(4 : ℝ) ^ (c * (j : ℝ)))
def historyAlpha (d : ℕ) : ℝ := nu d / (100 * (d : ℝ))
def historyBeta (d : ℕ) : ℝ := 0.2 * nu d
def historyEarlier (d j : ℕ) : ℕ := ⌊historyAlpha d * (j : ℝ)⌋₊
def historyChildren (d j : ℕ) : ℕ := ⌊(4 : ℝ) ^ (historyBeta d * (j : ℝ))⌋₊
def witnessRadius (j : ℕ) : ℝ := (4 : ℝ) ^ (10 * j)
def historyExponent (d : ℕ) (c : ℝ) : ℝ := min (c * historyAlpha d / 4) (nu d / 20)

def recursionBound (d n₀ j : ℕ) (c C : ℝ) (Z : ℕ → ℝ) : ℝ :=
  C * (j : ℝ) * witnessRadius j ^ d * birthBound c (max n₀ (historyEarlier d j)) +
  if n₀ ≤ historyEarlier d j then
    (C * witnessRadius j ^ d * Z (historyEarlier d j)) ^ historyChildren d j else 0

end AndersonAC.SolS78hist
