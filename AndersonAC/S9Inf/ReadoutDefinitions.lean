import AndersonAC.S9Fin.Core

/-! Infinite readout definitions copied verbatim from the frozen inventory.
The finite definitions are the finite lane's existing pure Core module. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology

namespace AndersonAC.S9

def comparableHeights (η : ℕ → ℝ) : Prop :=
  (∀ m, 0 < η m) ∧ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
    ∀ᶠ m in atTop, a / (4 : ℝ) ^ m ≤ η m ∧ η m ≤ c / (4 : ℝ) ^ m

def diagonalGreen {d : ℕ} (coupling : ℝ) (ω : Configuration d) (x : Site d) (z : ℂ) : ℂ :=
  AndersonAC.Blueprint.diagonalGreen coupling ω x z

end AndersonAC.S9
