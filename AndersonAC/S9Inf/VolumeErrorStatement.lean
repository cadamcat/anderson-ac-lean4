import OAI.MathematicalPhysics.Anderson.Certificates

/-! Frozen scalar asymptotic needed after finite/infinite volume comparison. -/

noncomputable section

open Filter OAI.Anderson
open scoped Topology

namespace AndersonAC.SolS9Inf

def VolumeComparisonErrorStatement : Prop :=
  ∀ (d : ℕ) (η : ℕ → ℝ),
    ((∀ m, 0 < η m) ∧ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ m in atTop, a / (4 : ℝ) ^ m ≤ η m ∧ η m ≤ c / (4 : ℝ) ^ m) →
    ∀ C c : ℝ, 0 < c →
      Tendsto (fun m => C * (sideLength m : ℝ) ^ (d - 1) * (η m)⁻¹ ^ 2 *
        Real.exp (-c * η m * sideLength m)) atTop (𝓝 0)

end AndersonAC.SolS9Inf
