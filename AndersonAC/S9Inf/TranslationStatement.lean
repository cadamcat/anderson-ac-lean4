import AndersonAC.S9Inf.Model

/-! covariance helper for the invariant positive-site event. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

def GreenTranslationStatement : Prop :=
  ∀ {d : ℕ} (coupling : ℝ) (ω : Configuration d) (a x y : Site d)
    (z : ℂ), 0 < z.im →
      scalarGreen coupling (fun u => ω (u + a)) x y z =
        scalarGreen coupling ω (x + a) (y + a) z

end AndersonAC.SolS9Inf
