import AndersonAC.S9Inf.CombesThomas
import AndersonAC.S9Inf.CTWeights

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9

theorem combes_thomas_infinite_proof (d : ℕ) (coupling : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (E η : ℝ), η ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (ω : Configuration d) (x y : Site d),
        ‖AndersonAC.SolS9Inf.scalarGreen coupling ω x y ((E : ℂ) + η * Complex.I)‖ ≤
          C / η * Real.exp (-c * η * AndersonAC.SolS9Inf.latticeDistance x y) :=
  combes_thomas_infinite_of_weights AndersonAC.SolS9Inf.ctWeightBounds_proof d coupling

end AndersonAC.SolS9
