import AndersonAC.S9Inf.RootCouplingLaw

/-! The frozen root-coupling record, copied verbatim from the inventory,
and its construction from the proved law helper. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.S9

def torusSite {d m : ℕ} (x : Site d) : Torus d m := fun j => (x j : ZMod (sideLength m))

def rootCubeMatch {d m : ℕ} (ωm : TorusConfiguration d m) (ω : Configuration d) : Prop :=
  ∀ x : Site d, (∀ j : Fin d, |x j| ≤ (sideLength m / 4 : ℕ)) →
    (ωm (torusSite x) : ℝ) = potential ω x

structure RootCoupling (d m : ℕ) where
  law : Measure (TorusConfiguration d m × Configuration d)
  probability : IsProbabilityMeasure law
  finite_marginal : law.map Prod.fst = torusLaw d m
  infinite_marginal : law.map Prod.snd = disorderLaw d
  matched : ∀ᵐ p ∂law, rootCubeMatch p.1 p.2

end AndersonAC.S9

namespace AndersonAC.SolS9

theorem rootCoupling_exists_proof (d m : ℕ) : Nonempty (AndersonAC.S9.RootCoupling d m) := by
  obtain ⟨μ, hprob, hfin, hinf, hmatch⟩ := AndersonAC.SolS9Inf.rootCouplingLaw_proof d m
  exact ⟨⟨μ, hprob, hfin, hinf, hmatch⟩⟩

end AndersonAC.SolS9
