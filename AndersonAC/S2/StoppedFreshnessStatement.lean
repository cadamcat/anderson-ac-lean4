import AndersonAC.S2.Definitions

/-! Lifts fixed-operation freshness to stopped histories. -/
noncomputable section
open MeasureTheory ProbabilityTheory AndersonAC.S2
universe u

namespace AndersonAC.SolS2

structure StoppedFreshnessLift : Prop where
  natTime : ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ)
    (Q : ℕ → RandomSources ι M → Query ι), ObeysQueryRules ι Q →
    (∀ q, FreshAt ι Q q) →
    ∀ (τ : RandomSources ι M → ℕ), IsRetainedStoppingTime ι Q τ →
    ∀ (D : Set (RandomSources ι M)), MeasurableSet[stoppedRetained ι Q τ] D →
    ∀ (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
      (O : Finset ℕ) (b : (o : ℕ) → Order (M o)),
      (sourcesLaw ι M ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s} ∩
        signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
        (2 : ℝ) ^ (-(s.card : ℤ)) *
          ∫ ω in {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s},
            completionWeight ι Q (τ ω) O b ω ∂sourcesLaw ι M
  aeTime : ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ)
    (Q : ℕ → RandomSources ι M → Query ι), ObeysQueryRules ι Q →
    (∀ q, FreshAt ι Q q) →
    ∀ (F : Filtration ℕ (inferInstance : MeasurableSpace (RandomSources ι M))),
      (∀ q, F q = retained ι Q q) →
    ∀ (τ : RandomSources ι M → WithTop ℕ) (hτ : IsStoppingTime F τ),
      (∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤) →
    ∀ (D : Set (RandomSources ι M)), MeasurableSet[hτ.measurableSpace] D →
    ∀ (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
      (O : Finset ℕ) (b : (o : ℕ) → Order (M o)),
      (sourcesLaw ι M ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} ∩
        signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
        (2 : ℝ) ^ (-(s.card : ℤ)) *
          ∫ ω in {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s},
            completionWeight ι Q ((τ ω).untopD 0) O b ω ∂sourcesLaw ι M

end AndersonAC.SolS2
