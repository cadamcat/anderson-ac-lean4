import AndersonAC.S2.Definitions

/-! Frozen helper contract for the random-order part of Lemma 2.2.
The helper must prove `AndersonAC.SolS2.OrderCompletion_proof : OrderCompletion`.
No sign-cylinder distribution is assumed in this contract. -/

noncomputable section
open MeasureTheory ProbabilityTheory AndersonAC.S2

namespace AndersonAC.SolS2

def OrderCompletion : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ)
    (Q : ℕ → RandomSources ι M → Query ι), ObeysQueryRules ι Q →
    ∀ (q : ℕ) (D : Set (RandomSources ι M)), MeasurableSet[retained ι Q q] D →
      ∀ (s : Finset (SignIndex ι)) (O : Finset ℕ) (b : (o : ℕ) → Order (M o)),
        (sourcesLaw ι M (D ∩ signsUnqueried ι Q q s ∩ orderCylinder ι O b)).toReal =
          ∫ ω in D ∩ signsUnqueried ι Q q s,
            completionWeight ι Q q O b ω ∂sourcesLaw ι M

end AndersonAC.SolS2
