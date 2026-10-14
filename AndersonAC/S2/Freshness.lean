import AndersonAC.S2.OrderCompletion
import AndersonAC.S2Fresh.Lift

/-! The joint retained-information law and its stopped versions (Lemma 2.2). -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace AndersonAC.S2
open AndersonAC.SolS2
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem conditional_freshness {M : ℕ → ℕ} {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ) : FreshAt ι Q q := by
  intro D hD s a O b
  rw [unqueried_sign_cylinder ι hQ q D hD s a O b,
    order_completion Q hQ q D hD s O b]

theorem conditional_freshness_stopped {M : ℕ → ℕ}
    {Q : ℕ → RandomSources ι M → Query ι} (hQ : ObeysQueryRules ι Q)
    (τ : RandomSources ι M → ℕ) (hτ : IsRetainedStoppingTime ι Q τ)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[stoppedRetained ι Q τ] D)
    (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        ∫ ω in {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q (τ ω) s},
          completionWeight ι Q (τ ω) O b ω ∂sourcesLaw ι M :=
  StoppedFreshnessLift_proof.natTime ι M Q hQ (conditional_freshness ι hQ)
    τ hτ D hD s a O b

theorem conditional_freshness_ae_stopped {M : ℕ → ℕ}
    {Q : ℕ → RandomSources ι M → Query ι} (hQ : ObeysQueryRules ι Q)
    (F : Filtration ℕ (inferInstance : MeasurableSpace (RandomSources ι M)))
    (hF : ∀ q, F q = retained ι Q q)
    (τ : RandomSources ι M → WithTop ℕ) (hτ : IsStoppingTime F τ)
    (hfinite : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[hτ.measurableSpace] D)
    (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M ({ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} ∩
      signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        ∫ ω in {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s},
          completionWeight ι Q ((τ ω).untopD 0) O b ω ∂sourcesLaw ι M :=
  StoppedFreshnessLift_proof.aeTime ι M Q hQ (conditional_freshness ι hQ)
    F hF τ hτ hfinite D hD s a O b

end AndersonAC.S2
