import AndersonAC.S3.Package
import AndersonAC.S3.Normalized
import AndersonAC.S3.StartupComparators
import AndersonAC.S3.ChargeEstimate
import AndersonAC.S3Circ.Circulant
import AndersonAC.S3H.BottomResolvent
import AndersonAC.S3H.Ray

/-!
The §3 endpoints assemble the helper estimates into the initialization result.
Bottom-resolvent and large-frequency estimates appear explicitly as hypotheses
where they are needed.
-/

noncomputable section

namespace AndersonAC.S3

/-- **Lemma 3.2** (planned `fourier_charge`), unconditional. -/
theorem fourier_charge_proof {d : ℕ} (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ (A : Type*) [Fintype A] (π : A → Torus d L), atMostTwo π → ∀ y : A → ℂ,
        form laplacianPlus (siteSum π y) ≤
          C * Real.rpow (normOne y) (4 / 3) * Real.rpow (Real.sqrt (normSq y)) (2 / 3) :=
  fourier_charge_of circulantCalculus_proof hd

/-- Comparators at any startup state, with only the large-frequency decay left. -/
theorem startup_comparators_of_decay (hLD : LargeSymbolDecayWStatement) {d : ℕ} (hd : 3 ≤ d)
    {e₂ : ℝ} (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) {c' C' : ℝ} (hc' : 0 < c') (hcC : c' ≤ C') :
    type_of% (startup_comparators torusFourier_proof circulantCalculus_proof hLD hd he₂ hc' hcC) :=
  startup_comparators torusFourier_proof circulantCalculus_proof hLD hd he₂ hc' hcC

/-- The normalized endpoint with only the bottom resolvent and the decay left. -/
theorem initialization_normalized_of_BR_decay (hB : BottomResolventStatement)
    (hLD : LargeSymbolDecayWStatement) {d : ℕ} (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    type_of% (initialization_normalized_of torusFourier_proof circulantCalculus_proof
      (gridBoundsW_of_helpers periodicGridQuadrature_proof hB
        (smallSymbolW_of_helpers torusFourier_proof periodicGridQuadrature_proof hB)
        (largeSymbolW_of_decayW hLD)) hLD hd e₂ he₂) :=
  initialization_normalized_of torusFourier_proof circulantCalculus_proof
    (gridBoundsW_of_helpers periodicGridQuadrature_proof hB
      (smallSymbolW_of_helpers torusFourier_proof periodicGridQuadrature_proof hB)
      (largeSymbolW_of_decayW hLD)) hLD hd e₂ he₂

/-- Lemma 3.5, the unconditional bottom-resolvent estimate. -/
theorem bottomResolvent_proof : BottomResolventStatement :=
  bottomResolvent_of_helpers rayEstimates_proof polarRayBound_proof

/-- The initialization input at `e₂ = 1/200` from the large-frequency symbol bound. -/
theorem initialization_of_large (hL : LargeSymbolStatement) :
    ∃ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) ∧ AndersonAC.Blueprint.InitializationInput e₂ :=
  initialization_of_BR_large bottomResolvent_proof hL

/-- The normalized endpoint with only the large-frequency decay left. -/
theorem initialization_normalized_of_decay (hLD : LargeSymbolDecayWStatement) {d : ℕ}
    (hd : 3 ≤ d) (e₂ : ℝ) (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    type_of% (initialization_normalized_of_BR_decay bottomResolvent_proof hLD hd e₂ he₂) :=
  initialization_normalized_of_BR_decay bottomResolvent_proof hLD hd e₂ he₂

end AndersonAC.S3
