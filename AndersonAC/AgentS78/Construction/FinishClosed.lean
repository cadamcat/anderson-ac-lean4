import AndersonAC.AgentS78.Construction.BoxClosed
import AndersonAC.AgentS78.Construction.ClearingTrueValues
import AndersonAC.AgentS78.Construction.TileCoreA1
import AndersonAC.AgentS78.Construction.StagePhasePkgClosed
import AndersonAC.AgentS78.Construction.TileTrueValues

/-! The uniform certificate input with `clearingTrueValues_proof` supplied. -/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The uniform certificate input from clearing-block measurability, tile bounds, the
clearing phase package, and tile true-value hypotheses. -/
theorem uniformCertificateInput_closed5 (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hclr : ClearingPhasePackage d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedTV d hd e₂ he₂ hcmeas hA1 hA2 hclr hTT clearingTrueValues_proof

/-- The uniform certificate input with the proved tile slot law. -/
theorem uniformCertificateInput_closed4 (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hclr : ClearingPhasePackage d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed5 d hd e₂ he₂ hcmeas tileSlotLaw_proof hA2 hclr hTT

/-- The uniform certificate input with the clearing phase package assembled from
`ClearingBoundR`. -/
theorem uniformCertificateInput_closedB (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) (_hP : ClearingDonePhysHyp d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed4 d hd e₂ he₂ hcmeas hA2 (clearingPhasePackage_closed d hd hB) hTT

/-- The uniform certificate input using the route R2 DONE identity off
`exceptionalSet` and the joint run invariant. -/
theorem uniformCertificateInput_closedR2 (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed4 d hd e₂ he₂ hcmeas hA2 (clearingPhasePackage_closed d hd hB) hTT

/-- The uniform certificate input with the proved tile true values. -/
theorem uniformCertificateInput_closedT (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) (hP : ClearingDonePhysHyp d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedB d hd e₂ he₂ hcmeas hA2 hB hP tileTrueValues_proof

/-- The uniform certificate input using route R2 and the proved tile true values. -/
theorem uniformCertificateInput_closedR2T (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedR2 d hd e₂ he₂ hcmeas hA2 hB tileTrueValues_proof

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedR2T
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedR2
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedT
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedB
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closed5
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closed4
