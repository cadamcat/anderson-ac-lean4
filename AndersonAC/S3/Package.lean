import AndersonAC.S3.GridBounds
import AndersonAC.S3.JointVolume
import AndersonAC.S3H.Slab
import AndersonAC.S3H.Fourier
import AndersonAC.S3H.PeriodicQuadrature
import AndersonAC.S3H.Polar
import AndersonAC.S3H.JointShellK
import AndersonAC.S3H.LayerCake
import AndersonAC.S3.Comparators
import AndersonAC.S3.SmallSymbol

/-!
WP05 package join (conditional form). `Packages.initialization` follows from the
helper statements below; once every helper `_proof` is integrated the hypotheses
are discharged and `initialization_proof` is stated with exactly the package type.

Dependency map of the hypotheses:
* `TorusFourierStatement` — helper S3-fourier;
* `PeriodicGridQuadratureStatement` — helper S3-pquad;
* `BottomResolventStatement` — helper S3-bottom, from `RayEstimatesStatement` (S3-ray)
  and `PolarRayBoundStatement` (S3-polar);
* `SmallSymbolStatement` — helper S3-symsmall, from TF, PQ, BR;
* `LargeSymbolStatement` — helper S3-symlarge, from TF, PQ, BR, `JointShellKStatement`
  (S3-kshell, from `JointShellXStatement` = `jointShellX_of_helpers slabSlice_proof _`,
  which needs `ConvexShellStatement` from S3-polar) and `LayerCakeStatement` (S3-layer).
-/

noncomputable section

namespace AndersonAC.S3

/-- The joint shell in sliced coordinates, with the slab helper discharged. -/
theorem jointShellX_of_convexShell (hshell : ConvexShellStatement) : JointShellXStatement :=
  jointShellX_of_helpers slabSlice_proof hshell

/-- WP05 from the intermediate helper statements. -/
theorem initialization_of_helpers (hF : TorusFourierStatement)
    (hQ : PeriodicGridQuadratureStatement) (hB : BottomResolventStatement)
    (hS : SmallSymbolStatement) (hL : LargeSymbolStatement) :
    ∃ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) ∧ AndersonAC.Blueprint.InitializationInput e₂ :=
  ⟨1 / 200, by norm_num, initialization_of_gridBounds hF (gridBounds_of_helpers hQ hB hS hL)⟩

/-- The joint shell in `k` coordinates, unconditionally (slab, convex shell and transfer
helpers integrated). -/
theorem jointShellK_proof : JointShellKStatement :=
  jointShellK_of_X_proof (jointShellX_of_convexShell convexShell_proof)

/-- WP05 with the integrated helpers discharged; remaining inputs: the bottom-of-band
continuum bounds and the two symbol statements. -/
theorem initialization_of_remaining (hB : BottomResolventStatement)
    (hS : SmallSymbolStatement) (hL : LargeSymbolStatement) :
    ∃ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) ∧ AndersonAC.Blueprint.InitializationInput e₂ :=
  initialization_of_helpers torusFourier_proof periodicGridQuadrature_proof hB hS hL

/-- `InitializationInput e₂` for every window parameter, from the window-parametric
symbol statements (the form needed with the comparators at the same `e₂`). -/
theorem initializationInput_of_remainingW (hB : BottomResolventStatement)
    (hS : SmallSymbolWStatement) (hLD : LargeSymbolDecayWStatement) {e₂ : ℝ}
    (he : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) : AndersonAC.Blueprint.InitializationInput e₂ :=
  initializationInput_of_gridBoundsW torusFourier_proof
    (gridBoundsW_of_helpers periodicGridQuadrature_proof hB hS (largeSymbolW_of_decayW hLD)) he

/-- `InitializationInput e₂` for every `e₂`, remaining inputs: bottom resolvent and the
large-frequency decay. -/
theorem initializationInput_of_BR_decay (hB : BottomResolventStatement)
    (hLD : LargeSymbolDecayWStatement) {e₂ : ℝ} (he : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    AndersonAC.Blueprint.InitializationInput e₂ :=
  initializationInput_of_remainingW hB
    (smallSymbolW_of_helpers torusFourier_proof periodicGridQuadrature_proof hB) hLD he

/-- WP05 (`e₂ = 1/200`) with only the bottom resolvent and the large-frequency symbol left. -/
theorem initialization_of_BR_large (hB : BottomResolventStatement) (hL : LargeSymbolStatement) :
    ∃ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) ∧ AndersonAC.Blueprint.InitializationInput e₂ :=
  initialization_of_remaining hB
    (smallSymbol_of_helpers torusFourier_proof periodicGridQuadrature_proof hB) hL

end AndersonAC.S3
