import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.EnergyInputs
import AndersonAC.S78Schur.Bridge
import AndersonAC.S78.EndpointAlgebra

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- Removed set at operation `a`. -/
def removedSet {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) : Finset (Torus d m) :=
  (I.state a.castSucc).active \ (I.state a.succ).active

/-- Old normalized inverse at operation `a`. -/
def oldInv {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) : Matrix (Torus d m) (Torus d m) ℂ :=
  normalizedInverse (I.state a.castSucc) t

/-- Per-operation Schur trial upper bound for the old bridge energy.
Uses `SolS78.schur_bridge_trial_proof` (Mathlib-only); the two copies of
`wardEnergy`/`schurEnergy` are definitionally equal. -/
theorem bridge_trial_bound {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k)
    (f : Torus d m → ℝ) (c : ℝ) :
    assemblyBridge I a f ≤
      ∑ i ∈ (I.state a.succ).active, ∑ x ∈ removedSet I a,
        (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 * (f i - c) ^ 2 := by
  classical
  have hBA : (I.state a.succ).active ⊆ (I.state a.castSucc).active :=
    I.nested a
  have hp : ∀ i ∈ (I.state a.castSucc).active, 0 ≤ (r i).im := by
    intro i _
    have h := (I.damping i).1
    have hc : 0 < I.c := I.positive.2.2.2.2.1
    exact hc.le.trans h
  have hsym : ∀ i j, oldInv I a i j = oldInv I a j i := by
    intro i j
    exact AndersonAC.SolS78.normalized_endpoint_symmetric
      (I.state a.castSucc) r t (I.physical _) i j
  -- Apply the proved variational trial; `S78`/`SolS78` copies are defeq.
  exact AndersonAC.SolS78.schur_bridge_trial_proof
    (I.state a.castSucc).active (I.state a.succ).active hBA
    (fun i => (r i).im) hp (oldInv I a) hsym f c |>.2

end AndersonAC.S78BridgeEnergy
