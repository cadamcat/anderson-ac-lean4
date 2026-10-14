import AndersonAC.S78.EnergyAssembly
import AndersonAC.S78SurvivorTail.Proof
import AndersonAC.S78Cutoff.LocalCutoff
import AndersonAC.S78MatrixBounds.Proof
import AndersonAC.S78BridgeEnergy.Main

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

/-- The survivor tail is discharged in the assembly energy join. -/
theorem assemblyEnergyBounds_of_pending_inputs (hmat : AssemblyMatrixBounds)
    (hcut : LocalCutoffInput) (hbridge : AssemblyBridgeBounds) : AssemblyEnergyBounds :=
  assemblyEnergyBounds_of_local_inputs hmat hcut assemblySurvivorTailBounds_proof hbridge

theorem assemblyEnergyBounds_of_matrix_bridge (hmat : AssemblyMatrixBounds)
    (hbridge : AssemblyBridgeBounds) : AssemblyEnergyBounds :=
  assemblyEnergyBounds_of_pending_inputs hmat localCutoffInput_proof hbridge

/-- All analytic inputs except the old Schur bridge are discharged. -/
theorem assemblyEnergyBounds_of_bridge (hbridge : AssemblyBridgeBounds) :
    AssemblyEnergyBounds :=
  assemblyEnergyBounds_of_matrix_bridge assemblyMatrixBounds_proof hbridge

/-- All analytic assembly estimates are supplied by proved dependencies. -/
theorem assemblyEnergyBounds_proof : AssemblyEnergyBounds :=
  assemblyEnergyBounds_of_bridge assemblyBridgeBounds_proof

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assemblySurvivorTailBounds_proof
#print axioms AndersonAC.SolS78.assemblyEnergyBounds_of_pending_inputs
#print axioms AndersonAC.SolS78.localCutoffInput_proof
#print axioms AndersonAC.SolS78.assemblyEnergyBounds_of_matrix_bridge
#print axioms AndersonAC.SolS78.assemblyMatrixBounds_proof
#print axioms AndersonAC.SolS78.assemblyEnergyBounds_of_bridge
#print axioms AndersonAC.SolS78.assemblyBridgeBounds_proof
#print axioms AndersonAC.SolS78.assemblyEnergyBounds_proof
