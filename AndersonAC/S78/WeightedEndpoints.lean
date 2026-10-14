import AndersonAC.S3WCube.Weighted
import AndersonAC.S78Local.WeightedLocalEnergy
import AndersonAC.S78Deviation.Deviation

/-! The proved §3 weighted-cube endpoint discharges the analytic hypothesis
of both local-energy transports. No §3 statement placeholder is used. -/
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

theorem weighted_local_energy_proof (d : ℕ) (hd : 3 ≤ d) :
    type_of% (AndersonAC.SolS78Local.weighted_local_energy_of_cube_endpoint d hd
      (AndersonAC.AgentS3.weighted_cube_proof hd)) :=
  AndersonAC.SolS78Local.weighted_local_energy_of_cube_endpoint d hd
    (AndersonAC.AgentS3.weighted_cube_proof hd)

theorem localDeviationInput_proof : LocalDeviationInput :=
  AndersonAC.SolS78Deviation.localDeviationInput_of_weightedCube
    (fun _ hd => AndersonAC.AgentS3.weighted_cube_proof hd)

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.weighted_local_energy_proof
#print axioms AndersonAC.SolS78.localDeviationInput_proof
