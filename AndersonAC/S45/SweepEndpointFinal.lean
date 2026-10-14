import AndersonAC.S45.EndpointAssembly
import AndersonAC.S45.FormDualityProof

/-! Unconditional `ordinary_sweep_endpoint`: the last input, `schur_dual_transport`, is
proved in `FormDualityProof` (argon-s45dual 26c8442, continuing luna-s45dual). -/

namespace AndersonAC.AgentS45

theorem schurDualTransport_holds : SchurDualTransportStmt :=
  fun P _ _ => @schur_dual_transport_proof P _ _

theorem ordinary_sweep_endpoint_proof :
    type_of% (ordinary_sweep_endpoint_of_dual schurDualTransport_holds) :=
  ordinary_sweep_endpoint_of_dual schurDualTransport_holds

end AndersonAC.AgentS45
