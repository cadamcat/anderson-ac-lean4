import AndersonAC.S6.Scattering

/-! Exact WP08 package proof for coordinator integration. -/
namespace AndersonAC.Blueprint.Packages

theorem scattering : ScatteringInput := by
  intro N M G hM hreal t ht r hp hInv
  have h := AndersonAC.SolS6.scattering_from_inverse M G t r hM hreal
    (fun i => le_of_lt (hp i)) hInv
  exact h

end AndersonAC.Blueprint.Packages

#print axioms AndersonAC.Blueprint.Packages.scattering
