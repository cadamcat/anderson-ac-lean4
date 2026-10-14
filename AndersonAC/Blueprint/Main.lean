import AndersonAC.Blueprint.Interfaces
import AndersonAC.Spectral.SpectralProof
import AndersonAC.Transport.Law
import AndersonAC.Transport.Sign
import AndersonAC.Transport.Spectral
import AndersonAC.Bridge.Bridge
import AndersonAC.S2.WardPackage
import AndersonAC.BoundaryFinite.Package
import AndersonAC.Prob.Binary
import AndersonAC.S45.ConcentrationPackageProof
import AndersonAC.S45.Deletion
import AndersonAC.S6.Package
import AndersonAC.S9.AveragingPackage
import AndersonAC.S9.ReadoutPackage
import AndersonAC.S78.Reset
import AndersonAC.S9.PurityPackage
import AndersonAC.S3.InitializationPackage
import AndersonAC.S78.CertificatesPackage

/-! Assembly of the final theorem from the package theorems. Every package is proved;
`Audit.lean` prints the axioms of `anderson_challenge` and of each package. -/

namespace AndersonAC.Blueprint

theorem paperTheorem_blueprint : PaperTheorem := by
  obtain ⟨e₂, he, hi⟩ := Packages.initialization
  have hcert := Packages.certificates he Packages.ward Packages.binary hi
    Packages.concentration Packages.deletion Packages.scattering Packages.reset
  exact paperTheorem_of_packages he hcert Packages.spectral Packages.boundary
    Packages.averaging Packages.readout Packages.purity

theorem simonProblem_blueprint : SimonProblem :=
  simonProblem_of_paper paperTheorem_blueprint Packages.lawTransport
    Packages.signTransport Packages.spectralTransport

/-- The final target: Simon's Problem 1 in independent Mathlib-only form. -/
theorem anderson_challenge : AndersonChallenge.Statement :=
  Packages.challengeBridge simonProblem_blueprint

end AndersonAC.Blueprint
