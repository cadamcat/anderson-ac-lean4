import AndersonAC.S9Inf.ReadoutDefinitions

/-! The remaining all-sites input definitions copied verbatim from the frozen inventory. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

namespace AndersonAC.S9

def halfProbabilityCertificates (d : ℕ) (coupling : ℝ) (I : Set ℝ) : Prop :=
  ∃ (b : CertificateBounds) (η : ℕ → ℝ), comparableHeights η ∧
    ∀ E ∈ I, ∀ᶠ m in atTop,
      (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (trueCertificateEvent d m coupling E (η m) b)

abbrev BoundaryTheory := AndersonAC.Blueprint.BoundaryInput

structure ResolvedAnderson (d : ℕ) (coupling : ℝ) where
  resolved : ∀ ω : Configuration d,
    AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω)
  measure_measurable : ∀ x : Site d, ∀ B : Set ℝ, MeasurableSet B →
    Measurable (fun ω => (resolved ω).spectral.vectorMeasure (siteVector x) B)

def allSitesPositive {d : ℕ} (coupling : ℝ) (E : ℝ) (ω : Configuration d) : Prop :=
  ∀ x : Site d, positiveBoundary (diagonalGreen coupling ω x) E

end AndersonAC.S9
