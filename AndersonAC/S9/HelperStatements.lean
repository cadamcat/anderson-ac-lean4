import AndersonAC.S9.Core
import AndersonAC.S9.OwnSite
import AndersonAC.S9.Statements

/-! Exact helper contracts for the phase dispatcher. Definitions are
propositions, not assumed proofs. Keep each contract unchanged after its
; return a theorem with the corresponding `_proof` name. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

namespace AndersonAC.SolS9

/-- Required by `AveragingInput`, which accepts any supplied
resolution, rather than only spectral package's selected constructed resolution. -/
def ResolutionTransformInput : Prop :=
  ∀ (d : ℕ) (T : StateSpace d →L[ℂ] StateSpace d), IsSelfAdjoint T →
    ∀ S : SpectralResolution T, ∀ (v : StateSpace d) (z : ℂ), 0 < z.im →
      inner ℂ v (AndersonAC.Blueprint.greenOperator T z v) =
        AndersonAC.Blueprint.borelTransform (S.vectorMeasure v) z

/-- Joint measurability at positive heights, needed before conditional
Fubini. The configuration-to-operator map should be handled in the strong
operator topology, not claimed to be continuous in operator norm. -/
def DiagonalGreenMeasurableInput : Prop :=
  ∀ (d : ℕ) (coupling : ℝ) (x : Site d),
    Measurable (fun p : Configuration d × {z : ℂ // 0 < z.im} =>
      AndersonAC.Blueprint.diagonalGreen coupling p.1 x p.2)

/-- The OAI moment/support fields force the basis measures to be
measurable under the product potential law, even for a supplied family of
resolutions. This supplies the scalar measure kernel used in conditional
averaging of complement-dependent energy sets. -/
def BasisMeasureMeasurableInput : Prop :=
  ∀ (d : ℕ) (coupling : ℝ)
    (S : ∀ ω : Configuration d, SpectralResolution (hamiltonian coupling ω))
    (x : Site d) (A : Set ℝ), MeasurableSet A →
      Measurable (fun ω => (S ω).vectorMeasure (siteVector x) A)

/-- Countable rational-height tests and continuity at positive heights
make the full vertical-boundary conditions Borel in their parameters. -/
def BoundarySetMeasurableInput : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (g : Ξ → ℝ → ℝ → ℂ),
    (∀ η : ℝ, 0 < η → Measurable (fun p : Ξ × ℝ => g p.1 p.2 η)) →
    (∀ ξ E, ContinuousOn (g ξ E) (Set.Ioi (0 : ℝ))) →
    MeasurableSet {p : Ξ × ℝ | ∃ w : ℂ, Tendsto (g p.1 p.2) (𝓝[>] 0) (𝓝 w)} ∧
      MeasurableSet {p : Ξ × ℝ | ∃ w : ℂ,
        Tendsto (g p.1 p.2) (𝓝[>] 0) (𝓝 w) ∧ 0 < w.im}

/-- Freeze the complement and then average the true own-site value. -/
def RestoreSiteLawInput : Prop :=
  ∀ (d : ℕ) (x : Site d),
    MeasurePreserving
      (fun p : ComplementConfiguration d x × SingleSite => restoreSite x p.1 p.2)
      ((complementLaw d x).prod uniformSite) (disorderLaw d)

/-- The adaptive finite-volume comparison from §9:178–288. The complete
matrix, cutoff, norm and certificate definitions are the concrete,
placeholder-free definitions in Statements.lean's Planned namespace. -/
def FiniteCutComparisonInput : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ε : ℝ)
    (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (b : Planned.CertificateBounds)
    (hprincipal : Planned.allPrincipalInvertible H E)
    (hcert : Planned.matrixCertificate H E η b),
      Planned.finite_cut_comparison H hH E η ε hη hε b hprincipal hcert

/-- A uniform Poisson bound orders the underlying finite measure with
the sharp Lebesgue constant. Used after constructing the averaged measure
in Lemma 9.1; no operator or rank-one hypothesis enters this measure lemma. -/
def BoundedPoissonMeasureInput : Prop :=
  ∀ (μ : Measure ℝ), IsFiniteMeasure μ → ∀ C : ℝ, 0 ≤ C →
    (∀ E η : ℝ, 0 < η →
      (AndersonAC.Blueprint.borelTransform μ ((E : ℂ) + η * Complex.I)).im ≤ Real.pi * C) →
    μ ≤ ENNReal.ofReal C • volume

/-- Compact moment data determine a measurable probability kernel.
Uniform support is essential to this contract. -/
def CompactMomentKernelInput : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Ξ → Measure ℝ) (M : ℝ), 0 ≤ M →
    (∀ ξ, IsProbabilityMeasure (μ ξ)) →
    (∀ ξ, μ ξ (Set.Icc (-M) M)ᶜ = 0) →
    (∀ n : ℕ, Measurable (fun ξ => ∫ t : ℝ, t ^ n ∂μ ξ)) →
    ∀ A : Set ℝ, MeasurableSet A → Measurable (fun ξ => μ ξ A)

def BasisMeasureMeasurableJoin : Prop :=
  CompactMomentKernelInput → BasisMeasureMeasurableInput

def DiagonalGreenMeasurableJoin : Prop :=
  AndersonAC.Blueprint.SpectralInput → BasisMeasureMeasurableInput →
    DiagonalGreenMeasurableInput

end AndersonAC.SolS9
