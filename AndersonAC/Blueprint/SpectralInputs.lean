import AndersonAC.Blueprint.Certificate

/-! Stable spectral joins. These are propositions to prove, not axioms. -/

noncomputable section
open MeasureTheory OAI.Anderson Filter
open scoped ENNReal lp Topology

namespace AndersonAC.Blueprint

/-- Construct the bounded PVM, OAI fields, and resolvent identity. -/
def SpectralInput : Prop :=
  ∀ (d : ℕ) (T : Operator d), IsSelfAdjoint T → Nonempty (ResolvedOperator T)

def HasBoundary (f : ℂ → ℂ) (E : ℝ) (w : ℂ) : Prop :=
  Tendsto (fun η : ℝ => f ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 w)

def FinitePositiveBoundary (f : ℂ → ℂ) (E : ℝ) : Prop :=
  ∃ w : ℂ, HasBoundary f E w ∧ 0 < w.im

/-- Finite boundary values on S imply AC of μ restricted to S.
This stronger-than-needed export follows from the bounded-limsup criterion. -/
def BoundedBoundaryCriterion : Prop :=
  ∀ μ : Measure ℝ, IsFiniteMeasure μ → ∀ S : Set ℝ, MeasurableSet S →
    (∀ E ∈ S, ∃ w : ℂ, HasBoundary (borelTransform μ) E w) →
    μ.restrict S ≪ volume

/-- Teschl 3.25, the bounded-boundary criterion, and uniqueness for differences of
scalar Borel transforms. Analytic uniqueness is used after proving the off-diagonal
transform is not identically zero. -/
structure BoundaryInput : Prop where
  finite : ∀ μ : Measure ℝ, IsFiniteMeasure μ →
    ∀ᵐ E ∂(volume : Measure ℝ), ∃ w : ℂ, HasBoundary (borelTransform μ) E w
  criterion : BoundedBoundaryCriterion
  difference_nonzero : ∀ μ ν : Measure ℝ, IsFiniteMeasure μ → IsFiniteMeasure ν →
    (∃ z : ℂ, 0 < z.im ∧ borelTransform μ z - borelTransform ν z ≠ 0) →
    ∀ᵐ E ∂(volume : Measure ℝ), ∃ w : ℂ,
      HasBoundary (fun z => borelTransform μ z - borelTransform ν z) E w ∧ w ≠ 0

def delta {d : ℕ} (x : Site d) : StateSpace d := lp.single 2 x (1 : ℂ)

def diagonalGreen {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x : Site d) (z : ℂ) : ℂ :=
  inner ℂ (delta x) (greenOperator (hamiltonian coupling ω) z (delta x))

/-- Energy almost everywhere precedes configuration almost everywhere here. Fubini
reverses the order and gives an exceptional set independent of the own-site value. -/
def BoundaryPositive (d : ℕ) (coupling : ℝ) (I : Set ℝ) : Prop :=
  ∀ᵐ E ∂(volume.restrict I), ∀ᵐ ω ∂disorderLaw d,
    ∀ x : Site d, FinitePositiveBoundary (diagonalGreen coupling ω x) E

/-- Spectral averaging for a rank-one site change. The supplied resolutions must
satisfy all OAI fields; no averaging identity is assumed. A uniform interval avoids
choosing an essential-supremum representative. The arbitrary `T` is the fixed
complementary operator. -/
def AveragingInput : Prop :=
  ∀ (d : ℕ) (T : Operator d), IsSelfAdjoint T →
    ∀ v : StateSpace d, ‖v‖ = 1 → ∀ a b : ℝ, a < b →
      ∀ S : ∀ s : ℝ, SpectralResolution
        (T + (s : ℂ) • InnerProductSpace.rankOne ℂ v v),
      ∀ B : Set ℝ, MeasurableSet B →
        (∫⁻ s : ℝ, (S s).vectorMeasure v B ∂uniformInterval a b) ≤
          (ENNReal.ofReal (b - a))⁻¹ * volume B

/-- Proposition 9.2 through fixed-energy all-site positivity.
Includes finite principal invertibility, rank cut, Wegner, Combes–Thomas,
boundary nonvanishing, iid ergodicity, and rank-one propagation. -/
def ReadoutInput : Prop :=
  SpectralInput → BoundaryInput → AveragingInput →
    ∀ (d : ℕ), 3 ≤ d → ∀ coupling : ℝ, 0 < coupling →
      ∀ I : Set ℝ, IsOpen I → I.Nonempty → Bornology.IsBounded I →
        WeakCertificates d coupling I → BoundaryPositive d coupling I

/-- The §9 purity conclusions, including own-site-independent null sets,
singular-mass removal, closed AC subspace, spectrum, and nonzero projection. -/
def PurityInput : Prop :=
  SpectralInput → BoundaryInput → AveragingInput →
    ∀ (d : ℕ), 3 ≤ d → ∀ coupling : ℝ, 0 < coupling →
      ∀ I : Set ℝ, IsOpen I → I.Nonempty → Bornology.IsBounded I →
        BoundaryPositive d coupling I →
          ∀ᵐ ω ∂disorderLaw d, ACRegion (hamiltonian coupling ω) I

end AndersonAC.Blueprint
