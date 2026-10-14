import AndersonAC.Blueprint.Certificate

/-!
Concrete reusable finite and probabilistic inputs. Matrix norms here are Euclidean
operator norms, not Mathlib's entrywise sup norm. The finite-run construction must
establish the schedule, geometry, and retained-history conditions separately.
-/

noncomputable section
open MeasureTheory OAI.Anderson ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

namespace AndersonAC.Blueprint

def opNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖

def matrixImag {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * Complex.I)⁻¹ • (A - A.conjTranspose)

def twoSidedInverse {n : Type*} [Fintype n] [DecidableEq n]
    (A G : Matrix n n ℂ) : Prop := A * G = 1 ∧ G * A = 1

/-- The §2 Ward identity and dissipativity. Schur-complement identities from Mathlib
are separate inputs. -/
def WardInput : Prop :=
  ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ), M.transpose = M →
    (∀ i j, (M i j).im = 0) → ∀ (t : ℝ), 0 < t →
      ∀ (r : Fin N → ℂ) (c : ℝ), 0 < c → (∀ i, c ≤ (r i).im) →
        ∃ G : Matrix (Fin N) (Fin N) ℂ,
          twoSidedInverse (M - (t : ℂ) • Matrix.diagonal r) G ∧
          G.transpose = G ∧ opNorm G ≤ (t * c)⁻¹ ∧
          (t : ℂ) • (G * Matrix.diagonal (fun i => ((r i).im : ℂ)) * G.conjTranspose) =
            matrixImag G

abbrev BitSpace := ℕ → Bool

def bitLaw : Measure BitSpace :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

def binaryTail (h : ℕ) (ε : BitSpace) : ℝ :=
  ∑' n : ℕ, (if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)

/-- The uniform series law and independence of untouched tails. This independence
alone does not imply adaptive freshness after retained queries; that requires the
chronological query argument. -/
def BinaryInput : Prop :=
  ∀ h : ℕ, Measurable (binaryTail h) ∧
    bitLaw.map (binaryTail h) = uniformInterval (-((2 : ℝ)⁻¹ ^ h)) ((2 : ℝ)⁻¹ ^ h) ∧
    IndepFun (fun ε : BitSpace => fun i : Fin h => ε i) (binaryTail h) bitLaw

def entrywiseSquare {n : Type*} (A : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => A i j ^ 2

/-- Scalar self-consistency and the two startup smallness bounds in Proposition 3.6.
The Fourier, charge, cube, and inverse-form comparison estimates are separate inputs. -/
def InitializationInput (e₂ : ℝ) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ (cutoff : ℕ) (c C : ℝ), 0 < c ∧ c ≤ C ∧
    ∀ n₀ m : ℕ, cutoff ≤ n₀ → 4 * n₀ ≤ m →
      ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E ∈ energyWindow d e₂,
        ∃ (r : ℂ) (G : Matrix (Torus d m) (Torus d m) ℂ),
          ‖r‖ ≤ C ∧ c ≤ r.im ∧
          twoSidedInverse
            (periodicHamiltonian 0 (fun _ => ⟨0, by norm_num⟩) - (E : ℂ) • 1 -
              ((scaleHeight n₀ u + scaleHeight m u : ℝ) : ℂ) • Matrix.diagonal (fun _ => r)) G ∧
          (∀ i, G i i = r) ∧
          opNorm (entrywiseSquare ((Real.sqrt (scaleHeight n₀ u + scaleHeight m u) : ℂ) • G)) ≤
            1 / 10 ∧
          ∀ i, (∑ j, ‖(Real.sqrt (scaleHeight n₀ u + scaleHeight m u) : ℂ) * G i j‖ ^ 4) ≤
            (1 / 10 : ℝ) * (scaleHeight n₀ u + scaleHeight m u) ^ (1 + (1 / 100 : ℝ))

def matrixCondExp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : MeasurableSpace Ω) {N : ℕ} (Y : Ω → Matrix (Fin N) (Fin N) ℂ) :
    Ω → Matrix (Fin N) (Fin N) ℂ :=
  fun ω i j => μ[fun ω => Y ω i j | m] ω

/-- concentration package: Golden–Thompson and the scalar predictable-envelope form of Lemma
5.6. Positive J,V avoid the paper's separate zero-variance convention.
`Y k` is the increment from time k to k+1; `v k` is ℱ k-measurable. -/
structure ConcentrationInput : Prop where
  goldenThompson : ∀ (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ),
    A.IsHermitian → B.IsHermitian →
      (Matrix.trace (NormedSpace.exp (A + B))).re ≤
        (Matrix.trace (NormedSpace.exp A * NormedSpace.exp B)).re
  maximal : ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω),
      IsProbabilityMeasure μ →
      ∀ (N : ℕ) (ℱ : Filtration ℕ mΩ)
        (Y : ℕ → Ω → Matrix (Fin N) (Fin N) ℂ) (v : ℕ → Ω → ℝ) (J V : ℝ),
        0 < J → 0 < V →
        (∀ k, @StronglyMeasurable Ω (Matrix (Fin N) (Fin N) ℂ) _ (ℱ (k + 1)) (Y k)) →
        (∀ k i j, Integrable (fun ω => Y k ω i j) μ) →
        (∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian ∧ opNorm (Y k ω) ≤ J) →
        (∀ k, matrixCondExp μ (ℱ k) (Y k) =ᵐ[μ] 0) →
        (∀ k, @Measurable Ω ℝ (ℱ k) _ (v k)) →
        (∀ k, ∀ᵐ ω ∂μ, 0 ≤ v k ω ∧
          ((v k ω : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
            matrixCondExp μ (ℱ k) (fun ω => Y k ω * Y k ω) ω).PosSemidef) →
        (∀ᵐ ω ∂μ, ∀ n, (∑ k ∈ Finset.range n, v k ω) ≤ V) →
        ∀ a : ℝ, 0 < a →
          μ {ω | ∃ n : ℕ, a < opNorm (∑ k ∈ Finset.range n, Y k ω)} ≤
            ENNReal.ofReal (2 * (N : ℝ) * Real.exp (-c * min (a ^ 2 / V) (a / J)))

/-- The exact one-site inverse update used before the moment, lag, K, Laplacian,
row-proxy, localization, and trial estimates. This formula uses transpose, not
conjugate transpose. -/
def DeletionInput : Prop :=
  ∀ (N : ℕ) (A G : Matrix (Fin N) (Fin N) ℂ), twoSidedInverse A G →
    ∀ (x : Fin N) (v : ℂ), 1 + v * G x x ≠ 0 →
      twoSidedInverse (A + Matrix.diagonal (fun i => if i = x then v else 0))
        (fun i j => G i j - v * G i x * G x j / (1 + v * G x x))

def scattering {N : ℕ} (t : ℝ) (r : Fin N → ℂ) (G : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  1 + (2 * Complex.I * (t : ℂ)) •
    (Matrix.diagonal (fun i => (Real.sqrt (r i).im : ℂ)) * G *
      Matrix.diagonal (fun i => (Real.sqrt (r i).im : ℂ)))

/-- The algebraic scattering identity from §6.1. Full-range localization, ridge drift
(Lemma 6.4), heat count, preparation trial, and deterministic completion are separate
results; they do not follow from this identity. -/
def ScatteringInput : Prop :=
  ∀ (N : ℕ) (M G : Matrix (Fin N) (Fin N) ℂ), M.transpose = M →
    (∀ i j, (M i j).im = 0) → ∀ t : ℝ, 0 < t →
      ∀ r : Fin N → ℂ, (∀ i, 0 < (r i).im) →
        twoSidedInverse (M - (t : ℂ) • Matrix.diagonal r) G →
          (scattering t r G).transpose = scattering t r G ∧
          scattering t r G * (scattering t r G).conjTranspose = 1

/-- Reset existence contract at the contraction join. Proposition 7.4 supplies the
mapping and contraction estimates; geometry and assembly are separate hypotheses. -/
def ResetInput : Prop :=
  ∀ (N : ℕ) (F : (Fin N → ℂ) → Fin N → ℂ) (r : Fin N → ℂ) (ρ : ℝ), 0 < ρ →
    (∀ z, ‖z - r‖ ≤ ρ → ‖F z - r‖ ≤ ρ) →
    (∀ z w, ‖z - r‖ ≤ ρ → ‖w - r‖ ≤ ρ → ‖F z - F w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖) →
    ∃ z, ‖z - r‖ ≤ ρ ∧ F z = z

end AndersonAC.Blueprint
