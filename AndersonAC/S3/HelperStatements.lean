import AndersonAC.S3.Definitions

/-!
Frozen helper statements for WP05 (§3, Proposition 3.6), stated as `Prop`
definitions so that the lead's proofs can take them as hypotheses until the
helper proofs are integrated. Each helper proves `<name>_proof : <Name>Statement`
in its own module, importing only this file (and Mathlib).

Route summary (lead, opus-s3): the fixed point, `‖K‖` and the fourth-power
rows are reduced to (i) finite torus Fourier algebra, (ii) a grid-quadrature
bridge for Lipschitz compactly supported functions, (iii) polar integration
along Euclidean rays plus explicit one-dimensional ray estimates, and (iv) a
joint-shell volume bound from strongly convex hyperplane slices.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
open AndersonAC.Blueprint

namespace AndersonAC.S3

/-! ### H1: one-dimensional ray estimates (§3 Lemma 3.5, along one ray) -/

/-- Along one ray `r ↦ h r` with `h 0 = 0`, `c₁ r ≤ h' r ≤ C₂ r`, `|h''| ≤ C₂` on
`[0,ρ]` and `h ρ` above the energy range: the second resolvent power has only a
logarithmic integral (by integration by parts), the absolute first power is
logarithmic, the first power is bounded, and the imaginary part is bounded below.
The weight is `r ^ n` with `n ≥ 2` (that is, dimension `n + 1 ≥ 3`). -/
def RayEstimatesStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ c₁ C₂ ρ₁ ρ₂ β₁ β₂ μ : ℝ,
    0 < c₁ → 0 < ρ₁ → ρ₁ ≤ ρ₂ → 0 < β₁ → β₁ ≤ β₂ → 0 < μ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (h h' h'' : ℝ → ℝ) (ρ : ℝ), ρ₁ ≤ ρ → ρ ≤ ρ₂ → h 0 = 0 →
        (∀ r ∈ Set.Icc (0 : ℝ) ρ, HasDerivAt h (h' r) r ∧ HasDerivAt h' (h'' r) r ∧
          c₁ * r ≤ h' r ∧ h' r ≤ C₂ * r ∧ |h'' r| ≤ C₂) →
        β₂ + μ ≤ h ρ →
        ∀ β ∈ Set.Icc β₁ β₂, ∀ v : ℝ, 0 < v → v ≤ 1 →
          ‖∫ r in (0 : ℝ)..ρ, ((r ^ n : ℝ) : ℂ) *
              (((h r : ℂ) - β - v * Complex.I)⁻¹) ^ 2‖ ≤ C * Real.log (2 / v) ∧
          (∫ r in (0 : ℝ)..ρ, r ^ n * ‖((h r : ℂ) - β - v * Complex.I)⁻¹‖) ≤
            C * Real.log (2 / v) ∧
          ‖∫ r in (0 : ℝ)..ρ, ((r ^ n : ℝ) : ℂ) * ((h r : ℂ) - β - v * Complex.I)⁻¹‖ ≤ C ∧
          c ≤ ∫ r in (0 : ℝ)..ρ, r ^ n * (v / ((h r - β) ^ 2 + v ^ 2))

/-! ### H4: polar integration along Euclidean rays and the convex shell bound -/

/-- Integrals on `Fin d → ℝ` are controlled by uniform bounds on the weighted
integrals along Euclidean unit rays (polar coordinates; `σ` is the sphere area). -/
def PolarRayBoundStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ σ : ℝ, 0 < σ ∧
    (∀ (f : (Fin d → ℝ) → ℂ) (M : ℝ), Integrable f →
      (∀ ω : Fin d → ℝ, ∑ j, ω j ^ 2 = 1 →
        ‖∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * f (r • ω)‖ ≤ M) →
      ‖∫ k, f k‖ ≤ σ * M) ∧
    (∀ (f : (Fin d → ℝ) → ℝ) (M : ℝ), Integrable f → (∀ k, 0 ≤ f k) →
      (∀ ω : Fin d → ℝ, ∑ j, ω j ^ 2 = 1 →
        M ≤ ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * f (r • ω)) →
      σ * M ≤ ∫ k, f k)

/-- Tangential shell bound: a `c`-strongly convex function on `ℝ^q`, `q ≥ 2`,
with a global minimizer `y₀`, has energy shells of width `2s` inside the ball of
radius `R` about `y₀` of volume `O(R^(q-2) s / c)`, including tangential slices. -/
def ConvexShellStatement : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∃ C : ℝ, 0 < C ∧
    ∀ (g : EuclideanSpace ℝ (Fin q) → ℝ) (y₀ : EuclideanSpace ℝ (Fin q)) (c R β s : ℝ),
      0 < c → 0 < R → 0 < s → StrongConvexOn Set.univ c g → (∀ y, g y₀ ≤ g y) →
      volume {y | dist y y₀ ≤ R ∧ |g y - β| ≤ s} ≤ ENNReal.ofReal (C * R ^ (q - 2) * s / c)

/-! ### H5: slicing a slab by hyperplanes parallel to it -/

/-- Fubini across a slab `|b·x - c| ≤ w`: parametrize each hyperplane `b·x = τ` by the
coordinates other than `j₀` (where `b j₀ ≠ 0`). Uniform slice bounds `M` give
volume at most `2 w M / |b j₀|`. -/
def SlabSliceStatement : Prop :=
  ∀ (n : ℕ) (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (S : Set (Fin (n + 1) → ℝ))
    (c w M : ℝ), b j₀ ≠ 0 → MeasurableSet S → 0 ≤ w → 0 ≤ M →
    (∀ τ : ℝ, volume {x' : Fin n → ℝ |
        Fin.insertNth (α := fun _ => ℝ) j₀
          ((τ - ∑ i, b (j₀.succAbove i) * x' i) / b j₀) x' ∈ S} ≤ ENNReal.ofReal M) →
    volume {x | x ∈ S ∧ |∑ j, b j * x j - c| ≤ w} ≤ ENNReal.ofReal (2 * w * M / |b j₀|)

/-! ### H2: finite Fourier algebra on the discrete torus -/

/-- The free lattice Green matrix written by its Fourier series. -/
def freeGreen {d L : ℕ} [NeZero L] (z : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  fun x y => gridAvg (fun k : Torus d L =>
    character k (x - y) * ((dispersion (gridAngle k) : ℂ) - z)⁻¹)

/-- Translation-invariant (circulant) matrix with kernel `m`. -/
def circulant {d L : ℕ} (m : Torus d L → ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  fun x y => m (x - y)

/-- Exact inverse and diagonal of the free resolvent; circulant operator norms are
bounded by the symbol; Parseval for rows; the symbol of the squared Green kernel;
additivity of the centered grid angles modulo `2π`. -/
def TorusFourierStatement : Prop :=
  ∀ (d L : ℕ) [NeZero L], 4 ≤ L →
    (∀ z : ℂ, (∀ k : Torus d L, (dispersion (gridAngle k) : ℂ) ≠ z) →
      twoSidedInverse (freeHopping - z • (1 : Matrix (Torus d L) (Torus d L) ℂ))
        (freeGreen z) ∧
      ∀ x : Torus d L, freeGreen z x x =
        gridAvg (fun k : Torus d L => ((dispersion (gridAngle k) : ℂ) - z)⁻¹)) ∧
    (∀ (m : Torus d L → ℂ) (B : ℝ), (∀ ζ, ‖fourier m ζ‖ ≤ B) → opNorm (circulant m) ≤ B) ∧
    (∀ (m : Torus d L → ℂ) (x : Torus d L),
      ∑ y, ‖circulant m x y‖ ^ 2 = gridAvgReal (fun ζ => ‖fourier m ζ‖ ^ 2)) ∧
    (∀ z : ℂ, (∀ k : Torus d L, (dispersion (gridAngle k) : ℂ) ≠ z) → ∀ ζ : Torus d L,
      fourier (fun x => freeGreen z x 0 ^ 2) ζ =
        gridAvg (fun k : Torus d L => ((dispersion (gridAngle k) : ℂ) - z)⁻¹ *
          ((dispersion (gridAngle (ζ - k)) : ℂ) - z)⁻¹)) ∧
    (∀ (k ζ : Torus d L) (j : Fin d), ∃ n : ℤ,
      gridAngle (k + ζ) j = gridAngle k j + gridAngle ζ j + 2 * Real.pi * n) ∧
    (∀ (k : Torus d L) (j : Fin d), ∃ n : ℤ,
      gridAngle (-k) j = -gridAngle k j + 2 * Real.pi * n)

/-! ### H3: grid quadrature and the inverse-square frequency sum -/

/-- Grid averages of Lipschitz functions supported in the cube `[-2,2]^d` agree with
the normalized integral up to `O(K/L)`. -/
def GridQuadratureStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
    ∀ (f : (Fin d → ℝ) → ℂ) (K : ℝ≥0), LipschitzWith K f →
      (∀ k : Fin d → ℝ, (∃ j, 2 < |k j|) → f k = 0) →
      ‖gridAvg (fun k : Torus d L => f (gridAngle k)) -
          ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ∫ k, f k‖ ≤ C * K / L

/-- For `d ≥ 3`, the normalized sum of `|ζ|⁻²` over nonzero grid frequencies is
bounded uniformly in `L`. -/
def FrequencySumStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
    gridAvgReal (fun ζ : Torus d L =>
      if ζ = 0 then 0 else (radius (gridAngle ζ) ^ 2)⁻¹) ≤ C

end AndersonAC.S3
