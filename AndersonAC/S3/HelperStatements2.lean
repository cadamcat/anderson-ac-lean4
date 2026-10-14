import AndersonAC.S3.Definitions

/-!
Second batch of frozen helper statements for WP05 (§3, Proposition 3.6),
lead agent-s3. Each helper proves `<name>_proof : <Name>Statement` (or the stated
implication) in its own module importing only this file, `HelperStatements` and Mathlib.

Route (lead): the fixed point, `‖K‖ ≤ 1/10` and the fourth-power rows are reduced to
(i) continuum bounds near the band bottom (`BottomResolventStatement`, from the ray and
polar helpers), (ii) grid quadrature for Lipschitz functions on the full frequency cube
(`PeriodicGridQuadratureStatement`), (iii) the joint-shell volume in `k` coordinates
(`JointShellKStatement`, transferred from the sliced coordinates), and (iv) a dyadic
layer-cake bound for products of two truncated reciprocals (`LayerCakeStatement`).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace AndersonAC.S3

/-- The fundamental frequency cube `[-π, π)^d`. -/
def torusCube (d : ℕ) : Set (Frequency d) :=
  Set.pi Set.univ (fun _ => Set.Ico (-Real.pi) Real.pi)

/-! ### H6: dyadic layer cake for a product of truncated reciprocals -/

/-- If the joint sublevel sets of `|φ₁|, |φ₂|` on `Ω` have measure at most
`V s₁ s₂`, and both are bounded by `S` on `Ω`, then the integral of
`1/(max(|φ₁|,v) max(|φ₂|,v))` over `Ω` is `O(V log²(S/v))`. Route: on `Ω`,
`1/max(|φ|,v) ≤ ∑_{i=0}^{N} (2/s_i) 1{|φ| ≤ s_i}` with `s_i = v 2^i`,
`N = ⌈log₂(S/v)⌉`; multiply, integrate termwise, sum `(N+1)²` terms of size `4V`. -/
def LayerCakeStatement : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (Ω : Set X) (φ₁ φ₂ : X → ℝ) (V S v : ℝ),
    MeasurableSet Ω → Measurable φ₁ → Measurable φ₂ → 0 ≤ V → 0 < v → v ≤ S →
    (∀ x ∈ Ω, |φ₁ x| ≤ S ∧ |φ₂ x| ≤ S) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ →
      μ {x | x ∈ Ω ∧ |φ₁ x| ≤ s₁ ∧ |φ₂ x| ≤ s₂} ≤ ENNReal.ofReal (V * s₁ * s₂)) →
    ∫⁻ x in Ω, ENNReal.ofReal ((max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹) ∂μ ≤
      ENNReal.ofReal (16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2)

/-! ### H7: grid quadrature on the full frequency cube -/

/-- For even `L`, the grid angles are the lower corners of the `L^d` cells of side
`2π/L` tiling `[-π,π)^d`; hence the grid average of a `K`-Lipschitz function (sup
metric on `Fin d → ℝ`) equals its normalized cube integral up to `C K / L`.
No support or periodicity assumption is needed. -/
def PeriodicGridQuadratureStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L →
    ∀ (f : Frequency d → ℂ) (K : ℝ≥0), LipschitzWith K f →
      ‖gridAvg (fun k : Torus d L => f (gridAngle k)) -
          ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ∫ k in torusCube d, f k‖ ≤ C * K / L

/-! ### H8: continuum resolvent bounds near the band bottom (Lemma 3.5) -/

/-- Lemma 3.5 of §3 in the form used by the lead (unnormalized cube integrals,
excess energy `β`, imaginary part `v`): the absolute first power is logarithmic,
the first power is bounded, its imaginary part is bounded below, and the second
power is logarithmic, the last uniformly for perturbed amplitudes `|a_j - 1| ≤ ε`
and arbitrary phases `φ`. Intended route: conditional on the ray and polar helpers
(`RayEstimatesStatement`, `PolarRayBoundStatement` in `HelperStatements`); split the
cube into the Euclidean ball of radius `3/10` (polar coordinates, rays
`h(r) = ℓ(rω)` or its perturbed analogue after translating the phases away using
`2π`-periodicity) and its complement, where `dispersion + 2d - β ≥ 1/100`. -/
def BottomResolventStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ β₁ β₂ : ℝ, 0 < β₁ → β₁ ≤ β₂ → β₂ ≤ 1 / 50 →
    ∃ ε C c : ℝ, 0 < ε ∧ 0 < C ∧ 0 < c ∧
      ∀ β ∈ Set.Icc β₁ β₂, ∀ v : ℝ, 0 < v → v ≤ 1 →
        (∫ k in torusCube d,
            ‖(((dispersion k + 2 * d - β : ℝ) : ℂ) - v * Complex.I)⁻¹‖) ≤
          C * Real.log (2 / v) ∧
        ‖∫ k in torusCube d, (((dispersion k + 2 * d - β : ℝ) : ℂ) - v * Complex.I)⁻¹‖ ≤ C ∧
        c ≤ ∫ k in torusCube d, v / ((dispersion k + 2 * d - β) ^ 2 + v ^ 2) ∧
        ∀ a φ : Frequency d, (∀ j, |a j - 1| ≤ ε) →
          ‖∫ k in torusCube d,
              ((((perturbedDispersion a φ k + 2 * d - β : ℝ) : ℂ) - v * Complex.I)⁻¹) ^ 2‖ ≤
            C * Real.log (2 / v)

/-! ### H9: the joint shell in the original frequency coordinates -/

/-- The conclusion of the lead's `joint_shell_volume` (sliced coordinates
`x_j = sin(k_j + ζ_j/2)`), stated for every `n ≥ 2`. -/
def JointShellXStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ ζ : Frequency (n + 1), (∀ j, |ζ j| ≤ 1 / 2) →
    ∀ j₀ : Fin (n + 1), ζ j₀ ≠ 0 → ∀ E s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ →
      volume {x : Frequency (n + 1) | (∀ j, |x j| ≤ 1 / 4) ∧
          |slicedDispersion (-1) ζ x - E| ≤ s₁ ∧ |slicedDispersion 1 ζ x - E| ≤ s₂} ≤
        ENNReal.ofReal (C * s₁ * s₂ / |ζ j₀|)

/-- Joint shell volume near the band bottom in `k` coordinates. Route: on the set,
`|ζ_j| ≤ 0.42`; with `θ = k + ζ/2` (translation) one has `|θ_j| ≤ 0.21`,
`dispersion k = slicedDispersion (-1) ζ (sin ∘ θ)` and
`dispersion (k+ζ) = slicedDispersion 1 ζ (sin ∘ θ)`; the `θ`-set is the image of
the sliced joint set under coordinatewise `arcsin`, which is `2`-Lipschitz on
`[-1/4,1/4]` (sup metric); compare volumes via `LipschitzOnWith.hausdorffMeasure_image_le`
and `hausdorffMeasure_pi_real`. -/
def JointShellKStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ ζ : Frequency d, ∀ j₀ : Fin d, ζ j₀ ≠ 0 →
    ∀ E s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ →
      volume {k : Frequency d | (∀ j, |k j| ≤ 21 / 100) ∧ (∀ j, |k j + ζ j| ≤ 21 / 100) ∧
          |dispersion k - E| ≤ s₁ ∧ |dispersion (k + ζ) - E| ≤ s₂} ≤
        ENNReal.ofReal (C * s₁ * s₂ / |ζ j₀|)

end AndersonAC.S3
