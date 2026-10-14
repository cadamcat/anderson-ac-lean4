import AndersonAC.S3.HelperStatements

/-!
Frozen statement (lead agent-s3) for the circulant calculus on the discrete torus
used by the inverse-form comparators of Proposition 3.6 (§3, lines 690–735):
quadratic forms, Parseval, inverses, the mean projection, the Laplacian and the
squared-modulus Green kernel are all diagonalized by the (unnormalized) Fourier
transform `fourier`. Characters: `character k x = exp(i Σ_j gridAngle k j · (x j).val)`
is a group character in `x` (the grid angle is `2π m/L` with `m ≡ k (mod L)`).
-/

noncomputable section
open scoped BigOperators

namespace AndersonAC.S3

/-- Finite Fourier calculus for circulant matrices on `Torus d L`. -/
def CirculantCalculusStatement : Prop :=
  ∀ (d L : ℕ) [NeZero L], 4 ≤ L →
    -- (1) quadratic forms of circulants
    (∀ (m y : Torus d L → ℂ),
      form (circulant m) y = gridAvgReal (fun ζ => (fourier m ζ).re * ‖fourier y ζ‖ ^ 2)) ∧
    -- (2) Parseval
    (∀ y : Torus d L → ℂ, normSq y = gridAvgReal (fun ζ => ‖fourier y ζ‖ ^ 2)) ∧
    -- (3) neutrality is the vanishing zero mode
    (∀ y : Torus d L → ℂ, fourier y 0 = ∑ x, y x) ∧
    -- (4) Fourier transform is bijective and turns products of circulants into products
    (∀ s : Torus d L → ℂ, ∃ m : Torus d L → ℂ, ∀ ζ, fourier m ζ = s ζ) ∧
    (∀ m m' : Torus d L → ℂ, (∀ ζ, fourier m ζ = fourier m' ζ) → m = m') ∧
    (∀ m m' : Torus d L → ℂ, ∃ m'' : Torus d L → ℂ,
      circulant m * circulant m' = circulant m'' ∧
      ∀ ζ, fourier m'' ζ = fourier m ζ * fourier m' ζ) ∧
    (∀ m : Torus d L → ℂ, (∀ ζ, fourier m ζ = 1) → circulant m = 1) ∧
    (∀ m m' : Torus d L → ℂ, circulant m + circulant m' = circulant (m + m') ∧
      ∀ ζ, fourier (m + m') ζ = fourier m ζ + fourier m' ζ) ∧
    (∀ (c : ℂ) (m : Torus d L → ℂ), c • circulant m = circulant (c • m) ∧
      ∀ ζ, fourier (c • m) ζ = c * fourier m ζ) ∧
    -- (5) Hermitian circulants
    (∀ m : Torus d L → ℂ, (∀ ζ, (fourier m ζ).im = 0) → (circulant m).conjTranspose = circulant m) ∧
    -- (6) the mean projection
    (meanProjection (Torus d L) = circulant (fun _ => ((Fintype.card (Torus d L) : ℂ))⁻¹) ∧
      ∀ ζ, fourier (fun _ : Torus d L => ((Fintype.card (Torus d L) : ℂ))⁻¹) ζ =
        if ζ = 0 then 1 else 0) ∧
    -- (7) the Laplacian
    (∃ m : Torus d L → ℂ, laplacian = circulant m ∧
      ∀ ζ, fourier m ζ = (laplacianSymbol (gridAngle ζ) : ℂ)) ∧
    -- (8) the squared modulus of the free Green kernel
    (∀ z : ℂ, (∀ k : Torus d L, (dispersion (gridAngle k) : ℂ) ≠ z) → ∀ ζ : Torus d L,
      fourier (fun x => ((‖freeGreen z x 0‖ ^ 2 : ℝ) : ℂ)) ζ =
        gridAvg (fun k : Torus d L => star (((dispersion (gridAngle k) : ℂ) - z)⁻¹) *
          ((dispersion (gridAngle (k + ζ)) : ℂ) - z)⁻¹))

end AndersonAC.S3
