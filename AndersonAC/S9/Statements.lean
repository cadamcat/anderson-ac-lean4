import AndersonAC.Blueprint.Transport

/-! Proposition-valued definitions for the spectral conclusions in
`09-spectral.tex`. This module states the obligations independently of their
proofs and records the interfaces used by the package theorems.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace AndersonAC.SolS9.Planned

open OAI.Anderson

/-- Paper convention `(T - z)⁻¹`, opposite to `spectrum.resolvent T z`. -/
def operatorResolvent {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : K →L[ℂ] K) (z : ℂ) : K →L[ℂ] K :=
  Ring.inverse (T - z • (1 : K →L[ℂ] K))

def borelTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  AndersonAC.Blueprint.borelTransform μ z

def verticalBoundary (g : ℂ → ℂ) (E : ℝ) (w : ℂ) : Prop :=
  AndersonAC.Blueprint.HasBoundary g E w

def finiteBoundary (g : ℂ → ℂ) (E : ℝ) : Prop :=
  ∃ w : ℂ, verticalBoundary g E w

def positiveBoundary (g : ℂ → ℂ) (E : ℝ) : Prop :=
  AndersonAC.Blueprint.FinitePositiveBoundary g E

def cauchyKernel (a v s : ℝ) : ℝ := v / ((s - a) ^ 2 + v ^ 2)

def densityLaw (ρ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun s => ENNReal.ofReal (ρ s))

def uniformOwnSite (coupling : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * coupling))⁻¹ • volume.restrict (Set.Icc (-coupling) coupling)

section Cavity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def blockHamiltonian (Hc : K →L[ℂ] K) (b : K) (s : ℝ) :
    (ℂ × K) →L[ℂ] (ℂ × K) :=
  (((s : ℂ) • ContinuousLinearMap.fst ℂ ℂ K) +
    (innerSL ℂ b).comp (ContinuousLinearMap.snd ℂ ℂ K)).prod
    ((ContinuousLinearMap.toSpanSingleton ℂ b).comp (ContinuousLinearMap.fst ℂ ℂ K) +
      Hc.comp (ContinuousLinearMap.snd ℂ ℂ K))

def cavityM (Hc : K →L[ℂ] K) (b : K) (z : ℂ) : ℂ :=
  z + inner ℂ b (operatorResolvent Hc z b)

/-- Scalar spectral theorem input for the block operator. The product uses
the ordinary product norm; the measure correspondence is a separate input. -/
structure BlockSpectralData (Hc : K →L[ℂ] K) (b : K) where
  measure : ℝ → Measure ℝ
  probability : ∀ s, IsProbabilityMeasure (measure s)
  measurable : ∀ B : Set ℝ, MeasurableSet B → Measurable (fun s => measure s B)
  transform_eq : ∀ s z, 0 < z.im → borelTransform (measure s) z =
    (operatorResolvent (blockHamiltonian Hc b s) z (1, 0)).1

/-- Equation (9.2), using the resolvent identity in block form. -/
def spectral_cavity (Hc : K →L[ℂ] K) (b : K) (hHc : IsSelfAdjoint Hc)
    (s : ℝ) (z : ℂ) (hz : 0 < z.im) : Prop :=
  (operatorResolvent (blockHamiltonian Hc b s) z (1, 0)).1 =
      ((s : ℂ) - cavityM Hc b z)⁻¹

def cavityM_im_pos (Hc : K →L[ℂ] K) (b : K) (hHc : IsSelfAdjoint Hc)
    (z : ℂ) (hz : 0 < z.im) : Prop :=
  0 < (cavityM Hc b z).im

def rank_one_resolvent_identity (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (v w : K) (hv : ‖v‖ = 1) (h : ℝ) (z : ℂ) (hz : 0 < z.im) : Prop :=
  operatorResolvent (T + (h : ℂ) • InnerProductSpace.rankOne ℂ v v) z w =
      operatorResolvent T z w -
        (((h : ℂ) * inner ℂ v (operatorResolvent T z w)) /
          (1 + (h : ℂ) * inner ℂ v (operatorResolvent T z v))) •
          operatorResolvent T z v

/-- Lemma 9.1. A scalar spectral resolution and its measurability are
inputs from the spectral-theorem module, not inferred from its mere name. -/
def own_site_averaging (Hc : K →L[ℂ] K) (b : K) (hHc : IsSelfAdjoint Hc)
    (D : BlockSpectralData Hc b) (ρ : ℝ → ℝ) (C : ℝ)
    (hρ : Measurable ρ) (hρnonneg : ∀ᵐ s ∂volume, 0 ≤ ρ s)
    (hρbound : ∀ᵐ s ∂volume, ρ s ≤ C) (hC : 0 ≤ C)
    [IsProbabilityMeasure (densityLaw ρ)] (B : Set ℝ) (hB : MeasurableSet B) : Prop :=
  ∫⁻ s, D.measure s B ∂densityLaw ρ ≤ ENNReal.ofReal C * volume B

end Cavity

/-- The analytic core of Lemma 9.1, separated from operator algebra. -/
structure RankOneMeasureFamily (M : ℂ → ℂ) where
  measure : ℝ → Measure ℝ
  probability : ∀ s, IsProbabilityMeasure (measure s)
  measurable : ∀ B : Set ℝ, MeasurableSet B → Measurable (fun s => measure s B)
  transform_eq : ∀ s z, 0 < z.im →
    borelTransform (measure s) z = ((s : ℂ) - M z)⁻¹

def integral_cauchyKernel (a v : ℝ) (hv : 0 < v) : Prop :=
  ∫ s : ℝ, cauchyKernel a v s = Real.pi

def poissonConvolution (φ : ℝ → ℝ) (η t : ℝ) : ℝ :=
  (∫ E : ℝ, cauchyKernel t η E * φ E) / Real.pi

def poissonConvolution_uniform (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hcompact : HasCompactSupport φ) (ε : ℝ) (hε : 0 < ε) : Prop :=
  ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ t : ℝ, |poissonConvolution φ η t - φ t| < ε

def poisson_test_averaging_bound {M : ℂ → ℂ} (D : RankOneMeasureFamily M)
    (hM : ∀ z : ℂ, 0 < z.im → 0 < (M z).im)
    (ρ : ℝ → ℝ) (C : ℝ) (hρ : Measurable ρ)
    (hρnonneg : ∀ᵐ s ∂volume, 0 ≤ ρ s)
    (hρbound : ∀ᵐ s ∂volume, ρ s ≤ C) (hC : 0 ≤ C)
    [IsProbabilityMeasure (densityLaw ρ)] (φ : ℝ → ℝ)
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ) (hφnonneg : ∀ E, 0 ≤ φ E) : Prop :=
  ∫ s, (∫ E, φ E ∂D.measure s) ∂densityLaw ρ ≤ C * ∫ E, φ E

def rank_one_averaging {M : ℂ → ℂ} (D : RankOneMeasureFamily M)
    (hM : ∀ z : ℂ, 0 < z.im → 0 < (M z).im)
    (ρ : ℝ → ℝ) (C : ℝ) (hρ : Measurable ρ)
    (hρnonneg : ∀ᵐ s ∂volume, 0 ≤ ρ s)
    (hρbound : ∀ᵐ s ∂volume, ρ s ≤ C) (hC : 0 ≤ C)
    [IsProbabilityMeasure (densityLaw ρ)] (B : Set ℝ) (hB : MeasurableSet B) : Prop :=
  ∫⁻ s, D.measure s B ∂densityLaw ρ ≤ ENNReal.ofReal C * volume B

/-- The bounded-support version needed for OAI's normalized SingleSite.
It does not request measures for own-site values outside the actual law. -/
def uniform_rank_one_averaging (coupling : ℝ) (hcoupling : 0 < coupling)
    (M : ℂ → ℂ) (μ : SingleSite → Measure ℝ)
    (hprobability : ∀ s, IsProbabilityMeasure (μ s))
    (hmeas : ∀ B : Set ℝ, MeasurableSet B → Measurable (fun s => μ s B))
    (hM : ∀ z : ℂ, 0 < z.im → 0 < (M z).im)
    (htransform : ∀ s z, 0 < z.im → borelTransform (μ s) z =
      ((coupling * (s : ℝ) : ℂ) - M z)⁻¹)
    (B : Set ℝ) (hB : MeasurableSet B) : Prop :=
  ∫⁻ s, μ s B ∂uniformSite ≤ (ENNReal.ofReal (2 * coupling))⁻¹ * volume B

/-- Conditional form: the null set is fixed by the complement `ξ`. -/
def conditional_averaging_null {Ξ Own : Type*} [MeasurableSpace Ξ] [MeasurableSpace Own]
    (ν : Measure Ξ) [SFinite ν] (κ : Measure Own) [SFinite κ]
    (μ : Ξ → Own → Measure ℝ) (B : Ξ → Set ℝ)
    (hmeas : Measurable (fun p : Ξ × Own => μ p.1 p.2 (B p.1)))
    (hnull : ∀ᵐ ξ ∂ν, ∫⁻ s, μ ξ s (B ξ) ∂κ = 0) : Prop :=
  ∀ᵐ p ∂ν.prod κ, μ p.1 p.2 (B p.1) = 0

structure CertificateBounds where
  B : ℝ
  pMin : ℝ
  pMax : ℝ
  qMin : ℝ
  B_nonneg : 0 ≤ B
  pMin_pos : 0 < pMin
  pMin_le_pMax : pMin ≤ pMax
  qMin_pos : 0 < qMin

def comparisonConstant (b : CertificateBounds) : ℝ :=
  1 + (b.B + 1) / b.pMin

def columnConstant (b : CertificateBounds) : ℝ :=
  b.qMin / (b.pMax * comparisonConstant b ^ 2)

def cutMultiplier (ε : ℝ) : ℝ := 1 + ε⁻¹ ^ 2

def truncatedReadout (b : CertificateBounds) (ε q : ℝ) : ℝ :=
  min (2 * cutMultiplier ε * q) (columnConstant b)

section Finite

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixResolvent (H : Matrix n n ℂ) (E η : ℝ) : Matrix n n ℂ :=
  (H - ((E : ℂ) + η * Complex.I) • 1)⁻¹

def scalarQ (H : Matrix n n ℂ) (E η : ℝ) (i : n) : ℝ :=
  (matrixResolvent H E η i i).im

def matrixCertificate (H : Matrix n n ℂ) (E η : ℝ) (b : CertificateBounds) : Prop :=
  ∃ (A : Finset n) (r : n → ℂ) (G : Matrix n n ℂ),
    Fintype.card n ≤ 2 * A.card ∧
    (∀ i ∈ A, ‖r i‖ ≤ b.B ∧ b.pMin ≤ (r i).im ∧ (r i).im ≤ b.pMax) ∧
    (H - (E : ℂ) • 1 - (η : ℂ) • Matrix.diagonal (fun i => if i ∈ A then r i else 0)) * G = 1 ∧
    G * (H - (E : ℂ) • 1 - (η : ℂ) • Matrix.diagonal (fun i => if i ∈ A then r i else 0)) = 1 ∧
    (∀ i ∈ A, b.qMin ≤ (G i i).im)

def allPrincipalInvertible (H : Matrix n n ℂ) (E : ℝ) : Prop :=
  ∀ A : Finset n, IsUnit ((H - (E : ℂ) • 1).submatrix
    (fun i : A => (i : n)) (fun i : A => (i : n)))

def compress (A : Finset n) (T : Matrix n n ℂ) : Matrix A A ℂ :=
  T.submatrix (fun i : A => (i : n)) (fun i : A => (i : n))

def activeSchur (H : Matrix n n ℂ) (E : ℝ) (A : Finset n) : Matrix A A ℂ :=
  let H0 := H - (E : ℂ) • 1
  let Ac := Finset.univ \ A
  compress A H0 -
    H0.submatrix (fun i : A => (i : n)) (fun j : Ac => (j : n)) *
    (compress Ac H0)⁻¹ *
    H0.submatrix (fun j : Ac => (j : n)) (fun i : A => (i : n))

def dampingFunction (η : ℝ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  B * (1 - (η * Complex.I) • B)⁻¹

def windowProjection (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) :
    Matrix n n ℂ := by
  classical
  exact (hH.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => if |hH.eigenvalues i - E| ≤ δ then 1 else 0) *
    star (hH.eigenvectorUnitary : Matrix n n ℂ)

def windowRank (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) : ℕ :=
  Matrix.rank (windowProjection H hH E δ)

def cutInverse (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ε : ℝ) :
    Matrix n n ℂ :=
  (H - (E : ℂ) • 1)⁻¹ * (1 - windowProjection H hH E (ε * η))

def columnNormSq (G : Matrix n n ℂ) (i : n) : ℝ := ∑ j, ‖G j i‖ ^ 2

def hilbertSchmidtSq (G : Matrix n n ℂ) : ℝ := ∑ i, columnNormSq G i

def matrixOpNorm (G : Matrix n n ℂ) : ℝ :=
  ‖G.toEuclideanLin.toContinuousLinearMap‖

def matrixImaginaryPart (G : Matrix n n ℂ) : Matrix n n ℂ :=
  ((2 * Complex.I)⁻¹ : ℂ) • (G - star G)

def dissipative_inverse_bound (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p) (r : n → ℂ)
    (hr : ∀ i, p ≤ (r i).im) : Prop :=
  matrixOpNorm ((S - (η : ℂ) • Matrix.diagonal r)⁻¹) ≤ (η * p)⁻¹

def damped_ward_identity (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η : ℝ) (hη : 0 < η) (r : n → ℂ) (hr : ∀ i, 0 < (r i).im) : Prop :=
  let G := (S - (η : ℂ) • Matrix.diagonal r)⁻¹;
    matrixImaginaryPart G = (η : ℂ) •
      (star G * Matrix.diagonal (fun i => ((r i).im : ℂ)) * G)

def dampingFunction_difference (B C : Matrix n n ℂ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (η : ℝ) (hη : 0 < η) : Prop :=
  dampingFunction η B - dampingFunction η C =
      (1 - (η * Complex.I) • B)⁻¹ * (B - C) * (1 - (η * Complex.I) • C)⁻¹

def columnConstant_pos (b : CertificateBounds) : Prop :=
  0 < columnConstant b

/-- Equation (9.4), on the active Schur space. -/
def certified_subset_column (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (b : CertificateBounds)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n) (r : n → ℂ)
    (hr : ∀ i ∈ A, ‖r i‖ ≤ b.B ∧ b.pMin ≤ (r i).im ∧ (r i).im ≤ b.pMax)
    (hq : ∀ i : A, b.qMin ≤
      ((activeSchur H E A - (η : ℂ) • Matrix.diagonal (fun j : A => r j))⁻¹ i i).im) : Prop :=
  ∀ i : A, columnConstant b ≤ η * columnNormSq
      ((activeSchur H E A - (η * Complex.I) • 1)⁻¹) i

def active_resolvent_compression (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (hprincipal : allPrincipalInvertible H E) (A : Finset n) : Prop :=
  (activeSchur H E A - (η * Complex.I) • 1)⁻¹ =
      dampingFunction η (compress A ((H - (E : ℂ) • 1)⁻¹))

/-- Equation (9.5), in a form that does not need a matrix operator-norm convention. -/
def cut_rank_hilbertSchmidt (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n) : Prop :=
  let D := dampingFunction η (compress A ((H - (E : ℂ) • 1)⁻¹)) -
      dampingFunction η (compress A (cutInverse H hH E η ε));
    Matrix.rank D ≤ windowRank H hH E (ε * η) ∧
      matrixOpNorm D ≤ 2 / η ∧
      hilbertSchmidtSq D ≤ 4 * (windowRank H hH E (ε * η) : ℝ) / η ^ 2

/-- Equation (9.6), using the scalar spectral weight outside the cut. -/
def cut_column (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n) (i : A) : Prop :=
  η * columnNormSq (dampingFunction η (compress A (cutInverse H hH E η ε))) i ≤
      cutMultiplier ε * scalarQ H E η i

def finite_cut_comparison [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (b : CertificateBounds) (hprincipal : allPrincipalInvertible H E)
    (hcert : matrixCertificate H E η b) : Prop :=
  columnConstant b / 2 - 8 * (windowRank H hH E (ε * η) : ℝ) /
      (η * Fintype.card n) ≤
      (∑ i, truncatedReadout b ε (scalarQ H E η i)) / Fintype.card n

end Finite

def trueCertificateEvent (d m : ℕ) (coupling E η : ℝ) (b : CertificateBounds) :
    Set (TorusConfiguration d m) :=
  {ω | matrixCertificate (periodicHamiltonian coupling ω) E η b}

def comparableHeights (η : ℕ → ℝ) : Prop :=
  (∀ m, 0 < η m) ∧ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
    ∀ᶠ m in atTop, a / (4 : ℝ) ^ m ≤ η m ∧ η m ≤ c / (4 : ℝ) ^ m

def halfProbabilityCertificates (d : ℕ) (coupling : ℝ) (I : Set ℝ) : Prop :=
  ∃ (b : CertificateBounds) (η : ℕ → ℝ), comparableHeights η ∧
    ∀ E ∈ I, ∀ᶠ m in atTop,
      (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (trueCertificateEvent d m coupling E (η m) b)

def siteVector {d : ℕ} (x : Site d) : StateSpace d := AndersonAC.Blueprint.delta x

def diagonalGreen {d : ℕ} (coupling : ℝ) (ω : Configuration d) (x : Site d) (z : ℂ) : ℂ :=
  AndersonAC.Blueprint.diagonalGreen coupling ω x z

def offDiagonalGreen {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (z : ℂ) : ℂ :=
  inner ℂ (siteVector x) (operatorResolvent (hamiltonian coupling ω) z (siteVector y))

def latticeDistance {d : ℕ} (x y : Site d) : ℕ := ∑ j, Int.natAbs (x j - y j)

def trueCertificateEvent_measurable (d m : ℕ) (coupling E η : ℝ) (b : CertificateBounds) : Prop :=
  MeasurableSet (trueCertificateEvent d m coupling E η b)

def periodicHamiltonian_isHermitian (d m : ℕ) (coupling : ℝ) (ω : TorusConfiguration d m) : Prop :=
  (periodicHamiltonian coupling ω).IsHermitian

def true_principal_invertible_ae (d m : ℕ) (coupling E : ℝ) (hcoupling : 0 < coupling) : Prop :=
  ∀ᵐ ω ∂torusLaw d m, allPrincipalInvertible (periodicHamiltonian coupling ω) E

def finite_wegner (d m : ℕ) (coupling E δ : ℝ) (hcoupling : 0 < coupling) (hδ : 0 ≤ δ)
    (hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian) : Prop :=
  ∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E δ : ℝ) ∂torusLaw d m ≤
      (Fintype.card (Torus d m) : ℝ) * δ / coupling

/-- Equation (9.7); the rank expectation uses the unconditioned true law. -/
def finite_truncated_average (d m : ℕ) (coupling E η ε : ℝ)
    (hcoupling : 0 < coupling) (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (b : CertificateBounds)
    (hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian) : Prop :=
  columnConstant b / 2 * (torusLaw d m (trueCertificateEvent d m coupling E η b)).toReal -
      8 * (∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E (ε * η) : ℝ)
        ∂torusLaw d m) / (η * Fintype.card (Torus d m)) ≤
      ∫ ω, (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
        Fintype.card (Torus d m) ∂torusLaw d m

def torus_root_expectation (d m : ℕ) (coupling E η ε : ℝ) (b : CertificateBounds) : Prop :=
  (∫ ω, (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
      Fintype.card (Torus d m) ∂torusLaw d m) =
      ∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η 0) ∂torusLaw d m

def finite_root_readout (d m : ℕ) (coupling E η ε : ℝ) (hcoupling : 0 < coupling) (hη : 0 < η)
    (b : CertificateBounds) (hε : 0 < ε)
    (hεsmall : ε ≤ min 1 (columnConstant b * coupling / 64))
    (hcert : (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (trueCertificateEvent d m coupling E η b)) : Prop :=
  columnConstant b / 8 ≤ ∫ ω, truncatedReadout b ε
      (scalarQ (periodicHamiltonian coupling ω) E η 0) ∂torusLaw d m

def torusSite {d m : ℕ} (x : Site d) : Torus d m := fun j => (x j : ZMod (sideLength m))

def rootCubeMatch {d m : ℕ} (ωm : TorusConfiguration d m) (ω : Configuration d) : Prop :=
  ∀ x : Site d, (∀ j : Fin d, |x j| ≤ (sideLength m / 4 : ℕ)) →
    (ωm (torusSite x) : ℝ) = potential ω x

structure RootCoupling (d m : ℕ) where
  law : Measure (TorusConfiguration d m × Configuration d)
  probability : IsProbabilityMeasure law
  finite_marginal : law.map Prod.fst = torusLaw d m
  infinite_marginal : law.map Prod.snd = disorderLaw d
  matched : ∀ᵐ p ∂law, rootCubeMatch p.1 p.2

def rootCoupling_exists (d m : ℕ) : Prop :=
  Nonempty (RootCoupling d m)

def combes_thomas_infinite (d : ℕ) (coupling : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (E η : ℝ), η ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (ω : Configuration d) (x y : Site d),
        ‖offDiagonalGreen coupling ω x y ((E : ℂ) + η * Complex.I)‖ ≤
          C / η * Real.exp (-c * η * latticeDistance x y)

/-- Equation (9.10), before integrating in the coupled law. -/
def finite_infinite_resolvent_comparison (d : ℕ) (hd : 3 ≤ d) (coupling : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ m in atTop,
      ∀ (E η : ℝ), η ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (ωm : TorusConfiguration d m) (ω : Configuration d), rootCubeMatch ωm ω →
        ‖matrixResolvent (periodicHamiltonian coupling ωm) E η 0 0 -
          diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)‖ ≤
          C * (sideLength m : ℝ) ^ (d - 1) * η⁻¹ ^ 2 *
            Real.exp (-c * η * sideLength m)

def volume_comparison_error_tendsto (d : ℕ) (η : ℕ → ℝ)
    (hη : comparableHeights η) (C c : ℝ) (hc : 0 < c) : Prop :=
  Tendsto (fun m => C * (sideLength m : ℝ) ^ (d - 1) * (η m)⁻¹ ^ 2 *
      Real.exp (-c * η m * sideLength m)) atTop (𝓝 0)

def infinite_root_readout (d : ℕ) (hd : 3 ≤ d) (coupling E ε : ℝ)
    (b : CertificateBounds) (η : ℕ → ℝ) (hη : comparableHeights η)
    (hε : 0 < ε)
    (hfinite : ∀ᶠ m in atTop, columnConstant b / 8 ≤
      ∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E (η m) 0)
        ∂torusLaw d m) : Prop :=
  columnConstant b / 8 ≤ liminf (fun m => ∫ ω,
      truncatedReadout b ε (diagonalGreen coupling ω 0
        ((E : ℂ) + η m * Complex.I)).im ∂disorderLaw d) atTop

/-- Use the architecture's exact boundary interface. -/
abbrev BoundaryTheory := AndersonAC.Blueprint.BoundaryInput

/-- PVM/resolvent correspondence for every realization. -/
structure ResolvedAnderson (d : ℕ) (coupling : ℝ) where
  resolved : ∀ ω : Configuration d,
    AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω)
  measure_measurable : ∀ x : Site d, ∀ B : Set ℝ, MeasurableSet B →
    Measurable (fun ω => (resolved ω).spectral.vectorMeasure (siteVector x) B)

def resolved_anderson (d : ℕ) (coupling : ℝ)
    (S : AndersonAC.Blueprint.SpectralInput) : Prop :=
  Nonempty (ResolvedAnderson d coupling)

def shortestPathCount {d : ℕ} (x y : Site d) : ℕ :=
  (latticeDistance x y).factorial / ∏ j, (Int.natAbs (x j - y j)).factorial

def shortest_path_coefficient {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) : Prop :=
  (∀ n : ℕ, n < latticeDistance x y →
      ((hamiltonian coupling ω ^ n) (siteVector y)) x = 0) ∧
    ((hamiltonian coupling ω ^ latticeDistance x y) (siteVector y)) x =
      (-1 : ℂ) ^ latticeDistance x y * (shortestPathCount x y : ℂ) ∧
    0 < shortestPathCount x y

def offDiagonal_not_identically_zero {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (hxy : x ≠ y) : Prop :=
  ∃ z : ℂ, 0 < z.im ∧ offDiagonalGreen coupling ω x y z ≠ 0

def offDiagonal_boundary_nonzero {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (hxy : x ≠ y)
    (R : AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω)) (B : BoundaryTheory) : Prop :=
  ∀ᵐ E ∂volume,
      ∃ w : ℂ, verticalBoundary (offDiagonalGreen coupling ω x y) E w ∧ w ≠ 0

def allSitesPositive {d : ℕ} (coupling : ℝ) (E : ℝ) (ω : Configuration d) : Prop :=
  ∀ x : Site d, positiveBoundary (diagonalGreen coupling ω x) E

def boundary_positive_probability (d : ℕ) (coupling E ε : ℝ)
    (b : CertificateBounds) (η : ℕ → ℝ) (hη : comparableHeights η) (hε : 0 < ε)
    (hfinite : ∀ᵐ ω ∂disorderLaw d, finiteBoundary (diagonalGreen coupling ω 0) E)
    (hlower : columnConstant b / 8 ≤ liminf (fun m => ∫ ω,
      truncatedReadout b ε (diagonalGreen coupling ω 0
        ((E : ℂ) + η m * Complex.I)).im ∂disorderLaw d) atTop) : Prop :=
  0 < disorderLaw d {ω | positiveBoundary (diagonalGreen coupling ω 0) E}

/-- Real symmetry, PSD and zero y-diagonal force a real off-diagonal value. -/
def boundary_psd_zero_diagonal (g a k : ℂ) (hkim : k.im = 0)
    (hpsd : (Matrix.of (fun i j : Fin 2 =>
      if i = 0 then (if j = 0 then g.im else a.im)
      else (if j = 0 then a.im else k.im))).PosSemidef) : Prop :=
  a.im = 0

/-- The strict rank-one propagation calculation in §9, lines 440–448. -/
def rank_one_imaginary_part (g : ℂ) (a h : ℝ) (hg : 0 < g.im)
    (ha : a ≠ 0) (hh : h ≠ 0) : Prop :=
  0 < (-(h : ℂ) * (a : ℂ) ^ 2 / (1 + (h : ℂ) * g)).im

def positivity_mismatch_null (d : ℕ) (coupling E : ℝ) (hcoupling : 0 < coupling)
    (x y : Site d) (hxy : x ≠ y)
    (hadmissible : ∀ᵐ ω ∂disorderLaw d,
      finiteBoundary (diagonalGreen coupling ω x) E ∧
      finiteBoundary (diagonalGreen coupling ω y) E ∧
      ∃ a : ℂ, verticalBoundary (offDiagonalGreen coupling ω x y) E a ∧ a ≠ 0) : Prop :=
  disorderLaw d {ω | positiveBoundary (diagonalGreen coupling ω x) E ∧
      ∃ w : ℂ, verticalBoundary (diagonalGreen coupling ω y) E w ∧ w.im = 0} = 0

def translatedConfiguration {d : ℕ} (a : Site d) (ω : Configuration d) : Configuration d :=
  fun x => ω (x + a)

def iid_translation_zero_one (d : ℕ) (hd : 0 < d) (A : Set (Configuration d))
    (hA : MeasurableSet A)
    (hinvariant : ∀ a : Site d, (translatedConfiguration a) ⁻¹' A = A) : Prop :=
  disorderLaw d A = 0 ∨ disorderLaw d A = 1

/-- Equation (9.3), with the energy quantifier outside the probability-one claim. -/
def all_sites_positive (d : ℕ) (hd : 3 ≤ d) (coupling : ℝ) (hcoupling : 0 < coupling)
    (a b : ℝ) (hab : a < b) (R : ResolvedAnderson d coupling) (B : BoundaryTheory)
    (hcertificate : halfProbabilityCertificates d coupling (Set.Ioo a b)) : Prop :=
  ∀ᵐ E ∂volume.restrict (Set.Ioo a b),
      ∀ᵐ ω ∂disorderLaw d, allSitesPositive coupling E ω

/-- Finite upper Poisson bounds at sufficiently small heights. This is
equivalent to finite limsup for a nonnegative Poisson transform. -/
def boundedPoissonAt (μ : Measure ℝ) (E : ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
    (borelTransform μ ((E : ℂ) + η * Complex.I)).im ≤ C

def boundedPoissonSet (μ : Measure ℝ) (S : Set ℝ) (k : ℕ) : Set ℝ :=
  {E ∈ S | ∀ η : ℝ, 0 < η → η < 1 / (k + 1 : ℝ) →
    (borelTransform μ ((E : ℂ) + η * Complex.I)).im ≤ k + 1}

def poisson_interval_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E r : ℝ) (hr : 0 < r) : Prop :=
  μ (Set.Ioo (E - r) (E + r)) ≤ ENNReal.ofReal
      (2 * r * (borelTransform μ ((E : ℂ) + r * Complex.I)).im)

def bounded_boundary_ac (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Set ℝ) (hS : MeasurableSet S) (hbounded : ∀ E ∈ S, boundedPoissonAt μ E) : Prop :=
  μ.restrict S ≪ volume

def boundedPoisson_sets_cover (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Set ℝ) (hS : MeasurableSet S) (hbounded : ∀ E ∈ S, boundedPoissonAt μ E) : Prop :=
  (∀ k, MeasurableSet (boundedPoissonSet μ S k)) ∧
      S = ⋃ k : ℕ, boundedPoissonSet μ S k

/-- Abstract purity core: averaging eliminates the complementary null set.
`S ξ` depends only on `ξ`, never on the own-site variable `s`. -/
def conditional_purity {Ξ Own : Type*} [MeasurableSpace Ξ] [MeasurableSpace Own]
    (ν : Measure Ξ) [SFinite ν] (κ : Measure Own) [SFinite κ]
    (μ : Ξ → Own → Measure ℝ) (I : Set ℝ) (S : Ξ → Set ℝ)
    (hI : MeasurableSet I) (hS : ∀ ξ, MeasurableSet (S ξ))
    (hsub : ∀ ξ, S ξ ⊆ I)
    (hmeas : Measurable (fun p : Ξ × Own => μ p.1 p.2 (I \ S p.1)))
    (hac : ∀ᵐ ξ ∂ν, ∀ s, (μ ξ s).restrict (S ξ) ≪ volume)
    (haverage : ∀ᵐ ξ ∂ν, ∫⁻ s, μ ξ s (I \ S ξ) ∂κ = 0) : Prop :=
  ∀ᵐ p ∂ν.prod κ, (μ p.1 p.2).restrict I ≪ volume

abbrev ComplementConfiguration (d : ℕ) (x : Site d) :=
  {y : Site d // y ≠ x} → SingleSite

def complementLaw (d : ℕ) (x : Site d) : Measure (ComplementConfiguration d x) :=
  Measure.infinitePi (fun _ => uniformSite)

def restoreSite {d : ℕ} (x : Site d) (ξ : ComplementConfiguration d x)
    (s : SingleSite) : Configuration d := by
  classical
  exact fun y => if h : y = x then s else ξ ⟨y, h⟩

def restoreSite_measurePreserving (d : ℕ) (x : Site d) : Prop :=
  MeasurePreserving (fun p : ComplementConfiguration d x × SingleSite => restoreSite x p.1 p.2)
      ((complementLaw d x).prod uniformSite) (disorderLaw d)

/-- Cavity family on normalized own-site coordinates; M is complement-only. -/
structure SiteCavity {d : ℕ} (coupling : ℝ) (x : Site d)
    (R : ResolvedAnderson d coupling) where
  M : ComplementConfiguration d x → ℂ → ℂ
  positive_height : ∀ ξ z, 0 < z.im → 0 < (M ξ z).im
  finite_boundary : ∀ ξ, ∀ᵐ E ∂volume, finiteBoundary (M ξ) E
  jointly_measurable : MeasurableSet {p : ComplementConfiguration d x × ℝ |
    positiveBoundary (M p.1) p.2}
  cavity_eq : ∀ ξ s z, 0 < z.im →
    diagonalGreen coupling (restoreSite x ξ s) x z =
      ((coupling * (s : ℝ) : ℂ) - M ξ z)⁻¹

def siteCavity_exists {d : ℕ} (coupling : ℝ) (x : Site d)
    (R : ResolvedAnderson d coupling) (S : AndersonAC.Blueprint.SpectralInput) (B : BoundaryTheory) : Prop :=
  Nonempty (SiteCavity coupling x R)

def cavity_positive_boundary_all (M : ℂ → ℂ) (g : ℝ → ℂ → ℂ) (E : ℝ)
    (hM : positiveBoundary M E)
    (hcavity : ∀ s z, 0 < z.im → g s z = ((s : ℂ) - M z)⁻¹) : Prop :=
  ∀ s : ℝ, positiveBoundary (g s) E

def cavity_good_set_full {d : ℕ} (coupling : ℝ) (hcoupling : 0 < coupling)
    (x : Site d) (a b : ℝ) (R : ResolvedAnderson d coupling)
    (C : SiteCavity coupling x R)
    (hpositive : ∀ᵐ E ∂volume.restrict (Set.Ioo a b),
      ∀ᵐ ω ∂disorderLaw d, positiveBoundary (diagonalGreen coupling ω x) E) : Prop :=
  ∀ᵐ ξ ∂complementLaw d x,
      volume (Set.Ioo a b \ {E | positiveBoundary (C.M ξ) E}) = 0

def site_measure_purely_ac {d : ℕ} (coupling : ℝ) (hcoupling : 0 < coupling)
    (x : Site d) (a b : ℝ) (R : ResolvedAnderson d coupling)
    (C : SiteCavity coupling x R)
    (hpositive : ∀ᵐ E ∂volume.restrict (Set.Ioo a b),
      ∀ᵐ ω ∂disorderLaw d, positiveBoundary (diagonalGreen coupling ω x) E) : Prop :=
  ∀ᵐ ω ∂disorderLaw d,
      ((R.resolved ω).spectral.vectorMeasure (siteVector x)).restrict (Set.Ioo a b) ≪ volume

def basis_ac_implies_purelyACOn {d : ℕ} {T : StateSpace d →L[ℂ] StateSpace d}
    (S : SpectralResolution T) (I : Set ℝ) (hI : MeasurableSet I)
    (hbasis : ∀ x : Site d, (S.vectorMeasure (siteVector x)).restrict I ≪ volume) : Prop :=
  S.purelyACOn I

def positive_boundary_spectrum {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (a b : ℝ) (hpositive : ∀ᵐ E ∂volume.restrict (Set.Ioo a b),
      positiveBoundary (diagonalGreen coupling ω 0) E) : Prop :=
  Set.Ioo a b ⊆ AndersonAC.Blueprint.realSpectrum (hamiltonian coupling ω)

def positive_boundary_mass {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (a b : ℝ) (hab : a < b)
    (R : AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω))
    (hpositive : ∀ᵐ E ∂volume.restrict (Set.Ioo a b),
      positiveBoundary (diagonalGreen coupling ω 0) E) : Prop :=
  0 < R.spectral.vectorMeasure (siteVector 0) (Set.Ioo a b)

/-- Proposition 9.2. All spectral and boundary imports are explicit. -/
def certificate_readout (d : ℕ) (hd : 3 ≤ d) (coupling : ℝ) (hcoupling : 0 < coupling)
    (a b : ℝ) (hab : a < b) (R : ResolvedAnderson d coupling) (B : BoundaryTheory)
    (C : ∀ x : Site d, SiteCavity coupling x R)
    (hcertificate : halfProbabilityCertificates d coupling (Set.Ioo a b)) : Prop :=
  ∀ᵐ ω ∂disorderLaw d,
      Set.Ioo a b ⊆ AndersonAC.Blueprint.realSpectrum (hamiltonian coupling ω) ∧
      (R.resolved ω).spectral.purelyACOn (Set.Ioo a b) ∧
      0 < (R.resolved ω).spectral.vectorMeasure (siteVector 0) (Set.Ioo a b) ∧
      (R.resolved ω).spectral.projection (Set.Ioo a b) ≠ 0

/-- The common spectral inputs needed at each fixed positive coupling. -/
structure SpectralInputs where
  boundary : BoundaryTheory
  resolved : ∀ (d : ℕ) (coupling : ℝ), 3 ≤ d → 0 < coupling → ResolvedAnderson d coupling
  cavity : ∀ (d : ℕ) (coupling : ℝ) (hd : 3 ≤ d) (hcoupling : 0 < coupling),
    ∀ x : Site d, SiteCavity coupling x (resolved d coupling hd hcoupling)

/-- The earlier sections' output. d=3 is existential; d≥4 retains the
intrinsic `finiteBoxThreshold` required by the architecture target. -/
structure FiniteCertificateInputs (e₂ : ℝ) where
  three_threshold : ℝ
  three_threshold_pos : 0 < three_threshold
  three_certificate : ∀ coupling : ℝ, 0 < coupling → coupling < three_threshold →
    halfProbabilityCertificates 3 coupling (energyWindow 3 e₂)
  higher_threshold : ∀ d : ℕ, 4 ≤ d → ∃ threshold : ℝ, finiteBoxThreshold d threshold
  higher_certificate : ∀ (d : ℕ) (hd : 4 ≤ d) (threshold : ℝ), finiteBoxThreshold d threshold →
    ∀ coupling : ℝ, 0 < coupling → coupling < threshold →
      halfProbabilityCertificates d coupling (energyWindow d e₂)

def scaleHeight_comparable (u : ℝ) (hu : 0 < u) : Prop :=
  comparableHeights (fun m => scaleHeight m u)

/-- Normalized k-bounds connect the pre-existing OAI certificate event to
the general Proposition 9.2 event, using |Im r| ≤ ‖r‖. -/
def normalized_certificate_bridge (d k n₀ m : ℕ) (hk : 0 < k) (u E : ℝ) : Prop :=
  ∃ b : CertificateBounds, b.B = k ∧ b.pMin = 1 / (k : ℝ) ∧
      b.pMax = k ∧ b.qMin = 1 / (k : ℝ) ∧
      certificateEvent d k n₀ m u E =
        trueCertificateEvent d m (scaleCoupling n₀ u) E (scaleHeight m u) b

def threshold_supplies_certificate (d : ℕ) (hd : 4 ≤ d) (threshold : ℝ)
    (hthreshold : finiteBoxThreshold d threshold) (coupling : ℝ)
    (hcoupling : 0 < coupling) (hlt : coupling < threshold) : Prop :=
  halfProbabilityCertificates d coupling (higherDimWindow d)

/-- Conditional proof of Theorem 1.1 from the finite certificate. -/
def paper_theorem_of_certificate (e₂ : ℝ) (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (F : FiniteCertificateInputs e₂) (S : SpectralInputs) : Prop :=
  AndersonAC.Blueprint.PaperTheorem

/-- spectral averaging package, in exact interface. -/
def spectral_averaging : Prop :=
  AndersonAC.Blueprint.AveragingInput

/-- readout package, in exact interface. -/
def spectral_readout : Prop :=
  AndersonAC.Blueprint.ReadoutInput

/-- purity package, in exact interface. -/
def spectral_purity : Prop :=
  AndersonAC.Blueprint.PurityInput

def weakCertificates_bridge (d : ℕ) (coupling : ℝ) (I : Set ℝ)
    (h : AndersonAC.Blueprint.WeakCertificates d coupling I) : Prop :=
  halfProbabilityCertificates d coupling I

/-- Final join: the e₂ witness and certificate family come from §§3–8.
The §9 exports above discharge A, R and P in phase. -/
def paper_theorem_from_inputs (e₂ : ℝ) (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (F : AndersonAC.Blueprint.CertificateFamily e₂)
    (S : AndersonAC.Blueprint.SpectralInput) (B : AndersonAC.Blueprint.BoundaryInput)
    (A : AndersonAC.Blueprint.AveragingInput) (R : AndersonAC.Blueprint.ReadoutInput)
    (P : AndersonAC.Blueprint.PurityInput) : Prop :=
  AndersonAC.Blueprint.PaperTheorem

/-- The last paragraph of §9; shared with architecture parity transport. -/
def hopping_sign_conjugation (d : ℕ) : Prop :=
  ∃ U : StateSpace d ≃ₗᵢ[ℂ] StateSpace d, ∀ (coupling : ℝ) (ω : Configuration d),
      AndersonAC.Blueprint.conjugate U (hamiltonian coupling ω) =
        -hopping d + (coupling : ℂ) • potentialOperator ω

/-- Spectral transport under the parity unitary; shared with scalar-shift transport. -/
def ACRegion_unitary_conjugate {d : ℕ} (T : AndersonAC.Blueprint.Operator d)
    (hT : IsSelfAdjoint T) (U : StateSpace d ≃ₗᵢ[ℂ] StateSpace d) (I : Set ℝ)
    (hI : MeasurableSet I) (hac : AndersonAC.Blueprint.ACRegion T I) : Prop :=
  AndersonAC.Blueprint.ACRegion (AndersonAC.Blueprint.conjugate U T) I

end AndersonAC.SolS9.Planned
