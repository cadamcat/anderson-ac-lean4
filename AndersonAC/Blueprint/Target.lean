import OAI.MathematicalPhysics.Anderson.Certificates

/-!
Proposed target, not frozen. No theorem in this file assumes the preprint.
The real spectral set uses `spectrum ℂ`, with real energies embedded in ℂ.
OAI's spectral resolution has countably additive orthogonal projections,
finite scalar measures, compact support, and all moments tied to the operator.
WP01 must construct it from a bounded PVM, rather than postulate its fields.
-/

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal NNReal lp

namespace AndersonAC.Blueprint

abbrev Operator (d : ℕ) := StateSpace d →L[ℂ] StateSpace d

def realSpectrum {d : ℕ} (T : Operator d) : Set ℝ :=
  {E | (E : ℂ) ∈ spectrum ℂ T}

/-- `(T-z)⁻¹`, in the paper's sign convention. -/
def greenOperator {d : ℕ} (T : Operator d) (z : ℂ) : Operator d :=
  Ring.inverse (T - z • (1 : Operator d))

def borelTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ

/-- Constructed from WP01's bounded PVM; the extra field is needed by §9. -/
structure ResolvedOperator {d : ℕ} (T : Operator d) where
  spectral : SpectralResolution T
  resolvent_eq : ∀ (v : StateSpace d) (z : ℂ), 0 < z.im →
    inner ℂ v (greenOperator T z v) = borelTransform (spectral.vectorMeasure v) z

abbrev chi {d : ℕ} {T : Operator d} (S : SpectralResolution T) (I : Set ℝ) :=
  S.projection I

abbrev acSubspace {d : ℕ} {T : Operator d} (S : SpectralResolution T) :=
  S.acSubspace

/-- A nonzero purely AC restriction, including the asserted spectral interval. -/
def ACRegion {d : ℕ} (T : Operator d) (I : Set ℝ) : Prop :=
  I ⊆ realSpectrum T ∧ ∃ S : SpectralResolution T,
    Set.range (chi S I) ⊆ (acSubspace S : Set (StateSpace d)) ∧ chi S I ≠ 0

theorem acRegion_iff {d : ℕ} (T : Operator d) {I : Set ℝ}
    (hI : MeasurableSet I) :
    ACRegion T I ↔ I ⊆ realSpectrum T ∧
      ∃ S : SpectralResolution T, S.purelyACOn I ∧ S.projection I ≠ 0 := by
  constructor
  · rintro ⟨hσ, S, hac, hn⟩
    exact ⟨hσ, S, (S.range_subset_acVectors_iff hI).mp hac, hn⟩
  · rintro ⟨hσ, S, hac, hn⟩
    exact ⟨hσ, S, (S.range_subset_acVectors_iff hI).mpr hac, hn⟩

/-- Theorem 1.1, including the intrinsic threshold specification for d≥4.
The fixed `e₂` precedes the dimension quantifier; the AE event follows λ. -/
def PaperTheorem : Prop :=
  ∃ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) ∧
    ∀ d : ℕ, 3 ≤ d → ∃ lambdaBound : ℝ, 0 < lambdaBound ∧
      (4 ≤ d → finiteBoxThreshold d lambdaBound) ∧
      ∀ coupling : ℝ, 0 < coupling → coupling < lambdaBound →
        ∀ᵐ ω ∂disorderLaw d, ACRegion (hamiltonian coupling ω) (energyWindow d e₂)

def intervalCenter (a b : ℝ) : ℝ := (a + b) / 2
def intervalCoupling (a b : ℝ) : ℝ := (b - a) / 2
def affineConfiguration {d : ℕ} (a b : ℝ) (ω : Configuration d) : Site d → ℝ :=
  fun x => intervalCenter a b + intervalCoupling a b * potential ω x

/-- The unscaled iid uniform law on Simon's site potentials. -/
def uniformInterval (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Set.Icc a b)

def intervalLaw (d : ℕ) (a b : ℝ) : Measure (Site d → ℝ) :=
  Measure.infinitePi (fun _ => uniformInterval a b)

theorem uniformInterval_probability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (uniformInterval a b) := by
  constructor
  simp only [uniformInterval, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by simpa using hab) ENNReal.ofReal_ne_top

theorem intervalLaw_probability (d : ℕ) {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalLaw d a b) := by
  let : IsProbabilityMeasure (uniformInterval a b) := uniformInterval_probability hab
  unfold intervalLaw
  infer_instance

/-- A bounded realization stores the normalized coordinates, with no law assumed. -/
def IsIntervalConfiguration {d : ℕ} (a b : ℝ) (V : Site d → ℝ) : Prop :=
  ∃ ω : Configuration d, affineConfiguration a b ω = V

/-- Scalar center transport of the OAI operator, before reversing hopping. -/
def shiftedHamiltonian {d : ℕ} (a b : ℝ) (ω : Configuration d) : Operator d :=
  hamiltonian (intervalCoupling a b) ω +
    (intervalCenter a b : ℂ) • (1 : Operator d)

/-- Direct positive hopping definition on any real potential bounded by M.
`M` is data, not a hypothesis about a law or a spectral conclusion. -/
def boundedPotentialLinear {d : ℕ} (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) : StateSpace d →ₗ[ℂ] StateSpace d where
  toFun f := ⟨fun x => (V x : ℂ) * f x,
    ((lp.memℓp f).const_smul M).mono' (fun x => by
      change ‖(V x : ℂ) * f x‖ ≤ ‖M • f x‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_smul,
        Real.norm_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right (hV x) (norm_nonneg (f x)))⟩
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by ext x; change (V x : ℂ) * (c * f x) = c * ((V x : ℂ) * f x); ring

def boundedPotentialOperator {d : ℕ} (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) : Operator d :=
  (boundedPotentialLinear V M hM hV).mkContinuous M (fun f => by
    calc
      ‖boundedPotentialLinear V M hM hV f‖ ≤ ‖M • f‖ := by
        apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        intro x
        change ‖(V x : ℂ) * f x‖ ≤ ‖M • f x‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_smul,
          Real.norm_of_nonneg hM]
        exact mul_le_mul_of_nonneg_right (hV x) (norm_nonneg _)
      _ = M * ‖f‖ := by rw [norm_smul, Real.norm_of_nonneg hM])

def simonHamiltonian {d : ℕ} (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) : Operator d :=
  -hopping d + boundedPotentialOperator V M hM hV

def translateWindow (c : ℝ) (I : Set ℝ) : Set ℝ :=
  (fun E => c + E) '' I

/-- Simon Problem 1 with law and positive hopping stated directly.
The energy interval `(E₁, E₂)` depends on the center, not on the positive width.
The existential bound proves that the directly defined operator is bounded.
No spectral or iid hypothesis is hidden inside its construction.
(Coordinator, 2026-10-13: the window is a nonempty open interval, as in the paper.) -/
def SimonProblem : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ widthBound E₁ E₂ : ℝ, 0 < widthBound ∧ E₁ < E₂ ∧
    ∀ a b : ℝ, a < b → b - a < widthBound →
      ∀ᵐ V ∂intervalLaw d a b, ∃ (M : ℝ) (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M),
        ACRegion (simonHamiltonian V M hM hV)
          (translateWindow (intervalCenter a b) (Set.Ioo E₁ E₂))

end AndersonAC.Blueprint
