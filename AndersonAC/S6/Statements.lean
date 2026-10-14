import AndersonAC.S6.Definitions

/-! Planning propositions only. A definition of a proposition is not its proof. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator NNReal ComplexOrder
open Filter MeasureTheory ProbabilityTheory
namespace AndersonAC.S6.Planned
variable {ι B R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def parameter_margins (d : ℕ) (hd : 3 ≤ d) : Prop :=
  0 ≤ nu d ∧ nu d < (1 + delta) / 2 ∧ 0 < e0 ∧ e0 < delta - nu d ∧
  e0 / 2 < betaW ∧ betaW < 1 / 2 ∧ e0 + nu d < eh ∧
  betaW - e0 / 2 = (14 / 100) * delta ∧
  delta - e0 - nu d = ((56 / 100) - (1 / 100000) / (d : ℝ)) * delta ∧
  eh - e0 - nu d = ((2 / 100) - (1 / 100000) / (d : ℝ)) * delta

def scattering_unitary (t : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : g.IsSymm)
    (hWard : g - gᴴ = (2 * Complex.I * (t : ℂ)) •
      (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ)) : Prop :=
  (scatteringOfDamping t p g).IsSymm ∧ scatteringOfDamping t p g * (scatteringOfDamping t p g)ᴴ = 1

def scatteringInput_of_ward (hWard : WardInput) : Prop :=
  ScatteringInput

def projection_coordinate (C : Matrix R B ℂ) (i : R) : Prop :=
  0 ≤ projectionWeight C i ∧
  (∀ v ∈ matrixRange C, ‖v i‖ ^ 2 ≤ projectionWeight C i * ‖v‖ ^ 2) ∧
  (0 < projectionWeight C i → ∃ v ∈ matrixRange C,
    ‖v‖ = 1 ∧ ‖v i‖ ^ 2 = projectionWeight C i)

def core_completion (M N : Matrix (B ⊕ R) (B ⊕ R) ℝ)
    (t c K l : ℝ) (r : (B ⊕ R) → ℂ)
    (ht : 0 < t) (hl : 0 ≤ l) (hb : BroadBounds c K r)
    (hM : M.IsSymm) (hN : N.IsSymm) (hchange : CoreDiagonalChange M N)
    (hterminal : IsUnit (trueCoreMatrix N).det)
    (hprojection : ∀ i, projectionWeight
      (crossBlock (scattering t r (activeInverse M t r))) i ≤ 2 * l) : Prop :=
  let dg := completionDelta M N t r
  let dh := scaledInverse t dg
  let C := crossBlock (scattering t r (activeInverse M t r))
  let ds := scattering t (r ∘ Sum.inr) (completedInverse N t r) -
    survivorBlock (scattering t r (activeInverse M t r))
  IsUnit (dampedMatrix (realSurvivor N) t (r ∘ Sum.inr)).det ∧
  ‖ds‖ ≤ 2 ∧ ds = rangeProjection C * ds * (rangeProjection C).map star ∧
  (∀ i j, ‖dg i j‖ ≤ 2 * l / (t * c)) ∧
  (∀ i, sqRow dh i ≤ 2 * l / (t * c ^ 2)) ∧
  (∀ i, fourthRow dh i ≤ 8 * l ^ 3 / (t ^ 2 * c ^ 4)) ∧
  hsSq dh ≤ (Fintype.card B : ℝ) / (t * c ^ 2)

def supported_change_bounds (C : Matrix R B ℂ) (D : Matrix R R ℂ)
    (hD : ‖D‖ ≤ 2) (hleft : rangeProjection C * D = D) (hs : D.IsSymm) : Prop :=
  D = rangeProjection C * D * (rangeProjection C).map star ∧
  (∀ i j, ‖D i j‖ ≤ 2 * Real.sqrt (projectionWeight C i * projectionWeight C j)) ∧
  (∀ i, sqRow D i ≤ 4 * projectionWeight C i) ∧
  hsSq D ≤ 4 * (Fintype.card B : ℝ)

def range_localization (d : ℕ) (c K : ℝ) (hc : 0 < c) (hK : c ≤ K) : Prop :=
  ∃ a L : ℝ, 0 < a ∧ 0 < L ∧
    ∀ (b n : ℕ) (t : ℝ) (r : Fin n → ℂ) (ρ : Fin n → ℝ)
      (H : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin b) ℂ),
    0 < t → t ≤ 1 → BroadBounds c K r → ExteriorGeometry d ρ H C t r →
    (∀ v ∈ matrixRange C,
      ‖Matrix.toEuclideanLin (exponentialWeight a t ρ) v‖ ≤ L * ‖v‖) ∧
    (∀ i, projectionWeight C i ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i))

def core_decay (t c a L : ℝ) (p : R → ℝ) (ρ : R → ℝ)
    (C : Matrix R B ℂ) (dh ds : Matrix R R ℂ)
    (ht : 0 < t) (hc : 0 < c) (hL : 0 ≤ L) (hp : ∀ i, c ≤ p i)
    (hD : ‖ds‖ ≤ 2) (hleft : rangeProjection C * ds = ds) (hs : ds.IsSymm)
    (hrelation : ds = (2 * Complex.I * (Real.sqrt t : ℂ)) •
      (sqrtDamping p * dh * sqrtDamping p))
    (hdecay : ∀ i, projectionWeight C i ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i)) : Prop :=
  ∀ i j, ‖dh i j‖ ≤ L ^ 2 / (c * Real.sqrt t) *
    Real.exp (-a * t * (ρ i + ρ j))

def ridge_calculus (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) : Prop :=
  ridgeProjection C τ = ridgeRows C τ * (ridgeRows C τ)ᴴ ∧
  ridgeDefect C τ = (τ : ℂ) • (ridgeGram C τ)⁻¹ ∧
  (ridgeDefect C τ).PosSemidef ∧ (1 - ridgeDefect C τ).PosSemidef ∧
  (∀ i, 0 ≤ leverage C τ i ∧ leverage C τ i ≤ projectionWeight C i) ∧
  totalWeight (leverage C τ) = (((ridgeRows C τ)ᴴ * ridgeRows C τ).trace).re ∧
  totalWeight (leverage C τ) ≤ (Matrix.rank C : ℝ) ∧
  Matrix.rank C ≤ Fintype.card B

def ridge_limit (C : Matrix R B ℂ) : Prop :=
  Tendsto (ridgeProjection C) (nhdsWithin 0 (Set.Ioi 0)) (nhds (rangeProjection C))

def ridge_derivative (C : Matrix R B ℂ) (i : R) (τ : ℝ) (hτ : 0 < τ) : Prop :=
  HasDerivAt (fun s => leverage C s i)
    (-((C * ((ridgeGram C τ)⁻¹ * (ridgeGram C τ)⁻¹) * Cᴴ) i i).re) τ ∧
  0 ≤ ((C * ((ridgeGram C τ)⁻¹ * (ridgeGram C τ)⁻¹) * Cᴴ) i i).re

def ridge_continuous_monotone (C : Matrix R B ℂ) (i : R) : Prop :=
  ContinuousOn (fun τ => leverage C τ i) (Set.Ioi 0) ∧
  AntitoneOn (fun τ => leverage C τ i) (Set.Ioi 0) ∧
  ((∃ b, C i b ≠ 0) → StrictAntiOn (fun τ => leverage C τ i) (Set.Ioi 0))

def ridge_threshold (C : Matrix R B ℂ) (l : ℝ)
    (hl : 0 < l) (hlarge : 2 * l < maxWeight (projectionWeight C)) : Prop :=
  0 < ridgeThreshold C l ∧ maxWeight (leverage C (ridgeThreshold C l)) = 2 * l ∧
  ∀ τ, 0 < τ → maxWeight (leverage C τ) = 2 * l → τ = ridgeThreshold C l

def ridge_threshold_measurable (l : ℝ) (hl : 0 < l) : Prop :=
  Measurable (fun C : Matrix R B ℂ => ridgeThreshold C l) ∧
  Measurable (fun C : Matrix R B ℂ => rangeProjection C)

def ridge_initial (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l) (hsmall : l < 2)
    (hC : ‖C‖ ≤ 1) : Prop :=
  maxWeight (leverage C (l ^ (-2 : ℤ))) ≤ l ^ 2 ∧ l ^ 2 < 2 * l

def ridge_potential_monotone (l : ℝ) (m n : R → ℝ) (hl : 0 ≤ l)
    (hm : ∀ i, 0 ≤ m i) (hincr : ∀ i, m i ≤ n i) (hcap : ∀ i, n i ≤ 2 * l) : Prop :=
  potential l n - potential l m ≤ -6 * l * (totalWeight n - totalWeight m) ∧
  potential l n ≤ potential l m

def heat_potential_drift (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (ε l : ℝ) (running : ℕ → Set Ω)
    (pre post : ℕ → Ω → ι → ℝ) (hl : 0 < l) (hε : 0 ≤ ε ∧ ε ≤ 1 / 20)
    (hinput : LeverageDriftInput μ F ε running pre post)
    (hmax : ∀ k ω, ω ∈ running k → 2 * l ≤ maxWeight (pre k ω)) : Prop :=
  ∀ k, ∀ᵐ ω ∂μ, ω ∈ running k →
    μ[(fun ω => potential l (post k ω) - potential l (pre k ω)) | F k] ω ≤
      -(1 / 2) * (maxWeight (pre k ω)) ^ 2

def heat_count (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (l r : ℝ) (N : ℕ)
    (stop σ : Ω → ℕ) (Φ : ℕ → Ω → ℝ) (hl : 0 < l) (hr : 0 < r)
    (hinput : StoppedPotentialInput μ F l r N stop Φ)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ))) : Prop :=
  (∀ᵐ ω ∂μ, μ[(fun ω => ((stop ω - σ ω : ℕ) : ℝ)) | hσ.measurableSpace] ω ≤ 5 * r / l) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ,
    conditionalProbability μ hσ.measurableSpace {ω | n ≤ stop ω - σ ω} ω ≤
      2 * Real.exp (-Real.log 2 * (n : ℝ) / (⌈10 * r / l⌉₊ : ℝ)))

def heat_limit_margin (d : ℕ) (hd : 3 ≤ d) : Prop :=
  ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
    (1 / 2) * t ^ (-(eh - e0 - nu d)) ≤
      (heatLimit t : ℝ) * leverageScale t / coreCap d t

def construct_stopped_trial [Nonempty ι] (core : Finset ι) (t c K : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (ξ : ι → Ω → ℝ) (F0 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (order : ι ≃ Fin (Fintype.card ι)) (ht : 0 < t) (hl : leverageScale t < 2)
    (hN : 1 ≤ heatLimit t) (hr : ∀ ω, BroadBounds c K (r ω)) (hM : ∀ ω, (M0 ω).IsSymm)
    (hM0 : StronglyMeasurable[F0] M0) (hr0 : StronglyMeasurable[F0] r)
    (hξ : ∀ i, Measurable (ξ i)) (hF : F0 ≤ mΩ)
    (hterminal : ∀ ω (T : Finset ι), IsUnit
      (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι)) (fun i : {i // i ∈ T} => (i : ι))).det)) : Prop :=
  ∃ q : StoppedTrial core t r (fun ω => activeInverse (M0 ω) t (r ω)) order,
    (∀ k, q.history k = queryHistory F0 q.pivot q.residual k) ∧
    (∀ ω (i j : {i // i ∈ (q.state 0 ω).active}), (q.state 0 ω).M i j = M0 ω i j) ∧
    (∀ k ω, k < q.stop ω → q.residual k ω = ξ (q.pivot k ω) ω) ∧
    (∀ k ω, q.stop ω ≤ k → q.state k ω = q.state (q.stop ω) ω)

def fourth_distortion (t : ℝ) (g0 hg : Matrix ι ι ℂ) (ht : 0 < t)
    (hbudget : BudgetsHold t g0 hg) : Prop :=
  ∀ i, fourthRow (scaledInverse t (hg - g0)) i ≤ t ^ (1 + (109 / 100) * delta)

def prestate_from_budgets (K : ℝ) (hK : 1 ≤ K) (q : ℝ → ℝ)
    (hq : Tendsto q (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) : Prop :=
  ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
    ∀ (n : ℕ) (r : Fin n → ℂ) (g0 hg : Matrix (Fin n) (Fin n) ℂ),
    (∀ i, ‖r i‖ ≤ K) →
    (∀ i, fourthRow (scaledInverse t g0) i ≤ (4 / 5) * fourthCap t) →
    (∀ i, ‖g0 i i - r i‖ ≤ q t * t ^ betaW) → BudgetsHold t g0 hg →
    HeatPrestate t (3 * K + 1) r hg

def pivot_fourth (t : ℝ) (n : ℕ) (pivot : Fin n → ι)
    (g0 : Matrix ι ι ℂ) (g : Fin n → Matrix ι ι ℂ) (i : ι)
    (hinj : Function.Injective pivot)
    (hbudget : ∀ k, ‖g k i (pivot k) - g0 i (pivot k)‖ ≤ entryBudget t) : Prop :=
  ∑ k, ‖scaledInverse t (g k) i (pivot k)‖ ^ 4 ≤
    8 * fourthRow (scaledInverse t g0) i +
      8 * (n : ℝ) * (Real.sqrt t * entryBudget t) ^ 4

def pivot_mass (n : ℕ) (F : Fin n → ℝ) (hF : ∀ k, 0 ≤ F k) : Prop :=
  ∑ k, F k ≤ Real.sqrt ((n : ℝ) * ∑ k, (F k) ^ 2)

def ward_row_bound (t c K : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ)
    (ht : 0 < t) (hc : 0 < c) (hp : ∀ i, c ≤ p i)
    (hdiag : ∀ i, ‖g i i‖ ≤ K)
    (hWard : (t : ℂ) • (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ) = matrixImag g) : Prop :=
  ∀ i, (∑ j, p j * ‖scaledInverse t g i j‖ ^ 2) = (g i i).im ∧
    sqRow (scaledInverse t g) i ≤ K / c

def core_resolvent (g : Matrix (B ⊕ R) (B ⊕ R) ℂ) (V : Matrix B B ℂ)
    (hg : IsUnit g.det) (hV : IsUnit V.det)
    (hnew : IsUnit (g⁻¹ + Matrix.fromBlocks V 0 0 0).det) : Prop :=
  IsUnit (1 + V * coreBlock g).det ∧
  survivorBlock ((g⁻¹ + Matrix.fromBlocks V 0 0 0)⁻¹) - survivorBlock g =
    -(crossBlock g * (1 + V * coreBlock g)⁻¹ * V * g.submatrix Sum.inl Sum.inr)

def heat_update (t : ℝ) (r : ι → ℂ) (g : Matrix ι ι ℂ) (x : ι) (ξ : ℝ)
    (ht : 0 < t) (hg : IsUnit g.det)
    (hden : 1 + ((ξ : ℂ) + (t : ℂ) * r x) * g x x ≠ 0) : Prop :=
  ((g⁻¹ + Matrix.diagonal (fun i => if i = x then (ξ : ℂ) + (t : ℂ) * r x else 0))⁻¹).submatrix
    (fun i : {i : ι // i ≠ x} => (i : ι)) (fun i : {i : ι // i ≠ x} => (i : ι)) =
    heatInverse t r g x ξ

def heat_moments (K : ℝ) (hK : 1 ≤ K) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∃ L t0 : ℝ, 0 < L ∧ 0 < t0 ∧ ∀ (t η : ℝ) (rx gxx : ℂ) (ξ : Ω → ℝ),
    0 < t → t < t0 → ‖rx‖ + ‖gxx‖ ≤ K →
    ‖gxx - rx‖ ≤ K * t ^ betaW → Measurable ξ →
    (∀ ω, |ξ ω| ≤ K * Real.sqrt t) → (∫ ω, ξ ω ∂μ) = 0 →
    (∫ ω, (ξ ω) ^ 2 ∂μ) = t - η → 0 ≤ η / t → η / t ≤ K * t →
    (∀ ω, ‖heatCoefficient t rx gxx (ξ ω)‖ ≤ L) ∧
    ‖∫ ω, heatCoefficient t rx gxx (ξ ω) ∂μ‖ ≤ L * Real.sqrt t * t ^ betaW ∧
    |(∫ ω, ‖heatCoefficient t rx gxx (ξ ω)‖ ^ 2 ∂μ) - 1| ≤ L * (Real.sqrt t + η / t)

def pivot_location (d : ℕ) (a L : ℝ) (ha : 0 < a) (hL : 0 < L) : Prop :=
  ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
    ∀ (m dist : ι → ℝ) (ell : ℝ),
    (1 / 256) * t ^ (-4 : ℤ) ≤ ell →
    (∀ i, m i ≤ L * Real.exp (-2 * a * t *
      max (dist i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0)) →
    ∀ x, 2 * leverageScale t ≤ m x → dist x < ell / 2

def prefix_interval_bound (l : ℝ) (Z : ℕ → ℝ) (hl : 0 ≤ l)
    (hprefix : ∀ s, |∑ k ∈ Finset.range s, Z k| ≤ l / 2) : Prop :=
  ∀ k0 s, k0 ≤ s → |∑ k ∈ Finset.Ico k0 s, Z k| ≤ l

def two_sided_stream_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (c l J V : ℝ) (N : ℕ)
    (Z v : ℕ → Ω → ℝ) (hl : 0 < l) (hJ : 0 < J) (hV : 0 < V)
    (hconc : VectorConcentrationInput μ F c)
    (hadapted : ∀ k, StronglyMeasurable[F (k + 1)] (Z k))
    (hint : ∀ k, Integrable (Z k) μ)
    (hbias : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range N, |μ[Z k | F k] ω| ≤ l / 4)
    (hv : ∀ k, StronglyMeasurable[F k] (v k)) (hvpos : ∀ k ω, 0 ≤ v k ω)
    (hjump : ∀ k, ∀ᵐ ω ∂μ, |Z k ω - μ[Z k | F k] ω| ≤ J)
    (hvar : ∀ k, ∀ᵐ ω ∂μ,
      μ[(fun ω => (Z k ω - μ[Z k | F k] ω) ^ 2) | F k] ω ≤ v k ω)
    (hbudget : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range N, v k ω ≤ V) : Prop :=
  ∀ᵐ ω ∂μ,
    conditionalProbability μ (F 0) {ω | ∃ n ≤ N, l / 2 < |∑ k ∈ Finset.range n, Z k ω|} ω ≤
      4 * Real.exp (-c * min (l ^ 2 / (16 * V)) (l / (4 * J)))

def distortion_margin_identities (t : ℝ) (ht : 0 < t) : Prop :=
  (entryBudget t) ^ 2 / (fourthCap t / t) = t ^ (-(16 / 100) * delta) ∧
  entryBudget t / Real.sqrt (fourthCap t / t) = t ^ (-(8 / 100) * delta) ∧
  (t ^ ((125 / 1000) * delta)) ^ 2 / t ^ ((27 / 100) * delta) =
    t ^ (-(2 / 100) * delta) ∧
  t ^ betaW * t ^ ((27 / 100) * delta) = t ^ ((63 / 100) * delta)

def exponential_shell_tail (d : ℕ) (c : ℝ) (hc : 0 < c) : Prop :=
  ∃ K c' t0 : ℝ, 0 < K ∧ 0 < c' ∧ 0 < t0 ∧ ∀ t : ℝ, 0 < t → t < t0 →
    (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
      then (1 + (n : ℝ)) ^ (d - 1) * Real.exp (-c * t * n) else 0) ≤
        K * t ^ (-(d : ℝ)) * Real.exp (-c' * t ^ (-4 : ℤ))

def leverage_one_row_estimates (d : ℕ) (c K Cloc : ℝ) (hc : 0 < c) (hK : 1 ≤ K)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∃ L t0 : ℝ, 0 < L ∧ 0 < t0 ∧
    ∀ (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
    0 < t → t < t0 → (core.card : ℝ) ≤ coreCap d t → (∀ ω, BroadBounds c K (r ω)) →
    TrialLocalInput q μ d c K Cloc dist collapsed ell →
    (∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2) →
    (∀ k ω, k < q.stop ω → HeatPrestate t K
      (fun i : {i // i ∈ (q.state k ω).active} => r ω i) (trialInverse t (r ω) (q.state k ω))) →
    ∀ k i, (∀ᵐ ω ∂μ, k < q.stop ω →
      |μ[(fun ω => recordedLeverageIncrement q k ω i) | q.history k] ω| ≤
        oneRowBias d t L ‖heatV q k ω i‖) ∧
      (∀ ω, k < q.stop ω → |recordedLeverageIncrement q k ω i| ≤
        oneRowJump t L ‖heatV q k ω i‖)

def leverage_bias_margins (d : ℕ) (hd : 3 ≤ d) : Prop :=
  Tendsto (fun t : ℝ =>
    t ^ ((265 / 1000) * delta) + t ^ ((27 / 100) * delta) + t ^ ((34 / 100) * delta) +
    t ^ (1 / 2 - (2 / 100) * delta) + t ^ (1 / 2 + (48 / 100) * delta - nu d) +
    t ^ ((345 / 1000) * delta) + t ^ ((42 / 100) * delta))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
  (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
    (heatLimit t : ℝ) * (leverageScale t) ^ 2 / t ≤ t ^ ((27 / 100) * delta))

def preparation_of_small_component (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t) : Prop :=
  0 < clearingExponent d ∧ ∃ t0 : ℝ, 0 < t0 ∧
    ∀ (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
    0 < t → t < t0 → 1 ≤ core.card → (core.card : ℝ) ≤ coreCap d t →
    (∀ ω, BroadBounds c K (r ω)) →
    (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
    (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
    TrialLocalInput q μ d c K Cloc dist collapsed ell →
    VectorConcentrationInput μ q.history cConc →
    LeverageDriftInput μ q.history (ε t) (fun k => {ω | k < q.stop ω})
      (onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω)))
      (onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω))) →
    (∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) {ω | q.outcome ω = .fail} ω ≤
      Real.exp (-t ^ (-clearingExponent d))) ∧
    (∀ ω, q.outcome ω = .done →
      q.stop ω < heatLimit t ∧ BudgetsHold t (g0 ω) (q.state (q.stop ω) ω).hatG ∧
      projectionReady t (r ω) (q.state (q.stop ω) ω) ∧
      ((q.state 0 ω).active \ (q.state (q.stop ω) ω).active).card = q.stop ω)

end AndersonAC.S6.Planned
