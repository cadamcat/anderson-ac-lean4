import Mathlib
import AndersonAC.Blueprint.FiniteInputs

/-! Concrete Section 6 definitions. This module imports no planning theorems. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator NNReal ComplexOrder
open Filter MeasureTheory ProbabilityTheory

namespace AndersonAC.S6

def delta : ℝ := 1 / 100
def nu (d : ℕ) : ℝ := (1 / 100000) * delta / (d : ℝ)
def betaW : ℝ := (36 / 100) * delta
def e0 : ℝ := (44 / 100) * delta
def eh : ℝ := (46 / 100) * delta
def fourthCap (t : ℝ) : ℝ := t ^ (1 + delta)
def coreCap (d : ℕ) (t : ℝ) : ℝ := t ^ (-nu d)
def leverageScale (t : ℝ) : ℝ := t ^ (1 + e0)
def heatLimit (t : ℝ) : ℕ := ⌊t ^ (-1 - eh)⌋₊
def entryBudget (t : ℝ) : ℝ := t ^ ((42 / 100) * delta)
def rowBudget (t : ℝ) : ℝ := t ^ ((25 / 100) * delta)
def frobeniusBudget (t : ℝ) : ℝ := (heatLimit t : ℝ) * t ^ (-(1 / 100) * delta)

variable {ι B R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

def sqRow (H : Matrix ι ι ℂ) (i : ι) : ℝ := ∑ j, ‖H i j‖ ^ 2
def fourthRow (H : Matrix ι ι ℂ) (i : ι) : ℝ := ∑ j, ‖H i j‖ ^ 4
def hsSq (H : Matrix ι ι ℂ) : ℝ := ∑ i, sqRow H i
def scaledInverse (t : ℝ) (g : Matrix ι ι ℂ) : Matrix ι ι ℂ := (Real.sqrt t : ℂ) • g
def imagDamping (r : ι → ℂ) : ι → ℝ := fun i => (r i).im
def dampedMatrix (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) : Matrix ι ι ℂ :=
  M.map Complex.ofReal - (t : ℂ) • Matrix.diagonal r
def activeInverse (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) : Matrix ι ι ℂ :=
  (dampedMatrix M t r)⁻¹
def sqrtDamping (p : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (p i) : ℂ))
abbrev opNorm (A : Matrix ι ι ℂ) : ℝ := AndersonAC.Blueprint.opNorm A
abbrev twoSidedInverse (A G : Matrix ι ι ℂ) : Prop := AndersonAC.Blueprint.twoSidedInverse A G
abbrev matrixImag (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := AndersonAC.Blueprint.matrixImag A
def scatteringOfDamping (t : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1 + (2 * Complex.I * (t : ℂ)) • (sqrtDamping p * g * sqrtDamping p)
/- Same argument order and formula as Blueprint.scattering; generalized index type. -/
def scattering (t : ℝ) (r : ι → ℂ) (g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  scatteringOfDamping t (imagDamping r) g

/- Aliases to the integrated architecture contracts; no copied contract bodies. -/
abbrev WardInput := AndersonAC.Blueprint.WardInput
abbrev ScatteringInput := AndersonAC.Blueprint.ScatteringInput
def crossBlock (S : Matrix (B ⊕ R) (B ⊕ R) ℂ) : Matrix R B ℂ :=
  S.submatrix Sum.inr Sum.inl
def survivorBlock (S : Matrix (B ⊕ R) (B ⊕ R) ℂ) : Matrix R R ℂ :=
  S.submatrix Sum.inr Sum.inr
def coreBlock (S : Matrix (B ⊕ R) (B ⊕ R) ℂ) : Matrix B B ℂ :=
  S.submatrix Sum.inl Sum.inl
def matrixRange (C : Matrix R B ℂ) : Submodule ℂ (EuclideanSpace ℂ R) :=
  LinearMap.range (Matrix.toEuclideanLin C)
def rangeProjection (C : Matrix R B ℂ) : Matrix R R ℂ :=
  (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).symm (matrixRange C).starProjection
def projectionWeight (C : Matrix R B ℂ) (i : R) : ℝ := (rangeProjection C i i).re
def gram (C : Matrix R B ℂ) : Matrix B B ℂ := Cᴴ * C
def ridgeGram (C : Matrix R B ℂ) (τ : ℝ) : Matrix B B ℂ := gram C + (τ : ℂ) • 1
def ridgeInvSqrt (C : Matrix R B ℂ) (τ : ℝ) : Matrix B B ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram C τ)
def ridgeRows (C : Matrix R B ℂ) (τ : ℝ) : Matrix R B ℂ := C * ridgeInvSqrt C τ
def ridgeProjection (C : Matrix R B ℂ) (τ : ℝ) : Matrix R R ℂ :=
  C * (ridgeGram C τ)⁻¹ * Cᴴ
def leverage (C : Matrix R B ℂ) (τ : ℝ) (i : R) : ℝ := (ridgeProjection C τ i i).re
def maxWeight (m : R → ℝ) : ℝ := (Finset.univ.sup (fun i => Real.toNNReal (m i)) : ℝ≥0)
def totalWeight (m : R → ℝ) : ℝ := ∑ i, m i
def squareWeight (m : R → ℝ) : ℝ := ∑ i, (m i) ^ 2
def potential (l : ℝ) (m : R → ℝ) : ℝ := squareWeight m - 10 * l * totalWeight m
def ridgeDefect (C : Matrix R B ℂ) (τ : ℝ) : Matrix B B ℂ :=
  1 - (ridgeRows C τ)ᴴ * ridgeRows C τ

def BroadBounds (c K : ℝ) (r : ι → ℂ) : Prop :=
  0 < c ∧ ∀ i, ‖r i‖ ≤ K ∧ c ≤ (r i).im ∧ (r i).im ≤ K
def HeatPrestate (t K : ℝ) (r : ι → ℂ) (g : Matrix ι ι ℂ) : Prop :=
  (∀ i, ‖g i i‖ + ‖r i‖ ≤ K) ∧
  (∀ i, ‖g i i - r i‖ ≤ K * t ^ betaW) ∧
  (∀ i, fourthRow (scaledInverse t g) i ≤ fourthCap t)
def BudgetsHold (t : ℝ) (g0 hg : Matrix ι ι ℂ) : Prop :=
  (∀ i j, ‖hg i j - g0 i j‖ ≤ entryBudget t) ∧
  (∀ i, sqRow (scaledInverse t (hg - g0)) i ≤ rowBudget t) ∧
  hsSq (scaledInverse t (hg - g0)) ≤ frobeniusBudget t

/- Edge costs are zero precisely when an endpoint is terminal. -/
def edgeCost (T : Finset ι) (i j : ι) : ℕ := if i ∈ T ∨ j ∈ T then 0 else 1
def walkCost {G : SimpleGraph ι} (T : Finset ι) {i j : ι} : G.Walk i j → ℕ
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ a b _ _ w => edgeCost T a b + walkCost T w
/- Used only on connected lattice graphs; disconnected pairs otherwise have value zero. -/
def collapsedDistance (G : SimpleGraph ι) (T : Finset ι) (i j : ι) : ℕ :=
  sInf {n | ∃ w : G.Walk i j, walkCost T w = n}
def distanceToCore (dist : ι → ι → ℝ) (core : Finset ι) (i : ι) : ℝ :=
  if h : core.Nonempty then core.inf' h (dist i) else 0
def exteriorRadius (dist : R → ℝ) (i : R) : ℝ := max (dist i - 1) 0
def exponentialWeight (a t : ℝ) (ρ : R → ℝ) : Matrix R R ℂ :=
  Matrix.diagonal (fun i => (Real.exp (a * t * ρ i) : ℂ))

/- True completion changes only core diagonal potentials. -/
def CoreDiagonalChange (M N : Matrix (B ⊕ R) (B ⊕ R) ℝ) : Prop :=
  ∀ i j, (i ≠ j ∨ (∃ k, i = Sum.inr k) ∨ (∃ k, j = Sum.inr k)) → N i j = M i j
def trueCoreMatrix (N : Matrix (B ⊕ R) (B ⊕ R) ℝ) : Matrix B B ℝ :=
  N.submatrix Sum.inl Sum.inl
def realSurvivor (N : Matrix (B ⊕ R) (B ⊕ R) ℝ) : Matrix R R ℝ :=
  N.submatrix Sum.inr Sum.inr -
    N.submatrix Sum.inr Sum.inl * (trueCoreMatrix N)⁻¹ * N.submatrix Sum.inl Sum.inr
def completedInverse (N : Matrix (B ⊕ R) (B ⊕ R) ℝ) (t : ℝ) (r : (B ⊕ R) → ℂ) :
    Matrix R R ℂ := activeInverse (realSurvivor N) t (r ∘ Sum.inr)
def completionDelta (M N : Matrix (B ⊕ R) (B ⊕ R) ℝ) (t : ℝ) (r : (B ⊕ R) → ℂ) :
    Matrix R R ℂ := completedInverse N t r - survivorBlock (activeInverse M t r)
def heatCoefficient (t : ℝ) (rx gxx : ℂ) (ξ : ℝ) : ℂ :=
  -((ξ : ℂ) + (t : ℂ) * rx) /
    ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + (t : ℂ) * rx) * gxx))
def heatInverse (t : ℝ) (r : ι → ℂ) (g : Matrix ι ι ℂ) (x : ι) (ξ : ℝ) :
    Matrix {i : ι // i ≠ x} {i : ι // i ≠ x} ℂ :=
  fun i j => g i j + heatCoefficient t (r x) (g x x) ξ * (Real.sqrt t : ℂ) * g i x * g x j

/- The terminal correction can be arbitrarily large but commutes with the weight.
The direct hopping has bounded row/column degree and unit-size entries.
The source condition is the exterior equation of §6, obtained from §2 Schur geometry. -/
structure ExteriorGeometry (d : ℕ) (ρ : R → ℝ) (H : Matrix R R ℂ)
    (C : Matrix R B ℂ) (t : ℝ) (r : R → ℂ) : Prop where
  radius_nonneg : ∀ i, 0 ≤ ρ i
  decomposition : ∃ J K : Matrix R R ℝ,
    J.IsSymm ∧ K.IsSymm ∧ H = dampedMatrix (J + K) t r ∧
    (∀ i j, |J i j| ≤ 1) ∧
    (∀ i, ((Finset.univ.filter (fun j => J i j ≠ 0)).card : ℝ) ≤ 2 * d) ∧
    (∀ i j, J i j ≠ 0 → |ρ i - ρ j| ≤ 1) ∧
    (∀ i j, K i j ≠ 0 → ρ i = ρ j)
  exterior_source : ∀ w ∈ matrixRange C, ∀ i, 0 < ρ i →
    (Matrix.toEuclideanLin (H * (sqrtDamping (imagDamping r))⁻¹) w) i = 0

/- Exact exponent margins; no powers or quotients are taken in ℕ. -/

/- Scattering symmetry and unitarity from §2's Ward identity. -/


/- The projection diagonal is the squared norm of coordinate evaluation. -/

/- Lemma 6.1. The old terminal set has already been Schur eliminated into M,N.
The true terminal invertibility input is exactly invertibility of the true core Schur block.
Bounds are explicit in l, so their constants are independent of volume and |B|. -/

/- Generic support estimate used by Lemma 6.1 and Corollary 6.3. -/

/- Lemma 6.2. The radius is (d_T(i,B)-1)_+; the geometry bundle is the
explicit local Schur/hopping input. The constants precede all matrix sizes. -/

/- Corollary 6.3, composed with Lemmas 6.1 and 6.2 at the interface boundary. -/

/- Ridge algebra, the spectral limit, and the derivative stated before Lemma 6.4. -/




def ridgeThreshold (C : Matrix R B ℂ) (l : ℝ) : ℝ :=
  sSup {τ : ℝ | 0 < τ ∧ 2 * l ≤ maxWeight (leverage C τ)}





variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def conditionalProbability (μ : Measure Ω) (F : MeasurableSpace Ω) (E : Set Ω) : Ω → ℝ :=
  μ[E.indicator (fun _ => (1 : ℝ)) | F]

open Classical in
/-- Weight stream restricted to legal running times, so unconstrained stopped ridges
are never used in the conditional drift or its integrability requirements. -/
def onRunning {α : Type*} (run : ℕ → Set Ω) (w : ℕ → Ω → α → ℝ) :
    ℕ → Ω → α → ℝ := fun k ω => if ω ∈ run k then w k ω else 0

/- §6.4 conclusion, supplied by opus-l64 at each predictable legal heat.
Pre/post are measured at the same positive ridge; post includes deletion of the pivot.
This is an input, not a proved theorem or an axiom declaration. -/
structure LeverageDriftInput (μ : Measure Ω) (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (ε : ℝ) (running : ℕ → Set Ω) (pre post : ℕ → Ω → ι → ℝ) : Prop where
  integrable_preA : ∀ k, Integrable (fun ω => totalWeight (pre k ω)) μ
  integrable_postA : ∀ k, Integrable (fun ω => totalWeight (post k ω)) μ
  integrable_preP : ∀ k, Integrable (fun ω => squareWeight (pre k ω)) μ
  integrable_postP : ∀ k, Integrable (fun ω => squareWeight (post k ω)) μ
  total_drift : ∀ k, ∀ᵐ ω ∂μ, ω ∈ running k →
    |μ[(fun ω => totalWeight (post k ω) - totalWeight (pre k ω)) | F k] ω| ≤
      ε * maxWeight (pre k ω)
  square_drift : ∀ k, ∀ᵐ ω ∂μ, ω ∈ running k →
    μ[(fun ω => squareWeight (post k ω) - squareWeight (pre k ω)) | F k] ω ≤
      -(1 - ε) * (maxWeight (pre k ω)) ^ 2


/- One heat per time index. Ridge decreases are included in Φ's transition;
after stop all increments vanish. This is the output of the drift/ridge algebra. -/
structure StoppedPotentialInput (μ : Measure Ω) (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (l r : ℝ) (N : ℕ) (stop : Ω → ℕ) (Φ : ℕ → Ω → ℝ) : Prop where
  stopping : IsStoppingTime F (fun ω => (stop ω : WithTop ℕ))
  finite_stop : ∀ ω, stop ω ≤ N
  adapted : StronglyAdapted F Φ
  integrable : ∀ k, Integrable (Φ k) μ
  lower : ∀ k ω, -10 * l * r ≤ Φ k ω
  pre_cap : ∀ k ω, k < stop ω → Φ k ω ≤ 0
  stopped : ∀ k ω, stop ω ≤ k → Φ (k + 1) ω = Φ k ω
  drift : ∀ k, ∀ᵐ ω ∂μ,
    μ[(fun ω => Φ (k + 1) ω - Φ k ω) | F k] ω ≤
      -2 * l ^ 2 * (if k < stop ω then 1 else 0)

/- Lemma 6.5 at any finite retained-history prefix. -/

/- The floor in n_h retains the positive exponent for small t. -/

/- Original coordinates are kept for frozen entries throughout the stopped trial. -/
structure TrialState (core : Finset ι) where
  active : Finset ι
  core_active : core ⊆ active
  M : Matrix {i // i ∈ active} {i // i ∈ active} ℝ
  symmetric : M.IsSymm
  hatG : Matrix ι ι ℂ

def trialInverse {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core) :=
  activeInverse s.M t (fun i => r i)
def trialCross {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core) :
    Matrix ι {b // b ∈ core} ℂ :=
  fun i b => if hi : i ∈ s.active then
    if i ∈ core then 0 else
      scattering t (fun i : {i // i ∈ s.active} => r i) (trialInverse t r s)
        ⟨i, hi⟩ ⟨b, s.core_active b.property⟩
    else 0
def trialWeights {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core) (τ : ℝ) :=
  leverage (trialCross t r s) τ
def projectionReady {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core) : Prop :=
  ∀ i, projectionWeight (trialCross t r s) i ≤ 2 * leverageScale t
def chooseRidge (C : Matrix R B ℂ) (l τ : ℝ) : ℝ :=
  if maxWeight (leverage C τ) < 2 * l then ridgeThreshold C l else τ
def leastMaximizer (order : ι ≃ Fin (Fintype.card ι)) (m : ι → ℝ) : Option ι :=
  ((Finset.univ.filter (fun i => m (order.symm i) = maxWeight m)).sort (· ≤ ·)).head?.map order.symm

/- One real heat and the predictable freeze mask, including a possible breaking step. -/
def HeatTransition {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (s s' : TrialState core) (x : ι) (ξ : ℝ) : Prop :=
  ∃ hx : x ∈ s.active, x ∉ core ∧ s'.active = s.active.erase x ∧
    (s.M ⟨x, hx⟩ ⟨x, hx⟩ + ξ ≠ 0) ∧
    (∀ (i j : {i // i ∈ s'.active})
      (hi : (i : ι) ∈ s.active) (hj : (j : ι) ∈ s.active),
      s'.M i j = s.M ⟨i, hi⟩ ⟨j, hj⟩ -
        s.M ⟨i, hi⟩ ⟨x, hx⟩ * s.M ⟨x, hx⟩ ⟨j, hj⟩ /
          (s.M ⟨x, hx⟩ ⟨x, hx⟩ + ξ)) ∧
    (∀ i j, s'.hatG i j = s.hatG i j +
      if hi : i ∈ s'.active then if hj : j ∈ s'.active then
        trialInverse t r s' ⟨i, hi⟩ ⟨j, hj⟩ - s.hatG i j else 0 else 0)

inductive TrialOutcome | done | fail deriving DecidableEq
instance : MeasurableSpace TrialOutcome := ⊤

@[instance_reducible] def queryHistory (F0 : MeasurableSpace Ω) (pivot : ℕ → Ω → ι)
    (residual : ℕ → Ω → ℝ) (k : ℕ) : MeasurableSpace Ω :=
  F0 ⊔ ⨆ j ∈ Finset.range k,
    (MeasurableSpace.comap (pivot j) ‹MeasurableSpace ι› ⊔
      MeasurableSpace.comap (residual j) (borel ℝ))

structure StoppedTrial (core : Finset ι) (t : ℝ) (r : Ω → ι → ℂ) (g0 : Ω → Matrix ι ι ℂ)
    (order : ι ≃ Fin (Fintype.card ι)) where
  state : ℕ → Ω → TrialState core
  ridge : ℕ → Ω → ℝ
  pivot : ℕ → Ω → ι
  residual : ℕ → Ω → ℝ
  stop : Ω → ℕ
  outcome : Ω → TrialOutcome
  history : Filtration ℕ ‹MeasurableSpace Ω›
  damping_adapted : StronglyMeasurable[history 0] r
  initial_active : ∀ ω, (state 0 ω).active = Finset.univ
  start_entries : ∀ ω, (state 0 ω).hatG = g0 ω
  start_ridge : ∀ ω, ridge 0 ω = chooseRidge (trialCross t (r ω) (state 0 ω))
    (leverageScale t) ((leverageScale t) ^ (-2 : ℤ))
  initial_inverse : ∀ ω (i j : {i // i ∈ (state 0 ω).active}),
    trialInverse t (r ω) (state 0 ω) i j = g0 ω i j
  finite_stop : ∀ ω, stop ω ≤ heatLimit t
  stopping : IsStoppingTime history (fun ω => (stop ω : WithTop ℕ))
  running_budgets : ∀ k ω, k < stop ω → BudgetsHold t (g0 ω) (state k ω).hatG
  running_ridge : ∀ k ω, k < stop ω → 0 < ridge k ω
  pivot_max : ∀ k ω, k < stop ω →
    trialWeights t (r ω) (state k ω) (ridge k ω) (pivot k ω) =
      maxWeight (trialWeights t (r ω) (state k ω) (ridge k ω))
  pivot_tie : ∀ k ω i, k < stop ω →
    trialWeights t (r ω) (state k ω) (ridge k ω) i =
      trialWeights t (r ω) (state k ω) (ridge k ω) (pivot k ω) →
    order (pivot k ω) ≤ order i
  running_cap : ∀ k ω, k < stop ω →
    2 * leverageScale t ≤ maxWeight (trialWeights t (r ω) (state k ω) (ridge k ω)) ∧
      maxWeight (trialWeights t (r ω) (state k ω) (ridge k ω)) ≤ 4 * leverageScale t
  heat : ∀ k ω, k < stop ω →
    HeatTransition t (r ω) (state k ω) (state (k + 1) ω) (pivot k ω) (residual k ω)
  ridge_rule : ∀ k ω, k + 1 < stop ω → ridge (k + 1) ω =
    chooseRidge (trialCross t (r ω) (state (k + 1) ω)) (leverageScale t) (ridge k ω)
  done_iff : ∀ ω, outcome ω = .done ↔
    stop ω < heatLimit t ∧ BudgetsHold t (g0 ω) (state (stop ω) ω).hatG ∧
      projectionReady t (r ω) (state (stop ω) ω)
  fail_reason : ∀ ω, outcome ω = .fail →
    stop ω = heatLimit t ∨ ¬BudgetsHold t (g0 ω) (state (stop ω) ω).hatG ∨
      4 * leverageScale t < maxWeight
        (trialWeights t (r ω) (state (stop ω) ω) (ridge (stop ω - 1) ω))
  entries_adapted : ∀ k i j, StronglyMeasurable[history k] (fun ω => (state k ω).hatG i j)
  cross_adapted : ∀ k, StronglyMeasurable[history k] (fun ω => trialCross t (r ω) (state k ω))
  ridge_predictable : ∀ k, StronglyMeasurable[history k] (ridge k)
  pivot_predictable : ∀ k, Measurable[history k] (pivot k)
  residual_revealed : ∀ k, StronglyMeasurable[history (k + 1)] (residual k)
  outcome_measurable : Measurable outcome

/- Construction/measurability part of Proposition 6.6. All principal true
matrices are assumed invertible as in the paper, independently of damping.
No freshness claim is needed to define the deterministic adaptive rule. -/

/- Vector version of Lemma 5.6, via a (1+dimension)-dimensional Hermitian
dilation. It remains an explicit dependency of the trial theorem. -/
def VectorConcentrationInput (μ : Measure Ω) (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (c : ℝ) : Prop :=
  ∀ (D N : ℕ) (Y : ℕ → Ω → EuclideanSpace ℂ (Fin D)) (v : ℕ → Ω → ℝ)
    (J V a : ℝ), 0 < J → 0 < V → 0 < a →
    (∀ k, StronglyMeasurable[F (k + 1)] (Y k)) →
    (∀ k, Integrable (Y k) μ) →
    (∀ k, μ[Y k | F k] =ᵐ[μ] 0) →
    (∀ k, StronglyMeasurable[F k] (v k)) →
    (∀ k ω, 0 ≤ v k ω) →
    (∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ J) →
    (∀ k, ∀ᵐ ω ∂μ, μ[(fun ω => ‖Y k ω‖ ^ 2) | F k] ω ≤ v k ω) →
    (∀ᵐ ω ∂μ, ∑ k ∈ Finset.range N, v k ω ≤ V) →
    ∀ᵐ ω ∂μ,
      conditionalProbability μ (F 0) {ω | ∃ n ≤ N, a < ‖∑ k ∈ Finset.range n, Y k ω‖} ω ≤
        2 * (D + 1) * Real.exp (-c * min (a ^ 2 / V) (a / J))

/- Local geometry/freshness inputs of §6.6, supplied by §7. Geometry is
conditional on all preceding pivot locations, not on any later outcome. -/
structure TrialLocalInput {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (μ : Measure Ω)
    (d : ℕ) (c K Cloc : ℝ) (dist : ι → ι → ℝ) (collapsed : ℕ → Ω → ι → ι → ℝ)
    (ell : ℝ) : Prop where
  dist_nonneg : ∀ i j, 0 ≤ dist i j
  dist_symm : ∀ i j, dist i j = dist j i
  dist_triangle : ∀ i j k, dist i k ≤ dist i j + dist j k
  dist_self : ∀ i, dist i i = 0
  ell_lower : (1 / 256) * t ^ (-4 : ℤ) ≤ ell
  ell_upper : ell ≤ 2 * t ^ (-4 : ℤ)
  core_ball : ∃ center, ∀ b ∈ core, dist center b ≤ t ^ (-Cloc)
  shells : ∀ i (n : ℕ),
    ((Finset.univ.filter (fun j => (n : ℝ) ≤ dist i j ∧ dist i j < n + 1)).card : ℝ) ≤
      K * (1 + (n : ℝ)) ^ (d - 1)
  volume : ∀ i (L : ℝ), 0 ≤ L →
    ((Finset.univ.filter (fun j => dist i j ≤ L)).card : ℝ) ≤ K * (1 + L) ^ d
  metric : ∀ k ω, k ≤ q.stop ω →
    (∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2) →
    ∀ i j, dist i j / 2 - t ^ (-(103 / 100 : ℝ)) ≤ collapsed k ω i j
  range_geometry : ∀ k ω, k ≤ q.stop ω →
    (∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2) →
    ∃ H : Matrix ι ι ℂ,
      ExteriorGeometry d (fun i => max (distanceToCore (collapsed k ω) core i - 1) 0)
        H (trialCross t (r ω) (q.state k ω)) t (r ω)
  resolvent_decay : ∀ k ω, k < q.stop ω →
    (∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2) →
    ∀ i j : {i // i ∈ (q.state k ω).active},
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) i j‖ ≤
        K / Real.sqrt t * Real.exp (-c * t * collapsed k ω i j)
  residual_bound : ∀ k ω, k < q.stop ω →
    distanceToCore dist core (q.pivot k ω) < ell / 2 → |q.residual k ω| ≤ K * Real.sqrt t
  residual_integrable : ∀ k, Integrable (q.residual k) μ
  residual_square_integrable : ∀ k, Integrable (fun ω => (q.residual k ω) ^ 2) μ
  residual_mean : ∀ k, ∀ᵐ ω ∂μ, k < q.stop ω →
    distanceToCore dist core (q.pivot k ω) < ell / 2 → μ[q.residual k | q.history k] ω = 0
  residual_variance : ∀ k, ∃ η : Ω → ℝ,
    StronglyMeasurable[q.history k] η ∧
    (∀ᵐ ω ∂μ, k < q.stop ω →
      distanceToCore dist core (q.pivot k ω) < ell / 2 →
      0 ≤ η ω / t ∧ η ω / t ≤ K * t ∧
        μ[(fun ω => (q.residual k ω) ^ 2) | q.history k] ω = t - η ω)







/- Sherman–Morrison in the normalization used throughout §6. -/

/- Heat coefficient moments used in the budget argument; Lemma 6.4's drift
is still supplied separately. Constants precede t and the residual law. -/

/- Range decay and local metric geometry place every admissible pivot. -/

/- The two-sided stream bounds every constant-ridge interval between
adjustments, including the candidate first cap-breaking heat. -/

/- Scalar varying-ridge stream, centered at its predictable conditional mean.
This is the precise two-sided concentration step in clearing-two-sided. -/

/- Exact threshold exponents in the distortion concentration argument. -/

/- Exponential shells remove the dependence on the ambient torus volume. -/

def clearingExponent (d : ℕ) : ℝ := (eh - e0 - nu d) / 4

def epsilonScale (d : ℕ) (t : ℝ) : ℝ :=
  t ^ betaW + Real.sqrt t + coreCap d t * Real.sqrt (fourthCap t)
def recordedLeverageIncrement {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) (i : ι) : ℝ :=
  if k < q.stop ω ∧ i ∈ (q.state (k + 1) ω).active ∧ i ∉ core then
    trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω) i -
      trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i else 0
def heatV {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) (i : ι) : ℂ :=
  if hi : i ∈ (q.state k ω).active then
    if hx : q.pivot k ω ∈ (q.state k ω).active then
      scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩ ⟨q.pivot k ω, hx⟩ *
        (Real.sqrt ((r ω i).im / (r ω (q.pivot k ω)).im) : ℂ)
    else 0 else 0
def oneRowBias (d : ℕ) (t L v : ℝ) : ℝ :=
  L * leverageScale t * (Real.sqrt t * t ^ betaW * v + v ^ 2 +
    leverageScale t * epsilonScale d t + leverageScale t * v / Real.sqrt t +
      (leverageScale t) ^ 2 / t)
def oneRowJump (t L v : ℝ) : ℝ := L * leverageScale t * (v + leverageScale t / Real.sqrt t)

/- Equations one-row-bias and one-row-jump: no uniform lower singular value
or discretization of the selected positive ridge is assumed. -/

/- The displayed bias exponent list and variance margin after summing over
distinct pivots. All scalar limits are uniform in the original row. -/

/- Proposition 6.6 probability/output part. Lemma 6.4 and Lemma 5.6 are
explicit hypotheses. qlag expresses the uniform little-oh at trial start.
The threshold t0 precedes the torus size, matrices, component and trial. -/

end AndersonAC.S6
