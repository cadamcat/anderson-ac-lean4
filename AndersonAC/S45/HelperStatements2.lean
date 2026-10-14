import AndersonAC.S45.Definitions

/-! Helper contracts frozen by agent-s45 (definitions only, no holes). -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

/-- Corrected form of `AndersonAC.S45.conditional_centering`. In the Phase 1
statement, `‹MeasurableSpace Ω›` and the measurability of `AEStronglyMeasurable B μ`
resolve to the sub-σ-algebra `m` (the most recent local instance), so `hm` reads
`m ≤ m` and `B` is assumed `m`-measurable: true but useless. Here the ambient
σ-algebra `mΩ` is declared after `m`, so it is the instance. -/
def ConditionalCenteringFixed : Prop :=
  ∀ (Ω P H : Type) (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (_hm : m ≤ mΩ)
    (B : Ω → Matrix P H ℂ) (J : ℝ),
    AEStronglyMeasurable B μ → 0 ≤ J → (∀ᵐ ω ∂μ, ‖B ω‖ ≤ J) →
    (∀ᵐ ω ∂μ, ‖B ω - μ[B | m] ω‖ ≤ 2 * J) ∧
    (μ[(fun ω => (B ω - μ[B | m] ω) * (B ω - μ[B | m] ω)ᴴ) | m] =ᵐ[μ]
      fun ω => μ[(fun ω => B ω * (B ω)ᴴ) | m] ω - μ[B | m] ω * (μ[B | m] ω)ᴴ) ∧
    μ[(fun ω => (B ω - μ[B | m] ω)ᴴ * (B ω - μ[B | m] ω)) | m] =ᵐ[μ]
      fun ω => μ[(fun ω => (B ω)ᴴ * B ω) | m] ω - (μ[B | m] ω)ᴴ * μ[B | m] ω

/-- Sanity check: the measurability hypothesis is for the ambient σ-algebra. -/
example (Ω : Type) (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (B : Ω → ℝ) (h : AEStronglyMeasurable B μ) : AEStronglyMeasurable[mΩ] B μ := h

/-- Each recorded Laplacian step of a well-formed sweep is symmetric with zero
row sums (04-sweep.tex:255, eq. (4.8): `L_x` is a real symmetric Laplacian on
survivors; masked by the next live set it stays one, because the ambient
`h` vanishes off the current live set). Consumed by `ordinary_sweep_endpoint`
(Schur duality) and by the hypothesis of `local_transfer`. -/
def StepLLaplacian : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] (q : AndersonAC.S45.Sequence P) (t : ℝ)
    (r : P → ℂ), q.wellFormed t r →
    (∀ k ≤ q.length, ((q.state k).state r).g.IsSymm) →
    ∀ k < q.length, (q.stepL t r k).IsSymm ∧ q.stepL t r k *ᵥ (fun _ => 1) = 0

open AndersonAC.S45 in
/-- The energy-form part of Lemma 5.5 (local transfer), 05-local-sweeps.tex:603-650:
same hypotheses as `AndersonAC.S45.local_transfer`, conclusion only the two-sided
form bound of the accumulated Laplacian record. The lead proves the J, lag, row and
validity parts of `local_transfer` from this. -/
def LocalTransferL : Prop :=
  ∀ (d : ℕ) (C c : ℝ), 1 ≤ C → 0 < c →
    ∃ C' > 0, ∃ t0 > 0, ∀ (n m : ℕ) (t b θ : ℝ)
    (dist : Fin n → Fin n → ℝ) (r : Fin n → ℂ) (res : Finset (Fin n))
    (cover : TileCover (P := Fin n) (I := Fin m) d t b C dist)
    (q : Sequence (Fin n)) (blocks : Fin cover.count → Finset ℕ) (D0 : RMat (Fin n)),
    0 < t → t < t0 → 0 < b → b ≤ t → 1 / 4 ≤ θ → θ ≤ 5 / 8 →
    ShellBounds d C dist → q.wellFormed t r → (q.state 0).live = Finset.univ →
    (∀ k < q.length, ∃! T, k ∈ blocks T) → (∀ T, blocks T ⊆ Finset.range q.length) →
    (∀ k < q.length, ∀ x, q.pivot k = some x → ∀ T, k ∈ blocks T → x ∈ cover.tile T) →
    (∀ k l, k < q.length → l < q.length → ∀ x y,
      q.pivot k = some x → q.pivot l = some y → cover.site x = cover.site y → k = l) →
    TraceTails q t C c r res dist →
    (∀ k < q.length, (q.stepL t r k).IsSymm ∧ q.stepL t r k *ᵥ (fun _ => 1) = 0) →
    formComparable (qform D0) (spatialEnergy cover.site b cover.energy) C →
    (∀ i, (q.state 0).ambientLag t r i = 0) →
    (∀ i, ((q.state 0).ambient r).fourthRow t Finset.univ i ≤ 3 / 4 * rowCap t) →
    (∀ i ∈ res, ((q.state 0).ambient r).fourthRow t res i ≤ θ^2 * rowCap t) →
    (∀ T, localBudget cover T (q.Jrecord t r (blocks T)) (q.Lrecord t r (blocks T))
      (q.lagRecord t r (blocks T)) (q.rowRecord t r Finset.univ (blocks T))
      (q.rowRecord t r res (blocks T))) →
    formAbsLe (qform (q.Lrecord t r (Finset.range q.length))) (qform D0)
      (C' * power t (delta / 8))

end AndersonAC.AgentS45
