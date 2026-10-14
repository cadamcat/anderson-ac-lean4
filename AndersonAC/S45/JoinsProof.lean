import AndersonAC.S45.Definitions
import AndersonAC.S45.GammaProof
import AndersonAC.S45.PrestateProof
import AndersonAC.S45.DuplicationProof
import AndersonAC.S45.SweepEndpointProof

/-! Composition contracts for the §4.8 table and the §4 joins.

This file deliberately does not import `Statements.lean`. The copied contracts
below let the join proofs be built independently of their upstream proofs.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

def AnalyticPrestateStmt : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n : ℕ) (t : ℝ) (s : State (Fin n)) (Λplus Wstar : Form (Fin n)),
    t < t0 → Prestate t C Λplus Wstar s →
    (∀ i, ‖s.rawLag i‖ ≤ C' * power t AndersonAC.S45.beta ∧
      |s.q i - s.p i| ≤ C' * power t AndersonAC.S45.beta ∧
      (∑ j, s.F t i j) ≤ C' ∧ ‖s.h t i i‖ ≤ C' * Real.sqrt t) ∧
    (∀ i, ‖diagonal (s.h t i) * s.h t‖^2 ≤ C' * power t (delta / 2)) ∧
    (∀ i, (s.F t ^ 3) i i ≤ C' * power t kappa * rowCap t)

def JBoundsStmt : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n Ω : Type) [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State n)
    (Λplus Wstar : Form n) (S : Finset n) (ξ : n → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    ‖∑ x ∈ S, ∫ ω, Jinc t s x (ξ x ω) ∂μ‖ ≤ C' * power t AndersonAC.S45.beta ∧
    (∀ z : n → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ u : n → ℂ,
      (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u)) +
      (∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u)) ≤
        C' * power t (delta / 2) * l2sq u)

def LaplacianBoundsStmt : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    formAbsLe (qform (∑ x ∈ S, ∫ ω, Linc t s x (ξ x ω) ∂μ))
      (qform (s.D t)) (C' * power t AndersonAC.S45.beta) ∧
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ f : P → ℝ,
      (∑ x ∈ S, l2sq (Linc t s x (z x) *ᵥ f)) ≤
        C' * power t (delta / 2) * qform (s.D t) f ∧
      (∑ x ∈ S, l1 (Linc t s x (z x) *ᵥ f)^2) ≤ C' / t * qform (s.D t) f ∧
      (∑ x ∈ S, Wstar (Linc t s x (z x) *ᵥ f)) ≤
        C' * power t (delta / 2) * qform (s.D t) f ∧
      (∀ x ∈ S, neutral (Linc t s x (z x) *ᵥ f)))

def LagBoundsStmt : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → rowNorm (s.P t) ≤ C * logFactor t →
    (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) →
      arrayA2sq S (fun i x => lagInc t s x (z x) i) ≤
        C' * logFactor t ^ 2 * power t delta) ∧
    (∀ i, ‖∑ x ∈ S, ∫ ω, lagInc t s x (ξ x ω) i ∂μ‖ ≤
      C' * (logFactor t * (power t (2 * AndersonAC.S45.beta) + Real.sqrt t) +
        logFactor t ^ 2 * power t (delta / 2)))

def FourthBoundsStmt : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S cols : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    (∀ i, |∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ| ≤
      C' * power t kappa * rowCap t) ∧
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ i,
      (∑ x ∈ S, |fourthProxy t s cols i x (z x)|^2) ≤
        C' * power t kappa * rowCap t ^ 2)

def IncrementPullbackStmt : Prop :=
  ∀ {P H : Type} [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
    (S : Finset P) (L : P → RMat P) (B : Matrix P H ℝ) (D : RMat P)
    (W Wstar : Form P) (C σ : ℝ) (_hC : 0 ≤ C) (_hσ : 0 ≤ σ)
    (_hL : ∀ x ∈ S, (L x).IsSymm)
    (_hneutral : ∀ x ∈ S, ∀ f, neutral (L x *ᵥ f))
    (_hD : ∀ f, qform D f ≤ C * W f)
    (_hB : ∀ v, W (B *ᵥ v) ≤ C * l2sq v)
    (_hdual : ∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y)
    (_hstack : ∀ f, (∑ x ∈ S, Wstar (L x *ᵥ f)) ≤ σ * qform D f),
    (∑ x ∈ S, (pullback B (L x))^2) ≤ (C^3 * σ) • (1 : RMat H)

private theorem gram_dotProduct {I : Type*} [Fintype I] [DecidableEq I]
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix I I 𝕜) (u : I → 𝕜) :
    star u ⬝ᵥ ((Aᴴ * A) *ᵥ u) = (l2sq (A *ᵥ u) : 𝕜) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  simp only [dotProduct, l2sq]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simpa using RCLike.conj_mul ((A *ᵥ u) i)

private theorem gram_sum_dotProduct {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]
    {𝕜 : Type*} [RCLike 𝕜] (S : Finset P) (A : P → Matrix I I 𝕜) (u : I → 𝕜) :
    star u ⬝ᵥ ((∑ x ∈ S, (A x)ᴴ * A x) *ᵥ u) =
      (∑ x ∈ S, l2sq (A x *ᵥ u) : 𝕜) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp_rw [gram_dotProduct]

private theorem power_half_sq {t e : ℝ} (ht : 0 < t) :
    power t e = power t (e / 2) ^ 2 := by
  unfold power
  have h := Real.rpow_mul_natCast ht.le (e / 2) 2
  change Real.rpow t (e / 2 * (2 : ℝ)) = _ at h
  have he : e / 2 * (2 : ℝ) = e := by ring
  rw [he] at h
  exact h

private theorem gram_sum_le {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]
    {𝕜 : Type*} [RCLike 𝕜] (S : Finset P) (A : P → Matrix I I 𝕜) (R : ℝ)
    (hstack : ∀ u, (∑ x ∈ S, l2sq (A x *ᵥ u)) ≤ R * l2sq u) :
    (∑ x ∈ S, (A x)ᴴ * A x) ≤ R • (1 : Matrix I I 𝕜) := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hterms : ∀ x ∈ S, IsSelfAdjoint ((A x)ᴴ * A x) := by
      intro x hx
      exact (Matrix.isHermitian_conjTranspose_mul_self (A x)).isSelfAdjoint
    have hsum : IsSelfAdjoint (∑ x ∈ S, (A x)ᴴ * A x) :=
      isSelfAdjoint_sum S hterms
    have hId : IsSelfAdjoint (R • (1 : Matrix I I 𝕜)) := by
      change star (R • (1 : Matrix I I 𝕜)) = R • (1 : Matrix I I 𝕜)
      simp
    exact (hId.sub hsum).isHermitian
  · intro u
    have hId : star u ⬝ᵥ ((R • (1 : Matrix I I 𝕜)) *ᵥ u) =
        ((R * l2sq u : ℝ) : 𝕜) := by
      rw [Matrix.smul_mulVec, dotProduct_smul]
      have hu : star u ⬝ᵥ (1 *ᵥ u) = (l2sq u : 𝕜) := by
        simpa using (gram_dotProduct (I := I) (𝕜 := 𝕜) (A := 1) u)
      rw [hu]
      simp
    have hsum := gram_sum_dotProduct S (fun x => A x) u
    have hdiff :
        star u ⬝ᵥ ((R • (1 : Matrix I I 𝕜) - ∑ x ∈ S, (A x)ᴴ * A x) *ᵥ u) =
          ((R * l2sq u - ∑ x ∈ S, l2sq (A x *ᵥ u) : ℝ) : 𝕜) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, hId, hsum]
      push_cast
      rfl
    rw [hdiff]
    exact RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (hstack u))

private theorem gram_sum_le_implies_stack {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]
    {𝕜 : Type*} [RCLike 𝕜] (S : Finset P) (A : P → Matrix I I 𝕜) (R : ℝ)
    (hgram : (∑ x ∈ S, (A x)ᴴ * A x) ≤ R • (1 : Matrix I I 𝕜)) :
    ∀ u : I → 𝕜, (∑ x ∈ S, l2sq (A x *ᵥ u)) ≤ R * l2sq u := by
  have hpos : Matrix.PosSemidef (R • (1 : Matrix I I 𝕜) -
      ∑ x ∈ S, (A x)ᴴ * A x) := Matrix.le_iff.mp hgram
  intro u
  have hId : star u ⬝ᵥ ((R • (1 : Matrix I I 𝕜)) *ᵥ u) =
      ((R * l2sq u : ℝ) : 𝕜) := by
    rw [Matrix.smul_mulVec, dotProduct_smul]
    have hu : star u ⬝ᵥ (1 *ᵥ u) = (l2sq u : 𝕜) := by
      simpa using (gram_dotProduct (I := I) (𝕜 := 𝕜) (A := 1) u)
    rw [hu]
    simp
  have hsum := gram_sum_dotProduct S A u
  have hdiff :
      star u ⬝ᵥ ((R • (1 : Matrix I I 𝕜) - ∑ x ∈ S, (A x)ᴴ * A x) *ᵥ u) =
        ((R * l2sq u - ∑ x ∈ S, l2sq (A x *ᵥ u) : ℝ) : 𝕜) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hId, hsum]
    push_cast
    rfl
  have hq := hpos.dotProduct_mulVec_nonneg u
  rw [hdiff] at hq
  exact sub_nonneg.mp (RCLike.ofReal_nonneg.mp hq)

private theorem l2OperatorNorm_le {P : Type*} [Fintype P] [DecidableEq P]
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix P P 𝕜) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ u, l2sq (A *ᵥ u) ≤ R * l2sq u) :
    ‖A‖ ≤ Real.sqrt R := by
  rw [Matrix.cstar_norm_def]
  apply (Matrix.toEuclideanCLM (𝕜 := 𝕜) A).opNorm_le_bound (Real.sqrt_nonneg R)
  intro x
  let u : P → 𝕜 := WithLp.ofLp x
  have hx : (WithLp.toLp 2 u : EuclideanSpace 𝕜 P) = x := by simp [u]
  have hy : Matrix.toEuclideanCLM (𝕜 := 𝕜) A x =
      (WithLp.toLp 2 (A *ᵥ u) : EuclideanSpace 𝕜 P) := by
    rw [← hx, Matrix.toEuclideanCLM_toLp]
  have hnormX : ‖x‖ ^ 2 = l2sq u := by
    rw [← hx]
    simpa [l2sq] using EuclideanSpace.norm_sq_eq (WithLp.toLp 2 u : EuclideanSpace 𝕜 P)
  have hnormY :
      ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) A x‖ ^ 2 = l2sq (A *ᵥ u) := by
    rw [hy]
    simpa [l2sq] using EuclideanSpace.norm_sq_eq
      (WithLp.toLp 2 (A *ᵥ u) : EuclideanSpace 𝕜 P)
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) A x‖ ^ 2 ≤
      (Real.sqrt R * ‖x‖) ^ 2 := by
    calc
      ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) A x‖ ^ 2 ≤ R * ‖x‖ ^ 2 := by
        rw [hnormY, hnormX]
        exact hA u
      _ = (Real.sqrt R * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hR]
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg R) (norm_nonneg x))

private theorem real_square_stack_jump {P H : Type*} [Fintype P] [DecidableEq P]
    [Fintype H] [DecidableEq H]
    (S : Finset P) (A : P → RMat H) (R : ℝ) (hR : 0 ≤ R)
    (hSymm : ∀ x ∈ S, (A x).IsSymm)
    (hstack : (∑ x ∈ S, (A x) ^ 2) ≤ R • (1 : RMat H)) :
    ∀ x ∈ S, ‖A x‖ ≤ Real.sqrt R := by
  have htranspose : (∑ x ∈ S, (A x)ᴴ * A x) = ∑ x ∈ S, (A x) ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hA : (A x)ᴴ = A x := by
      simp [Matrix.IsSymm.eq (hSymm x hx)]
    rw [hA, pow_two]
  have hgram : (∑ x ∈ S, (A x)ᴴ * A x) ≤ R • (1 : RMat H) := by
    rw [htranspose]
    exact hstack
  have hAction := gram_sum_le_implies_stack (I := H) S (fun x => A x) R hgram
  intro x hx
  have hsingle : ∀ u : H → ℝ,
      l2sq (A x *ᵥ u) ≤ ∑ y ∈ S, l2sq (A y *ᵥ u) := by
    intro u
    exact Finset.single_le_sum (f := fun y => l2sq (A y *ᵥ u))
      (fun y hy => Finset.sum_nonneg fun i _ => sq_nonneg _) hx
  exact l2OperatorNorm_le (A x) R hR fun u => (hsingle u).trans (hAction u)

private theorem pad_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (A : Matrix S S ℝ) (hA : A.IsSymm) : (pad S A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [pad, hi, hj, hA.apply]
  · simp [pad, hi, hj]
  · simp [pad, hi, hj]
  · simp [pad, hi, hj]

private theorem laplacian_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (hA : A.IsSymm) : (laplacian A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · simp [laplacian, hij, Ne.symm hij, hA.apply i j]

private theorem Ledge_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (hs : s.g.IsSymm) :
    (Ledge t s x ξ).IsSymm := by
  have hh : (s.h t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [State.h, hs.apply i j]
  have hF : (s.F t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [State.F, entryAbsSquare, hh.apply i j]
  apply Matrix.IsSymm.ext
  intro i j
  unfold Ledge
  rw [hh.apply i j, hh.apply x j, hh.apply i x,
    hF.apply x j, hF.apply i x]
  ring

private theorem Linc_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (hs : s.g.IsSymm) :
    (Linc t s x ξ).IsSymm := by
  unfold Linc
  exact pad_isSymm (survivors x) _ (laplacian_isSymm _ (Ledge_isSymm t s x ξ hs))

private theorem pullback_isSymm {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (B : Matrix P H ℝ) (A : RMat P)
    (hA : A.IsSymm) : (pullback B A).IsSymm := by
  unfold pullback
  change (Bᵀ * A * B)ᵀ = Bᵀ * A * B
  simp [Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq, Matrix.mul_assoc]

private theorem qform_pullback {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] (B : Matrix P H ℝ) (A : RMat P) (v : H → ℝ) :
    qform (pullback B A) v = qform A (B *ᵥ v) := by
  change dotProduct v (((Bᵀ * A) * B) *ᵥ v) =
    dotProduct (B *ᵥ v) (A *ᵥ (B *ᵥ v))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

private def pullbackLinearMap {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (B : Matrix P H ℝ) :
    RMat P →ₗ[ℝ] RMat H where
  toFun := pullback B
  map_add' A A' := by
    ext i j
    simp [pullback, Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    ext i j
    simp [pullback, Matrix.mul_smul, Matrix.smul_mul]

private noncomputable def pullbackContinuousMap {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (B : Matrix P H ℝ) :
    RMat P →L[ℝ] RMat H where
  toLinearMap := pullbackLinearMap B
  cont := LinearMap.continuous_of_finiteDimensional (pullbackLinearMap B)

private def LedgeAtGamma {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (g : ℂ) : RMat (survivors x) :=
  fun i j => s.p i * s.p j *
    (-2 * (g * star (s.h t i j) * s.h t i x * s.h t x j).re +
      (‖g‖ ^ 2 - s.p x / (s.q x - s.p x * s.F t x x)) *
        s.F t i x * s.F t x j)

private def LincAtGamma {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (g : ℂ) : RMat P :=
  pad (survivors x) (laplacian (LedgeAtGamma t s x g))

private def laplacianLinearMap {P : Type*} [Fintype P] [DecidableEq P] :
    RMat P →ₗ[ℝ] RMat P where
  toFun := laplacian
  map_add' A B := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hsum :
          (∑ k, if k = i then 0 else (A + B) i k) =
            (∑ k, if k = i then 0 else A i k) +
              (∑ k, if k = i then 0 else B i k) := by
        calc
          (∑ k, if k = i then 0 else (A + B) i k) =
              ∑ k, ((if k = i then 0 else A i k) + (if k = i then 0 else B i k)) := by
                apply Finset.sum_congr rfl
                intro k hk
                by_cases hki : k = i <;> simp [hki]
          _ = _ := by rw [Finset.sum_add_distrib]
      calc
        laplacian (A + B) i i =
            (∑ k, if k = i then 0 else (A + B) i k) := by
              dsimp [laplacian]
              rw [if_pos rfl]
        _ = _ := hsum
        _ = (laplacian A + laplacian B) i i := by
              dsimp [laplacian]
              rw [if_pos rfl, if_pos rfl]
    · simp [laplacian, hij]
      ring
  map_smul' c A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [laplacian, Finset.mul_sum]
    · simp [laplacian, hij]

private def padLinearMap {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) : Matrix S S ℝ →ₗ[ℝ] RMat P where
  toFun := pad S
  map_add' A B := by
    ext i j
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [pad, hi, hj]
  map_smul' c A := by
    ext i j
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [pad, hi, hj]

private theorem Linc_integrable_of_gamma_bound {Ω P : Type} [MeasurableSpace Ω]
    [Fintype P] [DecidableEq P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : State P) (x : P)
    (t : ℝ) (ξ : Ω → ℝ) (hξ : Measurable ξ) (G : ℝ)
    (hγ : ∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ ≤ G) :
    Integrable (fun ω => Linc t s x (ξ ω)) μ := by
  let F : ℂ → RMat P := fun g => LincAtGamma t s x g
  have hEdge : Continuous (fun g => LedgeAtGamma t s x g) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    dsimp [LedgeAtGamma]
    fun_prop
  have hLap : Continuous (laplacianLinearMap (P := survivors x)) :=
    LinearMap.continuous_of_finiteDimensional (laplacianLinearMap (P := survivors x))
  have hPad : Continuous (padLinearMap (P := P) (survivors x)) :=
    LinearMap.continuous_of_finiteDimensional (padLinearMap (P := P) (survivors x))
  have hF : Continuous F := by
    change Continuous (fun g => padLinearMap (survivors x)
      (laplacianLinearMap (P := survivors x) (LedgeAtGamma t s x g)))
    exact hPad.comp (hLap.comp hEdge)
  let N : ℂ → ℝ := fun g => ‖F g‖
  have hN : Continuous N := continuous_norm.comp hF
  let Kball : Set ℂ := Metric.closedBall 0 G
  have hKball : IsCompact Kball := by
    simpa [Kball] using isCompact_closedBall (0 : ℂ) G
  have hBdd : BddAbove (N '' Kball) := hKball.bddAbove_image hN.continuousOn
  rcases hBdd with ⟨M, hM⟩
  let M' := max M 0
  have hbound : ∀ᵐ ω ∂μ,
      ‖LincAtGamma t s x (gamma t s x (ξ ω))‖ ≤ M' := by
    filter_upwards [hγ] with ω hω
    have hmem : gamma t s x (ξ ω) ∈ Kball := by
      simpa [Kball, Metric.mem_closedBall, dist_eq_norm] using hω
    have hmem' : N (gamma t s x (ξ ω)) ∈ N '' Kball :=
      ⟨gamma t s x (ξ ω), hmem, rfl⟩
    change N (gamma t s x (ξ ω)) ≤ M'
    exact (hM hmem').trans (le_max_left M 0)
  have hγmeas : Measurable (fun ω => gamma t s x (ξ ω)) := by
    unfold gamma
    fun_prop
  have hmeas : Measurable (fun ω => LincAtGamma t s x (gamma t s x (ξ ω))) :=
    hF.measurable.comp hγmeas
  have hInt : Integrable (fun ω => LincAtGamma t s x (gamma t s x (ξ ω))) μ :=
    ⟨hmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded hbound⟩
  have hEq : (fun ω => Linc t s x (ξ ω)) =
      fun ω => LincAtGamma t s x (gamma t s x (ξ ω)) := by
    funext ω
    rfl
  simpa only [hEq]

private theorem integral_pullback_sum {Ω P H : Type*} [MeasurableSpace Ω]
    [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
    (μ : Measure Ω) (S : Finset P) (B : Matrix P H ℝ)
    (Y : P → Ω → RMat P) (hInt : ∀ x ∈ S, Integrable (Y x) μ) :
    (∑ x ∈ S, ∫ ω, pullback B (Y x ω) ∂μ) =
      pullback B (∑ x ∈ S, ∫ ω, Y x ω ∂μ) := by
  calc
    (∑ x ∈ S, ∫ ω, pullback B (Y x ω) ∂μ) =
        ∑ x ∈ S, pullback B (∫ ω, Y x ω ∂μ) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (pullbackContinuousMap B).integral_comp_comm (hInt x hx)
    _ = pullback B (∑ x ∈ S, ∫ ω, Y x ω ∂μ) := by
          change ∑ x ∈ S, pullbackLinearMap B (∫ ω, Y x ω ∂μ) = _
          exact (map_sum (pullbackLinearMap B) (fun x => ∫ ω, Y x ω ∂μ) S).symm

private noncomputable def transposeContinuousMap {P : Type*} [Fintype P]
    [DecidableEq P] : RMat P →L[ℝ] RMat P where
  toLinearMap := (Matrix.transposeLinearEquiv P P ℝ ℝ).toLinearMap
  cont := LinearMap.continuous_of_finiteDimensional _

private theorem integral_isSymm {Ω P : Type*} [MeasurableSpace Ω] [Fintype P]
    [DecidableEq P] (μ : Measure Ω) (F : Ω → RMat P) (hInt : Integrable F μ)
    (hF : ∀ ω, (F ω).IsSymm) : (∫ ω, F ω ∂μ).IsSymm := by
  have hcomp : (∫ ω, (F ω)ᵀ ∂μ) = (∫ ω, F ω ∂μ)ᵀ := by
    simpa [transposeContinuousMap, Matrix.transposeLinearEquiv] using
      (transposeContinuousMap (P := P)).integral_comp_comm hInt
  change (∫ ω, F ω ∂μ)ᵀ = ∫ ω, F ω ∂μ
  calc
    (∫ ω, F ω ∂μ)ᵀ = ∫ ω, (F ω)ᵀ ∂μ := hcomp.symm
    _ = ∫ ω, F ω ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall fun ω => (hF ω).eq)

private theorem finite_sum_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (A : P → RMat P) (hA : ∀ x ∈ S, (A x).IsSymm) :
    (∑ x ∈ S, A x).IsSymm := by
  change (∑ x ∈ S, A x)ᵀ = ∑ x ∈ S, A x
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun x hx => (hA x hx).eq

private theorem real_symm_opNorm_le_of_qform {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (R : ℝ) (hR : 0 ≤ R) (hA : A.IsSymm)
    (hquad : ∀ v, |qform A v| ≤ R * l2sq v) : ‖A‖ ≤ R := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hHerm : A.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
  have hT : T.IsSymmetric := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) A :
      EuclideanSpace ℝ P →ₗ[ℝ] EuclideanSpace ℝ P).IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  have hnorm : ‖A‖ = ‖T‖ := by
    dsimp [T]
    exact Matrix.cstar_norm_def A
  rw [hnorm, T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · subst x
    simpa using hR
  let v : P → ℝ := WithLp.ofLp x
  have hx' : (WithLp.toLp 2 v : EuclideanSpace ℝ P) = x := by simp [v]
  have hnormSq : ‖x‖ ^ 2 = l2sq v := by
    rw [← hx']
    simpa [l2sq] using EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v : EuclideanSpace ℝ P)
  have hform : T.reApplyInnerSelf x = qform A v := by
    rw [← hx']
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm,
      Matrix.inner_toEuclideanCLM]
    simp [qform, dotProduct]
  have hnum : |T.reApplyInnerSelf x| ≤ R * ‖x‖ ^ 2 := by
    rw [hform, hnormSq]
    exact hquad v
  have hden : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_of_pos hden]
  exact (div_le_iff₀ hden).2 hnum

private theorem l1_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (f : ι → ℝ) : l1 (f ∘ e) = l1 f := by
  unfold l1
  exact Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp])

private theorem l2sq_comp_equiv {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [RCLike α] (e : κ ≃ ι) (f : ι → α) : l2sq (f ∘ e) = l2sq f := by
  unfold l2sq
  exact Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp])

private theorem neutral_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (y : κ → ℝ) (hy : neutral y) : neutral (y ∘ e.symm) := by
  unfold neutral at hy ⊢
  calc
    (∑ i, y (e.symm i)) = ∑ i, y i :=
      Fintype.sum_equiv e.symm _ _ (fun i => by simp [Function.comp])
    _ = 0 := hy

private theorem submatrix_one_sub {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Ring α] (e : κ ≃ ι) (A : Matrix ι ι α) :
    (1 - A).submatrix e e = 1 - A.submatrix e e := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.submatrix_apply, hij]

private theorem State.reindex_P {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (s : State ι) (t : ℝ) :
    (State.reindex e s).P t = (s.P t).submatrix e e := by
  simp only [State.P, State.reindex_K]
  rw [← submatrix_one_sub e (s.K t)]
  exact Matrix.inv_submatrix_equiv (1 - s.K t) e e

private theorem State.reindex_lag {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (s : State ι) (t : ℝ) :
    (State.reindex e s).lag t = s.lag t ∘ e := by
  change (State.reindex e s).P t *ᵥ (s.rawLag ∘ e) = s.lag t ∘ e
  rw [State.reindex_P, Matrix.submatrix_mulVec_equiv]
  apply congrArg (fun f : ι → ℂ => f ∘ e)
  congr 1
  funext i
  simp

private theorem State.reindex_F {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (s : State ι) (t : ℝ) :
    (State.reindex e s).F t = (s.F t).submatrix e e := by
  ext i j
  simp [State.F, State.reindex_h, entryAbsSquare, submatrix_apply]

private theorem Prestate.reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (t C : ℝ)
    (s : State ι) (Λplus Wstar : Form ι)
    (hpre : Prestate t C Λplus Wstar s) :
    Prestate t C (fun y => Λplus (y ∘ e.symm)) (fun y => Wstar (y ∘ e.symm))
      (State.reindex e s) := by
  have hsym : (State.reindex e s).g.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hpre.symmetric.apply (e i) (e j)
  have hdiag : diagonal (fun i => ((State.reindex e s).p i : ℂ)) =
      (diagonal (fun i => (s.p i : ℂ))).submatrix e e := by
    ext i j
    by_cases hij : i = j <;> simp [State.reindex, State.p, Matrix.submatrix_apply, hij]
  have hstar : ((s.h t).submatrix e e)ᴴ = (s.h t)ᴴ.submatrix e e := by
    ext i j
    rfl
  have hmul :
      (s.h t).submatrix e e * (diagonal (fun i => (s.p i : ℂ))).submatrix e e *
          (s.h t)ᴴ.submatrix e e =
        (s.h t * diagonal (fun i => (s.p i : ℂ)) * (s.h t)ᴴ).submatrix e e := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  have hward : (State.reindex e s).ward t := by
    change (State.reindex e s).h t * diagonal (fun i => ((State.reindex e s).p i : ℂ)) *
      ((State.reindex e s).h t)ᴴ = matrixIm (State.reindex e s).g
    rw [State.reindex_h, hdiag, hstar, hmul]
    have h := congrArg (fun A : CMat ι => A.submatrix e e) hpre.ward
    calc
      (s.h t * diagonal (fun i => (s.p i : ℂ)) * (s.h t)ᴴ).submatrix e e =
          (matrixIm s.g).submatrix e e := h
      _ = matrixIm (State.reindex e s).g := by
          ext i j
          rfl
  have hKcap : ‖(State.reindex e s).K t‖ ≤ 1 / 2 := by
    rw [State.reindex_K, norm_submatrix_equiv]
    exact hpre.K_cap
  have hunit : IsUnit (1 - (State.reindex e s).K t) := by
    rw [State.reindex_K, ← submatrix_one_sub e (s.K t)]
    exact (Matrix.isUnit_submatrix_equiv e e).mpr hpre.invertible
  have hkernel : constantKernel ((State.reindex e s).D t) := by
    rcases hpre.kernel with ⟨hDsym, hDnonneg, hDzero⟩
    refine ⟨State.D_symm (State.reindex e s) t hsym, ?_, ?_⟩
    · intro f
      rw [State.reindex_D, qform_submatrix]
      exact hDnonneg _
    · intro f
      rw [State.reindex_D, qform_submatrix]
      constructor
      · intro hf
        rcases (hDzero (f ∘ e.symm)).mp hf with ⟨a, ha⟩
        refine ⟨a, fun i => ?_⟩
        simpa using ha (e i)
      · rintro ⟨a, ha⟩
        apply (hDzero (f ∘ e.symm)).mpr
        refine ⟨a, fun i => ?_⟩
        simpa using ha (e.symm i)
  have hquad : ∀ y : κ → ℝ,
      (∑ i, y i ^ 2 / (State.reindex e s).p i ^ 2) =
        ∑ i, (y ∘ e.symm) i ^ 2 / s.p i ^ 2 := by
    intro y
    unfold State.reindex State.p
    exact Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp])
  refine {
    scale := hpre.scale
    broad := ?_
    symmetric := hsym
    ward := hward
    K_cap := hKcap
    invertible := hunit
    kernel := hkernel
    row_cap := ?_
    lag_cap := ?_
    sharp := ?_
    fourier := ?_
    dual_fourier := ?_
    volume := ?_ }
  · intro i
    simpa [State.reindex, State.p] using hpre.broad (e i)
  · intro i
    rw [State.reindex_fourthRow]
    exact hpre.row_cap (e i)
  · intro i
    simpa [State.reindex_lag] using hpre.lag_cap (e i)
  · intro y hy
    have hyold : neutral (y ∘ e.symm) := neutral_comp_equiv e y hy
    have hX : (State.reindex e s).X t y = s.X t (y ∘ e.symm) := by
      change dualForm (qform ((State.reindex e s).D t)) y =
        dualForm (qform (s.D t)) (y ∘ e.symm)
      rw [State.reindex_D, dualForm_submatrix]
    calc
      (State.reindex e s).X t y = s.X t (y ∘ e.symm) := hX
      _ ≤ (1 + C * power t kappa) *
          (∑ i, (y ∘ e.symm) i ^ 2 / s.p i ^ 2) +
          C * t * Λplus (y ∘ e.symm) := hpre.sharp _ hyold
      _ = (1 + C * power t kappa) *
          (∑ i, y i ^ 2 / (State.reindex e s).p i ^ 2) +
          C * t * Λplus (y ∘ e.symm) := by
            rw [← hquad y]
  · intro y hy
    have hyold := neutral_comp_equiv e y hy
    calc
      Λplus (y ∘ e.symm) ≤ C * power (l1 (y ∘ e.symm)) (4 / 3) *
          power (l2sq (y ∘ e.symm)) (1 / 3) := hpre.fourier _ hyold
      _ = C * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3) := by
          rw [l1_comp_equiv e.symm y, l2sq_comp_equiv e.symm y]
  · intro y hy
    have hyold := neutral_comp_equiv e y hy
    calc
      Wstar (y ∘ e.symm) ≤ l2sq (y ∘ e.symm) + C * t *
          power (l1 (y ∘ e.symm)) (4 / 3) *
          power (l2sq (y ∘ e.symm)) (1 / 3) := hpre.dual_fourier _ hyold
      _ = l2sq y + C * t * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3) := by
          rw [l1_comp_equiv e.symm y, l2sq_comp_equiv e.symm y]
  · simpa [Fintype.card_congr e] using hpre.volume

theorem analytic_prestate_generic (hAnalytic : AnalyticPrestateStmt) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
      ∀ (P : Type) [Fintype P] [DecidableEq P] (t : ℝ) (s : State P)
        (Λplus Wstar : Form P),
        t < t0 → Prestate t C Λplus Wstar s →
        (∀ i, ‖s.rawLag i‖ ≤ C' * power t beta ∧
          |s.q i - s.p i| ≤ C' * power t beta ∧
          (∑ j, s.F t i j) ≤ C' ∧ ‖s.h t i i‖ ≤ C' * Real.sqrt t) ∧
        (∀ i, ‖diagonal (s.h t i) * s.h t‖^2 ≤ C' * power t (delta / 2)) ∧
        (∀ i, (s.F t ^ 3) i i ≤ C' * power t kappa * rowCap t) := by
  intro C hC
  obtain ⟨C', hC', t0, ht0, hFin⟩ := hAnalytic C hC
  refine ⟨C', hC', t0, ht0, ?_⟩
  intro P instF instD t s Λplus Wstar ht hpre
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  let s' := State.reindex e s
  let Λ' : Form (Fin (Fintype.card P)) := fun y => Λplus (y ∘ e.symm)
  let W' : Form (Fin (Fintype.card P)) := fun y => Wstar (y ∘ e.symm)
  have hpre' : Prestate t C Λ' W' s' := by
    simpa [s', Λ', W'] using Prestate.reindex e t C s Λplus Wstar hpre
  obtain ⟨hrows, hdiagonal, hcube⟩ :=
    hFin (Fintype.card P) t s' Λ' W' ht hpre'
  constructor
  · intro i
    obtain ⟨hraw, hqp, hrow, hentry⟩ := hrows (e.symm i)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [s', State.reindex, State.rawLag] using hraw
    · simpa [s', State.reindex, State.q, State.p] using hqp
    · have hsum : (∑ j : Fin (Fintype.card P), s'.F t (e.symm i) j) =
          ∑ j : P, s.F t i j := by
        rw [show s'.F t = (s.F t).submatrix e e by simp [s', State.reindex_F]]
        exact Fintype.sum_equiv e _ _ (fun j => by simp [submatrix_apply])
      rw [← hsum]
      exact hrow
    · simpa [s', State.reindex_h] using hentry
  · constructor
    · intro i
      let q : Fin (Fintype.card P) := e.symm i
      have hdiag : diagonal (s'.h t q) = (diagonal (s.h t i)).submatrix e e := by
        ext j k
        by_cases hjk : j = k <;> simp [q, s', State.reindex_h, submatrix_apply, hjk]
      have hprod : diagonal (s'.h t q) * s'.h t =
          (diagonal (s.h t i) * s.h t).submatrix e e := by
        rw [hdiag, State.reindex_h, Matrix.submatrix_mul_equiv]
      have hnorm : ‖diagonal (s'.h t q) * s'.h t‖ =
          ‖diagonal (s.h t i) * s.h t‖ := by
        rw [hprod, norm_submatrix_equiv]
      simpa [q, hnorm] using hdiagonal q
    · intro i
      have hFcube : s'.F t ^ 3 = (s.F t ^ 3).submatrix e e := by
        let R := Matrix.reindexRingEquiv ℝ e.symm
        have hR (A : RMat P) : R A = A.submatrix e e := rfl
        rw [show s'.F t = (s.F t).submatrix e e by simp [s', State.reindex_F]]
        rw [← hR (s.F t), ← hR (s.F t ^ 3)]
        exact (map_pow R (s.F t) 3).symm
      simpa [s', hFcube] using hcube (e.symm i)

/-- Convert the Laplacian form mean into an operator-norm bound after pullback. -/
theorem l_mean_from_form {Ω P H : Type} [MeasurableSpace Ω]
    [Fintype P] [DecidableEq P] [Fintype H] [DecidableEq H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t C K : ℝ) (s : State P) (S : Finset P) (B : Matrix P H ℝ)
    (W : Form P) (ξ : P → Ω → ℝ)
    (ht : 0 < t) (hC : 0 ≤ C) (hK : 0 ≤ K) (hsym : s.g.IsSymm)
    (hD : ∀ f, qform (s.D t) f ≤ C * W f)
    (hB : ∀ v, W (B *ᵥ v) ≤ C * l2sq v)
    (hForm : formAbsLe
      (qform (∑ x ∈ S, ∫ ω, Linc t s x (ξ x ω) ∂μ))
      (qform (s.D t)) (K * power t AndersonAC.S45.beta))
    (hInt : ∀ x ∈ S, Integrable (fun ω => Linc t s x (ξ x ω)) μ) :
    ‖∑ x ∈ S, ∫ ω, pullback B (Linc t s x (ξ x ω)) ∂μ‖ ≤
      C ^ 2 * K * power t AndersonAC.S45.beta := by
  let G : RMat P := ∑ x ∈ S, ∫ ω, Linc t s x (ξ x ω) ∂μ
  have hterms : ∀ x ∈ S, (∫ ω, Linc t s x (ξ x ω) ∂μ).IsSymm := by
    intro x hx
    exact integral_isSymm μ _ (hInt x hx)
      (fun ω => Linc_isSymm t s x (ξ x ω) hsym)
  have hGsym : G.IsSymm := finite_sum_isSymm S
    (fun x => ∫ ω, Linc t s x (ξ x ω) ∂μ) hterms
  have hmean :
      (∑ x ∈ S, ∫ ω, pullback B (Linc t s x (ξ x ω)) ∂μ) = pullback B G := by
    simpa [G] using integral_pullback_sum μ S B
      (fun x ω => Linc t s x (ξ x ω)) hInt
  have hQnonneg : 0 ≤ K * power t AndersonAC.S45.beta :=
    mul_nonneg hK (Real.rpow_nonneg ht.le _)
  let R := C ^ 2 * K * power t AndersonAC.S45.beta
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg (sq_nonneg C) hK) (Real.rpow_nonneg ht.le _)
  have hqform : ∀ v, |qform (pullback B G) v| ≤ R * l2sq v := by
    intro v
    rw [qform_pullback]
    have hDbound : qform (s.D t) (B *ᵥ v) ≤ C ^ 2 * l2sq v := by
      calc
        qform (s.D t) (B *ᵥ v) ≤ C * W (B *ᵥ v) := hD _
        _ ≤ C * (C * l2sq v) := mul_le_mul_of_nonneg_left (hB v) hC
        _ = C ^ 2 * l2sq v := by ring
    calc
      |qform G (B *ᵥ v)| ≤
          (K * power t AndersonAC.S45.beta) * qform (s.D t) (B *ᵥ v) := hForm _
      _ ≤ (K * power t AndersonAC.S45.beta) * (C ^ 2 * l2sq v) :=
          mul_le_mul_of_nonneg_left hDbound hQnonneg
      _ = R * l2sq v := by dsimp [R]; ring
  have hMnorm := real_symm_opNorm_le_of_qform (pullback B G) R hR
    (pullback_isSymm B G hGsym) hqform
  rw [hmean]
  exact hMnorm

/-- Pull the Laplacian square stack through the extension matrix and obtain
single-increment operator bounds. -/
theorem l_square_jump_from_bounds {P H : Type} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H]
    (t C K : ℝ) (s : State P) (S : Finset P) (B : Matrix P H ℝ)
    (W Wstar : Form P) (ht : 0 < t) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsym : s.g.IsSymm)
    (hD : ∀ f, qform (s.D t) f ≤ C * W f)
    (hB : ∀ v, W (B *ᵥ v) ≤ C * l2sq v)
    (hdual : ∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y)
    (hLap : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ f : P → ℝ,
      (∑ x ∈ S, Wstar (Linc t s x (z x) *ᵥ f)) ≤
        K * power t (delta / 2) * qform (s.D t) f ∧
      (∀ x ∈ S, neutral (Linc t s x (z x) *ᵥ f)))
    (hInc : IncrementPullbackStmt) :
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) →
      (∑ x ∈ S, (pullback B (Linc t s x (z x))) ^ 2) ≤
        (C ^ 3 * K * power t (delta / 2)) • (1 : RMat H)) ∧
    (∀ x ∈ S, ∀ z, |z| ≤ C * Real.sqrt t →
      ‖pullback B (Linc t s x z)‖ ≤
        (Real.sqrt (C ^ 3 * K) + 1) * power t (delta / 4)) := by
  let σ := K * power t (delta / 2)
  let Q := C ^ 3 * K
  let R := C ^ 3 * σ
  have hσ : 0 ≤ σ := mul_nonneg hK (Real.rpow_nonneg ht.le _)
  have hQ : 0 ≤ Q := mul_nonneg (pow_nonneg hC _) hK
  have hR : 0 ≤ R := mul_nonneg (pow_nonneg hC _) hσ
  have hpow : power t (delta / 2) = power t (delta / 4) ^ 2 := by
    have h := power_half_sq (t := t) (e := delta / 2) ht
    have he : (delta / 2) / 2 = delta / 4 := by ring
    rw [he] at h
    exact h
  have hReq : R = Q * power t (delta / 2) := by
    dsimp [R, Q, σ]
    ring
  have hcoeff : Q ≤ (Real.sqrt Q + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg Q]
  have hhalf : 0 ≤ power t (delta / 4) := (Real.rpow_pos_of_pos ht _).le
  constructor
  · intro z hz
    have hL : ∀ x ∈ S, (Linc t s x (z x)).IsSymm := by
      intro x hx
      exact Linc_isSymm t s x (z x) hsym
    have hneutral : ∀ x ∈ S, ∀ f, neutral (Linc t s x (z x) *ᵥ f) := by
      intro x hx f
      exact (hLap z hz f).2 x hx
    have hstack : ∀ f,
        (∑ x ∈ S, Wstar (Linc t s x (z x) *ᵥ f)) ≤ σ * qform (s.D t) f := by
      intro f
      simpa [σ] using (hLap z hz f).1
    have hbound := hInc (P := P) (H := H) S (fun x => Linc t s x (z x)) B
      (s.D t) W Wstar C σ hC hσ hL hneutral hD hB hdual hstack
    simpa [σ, R, mul_assoc] using hbound
  · intro x hx z hz
    let Z : P → ℝ := fun y => if y = x then z else 0
    let Lfun : P → RMat P := fun y => Linc t s y (Z y)
    let A : P → RMat H := fun y => pullback B (Lfun y)
    have hzs : ∀ y ∈ S, |Z y| ≤ C * Real.sqrt t := by
      intro y hy
      by_cases hyx : y = x
      · subst y
        simpa [Z] using hz
      · simpa [Z, hyx] using mul_nonneg hC (Real.sqrt_nonneg t)
    have hLsym : ∀ y ∈ S, (Lfun y).IsSymm := by
      intro y hy
      exact Linc_isSymm t s y (if y = x then z else 0) hsym
    have hAsym : ∀ y ∈ S, (A y).IsSymm := by
      intro y hy
      exact pullback_isSymm B _ (hLsym y hy)
    have hneutral : ∀ y ∈ S, ∀ f, neutral (Lfun y *ᵥ f) := by
      intro y hy f
      exact (hLap Z hzs f).2 y hy
    have hstack : ∀ f, (∑ y ∈ S, Wstar (Lfun y *ᵥ f)) ≤ σ * qform (s.D t) f := by
      intro f
      simpa [σ] using (hLap Z hzs f).1
    have hmat : (∑ y ∈ S, (A y) ^ 2) ≤ R • (1 : RMat H) := by
      have h := hInc (P := P) (H := H) S Lfun B (s.D t) W Wstar C σ
        hC hσ hLsym hneutral hD hB hdual hstack
      simpa [A, R, σ, Lfun] using h
    have hjump := real_square_stack_jump (P := P) (H := H) S A R hR hAsym hmat x hx
    have hlarge : R ≤ ((Real.sqrt Q + 1) * power t (delta / 4)) ^ 2 := by
      rw [hReq, hpow]
      calc
        Q * power t (delta / 4) ^ 2 ≤
            (Real.sqrt Q + 1) ^ 2 * power t (delta / 4) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
        _ = ((Real.sqrt Q + 1) * power t (delta / 4)) ^ 2 := by ring
    have htarget_nonneg : 0 ≤ (Real.sqrt Q + 1) * power t (delta / 4) :=
      mul_nonneg (by positivity) hhalf
    have hroot : Real.sqrt R ≤ (Real.sqrt Q + 1) * power t (delta / 4) := by
      apply le_of_sq_le_sq ?_ htarget_nonneg
      rw [Real.sq_sqrt hR]
      exact hlarge
    have hA : A x = pullback B (Linc t s x z) := by simp [A, Lfun, Z]
    rw [hA] at hjump
    exact hjump.trans hroot

/-- The two matrix square stacks and the single-jump bound from the J estimate. -/
theorem j_table_estimates {P : Type} [Fintype P] [DecidableEq P]
    (t scalarC K : ℝ) (s : State P) (S : Finset P)
    (ht : 0 < t) (hscalarC : 0 ≤ scalarC) (hK : 0 ≤ K)
    (hstack : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) →
      ∀ u : P → ℂ,
        (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u)) +
        (∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u)) ≤
          K * power t (delta / 2) * l2sq u) :
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) →
      (∑ x ∈ S, Jinc t s x (z x) * (Jinc t s x (z x))ᴴ) ≤
        (K * power t (delta / 2)) • (1 : CMat P) ∧
      (∑ x ∈ S, (Jinc t s x (z x))ᴴ * Jinc t s x (z x)) ≤
        (K * power t (delta / 2)) • (1 : CMat P)) ∧
    (∀ x ∈ S, ∀ z, |z| ≤ scalarC * Real.sqrt t →
      ‖Jinc t s x z‖ ≤ (Real.sqrt K + 1) * power t (delta / 4)) := by
  let R := K * power t (delta / 2)
  have hhalf : 0 ≤ power t (delta / 4) := (Real.rpow_pos_of_pos ht _).le
  have hpow : power t (delta / 2) = power t (delta / 4) ^ 2 := by
    have h := power_half_sq (t := t) (e := delta / 2) ht
    have he : (delta / 2) / 2 = delta / 4 := by ring
    rw [he] at h
    exact h
  have hR : 0 ≤ R := mul_nonneg hK (Real.rpow_nonneg ht.le _)
  have hlsq_nonneg (u : P → ℂ) : 0 ≤ l2sq u :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfirst (z : P → ℝ) (hz : ∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t)
      (u : P → ℂ) :
      (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u)) ≤ R * l2sq u := by
    have hsecond : 0 ≤ ∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u) :=
      Finset.sum_nonneg fun x _ => hlsq_nonneg _
    have h := hstack z hz u
    dsimp [R]
    linarith
  have hsecond (z : P → ℝ) (hz : ∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t)
      (u : P → ℂ) :
      (∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u)) ≤ R * l2sq u := by
    have hfirstNonneg : 0 ≤ ∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u) :=
      Finset.sum_nonneg fun x _ => hlsq_nonneg _
    have h := hstack z hz u
    dsimp [R]
    linarith
  constructor
  · intro z hz
    constructor
    · have h := gram_sum_le S (fun x => (Jinc t s x (z x))ᴴ) R
          (fun u => hsecond z hz u)
      simpa [R] using h
    · exact gram_sum_le S (fun x => Jinc t s x (z x)) R (fun u => hfirst z hz u)
  · intro x hx z hz
    let zs : P → ℝ := fun y => if y = x then z else 0
    have hzs : ∀ y ∈ S, |zs y| ≤ scalarC * Real.sqrt t := by
      intro y hy
      by_cases hxy : y = x
      · subst y
        simpa [zs] using hz
      · simp [zs, hxy]
        exact mul_nonneg hscalarC (Real.sqrt_nonneg _)
    have hsingle : ∀ u : P → ℂ,
        l2sq (Jinc t s x z *ᵥ u) ≤ R * l2sq u := by
      intro u
      have hsingle' : l2sq (Jinc t s x (zs x) *ᵥ u) ≤
          ∑ y ∈ S, l2sq (Jinc t s y (zs y) *ᵥ u) :=
        Finset.single_le_sum (f := fun y => l2sq (Jinc t s y (zs y) *ᵥ u))
          (fun y hy => hlsq_nonneg _) hx
      have hsum := hfirst zs hzs u
      simpa [zs] using hsingle'.trans hsum
    have hnorm := l2OperatorNorm_le (Jinc t s x z) R hR hsingle
    have hcoef : K ≤ (Real.sqrt K + 1) ^ 2 := by
      nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K]
    have hlarge : R ≤ ((Real.sqrt K + 1) * power t (delta / 4)) ^ 2 := by
      dsimp [R]
      calc
        K * power t (delta / 2) = K * power t (delta / 4) ^ 2 := by rw [hpow]
        _ ≤ (Real.sqrt K + 1) ^ 2 * power t (delta / 4) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
        _ = ((Real.sqrt K + 1) * power t (delta / 4)) ^ 2 := by ring
    have htarget_nonneg : 0 ≤ (Real.sqrt K + 1) * power t (delta / 4) :=
      mul_nonneg (by positivity) hhalf
    have hroot : Real.sqrt R ≤ (Real.sqrt K + 1) * power t (delta / 4) := by
      apply le_of_sq_le_sq ?_ htarget_nonneg
      rw [Real.sq_sqrt hR]
      exact hlarge
    exact hnorm.trans hroot

private theorem rowCap_pos {t : ℝ} (ht : 0 < t) : 0 < rowCap t :=
  Real.rpow_pos_of_pos ht _

/-- Normalize the fourth-power estimates by their row scale. -/
theorem normalized_row_estimates {P Ω : Type} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t scalarC K : ℝ) (s : State P) (S cols : Finset P) (ξ : P → Ω → ℝ)
    (ht : 0 < t) (hK : 0 ≤ K)
    (hmean : ∀ i, |∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ| ≤
      K * power t kappa * rowCap t)
    (hsquare : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) → ∀ i,
      (∑ x ∈ S, |fourthProxy t s cols i x (z x)|^2) ≤
        K * power t kappa * rowCap t ^ 2) :
    (∀ i, |∑ x ∈ S, ∫ ω,
      fourthProxy t s cols i x (ξ x ω) / rowCap t ∂μ| ≤
        (K + 1) * power t kappa) ∧
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) → ∀ i,
      (∑ x ∈ S, |fourthProxy t s cols i x (z x) / rowCap t|^2) ≤
        (K + 1) * power t kappa) ∧
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) → ∀ i x,
      x ∈ S → |fourthProxy t s cols i x (z x) / rowCap t| ≤
        (K + 1) * power t (kappa / 2)) := by
  let H := rowCap t
  have hH : 0 < H := rowCap_pos ht
  have hH2 : 0 < H ^ 2 := sq_pos_of_pos hH
  have hpw : 0 ≤ power t kappa := (Real.rpow_pos_of_pos ht _).le
  constructor
  · intro i
    have hsum := hmean i
    have hscale :
        (∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) / H ∂μ) =
          (∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ) / H := by
      simp_rw [integral_div]
      rw [Finset.sum_div]
    rw [hscale, abs_div, abs_of_pos hH]
    have hdiv := div_le_div_of_nonneg_right hsum hH.le
    have hcancel :
        (K * power t kappa * H) / H = K * power t kappa := by
      field_simp [ne_of_gt hH]
    rw [hcancel] at hdiv
    calc
      |∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ| / H ≤
          K * power t kappa := hdiv
      _ ≤ (K + 1) * power t kappa := by
          nlinarith [hpw]
  · constructor
    · intro z hz i
      have hsum := hsquare z hz i
      have hscale :
          (∑ x ∈ S, |fourthProxy t s cols i x (z x) / H|^2) =
            (∑ x ∈ S, |fourthProxy t s cols i x (z x)|^2) / H ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_div, abs_of_pos hH, div_pow]
      rw [hscale]
      have hdiv := div_le_div_of_nonneg_right hsum hH2.le
      have hcancel :
          (K * power t kappa * H ^ 2) / H ^ 2 = K * power t kappa := by
        field_simp [ne_of_gt hH]
      rw [hcancel] at hdiv
      calc
        (∑ x ∈ S, |fourthProxy t s cols i x (z x)|^2) / H ^ 2 ≤
            K * power t kappa := hdiv
        _ ≤ (K + 1) * power t kappa := by
            nlinarith [hpw]
    · intro z hz i x hx
      have hsum := hsquare z hz i
      have hsingle : |fourthProxy t s cols i x (z x)| ^ 2 ≤
          ∑ y ∈ S, |fourthProxy t s cols i y (z y)| ^ 2 :=
        Finset.single_le_sum
          (f := fun y => |fourthProxy t s cols i y (z y)| ^ 2)
          (fun y hy => sq_nonneg _) hx
      have hterm : |fourthProxy t s cols i x (z x)| ^ 2 ≤
          K * power t kappa * H ^ 2 := hsingle.trans hsum
      have hdiv := div_le_div_of_nonneg_right hterm hH2.le
      have hcancel :
          (K * power t kappa * H ^ 2) / H ^ 2 = K * power t kappa := by
        field_simp [ne_of_gt hH]
      rw [hcancel] at hdiv
      have hquot : (|fourthProxy t s cols i x (z x)| / H) ^ 2 ≤
          K * power t kappa := by
        have heq :
            (|fourthProxy t s cols i x (z x)| / H) ^ 2 =
              |fourthProxy t s cols i x (z x)| ^ 2 / H ^ 2 := by ring
        rw [heq]
        exact hdiv
      have hhalf : 0 ≤ power t (kappa / 2) :=
        (Real.rpow_pos_of_pos ht _).le
      have hcoef : K ≤ (K + 1) ^ 2 := by nlinarith [sq_nonneg K]
      have hlarge : K * power t kappa ≤
          ((K + 1) * power t (kappa / 2)) ^ 2 := by
        calc
          K * power t kappa = K * power t (kappa / 2) ^ 2 := by
            rw [power_half_sq ht]
          _ ≤ (K + 1) ^ 2 * power t (kappa / 2) ^ 2 :=
            mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
          _ = ((K + 1) * power t (kappa / 2)) ^ 2 := by ring
      have htarget_nonneg : 0 ≤ (K + 1) * power t (kappa / 2) :=
        mul_nonneg (by linarith) hhalf
      calc
        |fourthProxy t s cols i x (z x) / H| =
            |fourthProxy t s cols i x (z x)| / H := by
              rw [abs_div, abs_of_pos hH]
        _ ≤ (K + 1) * power t (kappa / 2) :=
              le_of_sq_le_sq (hquot.trans hlarge) htarget_nonneg

private theorem logFactor_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 ≤ logFactor t := by
  have hinv : 1 ≤ 1 / t := by
    rw [le_div_iff₀ ht]
    nlinarith
  simp only [logFactor]
  exact add_nonneg (by norm_num) (Real.log_nonneg hinv)

/-- Turn the lag helper's uniform array estimate into its row estimates. -/
theorem lag_table_estimates {P Ω : Type} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t C K : ℝ) (s : State P) (S : Finset P)
    (ξ : P → Ω → ℝ) (ht : 0 < t) (ht1 : t < 1) (hC0 : 0 ≤ C) (hK : 0 ≤ K)
    (hmean : ∀ i, ‖∑ x ∈ S, ∫ ω, lagInc t s x (ξ x ω) i ∂μ‖ ≤
      K * (logFactor t * (power t (2 * AndersonAC.S45.beta) + Real.sqrt t) +
        logFactor t ^ 2 * power t (delta / 2)))
    (harray : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) →
      arrayA2sq S (fun i x => lagInc t s x (z x) i) ≤
        K * logFactor t ^ 2 * power t delta) :
    (∀ i, ‖∑ x ∈ S, ∫ ω, lagInc t s x (ξ x ω) i ∂μ‖ ≤
      K * (logFactor t * (power t (2 * AndersonAC.S45.beta) + Real.sqrt t) +
        logFactor t ^ 2 * power t (delta / 2))) ∧
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ i,
      (∑ x ∈ S, ‖lagInc t s x (z x) i‖^2) ≤ K * logFactor t ^ 2 * power t delta) ∧
    (∀ x ∈ S, ∀ z, |z| ≤ C * Real.sqrt t → ∀ i,
      ‖lagInc t s x z i‖ ≤
        (K + 1) * logFactor t * power t (delta / 2)) := by
  have hlog : 0 ≤ logFactor t := logFactor_nonneg ht ht1
  have hhalf : 0 ≤ power t (delta / 2) := (Real.rpow_pos_of_pos ht _).le
  have hpower : 0 ≤ power t delta := (Real.rpow_pos_of_pos ht _).le
  have hcoef : K ≤ (K + 1) ^ 2 := by nlinarith [sq_nonneg K]
  let A (z : P → ℝ) (i : P) := ∑ x ∈ S, ‖lagInc t s x (z x) i‖ ^ 2
  have hA_nonneg (z : P → ℝ) (i : P) : 0 ≤ A z i := by
    dsimp [A]
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  have hA_le_array (z : P → ℝ) (i : P) :
      A z i ≤ arrayA2sq S (fun i x => lagInc t s x (z x) i) := by
    have h := norm_le_pi_norm (A z) i
    rw [Real.norm_eq_abs, abs_of_nonneg (hA_nonneg z i)] at h
    simpa [A, arrayA2sq] using h
  constructor
  · exact hmean
  · constructor
    · intro z hz i
      exact (hA_le_array z i).trans (harray z hz)
    · intro x hx z hz i
      let zs : P → ℝ := fun y => if y = x then z else 0
      have hzs : ∀ y ∈ S, |zs y| ≤ C * Real.sqrt t := by
        intro y hy
        by_cases hxy : y = x
        · subst y
          simpa [zs] using hz
        · simp [zs, hxy]
          exact mul_nonneg hC0 (Real.sqrt_nonneg _)
      have hsum := (hA_le_array zs i).trans (harray zs hzs)
      have hsingle : ‖lagInc t s x z i‖ ^ 2 ≤
          ∑ y ∈ S, ‖lagInc t s y (zs y) i‖ ^ 2 := by
        have hsingle' := Finset.single_le_sum
          (f := fun y => ‖lagInc t s y (zs y) i‖ ^ 2)
          (fun y hy => sq_nonneg _) hx
        simpa [zs] using hsingle'
      have hterm : ‖lagInc t s x z i‖ ^ 2 ≤ K * logFactor t ^ 2 * power t delta :=
        hsingle.trans hsum
      have hlarge : K * logFactor t ^ 2 * power t delta ≤
          ((K + 1) * logFactor t * power t (delta / 2)) ^ 2 := by
        calc
          K * logFactor t ^ 2 * power t delta =
              K * (logFactor t ^ 2 * power t (delta / 2) ^ 2) := by
                rw [power_half_sq ht]
                ring
          _ ≤ (K + 1) ^ 2 * (logFactor t ^ 2 * power t (delta / 2) ^ 2) :=
                mul_le_mul_of_nonneg_right hcoef
                  (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ = ((K + 1) * logFactor t * power t (delta / 2)) ^ 2 := by ring
      have htarget_nonneg : 0 ≤ (K + 1) * logFactor t * power t (delta / 2) :=
        mul_nonneg (mul_nonneg (by linarith) hlog) hhalf
      exact le_of_sq_le_sq (hterm.trans hlarge) htarget_nonneg

private theorem smul_one_mono {P 𝕜 : Type*} [Fintype P] [DecidableEq P]
    [RCLike 𝕜] {a b : ℝ} (hab : a ≤ b) :
    a • (1 : Matrix P P 𝕜) ≤ b • (1 : Matrix P P 𝕜) := by
  rw [Matrix.le_iff]
  have hdiff : b • (1 : Matrix P P 𝕜) - a • 1 = (b - a) • 1 := by
    rw [← sub_smul]
  rw [hdiff]
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (sub_nonneg.mpr hab)

set_option maxHeartbeats 1000000

theorem ordinary_increment_estimates_from_helpers
    (hAnalytic : AnalyticPrestateStmt) (hJ : JBoundsStmt)
    (hLap : LaplacianBoundsStmt) (hLag : LagBoundsStmt)
    (hFourth : FourthBoundsStmt) (hInc : IncrementPullbackStmt) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
      ∀ (P H Ω : Type) [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
        [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (t : ℝ) (s : State P) (Λplus W Wstar : Form P) (S cols : Finset P)
        (B : Matrix P H ℝ) (ξ : P → Ω → ℝ),
        t < t0 → Prestate t C Λplus Wstar s → rowNorm (s.P t) ≤ C * logFactor t →
        (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
        (∀ f, qform (s.D t) f ≤ C * W f) →
        (∀ v, W (B *ᵥ v) ≤ C * l2sq v) →
        (∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y) →
        FamilyTable μ t C C' s S cols B ξ := by
  intro C hC
  obtain ⟨Ka, hKa, ta, hta, hAnalyticC⟩ := analytic_prestate_generic hAnalytic C hC
  obtain ⟨KJ, hKJ, tJ, htJ, hJC⟩ := hJ C hC
  obtain ⟨KL, hKL, tL, htL, hLC⟩ := hLap C hC
  obtain ⟨Klag, hKlag, tlag, htlag, hLagC⟩ := hLag C hC
  obtain ⟨Kfour, hKfour, tfour, htfour, hFourthC⟩ := hFourth C hC
  let Cstate : ℝ := 2 * C + Ka + 1
  have hCstate : 1 ≤ Cstate := by
    dsimp [Cstate]
    linarith [hC, hKa]
  obtain ⟨Kgamma, hKgamma, tgamma, htgamma, hGamma⟩ :=
    gamma_moments_proof Cstate hCstate
  let Kout : ℝ := 1 + KJ + C ^ 2 * KL + C ^ 3 * KL +
    (Real.sqrt (C ^ 3 * KL) + 1) + (Real.sqrt KJ + 1) + (Klag + 1) + (Kfour + 1)
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hKL0 : 0 ≤ KL := le_of_lt hKL
  have hKJ0 : 0 ≤ KJ := le_of_lt hKJ
  have hKlag0 : 0 ≤ Klag := le_of_lt hKlag
  have hKfour0 : 0 ≤ Kfour := le_of_lt hKfour
  have hCube0 : 0 ≤ C ^ 3 * KL := mul_nonneg (pow_nonneg hC0 _) hKL0
  have hKout : 0 < Kout := by
    dsimp [Kout]
    positivity
  have hJcoef : KJ ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  have hLmeanCoef : C ^ 2 * KL ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  have hLsquareCoef : C ^ 3 * KL ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  have hLjumpCoef : Real.sqrt (C ^ 3 * KL) + 1 ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  have hJjumpCoef : Real.sqrt KJ + 1 ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  have hLagCoef : Klag ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  have hLagJumpCoef : Klag + 1 ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  have hFourCoef : Kfour + 1 ≤ Kout := by
    dsimp [Kout]
    nlinarith [Real.sqrt_nonneg KJ, Real.sqrt_nonneg (C ^ 3 * KL)]
  let t0 := min ta (min tJ (min tL (min tlag (min tfour tgamma))))
  have ht0 : 0 < t0 := by dsimp [t0]; positivity
  refine ⟨Kout, hKout, t0, ht0, ?_⟩
  intro P H Ω instP instH instDP instDH instΩ μ instμ t s Λplus W Wstar S cols B ξ
    hsmall hpre hrowNorm hMom hD hB hdual
  change t < min ta (min tJ (min tL (min tlag (min tfour tgamma)))) at hsmall
  rcases lt_min_iff.mp hsmall with ⟨htA, hmore⟩
  rcases lt_min_iff.mp hmore with ⟨htJ', hmore⟩
  rcases lt_min_iff.mp hmore with ⟨htL', hmore⟩
  rcases lt_min_iff.mp hmore with ⟨htlag', hmore⟩
  rcases lt_min_iff.mp hmore with ⟨htfour', htgamma'⟩
  have hA := hAnalyticC P t s Λplus Wstar htA hpre
  have hJraw := hJC P Ω μ t s Λplus Wstar S ξ htJ' hpre hMom
  have hLapraw := hLC P Ω μ t s Λplus Wstar S ξ htL' hpre hMom
  have hLagraw := hLagC P Ω μ t s Λplus Wstar S ξ htlag' hpre hrowNorm hMom
  have hFourthraw := hFourthC P Ω μ t s Λplus Wstar S cols ξ htfour' hpre hMom
  have hbeta0 : 0 ≤ AndersonAC.S45.beta := by
    norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
  have hpowbeta : power t AndersonAC.S45.beta ≤ 1 := by
    unfold power
    exact Real.rpow_le_one hpre.scale.1.le hpre.scale.2.le hbeta0
  have hCstateC : C ≤ Cstate := by dsimp [Cstate]; linarith [hKa]
  have hMomentState (x : P) (hx : x ∈ S) : MomentLaw μ t Cstate (ξ x) := by
    rcases hMom x hx with ⟨hmeas, hmean, hvariance, hbounded⟩
    refine ⟨hmeas, hmean, hvariance, ?_⟩
    filter_upwards [hbounded] with ω hω
    exact hω.trans (mul_le_mul_of_nonneg_right hCstateC (Real.sqrt_nonneg _))
  have hstateBound (x : P) : ‖s.g x x‖ + ‖s.r x‖ ≤ Cstate := by
    have hraw := (hA.1 x).1
    have hr := (hpre.broad x).1
    have hdiag : ‖s.g x x‖ ≤ ‖s.rawLag x‖ + ‖s.r x‖ := by
      have heq : s.g x x = s.rawLag x + s.r x := by simp [State.rawLag]
      rw [heq]
      exact norm_add_le _ _
    calc
      ‖s.g x x‖ + ‖s.r x‖ ≤ ‖s.rawLag x‖ + 2 * ‖s.r x‖ := by linarith [hdiag]
      _ ≤ Ka * power t beta + 2 * C := by
        nlinarith [hraw, hr]
      _ ≤ Ka + 2 * C := by
        nlinarith [mul_le_mul_of_nonneg_left hpowbeta (le_of_lt hKa)]
      _ ≤ Cstate := by dsimp [Cstate]; linarith
  have hInt : ∀ x ∈ S, Integrable (fun ω => Linc t s x (ξ x ω)) μ := by
    intro x hx
    have hg := hGamma P Ω μ t s x (ξ x) hpre.scale.1 htgamma'
      (hstateBound x) (hMomentState x hx)
    have hγ : ∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω)‖ ≤ Kgamma :=
      hg.1.mono (fun ω hω => hω.1)
    exact Linc_integrable_of_gamma_bound μ s x t (ξ x) (hMom x hx).measurable
      Kgamma hγ
  obtain ⟨hJmean, hJstack⟩ := hJraw
  obtain ⟨hLform, hLstack⟩ := hLapraw
  obtain ⟨hLagarray, hLagmean⟩ := hLagraw
  obtain ⟨hFourthmean, hFourthsquare⟩ := hFourthraw
  have hJtable := j_table_estimates t C KJ s S hpre.scale.1 hC0 hKJ0 hJstack
  have hLpull : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) →
      ∀ f : P → ℝ,
        (∑ x ∈ S, Wstar (Linc t s x (z x) *ᵥ f)) ≤
          KL * power t (delta / 2) * qform (s.D t) f ∧
        (∀ x ∈ S, neutral (Linc t s x (z x) *ᵥ f)) := by
    intro z hz f
    exact ⟨(hLstack z hz f).2.2.1, (hLstack z hz f).2.2.2⟩
  have hLtable := l_square_jump_from_bounds t C KL s S B W Wstar hpre.scale.1
    hC0 hKL0 hpre.symmetric hD hB hdual hLpull hInc
  have hLmean := l_mean_from_form μ t C KL s S B W ξ hpre.scale.1 hC0 hKL0
    hpre.symmetric hD hB hLform hInt
  have hLagtable := lag_table_estimates μ t C Klag s S ξ hpre.scale.1
    hpre.scale.2 hC0 hKlag0 hLagmean hLagarray
  have hFourthtable := normalized_row_estimates μ t C Kfour s S cols ξ hpre.scale.1
    hKfour0 hFourthmean hFourthsquare
  have hlog0 : 0 ≤ logFactor t := logFactor_nonneg hpre.scale.1 hpre.scale.2
  have hpowBeta0 : 0 ≤ power t AndersonAC.S45.beta := by
    unfold power
    exact (Real.rpow_pos_of_pos hpre.scale.1 _).le
  have hpowDelta2 : 0 ≤ power t (delta / 2) := by
    unfold power
    exact (Real.rpow_pos_of_pos hpre.scale.1 _).le
  have hpowKappa : 0 ≤ power t kappa := by
    unfold power
    exact (Real.rpow_pos_of_pos hpre.scale.1 _).le
  have hpowKappa2 : 0 ≤ power t (kappa / 2) := by
    unfold power
    exact (Real.rpow_pos_of_pos hpre.scale.1 _).le
  have hJmeanCoef : KJ * power t AndersonAC.S45.beta ≤ Kout * power t AndersonAC.S45.beta :=
    mul_le_mul_of_nonneg_right hJcoef hpowBeta0
  have hLmeanCoef' : C ^ 2 * KL * power t AndersonAC.S45.beta ≤
      Kout * power t AndersonAC.S45.beta :=
    mul_le_mul_of_nonneg_right hLmeanCoef hpowBeta0
  have hJpowCoef : KJ * power t (delta / 2) ≤ Kout * power t (delta / 2) :=
    mul_le_mul_of_nonneg_right hJcoef hpowDelta2
  have hLpowCoef : C ^ 3 * KL * power t (delta / 2) ≤ Kout * power t (delta / 2) :=
    mul_le_mul_of_nonneg_right hLsquareCoef hpowDelta2
  have hJjumpPow : (Real.sqrt KJ + 1) * power t (delta / 4) ≤
      Kout * power t (delta / 4) :=
    mul_le_mul_of_nonneg_right hJjumpCoef (by
      unfold power
      exact (Real.rpow_pos_of_pos hpre.scale.1 _).le)
  have hLjumpPow : (Real.sqrt (C ^ 3 * KL) + 1) * power t (delta / 4) ≤
      Kout * power t (delta / 4) :=
    mul_le_mul_of_nonneg_right hLjumpCoef (by
      unfold power
      exact (Real.rpow_pos_of_pos hpre.scale.1 _).le)
  have hLagMeanCoef : Klag ≤ Kout := hLagCoef
  have hLagJumpPow : (Klag + 1) * logFactor t * power t (delta / 2) ≤
      Kout * logFactor t * power t (delta / 2) := by
    have hfactor : 0 ≤ logFactor t * power t (delta / 2) :=
      mul_nonneg hlog0 hpowDelta2
    nlinarith [mul_le_mul_of_nonneg_right hLagJumpCoef hfactor]
  have hRowMeanPow : (Kfour + 1) * power t kappa ≤ Kout * power t kappa :=
    mul_le_mul_of_nonneg_right hFourCoef hpowKappa
  have hRowSquarePow : (Kfour + 1) * power t kappa ≤ Kout * power t kappa :=
    hRowMeanPow
  have hRowJumpPow : (Kfour + 1) * power t (kappa / 2) ≤
      Kout * power t (kappa / 2) :=
    mul_le_mul_of_nonneg_right hFourCoef hpowKappa2
  have hLagSquarePow : Klag * logFactor t ^ 2 * power t delta ≤
      Kout * logFactor t ^ 2 * power t delta := by
    have hfactor : 0 ≤ logFactor t ^ 2 * power t delta :=
      mul_nonneg (sq_nonneg _) (by
        unfold power
        exact (Real.rpow_pos_of_pos hpre.scale.1 _).le)
    nlinarith [mul_le_mul_of_nonneg_right hLagMeanCoef hfactor]
  refine {
    J_mean := hJmean.trans hJmeanCoef
    J_squares := ?_
    J_jump := ?_
    L_mean := hLmean.trans hLmeanCoef'
    L_square := ?_
    L_jump := ?_
    lag_mean := ?_
    lag_square := ?_
    lag_jump := ?_
    row_mean := ?_
    row_square := ?_
    row_jump := ?_ }
  · intro z hz
    rcases hJtable.1 z hz with ⟨h1, h2⟩
    exact ⟨h1.trans (smul_one_mono hJpowCoef), h2.trans (smul_one_mono hJpowCoef)⟩
  · intro x hx z hz
    exact (hJtable.2 x hx z hz).trans hJjumpPow
  · intro z hz
    exact (hLtable.1 z hz).trans (smul_one_mono hLpowCoef)
  · intro x hx z hz
    exact (hLtable.2 x hx z hz).trans hLjumpPow
  · intro i
    exact (hLagtable.1 i).trans (by
      have hfactor : 0 ≤ logFactor t *
          (power t (2 * AndersonAC.S45.beta) + Real.sqrt t) +
            logFactor t ^ 2 * power t (delta / 2) := by
        have hp : 0 ≤ power t (2 * AndersonAC.S45.beta) := by
          unfold power
          exact (Real.rpow_pos_of_pos hpre.scale.1 _).le
        exact add_nonneg (mul_nonneg hlog0 (add_nonneg hp (Real.sqrt_nonneg _)))
          (mul_nonneg (sq_nonneg _) hpowDelta2)
      exact (mul_le_mul_of_nonneg_right hLagMeanCoef hfactor))
  · intro z hz i
    exact (hLagtable.2.1 z hz i).trans hLagSquarePow
  · intro x hx z hz i
    exact (hLagtable.2.2 x hx z hz i).trans hLagJumpPow
  · intro i
    exact (hFourthtable.1 i).trans hRowMeanPow
  · intro z hz i
    exact (hFourthtable.2.1 z hz i).trans hRowSquarePow
  · intro x hx z hz i
    let zs : P → ℝ := fun y => if y = x then z else 0
    have hzs : ∀ y ∈ S, |zs y| ≤ C * Real.sqrt t := by
      intro y hy
      by_cases hxy : y = x
      · subst y
        simpa [zs] using hz
      · simp [zs, hxy]
        exact mul_nonneg hC0 (Real.sqrt_nonneg _)
    have h := hFourthtable.2.2 zs hzs i x hx
    simpa [zs] using h.trans hRowJumpPow


end AndersonAC.AgentS45
