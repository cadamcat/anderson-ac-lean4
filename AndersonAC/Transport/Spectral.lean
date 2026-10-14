import AndersonAC.Blueprint.Transport

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal BigOperators

namespace AndersonAC.LunaTransport

/-- Translation `t ↦ c + t` as a measurable equivalence of ℝ. -/
def shiftEquiv (c : ℝ) : ℝ ≃ᵐ ℝ where
  toEquiv :=
    { toFun := fun t => c + t
      invFun := fun t => t - c
      left_inv := fun t => by ring
      right_inv := fun t => by ring }
  measurable_toFun := by
    show Measurable (fun t : ℝ => c + t)
    fun_prop
  measurable_invFun := by
    show Measurable (fun t : ℝ => t - c)
    fun_prop

lemma shiftEquiv_map_volume (c : ℝ) :
    (volume : Measure ℝ).map (shiftEquiv c) = volume :=
  (MeasureTheory.measurePreserving_add_left (volume : Measure ℝ) c).map_eq

section Conj

variable {d : ℕ} (U : StateSpace d ≃ₗᵢ[ℂ] StateSpace d)

/-- The unitary as a continuous linear map. -/
def transA : Blueprint.Operator d :=
  U.toLinearIsometry.toContinuousLinearMap

/-- Its inverse as a continuous linear map. -/
def transB : Blueprint.Operator d :=
  U.symm.toLinearIsometry.toContinuousLinearMap

lemma transA_mul_transB : transA U * transB U = 1 :=
  ContinuousLinearMap.ext fun v => U.apply_symm_apply v

lemma transB_mul_transA : transB U * transA U = 1 :=
  ContinuousLinearMap.ext fun v => U.symm_apply_apply v

lemma transA_transB_apply (z : StateSpace d) : transA U (transB U z) = z := by
  have h := congrArg (· z) (transA_mul_transB U)
  simpa using h

lemma transB_transA_apply (z : StateSpace d) : transB U (transA U z) = z := by
  have h := congrArg (· z) (transB_mul_transA U)
  simpa using h

lemma inner_transA (x y : StateSpace d) :
    inner ℂ (transA U x) (transA U y) = inner ℂ x y :=
  U.inner_map_map x y

lemma norm_transA (x : StateSpace d) : ‖transA U x‖ = ‖x‖ :=
  U.toLinearIsometry.norm_map x

/-- The unitary as a unit of the operator algebra. -/
def conjUnit : (Blueprint.Operator d)ˣ where
  val := transA U
  inv := transB U
  val_inv := transA_mul_transB U
  inv_val := transB_mul_transA U

/-- Unitary conjugation preserves the spectrum. -/
lemma spectrum_trans_conj (X : Blueprint.Operator d) :
    spectrum ℂ (transA U * X * transB U) = spectrum ℂ X := by
  have e1 : transA U * X * transB U
      = ((conjUnit U : (Blueprint.Operator d)ˣ) : Blueprint.Operator d) * X
        * ((((conjUnit U)⁻¹ : (Blueprint.Operator d)ˣ)) : Blueprint.Operator d) :=
    rfl
  rw [e1]
  exact spectrum.units_conjugate

/-- Unitary conjugation preserves self-adjointness. -/
lemma IsSelfAdjoint_trans_conj (P : Blueprint.Operator d) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (transA U * P * transB U) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hP ⊢
  intro x y
  show inner ℂ (transA U (P (transB U x))) y
    = inner ℂ x (transA U (P (transB U y)))
  calc inner ℂ (transA U (P (transB U x))) y
      = inner ℂ (transA U (P (transB U x))) (transA U (transB U y)) := by
        rw [transA_transB_apply]
    _ = inner ℂ (P (transB U x)) (transB U y) := inner_transA U _ _
    _ = inner ℂ (transB U x) (P (transB U y)) := hP _ _
    _ = inner ℂ (transA U (transB U x)) (transA U (P (transB U y))) :=
        (inner_transA U _ _).symm
    _ = inner ℂ x (transA U (P (transB U y))) := by rw [transA_transB_apply]

/-- Powers pass through the conjugation. -/
lemma conj_pow (X : Blueprint.Operator d) (n : ℕ) :
    (transA U * X * transB U) ^ n = transA U * X ^ n * transB U := by
  induction n with
  | zero => simp [transA_mul_transB]
  | succ n ih =>
    rw [pow_succ, ih]
    calc (transA U * X ^ n * transB U) * (transA U * X * transB U)
        = transA U * (X ^ n * ((transB U * transA U) * (X * transB U))) := by
          noncomm_ring
      _ = transA U * X ^ (n + 1) * transB U := by
          rw [transB_mul_transA]; noncomm_ring

/-- Inner products against conjugated powers reduce to the original. -/
lemma inner_conj_pow (X : Blueprint.Operator d) (n : ℕ) (v : StateSpace d) :
    inner ℂ v (((transA U * X * transB U) ^ n) v)
      = inner ℂ (transB U v) ((X ^ n) (transB U v)) := by
  rw [conj_pow U X n,
    show ((transA U * X ^ n * transB U) v) = transA U ((X ^ n) (transB U v))
      from rfl]
  have step := inner_transA U (transB U v) ((X ^ n) (transB U v))
  rw [transA_transB_apply] at step
  exact step

variable (T : Blueprint.Operator d) (S : SpectralResolution T) (c : ℝ)

/-- Transported projections: `U P_{(·+c)⁻¹B} U⁻¹`. -/
def transProj (B : Set ℝ) : Blueprint.Operator d :=
  transA U * S.projection ((shiftEquiv c) ⁻¹' B) * transB U

/-- Transported scalar measures: pushforward by `t ↦ c + t`. -/
def transMeas (v : StateSpace d) : Measure ℝ :=
  (S.vectorMeasure (transB U v)).map (shiftEquiv c)

lemma transProj_apply (B : Set ℝ) (v : StateSpace d) :
    transProj U T S c B v
      = transA U (S.projection ((shiftEquiv c) ⁻¹' B) (transB U v)) := rfl

lemma transProj_empty : transProj U T S c ∅ = 0 := by
  simp [transProj, Set.preimage_empty, S.projection_empty]

lemma transProj_univ : transProj U T S c Set.univ = 1 := by
  simp only [transProj, Set.preimage_univ, S.projection_univ, mul_one]
  exact transA_mul_transB U

lemma transProj_selfAdjoint (B : Set ℝ) (hB : MeasurableSet B) :
    IsSelfAdjoint (transProj U T S c B) :=
  IsSelfAdjoint_trans_conj U _
    (S.projection_selfAdjoint _ ((shiftEquiv c).measurable hB))

lemma transProj_mul_key (P₁ P₂ : Blueprint.Operator d) :
    (transA U * P₁ * transB U) * (transA U * P₂ * transB U)
      = transA U * (P₁ * P₂) * transB U := by
  calc (transA U * P₁ * transB U) * (transA U * P₂ * transB U)
      = transA U * (P₁ * ((transB U * transA U) * (P₂ * transB U))) := by
        noncomm_ring
    _ = transA U * (P₁ * P₂) * transB U := by
        rw [transB_mul_transA]; noncomm_ring

lemma transProj_inter (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    transProj U T S c (B ∩ C)
      = transProj U T S c B * transProj U T S c C := by
  have h := S.projection_inter _ _ ((shiftEquiv c).measurable hB)
    ((shiftEquiv c).measurable hC)
  unfold transProj
  rw [Set.preimage_inter, h]
  exact (transProj_mul_key U _ _).symm

lemma transProj_iUnion (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hpair : Pairwise (fun i j => Disjoint (B i) (B j))) (v : StateSpace d) :
    HasSum (fun n => transProj U T S c (B n) v)
      (transProj U T S c (⋃ n, B n) v) := by
  have hdis : Pairwise
      (fun i j => Disjoint ((shiftEquiv c) ⁻¹' (B i)) ((shiftEquiv c) ⁻¹' (B j))) := by
    intro i j hij
    exact Disjoint.preimage _ (hpair hij)
  have hsum := S.projection_iUnion _
    (fun n => (shiftEquiv c).measurable (hB n)) hdis (transB U v)
  rw [← Set.preimage_iUnion] at hsum
  have hsumA := hsum.mapL (transA U)
  have e1 : (fun n => transProj U T S c (B n) v)
      = (fun n => transA U
        (S.projection ((shiftEquiv c) ⁻¹' (B n)) (transB U v))) := by
    funext n
    rfl
  have e2 : transProj U T S c (⋃ n, B n) v
      = transA U
        (S.projection ((shiftEquiv c) ⁻¹' (⋃ n, B n)) (transB U v)) := rfl
  rw [e1, e2]
  exact hsumA

lemma transMeas_finite (v : StateSpace d) :
    IsFiniteMeasure (transMeas U T S c v) := by
  haveI := S.finite_vectorMeasure (transB U v)
  unfold transMeas
  exact Measure.isFiniteMeasure_map _ _

lemma transMeas_apply (v : StateSpace d) (B : Set ℝ) (hB : MeasurableSet B) :
    transMeas U T S c v B = ENNReal.ofReal (‖transProj U T S c B v‖ ^ 2) := by
  unfold transMeas
  rw [Measure.map_apply (shiftEquiv c).measurable hB,
    S.vectorMeasure_apply _ _ ((shiftEquiv c).measurable hB),
    transProj_apply, norm_transA]

/-- Powers are integrable against the original vector measures. -/
lemma integrable_pow_vecMeas {d : ℕ} (T : Blueprint.Operator d)
    (S : SpectralResolution T) (w : StateSpace d) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) (S.vectorMeasure w) := by
  haveI := S.finite_vectorMeasure w
  refine Integrable.of_bound ((continuous_pow k).aestronglyMeasurable)
    ((‖T‖ + 1) ^ k) ?_
  have hsupp : ∀ᵐ x ∂(S.vectorMeasure w), x ∈ Set.Icc (-‖T‖) ‖T‖ :=
    mem_ae_iff.mpr (S.vectorMeasure_supported w)
  filter_upwards [hsupp] with x hx
  simp only [Set.mem_Icc] at hx
  have habs : |x| ≤ ‖T‖ := abs_le.mpr hx
  rw [norm_pow, Real.norm_eq_abs]
  calc |x| ^ k ≤ ‖T‖ ^ k := by
        apply pow_le_pow_left₀ (abs_nonneg x) habs
    _ ≤ (‖T‖ + 1) ^ k := by
        apply pow_le_pow_left₀ (norm_nonneg T) (by linarith)

lemma transMeas_moments (v : StateSpace d) (n : ℕ) :
    ∫ t, t ^ n ∂(transMeas U T S c v)
      = (inner ℂ v ((((Blueprint.conjugate U (T + (c : ℂ) • 1)) ^ n)) v)).re := by
  have hT' : Blueprint.conjugate U (T + (c : ℂ) • 1)
      = transA U * (T + (c : ℂ) • 1) * transB U := rfl
  rw [hT']
  have hAe : AEMeasurable (⇑(shiftEquiv c)) (S.vectorMeasure (transB U v)) :=
    (shiftEquiv c).measurable.aemeasurable
  have hpowN : AEStronglyMeasurable (fun t : ℝ => t ^ n)
      ((S.vectorMeasure (transB U v)).map (shiftEquiv c)) :=
    (continuous_pow n).aestronglyMeasurable
  have hmap : ∫ t, t ^ n ∂(transMeas U T S c v)
      = ∫ x, ((shiftEquiv c) x) ^ n ∂(S.vectorMeasure (transB U v)) := by
    unfold transMeas
    exact integral_map hAe hpowN
  rw [hmap]
  have hexp : ∀ x : ℝ, ((shiftEquiv c) x) ^ n
      = ∑ m ∈ Finset.range (n + 1), x ^ m * c ^ (n - m) * (n.choose m : ℝ) := by
    intro x
    have e1 : (shiftEquiv c) x = c + x := rfl
    rw [e1, add_comm c x]
    exact add_pow x c n
  have hfun : (fun x : ℝ => ((shiftEquiv c) x) ^ n)
      = (fun x => ∑ m ∈ Finset.range (n + 1),
        x ^ m * c ^ (n - m) * (n.choose m : ℝ)) :=
    funext hexp
  have hint : ∀ m ∈ Finset.range (n + 1),
      Integrable (fun x : ℝ => x ^ m * c ^ (n - m) * (n.choose m : ℝ))
        (S.vectorMeasure (transB U v)) := by
    intro m _
    exact ((integrable_pow_vecMeas T S (transB U v) m).mul_const _).mul_const _
  rw [hfun, integral_finsetSum _ hint]
  have htermI : ∀ m ∈ Finset.range (n + 1),
      (∫ x, x ^ m * c ^ (n - m) * (n.choose m : ℝ)
        ∂(S.vectorMeasure (transB U v)))
        = (inner ℂ (transB U v) (((T ^ m)) (transB U v))).re
          * c ^ (n - m) * (n.choose m : ℝ) := by
    intro m _
    rw [integral_mul_const, integral_mul_const, S.vectorMeasure_moments]
  rw [Finset.sum_congr rfl (fun m hm => htermI m hm)]
  have hcomm : Commute T (((c : ℂ)) • (1 : Blueprint.Operator d)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (Algebra.commute_algebraMap_left _ _).symm
  have hexpOp : (T + (c : ℂ) • 1) ^ n
      = ∑ m ∈ Finset.range (n + 1),
        T ^ m * (((c : ℂ) • 1) ^ (n - m))
          * (((n.choose m : ℕ)) : Blueprint.Operator d) :=
    hcomm.add_pow n
  have hcpow : ∀ k : ℕ, ((((c : ℂ)) • (1 : Blueprint.Operator d)) ^ k)
      = ((((c ^ k : ℝ)) : ℂ)) • (1 : Blueprint.Operator d) := by
    intro k
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
      ← map_pow]
    congr 1
    push_cast
    ring
  have hCnat : ∀ k : ℕ, ((k : Blueprint.Operator d))
      = (↑((k : ℝ)) : ℂ) • (1 : Blueprint.Operator d) := by
    intro k
    rw [← map_natCast (algebraMap ℂ (Blueprint.Operator d)) k,
      Algebra.algebraMap_eq_smul_one, Complex.ofReal_natCast]
  have eop : ∀ m : ℕ, T ^ m * (((c : ℂ) • 1) ^ (n - m))
        * ((n.choose m : ℕ) : Blueprint.Operator d)
      = (Complex.ofReal ((n.choose m : ℝ) * c ^ (n - m))) • (T ^ m) := by
    intro m
    rw [hcpow, hCnat]
    simp only [mul_smul_comm, mul_one]
    rw [← mul_smul]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  have eapp : ∀ (s : ℂ) (X : Blueprint.Operator d) (z : StateSpace d),
      ((s • X) z) = s • (X z) := fun s X z => rfl
  have eop_app : ∀ m : ℕ, ∀ z : StateSpace d,
      (T ^ m * (((c : ℂ) • 1) ^ (n - m))
        * ((n.choose m : ℕ) : Blueprint.Operator d)) z
      = (Complex.ofReal ((n.choose m : ℝ) * c ^ (n - m))) • ((T ^ m) z) := by
    intro m z
    rw [eop m]
    rfl
  have hterm : ∀ m ∈ Finset.range (n + 1),
      (inner ℂ (transB U v)
        ((T ^ m * (((c : ℂ) • 1) ^ (n - m))
          * ((n.choose m : ℕ) : Blueprint.Operator d)) (transB U v)))
      = (Complex.ofReal ((n.choose m : ℝ) * c ^ (n - m)))
        * inner ℂ (transB U v) ((T ^ m) (transB U v)) := by
    intro m _
    rw [eop_app m (transB U v), inner_smul_right]
  rw [inner_conj_pow U (T + (c : ℂ) • 1) n v, hexpOp, sum_apply, inner_sum,
    Complex.re_sum]
  exact Finset.sum_congr rfl (fun m hm => by
    rw [hterm m hm]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring)

/-- The pushed measure vanishes outside the shifted support interval. -/
lemma transMeas_supported_aux (v : StateSpace d) :
    transMeas U T S c v ((Set.Icc (c - ‖T‖) (c + ‖T‖))ᶜ) = 0 := by
  have hsub : (shiftEquiv c) ⁻¹' ((Set.Icc (c - ‖T‖) (c + ‖T‖))ᶜ)
      ⊆ (Set.Icc (-‖T‖) ‖T‖)ᶜ := by
    intro t ht
    simp only [Set.mem_preimage, Set.mem_compl_iff] at ht
    simp only [Set.mem_compl_iff]
    intro hIcc
    apply ht
    have e1 : (shiftEquiv c) t = c + t := rfl
    rw [e1]
    simp only [Set.mem_Icc] at hIcc ⊢
    constructor <;> linarith [hIcc.1, hIcc.2]
  have h0 : S.vectorMeasure (transB U v) ((Set.Icc (-‖T‖) ‖T‖)ᶜ) = 0 :=
    S.vectorMeasure_supported _
  have hmap : transMeas U T S c v ((Set.Icc (c - ‖T‖) (c + ‖T‖))ᶜ)
      = S.vectorMeasure (transB U v)
        ((shiftEquiv c) ⁻¹' ((Set.Icc (c - ‖T‖) (c + ‖T‖))ᶜ)) := by
    unfold transMeas
    rw [Measure.map_apply (shiftEquiv c).measurable measurableSet_Icc.compl]
  rw [hmap]
  exact le_antisymm ((measure_mono hsub).trans_eq h0) (by positivity)

/-- Powers are integrable against the transported measures. -/
lemma integrable_pow_transMeas (v : StateSpace d) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) (transMeas U T S c v) := by
  haveI := transMeas_finite U T S c v
  refine Integrable.of_bound ((continuous_pow k).aestronglyMeasurable)
    ((|c| + ‖T‖ + 1) ^ k) ?_
  have hsupp : ∀ᵐ x ∂(transMeas U T S c v), x ∈ Set.Icc (c - ‖T‖) (c + ‖T‖) :=
    mem_ae_iff.mpr (transMeas_supported_aux U T S c v)
  filter_upwards [hsupp] with x hx
  simp only [Set.mem_Icc] at hx
  have habs : |x| ≤ |c| + ‖T‖ := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, neg_abs_le c, le_abs_self c]
  rw [norm_pow, Real.norm_eq_abs]
  calc |x| ^ k ≤ (|c| + ‖T‖) ^ k :=
        pow_le_pow_left₀ (abs_nonneg x) habs k
    _ ≤ (|c| + ‖T‖ + 1) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) k

/-- Operator powers grow at most exponentially in the norm, pointwise. -/
lemma opNorm_pow_apply_le (X : Blueprint.Operator d) (k : ℕ) (v : StateSpace d) :
    ‖(X ^ k) v‖ ≤ ‖X‖ ^ k * ‖v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have happ : ((X ^ (k + 1)) v) = X ((X ^ k) v) := by rw [pow_succ']; rfl
    rw [happ]
    calc ‖X ((X ^ k) v)‖ ≤ ‖X‖ * ‖(X ^ k) v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖X‖ * (‖X‖ ^ k * ‖v‖) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖X‖ ^ (k + 1) * ‖v‖ := by rw [pow_succ']; ring

/-- Chebyshev moment bound for the transported measure. -/
lemma moment_bound (v : StateSpace d) (k : ℕ) :
    (∫ t, t ^ k ∂(transMeas U T S c v))
      ≤ ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ k * ‖v‖ ^ 2 := by
  rw [transMeas_moments]
  have hCS : ‖inner ℂ v
        (((Blueprint.conjugate U (T + (c : ℂ) • 1)) ^ k) v)‖
      ≤ ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ k * ‖v‖ ^ 2 := by
    have h1 : ‖inner ℂ v ((((Blueprint.conjugate U (T + (c : ℂ) • 1)) ^ k)) v)‖
        ≤ ‖v‖ * (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ k * ‖v‖) := by
      calc ‖inner ℂ v _‖ ≤ ‖v‖ * ‖(((Blueprint.conjugate U (T + (c : ℂ) • 1)) ^ k) v)‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖v‖ * (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ k * ‖v‖) := by
            apply mul_le_mul_of_nonneg_left
              (opNorm_pow_apply_le _ _ _) (norm_nonneg _)
    calc ‖inner ℂ v _‖
        ≤ ‖v‖ * (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ k * ‖v‖) := h1
      _ = ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ k * ‖v‖ ^ 2 := by ring
  exact (Complex.re_le_norm _).trans hCS

/-- Markov tail estimate for the transported measure. -/
lemma transMeas_tail (v : StateSpace d) (R : ℝ)
    (hR : ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ < R) (n : ℕ) :
    transMeas U T S c v {t | R ≤ |t|}
      ≤ ENNReal.ofReal
        ((‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n) * ‖v‖ ^ 2) := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hsub : {t : ℝ | R ≤ |t|}
      ⊆ {t | ENNReal.ofReal (R ^ (2 * n)) ≤ ENNReal.ofReal (t ^ (2 * n))} := by
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    apply ENNReal.ofReal_le_ofReal
    have h1 : R ^ (2 * n) ≤ |t| ^ (2 * n) :=
      pow_le_pow_left₀ hR0.le ht (2 * n)
    have h2 : |t| ^ (2 * n) = t ^ (2 * n) := by
      calc |t| ^ (2 * n) = (|t| ^ 2) ^ n := by rw [pow_mul]
        _ = (t ^ 2) ^ n := by rw [sq_abs]
        _ = t ^ (2 * n) := by rw [pow_mul]
    rw [← h2]
    exact h1
  have hmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal (t ^ (2 * n)))
      (transMeas U T S c v) :=
    (ENNReal.measurable_ofReal.comp (continuous_pow _).measurable).aemeasurable
  have hε0 : ENNReal.ofReal (R ^ (2 * n)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hR0 _)
  have hεT : ENNReal.ofReal (R ^ (2 * n)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmark := meas_ge_le_lintegral_div hmeas hε0 hεT
  have hInt : Integrable (fun t : ℝ => t ^ (2 * n)) (transMeas U T S c v) :=
    integrable_pow_transMeas U T S c v (2 * n)
  have hnn : ∀ᵐ t ∂(transMeas U T S c v), 0 ≤ t ^ (2 * n) :=
    Filter.Eventually.of_forall (fun t => by
      have e : (2 * n) = n * 2 := by ring
      rw [e, pow_mul]
      exact sq_nonneg _)
  have hconv : (∫⁻ t, ENNReal.ofReal (t ^ (2 * n)) ∂(transMeas U T S c v))
      = ENNReal.ofReal (∫ t, t ^ (2 * n) ∂(transMeas U T S c v)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt hnn]
  have hle : (∫ t, t ^ (2 * n) ∂(transMeas U T S c v))
      ≤ ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ (2 * n) * ‖v‖ ^ 2 :=
    moment_bound U T S c v (2 * n)
  have hRpos : (0 : ℝ) < R ^ (2 * n) := pow_pos hR0 _
  have hdiv : ENNReal.ofReal (∫ t, t ^ (2 * n) ∂(transMeas U T S c v))
        / ENNReal.ofReal (R ^ (2 * n))
      ≤ ENNReal.ofReal
        ((‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n) * ‖v‖ ^ 2) := by
    rw [← ENNReal.ofReal_div_of_pos hRpos]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (∫ t, t ^ (2 * n) ∂(transMeas U T S c v)) * (R ^ (2 * n))⁻¹
        ≤ (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ (2 * n) * ‖v‖ ^ 2)
          * (R ^ (2 * n))⁻¹ :=
      mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hRpos.le)
    have h2 : (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ ^ (2 * n) * ‖v‖ ^ 2)
          * (R ^ (2 * n))⁻¹
        = (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n) * ‖v‖ ^ 2 := by
      rw [div_pow]
      ring
    rw [div_eq_mul_inv]
    exact h1.trans_eq h2
  calc transMeas U T S c v {t | R ≤ |t|}
      ≤ transMeas U T S c v
        {t | ENNReal.ofReal (R ^ (2 * n)) ≤ ENNReal.ofReal (t ^ (2 * n))} :=
        measure_mono hsub
    _ ≤ (∫⁻ t, ENNReal.ofReal (t ^ (2 * n)) ∂(transMeas U T S c v))
        / ENNReal.ofReal (R ^ (2 * n)) := hmark
    _ = ENNReal.ofReal (∫ t, t ^ (2 * n) ∂(transMeas U T S c v))
        / ENNReal.ofReal (R ^ (2 * n)) := by rw [hconv]
    _ ≤ ENNReal.ofReal
        ((‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n) * ‖v‖ ^ 2) :=
        hdiv

/-- Each tail set is null by letting `n → ∞`. -/
lemma transMeas_tail_null (v : StateSpace d) (R : ℝ)
    (hR : ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ < R) :
    transMeas U T S c v {t | R ≤ |t|} = 0 := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hq0 : 0 ≤ ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R :=
    div_nonneg (norm_nonneg _) hR0.le
  have hq1 : ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R < 1 :=
    (div_lt_one hR0).mpr hR
  have hlim0 : Filter.Tendsto
      (fun n => (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n))
      Filter.atTop (nhds 0) := by
    have h2 : ∀ n : ℕ, (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n)
        = ((‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ 2) ^ n := by
      intro n
      rw [← pow_mul]
    simp_rw [h2]
    apply tendsto_pow_atTop_nhds_zero_of_lt_one _ _
    · exact sq_nonneg _
    · exact pow_lt_one₀ hq0 hq1 two_ne_zero
  have hlim : Filter.Tendsto
      (fun n => ENNReal.ofReal
        ((‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n) * ‖v‖ ^ 2))
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto
        (fun n => (‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n) * ‖v‖ ^ 2)
        Filter.atTop (nhds (0 * ‖v‖ ^ 2)) :=
      hlim0.mul tendsto_const_nhds
    rw [zero_mul] at hreal
    have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    rw [ENNReal.ofReal_zero] at hcomp
    exact hcomp
  have hle : ∀ n : ℕ, transMeas U T S c v {t | R ≤ |t|}
      ≤ ENNReal.ofReal
        ((‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ / R) ^ (2 * n) * ‖v‖ ^ 2) :=
    fun n => transMeas_tail U T S c v R hR n
  have h0 : transMeas U T S c v {t | R ≤ |t|} ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall hle)
  exact le_antisymm h0 (by positivity)

/-- Support of the transported measure via the Chebyshev squeeze. -/
lemma transMeas_supported (v : StateSpace d) :
    transMeas U T S c v
      ((Set.Icc (-‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖)
        ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖)ᶜ) = 0 := by
  set M := ‖Blueprint.conjugate U (T + (c : ℂ) • 1)‖ with hM
  have hcover : (Set.Icc (-M) M)ᶜ
      ⊆ ⋃ j : ℕ, {t : ℝ | M + 1 / ((j : ℝ) + 1) ≤ |t|} := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_iUnion,
      Set.mem_ofPred_eq] at ht ⊢
    have habs : M < |t| := by
      by_contra h
      exact ht (abs_le.mp (not_lt.mp h))
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (|t| - M))
    have hnpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
    refine ⟨n, ?_⟩
    have h1 : (1 : ℝ) / (|t| - M) ≤ ((n : ℝ) + 1) :=
      le_trans hn.le (by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith)
    have h2 : (1 : ℝ) / (((n : ℝ) + 1)) ≤ |t| - M := by
      have hpos : (0 : ℝ) < 1 / (|t| - M) := by
        apply one_div_pos.mpr
        linarith [habs]
      have hle2 := one_div_le_one_div_of_le hpos h1
      rwa [one_div_one_div] at hle2
    linarith [h2]
  have hnull : ∀ j : ℕ, transMeas U T S c v
      {t : ℝ | M + 1 / ((j : ℝ) + 1) ≤ |t|} = 0 := by
    intro j
    apply transMeas_tail_null
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hle : transMeas U T S c v ((Set.Icc (-M) M)ᶜ)
      ≤ transMeas U T S c v
        (⋃ j : ℕ, {t : ℝ | M + 1 / ((j : ℝ) + 1) ≤ |t|}) :=
    measure_mono hcover
  rw [measure_iUnion_null hnull] at hle
  exact nonpos_iff_eq_zero.mp hle

/-- The transported spectral resolution. -/
def transportResolution : SpectralResolution
    (Blueprint.conjugate U (T + (c : ℂ) • 1)) where
  projection := transProj U T S c
  projection_empty := transProj_empty U T S c
  projection_univ := transProj_univ U T S c
  projection_selfAdjoint := fun B hB => transProj_selfAdjoint U T S c B hB
  projection_inter := fun B C hB hC => transProj_inter U T S c B C hB hC
  projection_iUnion := fun B hB hpair v => transProj_iUnion U T S c B hB hpair v
  vectorMeasure := transMeas U T S c
  finite_vectorMeasure := fun v => transMeas_finite U T S c v
  vectorMeasure_apply := fun v B hB => transMeas_apply U T S c v B hB
  vectorMeasure_supported := fun v => transMeas_supported U T S c v
  vectorMeasure_moments := fun v n => transMeas_moments U T S c v n

lemma preimage_translateWindow (I : Set ℝ) :
    (shiftEquiv c) ⁻¹' (Blueprint.translateWindow c I) = I := by
  have hJ : Blueprint.translateWindow c I = (shiftEquiv c) '' I := rfl
  rw [hJ]
  exact (shiftEquiv c).injective.preimage_image I

/-- Transport of the absolutely continuous subspace. -/
lemma transACRange (I : Set ℝ)
    (hac : Set.range (S.projection I) ⊆ (S.acSubspace : Set (StateSpace d))) :
    Set.range ((transportResolution U T S c).projection
        (Blueprint.translateWindow c I))
      ⊆ ((transportResolution U T S c).acSubspace : Set (StateSpace d)) := by
  have hJI := preimage_translateWindow c I
  rintro y ⟨v, rfl⟩
  have hy : (transportResolution U T S c).projection
        (Blueprint.translateWindow c I) v
      = transA U (S.projection I (transB U v)) := by
    show transProj U T S c (Blueprint.translateWindow c I) v = _
    rw [transProj_apply, hJI]
  rw [hy]
  have hx : S.projection I (transB U v) ∈ S.acSubspace :=
    hac ⟨transB U v, rfl⟩
  have hxM : S.vectorMeasure (S.projection I (transB U v)) ≪ volume :=
    (SpectralResolution.mem_acSubspace _ _).mp hx
  have hmapEq : transMeas U T S c
        (transA U (S.projection I (transB U v)))
      = (S.vectorMeasure (S.projection I (transB U v))).map (shiftEquiv c) := by
    have hBAx : transB U (transA U (S.projection I (transB U v)))
        = S.projection I (transB U v) :=
      transB_transA_apply U _
    unfold transMeas
    rw [hBAx]
  rw [SetLike.mem_coe, SpectralResolution.mem_acSubspace]
  show transMeas U T S c (transA U (S.projection I (transB U v))) ≪ volume
  rw [hmapEq]
  have hac2 := hxM.map (shiftEquiv c).measurable
  rw [shiftEquiv_map_volume] at hac2
  exact hac2

/-- Transport of the nonzero projection. -/
lemma transProj_nonzero (I : Set ℝ) (hn : S.projection I ≠ 0) :
    (transportResolution U T S c).projection
      (Blueprint.translateWindow c I) ≠ 0 := by
  have hJI := preimage_translateWindow c I
  intro h0
  apply hn
  apply ContinuousLinearMap.ext
  intro w
  have h1 : S.projection I w
      = transB U (transProj U T S c (Blueprint.translateWindow c I)
        (transA U w)) := by
    rw [transProj_apply, hJI, transB_transA_apply, transB_transA_apply]
  have h2 : (transportResolution U T S c).projection
        (Blueprint.translateWindow c I)
      = transProj U T S c (Blueprint.translateWindow c I) := rfl
  rw [h2] at h0
  rw [h1, h0]
  simp

/-- Transport of the real spectrum. -/
lemma spectrum_translate (I : Set ℝ) (hσ : I ⊆ Blueprint.realSpectrum T) :
    Blueprint.translateWindow c I
      ⊆ Blueprint.realSpectrum
        (Blueprint.conjugate U (T + (c : ℂ) • 1)) := by
  intro E hE
  obtain ⟨F, hF, rfl⟩ := hE
  show (c + F) ∈ Blueprint.realSpectrum _
  unfold Blueprint.realSpectrum
  simp only [Set.mem_ofPred_eq]
  have hspec : spectrum ℂ (Blueprint.conjugate U (T + (c : ℂ) • 1))
      = spectrum ℂ (transA U * (T + (c : ℂ) • 1) * transB U) := rfl
  rw [hspec, spectrum_trans_conj]
  have hFmem : ((F : ℝ) : ℂ) ∈ spectrum ℂ T := hσ hF
  rw [spectrum.mem_iff] at hFmem ⊢
  have heq : algebraMap ℂ (Blueprint.Operator d) (((c + F : ℝ)) : ℂ)
        - (T + (c : ℂ) • 1)
      = algebraMap ℂ (Blueprint.Operator d) ((F : ℝ) : ℂ) - T := by
    simp only [Algebra.algebraMap_eq_smul_one, Complex.ofReal_add, add_smul]
    abel
  rw [heq]
  exact hFmem

end Conj

/-- The spectral transport core: shift + unitary conjugation of an AC region. -/
theorem spectralTransportCore : Blueprint.SpectralTransportInput := by
  intro d T hT c U I hAC
  obtain ⟨hσ, S, hac, hn⟩ := hAC
  refine ⟨spectrum_translate U T c I hσ,
    transportResolution U T S c, ?_, ?_⟩
  · exact transACRange U T S c I hac
  · exact transProj_nonzero U T S c I hn

end AndersonAC.LunaTransport

namespace AndersonAC.Blueprint.Packages

theorem spectralTransport : AndersonAC.Blueprint.SpectralTransportInput :=
  AndersonAC.LunaTransport.spectralTransportCore


end AndersonAC.Blueprint.Packages
