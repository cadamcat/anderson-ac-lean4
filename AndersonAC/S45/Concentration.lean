import AndersonAC.S45.ConcentrationHelpers
import AndersonAC.S45.HelperStatements

/-! Lemma 5.6 (`05-local-sweeps.tex:686`), the `maximal` field of
`ConcentrationInput`: matrix Freedman with a scalar predictable envelope.

The proof follows the paper. For `0 ≤ u`, `uJ ≤ 1`,
`T_n = Re Tr exp(u S_n) · exp(-u² W_n)` (with `S_n = ∑_{k<n} Y_k`,
`W_n = ∑_{k<n} v_k`) is a supermartingale: Golden–Thompson, the quadratic
bound `e^{uY} ≤ 1 + uY + u²Y²` paired against `exp(u S_n) ≥ 0`, the
martingale-difference property and `Tr(B E[Y²|ℱ]) ≤ v Tr B`. Adding the same
process for `-Y` and applying Ville's inequality bounds the two-sided crossing.

Inputs taken as hypotheses here: Golden–Thompson, the deterministic
trace facts `TraceHelpers` and Ville's inequality `VilleStatement` (helper
statements). Everything else is proved. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace AndersonAC.OpusS45

open AndersonAC.Blueprint

/-- Golden–Thompson in the exact form of `ConcentrationInput.goldenThompson`. -/
def GTStatement : Prop :=
  ∀ (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ),
    A.IsHermitian → B.IsHermitian →
      (Matrix.trace (NormedSpace.exp (A + B))).re ≤
        (Matrix.trace (NormedSpace.exp A * NormedSpace.exp B)).re

/-- The `maximal` field of `ConcentrationInput`, verbatim. -/
def MaximalStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω),
      IsProbabilityMeasure μ →
      ∀ (N : ℕ) (ℱ : Filtration ℕ mΩ)
        (Y : ℕ → Ω → Matrix (Fin N) (Fin N) ℂ) (v : ℕ → Ω → ℝ) (J V : ℝ),
        0 < J → 0 < V →
        (∀ k, @StronglyMeasurable Ω (Matrix (Fin N) (Fin N) ℂ) _ (ℱ (k + 1)) (Y k)) →
        (∀ k i j, Integrable (fun ω => Y k ω i j) μ) →
        (∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian ∧ opNorm (Y k ω) ≤ J) →
        (∀ k, matrixCondExp μ (ℱ k) (Y k) =ᵐ[μ] 0) →
        (∀ k, @Measurable Ω ℝ (ℱ k) _ (v k)) →
        (∀ k, ∀ᵐ ω ∂μ, 0 ≤ v k ω ∧
          ((v k ω : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
            matrixCondExp μ (ℱ k) (fun ω => Y k ω * Y k ω) ω).PosSemidef) →
        (∀ᵐ ω ∂μ, ∀ n, (∑ k ∈ Finset.range n, v k ω) ≤ V) →
        ∀ a : ℝ, 0 < a →
          μ {ω | ∃ n : ℕ, a < opNorm (∑ k ∈ Finset.range n, Y k ω)} ≤
            ENNReal.ofReal (2 * (N : ℝ) * Real.exp (-c * min (a ^ 2 / V) (a / J)))

example : MaximalStatement = (∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω),
      IsProbabilityMeasure μ →
      ∀ (N : ℕ) (ℱ : Filtration ℕ mΩ)
        (Y : ℕ → Ω → Matrix (Fin N) (Fin N) ℂ) (v : ℕ → Ω → ℝ) (J V : ℝ),
        0 < J → 0 < V →
        (∀ k, @StronglyMeasurable Ω (Matrix (Fin N) (Fin N) ℂ) _ (ℱ (k + 1)) (Y k)) →
        (∀ k i j, Integrable (fun ω => Y k ω i j) μ) →
        (∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian ∧ opNorm (Y k ω) ≤ J) →
        (∀ k, matrixCondExp μ (ℱ k) (Y k) =ᵐ[μ] 0) →
        (∀ k, @Measurable Ω ℝ (ℱ k) _ (v k)) →
        (∀ k, ∀ᵐ ω ∂μ, 0 ≤ v k ω ∧
          ((v k ω : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
            matrixCondExp μ (ℱ k) (fun ω => Y k ω * Y k ω) ω).PosSemidef) →
        (∀ᵐ ω ∂μ, ∀ n, (∑ k ∈ Finset.range n, v k ω) ≤ V) →
        ∀ a : ℝ, 0 < a →
          μ {ω | ∃ n : ℕ, a < opNorm (∑ k ∈ Finset.range n, Y k ω)} ≤
            ENNReal.ofReal (2 * (N : ℝ) * Real.exp (-c * min (a ^ 2 / V) (a / J)))) := rfl

abbrev CM (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-! ### Deterministic matrix facts -/

theorem exp_continuous' (N : ℕ) : Continuous (fun M : CM N => NormedSpace.exp M) :=
  continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt

theorem continuous_re_trace_mul (N : ℕ) :
    Continuous (fun p : CM N × CM N => (Matrix.trace (p.1 * p.2)).re) := by
  fun_prop

theorem opNorm_def {N : ℕ} (X : CM N) : opNorm X = ‖X‖ := rfl

theorem opNorm_add_le {N : ℕ} (X Z : CM N) : opNorm (X + Z) ≤ opNorm X + opNorm Z :=
  norm_add_le X Z

theorem opNorm_neg {N : ℕ} (X : CM N) : opNorm (-X) = opNorm X := norm_neg X

theorem opNorm_smul {N : ℕ} (u : ℝ) (X : CM N) : opNorm (u • X) = |u| * opNorm X := by
  rw [opNorm_def, opNorm_def, ← Real.norm_eq_abs]
  rw [show (u • X : CM N) = (u : ℂ) • X from (Complex.coe_smul u X).symm, norm_smul,
    Complex.norm_real]

theorem opNorm_zero_dim (X : CM 0) : opNorm X = 0 := by
  rw [opNorm_def, Subsingleton.elim X 0, norm_zero]

theorem re_trace_mul_apply {N : ℕ} (H X : CM N) :
    (Matrix.trace (H * X)).re = ∑ i, ∑ j, (H i j * X j i).re := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.re_sum]

theorem abs_re_trace_le (hB : OpNormBounds) {N : ℕ} (X : CM N) :
    |(Matrix.trace X).re| ≤ N * opNorm X := by
  unfold Matrix.trace
  rw [Complex.re_sum]
  calc |∑ i, (X i i).re| ≤ ∑ i, |(X i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, opNorm X := Finset.sum_le_sum fun i _ =>
        (Complex.abs_re_le_norm _).trans (hB.2 N X i i)
    _ = N * opNorm X := by simp

theorem re_trace_smul_mul {N : ℕ} (e : ℝ) (B X : CM N) :
    (Matrix.trace ((e • B) * X)).re = e * (Matrix.trace (B * X)).re := by
  rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem isHermitian_real_smul {N : ℕ} (u : ℝ) {S : CM N} (h : S.IsHermitian) :
    (u • S).IsHermitian := Matrix.IsHermitian.smul h rfl

/-! ### Conditional expectation pull-out against bounded measurable weights -/

theorem setIntegral_mul_condExp {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[m] s)
    {h X : Ω → ℂ} (hh : StronglyMeasurable[m] h) (c : ℝ) (hc : ∀ᵐ ω ∂μ, ‖h ω‖ ≤ c)
    (hX : Integrable X μ) :
    ∫ ω in s, h ω * X ω ∂μ = ∫ ω in s, h ω * μ[X | m] ω ∂μ := by
  have hhm : AEStronglyMeasurable h μ := (hh.mono hm).aestronglyMeasurable
  have hint : Integrable (fun ω => h ω * X ω) μ := hX.bdd_mul hhm hc
  rw [← setIntegral_condExp hm hint hs]
  refine setIntegral_congr_ae (hm s hs) ?_
  filter_upwards [condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.mul ℝ ℂ) hm hh
    hX c hc] with ω hω _
  simpa using hω

theorem setIntegral_re_trace_condExp {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[m] s) {N : ℕ}
    {H X : Ω → CM N} (hH : ∀ i j, StronglyMeasurable[m] (fun ω => H ω i j)) (c : ℝ)
    (hc : ∀ᵐ ω ∂μ, ∀ i j, ‖H ω i j‖ ≤ c)
    (hX : ∀ i j, Integrable (fun ω => X ω i j) μ) :
    ∫ ω in s, (Matrix.trace (H ω * X ω)).re ∂μ =
      ∫ ω in s, (Matrix.trace (H ω * @matrixCondExp Ω mΩ μ m N X ω)).re ∂μ := by
  have hHm : ∀ i j, AEStronglyMeasurable (fun ω => H ω i j) μ :=
    fun i j => ((hH i j).mono hm).aestronglyMeasurable
  have hb : ∀ i j, ∀ᵐ ω ∂μ, ‖H ω i j‖ ≤ c := fun i j => hc.mono fun ω h => h i j
  have hi1 : ∀ i j, Integrable (fun ω => H ω i j * X ω j i) μ :=
    fun i j => (hX j i).bdd_mul (hHm i j) (hb i j)
  have hi2 : ∀ i j, Integrable (fun ω => H ω i j * μ[fun ω => X ω j i | m] ω) μ :=
    fun i j => integrable_condExp.bdd_mul (hHm i j) (hb i j)
  simp only [re_trace_mul_apply]
  rw [integral_finsetSum _ fun i _ => ?_, integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => ?_, integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have e1 := integral_re (μ := μ.restrict s) (hi1 i j).restrict
      have e2 := integral_re (μ := μ.restrict s) (hi2 i j).restrict
      simp only [RCLike.re_to_complex] at e1 e2
      rw [e1, setIntegral_mul_condExp hm hs (hH i j) c (hb i j) (hX j i), ← e2]
      rfl
    · exact ((hi2 i j).restrict).re
    · exact ((hi1 i j).restrict).re
  · exact integrable_finsetSum _ fun j _ => ((hi2 i j).restrict).re
  · exact integrable_finsetSum _ fun j _ => ((hi1 i j).restrict).re

theorem integrable_re_trace_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {N : ℕ} {H X : Ω → CM N}
    (hH : ∀ i j, AEStronglyMeasurable (fun ω => H ω i j) μ) (c : ℝ)
    (hc : ∀ᵐ ω ∂μ, ∀ i j, ‖H ω i j‖ ≤ c)
    (hX : ∀ i j, Integrable (fun ω => X ω i j) μ) :
    Integrable (fun ω => (Matrix.trace (H ω * X ω)).re) μ := by
  simp only [re_trace_mul_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hX j i).bdd_mul (hH i j) (hc.mono fun ω h => h i j)).re

/-! ### The trace-exponential process -/

section Process

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def psum {N : ℕ} (Y : ℕ → Ω → CM N) (n : ℕ) (ω : Ω) : CM N := ∑ k ∈ Finset.range n, Y k ω

def vsum (v : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range n, v k ω

def Tproc {N : ℕ} (u : ℝ) (Y : ℕ → Ω → CM N) (v : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Matrix.trace (NormedSpace.exp (u • psum Y n ω))).re * Real.exp (-(u ^ 2 * vsum v n ω))

/-- The hypotheses of `ConcentrationInput.maximal`, bundled. -/
structure Hyp (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) {N : ℕ} (Y : ℕ → Ω → CM N)
    (v : ℕ → Ω → ℝ) (J V : ℝ) : Prop where
  meas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)
  int : ∀ k i j, Integrable (fun ω => Y k ω i j) μ
  bdd : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian ∧ opNorm (Y k ω) ≤ J
  mart : ∀ k, matrixCondExp μ (ℱ k) (Y k) =ᵐ[μ] 0
  vmeas : ∀ k, Measurable[ℱ k] (v k)
  var : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ v k ω ∧
    ((v k ω : ℂ) • (1 : CM N) - matrixCondExp μ (ℱ k) (fun ω => Y k ω * Y k ω) ω).PosSemidef
  tot : ∀ᵐ ω ∂μ, ∀ n, vsum v n ω ≤ V

variable {μ : Measure Ω} {ℱ : Filtration ℕ mΩ} {N : ℕ} {Y : ℕ → Ω → CM N}
  {v : ℕ → Ω → ℝ} {J V : ℝ}

omit mΩ in
theorem psum_succ (Y : ℕ → Ω → CM N) (n : ℕ) (ω : Ω) :
    psum Y (n + 1) ω = psum Y n ω + Y n ω := Finset.sum_range_succ _ _

omit mΩ in
theorem vsum_succ (v : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    vsum v (n + 1) ω = vsum v n ω + v n ω := Finset.sum_range_succ _ _

theorem Hyp.sm_lt (h : Hyp μ ℱ Y v J V) {k n : ℕ} (hk : k < n) :
    StronglyMeasurable[ℱ n] (Y k) := (h.meas k).mono (ℱ.mono (by omega))

theorem Hyp.sm (h : Hyp μ ℱ Y v J V) (k : ℕ) : StronglyMeasurable (Y k) :=
  (h.meas k).mono (ℱ.le _)

theorem Hyp.psum_sm (h : Hyp μ ℱ Y v J V) (n : ℕ) : StronglyMeasurable[ℱ n] (psum Y n) := by
  unfold psum
  exact Finset.stronglyMeasurable_fun_sum _ fun k hk => h.sm_lt (Finset.mem_range.1 hk)

theorem Hyp.vsum_sm (h : Hyp μ ℱ Y v J V) {n m : ℕ} (hnm : n ≤ m + 1) :
    StronglyMeasurable[ℱ m] (vsum v n) := by
  unfold vsum
  refine Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_
  have hk' : k < n := Finset.mem_range.1 hk
  exact ((h.vmeas k).stronglyMeasurable).mono (ℱ.mono (by omega))

/-- Pointwise consequences of the a.e. hypotheses. -/
structure Good (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → CM N)
    (v : ℕ → Ω → ℝ) (J V : ℝ) (ω : Ω) : Prop where
  herm : ∀ k, (Y k ω).IsHermitian
  norm : ∀ k, opNorm (Y k ω) ≤ J
  vnn : ∀ k, 0 ≤ v k ω
  var : ∀ k,
    ((v k ω : ℂ) • (1 : CM N) - matrixCondExp μ (ℱ k) (fun ω => Y k ω * Y k ω) ω).PosSemidef
  tot : ∀ n, vsum v n ω ≤ V

theorem Hyp.ae_good (h : Hyp μ ℱ Y v J V) : ∀ᵐ ω ∂μ, Good μ ℱ Y v J V ω := by
  have h1 := ae_all_iff.2 h.bdd
  have h2 := ae_all_iff.2 h.var
  filter_upwards [h1, h2, h.tot] with ω h1 h2 h3
  exact ⟨fun k => (h1 k).1, fun k => (h1 k).2, fun k => (h2 k).1, fun k => (h2 k).2, h3⟩

namespace Good

variable {ω : Ω} (g : Good μ ℱ Y v J V ω)
include g

theorem psum_herm (n : ℕ) : (psum Y n ω).IsHermitian := by
  induction n with
  | zero => simp [psum, Matrix.isHermitian_zero]
  | succ n ih => rw [psum_succ]; exact ih.add (g.herm n)

theorem psum_norm (n : ℕ) : opNorm (psum Y n ω) ≤ n * J := by
  induction n with
  | zero => simp [psum, opNorm_def]
  | succ n ih =>
    rw [psum_succ]
    calc opNorm (psum Y n ω + Y n ω) ≤ opNorm (psum Y n ω) + opNorm (Y n ω) := opNorm_add_le _ _
      _ ≤ n * J + J := add_le_add ih (g.norm n)
      _ = (n + 1 : ℕ) * J := by push_cast; ring

theorem vsum_nonneg (n : ℕ) : 0 ≤ vsum v n ω :=
  Finset.sum_nonneg fun k _ => g.vnn k

theorem v_le (k : ℕ) : v k ω ≤ V := by
  have := g.tot (k + 1)
  rw [vsum_succ] at this
  linarith [g.vsum_nonneg k]

theorem exp_norm (hB : OpNormBounds) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    opNorm (NormedSpace.exp (u • psum Y n ω)) ≤ Real.exp (u * (n * J)) :=
  (hB.1 N _).trans (Real.exp_le_exp.2 (by
    rw [opNorm_smul, abs_of_nonneg hu]; exact mul_le_mul_of_nonneg_left (g.psum_norm n) hu))

theorem exp_neg_le_one {u : ℝ} (n : ℕ) : Real.exp (-(u ^ 2 * vsum v n ω)) ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith [g.vsum_nonneg n, sq_nonneg u])

theorem tproc_abs (hB : OpNormBounds) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |Tproc u Y v n ω| ≤ N * Real.exp (u * (n * J)) := by
  unfold Tproc
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := (abs_re_trace_le hB (NormedSpace.exp (u • psum Y n ω))).trans
    (mul_le_mul_of_nonneg_left (g.exp_norm hB hu n) (Nat.cast_nonneg N))
  calc _ ≤ N * Real.exp (u * (n * J)) * 1 :=
        mul_le_mul h1 (g.exp_neg_le_one n) (Real.exp_pos _).le (by positivity)
    _ = _ := mul_one _

end Good

theorem Hyp.tproc_sm (h : Hyp μ ℱ Y v J V) (u : ℝ) (n : ℕ) :
    StronglyMeasurable[ℱ n] (Tproc u Y v n) := by
  have hc := exp_continuous' N
  have h1 : StronglyMeasurable[ℱ n]
      (fun ω => (Matrix.trace (NormedSpace.exp (u • psum Y n ω))).re) :=
    (Complex.continuous_re.comp ((hc.comp (continuous_const_smul u)).matrix_trace)).comp_stronglyMeasurable
      (h.psum_sm n)
  have h2 : StronglyMeasurable[ℱ n] (fun ω => Real.exp (-(u ^ 2 * vsum v n ω))) :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-(u ^ 2 * x))).comp_stronglyMeasurable
      (h.vsum_sm (by omega))
  exact h1.mul h2

theorem Hyp.tproc_int [IsFiniteMeasure μ] (hB : OpNormBounds) (h : Hyp μ ℱ Y v J V) {u : ℝ}
    (hu : 0 ≤ u) (n : ℕ) : Integrable (Tproc u Y v n) μ :=
  Integrable.of_bound ((h.tproc_sm u n).mono (ℱ.le n)).aestronglyMeasurable _
    (h.ae_good.mono fun ω g => by rw [Real.norm_eq_abs]; exact g.tproc_abs hB hu n)

theorem Hyp.step [IsFiniteMeasure μ] (hGT : GTStatement) (hT : TraceHelpers)
    (h : Hyp μ ℱ Y v J V) {u : ℝ} (hu : 0 ≤ u) (huJ : u * J ≤ 1) (n : ℕ) (s : Set Ω)
    (hs : MeasurableSet[ℱ n] s) :
    ∫ ω in s, Tproc u Y v (n + 1) ω ∂μ ≤ ∫ ω in s, Tproc u Y v n ω ∂μ := by
  obtain ⟨hExpPSD, hPair, hQuad, -, hB⟩ := hT
  set B : Ω → CM N := fun ω => NormedSpace.exp (u • psum Y n ω) with hBdef
  set e : Ω → ℝ := fun ω => Real.exp (-(u ^ 2 * vsum v (n + 1) ω)) with hedef
  set H : Ω → CM N := fun ω => e ω • B ω with hHdef
  set M : Ω → CM N := matrixCondExp μ (ℱ n) (fun ω => Y n ω * Y n ω) with hMdef
  set K : ℝ := Real.exp (u * (n * J)) with hKdef
  have hgood := h.ae_good
  have hle := ℱ.le n
  -- measurability
  have hBsm : StronglyMeasurable[ℱ n] B :=
    ((exp_continuous' N).comp (continuous_const_smul u)).comp_stronglyMeasurable (h.psum_sm n)
  have hesm : StronglyMeasurable[ℱ n] e :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-(u ^ 2 * x))).comp_stronglyMeasurable
      (h.vsum_sm le_rfl)
  have hHsm : StronglyMeasurable[ℱ n] H := hesm.smul hBsm
  have hHij : ∀ i j, StronglyMeasurable[ℱ n] (fun ω => H ω i j) := fun i j =>
    (Continuous.matrix_elem continuous_id i j).comp_stronglyMeasurable hHsm
  have hHij' : ∀ i j, AEStronglyMeasurable (fun ω => H ω i j) μ := fun i j =>
    ((hHij i j).mono hle).aestronglyMeasurable
  have htrB : StronglyMeasurable[ℱ n] (fun ω => (Matrix.trace (B ω)).re) :=
    (Complex.continuous_re.comp (continuous_id.matrix_trace)).comp_stronglyMeasurable hBsm
  have hvsm : StronglyMeasurable[ℱ n] (v n) := (h.vmeas n).stronglyMeasurable
  -- bounds
  have he01 : ∀ᵐ ω ∂μ, 0 ≤ e ω ∧ e ω ≤ 1 := hgood.mono fun ω g =>
    ⟨(Real.exp_pos _).le, g.exp_neg_le_one (n + 1)⟩
  have hBb : ∀ᵐ ω ∂μ, ∀ i j, ‖B ω i j‖ ≤ K := hgood.mono fun ω g i j =>
    (hB.2 N _ i j).trans (g.exp_norm hB hu n)
  have hHb : ∀ᵐ ω ∂μ, ∀ i j, ‖H ω i j‖ ≤ K := by
    filter_upwards [he01, hBb] with ω he hb i j
    have : H ω i j = (e ω : ℂ) * B ω i j := by
      simp [H, Matrix.smul_apply, Complex.real_smul]
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he.1]
    calc e ω * ‖B ω i j‖ ≤ 1 * K := mul_le_mul he.2 (hb i j) (norm_nonneg _) zero_le_one
      _ = K := one_mul K
  have htrBb : ∀ᵐ ω ∂μ, |(Matrix.trace (B ω)).re| ≤ N * K := hgood.mono fun ω g =>
    (abs_re_trace_le hB _).trans (mul_le_mul_of_nonneg_left (g.exp_norm hB hu n)
      (Nat.cast_nonneg N))
  have hYY : ∀ i j, Integrable (fun ω => (Y n ω * Y n ω) i j) μ := fun i j =>
    Integrable.of_bound
      ((Continuous.matrix_elem (continuous_id.mul continuous_id) i j).comp_stronglyMeasurable
        (h.sm n)).aestronglyMeasurable (J * J)
      (hgood.mono fun ω g => (hB.2 N _ i j).trans (by
        rw [opNorm_def]
        exact (norm_mul_le _ _).trans (mul_le_mul (g.norm n) (g.norm n) (norm_nonneg _)
          ((norm_nonneg _).trans (g.norm n)))))
  have hMi : ∀ i j, Integrable (fun ω => M ω i j) μ := fun i j => integrable_condExp
  -- the functions
  have hf1 : Integrable (fun ω => (Matrix.trace (B ω)).re * e ω) μ :=
    Integrable.of_bound ((htrB.mul hesm).mono hle).aestronglyMeasurable (N * K * 1)
      (by
        filter_upwards [htrBb, he01] with ω h1 h2
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
        exact mul_le_mul h1 h2.2 h2.1 (by positivity))
  have hf2 : Integrable (fun ω => (Matrix.trace (H ω * Y n ω)).re) μ :=
    integrable_re_trace_mul hHij' K hHb (h.int n)
  have hf3 : Integrable (fun ω => (Matrix.trace (H ω * (Y n ω * Y n ω))).re) μ :=
    integrable_re_trace_mul hHij' K hHb hYY
  have hf3' : Integrable (fun ω => (Matrix.trace (H ω * M ω)).re) μ :=
    integrable_re_trace_mul hHij' K hHb hMi
  have hfv : Integrable (fun ω => (Matrix.trace (B ω)).re * e ω * v n ω) μ :=
    Integrable.of_bound (((htrB.mul hesm).mul hvsm).mono hle).aestronglyMeasurable (N * K * 1 * V)
      (by
        filter_upwards [htrBb, he01, hgood] with ω h1 h2 g
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h2.1, abs_of_nonneg (g.vnn n)]
        exact mul_le_mul (mul_le_mul h1 h2.2 h2.1 (by positivity)) (g.v_le n) (g.vnn n)
          (by positivity))
  have hT1 := h.tproc_int hB hu (n + 1)
  have hT0 := h.tproc_int hB hu n
  -- Step A: Golden–Thompson and the quadratic bound
  have hA : ∀ᵐ ω ∂μ, Tproc u Y v (n + 1) ω ≤
      (Matrix.trace (B ω)).re * e ω + u * (Matrix.trace (H ω * Y n ω)).re +
        u ^ 2 * (Matrix.trace (H ω * (Y n ω * Y n ω))).re := by
    filter_upwards [hgood] with ω g
    have hS := g.psum_herm n
    have hYh := g.herm n
    have he0 : 0 ≤ e ω := (Real.exp_pos _).le
    have hGTω := hGT N (u • psum Y n ω) (u • Y n ω) (isHermitian_real_smul u hS)
      (isHermitian_real_smul u hYh)
    have hQ := hQuad N (B ω) (Y n ω) u J (hExpPSD N _ (isHermitian_real_smul u hS)) hYh
      (g.norm n) hu huJ
    have hT : Tproc u Y v (n + 1) ω =
        (Matrix.trace (NormedSpace.exp (u • psum Y n ω + u • Y n ω))).re * e ω := by
      simp only [Tproc, psum_succ, smul_add, e]
    rw [hT, re_trace_smul_mul, re_trace_smul_mul]
    calc _ ≤ (Matrix.trace (B ω * NormedSpace.exp (u • Y n ω))).re * e ω :=
          mul_le_mul_of_nonneg_right hGTω he0
      _ ≤ ((Matrix.trace (B ω)).re + u * (Matrix.trace (B ω * Y n ω)).re +
            u ^ 2 * (Matrix.trace (B ω * (Y n ω * Y n ω))).re) * e ω :=
          mul_le_mul_of_nonneg_right hQ he0
      _ = _ := by ring
  -- Step B: the martingale-difference term vanishes
  have hB2 : ∫ ω in s, (Matrix.trace (H ω * Y n ω)).re ∂μ = 0 := by
    rw [setIntegral_re_trace_condExp hle hs hHij K hHb (h.int n)]
    refine integral_eq_zero_of_ae (ae_restrict_of_ae ?_)
    filter_upwards [h.mart n] with ω hω
    simp only [Pi.zero_apply]
    have : @matrixCondExp Ω mΩ μ (ℱ n) N (Y n) ω = 0 := hω
    rw [this, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  -- Step C: the square term is replaced by its conditional expectation
  have hC : ∫ ω in s, (Matrix.trace (H ω * (Y n ω * Y n ω))).re ∂μ =
      ∫ ω in s, (Matrix.trace (H ω * M ω)).re ∂μ :=
    setIntegral_re_trace_condExp hle hs hHij K hHb hYY
  -- Step D: the scalar envelope
  have hD : ∀ᵐ ω ∂μ, (Matrix.trace (H ω * M ω)).re ≤
      (Matrix.trace (B ω)).re * e ω * v n ω := by
    filter_upwards [hgood] with ω g
    have hPSD := hExpPSD N _ (isHermitian_real_smul u (g.psum_herm n))
    have h0 := hPair N (B ω) _ hPSD (g.var n)
    have hexp : (Matrix.trace (B ω * ((v n ω : ℂ) • (1 : CM N) - M ω))).re =
        v n ω * (Matrix.trace (B ω)).re - (Matrix.trace (B ω * M ω)).re := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
        Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul]
    rw [re_trace_smul_mul]
    have he0 : 0 ≤ e ω := (Real.exp_pos _).le
    have : (Matrix.trace (B ω * M ω)).re ≤ v n ω * (Matrix.trace (B ω)).re := by
      have : (Matrix.trace (B ω * ((v n ω : ℂ) • (1 : CM N) - M ω))).re = _ := hexp
      linarith
    calc e ω * (Matrix.trace (B ω * M ω)).re ≤ e ω * (v n ω * (Matrix.trace (B ω)).re) :=
          mul_le_mul_of_nonneg_left this he0
      _ = _ := by ring
  -- Step E: `1 + x ≤ e^x`
  have hE : ∀ᵐ ω ∂μ, (Matrix.trace (B ω)).re * e ω + u ^ 2 *
      ((Matrix.trace (B ω)).re * e ω * v n ω) ≤ Tproc u Y v n ω := by
    filter_upwards [hgood] with ω g
    have hPSD := hExpPSD N _ (isHermitian_real_smul u (g.psum_herm n))
    have htr : 0 ≤ (Matrix.trace (B ω)).re := by
      have := hPair N 1 (B ω) Matrix.PosSemidef.one hPSD
      simpa using this
    have he0 : 0 ≤ e ω := (Real.exp_pos _).le
    have h1 : e ω * (1 + u ^ 2 * v n ω) ≤ Real.exp (-(u ^ 2 * vsum v n ω)) := by
      have h2 : 1 + u ^ 2 * v n ω ≤ Real.exp (u ^ 2 * v n ω) := by
        linarith [Real.add_one_le_exp (u ^ 2 * v n ω)]
      calc e ω * (1 + u ^ 2 * v n ω) ≤ e ω * Real.exp (u ^ 2 * v n ω) :=
            mul_le_mul_of_nonneg_left h2 he0
        _ = Real.exp (-(u ^ 2 * vsum v n ω)) := by
          simp only [e]
          rw [← Real.exp_add, vsum_succ]
          ring_nf
    calc _ = (Matrix.trace (B ω)).re * (e ω * (1 + u ^ 2 * v n ω)) := by ring
      _ ≤ (Matrix.trace (B ω)).re * Real.exp (-(u ^ 2 * vsum v n ω)) :=
          mul_le_mul_of_nonneg_left h1 htr
      _ = Tproc u Y v n ω := rfl
  -- assemble
  calc ∫ ω in s, Tproc u Y v (n + 1) ω ∂μ
      ≤ ∫ ω in s, ((Matrix.trace (B ω)).re * e ω + u * (Matrix.trace (H ω * Y n ω)).re +
          u ^ 2 * (Matrix.trace (H ω * (Y n ω * Y n ω))).re) ∂μ :=
        setIntegral_mono_ae hT1.integrableOn
          ((hf1.add (hf2.const_mul u)).add (hf3.const_mul (u ^ 2))).integrableOn hA
    _ = ∫ ω in s, (Matrix.trace (B ω)).re * e ω ∂μ +
          u * ∫ ω in s, (Matrix.trace (H ω * Y n ω)).re ∂μ +
          u ^ 2 * ∫ ω in s, (Matrix.trace (H ω * (Y n ω * Y n ω))).re ∂μ := by
        have e1 : ∫ ω in s, ((Matrix.trace (B ω)).re * e ω +
            u * (Matrix.trace (H ω * Y n ω)).re) ∂μ =
            ∫ ω in s, (Matrix.trace (B ω)).re * e ω ∂μ +
            ∫ ω in s, u * (Matrix.trace (H ω * Y n ω)).re ∂μ :=
          integral_add (μ := μ.restrict s) hf1.integrableOn.integrable
            (hf2.const_mul u).integrableOn.integrable
        have e2 : ∫ ω in s, ((Matrix.trace (B ω)).re * e ω +
            u * (Matrix.trace (H ω * Y n ω)).re +
            u ^ 2 * (Matrix.trace (H ω * (Y n ω * Y n ω))).re) ∂μ =
            ∫ ω in s, ((Matrix.trace (B ω)).re * e ω +
              u * (Matrix.trace (H ω * Y n ω)).re) ∂μ +
            ∫ ω in s, u ^ 2 * (Matrix.trace (H ω * (Y n ω * Y n ω))).re ∂μ :=
          integral_add (μ := μ.restrict s)
            (hf1.add (hf2.const_mul u)).integrableOn.integrable
            (hf3.const_mul (u ^ 2)).integrableOn.integrable
        have e3 : ∫ ω in s, u * (Matrix.trace (H ω * Y n ω)).re ∂μ =
            u * ∫ ω in s, (Matrix.trace (H ω * Y n ω)).re ∂μ :=
          integral_const_mul (μ := μ.restrict s) _ _
        have e4 : ∫ ω in s, u ^ 2 * (Matrix.trace (H ω * (Y n ω * Y n ω))).re ∂μ =
            u ^ 2 * ∫ ω in s, (Matrix.trace (H ω * (Y n ω * Y n ω))).re ∂μ :=
          integral_const_mul (μ := μ.restrict s) _ _
        rw [e2, e1, e3, e4]
    _ = ∫ ω in s, (Matrix.trace (B ω)).re * e ω ∂μ +
          u ^ 2 * ∫ ω in s, (Matrix.trace (H ω * M ω)).re ∂μ := by
        rw [hB2, hC]; ring
    _ ≤ ∫ ω in s, (Matrix.trace (B ω)).re * e ω ∂μ +
          u ^ 2 * ∫ ω in s, (Matrix.trace (B ω)).re * e ω * v n ω ∂μ := by
        have hle : ∫ ω in s, (Matrix.trace (H ω * M ω)).re ∂μ ≤
            ∫ ω in s, (Matrix.trace (B ω)).re * e ω * v n ω ∂μ :=
          setIntegral_mono_ae hf3'.integrableOn hfv.integrableOn hD
        have hmul := mul_le_mul_of_nonneg_left hle (sq_nonneg u)
        linarith
    _ = ∫ ω in s, ((Matrix.trace (B ω)).re * e ω + u ^ 2 *
          ((Matrix.trace (B ω)).re * e ω * v n ω)) ∂μ := by
        have e1 : ∫ ω in s, ((Matrix.trace (B ω)).re * e ω +
            u ^ 2 * ((Matrix.trace (B ω)).re * e ω * v n ω)) ∂μ =
            ∫ ω in s, (Matrix.trace (B ω)).re * e ω ∂μ +
            ∫ ω in s, u ^ 2 * ((Matrix.trace (B ω)).re * e ω * v n ω) ∂μ :=
          integral_add (μ := μ.restrict s) hf1.integrableOn.integrable
            (hfv.const_mul (u ^ 2)).integrableOn.integrable
        have e2 : ∫ ω in s, u ^ 2 * ((Matrix.trace (B ω)).re * e ω * v n ω) ∂μ =
            u ^ 2 * ∫ ω in s, (Matrix.trace (B ω)).re * e ω * v n ω ∂μ :=
          integral_const_mul (μ := μ.restrict s) _ _
        have e3 : ∫ ω in s, (Matrix.trace (B ω)).re * e ω ∂μ +
              u ^ 2 * ∫ ω in s, (Matrix.trace (B ω)).re * e ω * v n ω ∂μ =
              ∫ ω in s, (Matrix.trace (B ω)).re * e ω ∂μ +
              ∫ ω in s, u ^ 2 * ((Matrix.trace (B ω)).re * e ω * v n ω) ∂μ := by
          rw [e2]
        exact e3.trans e1.symm
    _ ≤ ∫ ω in s, Tproc u Y v n ω ∂μ :=
        setIntegral_mono_ae (hf1.add (hfv.const_mul (u ^ 2))).integrableOn hT0.integrableOn hE

theorem Hyp.supermartingale [IsFiniteMeasure μ] (hGT : GTStatement) (hT : TraceHelpers)
    (h : Hyp μ ℱ Y v J V) {u : ℝ} (hu : 0 ≤ u) (huJ : u * J ≤ 1) :
    Supermartingale (Tproc u Y v) ℱ μ :=
  supermartingale_of_setIntegral_succ_le (fun n => h.tproc_sm u n)
    (fun n => h.tproc_int hT.2.2.2.2 hu n)
    (fun n s hs => h.step hGT hT hu huJ n s hs)

theorem Hyp.tproc_nonneg_ae (hT : TraceHelpers) (h : Hyp μ ℱ Y v J V) (u : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ Tproc u Y v n ω := by
  obtain ⟨hExpPSD, hPair, -, -, -⟩ := hT
  filter_upwards [h.ae_good] with ω g
  unfold Tproc
  have hpsd := hExpPSD N _ (isHermitian_real_smul u (g.psum_herm n))
  have htr : 0 ≤ (Matrix.trace (NormedSpace.exp (u • psum Y n ω))).re := by
    have h1 := hPair N 1 _ Matrix.PosSemidef.one hpsd
    simpa using h1
  exact mul_nonneg htr (Real.exp_pos _).le

theorem tproc_zero {N : ℕ} (u : ℝ) (Y : ℕ → Ω → CM N) (v : ℕ → Ω → ℝ) (ω : Ω) :
    Tproc u Y v 0 ω = N := by
  simp only [Tproc, psum, vsum, Finset.range_zero, Finset.sum_empty, smul_zero]
  rw [NormedSpace.exp_zero, Matrix.trace_one]
  simp [Fintype.card_fin]

omit mΩ in
theorem psum_neg {N : ℕ} (Y : ℕ → Ω → CM N) (n : ℕ) (ω : Ω) :
    psum (fun k ω => -Y k ω) n ω = -psum Y n ω := by
  simp [psum, Finset.sum_neg_distrib]

/-- Negated increments satisfy the same hypotheses (variance uses `(-Y)² = Y²`). -/
theorem Hyp.neg (h : Hyp μ ℱ Y v J V) : Hyp μ ℱ (fun k ω => -Y k ω) v J V where
  meas k := (h.meas k).neg
  int k i j := ((h.int k i j).neg).congr
    (ae_of_all _ fun ω => by simp [Matrix.neg_apply])
  bdd k := h.bdd k |>.mono fun ω hω =>
    ⟨hω.1.neg, by rw [opNorm_neg]; exact hω.2⟩
  mart k := by
    have hk := h.mart k
    have hentry : ∀ i j, ∀ᵐ ω ∂μ, μ[fun ω => Y k ω i j | ℱ k] ω = 0 := fun i j => by
      filter_upwards [hk] with ω hω
      have eij := congrFun (congrFun hω i) j
      simpa [matrixCondExp] using eij
    have hneg : ∀ i j, ∀ᵐ ω ∂μ, μ[fun ω => (-Y k ω) i j | ℱ k] ω = 0 := fun i j => by
      have e2 : (fun ω => (-Y k ω) i j) = -(fun ω => Y k ω i j) := by
        funext ω; simp [Matrix.neg_apply, Pi.neg_apply]
      rw [e2]
      filter_upwards [condExp_neg (fun ω => Y k ω i j) (ℱ k), hentry i j]
        with ω h1 h2
      calc μ[-(fun ω => Y k ω i j) | ℱ k] ω
          = (-μ[fun ω => Y k ω i j | ℱ k]) ω := h1
        _ = 0 := by simp [h2]
    have hall : ∀ᵐ ω ∂μ, ∀ i j, μ[fun ω => (-Y k ω) i j | ℱ k] ω = 0 :=
      ae_all_iff.2 fun i => ae_all_iff.2 (hneg i)
    filter_upwards [hall] with ω hω
    ext i j
    show μ[fun ω => (-Y k ω) i j | ℱ k] ω = _
    rw [hω i j]
    rfl
  vmeas := h.vmeas
  var k := by
    have hkk := h.var k
    filter_upwards [hkk] with ω hω
    refine ⟨hω.1, ?_⟩
    have e : (fun ω => (-Y k ω) * (-Y k ω)) = (fun ω => Y k ω * Y k ω) := by
      funext ω; exact neg_mul_neg _ _
    rw [e]
    exact hω.2
  tot := h.tot

end Process

open MeasureTheory ProbabilityTheory in
theorem maximal_of_helpers (hGT : GTStatement) (hT : TraceHelpers)
    (hV : AndersonAC.SolS45.VilleStatement) : MaximalStatement := by
  obtain ⟨hExpPSD, hPair, hQuad, hExpTrace, hB⟩ := hT
  refine ⟨1 / 4, by norm_num, fun Ω mΩ μ hprob N ℱ Y v J V hJ hVpos hmeas hint hbdd
    hmart hvmeas hvar htot a ha => ?_⟩
  have hHyp : Hyp (μ := μ) (ℱ := ℱ) Y v J V :=
    { meas := hmeas, int := hint, bdd := hbdd, mart := hmart, vmeas := hvmeas,
      var := hvar, tot := htot }
  by_cases hN : N = 0
  · subst hN
    have hempty : {ω | ∃ n : ℕ, a < opNorm (∑ k ∈ Finset.range n, Y k ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      push_neg
      intro n
      have h0 : (∑ k ∈ Finset.range n, Y k ω) = 0 :=
        Finset.sum_eq_zero fun k _ => Subsingleton.elim _ _
      rw [h0, opNorm_zero_dim]
      exact ha.le
    rw [hempty, measure_empty]
    exact bot_le
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hNreal : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    -- choice of u and its properties
    set u : ℝ := min (a / (2 * V)) (1 / J) with hu_def
    have hJpos := hJ
    have haV : 0 < a / (2 * V) := by positivity
    have h1J : 0 < 1 / J := by positivity
    have hu_pos : 0 < u := lt_min haV h1J
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have huJ : u * J ≤ 1 := by
      have hle : u ≤ 1 / J := min_le_right _ _
      calc u * J ≤ (1 / J) * J := by gcongr
        _ = 1 := by field_simp
    have hu2V : u ≤ a / (2 * V) := min_le_left _ _
    -- key exponent lower bound: u*a - u^2*V ≥ (1/4)*min(a^2/V, a/J)
    have hexp : (1 / 4 : ℝ) * min (a ^ 2 / V) (a / J) ≤ u * a - u ^ 2 * V := by
      by_cases hcase : a / (2 * V) ≤ 1 / J
      · have hu_eq : u = a / (2 * V) := min_eq_left hcase
        rw [hu_eq]
        have hm : min (a ^ 2 / V) (a / J) ≤ a ^ 2 / V := min_le_left _ _
        have hVpos' : (0:ℝ) < V := hVpos
        have e : a / (2 * V) * a - (a / (2 * V)) ^ 2 * V = a ^ 2 / (4 * V) := by
          field_simp; ring
        rw [e]
        calc (1/4) * min (a^2/V) (a/J) ≤ (1/4) * (a^2/V) := by gcongr
          _ = a^2/(4*V) := by ring
      · push_neg at hcase
        have hu_eq : u = 1 / J := min_eq_right hcase.le
        rw [hu_eq]
        have h2V : 2 * V < a * J := by
          have h := (div_lt_div_iff₀ hJ (by positivity : (0:ℝ) < 2 * V)).mp hcase
          simpa using h
        have hVle : V ≤ a * J := by linarith [h2V, hVpos]
        have hmin : min (a ^ 2 / V) (a / J) = a / J := by
          apply min_eq_right
          have hJV : (0:ℝ) < J * V := by positivity
          have e : a ^ 2 / V - a / J = a * (a * J - V) / (J * V) := by
            field_simp
          have hnn : (0:ℝ) ≤ a * (a * J - V) / (J * V) :=
            div_nonneg (mul_nonneg ha.le (by linarith)) hJV.le
          linarith
        rw [hmin]
        have h43 : 4 * V ≤ 3 * (a * J) := by
          have : (0:ℝ) < a * J := by positivity
          linarith
        have hJne : J ≠ 0 := ne_of_gt hJ
        have hVne : V ≠ 0 := ne_of_gt hVpos
        have egoal : (1:ℝ) / 4 * (a / J) ≤ 1 / J * a - (1 / J) ^ 2 * V := by
          have e2 : (1:ℝ) / J * a - (1 / J) ^ 2 * V - 1 / 4 * (a / J)
              = (3 * (a * J) - 4 * V) / (4 * J ^ 2) := by
            field_simp; ring
          have hnn : (0:ℝ) ≤ (3 * (a * J) - 4 * V) / (4 * J ^ 2) := by
            apply div_nonneg (by linarith) (by positivity)
          linarith
        exact egoal
    -- supermartingales for Y and -Y, and their sum
    have hTup : TraceHelpers := ⟨hExpPSD, hPair, hQuad, hExpTrace, hB⟩
    have hS1 : Supermartingale (Tproc u Y v) ℱ μ :=
      hHyp.supermartingale hGT hTup hu_nonneg huJ
    have hHypN := hHyp.neg
    have hS2 : Supermartingale (Tproc u (fun k ω => -Y k ω) v) ℱ μ :=
      hHypN.supermartingale hGT hTup hu_nonneg huJ
    set Z : ℕ → Ω → ℝ := Tproc u Y v + Tproc u (fun k ω => -Y k ω) v with hZdef
    have hS : Supermartingale Z ℱ μ := hS1.add hS2
    have hnn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ Z n ω := fun n => by
      filter_upwards [hHyp.tproc_nonneg_ae hTup u n,
        hHypN.tproc_nonneg_ae hTup u n] with ω h1 h2
      have e : Z n ω = Tproc u Y v n ω + Tproc u (fun k ω => -Y k ω) v n ω :=
        rfl
      rw [e]
      exact add_nonneg h1 h2
    have h0 : ∀ᵐ ω ∂μ, Z 0 ω ≤ 2 * (N : ℝ) := by
      apply ae_of_all
      intro ω
      have e1 := tproc_zero (N := N) u Y v ω
      have e2 := tproc_zero (N := N) u (fun k ω => -Y k ω) v ω
      have e : Z 0 ω = Tproc u Y v 0 ω + Tproc u (fun k ω => -Y k ω) v 0 ω :=
        rfl
      rw [e, e1, e2]
      ring_nf
      exact le_rfl
    -- Ville with D = 2N and b = exp(u*a - u^2*V)
    set D : ℝ := 2 * (N : ℝ) with hDdef
    set b : ℝ := Real.exp (u * a - u ^ 2 * V) with hbdef
    have hDnn : 0 ≤ D := by rw [hDdef]; positivity
    have hbpos : 0 < b := Real.exp_pos _
    have hVille : μ {ω | ∃ n : ℕ, b ≤ Z n ω} ≤ ENNReal.ofReal (D / b) :=
      hV Ω μ ℱ Z D b hS hnn h0 hDnn hbpos
    -- crossing is contained in the Ville event on the Good set
    have haeG := hHyp.ae_good
    have hnull : μ {ω | ¬Good μ ℱ Y v J V ω} = 0 := by
      have hmem : {ω | Good μ ℱ Y v J V ω} ∈ MeasureTheory.ae μ := haeG
      have h0 := MeasureTheory.mem_ae_iff.mp hmem
      simpa [Set.compl_setOf] using h0
    set C : Set Ω := {ω | ∃ n : ℕ, a < opNorm (∑ k ∈ Finset.range n, Y k ω)}
    set E : Set Ω := {ω | ∃ n : ℕ, b ≤ Z n ω}
    have hsub : C ⊆ E ∪ {ω | ¬Good μ ℱ Y v J V ω} := by
      intro ω hω
      by_cases hgω : Good μ ℱ Y v J V ω
      · left
        obtain ⟨n, hn⟩ := hω
        -- identify the sum with psum
        have hSn : (∑ k ∈ Finset.range n, Y k ω) = psum Y n ω := rfl
        rw [hSn] at hn
        set S : CM N := psum Y n ω with hSdef
        set W : ℝ := vsum v n ω with hWdef
        have gS : S.IsHermitian := hgω.psum_herm n
        have hWle : W ≤ V := hgω.tot n
        have hWnn : 0 ≤ W := by
          have := hgω.vsum_nonneg n
          simpa [hWdef, vsum] using this
        -- trace bound
        have hTr := hExpTrace N S u hNpos gS hu_nonneg
        -- T^+ and T^- against the scalar envelope
        have hexpW : Real.exp (u ^ 2 * W) ≤ Real.exp (u ^ 2 * V) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hWle (sq_nonneg u))
        have hexpWpos : (0:ℝ) < Real.exp (u ^ 2 * W) := Real.exp_pos _
        have hexpVpos : (0:ℝ) < Real.exp (u ^ 2 * V) := Real.exp_pos _
        have hT1 : (Matrix.trace (NormedSpace.exp (u • S))).re
            = Tproc u Y v n ω * Real.exp (u ^ 2 * W) := by
          unfold Tproc
          have hexp : Real.exp (-(u ^ 2 * W)) * Real.exp (u ^ 2 * W) = 1 := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          calc (Matrix.trace (NormedSpace.exp (u • S))).re
              = (Matrix.trace (NormedSpace.exp (u • S))).re * 1 := (mul_one _).symm
            _ = (Matrix.trace (NormedSpace.exp (u • S))).re *
                (Real.exp (-(u ^ 2 * W)) * Real.exp (u ^ 2 * W)) := by rw [hexp]
            _ = ((Matrix.trace (NormedSpace.exp (u • S))).re *
                Real.exp (-(u ^ 2 * W))) * Real.exp (u ^ 2 * W) := by ring
        have hpn : psum (fun k ω => -Y k ω) n ω = -S := by
          simp [psum_neg, hSdef]
        have hT2 : (Matrix.trace (NormedSpace.exp (-(u • S)))).re
            = Tproc u (fun k ω => -Y k ω) v n ω * Real.exp (u ^ 2 * W) := by
          have eS : u • psum (fun k ω => -Y k ω) n ω = -(u • S) := by
            rw [hpn, smul_neg]
          unfold Tproc
          rw [eS]
          have hexp : Real.exp (-(u ^ 2 * W)) * Real.exp (u ^ 2 * W) = 1 := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          calc (Matrix.trace (NormedSpace.exp (-(u • S)))).re
              = (Matrix.trace (NormedSpace.exp (-(u • S)))).re * 1 := (mul_one _).symm
            _ = (Matrix.trace (NormedSpace.exp (-(u • S)))).re *
                (Real.exp (-(u ^ 2 * W)) * Real.exp (u ^ 2 * W)) := by rw [hexp]
            _ = ((Matrix.trace (NormedSpace.exp (-(u • S)))).re *
                Real.exp (-(u ^ 2 * W))) * Real.exp (u ^ 2 * W) := by ring
        have hz_nn : 0 ≤ Z n ω := by
          have h1 : 0 ≤ Tproc u Y v n ω := by
            unfold Tproc
            have hpsd := hExpPSD N _ (isHermitian_real_smul u gS)
            have htr : 0 ≤ (Matrix.trace (NormedSpace.exp (u • S))).re := by
              have h1 := hPair N 1 _ Matrix.PosSemidef.one hpsd
              simpa using h1
            exact mul_nonneg htr (Real.exp_pos _).le
          have h2 : 0 ≤ Tproc u (fun k ω => -Y k ω) v n ω := by
            unfold Tproc
            have hSneg : (psum (fun k ω => -Y k ω) n ω).IsHermitian := by
              rw [hpn]; exact gS.neg
            have hpsd := hExpPSD N _ (isHermitian_real_smul u hSneg)
            have htr : 0 ≤ (Matrix.trace
                (NormedSpace.exp (u • psum (fun k ω => -Y k ω) n ω))).re := by
              have h1 := hPair N 1 _ Matrix.PosSemidef.one hpsd
              simpa using h1
            exact mul_nonneg htr (Real.exp_pos _).le
          have e : Z n ω = Tproc u Y v n ω + Tproc u (fun k ω => -Y k ω) v n ω :=
            rfl
          rw [e]
          exact add_nonneg h1 h2
        have hz_eq : Z n ω * Real.exp (u ^ 2 * W)
            = (Matrix.trace (NormedSpace.exp (u • S))).re +
              (Matrix.trace (NormedSpace.exp (-(u • S)))).re := by
          have e : Z n ω = Tproc u Y v n ω + Tproc u (fun k ω => -Y k ω) v n ω :=
            rfl
          rw [e, hT1, hT2]
          ring
        have hlt1 : Real.exp (u * a) < Real.exp (u * opNorm S) :=
          Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hn hu_pos)
        have hlt2 : Real.exp (u * a) < Z n ω * Real.exp (u ^ 2 * V) := by
          calc Real.exp (u * a) < Real.exp (u * opNorm S) := hlt1
            _ ≤ (Matrix.trace (NormedSpace.exp (u • S))).re +
                (Matrix.trace (NormedSpace.exp (-(u • S)))).re := hTr
            _ = Z n ω * Real.exp (u ^ 2 * W) := hz_eq.symm
            _ ≤ Z n ω * Real.exp (u ^ 2 * V) :=
                mul_le_mul_of_nonneg_left hexpW hz_nn
        have hb_le : b ≤ Z n ω := by
          have e : b = Real.exp (u * a) / Real.exp (u ^ 2 * V) := by
            rw [hbdef, Real.exp_sub]
          rw [e]
          exact le_of_lt ((div_lt_iff₀ hexpVpos).mpr hlt2)
        exact ⟨n, hb_le⟩
      · right
        exact hgω
    have hC_le : μ C ≤ μ E := by
      calc μ C ≤ μ (E ∪ {ω | ¬Good μ ℱ Y v J V ω}) := measure_mono hsub
        _ ≤ μ E + μ {ω | ¬Good μ ℱ Y v J V ω} := measure_union_le _ _
        _ = μ E := by rw [hnull, add_zero]
    -- convert D/b to the Freedman form and absorb the exponent
    have eDb : D / b
        = 2 * (N : ℝ) * Real.exp (-(u * a - u ^ 2 * V)) := by
      rw [hDdef, hbdef, div_eq_mul_inv, Real.exp_neg]
    have ele : 2 * (N : ℝ) * Real.exp (-(u * a - u ^ 2 * V))
        ≤ 2 * (N : ℝ) * Real.exp (-((1 / 4 : ℝ) * min (a ^ 2 / V) (a / J))) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith [hexp])) (by positivity)
    calc μ C ≤ μ E := hC_le
      _ ≤ ENNReal.ofReal (D / b) := hVille
      _ = ENNReal.ofReal
          (2 * (N : ℝ) * Real.exp (-(u * a - u ^ 2 * V))) := by rw [eDb]
      _ ≤ ENNReal.ofReal
          (2 * (N : ℝ) * Real.exp (-((1 / 4 : ℝ) * min (a ^ 2 / V) (a / J)))) :=
          ENNReal.ofReal_le_ofReal ele
      _ = _ := by rw [hDdef, neg_mul]

end AndersonAC.OpusS45
