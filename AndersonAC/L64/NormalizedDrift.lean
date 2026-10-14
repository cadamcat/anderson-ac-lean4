import AndersonAC.L64.Normalized

/-!
# Lemma 6.4: pathwise remainders and conditional drift of the normalized heat

For `|c| ≤ K` we split `𝒜'(c) - 𝒜` and `𝒫'(c) - 𝒫` into a part that is affine in `(|c|², c)`
and a remainder bounded by explicit quantities (`ρA`, `ρP`). Taking expectations then only needs
`𝔼 c` and `𝔼 |c|²` (paper l.505–640).
-/

open Matrix Finset ComplexConjugate MeasureTheory

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

/-! ### Measurability and an expectation lemma -/

section Prob

lemma measurable_matrix_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable (fun A : Matrix n n ℂ => A⁻¹) := by
  have : (fun A : Matrix n n ℂ => A⁻¹) = fun A => Ring.inverse A.det • A.adjugate := by
    funext A; exact Matrix.inv_def A
  rw [this]
  simp only [Ring.inverse_eq_inv']
  exact (Measurable.inv (continuous_id.matrix_det.measurable)).smul
    (continuous_id.matrix_adjugate.measurable)

variable {α : Type*} [MeasurableSpace α] {B : Type*} [Fintype B]

lemma Measurable.mulVec' {M : α → Matrix B B ℂ} {y : α → B → ℂ} (hM : Measurable M)
    (hy : Measurable y) : Measurable (fun a => M a *ᵥ y a) := by
  refine Measurable.of_eval fun b => ?_
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun b' _ =>
    (hM.eval_matrix).mul ((measurable_pi_apply b').comp hy)

lemma Measurable.dotProduct' {y z : α → B → ℂ} (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun a => y a ⬝ᵥ z a) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun b _ =>
    ((measurable_pi_apply b).comp hy).mul ((measurable_pi_apply b).comp hz)

/-- Expectation of a function that is affine in `(|c|², c)` up to a bounded remainder. -/
lemma integral_affine_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℂ} (hc : Measurable c) {K : ℝ}
    (hK : ∀ᵐ ω ∂μ, ‖c ω‖ ≤ K) {F : ℂ → ℝ} (hF : Measurable F) (a0 a2 : ℝ) (κ : ℂ) {ρ : ℝ}
    (hR : ∀ z : ℂ, ‖z‖ ≤ K → |F z - (a0 + a2 * ‖z‖ ^ 2 + (z * κ).re)| ≤ ρ) :
    Integrable (fun ω => F (c ω)) μ ∧
    |∫ ω, F (c ω) ∂μ - (a0 + a2 * ∫ ω, ‖c ω‖ ^ 2 ∂μ + ((∫ ω, c ω ∂μ) * κ).re)| ≤ ρ := by
  have hcI : Integrable c μ := Integrable.of_bound hc.aestronglyMeasurable K hK
  have hc2I : Integrable (fun ω => ‖c ω‖ ^ 2) μ := by
    refine Integrable.of_bound ((continuous_norm.measurable.comp hc).pow_const 2).aestronglyMeasurable
      (K ^ 2) ?_
    filter_upwards [hK] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hLI : Integrable (fun ω => a0 + a2 * ‖c ω‖ ^ 2 + (c ω * κ).re) μ :=
    ((integrable_const a0).add (hc2I.const_mul a2)).add (hcI.mul_const κ).re
  have hFI : Integrable (fun ω => F (c ω)) μ := by
    refine Integrable.of_bound (hF.comp hc).aestronglyMeasurable
      (|a0| + |a2| * K ^ 2 + K * ‖κ‖ + ρ) ?_
    filter_upwards [hK] with ω hω
    have h1 := hR (c ω) hω
    have h2 : |a0 + a2 * ‖c ω‖ ^ 2 + (c ω * κ).re| ≤ |a0| + |a2| * K ^ 2 + K * ‖κ‖ := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
      · rw [abs_mul, abs_of_nonneg (sq_nonneg ‖c ω‖)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hω 2) (abs_nonneg _)
      · refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (F (c ω)) (a0 + a2 * ‖c ω‖ ^ 2 + (c ω * κ).re)
    linarith
  refine ⟨hFI, ?_⟩
  have eL : ∫ ω, (a0 + a2 * ‖c ω‖ ^ 2 + (c ω * κ).re) ∂μ
      = a0 + a2 * ∫ ω, ‖c ω‖ ^ 2 ∂μ + ((∫ ω, c ω ∂μ) * κ).re := by
    have i1 : Integrable (fun ω => a0 + a2 * ‖c ω‖ ^ 2) μ :=
      (integrable_const a0).add (hc2I.const_mul a2)
    have i2 : Integrable (fun ω => (c ω * κ).re) μ := (hcI.mul_const κ).re
    have i3 : Integrable (fun ω => a2 * ‖c ω‖ ^ 2) μ := hc2I.const_mul a2
    rw [integral_add i1 i2, integral_add (integrable_const a0) i3, integral_const, probReal_univ,
      one_smul, integral_const_mul]
    congr 1
    have := integral_re (hcI.mul_const κ)
    simp only [RCLike.re_to_complex] at this
    rw [this, integral_mul_const]
  rw [← eL, ← integral_sub hFI hLI, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => F (c ω) - (a0 + a2 * ‖c ω‖ ^ 2 + (c ω * κ).re)) (C := ρ)
    (by filter_upwards [hK] with ω hω; rw [Real.norm_eq_abs]; exact hR _ hω)
  rwa [probReal_univ, mul_one] at this

end Prob

namespace NHeat

variable {ι B : Type*} [Fintype B] [DecidableEq B] (H : NHeat ι B)

lemma continuous_D : Continuous (fun c : ℂ => H.D c) := by
  have : (fun c : ℂ => H.D c) = fun c => (((‖c‖ ^ 2 * H.vn - 1 : ℝ)) : ℂ)
      • vecMulVec (star H.ux) H.ux + c • vecMulVec H.b H.ux
      + conj c • vecMulVec (star H.ux) (star H.b) := funext H.D_eq
  rw [this]
  fun_prop

lemma continuous_w (i : ι) : Continuous (fun c : ℂ => H.w c i) := by
  unfold w; fun_prop

lemma measurable_lev' (i : ι) : Measurable (fun c : ℂ => H.lev' c i) := by
  unfold lev'
  have h1 : Measurable (fun c : ℂ => (1 + H.D c)⁻¹) :=
    measurable_matrix_inv.comp (continuous_const.add H.continuous_D).measurable
  have h2 : Measurable (fun c : ℂ => star (H.w c i)) := (H.continuous_w i).star.measurable
  exact Complex.measurable_re.comp
    (Measurable.dotProduct' (H.continuous_w i).measurable (Measurable.mulVec' h1 h2))

lemma measurable_A' : Measurable (fun c : ℂ => H.A' c) := by
  unfold A'; exact Finset.measurable_sum _ fun i _ => H.measurable_lev' i

lemma measurable_P' : Measurable (fun c : ℂ => H.P' c) := by
  unfold P'; exact Finset.measurable_sum _ fun i _ => (H.measurable_lev' i).pow_const 2

/-- `∑_i |v_i|⁴`. -/
noncomputable def v4 : ℝ := ∑ i ∈ H.S, ‖H.v i‖ ^ 4

/-- almost-sure bound on `‖D_*‖_F²` when `|c| ≤ K`. -/
noncomputable def Φ (K : ℝ) : ℝ :=
  3 * ((K ^ 2 * H.vn + 1) ^ 2 * H.m ^ 2 + 2 * K ^ 2 * nsq H.b * H.m)

/-- Bessel constant of the new rows when `|c| ≤ K`. -/
noncomputable def ω (K : ℝ) : ℝ := 2 * (1 + K ^ 2 * H.vn * H.m)

/-- remainder bound for `𝒜`. -/
noncomputable def ρA (K : ℝ) : ℝ := (1 + 2 * H.ω K) * H.Φ K

/-- remainder bound for `𝒫`. -/
noncomputable def ρP (K : ℝ) : ℝ :=
  2 * (K ^ 2 * H.vw H.lev * H.m * √(H.Φ K) + 2 * K * √H.m * √(H.Φ K) * (H.m * √H.vn))
    + 4 * H.m * H.ω K * H.Φ K + 16 * K ^ 2 * H.m * H.vw H.lev + 4 * K ^ 4 * H.m ^ 2 * H.v4
    + 8 * (2 * H.m + 2 * K ^ 2 * H.vn * H.m) * H.ω K * H.Φ K

lemma lev_nn (i : ι) : 0 ≤ H.lev i := nsq_nonneg _

lemma m_nn : 0 ≤ H.m := nsq_nonneg _

lemma vn_nonneg : 0 ≤ H.vn := sum_nonneg fun _ _ => sq_nonneg _

lemma vw_lev_nonneg : 0 ≤ H.vw H.lev :=
  sum_nonneg fun _ _ => mul_nonneg (nsq_nonneg _) (sq_nonneg _)

lemma v4_nonneg : 0 ≤ H.v4 := sum_nonneg fun _ _ => by positivity

lemma ω_nonneg (K : ℝ) : 0 ≤ H.ω K := by
  have := H.vn_nonneg; have := nsq_nonneg H.ux
  unfold ω m; positivity

lemma Φ_nonneg (K : ℝ) : 0 ≤ H.Φ K := by
  have := H.vn_nonneg; have := nsq_nonneg H.ux; have := nsq_nonneg H.b
  unfold Φ m; positivity

lemma norm_sq_v_le_vn {i : ι} (hi : i ∈ H.S) : ‖H.v i‖ ^ 2 ≤ H.vn :=
  single_le_sum (f := fun i => ‖H.v i‖ ^ 2) (fun _ _ => sq_nonneg _) hi

/-- `‖D_*‖_F² ≤ Φ(K)` (eq. `clearing-gram-bounds`, Frobenius form). -/
lemma fro_D_le (c : ℂ) (K : ℝ) (hc : ‖c‖ ≤ K) : fro (H.D c) ≤ H.Φ K := by
  rw [D_eq]
  refine (fro_add3_le _ _ _).trans ?_
  rw [fro_smul, fro_smul, fro_smul, fro_vecMulVec, fro_vecMulVec, fro_vecMulVec, nsq_star,
    nsq_star, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_conj]
  have hvn := H.vn_nonneg
  have hm := nsq_nonneg H.ux
  have hb := nsq_nonneg H.b
  have hc0 := norm_nonneg c
  have hK : ‖c‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hc0 hc 2
  have h1 : (‖c‖ ^ 2 * H.vn - 1) ^ 2 ≤ (K ^ 2 * H.vn + 1) ^ 2 := by
    refine sq_le_sq' ?_ ?_
    · nlinarith
    · nlinarith
  unfold Φ m
  have : (‖c‖ ^ 2 * H.vn - 1) ^ 2 * (nsq H.ux * nsq H.ux) + ‖c‖ ^ 2 * (nsq H.b * nsq H.ux)
      + ‖c‖ ^ 2 * (nsq H.ux * nsq H.b)
      ≤ (K ^ 2 * H.vn + 1) ^ 2 * nsq H.ux ^ 2 + 2 * K ^ 2 * nsq H.b * nsq H.ux := by
    have e1 : (‖c‖ ^ 2 * H.vn - 1) ^ 2 * (nsq H.ux * nsq H.ux)
        ≤ (K ^ 2 * H.vn + 1) ^ 2 * nsq H.ux ^ 2 := by
      rw [← sq]; exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have e2 : ‖c‖ ^ 2 * (nsq H.b * nsq H.ux) ≤ K ^ 2 * (nsq H.b * nsq H.ux) :=
      mul_le_mul_of_nonneg_right hK (mul_nonneg hb hm)
    nlinarith
  linarith

/-! ### The total leverage -/

/-- `Re (u_x (1-Q) u_x*)`. -/
noncomputable def kA1 : ℝ := (H.ux ⬝ᵥ ((1 - H.Q) *ᵥ star H.ux)).re
/-- coefficient of `c` in `Re tr(D (1 - Q))`. -/
noncomputable def kA2 : ℂ :=
  H.ux ⬝ᵥ ((1 - H.Q) *ᵥ H.b) + conj (star H.b ⬝ᵥ ((1 - H.Q) *ᵥ star H.ux))

/-- affine part of `𝒜' - 𝒜`. -/
noncomputable def LA (c : ℂ) : ℝ := (‖c‖ ^ 2 * H.vn - 1) * H.kA1 + (c * H.kA2).re

lemma abs_A'_sub_A_sub_LA (hB : H.Bessel) (c : ℂ) (K : ℝ) (hc : ‖c‖ ≤ K)
    (hΦ : H.Φ K ≤ 1 / 4) :
    |H.A' c - H.A - H.LA c| ≤ H.ρA K := by
  have hF0 := H.fro_D_le c K hc
  have hF : fro (H.D c) ≤ 1 / 4 := hF0.trans hΦ
  have e : H.A' c - H.A - H.LA c = -fro (H.D c)
      + ∑ i ∈ H.S, (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re := by
    rw [H.A'_sub_A c hF, re_trace_D_mul, LA, kA1, kA2]; ring
  rw [e]
  have hω : ‖c‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg c) hc 2
  have hW : ∀ z : B → ℂ, ∑ i ∈ H.S, ‖H.w c i ⬝ᵥ z‖ ^ 2 ≤ H.ω K * nsq z := by
    intro z
    refine (H.W_bessel hB c z).trans (mul_le_mul_of_nonneg_right ?_ (nsq_nonneg z))
    unfold ω
    have := H.vn_nonneg; have := nsq_nonneg H.ux
    have : ‖c‖ ^ 2 * H.vn * H.m ≤ K ^ 2 * H.vn * H.m := by unfold m; gcongr
    linarith
  have hq := H.sum_nsq_q_le c (H.ω K) hW
  have h1 : |∑ i ∈ H.S, (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re|
      ≤ 2 * ∑ i ∈ H.S, nsq (H.q c i) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    exact sum_le_sum fun i _ => (Complex.abs_re_le_norm _).trans (H.norm_q_Z_le c hF i)
  have h2 := fro_nonneg (H.D c)
  have h3 := H.ω_nonneg K
  calc |-fro (H.D c) + ∑ i ∈ H.S, (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re|
      ≤ fro (H.D c) + 2 * ∑ i ∈ H.S, nsq (H.q c i) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_of_nonneg h2]; linarith
    _ ≤ fro (H.D c) + 2 * (H.ω K * fro (H.D c)) := by linarith
    _ = (1 + 2 * H.ω K) * fro (H.D c) := by ring
    _ ≤ H.ρA K := mul_le_mul_of_nonneg_left hF0 (by linarith)

/-! ### The squared leverage -/

/-- `Re (u_x X₀ u_x*)`, `X₀ = ∑ m_i u_i* u_i`. -/
noncomputable def kP1 : ℝ := (H.ux ⬝ᵥ (H.G0 H.lev *ᵥ star H.ux)).re
/-- coefficient of `c` in `Re tr(D X₀)`. -/
noncomputable def kP2 : ℂ :=
  H.ux ⬝ᵥ (H.G0 H.lev *ᵥ H.b) + conj (star H.b ⬝ᵥ (H.G0 H.lev *ᵥ star H.ux))

/-- affine part of `𝒫' - 𝒫`. -/
noncomputable def LP (c : ℂ) : ℝ :=
  -H.m ^ 2 + 2 * (2 * (c * (H.ux ⬝ᵥ H.bw H.lev)).re + ‖c‖ ^ 2 * H.m * H.vw H.lev)
    - 2 * ((‖c‖ ^ 2 * H.vn - 1) * H.kP1 + (c * H.kP2).re)

/-- the part of `∑ m_i w_i D w_i*` that comes from replacing old rows by new ones. -/
noncomputable def TP (c : ℂ) : ℂ :=
  ((‖c‖ ^ 2 * H.vw H.lev : ℝ) : ℂ) * (H.ux ⬝ᵥ (H.D c *ᵥ star H.ux))
    + c * (H.ux ⬝ᵥ (H.D c *ᵥ H.bw H.lev))
    + conj c * (star (H.bw H.lev) ⬝ᵥ (H.D c *ᵥ star H.ux))

/-- Exact decomposition (eq. `clearing-square-decomposition` with the expansions of l.580–640). -/
lemma P'_sub_P (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) :
    H.P' c - H.P = H.LP c - 2 * (H.TP c).re
      + 2 * ∑ i ∈ H.S, H.lev i * (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re
      + ∑ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2 := by
  have e1 : H.P' c - H.P = 2 * ∑ i ∈ H.S, H.lev i * (H.lev' c i - H.lev i)
      + ∑ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2 - H.m ^ 2 := by
    simp only [P', P]
    rw [show ∑ i ∈ H.S, H.lev' c i ^ 2 = ∑ i ∈ H.S, (H.lev i ^ 2
        + 2 * (H.lev i * (H.lev' c i - H.lev i)) + (H.lev' c i - H.lev i) ^ 2) from
      sum_congr rfl fun i _ => by ring]
    simp only [sum_add_distrib, mul_sum]
    ring
  have e2 : ∑ i ∈ H.S, H.lev i * (H.lev' c i - H.lev i)
      = ∑ i ∈ H.S, H.lev i * (nsq (H.w c i) - H.lev i)
        - (∑ i ∈ H.S, (H.lev i : ℂ) * (H.w c i ⬝ᵥ (H.D c *ᵥ star (H.w c i)))).re
        + ∑ i ∈ H.S, H.lev i * (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re := by
    rw [Complex.re_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [H.lev'_expand c hF i, Complex.re_ofReal_mul]; ring
  have e3 := H.sum_lev_wDw c
  have e4 : (trace (H.D c * H.G0 H.lev)).re = (‖c‖ ^ 2 * H.vn - 1) * H.kP1 + (c * H.kP2).re := by
    rw [re_trace_D_mul, kP1, kP2]
  rw [e1, e2, e3, H.sum_lev_d0 c]
  simp only [Complex.add_re] at *
  rw [e4]
  unfold LP TP
  simp only [Complex.add_re]
  ring

lemma nsq_bw_lev_le (hB : H.Bessel) (hmax : ∀ i ∈ H.S, H.lev i ≤ H.m) :
    nsq (H.bw H.lev) ≤ H.m ^ 2 * H.vn := by
  refine (hB.dual _).trans ?_
  rw [vn, mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (H.lev_nn i)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (H.lev_nn i) (hmax i hi) 2) (sq_nonneg _)

lemma abs_P'_sub_P_sub_LP (hB : H.Bessel) (hmax : ∀ i ∈ H.S, H.lev i ≤ H.m) (c : ℂ) (K : ℝ)
    (hc : ‖c‖ ≤ K) (hΦ : H.Φ K ≤ 1 / 4) :
    |H.P' c - H.P - H.LP c| ≤ H.ρP K := by
  have hF0 := H.fro_D_le c K hc
  have hF : fro (H.D c) ≤ 1 / 4 := hF0.trans hΦ
  have hK0 : 0 ≤ K := (norm_nonneg c).trans hc
  have hc2 : ‖c‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg c) hc 2
  have hm : 0 ≤ H.m := H.m_nn
  have hvn := H.vn_nonneg
  have hvL := H.vw_lev_nonneg
  have hW : ∀ z : B → ℂ, ∑ i ∈ H.S, ‖H.w c i ⬝ᵥ z‖ ^ 2 ≤ H.ω K * nsq z := by
    intro z
    refine (H.W_bessel hB c z).trans (mul_le_mul_of_nonneg_right ?_ (nsq_nonneg z))
    unfold ω
    have : ‖c‖ ^ 2 * H.vn * H.m ≤ K ^ 2 * H.vn * H.m := by gcongr
    linarith
  have hq := H.sum_nsq_q_le c (H.ω K) hW
  have hω := H.ω_nonneg K
  have hmm : √(nsq H.ux) * √(nsq H.ux) = H.m := Real.mul_self_sqrt (nsq_nonneg _)
  have hFn := fro_nonneg (H.D c)
  have hsF : √(fro (H.D c)) ≤ √(H.Φ K) := Real.sqrt_le_sqrt hF0
  -- the replacement term
  have hT : ‖H.TP c‖ ≤ K ^ 2 * H.vw H.lev * H.m * √(H.Φ K)
      + 2 * K * √H.m * √(H.Φ K) * (H.m * √H.vn) := by
    have hbL : √(nsq (H.bw H.lev)) ≤ H.m * √H.vn := by
      rw [← Real.sqrt_sq hm, ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt (H.nsq_bw_lev_le hB hmax)
    have t1 : ‖((‖c‖ ^ 2 * H.vw H.lev : ℝ) : ℂ) * (H.ux ⬝ᵥ (H.D c *ᵥ star H.ux))‖
        ≤ K ^ 2 * H.vw H.lev * H.m * √(H.Φ K) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have h1 := norm_dotProduct_mulVec_le (H.D c) H.ux (star H.ux)
      rw [nsq_star] at h1
      have h2 : ‖H.ux ⬝ᵥ (H.D c *ᵥ star H.ux)‖ ≤ H.m * √(H.Φ K) := by
        refine h1.trans ?_
        calc √(nsq H.ux) * √(fro (H.D c)) * √(nsq H.ux)
            = (√(nsq H.ux) * √(nsq H.ux)) * √(fro (H.D c)) := by ring
          _ ≤ H.m * √(H.Φ K) := by rw [hmm]; exact mul_le_mul_of_nonneg_left hsF hm
      calc ‖c‖ ^ 2 * H.vw H.lev * ‖H.ux ⬝ᵥ (H.D c *ᵥ star H.ux)‖
          ≤ K ^ 2 * H.vw H.lev * (H.m * √(H.Φ K)) := by gcongr
        _ = _ := by ring
    have t2 : ‖c * (H.ux ⬝ᵥ (H.D c *ᵥ H.bw H.lev))‖ ≤ K * √H.m * √(H.Φ K) * (H.m * √H.vn) := by
      rw [norm_mul]
      have h1 := norm_dotProduct_mulVec_le (H.D c) H.ux (H.bw H.lev)
      have h2 : ‖H.ux ⬝ᵥ (H.D c *ᵥ H.bw H.lev)‖ ≤ √H.m * √(H.Φ K) * (H.m * √H.vn) := by
        refine h1.trans ?_
        refine mul_le_mul (mul_le_mul_of_nonneg_left hsF (Real.sqrt_nonneg _)) hbL
          (Real.sqrt_nonneg _) (by positivity)
      calc ‖c‖ * ‖H.ux ⬝ᵥ (H.D c *ᵥ H.bw H.lev)‖
          ≤ K * (√H.m * √(H.Φ K) * (H.m * √H.vn)) :=
            mul_le_mul hc h2 (norm_nonneg _) hK0
        _ = _ := by ring
    have t3 : ‖conj c * (star (H.bw H.lev) ⬝ᵥ (H.D c *ᵥ star H.ux))‖
        ≤ K * √H.m * √(H.Φ K) * (H.m * √H.vn) := by
      rw [norm_mul, Complex.norm_conj]
      have h1 := norm_dotProduct_mulVec_le (H.D c) (star (H.bw H.lev)) (star H.ux)
      rw [nsq_star, nsq_star] at h1
      have h2 : ‖star (H.bw H.lev) ⬝ᵥ (H.D c *ᵥ star H.ux)‖
          ≤ (H.m * √H.vn) * √(H.Φ K) * √H.m := by
        refine h1.trans ?_
        exact mul_le_mul (mul_le_mul hbL hsF (Real.sqrt_nonneg _) (by positivity)) le_rfl
          (Real.sqrt_nonneg _) (by positivity)
      calc ‖c‖ * ‖star (H.bw H.lev) ⬝ᵥ (H.D c *ᵥ star H.ux)‖
          ≤ K * ((H.m * √H.vn) * √(H.Φ K) * √H.m) := mul_le_mul hc h2 (norm_nonneg _) hK0
        _ = _ := by ring
    unfold TP
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (((‖c‖ ^ 2 * H.vw H.lev : ℝ) : ℂ) * (H.ux ⬝ᵥ (H.D c *ᵥ star H.ux)))
      (c * (H.ux ⬝ᵥ (H.D c *ᵥ H.bw H.lev)))
    linarith
  -- the second-order normalization term
  have hE : |∑ i ∈ H.S, H.lev i * (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re|
      ≤ 2 * H.m * (H.ω K * H.Φ K) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ H.S, |H.lev i * (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re|
        ≤ ∑ i ∈ H.S, H.m * (2 * nsq (H.q c i)) := by
          refine sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_of_nonneg (H.lev_nn i)]
          exact mul_le_mul (hmax i hi)
            ((Complex.abs_re_le_norm _).trans (H.norm_q_Z_le c hF i)) (abs_nonneg _) hm
      _ = 2 * H.m * ∑ i ∈ H.S, nsq (H.q c i) := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ ≤ 2 * H.m * (H.ω K * fro (H.D c)) := by gcongr
      _ ≤ 2 * H.m * (H.ω K * H.Φ K) := by gcongr
  -- the square terms
  have hS : ∑ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2
      ≤ 16 * K ^ 2 * H.m * H.vw H.lev + 4 * K ^ 4 * H.m ^ 2 * H.v4
        + 8 * (2 * H.m + 2 * K ^ 2 * H.vn * H.m) * (H.ω K * H.Φ K) := by
    have hWm : ∀ i ∈ H.S, nsq (H.w c i) ≤ 2 * H.m + 2 * K ^ 2 * H.vn * H.m := by
      intro i hi
      have h1 := nsq_add_le (H.u i) ((c * H.v i) • H.ux)
      rw [nsq_smul, norm_mul, mul_pow] at h1
      have h2 : ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * nsq H.ux ≤ K ^ 2 * H.vn * H.m := by
        unfold m; gcongr; exact H.norm_sq_v_le_vn hi
      have h3 := hmax i hi
      unfold lev at h3
      unfold w; linarith
    have hpt : ∀ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2
        ≤ 16 * K ^ 2 * H.m * (H.lev i * ‖H.v i‖ ^ 2) + 4 * K ^ 4 * H.m ^ 2 * ‖H.v i‖ ^ 4
          + 8 * (2 * H.m + 2 * K ^ 2 * H.vn * H.m) * nsq (H.q c i) := by
      intro i hi
      set d0 := nsq (H.w c i) - H.lev i
      set d1 := H.lev' c i - nsq (H.w c i)
      have hd1 : d1 ^ 2 ≤ 4 * (2 * H.m + 2 * K ^ 2 * H.vn * H.m) * nsq (H.q c i) := by
        have h := H.abs_lev'_sub_le c hF i
        have h' : d1 ^ 2 ≤ (2 * (√(nsq (H.w c i)) * √(nsq (H.q c i)))) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
        rw [mul_pow, mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at h'
        have := mul_le_mul_of_nonneg_right (hWm i hi) (nsq_nonneg (H.q c i))
        nlinarith
      have hd0 : d0 ^ 2 ≤ 8 * K ^ 2 * H.m * (H.lev i * ‖H.v i‖ ^ 2)
          + 2 * K ^ 4 * H.m ^ 2 * ‖H.v i‖ ^ 4 := by
        have e : d0 = 2 * (c * H.v i * (H.ux ⬝ᵥ star (H.u i))).re + ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m := by
          simp only [d0, nsq_w]; ring
        have h1 : |2 * (c * H.v i * (H.ux ⬝ᵥ star (H.u i))).re|
            ≤ 2 * (K * ‖H.v i‖ * (√H.m * √(H.lev i))) := by
          rw [abs_mul, abs_two]
          refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) zero_le_two
          rw [norm_mul, norm_mul]
          have := norm_dotProduct_le H.ux (star (H.u i))
          rw [nsq_star] at this
          exact mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) this (norm_nonneg _)
            (by positivity)
        have h1' : (2 * (c * H.v i * (H.ux ⬝ᵥ star (H.u i))).re) ^ 2
            ≤ 4 * K ^ 2 * ‖H.v i‖ ^ 2 * (H.m * H.lev i) := by
          have := pow_le_pow_left₀ (abs_nonneg _) h1 2
          rw [sq_abs] at this
          refine this.trans (le_of_eq ?_)
          rw [show (2 * (K * ‖H.v i‖ * (√H.m * √(H.lev i)))) ^ 2
              = 4 * K ^ 2 * ‖H.v i‖ ^ 2 * (√H.m ^ 2 * √(H.lev i) ^ 2) by ring,
            Real.sq_sqrt hm, Real.sq_sqrt (H.lev_nn i)]
        have h2 : (‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m) ^ 2 ≤ K ^ 4 * ‖H.v i‖ ^ 4 * H.m ^ 2 := by
          have : (‖c‖ ^ 2) ^ 2 ≤ (K ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hc2 2
          calc (‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m) ^ 2 = (‖c‖ ^ 2) ^ 2 * (‖H.v i‖ ^ 4 * H.m ^ 2) := by
                ring
            _ ≤ (K ^ 2) ^ 2 * (‖H.v i‖ ^ 4 * H.m ^ 2) := by gcongr
            _ = _ := by ring
        rw [e]
        nlinarith [sq_nonneg (2 * (c * H.v i * (H.ux ⬝ᵥ star (H.u i))).re
          - ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m)]
      have : H.lev' c i - H.lev i = d0 + d1 := by simp only [d0, d1]; ring
      rw [this]
      nlinarith [sq_nonneg (d0 - d1)]
    calc ∑ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2
        ≤ ∑ i ∈ H.S, (16 * K ^ 2 * H.m * (H.lev i * ‖H.v i‖ ^ 2) + 4 * K ^ 4 * H.m ^ 2 * ‖H.v i‖ ^ 4
          + 8 * (2 * H.m + 2 * K ^ 2 * H.vn * H.m) * nsq (H.q c i)) := sum_le_sum hpt
      _ = 16 * K ^ 2 * H.m * H.vw H.lev + 4 * K ^ 4 * H.m ^ 2 * H.v4
          + 8 * (2 * H.m + 2 * K ^ 2 * H.vn * H.m) * ∑ i ∈ H.S, nsq (H.q c i) := by
        simp only [sum_add_distrib, ← mul_sum, vw, v4]
      _ ≤ _ := by
        have : 0 ≤ 8 * (2 * H.m + 2 * K ^ 2 * H.vn * H.m) := by unfold m; positivity
        gcongr
        exact hq.trans (mul_le_mul_of_nonneg_left hF0 hω)
  rw [H.P'_sub_P c hF]
  have hre : |(H.TP c).re| ≤ ‖H.TP c‖ := Complex.abs_re_le_norm _
  have hS0 : 0 ≤ ∑ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have key : |H.LP c - 2 * (H.TP c).re
      + 2 * ∑ i ∈ H.S, H.lev i * (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re
      + ∑ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2 - H.LP c|
      ≤ 2 * ‖H.TP c‖ + 2 * (2 * H.m * (H.ω K * H.Φ K))
        + ∑ i ∈ H.S, (H.lev' c i - H.lev i) ^ 2 := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (∑ i ∈ H.S, H.lev i * (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re)
      have := le_abs_self ((H.TP c).re)
      linarith
    · have := le_abs_self (∑ i ∈ H.S, H.lev i * (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re)
      have := neg_abs_le ((H.TP c).re)
      linarith
  refine key.trans ?_
  unfold ρP
  nlinarith

/-! ### The conditional drift of the normalized heat -/

/-- **Normalized leverage drift.** For a random heat coefficient `c` with `|c| ≤ K` almost surely,
the conditional changes of `𝒜` and `𝒫` are controlled by `𝔼c`, `𝔼|c|²` and the explicit
remainders `ρA`, `ρP` (all deterministic). This is the abstract content of the proof of
Lemma 6.4, eqs. `clearing-total-leverage`–`clearing-normalization-squares`. -/
theorem drift {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : Ω → ℂ) (hc : Measurable c) (K : ℝ) (hK : ∀ᵐ ω ∂μ, ‖c ω‖ ≤ K)
    (hB : H.Bessel) (hmax : ∀ i ∈ H.S, H.lev i ≤ H.m) (hΦ : H.Φ K ≤ 1 / 4) :
    Integrable (fun ω => H.A' (c ω) - H.A) μ ∧ Integrable (fun ω => H.P' (c ω) - H.P) μ ∧
    |∫ ω, (H.A' (c ω) - H.A) ∂μ|
      ≤ 3 * H.m * |(∫ ω, ‖c ω‖ ^ 2 ∂μ) * H.vn - 1|
        + 6 * ‖∫ ω, c ω ∂μ‖ * √H.m * √(nsq H.b) + H.ρA K ∧
    ∫ ω, (H.P' (c ω) - H.P) ∂μ
      ≤ -H.m ^ 2 + 2 * (∫ ω, ‖c ω‖ ^ 2 ∂μ) * H.m * H.vw H.lev
        + 2 * H.m ^ 2 * |(∫ ω, ‖c ω‖ ^ 2 ∂μ) * H.vn - 1|
        + 4 * ‖∫ ω, c ω ∂μ‖ * H.m * √H.m * (√H.vn + √(nsq H.b)) + H.ρP K := by
  set Ec := ∫ ω, c ω ∂μ
  set Ec2 := ∫ ω, ‖c ω‖ ^ 2 ∂μ
  have hm := H.m_nn
  have hsm : √H.m * √H.m = H.m := Real.mul_self_sqrt hm
  -- total leverage
  obtain ⟨hAI, hA⟩ := integral_affine_bound (μ := μ) hc hK (F := fun z => H.A' z - H.A)
    ((H.measurable_A').sub_const _) (-H.kA1) (H.vn * H.kA1) H.kA2 (ρ := H.ρA K)
    (fun z hz => by
      have := H.abs_A'_sub_A_sub_LA hB z K hz hΦ
      convert this using 2; unfold LA; ring)
  -- squared leverage
  obtain ⟨hPI, hP⟩ := integral_affine_bound (μ := μ) hc hK (F := fun z => H.P' z - H.P)
    ((H.measurable_P').sub_const _) (-H.m ^ 2 + 2 * H.kP1)
    (2 * H.m * H.vw H.lev - 2 * H.vn * H.kP1) (4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2)
    (ρ := H.ρP K)
    (fun z hz => by
      have := H.abs_P'_sub_P_sub_LP hB hmax z K hz hΦ
      have e : (z * (4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2)).re
          = 4 * (z * (H.ux ⬝ᵥ H.bw H.lev)).re - 2 * (z * H.kP2).re := by
        simp only [mul_sub, Complex.sub_re, Complex.mul_re, Complex.mul_im]
        norm_num; ring
      convert this using 2; unfold LP; rw [e]; ring)
  refine ⟨hAI, hPI, ?_, ?_⟩
  · -- the affine part of `𝒜`
    have k1 : |H.kA1| ≤ 3 * H.m := by
      have := (Complex.abs_re_le_norm _).trans (hB.V_form H.ux (star H.ux))
      rw [nsq_star] at this
      unfold kA1
      calc _ ≤ 3 * (√(nsq H.ux) * √(nsq H.ux)) := this
        _ = 3 * H.m := by rw [Real.mul_self_sqrt (nsq_nonneg _)]; rfl
    have k2 : ‖H.kA2‖ ≤ 6 * (√H.m * √(nsq H.b)) := by
      unfold kA2
      have h1 := hB.V_form H.ux H.b
      have h2 := hB.V_form (star H.b) (star H.ux)
      rw [nsq_star, nsq_star] at h2
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_conj]
      unfold m
      linarith [mul_comm (√(nsq H.b)) (√(nsq H.ux))]
    have hlin : |-H.kA1 + H.vn * H.kA1 * Ec2 + (Ec * H.kA2).re|
        ≤ 3 * H.m * |Ec2 * H.vn - 1| + 6 * ‖Ec‖ * √H.m * √(nsq H.b) := by
      have e : -H.kA1 + H.vn * H.kA1 * Ec2 + (Ec * H.kA2).re
          = (Ec2 * H.vn - 1) * H.kA1 + (Ec * H.kA2).re := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, mul_comm (3 * H.m)]
        exact mul_le_mul_of_nonneg_left k1 (abs_nonneg _)
      · refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul]
        calc ‖Ec‖ * ‖H.kA2‖ ≤ ‖Ec‖ * (6 * (√H.m * √(nsq H.b))) :=
              mul_le_mul_of_nonneg_left k2 (norm_nonneg _)
          _ = _ := by ring
    have : ∫ ω, (H.A' (c ω) - H.A) ∂μ
        = (∫ ω, (H.A' (c ω) - H.A) ∂μ - (-H.kA1 + H.vn * H.kA1 * Ec2 + (Ec * H.kA2).re))
          + (-H.kA1 + H.vn * H.kA1 * Ec2 + (Ec * H.kA2).re) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith
  · -- the affine part of `𝒫`
    have k1 : |H.kP1| ≤ H.m ^ 2 := by
      have := (Complex.abs_re_le_norm _).trans (hB.G0_form hmax H.ux (star H.ux))
      rw [nsq_star] at this
      unfold kP1
      calc _ ≤ H.m * (√(nsq H.ux) * √(nsq H.ux)) := this
        _ = H.m ^ 2 := by rw [Real.mul_self_sqrt (nsq_nonneg _)]; unfold m; ring
    have k2 : ‖H.kP2‖ ≤ 2 * (H.m * √H.m * √(nsq H.b)) := by
      unfold kP2
      have h1 := hB.G0_form hmax H.ux H.b
      have h2 := hB.G0_form hmax (star H.b) (star H.ux)
      rw [nsq_star, nsq_star] at h2
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_conj]
      unfold m at *
      nlinarith [mul_comm (√(nsq H.b)) (√(nsq H.ux))]
    have k3 : ‖H.ux ⬝ᵥ H.bw H.lev‖ ≤ H.m * √H.m * √H.vn := by
      refine (norm_dotProduct_le _ _).trans ?_
      have : √(nsq (H.bw H.lev)) ≤ H.m * √H.vn := by
        rw [← Real.sqrt_sq hm, ← Real.sqrt_mul (sq_nonneg _)]
        exact Real.sqrt_le_sqrt (H.nsq_bw_lev_le hB hmax)
      calc √(nsq H.ux) * √(nsq (H.bw H.lev)) ≤ √H.m * (H.m * √H.vn) :=
            mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
        _ = _ := by ring
    have hEc2 : 0 ≤ Ec2 := integral_nonneg fun ω => sq_nonneg _
    have hlin : -H.m ^ 2 + 2 * H.kP1 + (2 * H.m * H.vw H.lev - 2 * H.vn * H.kP1) * Ec2
          + (Ec * (4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2)).re
        ≤ -H.m ^ 2 + 2 * Ec2 * H.m * H.vw H.lev + 2 * H.m ^ 2 * |Ec2 * H.vn - 1|
          + 4 * ‖Ec‖ * H.m * √H.m * (√H.vn + √(nsq H.b)) := by
      have e : -H.m ^ 2 + 2 * H.kP1 + (2 * H.m * H.vw H.lev - 2 * H.vn * H.kP1) * Ec2
          + (Ec * (4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2)).re
          = -H.m ^ 2 + 2 * Ec2 * H.m * H.vw H.lev - 2 * ((Ec2 * H.vn - 1) * H.kP1)
            + (Ec * (4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2)).re := by ring
      rw [e]
      have t1 : -(2 * ((Ec2 * H.vn - 1) * H.kP1)) ≤ 2 * H.m ^ 2 * |Ec2 * H.vn - 1| := by
        have := neg_abs_le ((Ec2 * H.vn - 1) * H.kP1)
        rw [abs_mul] at this
        have := mul_le_mul_of_nonneg_left k1 (abs_nonneg (Ec2 * H.vn - 1))
        nlinarith
      have t2 : (Ec * (4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2)).re
          ≤ 4 * ‖Ec‖ * H.m * √H.m * (√H.vn + √(nsq H.b)) := by
        refine (Complex.re_le_norm _).trans ?_
        rw [norm_mul]
        have : ‖4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2‖
            ≤ 4 * (H.m * √H.m * √H.vn) + 2 * (2 * (H.m * √H.m * √(nsq H.b))) := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]; norm_num; exact k3
          · rw [norm_mul]; norm_num; linarith
        calc ‖Ec‖ * ‖4 * (H.ux ⬝ᵥ H.bw H.lev) - 2 * H.kP2‖
            ≤ ‖Ec‖ * (4 * (H.m * √H.m * √H.vn) + 2 * (2 * (H.m * √H.m * √(nsq H.b)))) :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = _ := by ring
      linarith
    have := (abs_le.mp hP).2
    linarith

end NHeat

end AndersonAC.L64
