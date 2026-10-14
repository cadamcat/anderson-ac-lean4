import AndersonAC.AgentS6Row.Expansion
import AndersonAC.AgentS6Row.BiasArithmetic

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6Row

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω}

/-- Conditional row bias for predictable scalar data with a controlled normalization remainder. -/
theorem conditional_row_bias (μ : Measure[mΩ] Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (E : Set Ω) (hE : MeasurableSet[m] E) (D : Ω → RowData) (f : Ω → ℝ) (z : Ω → ℂ)
    (t l c C R V M K a ε : ℝ) (ht : 0 < t) (hl : 0 ≤ l) (hc : 0 < c)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hV : 0 ≤ V) (hM : 0 ≤ M) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hs : Real.sqrt t ≤ 1) (haε : a ≤ ε) (hsε : Real.sqrt t ≤ ε)
    (hvsm : StronglyMeasurable[m] (fun ω => (D ω).v))
    (hmsm : StronglyMeasurable[m] (fun ω => (D ω).m))
    (hssm : StronglyMeasurable[m] (fun ω => (D ω).s))
    (hjsm : StronglyMeasurable[m] (fun ω => (D ω).j))
    (hvnsm : StronglyMeasurable[m] (fun ω => (D ω).vn))
    (hDb : ∀ ω, 0 ≤ (D ω).m ∧ (D ω).m ≤ 4 * l ∧ ‖(D ω).v‖ ≤ 2 ∧ ‖(D ω).s‖ ≤ 4 * l ∧
      ‖(D ω).j‖ ≤ 4 * l / (Real.sqrt t * c) ∧ 0 ≤ (D ω).vn ∧ (D ω).vn ≤ 2)
    (hdev : ∀ ω ∈ E, |(D ω).vn - 1| ≤ V * ε)
    (hzm : Measurable[mΩ] z) (hzb : ∀ ω, ‖z ω‖ ≤ C) (hfI : Integrable f μ)
    (hrem : ∀ ω, |f ω - (D ω).affine (z ω)| ≤ R * (l ^ 2 * ‖(D ω).v‖ / Real.sqrt t + l ^ 3 / t))
    (hmean : ∀ᵐ ω ∂μ, ‖μ[z | m] ω‖ ≤ M * Real.sqrt t * a)
    (hsecond : ∀ᵐ ω ∂μ, |μ[(fun ω => ‖z ω‖ ^ 2) | m] ω - E.indicator (fun _ => (1 : ℝ)) ω| ≤ K * Real.sqrt t) :
    ∀ᵐ ω ∂μ, ω ∈ E → |μ[f | m] ω| ≤ biasConstant c R V M K * l *
      (Real.sqrt t * a * ‖(D ω).v‖ + ‖(D ω).v‖ ^ 2 + l * ε + l * ‖(D ω).v‖ / Real.sqrt t + l ^ 2 / t) := by
  letI : MeasurableSpace Ω := mΩ
  let a0 : Ω → ℝ := fun ω => (D ω).a0
  let a2 : Ω → ℝ := fun ω => (D ω).a2
  let κ : Ω → ℂ := fun ω => (D ω).kappa
  let rEnv : Ω → ℝ := fun ω => R * (l ^ 2 * ‖(D ω).v‖ / Real.sqrt t + l ^ 3 / t)
  let aEnv : Ω → ℝ := fun ω => 4 * l * ‖(D ω).v‖ ^ 2 + 32 * l ^ 2
  let kEnv : Ω → ℝ := fun ω => 4 * l * ‖(D ω).v‖ + 16 * l ^ 2 / (Real.sqrt t * c)
  have hε : 0 ≤ ε := (Real.sqrt_nonneg t).trans hsε
  have ha0m : StronglyMeasurable[m] a0 := hssm.norm.pow 2
  have ha2m : StronglyMeasurable[m] a2 :=
    ((hvsm.norm.pow 2).mul hmsm).sub (hvnsm.mul (hssm.norm.pow 2))
  have hκm : StronglyMeasurable[m] κ := (hvsm.mul hssm).sub (hssm.mul hjsm)
  have ha0b : ∀ ω, ‖a0 ω‖ ≤ 16 * l ^ 2 := fun ω => by
    rw [show a0 ω = ‖(D ω).s‖ ^ 2 from rfl, Real.norm_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hDb ω).2.2.2.1 2
    nlinarith
  have ha2b : ∀ ω, |a2 ω| ≤ aEnv ω := fun ω => by
    obtain ⟨hm0, hm4, _, hs4, _, hvn0, hvn2⟩ := hDb ω
    have hsq : ‖(D ω).s‖ ^ 2 ≤ 16 * l ^ 2 := by nlinarith [norm_nonneg (D ω).s]
    have h1 := mul_le_mul_of_nonneg_right hm4 (sq_nonneg ‖(D ω).v‖)
    have h2 := mul_le_mul hvn2 hsq (sq_nonneg _) (show (0 : ℝ) ≤ 2 by norm_num)
    unfold a2 RowData.a2 aEnv
    calc
      _ ≤ |‖(D ω).v‖ ^ 2 * (D ω).m| + |(D ω).vn * ‖(D ω).s‖ ^ 2| := abs_sub _ _
      _ = ‖(D ω).v‖ ^ 2 * (D ω).m + (D ω).vn * ‖(D ω).s‖ ^ 2 := by
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hm0), abs_of_nonneg (mul_nonneg hvn0 (sq_nonneg _))]
      _ ≤ _ := by nlinarith
  have hκb : ∀ ω, ‖κ ω‖ ≤ kEnv ω := fun ω => by
    have hs4 := (hDb ω).2.2.2.1
    have hj4 := (hDb ω).2.2.2.2.1
    have h1 := mul_le_mul_of_nonneg_left hs4 (norm_nonneg (D ω).v)
    have h2 := mul_le_mul hs4 hj4 (norm_nonneg (D ω).j) (by positivity : 0 ≤ 4 * l)
    unfold κ RowData.kappa kEnv
    calc
      _ ≤ ‖(D ω).v * (D ω).s‖ + ‖(D ω).s * (D ω).j‖ := norm_sub_le _ _
      _ = ‖(D ω).v‖ * ‖(D ω).s‖ + ‖(D ω).s‖ * ‖(D ω).j‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖(D ω).v‖ * (4 * l) + (4 * l) * (4 * l / (Real.sqrt t * c)) := add_le_add h1 h2
      _ = _ := by ring
  have ha2const : ∀ ω, ‖a2 ω‖ ≤ 16 * l + 32 * l ^ 2 := fun ω => by
    have hv2 := (hDb ω).2.2.1
    have hv4 : ‖(D ω).v‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (D ω).v]
    have hh := ha2b ω
    rw [Real.norm_eq_abs]
    unfold aEnv at hh
    nlinarith
  have hκconst : ∀ ω, ‖κ ω‖ ≤ 8 * l + 16 * l ^ 2 / (Real.sqrt t * c) := fun ω => by
    have hh := hκb ω
    have hv2 := (hDb ω).2.2.1
    unfold kEnv at hh
    nlinarith
  have hzI : Integrable z μ := Integrable.of_bound (mα := mΩ) (μ := μ) hzm.aestronglyMeasurable C (Filter.Eventually.of_forall hzb)
  have hz2I : Integrable (fun ω => ‖z ω‖ ^ 2) μ := Integrable.of_bound (mα := mΩ) (μ := μ)
    (hzm.norm.pow_const 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hzb ω) 2)
  have ha0I : Integrable a0 μ := Integrable.of_bound (mα := mΩ) (μ := μ) (ha0m.mono hm).aestronglyMeasurable
    (16 * l ^ 2) (Filter.Eventually.of_forall ha0b)
  have ha2zI : Integrable (fun ω => a2 ω * ‖z ω‖ ^ 2) μ := by
    have hh := hz2I.bdd_mul (ha2m.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall ha2const)
    simpa only [mul_comm] using hh
  have hzκI : Integrable (fun ω => z ω * κ ω) μ := by
    have hh := hzI.bdd_mul (hκm.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hκconst)
    simpa only [mul_comm] using hh
  have hreI : Integrable (fun ω => (z ω * κ ω).re) μ := hzκI.re
  have haffI : Integrable (fun ω => a0 ω + a2 ω * ‖z ω‖ ^ 2 + 2 * (z ω * κ ω).re) μ :=
    (ha0I.add ha2zI).add (hreI.const_mul 2)
  have hRsm : StronglyMeasurable[m] rEnv := stronglyMeasurable_const.mul
    (((stronglyMeasurable_const.mul hvsm.norm).div stronglyMeasurable_const).add stronglyMeasurable_const)
  have hRconst : ∀ ω, ‖rEnv ω‖ ≤ R * (l ^ 2 * 2 / Real.sqrt t + l ^ 3 / t) := fun ω => by
    have hnon : 0 ≤ rEnv ω := by dsimp [rEnv]; positivity
    rw [Real.norm_of_nonneg hnon]
    dsimp [rEnv]
    gcongr
    exact (hDb ω).2.2.1
  have hRI : Integrable rEnv μ := Integrable.of_bound (mα := mΩ) (μ := μ) (hRsm.mono hm).aestronglyMeasurable
    _ (Filter.Eventually.of_forall hRconst)
  have hce := condExp_affine_envelope hm hRsm hRI ha0m ha2m hκm ha0I ha2zI hzI hz2I hzκI hreI
    haffI hfI (Filter.Eventually.of_forall hrem) hmean hsecond
    (Filter.Eventually.of_forall ha2b) (Filter.Eventually.of_forall hκb)
  filter_upwards [hce] with ω hce hω
  have hunit : E.indicator (fun _ => (1 : ℝ)) ω = 1 := Set.indicator_of_mem hω _
  rw [hunit, mul_one] at hce
  have hbase : |a0 ω + a2 ω| ≤ 4 * l * ‖(D ω).v‖ ^ 2 + 16 * V * l ^ 2 * ε := by
    obtain ⟨hm0, hm4, _, hs4, _, hvn0, hvn2⟩ := hDb ω
    have hsq : ‖(D ω).s‖ ^ 2 ≤ 16 * l ^ 2 := by nlinarith [norm_nonneg (D ω).s]
    have hdev' : |1 - (D ω).vn| ≤ V * ε := by rw [abs_sub_comm]; exact hdev ω hω
    have h1 := mul_le_mul_of_nonneg_right hm4 (sq_nonneg ‖(D ω).v‖)
    have h2 := mul_le_mul hsq hdev' (abs_nonneg _) (show 0 ≤ 16 * l ^ 2 by positivity)
    have he : a0 ω + a2 ω = ‖(D ω).v‖ ^ 2 * (D ω).m + (1 - (D ω).vn) * ‖(D ω).s‖ ^ 2 := by
      dsimp [a0, a2, RowData.a0, RowData.a2]
      ring
    rw [he]
    calc
      _ ≤ |‖(D ω).v‖ ^ 2 * (D ω).m| + |(1 - (D ω).vn) * ‖(D ω).s‖ ^ 2| := abs_add_le _ _
      _ = ‖(D ω).v‖ ^ 2 * (D ω).m + |1 - (D ω).vn| * ‖(D ω).s‖ ^ 2 := by
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hm0), abs_mul, abs_of_nonneg (sq_nonneg (‖(D ω).s‖ : ℝ))]
      _ ≤ _ := by nlinarith
  apply row_bias_arithmetic ht hl hc hR hV hM hK ha (norm_nonneg _) hs haε hsε
  have htriangle : |μ[f | m] ω| ≤ |μ[f | m] ω - (a0 ω + a2 ω)| + |a0 ω + a2 ω| := by
    calc
      _ = |(μ[f | m] ω - (a0 ω + a2 ω)) + (a0 ω + a2 ω)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  dsimp [rEnv, aEnv, kEnv] at hce
  linarith only [htriangle, hce, hbase]

end AndersonAC.AgentS6Row
