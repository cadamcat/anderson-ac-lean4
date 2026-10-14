import AndersonAC.AgentS6Row.Algebra

open MeasureTheory

namespace AndersonAC.AgentS6Row

open ComplexConjugate

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {m : MeasurableSpace Ω}

/-- Pull a predictable affine function of `c` and `‖c‖²` through conditional expectation.
The final estimate only uses conditional moment bounds and a uniform remainder. -/
theorem condExp_affine_bound
    (hm : m ≤ mΩ)
    {a₀ a₂ unit : Ω → ℝ} {c κ : Ω → ℂ} {f : Ω → ℝ}
    {R B₁ B₂ A₂ Kκ : ℝ}
    (ha₀m : StronglyMeasurable[m] a₀) (ha₂m : StronglyMeasurable[m] a₂)
    (hκm : StronglyMeasurable[m] κ)
    (ha₀I : Integrable a₀ μ) (ha₂sI : Integrable (fun ω => a₂ ω * ‖c ω‖ ^ 2) μ)
    (hcI : Integrable c μ) (hc₂I : Integrable (fun ω => ‖c ω‖ ^ 2) μ)
    (hcκI : Integrable (fun ω => c ω * κ ω) μ)
    (hrealI : Integrable (fun ω => (c ω * κ ω).re) μ)
    (haffI : Integrable (fun ω => a₀ ω + a₂ ω * ‖c ω‖ ^ 2 + 2 * (c ω * κ ω).re) μ)
    (hfI : Integrable f μ)
    (hrem : ∀ᵐ ω ∂μ,
      |f ω - (a₀ ω + a₂ ω * ‖c ω‖ ^ 2 + 2 * (c ω * κ ω).re)| ≤ R)
    (hmean : ∀ᵐ ω ∂μ, ‖μ[c | m] ω‖ ≤ B₁)
    (hsecond : ∀ᵐ ω ∂μ, |μ[(fun ω => ‖c ω‖ ^ 2) | m] ω - unit ω| ≤ B₂)
    (ha₂b : ∀ᵐ ω ∂μ, |a₂ ω| ≤ A₂) (hκb : ∀ᵐ ω ∂μ, ‖κ ω‖ ≤ Kκ) :
    ∀ᵐ ω ∂μ,
      |μ[f | m] ω - (a₀ ω + a₂ ω * unit ω)| ≤ R + A₂ * B₂ + 2 * B₁ * Kκ := by
  let s : Ω → ℝ := fun ω => ‖c ω‖ ^ 2
  let p : Ω → ℂ := fun ω => c ω * κ ω
  let g : Ω → ℝ := fun ω => a₀ ω + a₂ ω * s ω + 2 * (p ω).re
  have ha₂sI' : Integrable (a₂ * s) μ := by
    change Integrable (fun ω => a₂ ω * ‖c ω‖ ^ 2) μ
    exact ha₂sI
  have hmul₂ : μ[(fun ω => a₂ ω * s ω) | m] =ᵐ[μ] a₂ * μ[s | m] :=
    condExp_mul_of_stronglyMeasurable_left ha₂m
      ha₂sI' (by simpa [s] using hc₂I)
  have hmul : μ[p | m] =ᵐ[μ] μ[c | m] * κ := by
    have h := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
      hκm (by simpa [mul_comm] using hcκI) hcI
    have h₀ : μ[(fun ω => κ ω * c ω) | m] =ᵐ[μ] κ * μ[c | m] := by
      change μ[(fun ω => κ ω * c ω) | m] =ᵐ[μ] κ * μ[c | m] at h
      exact h
    have hp : (fun ω => c ω * κ ω) =ᵐ[μ] fun ω => κ ω * c ω :=
      Filter.Eventually.of_forall fun ω => mul_comm (c ω) (κ ω)
    filter_upwards [condExp_congr_ae hp, h₀] with ω h₁ h₂
    calc
      μ[p | m] ω = μ[(fun ω => κ ω * c ω) | m] ω := h₁
      _ = κ ω * μ[c | m] ω := h₂
      _ = μ[c | m] ω * κ ω := by ring
  have hre : μ[(fun ω => (p ω).re) | m] =ᵐ[μ] fun ω => (μ[p | m] ω).re := by
    have h := (Complex.reCLM.comp_condExp_comm (μ := μ) (m := m) hcκI).symm
    change μ[(fun ω => (c ω * κ ω).re) | m] =ᵐ[μ]
      fun ω => (μ[(fun ω => c ω * κ ω) | m] ω).re at h
    simpa only [p] using h
  have hscale : μ[(fun ω => 2 * (p ω).re) | m] =ᵐ[μ]
      fun ω => 2 * (μ[p | m] ω).re := by
    have hsmul := condExp_smul (μ := μ) (m₀ := mΩ)
      (2 : ℝ) (fun ω => (p ω).re) m
    have hfun : (fun ω => 2 * (p ω).re) = (2 : ℝ) • (fun ω => (p ω).re) := by
      funext ω; simp [smul_eq_mul]
    have hsmul' : μ[(fun ω => 2 * (p ω).re) | m] =ᵐ[μ]
        (2 : ℝ) • μ[(fun ω => (p ω).re) | m] :=
      (condExp_congr_ae (Filter.Eventually.of_forall fun ω => congrFun hfun ω)).trans hsmul
    filter_upwards [hsmul', hre] with ω h₁ h₂
    simp only [Pi.smul_apply, smul_eq_mul] at h₁
    rw [h₂] at h₁
    exact h₁
  have hconst : μ[a₀ | m] =ᵐ[μ] a₀ := by
    exact Filter.Eventually.of_forall fun ω =>
      congrFun (condExp_of_stronglyMeasurable (μ := μ)
        (m₀ := mΩ) hm ha₀m ha₀I) ω
  have hlin₁ : μ[(fun ω => a₀ ω + a₂ ω * s ω) | m] =ᵐ[μ]
      μ[a₀ | m] + μ[(fun ω => a₂ ω * s ω) | m] :=
    condExp_add ha₀I (by simpa [s] using ha₂sI) m
  have hlin₂ : μ[g | m] =ᵐ[μ]
      μ[(fun ω => a₀ ω + a₂ ω * s ω) | m] + μ[(fun ω => 2 * (p ω).re) | m] :=
    condExp_add (ha₀I.add (by simpa [s] using ha₂sI)) (hrealI.const_mul 2) m
  have hlin : μ[g | m] =ᵐ[μ]
      fun ω => a₀ ω + a₂ ω * μ[s | m] ω + 2 * (μ[p | m] ω).re := by
    filter_upwards [hlin₁, hlin₂, hconst, hmul₂, hscale] with ω h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₁ h₂
    simp only [Pi.mul_apply] at h₄
    calc
      μ[g | m] ω = μ[(fun ω => a₀ ω + a₂ ω * s ω) | m] ω +
          μ[(fun ω => 2 * (p ω).re) | m] ω := h₂
      _ = (μ[a₀ | m] ω + μ[(fun ω => a₂ ω * s ω) | m] ω) +
          2 * (μ[p | m] ω).re := by rw [h₁, h₅]
      _ = a₀ ω + a₂ ω * μ[s | m] ω + 2 * (μ[p | m] ω).re := by rw [h₃, h₄]
  have hdiff : μ[(fun ω => f ω - g ω) | m] =ᵐ[μ] μ[f | m] - μ[g | m] :=
    condExp_sub hfI (by simpa [g, s, p] using haffI) m
  have hremCE : ∀ᵐ ω ∂μ, |μ[(fun ω => f ω - g ω) | m] ω| ≤ R := by
    apply ae_bdd_abs_condExp_of_ae_bdd_abs
    simpa [g, s, p] using hrem
  filter_upwards [hremCE, hdiff, hlin, hmean, hsecond, ha₂b, hκb, hmul] with ω hR hD hL hM hS hA hK hmulω
  have hD' : μ[(fun ω => f ω - g ω) | m] ω = μ[f | m] ω - μ[g | m] ω := by
    simpa only [Pi.sub_apply] using hD
  have h1 : |μ[f | m] ω - μ[g | m] ω| ≤ R := by rw [← hD']; exact hR
  have hB₁ : 0 ≤ B₁ := (norm_nonneg (μ[c | m] ω)).trans hM
  have hKκ : 0 ≤ Kκ := (norm_nonneg (κ ω)).trans hK
  have hA₂ : 0 ≤ A₂ := (abs_nonneg (a₂ ω)).trans hA
  have hB₂ : 0 ≤ B₂ := (abs_nonneg (μ[s | m] ω - unit ω)).trans hS
  have hProd : ‖μ[c | m] ω * κ ω‖ ≤ B₁ * Kκ := by
    rw [norm_mul]
    exact mul_le_mul hM hK (norm_nonneg (κ ω)) hB₁
  have h2 : |μ[g | m] ω - (a₀ ω + a₂ ω * unit ω)| ≤ A₂ * B₂ + 2 * B₁ * Kκ := by
    have ha : |a₂ ω * (μ[s | m] ω - unit ω)| ≤ A₂ * B₂ := by
      rw [abs_mul]
      exact mul_le_mul hA hS (abs_nonneg _) hA₂
    have hp : |2 * (μ[c | m] ω * κ ω).re| ≤ 2 * B₁ * Kκ := by
      calc
        |2 * (μ[c | m] ω * κ ω).re| ≤ 2 * ‖μ[c | m] ω * κ ω‖ := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
        _ ≤ 2 * B₁ * Kκ := by
          calc
            2 * ‖μ[c | m] ω * κ ω‖ ≤ 2 * (B₁ * Kκ) := mul_le_mul_of_nonneg_left hProd (by norm_num)
            _ = 2 * B₁ * Kκ := by ring
    have heq : μ[g | m] ω - (a₀ ω + a₂ ω * unit ω) =
        a₂ ω * (μ[s | m] ω - unit ω) + 2 * (μ[c | m] ω * κ ω).re := by
      rw [hL, hmulω]
      simp only [Pi.mul_apply]
      ring
    rw [heq]
    calc
      |a₂ ω * (μ[s | m] ω - unit ω) + 2 * (μ[c | m] ω * κ ω).re|
          ≤ |a₂ ω * (μ[s | m] ω - unit ω)| + |2 * (μ[c | m] ω * κ ω).re| := abs_add_le _ _
      _ ≤ A₂ * B₂ + 2 * B₁ * Kκ := add_le_add ha hp
  calc
    |μ[f | m] ω - (a₀ ω + a₂ ω * unit ω)|
        ≤ |μ[f | m] ω - μ[g | m] ω| + |μ[g | m] ω - (a₀ ω + a₂ ω * unit ω)| := by
          calc
            _ = |(μ[f | m] ω - μ[g | m] ω) + (μ[g | m] ω - (a₀ ω + a₂ ω * unit ω))| := by congr 1 <;> ring
            _ ≤ _ := abs_add_le _ _
    _ ≤ R + A₂ * B₂ + 2 * B₁ * Kκ := by linarith


/-- The same affine conditional estimate with a predictable remainder envelope. -/
theorem condExp_affine_envelope
    (hm : m ≤ mΩ)
    {a₀ a₂ unit : Ω → ℝ} {c κ : Ω → ℂ} {f : Ω → ℝ}
    {B₁ B₂ : ℝ} {R A₂ Kκ : Ω → ℝ}
    (hRm : StronglyMeasurable[m] R) (hRI : Integrable R μ)
    (ha₀m : StronglyMeasurable[m] a₀) (ha₂m : StronglyMeasurable[m] a₂)
    (hκm : StronglyMeasurable[m] κ)
    (ha₀I : Integrable a₀ μ) (ha₂sI : Integrable (fun ω => a₂ ω * ‖c ω‖ ^ 2) μ)
    (hcI : Integrable c μ) (hc₂I : Integrable (fun ω => ‖c ω‖ ^ 2) μ)
    (hcκI : Integrable (fun ω => c ω * κ ω) μ)
    (hrealI : Integrable (fun ω => (c ω * κ ω).re) μ)
    (haffI : Integrable (fun ω => a₀ ω + a₂ ω * ‖c ω‖ ^ 2 + 2 * (c ω * κ ω).re) μ)
    (hfI : Integrable f μ)
    (hrem : ∀ᵐ ω ∂μ,
      |f ω - (a₀ ω + a₂ ω * ‖c ω‖ ^ 2 + 2 * (c ω * κ ω).re)| ≤ R ω)
    (hmean : ∀ᵐ ω ∂μ, ‖μ[c | m] ω‖ ≤ B₁)
    (hsecond : ∀ᵐ ω ∂μ, |μ[(fun ω => ‖c ω‖ ^ 2) | m] ω - unit ω| ≤ B₂)
    (ha₂b : ∀ᵐ ω ∂μ, |a₂ ω| ≤ A₂ ω) (hκb : ∀ᵐ ω ∂μ, ‖κ ω‖ ≤ Kκ ω) :
    ∀ᵐ ω ∂μ,
      |μ[f | m] ω - (a₀ ω + a₂ ω * unit ω)| ≤ R ω + A₂ ω * B₂ + 2 * B₁ * Kκ ω := by
  let s : Ω → ℝ := fun ω => ‖c ω‖ ^ 2
  let p : Ω → ℂ := fun ω => c ω * κ ω
  let g : Ω → ℝ := fun ω => a₀ ω + a₂ ω * s ω + 2 * (p ω).re
  have ha₂sI' : Integrable (a₂ * s) μ := by
    change Integrable (fun ω => a₂ ω * ‖c ω‖ ^ 2) μ
    exact ha₂sI
  have hmul₂ : μ[(fun ω => a₂ ω * s ω) | m] =ᵐ[μ] a₂ * μ[s | m] :=
    condExp_mul_of_stronglyMeasurable_left ha₂m
      ha₂sI' (by simpa [s] using hc₂I)
  have hmul : μ[p | m] =ᵐ[μ] μ[c | m] * κ := by
    have h := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
      hκm (by simpa [mul_comm] using hcκI) hcI
    have h₀ : μ[(fun ω => κ ω * c ω) | m] =ᵐ[μ] κ * μ[c | m] := by
      change μ[(fun ω => κ ω * c ω) | m] =ᵐ[μ] κ * μ[c | m] at h
      exact h
    have hp : (fun ω => c ω * κ ω) =ᵐ[μ] fun ω => κ ω * c ω :=
      Filter.Eventually.of_forall fun ω => mul_comm (c ω) (κ ω)
    filter_upwards [condExp_congr_ae hp, h₀] with ω h₁ h₂
    calc
      μ[p | m] ω = μ[(fun ω => κ ω * c ω) | m] ω := h₁
      _ = κ ω * μ[c | m] ω := h₂
      _ = μ[c | m] ω * κ ω := by ring
  have hre : μ[(fun ω => (p ω).re) | m] =ᵐ[μ] fun ω => (μ[p | m] ω).re := by
    have h := (Complex.reCLM.comp_condExp_comm (μ := μ) (m := m) hcκI).symm
    change μ[(fun ω => (c ω * κ ω).re) | m] =ᵐ[μ]
      fun ω => (μ[(fun ω => c ω * κ ω) | m] ω).re at h
    simpa only [p] using h
  have hscale : μ[(fun ω => 2 * (p ω).re) | m] =ᵐ[μ]
      fun ω => 2 * (μ[p | m] ω).re := by
    have hsmul := condExp_smul (μ := μ) (m₀ := mΩ)
      (2 : ℝ) (fun ω => (p ω).re) m
    have hfun : (fun ω => 2 * (p ω).re) = (2 : ℝ) • (fun ω => (p ω).re) := by
      funext ω; simp [smul_eq_mul]
    have hsmul' : μ[(fun ω => 2 * (p ω).re) | m] =ᵐ[μ]
        (2 : ℝ) • μ[(fun ω => (p ω).re) | m] :=
      (condExp_congr_ae (Filter.Eventually.of_forall fun ω => congrFun hfun ω)).trans hsmul
    filter_upwards [hsmul', hre] with ω h₁ h₂
    simp only [Pi.smul_apply, smul_eq_mul] at h₁
    rw [h₂] at h₁
    exact h₁
  have hconst : μ[a₀ | m] =ᵐ[μ] a₀ := by
    exact Filter.Eventually.of_forall fun ω =>
      congrFun (condExp_of_stronglyMeasurable (μ := μ)
        (m₀ := mΩ) hm ha₀m ha₀I) ω
  have hlin₁ : μ[(fun ω => a₀ ω + a₂ ω * s ω) | m] =ᵐ[μ]
      μ[a₀ | m] + μ[(fun ω => a₂ ω * s ω) | m] :=
    condExp_add ha₀I (by simpa [s] using ha₂sI) m
  have hlin₂ : μ[g | m] =ᵐ[μ]
      μ[(fun ω => a₀ ω + a₂ ω * s ω) | m] + μ[(fun ω => 2 * (p ω).re) | m] :=
    condExp_add (ha₀I.add (by simpa [s] using ha₂sI)) (hrealI.const_mul 2) m
  have hlin : μ[g | m] =ᵐ[μ]
      fun ω => a₀ ω + a₂ ω * μ[s | m] ω + 2 * (μ[p | m] ω).re := by
    filter_upwards [hlin₁, hlin₂, hconst, hmul₂, hscale] with ω h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₁ h₂
    simp only [Pi.mul_apply] at h₄
    calc
      μ[g | m] ω = μ[(fun ω => a₀ ω + a₂ ω * s ω) | m] ω +
          μ[(fun ω => 2 * (p ω).re) | m] ω := h₂
      _ = (μ[a₀ | m] ω + μ[(fun ω => a₂ ω * s ω) | m] ω) +
          2 * (μ[p | m] ω).re := by rw [h₁, h₅]
      _ = a₀ ω + a₂ ω * μ[s | m] ω + 2 * (μ[p | m] ω).re := by rw [h₃, h₄]
  have hdiff : μ[(fun ω => f ω - g ω) | m] =ᵐ[μ] μ[f | m] - μ[g | m] :=
    condExp_sub hfI (by simpa [g, s, p] using haffI) m
  have hremCE : ∀ᵐ ω ∂μ, |μ[(fun ω => f ω - g ω) | m] ω| ≤ R ω := by
    have hi : Integrable (fun ω => f ω - g ω) μ := hfI.sub (by simpa [g, s, p] using haffI)
    have hnorm := norm_condExp_le (m := m) (μ := μ) (fun ω => f ω - g ω)
    have hdom := condExp_mono (m := m) hi.norm hRI (by
      filter_upwards [hrem] with ω hω
      simpa only [Real.norm_eq_abs, g, s, p] using hω)
    rw [condExp_of_stronglyMeasurable hm hRm hRI] at hdom
    filter_upwards [hnorm, hdom] with ω hn hd
    have hn' : |μ[(fun ω => f ω - g ω) | m] ω| ≤
        μ[(fun ω => ‖f ω - g ω‖) | m] ω := by
      simpa only [Real.norm_eq_abs] using hn
    exact hn'.trans hd
  filter_upwards [hremCE, hdiff, hlin, hmean, hsecond, ha₂b, hκb, hmul] with ω hR hD hL hM hS hA hK hmulω
  have hD' : μ[(fun ω => f ω - g ω) | m] ω = μ[f | m] ω - μ[g | m] ω := by
    simpa only [Pi.sub_apply] using hD
  have h1 : |μ[f | m] ω - μ[g | m] ω| ≤ (R ω) := by rw [← hD']; exact hR
  have hB₁ : 0 ≤ B₁ := (norm_nonneg (μ[c | m] ω)).trans hM
  have hKκ : 0 ≤ (Kκ ω) := (norm_nonneg (κ ω)).trans hK
  have hA₂ : 0 ≤ (A₂ ω) := (abs_nonneg (a₂ ω)).trans hA
  have hB₂ : 0 ≤ B₂ := (abs_nonneg (μ[s | m] ω - unit ω)).trans hS
  have hProd : ‖μ[c | m] ω * κ ω‖ ≤ B₁ * (Kκ ω) := by
    rw [norm_mul]
    exact mul_le_mul hM hK (norm_nonneg (κ ω)) hB₁
  have h2 : |μ[g | m] ω - (a₀ ω + a₂ ω * unit ω)| ≤ (A₂ ω) * B₂ + 2 * B₁ * (Kκ ω) := by
    have ha : |a₂ ω * (μ[s | m] ω - unit ω)| ≤ (A₂ ω) * B₂ := by
      rw [abs_mul]
      exact mul_le_mul hA hS (abs_nonneg _) hA₂
    have hp : |2 * (μ[c | m] ω * κ ω).re| ≤ 2 * B₁ * (Kκ ω) := by
      calc
        |2 * (μ[c | m] ω * κ ω).re| ≤ 2 * ‖μ[c | m] ω * κ ω‖ := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
        _ ≤ 2 * B₁ * (Kκ ω) := by
          calc
            2 * ‖μ[c | m] ω * κ ω‖ ≤ 2 * (B₁ * (Kκ ω)) := mul_le_mul_of_nonneg_left hProd (by norm_num)
            _ = 2 * B₁ * (Kκ ω) := by ring
    have heq : μ[g | m] ω - (a₀ ω + a₂ ω * unit ω) =
        a₂ ω * (μ[s | m] ω - unit ω) + 2 * (μ[c | m] ω * κ ω).re := by
      rw [hL, hmulω]
      simp only [Pi.mul_apply]
      ring
    rw [heq]
    calc
      |a₂ ω * (μ[s | m] ω - unit ω) + 2 * (μ[c | m] ω * κ ω).re|
          ≤ |a₂ ω * (μ[s | m] ω - unit ω)| + |2 * (μ[c | m] ω * κ ω).re| := abs_add_le _ _
      _ ≤ (A₂ ω) * B₂ + 2 * B₁ * (Kκ ω) := add_le_add ha hp
  calc
    |μ[f | m] ω - (a₀ ω + a₂ ω * unit ω)|
        ≤ |μ[f | m] ω - μ[g | m] ω| + |μ[g | m] ω - (a₀ ω + a₂ ω * unit ω)| := by
          calc
            _ = |(μ[f | m] ω - μ[g | m] ω) + (μ[g | m] ω - (a₀ ω + a₂ ω * unit ω))| := by congr 1 <;> ring
            _ ≤ _ := abs_add_le _ _
    _ ≤ (R ω) + (A₂ ω) * B₂ + 2 * B₁ * (Kκ ω) := by linarith


lemma condExp_supported {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (hm : m ≤ mΩ) (E : Set Ω) (hE : MeasurableSet[m] E)
    (f : Ω → V) (hf : Integrable f μ) (hsupport : ∀ ω, ω ∉ E → f ω = 0) :
    ∀ᵐ ω ∂μ, ω ∉ E → μ[f | m] ω = 0 := by
  have he : E.indicator f = f := by
    funext ω
    by_cases hω : ω ∈ E
    · exact Set.indicator_of_mem hω f
    · rw [Set.indicator_of_notMem hω, hsupport ω hω]
  have hc := condExp_indicator (m := m) hf hE
  rw [he] at hc
  filter_upwards [hc] with ω hc hω
  rw [hc, Set.indicator_of_notMem hω]

end AndersonAC.AgentS6Row
