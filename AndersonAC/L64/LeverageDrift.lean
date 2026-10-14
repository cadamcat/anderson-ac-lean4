import AndersonAC.L64.Inputs
import AndersonAC.L64.Arith

/-!
# Lemma 6.4 (conditional leverage drift), `06-clearing.tex` l.391–423

We assemble the abstract drift `NHeat.drift`, the concrete inputs (`Inputs.lean`), the moments of
the heat coefficient (`Residual.lean`) and the bookkeeping (`Arith.lean`).

* `drift_of_small`: explicit form, in terms of one small parameter `u`;
* `leverage_drift`: the statement of the paper, uniform over prestates as `t ↓ 0`.
-/

open Matrix Finset ComplexConjugate Complex MeasureTheory

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the constant `K₁` in `|𝔼 c_x - √t(g_xx - r_x)| ≤ K₁ t`. -/
noncomputable def K1c (C : ℝ) : ℝ := C ^ 2 + C ^ 3 + 16 * C ^ 5
/-- the constant `K₂` in `|𝔼|c_x|² - 1| ≤ K₂ √t`. -/
noncomputable def K2c (C : ℝ) : ℝ := C + C ^ 2 + 96 * C ^ 4

section Explicit

variable {M : Matrix ι ι ℝ} {t : ℝ} {r : ι → ℂ} {B : Finset ι} {x : ι} {τ : ℝ} {C c : ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Ω → ℝ} {η : ℝ}

set_option maxHeartbeats 1000000 in
/-- **Lemma 6.4, explicit form.** All error terms are bounded by `u` times constants depending
only on `C, c`, under explicit size conditions on `u`. -/
theorem drift_of_small (hM : M.IsSymm) (hs : Small t C) (hc0 : 0 < c)
    (hp : ∀ i, c ≤ (r i).im ∧ (r i).im ≤ C)
    (hgr : ‖(damped M t r)⁻¹ x x‖ + ‖r x‖ ≤ C)
    {Hs : ℝ} (hfour : ∑ j, ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x j‖ ^ 4 ≤ Hs)
    (hx : x ∉ B) (hτ : 0 < τ)
    (hmax : ∀ i ∈ Bᶜ, preLev M t r B τ i ≤ preLev M t r B τ x)
    (hm0 : 0 < preLev M t r B τ x)
    (hξm : Measurable ξ) (hm1 : ∫ ω, ξ ω ∂μ = 0) (hm2 : ∫ ω, ξ ω ^ 2 ∂μ = t - η)
    (hξb : ∀ᵐ ω ∂μ, |ξ ω| ≤ C * √t) (hη0 : 0 ≤ η) (hη1 : η ≤ C * t ^ 2)
    {u θ : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (huC : 3 * (C / c) * u ≤ 1) (huK2 : K2c C * u ≤ 1)
    (huΦ : u ^ 2 * KPhi C c ≤ 1 / 16)
    (hΛ : ‖(damped M t r)⁻¹ x x - r x‖ ≤ C * θ) (hθu : θ ≤ u) (hsθ : √t ≤ θ)
    (hF5 : √t * θ ≤ u * √(preLev M t r B τ x))
    (hF3 : (B.card + 1) * √Hs ≤ 2 * u)
    (hF4 : preLev M t r B τ x ≤ 4 * u ^ 2 * t)
    (hF6 : B.card * Hs ≤ u ^ 2 * preLev M t r B τ x)
    (hF7 : Hs ≤ u ^ 2) :
    Integrable (fun ω => postA M t r B x τ (ξ ω) - preA M t r B τ) μ ∧
    Integrable (fun ω => postP M t r B x τ (ξ ω) - preP M t r B τ) μ ∧
    |∫ ω, (postA M t r B x τ (ξ ω) - preA M t r B τ) ∂μ|
      ≤ KA C c (C + K1c C) (K2c C) * u * preLev M t r B τ x ∧
    ∫ ω, (postP M t r B x τ (ξ ω) - preP M t r B τ) ∂μ
      ≤ -preLev M t r B τ x ^ 2 + KP C c (C + K1c C) (K2c C) * u * preLev M t r B τ x ^ 2 := by
  have hC := hs.C_nonneg
  have ht := hs.pos
  have hp' : ∀ i, 0 < (r i).im := fun i => hc0.trans_le (hp i).1
  have hρ : ‖r x‖ ≤ C := le_trans (le_add_of_nonneg_left (norm_nonneg _)) hgr
  have hγ : ‖(damped M t r)⁻¹ x x‖ ≤ C := le_trans (le_add_of_nonneg_right (norm_nonneg _)) hgr
  set m := preLev M t r B τ x with hm_def
  -- the normalizer and the normalized heat
  obtain ⟨L, hL⟩ := exists_normalizer (scat t (pim r) (damped M t r)⁻¹) B τ Bᶜ hτ
  set H := theHeat M t r B x L with hH
  have hBes : H.Bessel := nheat_bessel (heatVec M t r x) hτ hL hx
  have hHm : H.m = m := nheat_m _ hτ hL
  have hHlev : ∀ i, H.lev i = preLev M t r B τ i := nheat_lev _ hτ hL
  have hHA : H.A = preA M t r B τ := nheat_A _ hτ hL hx
  have hHP : H.P = preP M t r B τ := nheat_P _ hτ hL hx
  have hmax' : ∀ i ∈ H.S, H.lev i ≤ H.m := fun i hi => by
    rw [hHlev, hHm]; exact hmax i (mem_of_mem_erase hi)
  -- the heat coefficient
  set γ := (damped M t r)⁻¹ x x with hγ_def
  set cω : Ω → ℂ := fun ω => hc t (r x) γ (ξ ω) with hcω
  have hcm : Measurable cω := measurable_hc hξm
  obtain ⟨hcb, hEc, hEc2⟩ := heat_moments (μ := μ) hξm hs hρ hγ hξb η hm1 hm2 hη0 hη1
  -- pathwise identification of the poststate
  have hD := isUnit_det_damped M t r hM ht hp'
  have hpost : ∀ᵐ ω ∂μ, H.A' (cω ω) = postA M t r B x τ (ξ ω)
      ∧ H.P' (cω ω) = postP M t r B x τ (ξ ω) := by
    filter_upwards [hξb] with ω hω
    have hne := one_add_ne_zero hs hρ hγ hω
    have hC' : ∀ i ∈ Bᶜ.erase x,
        crossRow (scat t (pim r) (dampedPost M t r x (ξ ω))⁻¹) B i
          = crossRow (scat t (pim r) (damped M t r)⁻¹) B i
            + (cω ω * heatVec M t r x i) • crossRow (scat t (pim r) (damped M t r)⁻¹) B x :=
      fun i hi => post_crossRow ht hp' hD hx (ξ ω) hne hi
    exact ⟨nheat_A' (heatVec M t r x) hτ hL _ _ hC' hx, nheat_P' (heatVec M t r x) hτ hL _ _ hC' hx⟩
  -- the sizes
  set Ec := ∫ ω, cω ω ∂μ
  set Ec2 := ∫ ω, ‖cω ω‖ ^ 2 ∂μ
  have hsqt := Real.sqrt_pos.mpr ht
  have hsqm := Real.sqrt_pos.mpr hm0
  have hwm : √m ^ 2 = m := Real.sq_sqrt hm0.le
  have hst : √t ^ 2 = t := Real.sq_sqrt ht.le
  have hθ0 : 0 ≤ θ := hsqt.le.trans hsθ
  have hHs0 : 0 ≤ Hs := le_trans (sum_nonneg fun _ _ => by positivity) hfour
  have hS : Sizes (√t) (√m) u C c (C + K1c C) (K2c C) H.vn Ec2 ‖Ec‖ (nsq H.b) (H.vw H.lev) H.v4 := by
    refine ⟨hsqt, hs.sqrt_le_one, hsqm, hu0, hu1, hc0, hC, by unfold K1c; positivity,
      by unfold K2c; positivity, ?_, ?_, huC, ?_, huK2, norm_nonneg _, ?_, ?_, nsq_nonneg _, ?_,
      H.v4_nonneg, ?_, H.vw_lev_nonneg, ?_⟩
    · -- `√m ≤ 2u√t`
      calc √m ≤ √(4 * u ^ 2 * t) := Real.sqrt_le_sqrt hF4
        _ = 2 * u * √t := by
          rw [show 4 * u ^ 2 * t = (2 * u) ^ 2 * t by ring, Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq (by linarith)]
    · -- `|‖v‖² - 1| ≤ 3 (C/c) u`
      have h1 := theHeat_vn_bound hM ht hc0 hp hx hτ hL hfour
      have hCc : 0 ≤ C / c := div_nonneg hC hc0.le
      have h2 : ‖(damped M t r)⁻¹ x x - r x‖ / c ≤ C / c * u := by
        rw [div_le_iff₀ hc0]
        calc ‖(damped M t r)⁻¹ x x - r x‖ ≤ C * θ := hΛ
          _ ≤ C * u := mul_le_mul_of_nonneg_left hθu hC
          _ = C / c * u * c := by field_simp
      have h3 : (B.card + 1) * (C / c * √Hs) ≤ C / c * (2 * u) := by
        calc (B.card + 1) * (C / c * √Hs) = C / c * ((B.card + 1) * √Hs) := by ring
          _ ≤ C / c * (2 * u) := mul_le_mul_of_nonneg_left hF3 hCc
      calc |H.vn - 1| ≤ _ := h1
        _ ≤ C / c * u + C / c * (2 * u) := add_le_add h2 h3
        _ = 3 * (C / c) * u := by ring
    · -- `|𝔼|c|² - 1| ≤ K₂ u`
      calc |Ec2 - 1| ≤ (C + C ^ 2 + 96 * C ^ 4) * √t := hEc2
        _ ≤ K2c C * u := by
          unfold K2c
          exact mul_le_mul_of_nonneg_left (hsθ.trans hθu) (by positivity)
    · -- `‖𝔼c‖ ≤ (C + K₁) u √t`
      have h1 : ‖Ec‖ ≤ (C + K1c C) * √t * θ := by
        have e1 : ‖((√t : ℝ) : ℂ) * (γ - r x)‖ ≤ √t * (C * θ) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hsqt.le]
          exact mul_le_mul_of_nonneg_left hΛ hsqt.le
        have e2 : (C ^ 2 + C ^ 3 + 16 * C ^ 5) * t ≤ K1c C * (√t * θ) := by
          unfold K1c
          have : t ≤ √t * θ := by
            calc t = √t * √t := (Real.mul_self_sqrt ht.le).symm
              _ ≤ √t * θ := mul_le_mul_of_nonneg_left hsθ hsqt.le
          exact mul_le_mul_of_nonneg_left this (by positivity)
        have := norm_sub_norm_le Ec (((√t : ℝ) : ℂ) * (γ - r x))
        calc ‖Ec‖ ≤ ‖Ec - ((√t : ℝ) : ℂ) * (γ - r x)‖ + ‖((√t : ℝ) : ℂ) * (γ - r x)‖ := by linarith
          _ ≤ K1c C * (√t * θ) + √t * (C * θ) := add_le_add (hEc.trans e2) e1
          _ = (C + K1c C) * √t * θ := by ring
      have hK : 0 ≤ C + K1c C := by unfold K1c; positivity
      calc ‖Ec‖ ≤ (C + K1c C) * √t * θ := h1
        _ ≤ (C + K1c C) * √t * u := mul_le_mul_of_nonneg_left hθu (by positivity)
        _ = (C + K1c C) * u * √t := by ring
    · -- `‖𝔼c‖ ≤ (C + K₁) u √m`
      have hK : 0 ≤ C + K1c C := by unfold K1c; positivity
      have h1 : ‖Ec‖ ≤ (C + K1c C) * (√t * θ) := by
        have e1 : ‖((√t : ℝ) : ℂ) * (γ - r x)‖ ≤ √t * (C * θ) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hsqt.le]
          exact mul_le_mul_of_nonneg_left hΛ hsqt.le
        have e2 : (C ^ 2 + C ^ 3 + 16 * C ^ 5) * t ≤ K1c C * (√t * θ) := by
          unfold K1c
          have : t ≤ √t * θ := by
            calc t = √t * √t := (Real.mul_self_sqrt ht.le).symm
              _ ≤ √t * θ := mul_le_mul_of_nonneg_left hsθ hsqt.le
          exact mul_le_mul_of_nonneg_left this (by positivity)
        have := norm_sub_norm_le Ec (((√t : ℝ) : ℂ) * (γ - r x))
        calc ‖Ec‖ ≤ ‖Ec - ((√t : ℝ) : ℂ) * (γ - r x)‖ + ‖((√t : ℝ) : ℂ) * (γ - r x)‖ := by linarith
          _ ≤ K1c C * (√t * θ) + √t * (C * θ) := add_le_add (hEc.trans e2) e1
          _ = (C + K1c C) * (√t * θ) := by ring
      calc ‖Ec‖ ≤ (C + K1c C) * (√t * θ) := h1
        _ ≤ (C + K1c C) * (u * √m) := mul_le_mul_of_nonneg_left hF5 hK
        _ = (C + K1c C) * u * √m := by ring
    · -- `‖b‖² ≤ m/(t c²)`
      have := theHeat_b_bound hM ht hc0 hp hx hτ hL
      rw [hHm] at this
      calc nsq H.b ≤ m / (t * c ^ 2) := this
        _ = √m ^ 2 / (√t ^ 2 * c ^ 2) := by rw [hwm, hst]
    · -- `∑|v|⁴ ≤ (C/c)² u²`
      calc H.v4 ≤ (C / c) ^ 2 * Hs := theHeat_v4_bound hM ht hc0 hp hx hτ hL hfour
        _ ≤ (C / c) ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_left hF7 (sq_nonneg _)
    · -- `∑ m_i |v_i|² ≤ (C/c) u m`
      have hsum2 : ∑ i ∈ H.S, H.lev i ^ 2 ≤ m * B.card := by
        have hA := hBes.A_le_card
        rw [Fintype.card_coe] at hA
        calc ∑ i ∈ H.S, H.lev i ^ 2 ≤ ∑ i ∈ H.S, m * H.lev i := sum_le_sum fun i hi => by
              rw [sq, ← hHm]; exact mul_le_mul_of_nonneg_right (hmax' i hi) (H.lev_nn i)
          _ = m * ∑ i ∈ H.S, H.lev i := by rw [mul_sum]
          _ ≤ m * B.card := by
              refine mul_le_mul_of_nonneg_left ?_ hm0.le
              have : ∑ i ∈ H.S, H.lev i ≤ H.A := by
                unfold NHeat.A; linarith [H.m_nn]
              linarith
      have hCS : H.vw H.lev ≤ √(∑ i ∈ H.S, H.lev i ^ 2) * √H.v4 := by
        have := sum_mul_le_sqrt H.S H.lev (fun i => ‖H.v i‖ ^ 2)
        unfold NHeat.vw NHeat.v4
        simpa [← pow_mul] using this
      have hv4 : √H.v4 ≤ C / c * √Hs := by
        have := theHeat_v4_bound hM ht hc0 hp hx hτ hL hfour
        calc √H.v4 ≤ √((C / c) ^ 2 * Hs) := Real.sqrt_le_sqrt this
          _ = C / c * √Hs := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hC hc0.le)]
      have hCc : 0 ≤ C / c := div_nonneg hC hc0.le
      have key : √(m * B.card) * √Hs ≤ u * m := by
        rw [← Real.sqrt_mul (by positivity)]
        calc √(m * B.card * Hs) ≤ √((u * m) ^ 2) := by
              apply Real.sqrt_le_sqrt
              calc m * B.card * Hs = m * (B.card * Hs) := by ring
                _ ≤ m * (u ^ 2 * m) := mul_le_mul_of_nonneg_left hF6 hm0.le
                _ = (u * m) ^ 2 := by ring
          _ = u * m := Real.sqrt_sq (by positivity)
      calc H.vw H.lev ≤ √(∑ i ∈ H.S, H.lev i ^ 2) * √H.v4 := hCS
        _ ≤ √(m * B.card) * (C / c * √Hs) :=
            mul_le_mul (Real.sqrt_le_sqrt hsum2) hv4 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = C / c * (√(m * B.card) * √Hs) := by ring
        _ ≤ C / c * (u * m) := mul_le_mul_of_nonneg_left key hCc
        _ = C / c * u * √m ^ 2 := by rw [hwm]; ring
  -- `Φ ≤ 1/4`
  have hm_eq : H.m = √m ^ 2 := by rw [hwm, hHm]
  have hm1' : √m ^ 2 ≤ 1 := by
    have hw1 := hS.w_le_one
    calc √m ^ 2 = √m * √m := by ring
      _ ≤ 1 * 1 := mul_le_mul hw1 hw1 hsqm.le zero_le_one
      _ = 1 := by ring
  have hΦ : H.Φ (4 * C) ≤ 1 / 4 := by
    have h1 := hS.Phi_le
    have e : H.Φ (4 * C) = 3 * (((4 * C) ^ 2 * H.vn + 1) ^ 2 * (√m ^ 2) ^ 2
        + 2 * (4 * C) ^ 2 * nsq H.b * √m ^ 2) := by
      unfold NHeat.Φ; rw [hm_eq]
    rw [e]
    have hk := KPhi_nonneg C c
    have : √m ^ 2 * (4 * u ^ 2) * KPhi C c ≤ 1 / 4 := by
      calc √m ^ 2 * (4 * u ^ 2) * KPhi C c = √m ^ 2 * (4 * (u ^ 2 * KPhi C c)) := by ring
        _ ≤ 1 * (4 * (1 / 16)) :=
            mul_le_mul hm1' (by linarith) (by positivity) zero_le_one
        _ = 1 / 4 := by norm_num
    exact h1.trans this
  -- apply the abstract drift
  obtain ⟨hAI, hPI, hA, hP⟩ := H.drift μ cω hcm (4 * C) hcb hBes hmax' hΦ
  have eA : ∫ ω, (postA M t r B x τ (ξ ω) - preA M t r B τ) ∂μ = ∫ ω, (H.A' (cω ω) - H.A) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hpost] with ω hω
    rw [hω.1, hHA]
  have eP : ∫ ω, (postP M t r B x τ (ξ ω) - preP M t r B τ) ∂μ = ∫ ω, (H.P' (cω ω) - H.P) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hpost] with ω hω
    rw [hω.2, hHP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hAI.congr ?_
    filter_upwards [hpost] with ω hω
    rw [hω.1, hHA]
  · refine hPI.congr ?_
    filter_upwards [hpost] with ω hω
    rw [hω.2, hHP]
  · rw [eA]
    have := total_bound hS (EA := ∫ ω, (H.A' (cω ω) - H.A) ∂μ) (by
      unfold NHeat.ρA NHeat.ω NHeat.Φ at hA
      rw [hm_eq] at hA
      exact hA)
    rwa [hwm] at this
  · rw [eP]
    have := square_bound hS (EP := ∫ ω, (H.P' (cω ω) - H.P) ∂μ) (by
      unfold NHeat.ρP NHeat.ω NHeat.Φ at hP
      rw [hm_eq] at hP
      exact hP)
    rwa [hwm] at this

end Explicit

section Asymptotic

/-- the exponent margin `κ > 0`. -/
noncomputable def κexp (δ ν e₀ βw : ℝ) : ℝ :=
  min (min (βw - e₀ / 2) ((δ - ν - e₀) / 2)) (min (e₀ / 2) ((1 + δ) / 2 - ν))

lemma rpow_le_of_le {t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (h : b ≤ a) : t ^ a ≤ t ^ b :=
  Real.rpow_le_rpow_of_exponent_ge ht ht1 h

lemma sqrt_rpow {t a : ℝ} (ht : 0 < t) : √(t ^ a) = t ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]; ring_nf

lemma rpow_sq {t a : ℝ} (ht : 0 < t) : (t ^ a) ^ 2 = t ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; push_cast; ring_nf

set_option maxHeartbeats 2000000 in
/-- **Lemma 6.4 (conditional leverage drift)**, `06-clearing.tex` l.391–423.

Fix constants `C, c > 0` and exponents with `0 ≤ ν < (1+δ)/2`, `0 < e₀ < δ - ν`,
`e₀/2 < βw < 1/2`; put `H_* = t^{1+δ}`, `r_* = t^{-ν}`, `l_* = t^{1+e₀}`. Then, uniformly over all
prestates as `t ↓ 0`: for every `ε > 0` there is `t₀ > 0` such that for `0 < t < t₀`, every finite
active set, real symmetric `M`, `r` with `p = Im r`, core `B` with `|B| ≤ r_*`, pivot `x ∉ B`,
ridge `τ > 0` and conditional law of the real residual `ξ` satisfying the displayed hypotheses,
`|𝔼(𝒜' - 𝒜)| ≤ ε m_*` and `𝔼(𝒫' - 𝒫) ≤ -(1 - ε) m_*²`.

Here `g = (M - t diag r)⁻¹`, `h = √t g`, `S = 1 + 2it D_p^{1/2} g D_p^{1/2}`, `𝒞 = S_{RB}` with
`R = Bᶜ`, `m_i = (𝒞(𝒞*𝒞 + τ)⁻¹𝒞*)_{ii}` (`preLev`), `m_* = m_x` (by `hmax`), and the primed
quantities are computed from the inverse of `M - t diag r + (ξ + t r_x) e_x e_xᵀ` on
`R' = R ∖ {x}` at the same `τ` (`postLev`). The probability space `(Ω, μ)` carries the conditional
law given the prestate. -/
theorem leverage_drift {C c δ ν e₀ βw : ℝ} (hc0 : 0 < c) (hν0 : 0 ≤ ν) (hν1 : ν < (1 + δ) / 2)
    (he0 : 0 < e₀) (he1 : e₀ < δ - ν) (hβ0 : e₀ / 2 < βw) (hβ1 : βw < 1 / 2) :
    ∀ ε > 0, ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (r : ι → ℂ) (B : Finset ι)
      (x : ι) (τ : ℝ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ξ : Ω → ℝ) (η : ℝ),
    M.IsSymm →
    (∀ i, ‖(damped M t r)⁻¹ i i‖ + ‖r i‖ ≤ C) →
    (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C) →
    (∀ i, ‖(damped M t r)⁻¹ i i - r i‖ ≤ C * t ^ βw) →
    (∀ i, ∑ j, ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ i j‖ ^ 4 ≤ t ^ (1 + δ)) →
    (B.card : ℝ) ≤ t ^ (-ν) → x ∉ B → 0 < τ →
    (∀ i ∈ Bᶜ, preLev M t r B τ i ≤ preLev M t r B τ x) →
    2 * t ^ (1 + e₀) ≤ preLev M t r B τ x → preLev M t r B τ x ≤ 4 * t ^ (1 + e₀) →
    Measurable ξ → ∫ ω, ξ ω ∂μ = 0 → ∫ ω, ξ ω ^ 2 ∂μ = t - η →
    (∀ᵐ ω ∂μ, |ξ ω| ≤ C * √t) → 0 ≤ η / t → η / t ≤ C * t →
    Integrable (fun ω => postA M t r B x τ (ξ ω) - preA M t r B τ) μ ∧
    Integrable (fun ω => postP M t r B x τ (ξ ω) - preP M t r B τ) μ ∧
    |∫ ω, (postA M t r B x τ (ξ ω) - preA M t r B τ) ∂μ| ≤ ε * preLev M t r B τ x ∧
    ∫ ω, (postP M t r B x τ (ξ ω) - preP M t r B τ) ∂μ ≤ -(1 - ε) * preLev M t r B τ x ^ 2 := by
  intro ε hε
  have hκ0 : 0 < κexp δ ν e₀ βw := by
    unfold κexp
    exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hκ1 : κexp δ ν e₀ βw ≤ βw - e₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hκ2 : κexp δ ν e₀ βw ≤ (δ - ν - e₀) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hκ3 : κexp δ ν e₀ βw ≤ e₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hκ4 : κexp δ ν e₀ βw ≤ (1 + δ) / 2 - ν := (min_le_right _ _).trans (min_le_right _ _)
  set κ := κexp δ ν e₀ βw
  set KA' := KA C c (C + K1c C) (K2c C)
  set KP' := KP C c (C + K1c C) (K2c C)
  set KΦ := KPhi C c
  set u₀ : ℝ := min (min (1 / 2) (1 / (3 * (|C| / c) + 1))) (min (min (1 / (|K2c C| + 1))
    (1 / (16 * |KΦ| + 1))) (min (ε / (|KA'| + 1)) (ε / (|KP'| + 1)))) with hu₀_def
  have hu₀ : 0 < u₀ := by
    have : 0 < 3 * (|C| / c) + 1 := by positivity
    refine lt_min (lt_min (by norm_num) (by positivity)) (lt_min (lt_min (by positivity)
      (by positivity)) (lt_min (by positivity) (by positivity)))
  refine ⟨min (1 / 2) (min ((1 / (4 * C ^ 2 + 1)) ^ 2) (u₀ ^ (1 / κ))), ?_, ?_⟩
  · refine lt_min (by norm_num) (lt_min (by positivity) (Real.rpow_pos_of_pos hu₀ _))
  intro t ht htt₀ ι _ _ M r B x τ Ω _ μ _ ξ η hM hgr hp hlag hfour hB hx hτ hmax hmlo hmhi
    hξm hm1 hm2 hξb hη0 hη1
  have ht1 : t ≤ 1 := by
    have := htt₀.le.trans (min_le_left _ _); linarith
  have hC : 0 ≤ C := hc0.le.trans ((hp x).1.trans (hp x).2)
  -- smallness of `t`
  have hsmall : Small t C := by
    refine ⟨ht, ht1, hC, ?_⟩
    have h1 : t ≤ (1 / (4 * C ^ 2 + 1)) ^ 2 :=
      htt₀.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : √t ≤ 1 / (4 * C ^ 2 + 1) := by
      calc √t ≤ √((1 / (4 * C ^ 2 + 1)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (4 * C ^ 2 + 1) := Real.sqrt_sq (by positivity)
    have h3 : 0 < 4 * C ^ 2 + 1 := by positivity
    rw [le_div_iff₀ h3] at h2
    have := Real.sqrt_nonneg t
    nlinarith
  -- the small parameter `u = t^κ`
  set u := t ^ κ with hu_def
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht _
  have huu₀ : u ≤ u₀ := by
    have h1 : t ≤ u₀ ^ (1 / κ) := htt₀.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc u = t ^ κ := rfl
      _ ≤ (u₀ ^ (1 / κ)) ^ κ := Real.rpow_le_rpow ht.le h1 hκ0.le
      _ = u₀ := by rw [one_div, Real.rpow_inv_rpow hu₀.le hκ0.ne']
  have hu1 : u ≤ 1 / 2 := huu₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle_inv : ∀ X : ℝ, 0 ≤ X → u ≤ 1 / (X + 1) → X * u ≤ 1 := by
    intro X hX h
    rw [le_div_iff₀ (by linarith)] at h
    nlinarith
  have hle_eps : ∀ X : ℝ, u ≤ ε / (|X| + 1) → X * u ≤ ε := by
    intro X h
    rw [le_div_iff₀ (by positivity)] at h
    have : X * u ≤ |X| * u := mul_le_mul_of_nonneg_right (le_abs_self X) hu0.le
    nlinarith
  have huC : 3 * (C / c) * u ≤ 1 := by
    have h := hle_inv (3 * (|C| / c)) (by positivity)
      (huu₀.trans ((min_le_left _ _).trans (min_le_right _ _)))
    have : 3 * (C / c) * u ≤ 3 * (|C| / c) * u := by
      have : C / c ≤ |C| / c := div_le_div_of_nonneg_right (le_abs_self C) hc0.le
      nlinarith
    linarith
  have huK2 : K2c C * u ≤ 1 := by
    have h := hle_inv |K2c C| (abs_nonneg _)
      (huu₀.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))))
    have : K2c C * u ≤ |K2c C| * u := mul_le_mul_of_nonneg_right (le_abs_self _) hu0.le
    linarith
  have huΦ : u ^ 2 * KΦ ≤ 1 / 16 := by
    have h := hle_inv (16 * |KΦ|) (by positivity)
      (huu₀.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
    have hK : 0 ≤ KΦ := KPhi_nonneg C c
    rw [abs_of_nonneg hK] at h
    have hu1' : u ≤ 1 := by linarith
    have h1 : u ^ 2 ≤ u := by
      calc u ^ 2 = u * u := by ring
        _ ≤ u * 1 := mul_le_mul_of_nonneg_left hu1' hu0.le
        _ = u := by ring
    have h2 : u ^ 2 * KΦ ≤ u * KΦ := mul_le_mul_of_nonneg_right h1 hK
    have h3 : 16 * (u * KΦ) ≤ 1 := by
      calc 16 * (u * KΦ) = 16 * KΦ * u := by ring
        _ ≤ 1 := h
    linarith
  have hKA : KA' * u ≤ ε :=
    hle_eps KA' (huu₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hKP : KP' * u ≤ ε :=
    hle_eps KP' (huu₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  -- exponent bookkeeping
  set m := preLev M t r B τ x with hm_def
  have hpos1 : 0 < t ^ (1 + e₀) := Real.rpow_pos_of_pos ht _
  have hm0 : 0 < m := by linarith
  have hθu : t ^ βw ≤ u := rpow_le_of_le ht ht1 (by linarith)
  have hsθ : √t ≤ t ^ βw := by
    rw [Real.sqrt_eq_rpow]; exact rpow_le_of_le ht ht1 (by linarith)
  have hu2 : u ^ 2 = t ^ (2 * κ) := rpow_sq ht
  have hF5 : √t * t ^ βw ≤ u * √m := by
    have e1 : √t * t ^ βw = t ^ ((1 + e₀) / 2) * t ^ (βw - e₀ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht, ← Real.rpow_add ht]; ring_nf
    have e2 : t ^ ((1 + e₀) / 2) ≤ √m := by
      rw [← sqrt_rpow ht]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [e1]
    have := rpow_le_of_le ht ht1 hκ1
    calc t ^ ((1 + e₀) / 2) * t ^ (βw - e₀ / 2) ≤ √m * u :=
          mul_le_mul e2 this (Real.rpow_pos_of_pos ht _).le (Real.sqrt_nonneg _)
      _ = u * √m := by ring
  have hF3 : (B.card + 1) * √(t ^ (1 + δ)) ≤ 2 * u := by
    rw [sqrt_rpow ht]
    have h1 : (1 : ℝ) ≤ t ^ (-ν) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
    have h2 : (B.card : ℝ) + 1 ≤ 2 * t ^ (-ν) := by linarith
    have h3 : t ^ (-ν) * t ^ ((1 + δ) / 2) ≤ u := by
      rw [← Real.rpow_add ht]
      exact rpow_le_of_le ht ht1 (by linarith)
    have h4 := Real.rpow_pos_of_pos ht ((1 + δ) / 2)
    calc (B.card + 1) * t ^ ((1 + δ) / 2) ≤ 2 * t ^ (-ν) * t ^ ((1 + δ) / 2) :=
          mul_le_mul_of_nonneg_right h2 h4.le
      _ = 2 * (t ^ (-ν) * t ^ ((1 + δ) / 2)) := by ring
      _ ≤ 2 * u := by linarith
  have hF4 : m ≤ 4 * u ^ 2 * t := by
    have e1 : t ^ (1 + e₀) = t * t ^ e₀ := by
      rw [Real.rpow_add ht, Real.rpow_one]
    have h1 : t ^ e₀ ≤ u ^ 2 := by rw [hu2]; exact rpow_le_of_le ht ht1 (by linarith)
    calc m ≤ 4 * t ^ (1 + e₀) := hmhi
      _ = 4 * t * t ^ e₀ := by rw [e1]; ring
      _ ≤ 4 * t * u ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 4 * u ^ 2 * t := by ring
  have hF6 : B.card * t ^ (1 + δ) ≤ u ^ 2 * m := by
    have h1 : t ^ (δ - ν - e₀) ≤ u ^ 2 := by rw [hu2]; exact rpow_le_of_le ht ht1 (by linarith)
    have e1 : t ^ (-ν) * t ^ (1 + δ) = t ^ (1 + e₀) * t ^ (δ - ν - e₀) := by
      rw [← Real.rpow_add ht, ← Real.rpow_add ht]; ring_nf
    have hp1 := Real.rpow_pos_of_pos ht (1 + δ)
    calc (B.card : ℝ) * t ^ (1 + δ) ≤ t ^ (-ν) * t ^ (1 + δ) := mul_le_mul_of_nonneg_right hB hp1.le
      _ = t ^ (1 + e₀) * t ^ (δ - ν - e₀) := e1
      _ ≤ t ^ (1 + e₀) * u ^ 2 := mul_le_mul_of_nonneg_left h1 hpos1.le
      _ ≤ m * u ^ 2 := by nlinarith [sq_nonneg u]
      _ = u ^ 2 * m := by ring
  have hF7 : t ^ (1 + δ) ≤ u ^ 2 := by rw [hu2]; exact rpow_le_of_le ht ht1 (by linarith)
  have hηnn : 0 ≤ η := by
    have := mul_nonneg hη0 ht.le
    rwa [div_mul_cancel₀ _ ht.ne'] at this
  have hηle : η ≤ C * t ^ 2 := by
    have := mul_le_mul_of_nonneg_right hη1 ht.le
    rw [div_mul_cancel₀ _ ht.ne'] at this
    linarith [show C * t * t = C * t ^ 2 by ring]
  -- the explicit drift
  obtain ⟨hAI, hPI, hA, hP⟩ := drift_of_small (x := x) (B := B) (τ := τ) hM hsmall hc0 hp (hgr x)
    (hfour x) hx hτ hmax hm0 hξm hm1 hm2 hξb hηnn hηle hu0 hu1 huC huK2 huΦ (hlag x) hθu hsθ
    hF5 hF3 hF4 hF6 hF7
  refine ⟨hAI, hPI, ?_, ?_⟩
  · calc |∫ ω, (postA M t r B x τ (ξ ω) - preA M t r B τ) ∂μ| ≤ KA' * u * m := hA
      _ ≤ ε * m := mul_le_mul_of_nonneg_right hKA hm0.le
  · calc ∫ ω, (postP M t r B x τ (ξ ω) - preP M t r B τ) ∂μ ≤ -m ^ 2 + KP' * u * m ^ 2 := hP
      _ ≤ -m ^ 2 + ε * m ^ 2 := by
          have := mul_le_mul_of_nonneg_right hKP (sq_nonneg m); linarith
      _ = -(1 - ε) * m ^ 2 := by ring

end Asymptotic

end AndersonAC.L64
