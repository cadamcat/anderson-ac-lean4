import AndersonAC.AgentS6Row.RowMean
import AndersonAC.L64.Arith

noncomputable section
open Matrix ComplexConjugate

namespace AndersonAC.AgentS6Row

open AndersonAC.L64

variable {ι B : Type*} [Fintype B] [DecidableEq B]

lemma fro_D_scale (H : NHeat ι B) {t l C c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hl : 0 ≤ l) (hC : 0 ≤ C) (hm : H.m ≤ 4 * l)
    (hvn : H.vn ≤ 2) (hb : nsq H.b ≤ H.m / (t * c ^ 2))
    (z : ℂ) (hz : ‖z‖ ≤ 4 * C) :
    fro (H.D z) ≤ 16 * KPhi C c * l ^ 2 / t := by
  have hKP := KPhi_nonneg C c
  have hf := H.fro_D_le z (4 * C) hz
  have hm0 := H.m_nn
  have hv0 := H.vn_nonneg
  have hA : ((4 * C) ^ 2 * H.vn + 1) ^ 2 ≤ (2 * (4 * C) ^ 2 + 1) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (4 * C)]
  have hmt : H.m ^ 2 ≤ H.m ^ 2 / t := by
    rw [le_div_iff₀ ht]
    nlinarith [sq_nonneg H.m]
  have hfirst : ((4 * C) ^ 2 * H.vn + 1) ^ 2 * H.m ^ 2 ≤
      (2 * (4 * C) ^ 2 + 1) ^ 2 * (H.m ^ 2 / t) :=
    mul_le_mul hA hmt (sq_nonneg _) (sq_nonneg _)
  have hsecond : 2 * (4 * C) ^ 2 * nsq H.b * H.m ≤
      (2 * (4 * C) ^ 2 / c ^ 2) * (H.m ^ 2 / t) := by
    calc
      _ ≤ 2 * (4 * C) ^ 2 * (H.m / (t * c ^ 2)) * H.m := by gcongr
      _ = _ := by ring
  have hm2 : H.m ^ 2 ≤ 16 * l ^ 2 := by nlinarith
  calc
    fro (H.D z) ≤ H.Φ (4 * C) := hf
    _ ≤ KPhi C c * (H.m ^ 2 / t) := by
      unfold NHeat.Φ KPhi
      nlinarith
    _ ≤ KPhi C c * (16 * l ^ 2 / t) := by
      gcongr
    _ = _ := by ring

lemma sqrt_fro_D_scale (H : NHeat ι B) {t l C c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hl : 0 ≤ l) (hC : 0 ≤ C) (hm : H.m ≤ 4 * l)
    (hvn : H.vn ≤ 2) (hb : nsq H.b ≤ H.m / (t * c ^ 2))
    (z : ℂ) (hz : ‖z‖ ≤ 4 * C) :
    Real.sqrt (fro (H.D z)) ≤ 4 * Real.sqrt (KPhi C c) * l / Real.sqrt t := by
  have hh := Real.sqrt_le_sqrt (fro_D_scale H ht ht1 hc hl hC hm hvn hb z hz)
  have he : Real.sqrt (16 * KPhi C c * l ^ 2 / t) =
      4 * Real.sqrt (KPhi C c) * l / Real.sqrt t := by
    rw [show 16 * KPhi C c * l ^ 2 = (16 : ℝ) * (KPhi C c * l ^ 2) by ring,
      Real.sqrt_div (mul_nonneg (by norm_num) (mul_nonneg (KPhi_nonneg C c) (sq_nonneg l))),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
      Real.sqrt_mul (KPhi_nonneg C c), Real.sqrt_sq hl]
    norm_num
    ring
  exact he ▸ hh

lemma rowRem_scale (H : NHeat ι B) {t l C D : ℝ} (ht : 0 < t) (hl : 0 < l)
    (hC : 0 ≤ C) (hD0 : 0 ≤ D) (i : ι) (hmi : H.lev i ≤ 4 * l)
    (hm : H.m ≤ 4 * l) (hvi : ‖H.v i‖ ≤ 2) (z : ℂ) (hz : ‖z‖ ≤ C)
    (hF : fro (H.D z) ≤ 1 / 4)
    (hD : Real.sqrt (fro (H.D z)) ≤ D * l / Real.sqrt t) :
    |rowRem H i z| ≤
      (2 * C * (4 * (1 + 2 * C) + 2) * D +
        2 * D ^ 2 * (4 * (1 + 2 * C)) ^ 2) *
        (l ^ 2 * ‖H.v i‖ / Real.sqrt t + l ^ 3 / t) := by
  let W : ℝ := 4 * (1 + 2 * C)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hm0 := H.m_nn
  have hu : Real.sqrt (nsq (H.u i)) ≤ 2 * Real.sqrt l := by
    calc
      _ ≤ Real.sqrt (4 * l) := Real.sqrt_le_sqrt hmi
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hx : Real.sqrt (nsq H.ux) ≤ 2 * Real.sqrt l := by
    calc
      _ ≤ Real.sqrt (4 * l) := Real.sqrt_le_sqrt hm
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hdiff : Real.sqrt (nsq (H.w z i - H.u i)) ≤ 2 * C * ‖H.v i‖ * Real.sqrt l := by
    rw [NHeat.w, add_sub_cancel_left, nsq_smul, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _), norm_mul]
    calc
      _ ≤ C * ‖H.v i‖ * (2 * Real.sqrt l) := by gcongr
      _ = _ := by ring
  have hwi : nsq (H.w z i) ≤ W ^ 2 * l := by
    have hh := nsq_add_le (H.u i) ((z * H.v i) • H.ux)
    rw [nsq_smul, norm_mul, mul_pow] at hh
    have hz2 : ‖z‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hv2 : ‖H.v i‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (H.v i)]
    have hmul : ‖z‖ ^ 2 * ‖H.v i‖ ^ 2 * nsq H.ux ≤ C ^ 2 * 4 * (4 * l) := by
      change ‖z‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m ≤ _
      gcongr
    change ‖z‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m ≤ C ^ 2 * 4 * (4 * l) at hmul
    change nsq (H.w z i) ≤ 2 * H.lev i + 2 * (‖z‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m) at hh
    have hlo := hl.le
    dsimp [W]
    nlinarith [mul_nonneg hC hlo, mul_nonneg (sq_nonneg C) hlo]
  have hw : Real.sqrt (nsq (H.w z i)) ≤ W * Real.sqrt l := by
    calc
      _ ≤ Real.sqrt (W ^ 2 * l) := Real.sqrt_le_sqrt hwi
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg W), Real.sqrt_sq hW]
  have hf : fro (H.D z) ≤ D ^ 2 * l ^ 2 / t := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hD 2
    rw [Real.sq_sqrt (fro_nonneg _), div_pow, mul_pow, Real.sq_sqrt ht.le] at hh
    exact hh
  have hwnon : 0 ≤ nsq (H.w z i) := nsq_nonneg _
  have hh := rowRem_abs_le H z hF i
  have h1 : Real.sqrt (nsq (H.w z i - H.u i)) * Real.sqrt (fro (H.D z)) *
      Real.sqrt (nsq (H.w z i)) ≤ 2 * C * W * D * l ^ 2 * ‖H.v i‖ / Real.sqrt t := by
    calc
      _ ≤ (2 * C * ‖H.v i‖ * Real.sqrt l) * (D * l / Real.sqrt t) * (W * Real.sqrt l) := by gcongr
      _ = 2 * C * W * D * l * (Real.sqrt l) ^ 2 * ‖H.v i‖ / Real.sqrt t := by ring
      _ = _ := by rw [Real.sq_sqrt hl.le]; ring
  have h2 : Real.sqrt (nsq (H.u i)) * Real.sqrt (fro (H.D z)) *
      Real.sqrt (nsq (H.w z i - H.u i)) ≤ 4 * C * D * l ^ 2 * ‖H.v i‖ / Real.sqrt t := by
    calc
      _ ≤ (2 * Real.sqrt l) * (D * l / Real.sqrt t) * (2 * C * ‖H.v i‖ * Real.sqrt l) := by gcongr
      _ = 4 * C * D * l * (Real.sqrt l) ^ 2 * ‖H.v i‖ / Real.sqrt t := by ring
      _ = _ := by rw [Real.sq_sqrt hl.le]; ring
  have h3 : 2 * fro (H.D z) * nsq (H.w z i) ≤ 2 * D ^ 2 * W ^ 2 * l ^ 3 / t := by
    calc
      _ ≤ 2 * (D ^ 2 * l ^ 2 / t) * (W ^ 2 * l) := by gcongr
      _ = _ := by ring
  have hA : 0 ≤ 2 * C * (W + 2) * D := by positivity
  have hB : 0 ≤ 2 * D ^ 2 * W ^ 2 := by positivity
  have hX : 0 ≤ l ^ 2 * ‖H.v i‖ / Real.sqrt t := by positivity
  have hY : 0 ≤ l ^ 3 / t := by positivity
  calc
    _ ≤ _ := hh
    _ ≤ (2 * C * W * D * l ^ 2 * ‖H.v i‖ / Real.sqrt t +
          4 * C * D * l ^ 2 * ‖H.v i‖ / Real.sqrt t) + 2 * D ^ 2 * W ^ 2 * l ^ 3 / t :=
      add_le_add (add_le_add h1 h2) h3
    _ = (2 * C * (W + 2) * D) * (l ^ 2 * ‖H.v i‖ / Real.sqrt t) +
          (2 * D ^ 2 * W ^ 2) * (l ^ 3 / t) := by ring
    _ ≤ _ := by
      change _ ≤ (2 * C * (W + 2) * D + 2 * D ^ 2 * W ^ 2) * _
      nlinarith only [mul_nonneg hA hY, mul_nonneg hB hX]

end AndersonAC.AgentS6Row
