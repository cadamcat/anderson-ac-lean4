import AndersonAC.AgentS6Row.Algebra

open Matrix ComplexConjugate

namespace AndersonAC.AgentS6Row

open AndersonAC.L64

variable {ι B : Type*} [Fintype B] [DecidableEq B] (H : NHeat ι B)

lemma rowRem_abs_le (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) (i : ι) :
    |rowRem H i c| ≤
      √(nsq (H.w c i - H.u i)) * √(fro (H.D c)) * √(nsq (H.w c i)) +
      √(nsq (H.u i)) * √(fro (H.D c)) * √(nsq (H.w c i - H.u i)) +
      2 * fro (H.D c) * nsq (H.w c i) := by
  let z := H.w c i - H.u i
  have hw : H.w c i = H.u i + z := by simp [z]
  have hstar : star (H.w c i) = star (H.u i) + star z := by rw [hw, star_add]
  have hdecomp :
      H.w c i ⬝ᵥ (H.D c *ᵥ star (H.w c i)) -
        H.u i ⬝ᵥ (H.D c *ᵥ star (H.u i)) =
        z ⬝ᵥ (H.D c *ᵥ star (H.w c i)) +
          H.u i ⬝ᵥ (H.D c *ᵥ star z) := by
    rw [hstar, hw, Matrix.mulVec_add]
    simp only [add_dotProduct, dotProduct_add]
    ring
  have h1 := norm_dotProduct_mulVec_le (H.D c) z (star (H.w c i))
  have h2 := norm_dotProduct_mulVec_le (H.D c) (H.u i) (star z)
  have h1' : ‖z ⬝ᵥ (H.D c *ᵥ star (H.w c i))‖ ≤
      √(nsq z) * √(fro (H.D c)) * √(nsq (H.w c i)) := by
    simpa only [nsq_star] using h1
  have h2' : ‖H.u i ⬝ᵥ (H.D c *ᵥ star z)‖ ≤
      √(nsq (H.u i)) * √(fro (H.D c)) * √(nsq z) := by
    simpa only [nsq_star] using h2
  have hq1 : nsq (H.q c i) ≤ fro (H.D c) * nsq (H.w c i) := by
    simpa [NHeat.q, nsq_star] using nsq_mulVec_le (H.D c) (star (H.w c i))
  have hq2 := NHeat.norm_q_Z_le H c hF i
  have hqnorm : ‖star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)‖ ≤
      2 * fro (H.D c) * nsq (H.w c i) := by
    calc
      _ ≤ 2 * nsq (H.q c i) := hq2
      _ ≤ 2 * (fro (H.D c) * nsq (H.w c i)) := mul_le_mul_of_nonneg_left hq1 (by norm_num)
      _ = _ := by ring
  have hNormsum :
      |-(z ⬝ᵥ (H.D c *ᵥ star (H.w c i)) +
          H.u i ⬝ᵥ (H.D c *ᵥ star z)).re +
          (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re| ≤
        ‖z ⬝ᵥ (H.D c *ᵥ star (H.w c i))‖ +
          ‖H.u i ⬝ᵥ (H.D c *ᵥ star z)‖ +
          ‖star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)‖ := by
    calc
      _ ≤ |(z ⬝ᵥ (H.D c *ᵥ star (H.w c i)) +
          H.u i ⬝ᵥ (H.D c *ᵥ star z)).re| +
          |(star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re| := by
            calc
              _ ≤ |-(z ⬝ᵥ (H.D c *ᵥ star (H.w c i)) +
                  H.u i ⬝ᵥ (H.D c *ᵥ star z)).re| +
                  |(star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re| := abs_add_le _ _
              _ = _ := by rw [abs_neg]
      _ ≤ ‖z ⬝ᵥ (H.D c *ᵥ star (H.w c i)) +
          H.u i ⬝ᵥ (H.D c *ᵥ star z)‖ +
          ‖star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)‖ :=
            add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
      _ ≤ _ := by
        gcongr
        exact norm_add_le _ _
  unfold rowRem
  rw [hdecomp]
  calc
    _ ≤ ‖z ⬝ᵥ (H.D c *ᵥ star (H.w c i))‖ +
        ‖H.u i ⬝ᵥ (H.D c *ᵥ star z)‖ +
        ‖star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)‖ := hNormsum
    _ ≤ √(nsq z) * √(fro (H.D c)) * √(nsq (H.w c i)) +
        √(nsq (H.u i)) * √(fro (H.D c)) * √(nsq z) +
        2 * fro (H.D c) * nsq (H.w c i) := by
          calc
            _ ≤ (√(nsq z) * √(fro (H.D c)) * √(nsq (H.w c i)) +
                √(nsq (H.u i)) * √(fro (H.D c)) * √(nsq z)) +
                2 * fro (H.D c) * nsq (H.w c i) :=
                  add_le_add (add_le_add h1' h2') hqnorm
            _ = _ := by ring

/-- Pathwise one-row jump from a bounded pivot leverage, fourth-row input, and Gram bound. -/
lemma row_jump_bound {t l C P D : ℝ} (c : ℂ) (i : ι) (ht : 0 < t) (hl : 0 < l)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hD0 : 0 ≤ D) (hvl : l / √t ≤ 1)
    (hm : H.m ≤ 4 * l) (hmi : H.lev i ≤ H.m)
    (hc : ‖c‖ ≤ C) (hvi : ‖H.v i‖ ^ 2 ≤ P * l / √t)
    (hF : fro (H.D c) ≤ 1 / 4) (hD : √(fro (H.D c)) ≤ D * l / √t) :
    |H.lev' c i - H.lev i| ≤
      (8 * C + 4 * C ^ 2 * P + 16 * (1 + C ^ 2 * P) * D) *
        l * (‖H.v i‖ + l / √t) := by
  have hm0 : 0 ≤ H.m := nsq_nonneg H.ux
  have hmi0 : 0 ≤ H.lev i := nsq_nonneg (H.u i)
  have hv0 : 0 ≤ ‖H.v i‖ := norm_nonneg _
  have hc2 : ‖c‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg c) hc 2
  have hW : nsq (H.w c i) ≤ 8 * (1 + C ^ 2 * P) * l := by
    have hsum := nsq_add_le (H.u i) ((c * H.v i) • H.ux)
    have hnorm : ‖c * H.v i‖ ^ 2 ≤ C ^ 2 * ‖H.v i‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
    have hmul : ‖c * H.v i‖ ^ 2 * H.m ≤ C ^ 2 * (P * l / √t) * (4 * l) := by
      calc
        ‖c * H.v i‖ ^ 2 * H.m ≤ (C ^ 2 * ‖H.v i‖ ^ 2) * H.m :=
          mul_le_mul_of_nonneg_right hnorm hm0
        _ = C ^ 2 * (‖H.v i‖ ^ 2 * H.m) := by ring
        _ ≤ C ^ 2 * (P * l / √t * H.m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvi hm0) (sq_nonneg C)
        _ = C ^ 2 * (P * l / √t) * H.m := by ring
        _ ≤ C ^ 2 * (P * l / √t) * (4 * l) :=
          mul_le_mul_of_nonneg_left hm
            (mul_nonneg (sq_nonneg C) (div_nonneg (mul_nonneg hP hl.le) (Real.sqrt_nonneg _)))
    have hsq : nsq ((c * H.v i) • H.ux) = ‖c * H.v i‖ ^ 2 * H.m := by
      simp [nsq_smul, NHeat.m]
    calc
      nsq (H.w c i) ≤ 2 * nsq (H.u i) + 2 * nsq ((c * H.v i) • H.ux) := by
        simpa only [NHeat.w] using hsum
      _ ≤ 2 * H.m + 2 * (C ^ 2 * (P * l / √t) * (4 * l)) := by
        rw [hsq]
        have hmi' : nsq (H.u i) ≤ H.m := by simpa [NHeat.lev] using hmi
        exact add_le_add
          (mul_le_mul_of_nonneg_left hmi' (by norm_num))
          (mul_le_mul_of_nonneg_left hmul (by norm_num))
      _ ≤ 8 * l + 8 * C ^ 2 * P * l := by
        have ht0 : 0 ≤ l / √t := div_nonneg hl.le (Real.sqrt_nonneg _)
        have hp : 0 ≤ C ^ 2 * P := mul_nonneg (sq_nonneg _) hP
        have hpow : l * (l / √t) ≤ l := by
          calc l * (l / √t) ≤ l * 1 := mul_le_mul_of_nonneg_left hvl hl.le
            _ = l := by ring
        have : C ^ 2 * (P * l / √t) * (4 * l) =
            4 * (C ^ 2 * P) * (l * (l / √t)) := by field_simp <;> ring
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ 8 * (C ^ 2 * P) by positivity)]
      _ = 8 * (1 + C ^ 2 * P) * l := by ring
  have hs : ‖rowS H i‖ ≤ H.m := by
    have hcs := norm_dotProduct_le H.ux (star (H.u i))
    rw [nsq_star] at hcs
    have hroot : √(H.m) * √(H.lev i) ≤ H.m := by
      have hlev : H.lev i ≤ H.m := hmi
      have hsqrt := Real.sqrt_le_sqrt hlev
      calc √(H.m) * √(H.lev i) ≤ √(H.m) * √(H.m) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
        _ = H.m := Real.mul_self_sqrt hm0
    have hcs' : ‖H.ux ⬝ᵥ star (H.u i)‖ ≤ √(H.m) * √(H.lev i) := by
      simpa [NHeat.m, NHeat.lev] using hcs
    simpa [rowS] using hcs'.trans hroot
  have hraw : |nsq (H.w c i) - H.lev i| ≤
      8 * C * l * ‖H.v i‖ + 4 * C ^ 2 * P * l ^ 2 / √t := by
    have hrawEq : nsq (H.w c i) - H.lev i =
        2 * (c * H.v i * rowS H i).re + ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m := by
      rw [NHeat.nsq_w]
      simp [rowS]
      ring
    rw [hrawEq]
    have hvnorm : ‖H.v i‖ ^ 2 * H.m ≤ P * l / √t * (4 * l) := by
      calc
        ‖H.v i‖ ^ 2 * H.m ≤ P * l / √t * H.m := mul_le_mul_of_nonneg_right hvi hm0
        _ ≤ P * l / √t * (4 * l) := mul_le_mul_of_nonneg_left hm
          (div_nonneg (mul_nonneg hP hl.le) (Real.sqrt_nonneg _))
    have hcross : |2 * (c * H.v i * rowS H i).re| ≤
        2 * C * ‖H.v i‖ * H.m := by
      calc
        _ ≤ 2 * ‖c * H.v i * rowS H i‖ := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
        _ = 2 * (‖c‖ * ‖H.v i‖ * ‖rowS H i‖) := by rw [norm_mul, norm_mul]
        _ ≤ 2 * (C * ‖H.v i‖ * H.m) := by
          have hcv : ‖c‖ * ‖H.v i‖ ≤ C * ‖H.v i‖ :=
            mul_le_mul_of_nonneg_right hc hv0
          calc
            2 * (‖c‖ * ‖H.v i‖ * ‖rowS H i‖) ≤
                2 * (C * ‖H.v i‖ * ‖rowS H i‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hcv (norm_nonneg _)) (by norm_num)
            _ = (2 * C * ‖H.v i‖) * ‖rowS H i‖ := by ring
            _ ≤ (2 * C * ‖H.v i‖) * H.m :=
              mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (by norm_num) hC) hv0)
            _ = 2 * (C * ‖H.v i‖ * H.m) := by ring
        _ = 2 * C * ‖H.v i‖ * H.m := by ring
    have hquad : ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m ≤
        4 * C ^ 2 * P * l ^ 2 / √t := by
      calc
        ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m = ‖c‖ ^ 2 * (‖H.v i‖ ^ 2 * H.m) := by ring
        _ ≤ C ^ 2 * (‖H.v i‖ ^ 2 * H.m) :=
          mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg _) hm0)
        _ ≤ C ^ 2 * (P * l / √t * (4 * l)) := mul_le_mul_of_nonneg_left hvnorm (sq_nonneg _)
        _ = 4 * C ^ 2 * P * l ^ 2 / √t := by ring
    have hnonneg : 0 ≤ ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m := by positivity
    have hlin : 2 * C * ‖H.v i‖ * H.m ≤ 8 * C * l * ‖H.v i‖ := by
      calc
        2 * C * ‖H.v i‖ * H.m ≤ 2 * C * ‖H.v i‖ * (4 * l) :=
          mul_le_mul_of_nonneg_left hm (mul_nonneg (mul_nonneg (by norm_num) hC) hv0)
        _ = 8 * C * l * ‖H.v i‖ := by ring
    calc
      |2 * (c * H.v i * rowS H i).re + ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m|
        ≤ |2 * (c * H.v i * rowS H i).re| +
          |‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m| := abs_add_le _ _
      _ ≤ 2 * C * ‖H.v i‖ * H.m + 4 * C ^ 2 * P * l ^ 2 / √t := by
        rw [abs_of_nonneg hnonneg]
        exact add_le_add hcross hquad
      _ ≤ _ := by linarith
  have hq : nsq (H.q c i) ≤ fro (H.D c) * nsq (H.w c i) := by
    simpa [NHeat.q, nsq_star] using nsq_mulVec_le (H.D c) (star (H.w c i))
  have hcor : |H.lev' c i - nsq (H.w c i)| ≤
      2 * nsq (H.w c i) * √(fro (H.D c)) := by
    have h0 := NHeat.abs_lev'_sub_le H c hF i
    have hqroot : √(nsq (H.q c i)) ≤ √(fro (H.D c)) * √(nsq (H.w c i)) := by
      calc
        √(nsq (H.q c i)) ≤ √(fro (H.D c) * nsq (H.w c i)) := Real.sqrt_le_sqrt hq
        _ = √(fro (H.D c)) * √(nsq (H.w c i)) := by
          rw [Real.sqrt_mul (fro_nonneg (H.D c))]
    calc
      _ ≤ 2 * (√(nsq (H.w c i)) * √(nsq (H.q c i))) := h0
      _ ≤ 2 * (√(nsq (H.w c i)) * (√(fro (H.D c)) * √(nsq (H.w c i)))) := by
        gcongr
      _ = 2 * nsq (H.w c i) * √(fro (H.D c)) := by
        calc
          2 * (√(nsq (H.w c i)) * (√(fro (H.D c)) * √(nsq (H.w c i)))) =
              2 * (√(nsq (H.w c i)) * √(nsq (H.w c i))) * √(fro (H.D c)) := by ring
          _ = _ := by rw [Real.mul_self_sqrt (nsq_nonneg _)]
  have hcorr' : 2 * nsq (H.w c i) * √(fro (H.D c)) ≤
      16 * (1 + C ^ 2 * P) * D * l ^ 2 / √t := by
    calc
      2 * nsq (H.w c i) * √(fro (H.D c)) ≤
          2 * (8 * (1 + C ^ 2 * P) * l) * (D * l / √t) := by
            gcongr
      _ = 16 * (1 + C ^ 2 * P) * D * l ^ 2 / √t := by ring
  have hL : 0 ≤ 8 * C + 4 * C ^ 2 * P + 16 * (1 + C ^ 2 * P) * D := by positivity
  let A : ℝ := 4 * C ^ 2 * P + 16 * (1 + C ^ 2 * P) * D
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hL₁ : 8 * C ≤ 8 * C + A := by linarith
  have hL₂ : A ≤ 8 * C + A := by linarith
  have hcorBound : |H.lev' c i - nsq (H.w c i)| ≤
      16 * (1 + C ^ 2 * P) * D * l ^ 2 / √t := hcor.trans hcorr'
  have hrawBound : |nsq (H.w c i) - H.lev i| ≤
      8 * C * l * ‖H.v i‖ + 4 * C ^ 2 * P * l ^ 2 / √t := hraw
  calc
    |H.lev' c i - H.lev i|
      ≤ |H.lev' c i - nsq (H.w c i)| +
        |nsq (H.w c i) - H.lev i| := by
          calc
            _ = |(H.lev' c i - nsq (H.w c i)) +
              (nsq (H.w c i) - H.lev i)| := by congr 1 <;> ring
            _ ≤ _ := abs_add_le _ _
    _ ≤ 8 * C * l * ‖H.v i‖ + A * l ^ 2 / √t := by
      calc
        _ ≤ 16 * (1 + C ^ 2 * P) * D * l ^ 2 / √t +
            (8 * C * l * ‖H.v i‖ + 4 * C ^ 2 * P * l ^ 2 / √t) :=
              add_le_add hcorBound hrawBound
        _ = 8 * C * l * ‖H.v i‖ + A * l ^ 2 / √t := by dsimp [A]; ring
    _ ≤ (8 * C + A) * l * (‖H.v i‖ + l / √t) := by
      have hterm1 := mul_le_mul_of_nonneg_right hL₁
        (mul_nonneg hl.le (norm_nonneg (H.v i)))
      have hterm2 := mul_le_mul_of_nonneg_right hL₂
        (div_nonneg (sq_nonneg l) (Real.sqrt_nonneg t))
      calc
        8 * C * l * ‖H.v i‖ + A * l ^ 2 / √t ≤
            (8 * C + A) * (l * ‖H.v i‖) + (8 * C + A) * (l ^ 2 / √t) := by
              apply add_le_add
              · calc
                  8 * C * l * ‖H.v i‖ = 8 * C * (l * ‖H.v i‖) := by ring
                  _ ≤ _ := hterm1
              · calc
                  A * l ^ 2 / √t = A * (l ^ 2 / √t) := by ring
                  _ ≤ _ := hterm2
        _ = (8 * C + A) * l * (‖H.v i‖ + l / √t) := by ring
  rw [show 8 * C + A = 8 * C + 4 * C ^ 2 * P + 16 * (1 + C ^ 2 * P) * D by
    dsimp [A]; ring]

end AndersonAC.AgentS6Row
