import AndersonAC.L64.Bridge
import AndersonAC.S6.Statements

open Matrix Finset ComplexConjugate

namespace AndersonAC.AgentS6Row

open AndersonAC.L64

lemma dot_star_swap {B : Type*} [Fintype B] (u v : B → ℂ) :
    u ⬝ᵥ star v = star (v ⬝ᵥ star u) := by
  change (∑ b, u b * star (v b)) =
    (starRingEnd ℂ) (∑ b, v b * star (u b))
  rw [map_sum]
  refine sum_congr rfl fun b _ => ?_
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

lemma re_conj_mul_conj (z w : ℂ) : (conj z * conj w).re = (z * w).re := by
  rw [← map_mul]
  simp

variable {ι B : Type*} [Fintype B] [DecidableEq B] (H : NHeat ι B)

noncomputable def rowS (i : ι) : ℂ := H.ux ⬝ᵥ star (H.u i)

noncomputable def rowAff (i : ι) (c : ℂ) : ℝ :=
  ‖rowS H i‖ ^ 2 + ‖c‖ ^ 2 * (‖H.v i‖ ^ 2 * H.m - H.vn * ‖rowS H i‖ ^ 2) +
    2 * (c * (H.v i * rowS H i - rowS H i * (H.u i ⬝ᵥ H.b))).re

lemma row_D (c : ℂ) (i : ι) :
    H.u i ⬝ᵥ (H.D c *ᵥ star (H.u i)) =
      ((‖c‖ ^ 2 * H.vn - 1 : ℝ) : ℂ) * ‖rowS H i‖ ^ 2 +
        c * (rowS H i * (H.u i ⬝ᵥ H.b)) +
        conj c * conj (rowS H i * (H.u i ⬝ᵥ H.b)) := by
  rw [H.D_eq]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, dotProduct_vecMulVec_mulVec, rowS]
  have hs : H.u i ⬝ᵥ star H.ux = conj (H.ux ⬝ᵥ star (H.u i)) :=
    dot_star_swap _ _
  have hb : star H.b ⬝ᵥ star (H.u i) = conj (H.u i ⬝ᵥ H.b) := by
    rw [star_dotProduct_star]
    rfl
  rw [hs, hb]
  rw [show conj (H.ux ⬝ᵥ star (H.u i)) * (H.ux ⬝ᵥ star (H.u i)) =
      ((‖H.ux ⬝ᵥ star (H.u i)‖ ^ 2 : ℝ) : ℂ) from conj_mul_self_eq _]
  push_cast
  simp only [map_mul]
  ring

lemma row_D_re (c : ℂ) (i : ι) :
    (H.u i ⬝ᵥ (H.D c *ᵥ star (H.u i))).re =
      (‖c‖ ^ 2 * H.vn - 1) * ‖rowS H i‖ ^ 2 +
        2 * (c * (rowS H i * (H.u i ⬝ᵥ H.b))).re := by
  rw [row_D H c i]
  have hcm : conj (c * (rowS H i * (H.u i ⬝ᵥ H.b))) =
      conj c * conj (rowS H i * (H.u i ⬝ᵥ H.b)) :=
    map_mul (starRingEnd ℂ) c _
  rw [← hcm, Complex.add_re, Complex.add_re, Complex.conj_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hnorm : (↑‖rowS H i‖ ^ 2 : ℂ).re = ‖rowS H i‖ ^ 2 := by norm_cast
  rw [hnorm]
  ring

noncomputable def rowRem (i : ι) (c : ℂ) : ℝ :=
  -((H.w c i ⬝ᵥ (H.D c *ᵥ star (H.w c i))) -
      (H.u i ⬝ᵥ (H.D c *ᵥ star (H.u i)))).re +
    (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re

lemma row_change_eq_affine_add_rem (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) (i : ι) :
    H.lev' c i - H.lev i = rowAff H i c + rowRem H i c := by
  rw [H.lev'_expand c hF i, H.nsq_w c i]
  unfold rowAff rowRem
  rw [Complex.sub_re]
  rw [row_D_re H c i]
  unfold rowS
  simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im, Complex.add_im]
  ring

end AndersonAC.AgentS6Row
