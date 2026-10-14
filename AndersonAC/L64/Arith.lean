import Mathlib

/-!
# Lemma 6.4: the final bookkeeping

Pure real arithmetic: the explicit bounds produced by `NHeat.drift`, together with the size
estimates of the inputs in terms of a single small parameter `u`, give
`|𝔼(𝒜'-𝒜)| ≤ KA u m` and `𝔼(𝒫'-𝒫) ≤ -m² + KP u m²`. Here `s = √t`, `w = √m`.
-/

namespace AndersonAC.L64

/-- the constant `K_Φ` bounding `Φ ≤ w² (w/s)² K_Φ`. -/
noncomputable def KPhi (C c : ℝ) : ℝ := 3 * ((2 * (4 * C) ^ 2 + 1) ^ 2 + 2 * (4 * C) ^ 2 / c ^ 2)

/-- the constant bounding `ω`. -/
noncomputable def Kω (C : ℝ) : ℝ := 2 * (1 + 2 * (4 * C) ^ 2)

/-- the constant in the total-leverage drift. -/
noncomputable def KA (C c Ke K2 : ℝ) : ℝ :=
  3 * (2 * K2 + 3 * (C / c)) + 6 * Ke / c + 4 * (1 + 2 * Kω C) * KPhi C c

/-- the constant in the squared-leverage drift. -/
noncomputable def KP (C c Ke K2 : ℝ) : ℝ :=
  4 * (C / c) + 2 * (2 * K2 + 3 * (C / c)) + 8 * Ke + 4 * Ke / c
    + 4 * (4 * C) ^ 2 * (C / c) * √(KPhi C c) + 16 * (4 * C) * √(KPhi C c)
    + 16 * Kω C * KPhi C c + 16 * (4 * C) ^ 2 * (C / c) + 4 * (4 * C) ^ 4 * (C / c) ^ 2
    + 32 * (2 + 4 * (4 * C) ^ 2) * Kω C * KPhi C c

lemma KPhi_nonneg (C c : ℝ) : 0 ≤ KPhi C c := by unfold KPhi; positivity

lemma Kω_nonneg (C : ℝ) : 0 ≤ Kω C := by unfold Kω; positivity

section

variable {s w u C c Ke K2 vn Ec2 Ecn nb vL v4 : ℝ}

/-- Common estimates. -/
structure Sizes (s w u C c Ke K2 vn Ec2 Ecn nb vL v4 : ℝ) : Prop where
  s_pos : 0 < s
  s_le : s ≤ 1
  w_pos : 0 < w
  u_pos : 0 < u
  u_le : u ≤ 1 / 2
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  Ke_nonneg : 0 ≤ Ke
  K2_nonneg : 0 ≤ K2
  ws : w ≤ 2 * u * s
  vn_dev : |vn - 1| ≤ 3 * (C / c) * u
  vn_small : 3 * (C / c) * u ≤ 1
  Ec2_dev : |Ec2 - 1| ≤ K2 * u
  Ec2_small : K2 * u ≤ 1
  Ecn_nonneg : 0 ≤ Ecn
  Ecn_s : Ecn ≤ Ke * u * s
  Ecn_w : Ecn ≤ Ke * u * w
  nb_nonneg : 0 ≤ nb
  nb_le : nb ≤ w ^ 2 / (s ^ 2 * c ^ 2)
  v4_nonneg : 0 ≤ v4
  v4_le : v4 ≤ (C / c) ^ 2 * u ^ 2
  vL_nonneg : 0 ≤ vL
  vL_le : vL ≤ (C / c) * u * w ^ 2

namespace Sizes

variable (h : Sizes s w u C c Ke K2 vn Ec2 Ecn nb vL v4)
include h

lemma w_le_one : w ≤ 1 := by
  have := h.ws; have := h.u_le; have := h.s_le; have := h.s_pos; have := h.u_pos
  nlinarith

lemma vn_nonneg : 0 ≤ vn := by
  have := (abs_le.mp h.vn_dev).1; have := h.vn_small; linarith

lemma vn_le : vn ≤ 2 := by
  have := (abs_le.mp h.vn_dev).2; have := h.vn_small; linarith

lemma Ec2_le : Ec2 ≤ 2 := by
  have := (abs_le.mp h.Ec2_dev).2; have := h.Ec2_small; linarith

lemma Ec2_nonneg : 0 ≤ Ec2 := by
  have := (abs_le.mp h.Ec2_dev).1; have := h.Ec2_small; linarith

lemma dev_le : |Ec2 * vn - 1| ≤ (2 * K2 + 3 * (C / c)) * u := by
  have e : Ec2 * vn - 1 = (Ec2 - 1) * vn + (vn - 1) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg h.vn_nonneg]
  have := mul_le_mul h.Ec2_dev h.vn_le h.vn_nonneg (by have := h.K2_nonneg; have := h.u_pos; positivity)
  have := h.vn_dev
  nlinarith

lemma sqrt_nb_le : √nb ≤ w / (s * c) := by
  have hsc : 0 < s * c := mul_pos h.s_pos h.c_pos
  rw [show w / (s * c) = √((w / (s * c)) ^ 2) from
    (Real.sqrt_sq (div_nonneg h.w_pos.le hsc.le)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_pow, mul_pow]; exact h.nb_le

lemma sqrt_vn_le : √vn ≤ 2 := by
  rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (h.vn_le.trans (by norm_num))

/-- `Φ ≤ w² · 4u² · K_Φ`. -/
lemma Phi_le :
    3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2)
      ≤ w ^ 2 * (4 * u ^ 2) * KPhi C c := by
  have hs := h.s_pos; have hc := h.c_pos; have hw := h.w_pos
  have hvn0 := h.vn_nonneg; have hvn2 := h.vn_le
  have h1 : ((4 * C) ^ 2 * vn + 1) ^ 2 ≤ (2 * (4 * C) ^ 2 + 1) ^ 2 := by
    have : (4 * C) ^ 2 * vn ≤ (4 * C) ^ 2 * 2 := mul_le_mul_of_nonneg_left hvn2 (sq_nonneg _)
    have : 0 ≤ (4 * C) ^ 2 * vn := mul_nonneg (sq_nonneg _) hvn0
    exact pow_le_pow_left₀ (add_nonneg (mul_nonneg (sq_nonneg _) hvn0) zero_le_one) (by linarith) 2
  have hws2 : w ^ 2 / s ^ 2 ≤ 4 * u ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := h.ws; have := h.u_pos
    nlinarith
  have hw2 : w ^ 2 ≤ w ^ 2 / s ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : s ^ 2 ≤ 1 := by have := h.s_le; nlinarith
    nlinarith [sq_nonneg w]
  have h2 : nb * w ^ 2 ≤ (w ^ 2 / s ^ 2) * w ^ 2 / c ^ 2 := by
    have := h.nb_le
    calc nb * w ^ 2 ≤ w ^ 2 / (s ^ 2 * c ^ 2) * w ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = (w ^ 2 / s ^ 2) * w ^ 2 / c ^ 2 := by field_simp
  unfold KPhi
  have hA : ((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 ≤ (2 * (4 * C) ^ 2 + 1) ^ 2 * (w ^ 2 * (w ^ 2 / s ^ 2)) := by
    rw [show (w ^ 2) ^ 2 = w ^ 2 * w ^ 2 by ring]
    exact mul_le_mul h1 (mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)) (by positivity) (sq_nonneg _)
  have hB : 2 * (4 * C) ^ 2 * nb * w ^ 2 ≤ 2 * (4 * C) ^ 2 / c ^ 2 * (w ^ 2 * (w ^ 2 / s ^ 2)) := by
    have : 2 * (4 * C) ^ 2 * nb * w ^ 2 = 2 * (4 * C) ^ 2 * (nb * w ^ 2) := by ring
    rw [this]
    calc 2 * (4 * C) ^ 2 * (nb * w ^ 2) ≤ 2 * (4 * C) ^ 2 * ((w ^ 2 / s ^ 2) * w ^ 2 / c ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hX : w ^ 2 * (w ^ 2 / s ^ 2) ≤ w ^ 2 * (4 * u ^ 2) :=
    mul_le_mul_of_nonneg_left hws2 (sq_nonneg _)
  have hK1 : 0 ≤ (2 * (4 * C) ^ 2 + 1) ^ 2 := sq_nonneg _
  have hK2 : 0 ≤ 2 * (4 * C) ^ 2 / c ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hX hK1, mul_le_mul_of_nonneg_left hX hK2]

lemma omega_le : 2 * (1 + (4 * C) ^ 2 * vn * w ^ 2) ≤ Kω C := by
  unfold Kω
  have hw1 := h.w_le_one; have hw0 := h.w_pos
  have : vn * w ^ 2 ≤ 2 := by
    have : w ^ 2 ≤ 1 := by nlinarith
    nlinarith [h.vn_nonneg, h.vn_le]
  nlinarith [sq_nonneg (4 * C)]

end Sizes

/-- The total-leverage bookkeeping. -/
theorem total_bound (h : Sizes s w u C c Ke K2 vn Ec2 Ecn nb vL v4) {EA : ℝ}
    (hA : |EA| ≤ 3 * w ^ 2 * |Ec2 * vn - 1| + 6 * Ecn * √(w ^ 2) * √nb
      + (1 + 2 * (2 * (1 + (4 * C) ^ 2 * vn * w ^ 2)))
        * (3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2))) :
    |EA| ≤ KA C c Ke K2 * u * w ^ 2 := by
  have hw := h.w_pos; have hu := h.u_pos; have hc := h.c_pos; have hs := h.s_pos
  rw [Real.sqrt_sq hw.le] at hA
  have t1 : 3 * w ^ 2 * |Ec2 * vn - 1| ≤ 3 * (2 * K2 + 3 * (C / c)) * u * w ^ 2 := by
    have := h.dev_le
    nlinarith [sq_nonneg w]
  have t2 : 6 * Ecn * w * √nb ≤ 6 * Ke / c * u * w ^ 2 := by
    have h1 := h.sqrt_nb_le
    have h2 := h.Ecn_s
    have : Ecn * w * √nb ≤ (Ke * u * s) * w * (w / (s * c)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h2 hw.le) h1 (Real.sqrt_nonneg _)
        (by have := h.Ke_nonneg; positivity)
    have e : (Ke * u * s) * w * (w / (s * c)) = Ke / c * u * w ^ 2 := by field_simp
    calc 6 * Ecn * w * √nb = 6 * (Ecn * w * √nb) := by ring
      _ ≤ 6 * (Ke / c * u * w ^ 2) := by linarith
      _ = 6 * Ke / c * u * w ^ 2 := by ring
  have t3 : (1 + 2 * (2 * (1 + (4 * C) ^ 2 * vn * w ^ 2)))
        * (3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2))
      ≤ 4 * (1 + 2 * Kω C) * KPhi C c * u * w ^ 2 := by
    have hΦ := h.Phi_le
    have hω := h.omega_le
    have hΦ0 : 0 ≤ 3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2) := by
      have := h.vn_nonneg; have := h.nb_nonneg; positivity
    have hu2 : u ^ 2 ≤ u := by have := h.u_le; nlinarith
    have hKP := KPhi_nonneg C c
    calc (1 + 2 * (2 * (1 + (4 * C) ^ 2 * vn * w ^ 2)))
          * (3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2))
        ≤ (1 + 2 * Kω C) * (w ^ 2 * (4 * u ^ 2) * KPhi C c) :=
          mul_le_mul (by linarith) hΦ hΦ0 (by have := Kω_nonneg C; linarith)
      _ = 4 * (1 + 2 * Kω C) * KPhi C c * (u ^ 2) * w ^ 2 := by ring
      _ ≤ 4 * (1 + 2 * Kω C) * KPhi C c * u * w ^ 2 := by
          have : 0 ≤ 4 * (1 + 2 * Kω C) * KPhi C c := by have := Kω_nonneg C; positivity
          gcongr
  unfold KA
  nlinarith

set_option maxHeartbeats 800000 in
/-- The squared-leverage bookkeeping. -/
theorem square_bound (h : Sizes s w u C c Ke K2 vn Ec2 Ecn nb vL v4) {EP : ℝ}
    (hP : EP ≤ -(w ^ 2) ^ 2 + 2 * Ec2 * w ^ 2 * vL + 2 * (w ^ 2) ^ 2 * |Ec2 * vn - 1|
      + 4 * Ecn * w ^ 2 * √(w ^ 2) * (√vn + √nb)
      + (2 * ((4 * C) ^ 2 * vL * w ^ 2 * √(3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2
              + 2 * (4 * C) ^ 2 * nb * w ^ 2))
            + 2 * (4 * C) * √(w ^ 2) * √(3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2
              + 2 * (4 * C) ^ 2 * nb * w ^ 2)) * (w ^ 2 * √vn))
        + 4 * w ^ 2 * (2 * (1 + (4 * C) ^ 2 * vn * w ^ 2))
          * (3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2))
        + 16 * (4 * C) ^ 2 * w ^ 2 * vL + 4 * (4 * C) ^ 4 * (w ^ 2) ^ 2 * v4
        + 8 * (2 * w ^ 2 + 2 * (4 * C) ^ 2 * vn * w ^ 2) * (2 * (1 + (4 * C) ^ 2 * vn * w ^ 2))
          * (3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2)))) :
    EP ≤ -(w ^ 2) ^ 2 + KP C c Ke K2 * u * (w ^ 2) ^ 2 := by
  have hw := h.w_pos; have hu := h.u_pos; have hc := h.c_pos; have hs := h.s_pos
  have hC := h.C_nonneg; have hKe := h.Ke_nonneg; have hK2 := h.K2_nonneg
  have hw1 := h.w_le_one
  have hu1 : u ≤ 1 := h.u_le.trans (by norm_num)
  have hvn0 := h.vn_nonneg; have hvn2 := h.vn_le
  have hvL0 := h.vL_nonneg; have hv40 := h.v4_nonneg; have hnb0 := h.nb_nonneg
  set Φ := 3 * (((4 * C) ^ 2 * vn + 1) ^ 2 * (w ^ 2) ^ 2 + 2 * (4 * C) ^ 2 * nb * w ^ 2)
  set ω := 2 * (1 + (4 * C) ^ 2 * vn * w ^ 2)
  set KΦ := KPhi C c
  set Kw := Kω C
  have hKΦ := KPhi_nonneg C c
  have hKw := Kω_nonneg C
  have hΦ0 : 0 ≤ Φ := by positivity
  have hω0 : 0 ≤ ω := by positivity
  have hΦ : Φ ≤ w ^ 2 * (4 * u ^ 2) * KΦ := h.Phi_le
  have hω : ω ≤ Kw := h.omega_le
  have hu2 : u ^ 2 ≤ u := by
    calc u ^ 2 = u * u := by ring
      _ ≤ u * 1 := mul_le_mul_of_nonneg_left hu1 hu.le
      _ = u := by ring
  have hW4 : 0 ≤ (w ^ 2) ^ 2 := by positivity
  rw [Real.sqrt_sq hw.le] at hP
  -- `√Φ ≤ 2 u w √K_Φ`
  have hsΦ : √Φ ≤ 2 * u * w * √KΦ := by
    have : Φ ≤ (2 * u * w) ^ 2 * KΦ := hΦ.trans (le_of_eq (by ring))
    calc √Φ ≤ √((2 * u * w) ^ 2 * KΦ) := Real.sqrt_le_sqrt this
      _ = 2 * u * w * √KΦ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hsvn := h.sqrt_vn_le
  have hsnb := h.sqrt_nb_le
  have hsK : 0 ≤ √KΦ := Real.sqrt_nonneg _
  have hdev := h.dev_le
  -- term by term
  have p1 : 2 * Ec2 * w ^ 2 * vL ≤ 4 * (C / c) * u * (w ^ 2) ^ 2 := by
    have hE2 := h.Ec2_le
    have hvL := h.vL_le
    have a : Ec2 * vL ≤ 2 * ((C / c) * u * w ^ 2) := mul_le_mul hE2 hvL hvL0 (by norm_num)
    have b := mul_le_mul_of_nonneg_left a (by positivity : (0 : ℝ) ≤ 2 * w ^ 2)
    calc 2 * Ec2 * w ^ 2 * vL = 2 * w ^ 2 * (Ec2 * vL) := by ring
      _ ≤ 2 * w ^ 2 * (2 * ((C / c) * u * w ^ 2)) := b
      _ = 4 * (C / c) * u * (w ^ 2) ^ 2 := by ring
  have p2 : 2 * (w ^ 2) ^ 2 * |Ec2 * vn - 1| ≤ 2 * (2 * K2 + 3 * (C / c)) * u * (w ^ 2) ^ 2 := by
    have b := mul_le_mul_of_nonneg_left hdev (by positivity : (0 : ℝ) ≤ 2 * (w ^ 2) ^ 2)
    calc 2 * (w ^ 2) ^ 2 * |Ec2 * vn - 1| ≤ 2 * (w ^ 2) ^ 2 * ((2 * K2 + 3 * (C / c)) * u) := b
      _ = 2 * (2 * K2 + 3 * (C / c)) * u * (w ^ 2) ^ 2 := by ring
  have p3 : 4 * Ecn * w ^ 2 * w * (√vn + √nb) ≤ (8 * Ke + 4 * Ke / c) * u * (w ^ 2) ^ 2 := by
    have a1 : Ecn * w * √vn ≤ (Ke * u * w) * w * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right h.Ecn_w hw.le) hsvn (Real.sqrt_nonneg _) (by positivity)
    have a2 : Ecn * w * √nb ≤ (Ke * u * s) * w * (w / (s * c)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h.Ecn_s hw.le) hsnb (Real.sqrt_nonneg _) (by positivity)
    have e2 : (Ke * u * s) * w * (w / (s * c)) = Ke / c * u * w ^ 2 := by field_simp
    have e : 4 * Ecn * w ^ 2 * w * (√vn + √nb) = 4 * w ^ 2 * (Ecn * w * √vn + Ecn * w * √nb) := by
      ring
    rw [e]
    have a1' : Ecn * w * √vn ≤ 2 * Ke * u * w ^ 2 := a1.trans (le_of_eq (by ring))
    have a2' : Ecn * w * √nb ≤ Ke / c * u * w ^ 2 := a2.trans (le_of_eq e2)
    have : Ecn * w * √vn + Ecn * w * √nb ≤ (2 * Ke + Ke / c) * u * w ^ 2 := by
      have := add_le_add a1' a2'
      calc Ecn * w * √vn + Ecn * w * √nb ≤ 2 * Ke * u * w ^ 2 + Ke / c * u * w ^ 2 := this
        _ = (2 * Ke + Ke / c) * u * w ^ 2 := by ring
    calc 4 * w ^ 2 * (Ecn * w * √vn + Ecn * w * √nb) ≤ 4 * w ^ 2 * ((2 * Ke + Ke / c) * u * w ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (8 * Ke + 4 * Ke / c) * u * (w ^ 2) ^ 2 := by ring
  have p4 : 2 * ((4 * C) ^ 2 * vL * w ^ 2 * √Φ + 2 * (4 * C) * w * √Φ * (w ^ 2 * √vn))
      ≤ (4 * (4 * C) ^ 2 * (C / c) * √KΦ + 16 * (4 * C) * √KΦ) * u * (w ^ 2) ^ 2 := by
    have a1 : vL * √Φ ≤ ((C / c) * u * w ^ 2) * (2 * u * w * √KΦ) :=
      mul_le_mul h.vL_le hsΦ (Real.sqrt_nonneg _) (by positivity)
    have a1' : ((C / c) * u * w ^ 2) * (2 * u * w * √KΦ) ≤ 2 * (C / c) * √KΦ * u * w ^ 2 := by
      have huw : u * w ≤ 1 := by
        calc u * w ≤ 1 * 1 := mul_le_mul hu1 hw1 hw.le zero_le_one
          _ = 1 := by ring
      have hk : 0 ≤ 2 * (C / c) * √KΦ * u * w ^ 2 := by positivity
      calc ((C / c) * u * w ^ 2) * (2 * u * w * √KΦ) = (2 * (C / c) * √KΦ * u * w ^ 2) * (u * w) := by
            ring
        _ ≤ (2 * (C / c) * √KΦ * u * w ^ 2) * 1 := mul_le_mul_of_nonneg_left huw hk
        _ = _ := by ring
    have a2 : w * √Φ * √vn ≤ w * (2 * u * w * √KΦ) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsΦ hw.le) hsvn (Real.sqrt_nonneg _) (by positivity)
    have e : 2 * ((4 * C) ^ 2 * vL * w ^ 2 * √Φ + 2 * (4 * C) * w * √Φ * (w ^ 2 * √vn))
        = 2 * (4 * C) ^ 2 * w ^ 2 * (vL * √Φ) + 4 * (4 * C) * w ^ 2 * (w * √Φ * √vn) := by ring
    rw [e]
    have b1 : 2 * (4 * C) ^ 2 * w ^ 2 * (vL * √Φ)
        ≤ 2 * (4 * C) ^ 2 * w ^ 2 * (2 * (C / c) * √KΦ * u * w ^ 2) :=
      mul_le_mul_of_nonneg_left (a1.trans a1') (by positivity)
    have b2 : 4 * (4 * C) * w ^ 2 * (w * √Φ * √vn) ≤ 4 * (4 * C) * w ^ 2 * (w * (2 * u * w * √KΦ) * 2) :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    have e1 : 2 * (4 * C) ^ 2 * w ^ 2 * (2 * (C / c) * √KΦ * u * w ^ 2)
        = 4 * (4 * C) ^ 2 * (C / c) * √KΦ * u * (w ^ 2) ^ 2 := by ring
    have e2 : 4 * (4 * C) * w ^ 2 * (w * (2 * u * w * √KΦ) * 2)
        = 16 * (4 * C) * √KΦ * u * (w ^ 2) ^ 2 := by ring
    linarith
  have p5 : 4 * w ^ 2 * ω * Φ ≤ 16 * Kw * KΦ * u * (w ^ 2) ^ 2 := by
    have : ω * Φ ≤ Kw * (w ^ 2 * (4 * u ^ 2) * KΦ) := mul_le_mul hω hΦ hΦ0 hKw
    have : 4 * w ^ 2 * (ω * Φ) ≤ 4 * w ^ 2 * (Kw * (w ^ 2 * (4 * u ^ 2) * KΦ)) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have e : 4 * w ^ 2 * (Kw * (w ^ 2 * (4 * u ^ 2) * KΦ)) = 16 * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2 := by
      ring
    have h3 : 16 * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2 ≤ 16 * Kw * KΦ * u * (w ^ 2) ^ 2 := by
      have hk : 0 ≤ 16 * Kw * KΦ * (w ^ 2) ^ 2 := by positivity
      calc 16 * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2 = (16 * Kw * KΦ * (w ^ 2) ^ 2) * u ^ 2 := by ring
        _ ≤ (16 * Kw * KΦ * (w ^ 2) ^ 2) * u := mul_le_mul_of_nonneg_left hu2 hk
        _ = _ := by ring
    calc 4 * w ^ 2 * ω * Φ = 4 * w ^ 2 * (ω * Φ) := by ring
      _ ≤ 4 * w ^ 2 * (Kw * (w ^ 2 * (4 * u ^ 2) * KΦ)) := this
      _ = 16 * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2 := e
      _ ≤ _ := h3
  have p6 : 16 * (4 * C) ^ 2 * w ^ 2 * vL ≤ 16 * (4 * C) ^ 2 * (C / c) * u * (w ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h.vL_le (by positivity : (0 : ℝ) ≤ 16 * (4 * C) ^ 2 * w ^ 2)
    calc 16 * (4 * C) ^ 2 * w ^ 2 * vL ≤ 16 * (4 * C) ^ 2 * w ^ 2 * ((C / c) * u * w ^ 2) := this
      _ = _ := by ring
  have p7 : 4 * (4 * C) ^ 4 * (w ^ 2) ^ 2 * v4 ≤ 4 * (4 * C) ^ 4 * (C / c) ^ 2 * u * (w ^ 2) ^ 2 := by
    have : v4 ≤ (C / c) ^ 2 * u := h.v4_le.trans (mul_le_mul_of_nonneg_left hu2 (sq_nonneg _))
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * (4 * C) ^ 4 * (w ^ 2) ^ 2)
    calc 4 * (4 * C) ^ 4 * (w ^ 2) ^ 2 * v4 ≤ 4 * (4 * C) ^ 4 * (w ^ 2) ^ 2 * ((C / c) ^ 2 * u) := this
      _ = _ := by ring
  have p8 : 8 * (2 * w ^ 2 + 2 * (4 * C) ^ 2 * vn * w ^ 2) * ω * Φ
      ≤ 32 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * u * (w ^ 2) ^ 2 := by
    have a : 2 * w ^ 2 + 2 * (4 * C) ^ 2 * vn * w ^ 2 ≤ (2 + 4 * (4 * C) ^ 2) * w ^ 2 := by
      have : (4 * C) ^ 2 * vn ≤ (4 * C) ^ 2 * 2 := mul_le_mul_of_nonneg_left hvn2 (sq_nonneg _)
      have := mul_le_mul_of_nonneg_right this (sq_nonneg w)
      calc 2 * w ^ 2 + 2 * (4 * C) ^ 2 * vn * w ^ 2 = 2 * w ^ 2 + 2 * ((4 * C) ^ 2 * vn * w ^ 2) := by
            ring
        _ ≤ 2 * w ^ 2 + 2 * ((4 * C) ^ 2 * 2 * w ^ 2) := by linarith
        _ = _ := by ring
    have b : ω * Φ ≤ Kw * (w ^ 2 * (4 * u ^ 2) * KΦ) := mul_le_mul hω hΦ hΦ0 hKw
    have c' : (2 * w ^ 2 + 2 * (4 * C) ^ 2 * vn * w ^ 2) * (ω * Φ)
        ≤ ((2 + 4 * (4 * C) ^ 2) * w ^ 2) * (Kw * (w ^ 2 * (4 * u ^ 2) * KΦ)) :=
      mul_le_mul a b (by positivity) (by positivity)
    have e : ((2 + 4 * (4 * C) ^ 2) * w ^ 2) * (Kw * (w ^ 2 * (4 * u ^ 2) * KΦ))
        = 4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2 := by ring
    have d : 4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2
        ≤ 4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * u * (w ^ 2) ^ 2 := by
      have hk : 0 ≤ 4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * (w ^ 2) ^ 2 := by positivity
      calc 4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2
          = (4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * (w ^ 2) ^ 2) * u ^ 2 := by ring
        _ ≤ (4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * (w ^ 2) ^ 2) * u :=
          mul_le_mul_of_nonneg_left hu2 hk
        _ = _ := by ring
    calc 8 * (2 * w ^ 2 + 2 * (4 * C) ^ 2 * vn * w ^ 2) * ω * Φ
        = 8 * ((2 * w ^ 2 + 2 * (4 * C) ^ 2 * vn * w ^ 2) * (ω * Φ)) := by ring
      _ ≤ 8 * (((2 + 4 * (4 * C) ^ 2) * w ^ 2) * (Kw * (w ^ 2 * (4 * u ^ 2) * KΦ))) := by linarith
      _ = 8 * (4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * u ^ 2 * (w ^ 2) ^ 2) := by rw [e]
      _ ≤ 8 * (4 * (2 + 4 * (4 * C) ^ 2) * Kw * KΦ * u * (w ^ 2) ^ 2) := by linarith
      _ = _ := by ring
  unfold KP
  linarith

end

end AndersonAC.L64
