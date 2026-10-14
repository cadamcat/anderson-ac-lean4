import Mathlib

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace AndersonAC.SolS78abort

/-- Abort bound used by `AndersonAC.S78.abortBound`. -/
def abortBound (d m : ℕ) (q C : ℝ) : ℝ := (1 + C * ((m : ℝ) + 1)) *
  Real.exp (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - (4 : ℝ) ^ (q * ((m : ℝ) / 2 - 1)))

theorem abort_nonneg (d m : ℕ) (q C : ℝ) (hC : 0 ≤ C) :
    0 ≤ abortBound d m q C := by
  unfold abortBound
  apply mul_nonneg
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ C * ((m : ℝ) + 1) := mul_nonneg hC (by linarith)
    linarith
  · exact le_of_lt (Real.exp_pos _)

theorem exp_neg_cast_tendsto :
    Filter.Tendsto (fun m : ℕ => Real.exp (-(m : ℝ))) Filter.atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp
    (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

end AndersonAC.SolS78abort

namespace AndersonAC.SolS78

open AndersonAC.SolS78abort

theorem uniform_abort_bound_proof (d : ℕ) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n₀ m, N ≤ n₀ → 4 * n₀ ≤ m → abortBound d m q C ≤ Real.exp (-(m : ℝ)) := by
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set a : ℝ := q * Real.log 4 / 4 with ha_def
  set b : ℝ := 1 - q * Real.log 4 / 2 with hb_def
  set K : ℝ := 20 * (d : ℝ) * Real.log 4 + C + 1 with hK_def
  have ha : 0 < a := by
    rw [ha_def]
    exact div_pos (mul_pos hq hL) (by norm_num)
  have ha2 : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hKpos : 0 < K := by
    rw [hK_def]
    have h20 : (0 : ℝ) ≤ 20 * (d : ℝ) * Real.log 4 := by
      apply mul_nonneg
      · exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
      · exact le_of_lt hL
    linarith
  set B : ℝ := max (max 2 (4 * (K + C) / a ^ 2)) ((-2 * b) / a) with hB_def
  obtain ⟨N, hN⟩ := exists_nat_gt (B / 4)
  refine ⟨N, fun n₀ m hn₀ hm => ?_⟩
  have hNlt : B / 4 < (N : ℝ) := hN
  have hN4 : B < 4 * (N : ℝ) := by linarith
  have hn0R : (N : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  have hmR : (4 : ℝ) * (n₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2N : (4 : ℝ) * (N : ℝ) ≤ (4 : ℝ) * (n₀ : ℝ) :=
    mul_le_mul_of_nonneg_left hn0R (by norm_num)
  have hBm : B ≤ (m : ℝ) := by linarith
  have h2B : (2 : ℝ) ≤ B := by
    rw [hB_def]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hT3B : 4 * (K + C) / a ^ 2 ≤ B := by
    rw [hB_def]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hT4B : (-2 * b) / a ≤ B := by
    rw [hB_def]
    exact le_max_right _ _
  have ht2 : (2 : ℝ) ≤ (m : ℝ) := le_trans h2B hBm
  have hT3 : 4 * (K + C) / a ^ 2 ≤ (m : ℝ) := le_trans hT3B hBm
  have hT4 : (-2 * b) / a ≤ (m : ℝ) := le_trans hT4B hBm
  have ht1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have htm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  set y : ℝ := Real.log 4 * (q * ((m : ℝ) / 2 - 1)) with hy_def
  have hR : (4 : ℝ) ^ (q * ((m : ℝ) / 2 - 1)) = Real.exp y := by
    rw [hy_def]
    exact Real.rpow_def_of_pos (by norm_num) _
  have ht_half : (0 : ℝ) ≤ (m : ℝ) / 2 - 1 := by linarith
  have hy0 : (0 : ℝ) ≤ y := by
    rw [hy_def]
    exact mul_nonneg (le_of_lt hL) (mul_nonneg (le_of_lt hq) ht_half)
  have h1y_nn : (0 : ℝ) ≤ 1 + y / 2 := by linarith
  have h1y_le : 1 + y / 2 ≤ Real.exp (y / 2) := by
    have h := Real.add_one_le_exp (y / 2)
    linarith
  have hR2 : Real.exp y = (Real.exp (y / 2)) ^ 2 := by
    have h : y / 2 + y / 2 = y := by ring
    calc Real.exp y = Real.exp (y / 2 + y / 2) := by rw [h]
      _ = Real.exp (y / 2) * Real.exp (y / 2) := Real.exp_add _ _
      _ = (Real.exp (y / 2)) ^ 2 := by ring
  have hRge : (1 + y / 2) ^ 2 ≤ Real.exp y := by
    rw [hR2]
    exact pow_le_pow_left₀ h1y_nn h1y_le 2
  have h1y_eq : (1 : ℝ) + y / 2 = a * (m : ℝ) + b := by
    rw [hy_def, ha_def, hb_def]
    ring
  have hRge2 : (a * (m : ℝ) + b) ^ 2 ≤ Real.exp y := by
    rw [← h1y_eq]
    exact hRge
  have hT4mul : -2 * b ≤ (m : ℝ) * a := (div_le_iff₀ ha).mp hT4
  have hcomm : (m : ℝ) * a = a * (m : ℝ) := mul_comm _ _
  have h_half_nn : (0 : ℝ) ≤ a * (m : ℝ) / 2 + b := by
    have h' : -2 * b ≤ a * (m : ℝ) := by
      rw [← hcomm]
      exact hT4mul
    linarith
  have h_ge : a * (m : ℝ) / 2 ≤ a * (m : ℝ) + b := by linarith
  have h_half0 : (0 : ℝ) ≤ a * (m : ℝ) / 2 := by
    have hpos : (0 : ℝ) ≤ a * (m : ℝ) := mul_nonneg (le_of_lt ha) htm0
    linarith
  have h_sq : (a * (m : ℝ) / 2) ^ 2 ≤ (a * (m : ℝ) + b) ^ 2 :=
    pow_le_pow_left₀ h_half0 h_ge 2
  have h_small : (a * (m : ℝ) / 2) ^ 2 ≤ Real.exp y :=
    le_trans h_sq hRge2
  have h4KC : 4 * (K + C) ≤ (m : ℝ) * a ^ 2 := (div_le_iff₀ ha2).mp hT3
  have h4KC' : 4 * (K + C) ≤ a ^ 2 * (m : ℝ) := by
    calc 4 * (K + C) ≤ (m : ℝ) * a ^ 2 := h4KC
      _ = a ^ 2 * (m : ℝ) := mul_comm _ _
  have h_sq_eq : (a * (m : ℝ) / 2) ^ 2 = a ^ 2 * (m : ℝ) ^ 2 / 4 := by ring
  have h_mul_t : 4 * (K + C) * (m : ℝ) ≤ (a ^ 2 * (m : ℝ)) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right h4KC' htm0
  have h_quad : (K + C) * (m : ℝ) ≤ a ^ 2 * (m : ℝ) ^ 2 / 4 := by
    have e1 : (a ^ 2 * (m : ℝ)) * (m : ℝ) = a ^ 2 * (m : ℝ) ^ 2 := by ring
    have e2 : 4 * (K + C) * (m : ℝ) / 4 = (K + C) * (m : ℝ) := by ring
    have hle : 4 * (K + C) * (m : ℝ) / 4 ≤ ((a ^ 2 * (m : ℝ)) * (m : ℝ)) / 4 :=
      div_le_div_of_nonneg_right h_mul_t (by norm_num)
    rw [e2] at hle
    rw [e1] at hle
    linarith
  have hCt : C ≤ C * (m : ℝ) := by
    have hle := mul_le_mul_of_nonneg_left ht1 hC
    simpa using hle
  have hK_le : K * (m : ℝ) + C ≤ (K + C) * (m : ℝ) := by
    have e : (K + C) * (m : ℝ) = K * (m : ℝ) + C * (m : ℝ) := by ring
    linarith
  have h_quad2 : K * (m : ℝ) + C ≤ a ^ 2 * (m : ℝ) ^ 2 / 4 :=
    le_trans hK_le h_quad
  have h_quad3 : K * (m : ℝ) + C ≤ Real.exp y := by
    rw [← h_sq_eq] at h_quad2
    exact le_trans h_quad2 h_small
  have hE_eq : 20 * (d : ℝ) * (m : ℝ) * Real.log 4 = (20 * (d : ℝ) * Real.log 4) * (m : ℝ) := by
    ring
  have h_exp_arg : C * ((m : ℝ) + 1) +
      (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - Real.exp y) ≤ -((m : ℝ)) := by
    have hKeq : K = 20 * (d : ℝ) * Real.log 4 + C + 1 := hK_def
    linarith
  have hP : (1 : ℝ) + C * ((m : ℝ) + 1) ≤ Real.exp (C * ((m : ℝ) + 1)) := by
    have h := Real.add_one_le_exp (C * ((m : ℝ) + 1))
    linarith
  have hE_rw : 20 * (d : ℝ) * (m : ℝ) * Real.log 4 - (4 : ℝ) ^ (q * ((m : ℝ) / 2 - 1))
      = 20 * (d : ℝ) * (m : ℝ) * Real.log 4 - Real.exp y := by
    rw [hR]
  have h_abort : abortBound d m q C =
      (1 + C * ((m : ℝ) + 1)) *
        Real.exp (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - Real.exp y) := by
    unfold abortBound
    rw [hR]
  calc abortBound d m q C
      = (1 + C * ((m : ℝ) + 1)) *
          Real.exp (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - Real.exp y) := h_abort
    _ ≤ Real.exp (C * ((m : ℝ) + 1)) *
          Real.exp (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - Real.exp y) :=
        mul_le_mul_of_nonneg_right hP (Real.exp_nonneg _)
    _ = Real.exp (C * ((m : ℝ) + 1) +
          (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - Real.exp y)) := by
        rw [← Real.exp_add]
    _ ≤ Real.exp (-((m : ℝ))) := Real.exp_le_exp.mpr h_exp_arg

theorem abort_bound_tendsto_proof (d : ℕ) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C) :
    Filter.Tendsto (fun m : ℕ => abortBound d m q C) Filter.atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := uniform_abort_bound_proof d q C hq hC
  have h_nonneg : ∀ m : ℕ, 0 ≤ abortBound d m q C :=
    fun m => abort_nonneg d m q C hC
  have h_le : ∀ᶠ m : ℕ in Filter.atTop, abortBound d m q C ≤ Real.exp (-(m : ℝ)) := by
    rw [eventually_atTop]
    exact ⟨4 * N, fun m hm => hN N m le_rfl hm⟩
  exact squeeze_zero' (Filter.Eventually.of_forall h_nonneg) h_le exp_neg_cast_tendsto

end AndersonAC.SolS78
