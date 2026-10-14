import AndersonAC.S78Extract.TorusGeometry

open scoped BigOperators
namespace AndersonAC.SolS78

open AndersonAC.S78 Filter

private theorem exists_growth_cutoff (q B : ℝ) (hq : 0 < q) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → B < (4 : ℝ) ^ (q * (j : ℝ)) := by
  have ha : 1 < (4 : ℝ) ^ q := Real.one_lt_rpow (by norm_num) hq
  have hev : ∀ᶠ j : ℕ in atTop, B < ((4 : ℝ) ^ q) ^ j :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).eventually_gt_atTop B
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun j hj => ?_⟩
  have h := hN j hj
  rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (4 : ℝ)) q j] at h
  exact h

private lemma nu_pos {d : ℕ} (hd : 3 ≤ d) : 0 < nu d := by
  dsimp [nu, delta]
  positivity

private lemma nu_lt_two {d : ℕ} (hd : 3 ≤ d) : nu d < 2 := by
  have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
  dsimp [nu, delta]
  have hden : 0 < 100000 * (d : ℝ) := by positivity
  have hden' : (1 : ℝ) < 100000 * (d : ℝ) := by nlinarith [hdR]
  field_simp
  nlinarith

private lemma historyAlpha_identity (d : ℕ) (hd : 3 ≤ d) :
    10 * historyAlpha d * (d : ℝ) = 0.1 * nu d := by
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
  dsimp [historyAlpha]
  field_simp
  ring

private lemma witnessRadius_rpow (j : ℕ) :
    witnessRadius j = (4 : ℝ) ^ (10 * (j : ℝ)) := by
  rw [witnessRadius, ← Real.rpow_natCast]
  congr 1
  norm_num [Nat.cast_mul]

private lemma witnessRadius_power_rpow {d j : ℕ} :
    witnessRadius j ^ d = (4 : ℝ) ^ ((10 * (j : ℝ)) * (d : ℝ)) := by
  rw [witnessRadius_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : 0 ≤ (4 : ℝ))]

private lemma stageScale_upper {j m : ℕ} (hjm : clearingScheduled j m) :
    stageScale 1 j m ≤ 2 / (4 : ℝ) ^ j := by
  have hmj : j ≤ m := by
    dsimp [clearingScheduled] at hjm
    omega
  have hpow : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ m := by
    gcongr <;> norm_num <;> omega
  have hrecip : ((4 : ℝ) ^ m)⁻¹ ≤ ((4 : ℝ) ^ j)⁻¹ := by
    exact inv_anti₀ (by positivity) hpow
  dsimp [stageScale]
  rw [one_div, one_div]
  calc
    ((4 : ℝ) ^ j)⁻¹ + ((4 : ℝ) ^ m)⁻¹ ≤ ((4 : ℝ) ^ j)⁻¹ + ((4 : ℝ) ^ j)⁻¹ :=
      add_le_add le_rfl hrecip
    _ = 2 / (4 : ℝ) ^ j := by rw [← two_mul, div_eq_mul_inv]

theorem exists_history_cutoff (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j m, N ≤ j → clearingScheduled j m →
      2 * C * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) ≤ witnessRadius j / 2 ∧
      (historyChildren d j : ℝ) *
          ((2 * Nat.ceil (3 * witnessRadius (historyEarlier d j)) + 1) ^ d : ℕ) <
        (stageScale 1 j m) ^ (-nu d) := by
  have hnu := nu_pos hd
  have hnu2 := nu_lt_two hd
  have hqRad : 0 < 2 - nu d := by linarith
  have hqPack : 0 < 0.7 * nu d := by positivity
  obtain ⟨Nrad, hrad⟩ := exists_growth_cutoff (2 - nu d) (4 * C) hqRad
  obtain ⟨Npack, hpack⟩ := exists_growth_cutoff (0.7 * nu d) (9 ^ d * 2 ^ nu d) hqPack
  let N := max 1 (max Nrad Npack)
  refine ⟨N, by simp [N], ?_⟩
  intro j m hNj hclear
  have hjNrad : Nrad ≤ j := le_trans (le_max_of_le_right (le_max_left _ _)) hNj
  have hjNpack : Npack ≤ j := le_trans (le_max_of_le_right (le_max_right _ _)) hNj
  have hradGrow : 4 * C < (4 : ℝ) ^ ((2 - nu d) * (j : ℝ)) := hrad j hjNrad
  have hradPow :
      (4 : ℝ) ^ ((2 - nu d) * (j : ℝ)) *
        (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) = witnessRadius j := by
    rw [← Real.rpow_add (by norm_num : 0 < (4 : ℝ))]
    rw [show (2 - nu d) * (j : ℝ) + (8 + nu d) * (j : ℝ) = 10 * (j : ℝ) by ring]
    exact (witnessRadius_rpow j).symm
  have hpowPos : 0 < (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num : 0 < (4 : ℝ)) _
  have hradProd := mul_lt_mul_of_pos_right hradGrow hpowPos
  rw [hradPow] at hradProd
  have hradGoal : 2 * C * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) ≤ witnessRadius j / 2 := by
    nlinarith [hradProd]

  let r := historyEarlier d j
  let R := Nat.ceil (3 * witnessRadius r)
  have halpha : 0 ≤ historyAlpha d := by
    dsimp [historyAlpha, nu, delta]
    positivity
  have hrAlpha : (r : ℝ) ≤ historyAlpha d * (j : ℝ) := by
    dsimp [r, historyEarlier]
    exact Nat.floor_le (mul_nonneg halpha (by positivity))
  have hAlpha : 10 * historyAlpha d * (d : ℝ) = 0.1 * nu d := historyAlpha_identity d hd
  have hWr : witnessRadius r ^ d ≤ (4 : ℝ) ^ (0.1 * nu d * (j : ℝ)) := by
    rw [witnessRadius_power_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
    calc
      (10 * (r : ℝ)) * (d : ℝ) ≤ (10 * (historyAlpha d * (j : ℝ))) * (d : ℝ) := by
        gcongr
      _ = 0.1 * nu d * (j : ℝ) := by rw [← hAlpha]; ring
  have hceil : (R : ℝ) < 3 * witnessRadius r + 1 := by
    dsimp [R]
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (by
      dsimp [witnessRadius]
      positivity))
  have hballRad : (2 * R + 1 : ℝ) ≤ 9 * witnessRadius r := by
    have hWrpos : 1 ≤ witnessRadius r := by
      dsimp [witnessRadius]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
    nlinarith

  have hpackGrow : 9 ^ d * 2 ^ nu d < (4 : ℝ) ^ (0.7 * nu d * (j : ℝ)) :=
    hpack j hjNpack
  have hbase : (9 : ℝ) ^ d * (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) <
      (2 : ℝ) ^ (-nu d) * (4 : ℝ) ^ (nu d * (j : ℝ)) := by
    have hdiv : (9 : ℝ) ^ d <
        (4 : ℝ) ^ (0.7 * nu d * (j : ℝ)) / (2 : ℝ) ^ (nu d) := by
      apply (lt_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _)).2
      simpa [mul_comm] using hpackGrow
    calc
      (9 : ℝ) ^ d * (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) <
          ((4 : ℝ) ^ (0.7 * nu d * (j : ℝ)) / (2 : ℝ) ^ (nu d)) *
            (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) := by
        exact mul_lt_mul_of_pos_right hdiv
          (Real.rpow_pos_of_pos (by norm_num : 0 < (4 : ℝ)) _)
      _ = (2 : ℝ) ^ (-nu d) * (4 : ℝ) ^ (nu d * (j : ℝ)) := by
        calc
          ((4 : ℝ) ^ (0.7 * nu d * (j : ℝ)) / (2 : ℝ) ^ (nu d)) *
              (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) =
              (4 : ℝ) ^ (0.7 * nu d * (j : ℝ)) *
                (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) / (2 : ℝ) ^ (nu d) := by ring
          _ = (4 : ℝ) ^ (nu d * (j : ℝ)) / (2 : ℝ) ^ (nu d) := by
            rw [← Real.rpow_add (by norm_num : 0 < (4 : ℝ))]
            congr 1
            ring
          _ = (2 : ℝ) ^ (-nu d) * (4 : ℝ) ^ (nu d * (j : ℝ)) := by
            rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]
            ring
  have hscale : 0 < stageScale 1 j m := by
    dsimp [stageScale]
    positivity
  have hstageUp := stageScale_upper hclear
  have hstagePow :
      (2 / (4 : ℝ) ^ j) ^ (-nu d) ≤ (stageScale 1 j m) ^ (-nu d) :=
    Real.rpow_le_rpow_of_nonpos hscale hstageUp (by linarith)
  have hstageEq :
      (2 / (4 : ℝ) ^ j) ^ (-nu d) =
        (2 : ℝ) ^ (-nu d) * (4 : ℝ) ^ (nu d * (j : ℝ)) := by
    rw [Real.div_rpow (by norm_num : 0 ≤ (2 : ℝ)) (by positivity)]
    rw [Real.rpow_neg (by norm_num : 0 ≤ ((4 : ℝ) ^ j))]
    rw [div_inv_eq_mul]
    rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (4 : ℝ)) j (nu d)]
    rw [show (j : ℝ) * nu d = nu d * (j : ℝ) by ring]
  have hstageLow :
      (9 : ℝ) ^ d * (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) <
        (stageScale 1 j m) ^ (-nu d) := by
    calc
      _ < (2 : ℝ) ^ (-nu d) * (4 : ℝ) ^ (nu d * (j : ℝ)) := hbase
      _ = (2 / (4 : ℝ) ^ j) ^ (-nu d) := hstageEq.symm
      _ ≤ (stageScale 1 j m) ^ (-nu d) := hstagePow
  have hk : (historyChildren d j : ℝ) ≤ (4 : ℝ) ^ (0.2 * nu d * (j : ℝ)) := by
    dsimp [historyChildren]
    exact Nat.floor_le (by positivity)
  have hball : ((2 * R + 1) ^ d : ℝ) ≤ (9 : ℝ) ^ d *
      (4 : ℝ) ^ (0.1 * nu d * (j : ℝ)) := by
    have hpow : ((2 * R + 1 : ℝ) ^ d) ≤ (9 * witnessRadius r) ^ d := by
      gcongr
    calc
      ((2 * R + 1 : ℝ) ^ d) ≤ 9 ^ d * witnessRadius r ^ d := by
        simpa [mul_pow] using hpow
      _ ≤ 9 ^ d * (4 : ℝ) ^ (0.1 * nu d * (j : ℝ)) := by gcongr
  have hcap : (historyChildren d j : ℝ) * ((2 * R + 1) ^ d : ℝ) ≤
      (9 : ℝ) ^ d * (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) := by
    calc
      _ ≤ (4 : ℝ) ^ (0.2 * nu d * (j : ℝ)) *
            ((9 : ℝ) ^ d * (4 : ℝ) ^ (0.1 * nu d * (j : ℝ))) := by
        exact mul_le_mul hk hball (by positivity) (by positivity)
      _ = (9 : ℝ) ^ d * (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) := by
        calc
          (4 : ℝ) ^ (0.2 * nu d * (j : ℝ)) *
              ((9 : ℝ) ^ d * (4 : ℝ) ^ (0.1 * nu d * (j : ℝ))) =
              (9 : ℝ) ^ d *
                ((4 : ℝ) ^ (0.2 * nu d * (j : ℝ)) *
                  (4 : ℝ) ^ (0.1 * nu d * (j : ℝ))) := by ring
          _ = (9 : ℝ) ^ d * (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : 0 < (4 : ℝ))]
            congr 1
            ring
  have hcapNat : (historyChildren d j : ℝ) *
      ((2 * R + 1) ^ d : ℕ) < (stageScale 1 j m) ^ (-nu d) := by
    have hcap' : (historyChildren d j : ℝ) * ((2 * R + 1) ^ d : ℕ) ≤
        (9 : ℝ) ^ d * (4 : ℝ) ^ (0.3 * nu d * (j : ℝ)) := by
      exact_mod_cast hcap
    exact lt_of_le_of_lt hcap' hstageLow
  exact ⟨hradGoal, by simpa [R, r] using hcapNat⟩

end AndersonAC.SolS78
