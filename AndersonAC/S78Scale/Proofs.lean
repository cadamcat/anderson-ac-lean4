import AndersonAC.S78.Definitions

open Set

namespace AndersonAC.SolS78

open AndersonAC.S78

theorem stage_scale_comparison_proof (u : ℝ) (j m : ℕ)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j ≤ m) :
    (1 / 4 : ℝ) / (4 : ℝ) ^ j < stageScale u j m ∧
    stageScale u j m ≤ 2 / (4 : ℝ) ^ j := by
  have huLower : (1 / 4 : ℝ) < u := hu.1
  have huUpper : u ≤ 1 := hu.2
  have huPos : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) huLower
  have hpj : 0 < (4 : ℝ) ^ j := by positivity
  have hpm : 0 < (4 : ℝ) ^ m := by positivity
  have hpowers : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hjm
  have hrecip : 1 / (4 : ℝ) ^ m ≤ 1 / (4 : ℝ) ^ j :=
    one_div_le_one_div_of_le hpj hpowers
  have hfirstLower : (1 / 4 : ℝ) / (4 : ℝ) ^ j < u / (4 : ℝ) ^ j :=
    (div_lt_div_iff_of_pos_right hpj).2 huLower
  have hfirstUpper : u / (4 : ℝ) ^ j ≤ 1 / (4 : ℝ) ^ j :=
    (div_le_div_iff_of_pos_right hpj).2 huUpper
  have hsecondUpper : u / (4 : ℝ) ^ m ≤ 1 / (4 : ℝ) ^ j :=
    (div_le_div_iff_of_pos_right hpm).2 huUpper |>.trans hrecip
  constructor
  · unfold stageScale
    linarith [hfirstLower, div_pos huPos hpm]
  · unfold stageScale
    calc
      u / (4 : ℝ) ^ j + u / (4 : ℝ) ^ m ≤
          1 / (4 : ℝ) ^ j + 1 / (4 : ℝ) ^ j := add_le_add hfirstUpper hsecondUpper
      _ = 2 / (4 : ℝ) ^ j := by ring

theorem assembly_exponent_margins_proof (d : ℕ) (hd : 3 ≤ d) :
    (d : ℝ) * nu d = 0.00001 * delta ∧
    0.36 * delta < 0.42 * delta - (d : ℝ) * nu d ∧
    0 < 0.0225 * delta - (d : ℝ) * nu d ∧
    0.10 * delta < 0.125 * delta - (d : ℝ) * nu d ∧ heatExponent < 0.03 := by
  have hdPos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdn : (d : ℝ) * nu d = 0.00001 * delta := by
    unfold nu delta
    field_simp
    norm_num
  have hdelta : 0 < delta := by norm_num [delta]
  refine ⟨hdn, ?_, ?_, ?_, ?_⟩
  · rw [hdn]
    nlinarith
  · rw [hdn]
    nlinarith
  · rw [hdn]
    nlinarith
  · norm_num [heatExponent, delta]

theorem sharp_diagonal_margin_proof (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ θ ∈ Set.Icc (0.25 : ℝ) 0.625, a ≤ θ ^ κ - θ := by
  let f : ℝ → ℝ := fun θ => θ ^ κ - θ
  have hcompact : IsCompact (Set.Icc (0.25 : ℝ) 0.625) := isCompact_Icc
  have hnonempty : (Set.Icc (0.25 : ℝ) 0.625).Nonempty := by
    exact ⟨0.25, by constructor <;> norm_num⟩
  have hcontinuous : ContinuousOn f (Set.Icc (0.25 : ℝ) 0.625) := by
    dsimp [f]
    exact (Real.continuous_rpow_const hκ.le).sub continuous_id |>.continuousOn
  obtain ⟨θ₀, hθ₀, hmin⟩ := hcompact.exists_isMinOn hnonempty hcontinuous
  have hθ₀pos : 0 < θ₀ := lt_of_lt_of_le (by norm_num) hθ₀.1
  have hθ₀lt : θ₀ < 1 := lt_of_le_of_lt hθ₀.2 (by norm_num)
  have hpow : θ₀ ^ (1 : ℝ) < θ₀ ^ κ :=
    Real.rpow_lt_rpow_of_exponent_gt hθ₀pos hθ₀lt hκ1
  have hfpos : 0 < f θ₀ := by
    dsimp [f]
    simpa only [Real.rpow_one] using (sub_pos.mpr hpow)
  refine ⟨f θ₀, hfpos, ?_⟩
  intro θ hθ
  exact hmin hθ

end AndersonAC.SolS78
