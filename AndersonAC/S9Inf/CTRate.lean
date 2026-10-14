import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A logarithmic weight rate absorbs the nearest-neighbor hopping error. -/

noncomputable section

namespace AndersonAC.SolS9Inf

def ctRate (d : ℕ) (η : ℝ) : ℝ := Real.log (1 + η / (4 * ((d : ℝ) + 1)))

theorem ctRate_bounds (d : ℕ) (η : ℝ) (hη : η ∈ Set.Ioc (0 : ℝ) 1) :
    0 < ctRate d η ∧
    2 * (d : ℝ) * (Real.exp (ctRate d η) - 1) ≤ η / 2 ∧
    η / (8 * ((d : ℝ) + 1)) ≤ ctRate d η := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 4 * ((d : ℝ) + 1) := by positivity
  let t : ℝ := η / (4 * ((d : ℝ) + 1))
  have ht : 0 < t := div_pos hη.1 hden
  have htone : t ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith only [hη.2, hd]
  have ha : 0 < ctRate d η := Real.log_pos (by change 1 < 1 + t; linarith)
  refine ⟨ha, ?_, ?_⟩
  · rw [ctRate, Real.exp_log (by change 0 < 1 + t; linarith), add_sub_cancel_left]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hη.1]
  · have hlog := Real.le_log_one_add_of_nonneg ht.le
    have hhalf : t / 2 ≤ 2 * t / (t + 2) := by
      apply (le_div_iff₀ (by linarith : 0 < t + 2)).mpr
      have htsq : t * t ≤ t := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left htone ht.le
      nlinarith only [htsq, ht]
    have heq : η / (8 * ((d : ℝ) + 1)) = t / 2 := by
      dsimp [t]
      field_simp [show (d : ℝ) + 1 ≠ 0 by positivity]
      ring
    rw [heq]
    exact hhalf.trans hlog

end AndersonAC.SolS9Inf
