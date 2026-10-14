import AndersonAC.S9Inf.WeightedReadout
import AndersonAC.S9Inf.CTRate
import AndersonAC.S9Inf.CTWeightStatement

/-! Uniform infinite-lattice decay from bounded truncated exponential weights. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9

open AndersonAC.SolS9Inf

theorem combes_thomas_infinite_of_weights (hweights : CTWeightBoundsStatement)
    (d : ℕ) (coupling : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (E η : ℝ), η ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (ω : Configuration d) (x y : Site d),
        ‖scalarGreen coupling ω x y ((E : ℂ) + η * Complex.I)‖ ≤
          C / η * Real.exp (-c * η * latticeDistance x y) := by
  let c : ℝ := 1 / (8 * ((d : ℝ) + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2, c, by norm_num, hc, ?_⟩
  intro E η hη ω x y
  let a := ctRate d η
  let N := latticeDistance x y
  let w := ctWeight y N a
  obtain ⟨ha, hsmall, hlower⟩ := ctRate_bounds d η hη
  change 0 < a at ha
  obtain ⟨hwy, hwb, hr⟩ := hweights y N a ha.le
  have hw : ∀ u, |w u| ≤ Real.exp (a * N) := by
    intro u
    rw [abs_of_nonneg (by dsimp [w, ctWeight]; positivity)]
    exact (hwb u).2
  have hp : ∀ u, 0 < w u := fun u => Real.exp_pos _
  have hb : 0 ≤ Real.exp a - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr ha.le)
  have hz : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη.1
  have hbound := scalarGreen_weight_bound coupling ω
    ((E : ℂ) + (η : ℂ) * Complex.I) hz w (Real.exp (a * N)) (Real.exp a - 1)
    (Real.exp_pos _).le hw hp hb hr (by simpa using hsmall) x y hwy
  have hwx : w x = Real.exp (a * (latticeDistance x y : ℝ)) := by simp [w, ctWeight, N]
  rw [hwx] at hbound
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hbound
  have hdivide : ‖scalarGreen coupling ω x y ((E : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      (2 / η) / Real.exp (a * (latticeDistance x y : ℝ)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [mul_comm] using hbound
  have halower : c * η ≤ a := by
    simpa only [c, div_eq_mul_inv, one_mul, mul_comm] using hlower
  calc
    _ ≤ (2 / η) / Real.exp (a * (latticeDistance x y : ℝ)) := hdivide
    _ = (2 / η) * Real.exp (-a * (latticeDistance x y : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ (2 / η) * Real.exp (-c * η * (latticeDistance x y : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hη.1.le)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right halower (Nat.cast_nonneg (latticeDistance x y))
      nlinarith only [hmul]

end AndersonAC.SolS9
