import AndersonAC.S9Inf.Nonvanishing

/-! Absorption of a bounded commutator in the weighted resolvent equation. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem weighted_green_estimate (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) (W D : K →L[ℂ] K)
    (hcomm : ∀ v : K,
      (T - z • (1 : K →L[ℂ] K)) (W v) =
        W ((T - z • (1 : K →L[ℂ] K)) v) + D (W v))
    (hD : ‖D‖ ≤ z.im / 2) (v : K) :
    ‖W (green T z v)‖ ≤ 2 / z.im * ‖W v‖ := by
  let q := green T z v
  have heq : W q = green T z (W v + D (W q)) := by
    have heq := hcomm q
    have hq : (T - z • (1 : K →L[ℂ] K)) q = v := by
      simpa only [q, green] using
        unit_inverse_apply_left _ (shifted_isUnit T hT z hz.ne') v
    rw [hq] at heq
    have h : green T z ((T - z • (1 : K →L[ℂ] K)) (W q)) = W q :=
      unit_inverse_apply_right _ (shifted_isUnit T hT z hz.ne') (W q)
    rw [heq] at h
    exact h.symm
  have hbound : ‖W q‖ ≤ (‖W v‖ + (z.im / 2) * ‖W q‖) / z.im := by
    calc
      ‖W q‖ = ‖green T z (W v + D (W q))‖ := congrArg norm heq
      _ ≤ ‖W v + D (W q)‖ / z.im := norm_green_apply_le T hT z hz _
      _ ≤ (‖W v‖ + ‖D (W q)‖) / z.im :=
        div_le_div_of_nonneg_right (norm_add_le _ _) hz.le
      _ ≤ (‖W v‖ + (z.im / 2) * ‖W q‖) / z.im := by
        apply div_le_div_of_nonneg_right _ hz.le
        exact add_le_add le_rfl
          ((D.le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
  have hscaled := (le_div_iff₀ hz).mp hbound
  have hh : ‖W q‖ ≤ (2 * ‖W v‖) / z.im := by
    apply (le_div_iff₀ hz).mpr
    nlinarith only [hscaled]
  simpa only [q, div_mul_eq_mul_div] using hh

end AndersonAC.SolS9Inf
