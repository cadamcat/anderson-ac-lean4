import Mathlib
import AndersonAC.S78.Contraction

open Matrix
set_option autoImplicit false

namespace AndersonAC.SolS78

/-- The quantitative contraction step in Proposition 7.4. `diagonal` is the
resolvent diagonal at r+z, and K is its first derivative. The remainder and
inverse bounds must be established from the damped matrix before applying this
lemma. All vector norms are the finite sup norm. -/
theorem reset_of_taylor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (diagonal : (ι → ℂ) → ι → ℂ) (r : ι → ℂ)
    (K P : Matrix ι ι ℂ) (R : (ι → ℂ) → ι → ℂ) (a L C : ℝ)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hP : (1 - K) * P = 1)
    (hnorm : ∀ v : ι → ℂ, ‖P.mulVec v‖ ≤ L * ‖v‖)
    (htaylor : ∀ z, ‖z‖ ≤ a → diagonal z = diagonal 0 + K.mulVec z + R z)
    (hR : ∀ z, ‖z‖ ≤ a → ‖R z‖ ≤ C * ‖z‖ ^ 2)
    (hRlip : ∀ z w, ‖z‖ ≤ a → ‖w‖ ≤ a → ‖R z - R w‖ ≤ C * a * ‖z - w‖)
    (himage : L * (‖diagonal 0 - r‖ + C * a ^ 2) ≤ a)
    (hsmall : L * C * a ≤ 1 / 2) :
    ∃ ζ : ι → ℂ, ‖ζ‖ ≤ a ∧ diagonal ζ = r + ζ := by
  let e := diagonal 0 - r
  let F : (ι → ℂ) → ι → ℂ := fun z => P.mulVec (e + R z)
  have hball : ∀ z, ‖z‖ ≤ a → ‖F z‖ ≤ a := by
    intro z hz
    have hs : ‖z‖ ^ 2 ≤ a ^ 2 := by nlinarith [norm_nonneg z]
    calc
      ‖F z‖ ≤ L * ‖e + R z‖ := hnorm _
      _ ≤ L * (‖e‖ + ‖R z‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hL
      _ ≤ L * (‖e‖ + C * a ^ 2) := by
        gcongr
        exact (hR z hz).trans (mul_le_mul_of_nonneg_left hs hC)
      _ ≤ a := himage
  have hcontract : ∀ z w, ‖z‖ ≤ a → ‖w‖ ≤ a →
      ‖F z - F w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖ := by
    intro z w hz hw
    have heq : F z - F w = P.mulVec (R z - R w) := by
      dsimp [F]
      rw [← Matrix.mulVec_sub]
      congr 1
      abel
    rw [heq]
    calc
      ‖P.mulVec (R z - R w)‖ ≤ L * ‖R z - R w‖ := hnorm _
      _ ≤ L * (C * a * ‖z - w‖) := mul_le_mul_of_nonneg_left (hRlip z w hz hw) hL
      _ = (L * C * a) * ‖z - w‖ := by ring
      _ ≤ (1 / 2) * ‖z - w‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  obtain ⟨ζ, hζ, hfixed⟩ := fixedPoint_closedBall F 0 a ha
    (by simpa only [sub_zero] using hball) (by simpa only [sub_zero] using hcontract)
  have hz : ‖ζ‖ ≤ a := by simpa only [sub_zero] using hζ
  have hlinear : ζ - K.mulVec ζ = e + R ζ := by
    have h := congrArg ((1 - K).mulVec) hfixed
    dsimp [F] at h
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec] at h
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using h.symm
  refine ⟨ζ, hz, ?_⟩
  rw [htaylor ζ hz]
  calc
    diagonal 0 + K.mulVec ζ + R ζ = r + K.mulVec ζ + (e + R ζ) := by dsimp [e]; abel
    _ = r + K.mulVec ζ + (ζ - K.mulVec ζ) := by rw [← hlinear]
    _ = r + ζ := by abel

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.reset_of_taylor
