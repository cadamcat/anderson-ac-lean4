import AndersonAC.AgentS78.Construction.ResetBlock
import AndersonAC.S78.MatrixReset

/-!
# The measurable reset correction solves the reset equation (Proposition 7.4)

`resetTransform_ball_contract`: under the hypotheses of Proposition 7.4
(07-assembly.tex:806–877; `S78.diagonal_reset`) the Taylor map `resetTransform t (M, r)` of
ResetBlock.lean maps the ball of radius `t^{.35δ}` into itself and is a `1/2`-contraction there
(the proof of `SolS78.reset_of_taylor`, with the uniform Taylor remainder
`SolS78.reset_taylor_proof` and the numerical smallness `SolS78.reset_numerical_smallness`).
Hence (`resetCorrection_fixedPoint`) the measurable Picard limit `resetCorrection t (M, r)` is
the reset correction: `‖ζ‖ ≤ t^{.35δ}` and `g'_ii = r_i + ζ_i` (`resetCorrection_solves`).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **Ball invariance and contraction of the reset map.** -/
theorem resetTransform_ball_contract (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ),
      0 < t → t < t₀ → (∀ i j, M i j = M j i ∧ (M i j).im = 0) →
      (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ ‖r i‖ ≤ C) →
      (∀ i, (resetInverse M r t i i).im ≤ C) →
      matrixNorm (squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t)) < 1 / 2 →
      (∀ v : ι → ℂ, ‖((1 - squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t))⁻¹).mulVec v‖ ≤
        C * Real.log (1 / t) * ‖v‖) →
      ‖resetLag M r t‖ ≤ t ^ (0.36 * delta) →
      (∀ z, ‖z‖ ≤ t ^ (0.35 * delta) → ‖resetTransform t (M, r) z‖ ≤ t ^ (0.35 * delta)) ∧
      (∀ z w, ‖z‖ ≤ t ^ (0.35 * delta) → ‖w‖ ≤ t ^ (0.35 * delta) →
        ‖resetTransform t (M, r) z - resetTransform t (M, r) w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖) := by
  obtain ⟨CT, aT, hCT, haT, htaylor⟩ := AndersonAC.SolS78.reset_taylor_proof c C hc hC
  set B := max C CT with hBdef
  have hB : 1 ≤ B := hC.trans (le_max_left _ _)
  have hδ : 0 < delta := by norm_num [delta]
  obtain ⟨tB, htB, hnum⟩ := AndersonAC.SolS78.reset_numerical_smallness B delta hB hδ
  obtain ⟨tA, htA, hrad⟩ := AndersonAC.SolS78.reset_radius_small (0.35 * delta) aT
    (by positivity) haT
  refine ⟨min tB (min tA 1), lt_min htB (lt_min htA one_pos), ?_⟩
  intro ι _ _ _ M r t ht hlt hM hr hdiag hK hP hlag
  have htB' : t < tB := hlt.trans_le (min_le_left _ _)
  have htA' : t < tA := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht1 : t < 1 := hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hL, himage, hsmall⟩ := hnum t ht htB'
  have hρa : t ^ (0.35 * delta) ≤ aT := hrad t ht htA'
  obtain ⟨R, hRexp, hRnorm, hRlip⟩ :=
    htaylor ι M r t ht hM (fun i => ⟨(hr i).1, (hr i).2.1, hdiag i⟩)
  set K := squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t) with hKdef
  set P := (1 - K)⁻¹ with hPdef
  set ρ := t ^ (0.35 * delta) with hρdef
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg ht.le _
  have hlog : 0 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]; exact neg_nonneg.mpr (Real.log_nonpos ht.le ht1.le)
  have hPB : ∀ v : ι → ℂ, ‖P.mulVec v‖ ≤ B * Real.log (1 / t) * ‖v‖ := fun v =>
    (hP v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C CT) hlog) (norm_nonneg v))
  -- the reset map on the ball is `P (lag + R z)`
  have hT : ∀ z, ‖z‖ ≤ ρ → resetTransform t (M, r) z = P.mulVec (resetLag M r t + R z) := by
    intro z hz
    have hexp : (fun i => resetInverse M (r + z) t i i) =
        (fun i => resetInverse M r t i i) + K.mulVec z + R z := hRexp z (hz.trans hρa)
    unfold resetTransform
    simp only
    congr 1
    funext i
    have hi := congrFun hexp i
    simp only [Pi.add_apply] at hi
    simp only [resetLag, Pi.add_apply, ← hKdef]
    rw [hi]
    ring
  constructor
  · intro z hz
    rw [hT z hz]
    have hRz : ‖R z‖ ≤ B * ρ ^ 2 := by
      have hs : ‖z‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [norm_nonneg z]
      exact (hRnorm z (hz.trans hρa)).trans (mul_le_mul (le_max_right C CT) hs (sq_nonneg _)
        (by linarith))
    calc ‖P.mulVec (resetLag M r t + R z)‖ ≤ B * Real.log (1 / t) * ‖resetLag M r t + R z‖ :=
          hPB _
      _ ≤ B * Real.log (1 / t) * (t ^ (0.36 * delta) + B * ρ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hL
          exact (norm_add_le _ _).trans (add_le_add hlag hRz)
      _ ≤ ρ := himage
  · intro z w hz hw
    rw [hT z hz, hT w hw, ← Matrix.mulVec_sub, add_sub_add_left_eq_sub]
    calc ‖P.mulVec (R z - R w)‖ ≤ B * Real.log (1 / t) * ‖R z - R w‖ := hPB _
      _ ≤ B * Real.log (1 / t) * (B * ρ * ‖z - w‖) := by
          apply mul_le_mul_of_nonneg_left _ hL
          refine (hRlip ρ z w hρ0 hρa hz hw).trans ?_
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_right C CT) hρ0
      _ = (B * Real.log (1 / t) * B * ρ) * ‖z - w‖ := by ring
      _ ≤ (1 / 2) * ‖z - w‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)

/-- **The measurable reset correction solves the reset equation.** -/
theorem resetCorrection_solves {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hK : matrixNorm (squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t)) < 1 / 2)
    (hball : ∀ z, ‖z‖ ≤ t ^ (0.35 * delta) → ‖resetTransform t (M, r) z‖ ≤ t ^ (0.35 * delta))
    (hcontract : ∀ z w, ‖z‖ ≤ t ^ (0.35 * delta) → ‖w‖ ≤ t ^ (0.35 * delta) →
      ‖resetTransform t (M, r) z - resetTransform t (M, r) w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖) :
    ‖resetCorrection t (M, r)‖ ≤ t ^ (0.35 * delta) ∧
      ∀ i, resetInverse M (r + resetCorrection t (M, r)) t i i =
        (r + resetCorrection t (M, r)) i := by
  obtain ⟨hζ, hfix⟩ := resetCorrection_fixedPoint t ht (M, r) hball hcontract
  refine ⟨hζ, ?_⟩
  set ζ := resetCorrection t (M, r)
  set K := squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t) with hKdef
  have hP : (1 - K) * (1 - K)⁻¹ = 1 := AndersonAC.SolS78.reset_linear_inverse K hK
  have h := congrArg ((1 - K).mulVec) hfix
  unfold resetTransform at h
  simp only at h
  rw [Matrix.mulVec_mulVec, ← hKdef, hP, Matrix.one_mulVec] at h
  intro i
  have hi := congrFun h i
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at hi
  simp only [Pi.add_apply]
  linear_combination hi

end AndersonAC.AgentS78
