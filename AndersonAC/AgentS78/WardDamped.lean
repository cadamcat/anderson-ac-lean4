import AndersonAC.AgentS78.S45Join

/-!
§2 Ward identity (02-state.tex:248–262) for a damped real terminal-Schur endpoint:
the inverse `G = (M - t diag r)⁻¹` of a real symmetric `M` is complex symmetric and
satisfies `t G diag(Im r) Gᴴ = Im G`. Consequently every `IsDampedEndpoint` gives an
S45 state (`toS45`) with `g.IsSymm` and `ward t`, the hypotheses of the S45↔S78
form transport (`AgentS78/S45Join.lean`) and of `S45.ordinary_sweep_endpoint`.
-/

open scoped BigOperators
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem ward_of_inverse (M : Matrix κ κ ℂ) (hM : ∀ i j, M i j = M j i ∧ (M i j).im = 0)
    (r : κ → ℂ) (G : Matrix κ κ ℂ) (t : ℝ) (ht : 0 ≤ t)
    (h1 : (M - (t : ℂ) • Matrix.diagonal r) * G = 1) (h2 : G * (M - (t : ℂ) • Matrix.diagonal r) = 1) :
    G.IsSymm ∧ (⟨G, r⟩ : AndersonAC.S45.State κ).ward t := by
  set B := M - (t : ℂ) • Matrix.diagonal r with hB
  have hMT : M.transpose = M := by ext i j; exact (hM j i).1
  have hMH : M.conjTranspose = M := by
    ext i j
    simp only [Matrix.conjTranspose_apply]
    rw [(hM j i).1]
    exact Complex.conj_eq_iff_im.mpr (hM i j).2
  have hBT : B.transpose = B := by
    rw [hB, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.diagonal_transpose, hMT]
  have hGT : G.transpose = G := by
    have hl : G.transpose * B = 1 := by
      rw [← hBT, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc G.transpose = G.transpose * (B * G) := by rw [h1, Matrix.mul_one]
      _ = (G.transpose * B) * G := by rw [Matrix.mul_assoc]
      _ = G := by rw [hl, Matrix.one_mul]
  refine ⟨hGT, ?_⟩
  have hBH : B.conjTranspose = M - (t : ℂ) • Matrix.diagonal (fun i => star (r i)) := by
    rw [hB, Matrix.conjTranspose_sub, hMH, Matrix.conjTranspose_smul, Matrix.diagonal_conjTranspose]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rfl
  have h2H : B.conjTranspose * G.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hdI : Matrix.diagonal (fun k => r k - star (r k)) =
      (2 * Complex.I) • Matrix.diagonal (fun k => ((r k).im : ℂ)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rw [show star (r a) = (starRingEnd ℂ) (r a) from rfl, Complex.sub_conj]
      push_cast
      ring
    · simp [Matrix.diagonal_apply, hab]
  have hdiff : B.conjTranspose - B = (t : ℂ) • ((2 * Complex.I) • Matrix.diagonal (fun k => ((r k).im : ℂ))) := by
    rw [← hdI, hBH, hB]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.diagonal_apply]; ring
    · simp [Matrix.diagonal_apply, hab]
  have hkey : G - G.conjTranspose = G * (B.conjTranspose - B) * G.conjTranspose := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2H, Matrix.mul_one, h2, Matrix.one_mul]
  set X := G * Matrix.diagonal (fun k => ((r k).im : ℂ)) * G.conjTranspose with hXdef
  have h3 : G - G.conjTranspose = (2 * Complex.I) • ((t : ℂ) • X) := by
    rw [hkey, hdiff, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_comm]
  have hGji : ∀ i j, G j i = G i j := by
    intro i j
    have := congrFun (congrFun hGT i) j
    simpa [Matrix.transpose_apply] using this
  have hX : (t : ℂ) • X = AndersonAC.S45.matrixIm G := by
    ext i j
    have e := congrFun (congrFun h3 i) j
    simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul] at e
    rw [hGji i j, show star (G i j) = (starRingEnd ℂ) (G i j) from rfl, Complex.sub_conj] at e
    simp only [AndersonAC.S45.matrixIm, Matrix.smul_apply, smul_eq_mul]
    have hI : (2 * Complex.I) ≠ 0 := by simp
    apply mul_left_cancel₀ hI
    push_cast at e
    linear_combination -e
  unfold AndersonAC.S45.State.ward
  rw [← hX]
  simp only [AndersonAC.S45.State.h, AndersonAC.S45.State.p, hXdef]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]

end AndersonAC.AgentS78
