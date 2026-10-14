import AndersonAC.Blueprint.Interfaces

/-! deletion package minimal join: the exact one-site inverse update (Sherman–Morrison
for a diagonal rank-one change), `Packages.deletion`. Sorry-free. -/

noncomputable section
open Matrix

namespace AndersonAC.OpusS45

open AndersonAC.Blueprint

theorem diag_single_eq {N : ℕ} (x : Fin N) (v : ℂ) :
    Matrix.diagonal (fun i => if i = x then v else 0) = Matrix.single x x v := by
  ext i j
  by_cases hij : i = j
  · subst hij; by_cases hix : i = x
    · subst hix; simp
    · simp [hix, Matrix.single, Ne.symm hix]
  · simp [Matrix.single, hij]
    intro h1 h2; exact absurd (h1.symm.trans h2) hij

theorem single_mul_mul_single_self {N : ℕ} (x : Fin N) (v : ℂ) (G : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.single x x v * G * Matrix.single x x v = (v * G x x) • Matrix.single x x v := by
  rw [Matrix.single_mul_mul_single, Matrix.smul_single, smul_eq_mul]

theorem update_eq {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (x : Fin N) (v : ℂ) :
    (fun i j => G i j - v * G i x * G x j / (1 + v * G x x)) =
      G - (1 + v * G x x)⁻¹ • (G * Matrix.single x x v * G) := by
  ext i j
  have hentry : (G * Matrix.single x x v * G) i j = G i x * v * G x j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · rw [Matrix.mul_single_apply_same]
    · intro b _ hb; rw [Matrix.mul_single_apply_of_ne (hbj := hb), zero_mul]
    · simp
  rw [Matrix.sub_apply, Matrix.smul_apply, hentry, smul_eq_mul]
  ring

theorem deletion_proof : DeletionInput := by
  intro N A G hAG x v hs
  obtain ⟨h1, h2⟩ := hAG
  rw [diag_single_eq, update_eq]
  set E := Matrix.single x x v with hE
  set s := 1 + v * G x x with hs_def
  have hEGE : E * G * E = (v * G x x) • E := single_mul_mul_single_self x v G
  have hcoef : (1 : ℂ) - s⁻¹ - s⁻¹ * (v * G x x) = 0 := by
    have : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
    rw [hs_def] at this ⊢
    linear_combination -this
  constructor
  · calc (A + E) * (G - s⁻¹ • (G * E * G))
        = A * G + E * G - s⁻¹ • (A * G * E * G) - s⁻¹ • (E * G * E * G) := by
          simp only [add_mul, mul_sub, Matrix.mul_smul, Matrix.mul_assoc]; abel
      _ = 1 + E * G - s⁻¹ • (E * G) - s⁻¹ • ((v * G x x) • (E * G)) := by
          rw [h1, hEGE, Matrix.one_mul, Matrix.smul_mul]
      _ = 1 + ((1 : ℂ) - s⁻¹ - s⁻¹ * (v * G x x)) • (E * G) := by
          rw [smul_smul, sub_smul, sub_smul, one_smul]; abel
      _ = 1 := by rw [hcoef, zero_smul, add_zero]
  · calc (G - s⁻¹ • (G * E * G)) * (A + E)
        = G * A + G * E - s⁻¹ • (G * E * (G * A)) - s⁻¹ • (G * E * G * E) := by
          simp only [mul_add, sub_mul, Matrix.smul_mul, Matrix.mul_assoc]; abel
      _ = 1 + G * E - s⁻¹ • (G * E) - s⁻¹ • ((v * G x x) • (G * E)) := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc (G * E) G E, Matrix.mul_assoc G E (G * E),
            ← Matrix.mul_assoc E G E, hEGE, Matrix.mul_smul]
      _ = 1 + ((1 : ℂ) - s⁻¹ - s⁻¹ * (v * G x x)) • (G * E) := by
          rw [smul_smul, sub_smul, sub_smul, one_smul]; abel
      _ = 1 := by rw [hcoef, zero_smul, add_zero]

end AndersonAC.OpusS45

theorem AndersonAC.Blueprint.Packages.deletion : AndersonAC.Blueprint.DeletionInput :=
  AndersonAC.OpusS45.deletion_proof

