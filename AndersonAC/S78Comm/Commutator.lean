import Mathlib

noncomputable section

namespace AndersonAC.SolS78

theorem reset_commutator_proof {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : Matrix ι ι ℂ) (z : ι → ℂ) (f : ι → ℝ)
    (hh : IsUnit h.det) (hnew : IsUnit (h⁻¹ - Matrix.diagonal z).det) :
    let F := Matrix.diagonal (fun i => (f i : ℂ))
    let h' := (h⁻¹ - Matrix.diagonal z)⁻¹
    F * h' - h' * F = (1 - h * Matrix.diagonal z)⁻¹ * (F * h - h * F) *
      (1 - Matrix.diagonal z * h)⁻¹ := by
  let F : Matrix ι ι ℂ := Matrix.diagonal (fun i => (f i : ℂ))
  let Z : Matrix ι ι ℂ := Matrix.diagonal z
  let A : Matrix ι ι ℂ := h⁻¹ - Z
  let H : Matrix ι ι ℂ := A⁻¹
  change F * H - H * F = (1 - h * Z)⁻¹ * (F * h - h * F) * (1 - Z * h)⁻¹

  have hinv_mul_h : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h hh
  have h_mul_hinv : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hh
  have hA_mul_H : A * H = 1 := by
    dsimp [H]
    exact Matrix.mul_nonsing_inv A hnew
  have hH_mul_A : H * A = 1 := by
    dsimp [H]
    exact Matrix.nonsing_inv_mul A hnew

  have hFZ : F * Z = Z * F := by
    dsimp [F, Z]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)

  have hAcomm : A * F - F * A = h⁻¹ * F - F * h⁻¹ := by
    change (h⁻¹ - Z) * F - F * (h⁻¹ - Z) = h⁻¹ * F - F * h⁻¹
    calc
      (h⁻¹ - Z) * F - F * (h⁻¹ - Z) =
          h⁻¹ * F - Z * F - (F * h⁻¹ - F * Z) := by rw [sub_mul, mul_sub]
      _ = h⁻¹ * F - F * h⁻¹ := by rw [hFZ]; abel

  have hcomm : F * H - H * F = H * (A * F - F * A) * H := by
    calc
      F * H - H * F = (H * A) * F * H - H * F * (A * H) := by
        rw [hH_mul_A, hA_mul_H]
        simp
      _ = H * (A * F - F * A) * H := by noncomm_ring

  have hinner : h⁻¹ * F - F * h⁻¹ = h⁻¹ * (F * h - h * F) * h⁻¹ := by
    calc
      h⁻¹ * F - F * h⁻¹ =
          (h⁻¹ * F) * (h * h⁻¹) - (h⁻¹ * h) * (F * h⁻¹) := by
        simp [hinv_mul_h, h_mul_hinv]
      _ = h⁻¹ * (F * h - h * F) * h⁻¹ := by noncomm_ring

  have hleft : (1 - h * Z)⁻¹ = H * h⁻¹ := by
    apply Matrix.inv_eq_left_inv
    calc
      (H * h⁻¹) * (1 - h * Z) = H * (h⁻¹ * (1 - h * Z)) := by
        rw [Matrix.mul_assoc]
      _ = H * (h⁻¹ - (h⁻¹ * h) * Z) := by
        simp only [mul_sub, mul_one, Matrix.mul_assoc]
      _ = H * (h⁻¹ - Z) := by rw [hinv_mul_h, one_mul]
      _ = 1 := by simpa [A] using hH_mul_A

  have hright : (1 - Z * h)⁻¹ = h⁻¹ * H := by
    apply Matrix.inv_eq_right_inv
    calc
      (1 - Z * h) * (h⁻¹ * H) = ((1 - Z * h) * h⁻¹) * H := by
        rw [Matrix.mul_assoc]
      _ = (h⁻¹ - Z) * H := by
        congr 1
        calc
          (1 - Z * h) * h⁻¹ = 1 * h⁻¹ - (Z * h) * h⁻¹ := by rw [sub_mul]
          _ = h⁻¹ - Z * (h * h⁻¹) := by rw [one_mul, Matrix.mul_assoc]
          _ = h⁻¹ - Z := by rw [h_mul_hinv, mul_one]
      _ = 1 := by simpa [A] using hA_mul_H

  calc
    F * H - H * F = H * (A * F - F * A) * H := hcomm
    _ = H * (h⁻¹ * F - F * h⁻¹) * H := by rw [hAcomm]
    _ = (H * h⁻¹) * (F * h - h * F) * (h⁻¹ * H) := by
      rw [hinner]
      noncomm_ring
    _ = (1 - h * Z)⁻¹ * (F * h - h * F) * (1 - Z * h)⁻¹ := by
      rw [← hleft, ← hright]

end AndersonAC.SolS78
