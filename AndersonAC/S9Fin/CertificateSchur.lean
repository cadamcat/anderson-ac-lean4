import AndersonAC.S9Fin.SchurProof
import AndersonAC.S9Fin.Columns

noncomputable section
open AndersonAC.S9

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply the general block inverse to the certified matrix. Damping has
support only in the active block, so the eliminated block is unchanged. -/
lemma certified_active_inverse (H : Matrix n n ℂ) (E η : ℝ)
    (A : Finset n) (r : n → ℂ) (G : Matrix n n ℂ)
    (hMG : (H - (E : ℂ) • 1 - (η : ℂ) •
      Matrix.diagonal (fun i => if i ∈ A then r i else 0)) * G = 1)
    (hprincipal : allPrincipalInvertible H E) :
    compress A G =
      (activeSchur H E A - (η : ℂ) • Matrix.diagonal (fun i : A => r i))⁻¹ := by
  let R := (η : ℂ) • Matrix.diagonal (fun i => if i ∈ A then r i else 0)
  let H' := H - R
  let Ac := Finset.univ \ A
  have hAc (i : Ac) : (i : n) ∉ A := (Finset.mem_sdiff.mp i.property).2
  have hRA : compress A R = (η : ℂ) • Matrix.diagonal (fun i : A => r i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [compress, R, Matrix.diagonal_apply, i.property]
    · have hne : (i : n) ≠ (j : n) := fun h => hij (Subtype.ext h)
      simp [compress, R, Matrix.diagonal_apply, hij, hne]
  have hRAC : R.submatrix (fun i : A => (i : n)) (fun j : Ac => (j : n)) = 0 := by
    ext i j
    have hne : (i : n) ≠ (j : n) := by
      intro h; exact hAc j (h ▸ i.property)
    simp [R, Matrix.diagonal_apply, hne]
  have hRCA : R.submatrix (fun i : Ac => (i : n)) (fun j : A => (j : n)) = 0 := by
    ext i j
    have hne : (i : n) ≠ (j : n) := by
      intro h; exact hAc i (h.symm ▸ j.property)
    simp [R, Matrix.diagonal_apply, hne]
  have hRC : compress Ac R = 0 := by
    ext i j
    simp [compress, R, Matrix.diagonal_apply, hAc]
  have hswap : H' - (E : ℂ) • 1 = H - (E : ℂ) • 1 - R := by
    dsimp [H']; abel
  have hD : compress Ac (H' - (E : ℂ) • 1) = compress Ac (H - (E : ℂ) • 1) := by
    rw [hswap]
    change compress Ac (H - (E : ℂ) • 1) - compress Ac R = _
    rw [hRC, sub_zero]
  have hS : activeSchur H' E A =
      activeSchur H E A - (η : ℂ) • Matrix.diagonal (fun i : A => r i) := by
    have hAC : (H' - (E : ℂ) • 1).submatrix
        (fun i : A => (i : n)) (fun j : Ac => (j : n)) =
        (H - (E : ℂ) • 1).submatrix
          (fun i : A => (i : n)) (fun j : Ac => (j : n)) := by
      rw [hswap, Matrix.submatrix_sub]
      change _ - R.submatrix (fun i : A => (i : n)) (fun j : Ac => (j : n)) = _
      rw [hRAC, sub_zero]
    have hCA : (H' - (E : ℂ) • 1).submatrix
        (fun i : Ac => (i : n)) (fun j : A => (j : n)) =
        (H - (E : ℂ) • 1).submatrix
          (fun i : Ac => (i : n)) (fun j : A => (j : n)) := by
      rw [hswap, Matrix.submatrix_sub]
      change _ - R.submatrix (fun i : Ac => (i : n)) (fun j : A => (j : n)) = _
      rw [hRCA, sub_zero]
    have hAA : compress A (H' - (E : ℂ) • 1) =
        compress A (H - (E : ℂ) • 1) - (η : ℂ) • Matrix.diagonal (fun i : A => r i) := by
      rw [hswap]
      change compress A (H - (E : ℂ) • 1) - compress A R = _
      rw [hRA]
    unfold activeSchur
    change compress A (H' - (E : ℂ) • 1) -
      (H' - (E : ℂ) • 1).submatrix (fun i : A => (i : n)) (fun j : Ac => (j : n)) *
      (compress Ac (H' - (E : ℂ) • 1))⁻¹ *
      (H' - (E : ℂ) • 1).submatrix (fun i : Ac => (i : n)) (fun j : A => (j : n)) = _
    rw [hAA, hAC, hCA, hD]
    dsimp [Ac]
    abel
  have hM : IsUnit (H' - (E : ℂ) • 1) := by
    exact (H' - (E : ℂ) • 1).isUnit_iff_isUnit_det.mpr
      (Matrix.isUnit_det_of_right_inverse (by simpa only [hswap] using hMG))
  have hG : G = (H' - (E : ℂ) • 1)⁻¹ := by
    apply (Matrix.inv_eq_right_inv _).symm
    simpa only [hswap] using hMG
  obtain ⟨_, hInv⟩ := schurCompression_proof n H' E A hM (by
    change IsUnit (compress Ac (H' - (E : ℂ) • 1))
    rw [hD]
    exact hprincipal Ac)
  rw [hG, ← hInv, hS]

end AndersonAC.SolS9
