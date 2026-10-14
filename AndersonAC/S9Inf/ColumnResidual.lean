import AndersonAC.S9Inf.ColumnLift
import AndersonAC.S9Inf.CubeShellStatement

/-! The residual of the lifted finite column is a boundary-layer vector. -/

noncomputable section

open OAI.Anderson AndersonAC.S9 AndersonAC.SolS9

namespace AndersonAC.SolS9Inf

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def inShell {d : ℕ} (R : ℕ) (x : Site d) : Prop :=
  (∀ j : Fin d, |x j| ≤ (R : ℤ) + 1) ∧ ∃ j : Fin d, (R : ℤ) ≤ |x j|

theorem abs_coordinate_le {d : ℕ} (x y : Site d)
    (hstep : ∀ j, |x j - y j| ≤ 1) (j : Fin d) : |x j| ≤ |y j| + 1 := by
  calc
    |x j| = |(x j - y j) + y j| := by congr 1; ring
    _ ≤ |x j - y j| + |y j| := abs_add_le _ _
    _ ≤ |y j| + 1 := by linarith [hstep j]

theorem cube_cross_shell {d : ℕ} (R : ℕ) (x y : Site d)
    (hstep : ∀ j, |x j - y j| ≤ 1)
    (hcross : (inCube R x ∧ ¬ inCube R y) ∨ (¬ inCube R x ∧ inCube R y)) :
    inShell R x := by
  have hrev : ∀ j, |y j - x j| ≤ 1 := by
    intro j
    simpa only [abs_sub_comm] using hstep j
  rcases hcross with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · refine ⟨fun j => (hx j).trans (by omega), ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, (R : ℤ) < |y j| := by simpa [inCube] using hy
    exact ⟨j, by have h := abs_coordinate_le y x hrev j; omega⟩
  · refine ⟨fun j => (abs_coordinate_le x y hstep j).trans (by linarith [hy j]), ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, (R : ℤ) < |x j| := by simpa [inCube] using hx
    exact ⟨j, hj.le⟩

theorem inCube_off_shell {d : ℕ} (R : ℕ) (x : Site d) (hx : ¬ inShell R x)
    (y : Site d) (hstep : ∀ j, |x j - y j| ≤ 1) : inCube R y ↔ inCube R x := by
  constructor
  · intro hy
    by_contra hn
    exact hx (cube_cross_shell R x y hstep (Or.inr ⟨hn, hy⟩))
  · intro hx'
    by_contra hn
    exact hx (cube_cross_shell R x y hstep (Or.inl ⟨hx', hn⟩))

theorem basis_step_bound {d : ℕ} (x : Site d) (j : Fin d) :
    (∀ k, |x k - (x + basisVector j) k| ≤ 1) ∧
    (∀ k, |x k - (x - basisVector j) k| ≤ 1) := by
  classical
  constructor <;> intro k <;>
    by_cases h : k = j <;> simp [basisVector, h]

def columnResidual {d m : ℕ} (R : ℕ) (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (v : Torus d m → ℂ) : StateSpace d :=
  (hamiltonian coupling ω - z • (1 : StateSpace d →L[ℂ] StateSpace d))
    (columnLift R v) - basis 0

theorem columnResidual_inside {d m : ℕ} (R : ℕ) (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (v : Torus d m → ℂ) (x : Site d) (hx : inCube R x)
    (heq : -(∑ j : Fin d, (v (torusSite (x + basisVector j)) +
      v (torusSite (x - basisVector j)))) +
      ((coupling * potential ω x : ℂ) - z) * v (torusSite x) =
        if x = 0 then 1 else 0) :
    columnResidual R coupling ω z v x = ∑ j : Fin d, (
      (if inCube R (x + basisVector j) then 0 else v (torusSite (x + basisVector j))) +
      (if inCube R (x - basisVector j) then 0 else v (torusSite (x - basisVector j)))) := by
  classical
  have hdiff (y : Site d) : v (torusSite y) - columnLift R v y =
      if inCube R y then 0 else v (torusSite y) := by
    by_cases hy : inCube R y <;> simp [hy]
  calc
    _ = (∑ j : Fin d, (v (torusSite (x + basisVector j)) +
          v (torusSite (x - basisVector j)))) -
        ∑ j : Fin d, (columnLift R v (x + basisVector j) +
          columnLift R v (x - basisVector j)) := by
      simp only [columnResidual, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, lp.coeFn_sub, lp.coeFn_smul,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hamiltonian_apply, basis, lp.single_apply,
        Pi.single_apply, columnLift_apply, if_pos hx]
      rw [← heq]
      ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [show (v (torusSite (x + basisVector j)) + v (torusSite (x - basisVector j))) -
          (columnLift R v (x + basisVector j) + columnLift R v (x - basisVector j)) =
          (v (torusSite (x + basisVector j)) - columnLift R v (x + basisVector j)) +
          (v (torusSite (x - basisVector j)) - columnLift R v (x - basisVector j)) by ring]
      rw [hdiff, hdiff]

theorem columnResidual_outside {d m : ℕ} (R : ℕ) (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (v : Torus d m → ℂ) (x : Site d) (hx : ¬ inCube R x) :
    columnResidual R coupling ω z v x =
      -(∑ j : Fin d, (columnLift R v (x + basisVector j) +
        columnLift R v (x - basisVector j))) := by
  classical
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (by simp [inCube])
  simp only [columnResidual, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, lp.coeFn_sub, lp.coeFn_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hamiltonian_apply]
  simp [hx, hx0, basis, lp.single_apply, Pi.single_apply]

theorem actual_column_equation {d m : ℕ} (coupling E η : ℝ) (hη : 0 < η)
    (ωm : TorusConfiguration d m) (ω : Configuration d) (hmatch : rootCubeMatch ωm ω)
    (x : Site d) (hx : inCube (sideLength m / 4) x) :
    -(∑ j : Fin d, (
      matrixResolvent (periodicHamiltonian coupling ωm) E η (torusSite (x + basisVector j)) 0 +
      matrixResolvent (periodicHamiltonian coupling ωm) E η (torusSite (x - basisVector j)) 0)) +
      ((coupling * potential ω x : ℂ) - ((E : ℂ) + η * Complex.I)) *
        matrixResolvent (periodicHamiltonian coupling ωm) E η (torusSite x) 0 =
          if x = 0 then 1 else 0 := by
  have h := finite_column_equation coupling E η hη ωm (torusSite x)
  rw [hmatch x hx] at h
  simpa only [torusSite_add_basis, torusSite_sub_basis, torusSite_eq_zero_iff x hx] using h

theorem columnResidual_support {d m : ℕ} (coupling E η : ℝ) (hη : 0 < η)
    (ωm : TorusConfiguration d m) (ω : Configuration d) (hmatch : rootCubeMatch ωm ω)
    (x : Site d) (hx : ¬ inShell (sideLength m / 4) x) :
    columnResidual (sideLength m / 4) coupling ω ((E : ℂ) + η * Complex.I)
      (fun q => matrixResolvent (periodicHamiltonian coupling ωm) E η q 0) x = 0 := by
  classical
  have hp (j : Fin d) := inCube_off_shell (sideLength m / 4) x hx
    (x + basisVector j) (basis_step_bound x j).1
  have hm (j : Fin d) := inCube_off_shell (sideLength m / 4) x hx
    (x - basisVector j) (basis_step_bound x j).2
  by_cases hc : inCube (sideLength m / 4) x
  · rw [columnResidual_inside (m := m) (sideLength m / 4) coupling ω
      ((E : ℂ) + η * Complex.I)
      (fun q => matrixResolvent (periodicHamiltonian coupling ωm) E η q 0) x hc
      (actual_column_equation coupling E η hη ωm ω hmatch x hc)]
    simp [hp, hm, hc]
  · rw [columnResidual_outside (m := m) (sideLength m / 4) coupling ω
      ((E : ℂ) + η * Complex.I)
      (fun q => matrixResolvent (periodicHamiltonian coupling ωm) E η q 0) x hc]
    simp [hp, hm, hc]

theorem columnResidual_norm_le {d m : ℕ} (R : ℕ) (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (v : Torus d m → ℂ) (B : ℝ) (hB : 0 ≤ B) (hv : ∀ q, ‖v q‖ ≤ B)
    (heq : ∀ x, inCube R x →
      -(∑ j : Fin d, (v (torusSite (x + basisVector j)) +
        v (torusSite (x - basisVector j)))) +
        ((coupling * potential ω x : ℂ) - z) * v (torusSite x) =
          if x = 0 then 1 else 0) (x : Site d) :
    ‖columnResidual R coupling ω z v x‖ ≤ 2 * (d : ℝ) * B := by
  have hcut (y : Site d) :
      ‖if inCube R y then 0 else v (torusSite y)‖ ≤ B := by
    by_cases hy : inCube R y <;> simp only [hy, ite_true, ite_false, norm_zero]
    · exact hB
    · exact hv _
  have hlift (y : Site d) : ‖columnLift R v y‖ ≤ B := by
    rw [columnLift_apply]
    by_cases hy : inCube R y <;> simp only [hy, ite_true, ite_false, norm_zero]
    · exact hv _
    · exact hB
  have hsum (f g : Fin d → ℂ) (hf : ∀ j, ‖f j‖ ≤ B) (hg : ∀ j, ‖g j‖ ≤ B) :
      ‖∑ j, (f j + g j)‖ ≤ 2 * (d : ℝ) * B := by
    calc
      _ ≤ ∑ j, ‖f j + g j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, (B + B) := Finset.sum_le_sum (fun j _ =>
        (norm_add_le _ _).trans (add_le_add (hf j) (hg j)))
      _ = _ := by simp; ring
  by_cases hx : inCube R x
  · rw [columnResidual_inside _ _ _ _ _ x hx (heq x hx)]
    exact hsum _ _ (fun j => hcut _) (fun j => hcut _)
  · rw [columnResidual_outside _ _ _ _ _ x hx, norm_neg]
    exact hsum _ _ (fun j => hlift _) (fun j => hlift _)

theorem actual_columnResidual_norm_le {d m : ℕ} (coupling E η : ℝ) (hη : 0 < η)
    (ωm : TorusConfiguration d m) (ω : Configuration d) (hmatch : rootCubeMatch ωm ω)
    (x : Site d) :
    ‖columnResidual (sideLength m / 4) coupling ω ((E : ℂ) + η * Complex.I)
      (fun q => matrixResolvent (periodicHamiltonian coupling ωm) E η q 0) x‖ ≤
        2 * (d : ℝ) * η⁻¹ :=
  columnResidual_norm_le _ _ _ _ _ η⁻¹ (inv_nonneg.mpr hη.le)
    (finite_column_entry_bound coupling E η hη ωm)
    (actual_column_equation coupling E η hη ωm ω hmatch) x

end AndersonAC.SolS9Inf
