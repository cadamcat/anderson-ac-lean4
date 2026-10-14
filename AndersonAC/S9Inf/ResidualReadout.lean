import AndersonAC.S9Inf.ColumnResidual

/-! Recover the root comparison by applying the infinite inverse to the residual. -/

noncomputable section

open OAI.Anderson AndersonAC.S9 AndersonAC.SolS9

namespace AndersonAC.SolS9Inf

theorem finiteSupport_basis_sum {d : ℕ} (r : StateSpace d) (S : Finset (Site d))
    (hs : ∀ x, x ∉ S → r x = 0) : r = ∑ x ∈ S, (r x) • basis x := by
  classical
  apply lp.ext
  funext x
  simp only [basis, ← lp.single_smul, smul_eq_mul, mul_one, lp.coeFn_sum,
    lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single]
  by_cases hx : x ∈ S
  · simp [hx]
  · simp [hx, hs x hx]

theorem residual_root_bound {d : ℕ} (coupling : ℝ) (ω : Configuration d) (z : ℂ)
    (r : StateSpace d) (S : Finset (Site d)) (hs : ∀ x, x ∉ S → r x = 0)
    (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hgreen : ∀ x ∈ S, ‖scalarGreen coupling ω 0 x z‖ ≤ D)
    (hr : ∀ x ∈ S, ‖r x‖ ≤ B) :
    ‖inner ℂ (basis 0) (green (hamiltonian coupling ω) z r)‖ ≤
      (S.card : ℝ) * D * B := by
  have heq : inner ℂ (basis 0) (green (hamiltonian coupling ω) z r) =
      ∑ x ∈ S, (r x) * scalarGreen coupling ω 0 x z := by
    conv_lhs => rw [finiteSupport_basis_sum r S hs]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, scalarGreen]
  rw [heq]
  calc
    _ ≤ ∑ x ∈ S, ‖(r x) * scalarGreen coupling ω 0 x z‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ S, B * D := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul]
      exact mul_le_mul (hr x hx) (hgreen x hx) (norm_nonneg _) hB
    _ = _ := by simp; ring

theorem root_difference_residual {d m : ℕ} (coupling E η : ℝ) (hη : 0 < η)
    (ωm : TorusConfiguration d m) (ω : Configuration d) :
    matrixResolvent (periodicHamiltonian coupling ωm) E η 0 0 -
      diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I) =
      inner ℂ (basis 0) (green (hamiltonian coupling ω) ((E : ℂ) + η * Complex.I)
        (columnResidual (sideLength m / 4) coupling ω ((E : ℂ) + η * Complex.I)
          (fun q => matrixResolvent (periodicHamiltonian coupling ωm) E η q 0))) := by
  let z : ℂ := (E : ℂ) + η * Complex.I
  let v := fun q => matrixResolvent (periodicHamiltonian coupling ωm) E η q 0
  let u := columnLift (sideLength m / 4) v
  let r := columnResidual (sideLength m / 4) coupling ω z v
  let A := hamiltonian coupling ω - z • (1 : StateSpace d →L[ℂ] StateSpace d)
  have hz : z.im ≠ 0 := by simpa [z] using hη.ne'
  have heq : basis 0 + r = A u := by dsimp [r, columnResidual, A, u]; abel
  have hu : green (hamiltonian coupling ω) z (basis 0 + r) = u := by
    rw [heq]
    exact unit_inverse_apply_right A (shifted_isUnit _
      (hamiltonian_isSelfAdjoint coupling ω) z hz) u
  have hroot := congrArg (fun q : StateSpace d => inner ℂ (basis 0) q) hu
  rw [map_add, inner_add_right] at hroot
  have hsitezero : torusSite (m := m) (0 : Site d) = 0 := by
    funext j
    simp [torusSite]
  have hu0 : inner ℂ (basis 0) u = matrixResolvent (periodicHamiltonian coupling ωm) E η 0 0 := by
    rw [inner_basis_left]
    have hc : inCube (sideLength m / 4) (0 : Site d) := by
      intro j
      simp only [Pi.zero_apply, abs_zero]
      exact_mod_cast Nat.zero_le (sideLength m / 4)
    simp [u, v, hc, hsitezero]
  rw [hu0] at hroot
  apply sub_eq_iff_eq_add.mpr
  simpa only [diagonalGreen, AndersonAC.Blueprint.diagonalGreen,
    AndersonAC.Blueprint.greenOperator, AndersonAC.Blueprint.delta,
    basis, green, z, r, v, add_comm] using hroot.symm

end AndersonAC.SolS9Inf
