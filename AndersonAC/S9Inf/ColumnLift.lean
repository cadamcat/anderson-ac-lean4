import AndersonAC.S9Inf.RootCoupling
import AndersonAC.S9Inf.ReadoutDefinitions
import AndersonAC.S9Fin.Scalar
import AndersonAC.S9Fin.Basic
import AndersonAC.S9Inf.CombesThomasProof

/-! Restrict a true finite resolvent column to the matching root cube. -/

noncomputable section

open OAI.Anderson AndersonAC.S9 AndersonAC.SolS9
open scoped Topology Matrix

namespace AndersonAC.SolS9Inf

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def inCube {d : ℕ} (R : ℕ) (x : Site d) : Prop :=
  ∀ j : Fin d, |x j| ≤ (R : ℤ)

def cubeFinset (d R : ℕ) : Finset (Site d) := by
  classical
  exact Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(R : ℤ)) (R : ℤ))

@[simp] theorem mem_cubeFinset {d R : ℕ} (x : Site d) :
    x ∈ cubeFinset d R ↔ inCube R x := by
  simp [cubeFinset, inCube, abs_le]

def columnLift {d m : ℕ} (R : ℕ) (v : Torus d m → ℂ) : StateSpace d :=
  ∑ x ∈ cubeFinset d R, lp.single 2 x (v (torusSite x))

@[simp] theorem columnLift_apply {d m : ℕ} (R : ℕ)
    (v : Torus d m → ℂ) (x : Site d) :
    columnLift R v x = if inCube R x then v (torusSite x) else 0 := by
  classical
  simp only [columnLift, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, mem_cubeFinset]

theorem torusSite_add_basis {d m : ℕ} (x : Site d) (j : Fin d) :
    torusSite (m := m) (x + basisVector j) = torusSite x + torusBasisVector j := by
  classical
  funext k
  by_cases h : k = j <;> simp [torusSite, basisVector, torusBasisVector, h]

theorem torusSite_sub_basis {d m : ℕ} (x : Site d) (j : Fin d) :
    torusSite (m := m) (x - basisVector j) = torusSite x - torusBasisVector j := by
  classical
  funext k
  by_cases h : k = j <;> simp [torusSite, basisVector, torusBasisVector, h]

theorem torusSite_eq_zero_iff {d m : ℕ} (x : Site d)
    (hx : inCube (sideLength m / 4) x) : torusSite (m := m) x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx' := rootRepresentative_torusSite x hx
    change rootRepresentative (torusSite x) = x at hx'
    rw [h] at hx'
    have hzero : rootRepresentative (0 : Torus d m) = 0 := by
      funext j
      exact ZMod.valMinAbs_zero _
    rw [hzero] at hx'
    exact hx'.symm
  · rintro rfl
    funext j
    simp [torusSite]

theorem periodic_mulVec {d m : ℕ} (coupling : ℝ) (ω : TorusConfiguration d m)
    (v : Torus d m → ℂ) (x : Torus d m) :
    (periodicHamiltonian coupling ω *ᵥ v) x =
      -(∑ j : Fin d, (v (x + torusBasisVector j) + v (x - torusBasisVector j))) +
        (coupling * (ω x : ℝ) : ℂ) * v x := by
  classical
  simp only [Matrix.mulVec, dotProduct, periodicHamiltonian, add_mul,
    neg_mul, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp_rw [ite_mul, one_mul, zero_mul]
  have hcomm (f : Torus d m → Fin d → ℂ) : (∑ y, ∑ j, f y j) = ∑ j, ∑ y, f y j :=
    Finset.sum_comm
  rw [hcomm, hcomm]
  simp

theorem finite_column_equation {d m : ℕ} (coupling E η : ℝ) (hη : 0 < η)
    (ω : TorusConfiguration d m) (x : Torus d m) :
    -(∑ j : Fin d, (
      matrixResolvent (periodicHamiltonian coupling ω) E η (x + torusBasisVector j) 0 +
      matrixResolvent (periodicHamiltonian coupling ω) E η (x - torusBasisVector j) 0)) +
      ((coupling * (ω x : ℝ) : ℂ) - ((E : ℂ) + η * Complex.I)) *
        matrixResolvent (periodicHamiltonian coupling ω) E η x 0 =
          if x = 0 then 1 else 0 := by
  classical
  let H := periodicHamiltonian coupling ω
  have hH := periodicHamiltonian_isHermitian_proof d m coupling ω
  have hu : IsUnit (H - ((E : ℂ) + η * Complex.I) • 1) := by
    rw [scalar_damped_matrix_eq]
    exact damped_isUnit (H - (E : ℂ) • 1) (hH.sub (by simp [Matrix.IsHermitian]))
      η 1 hη zero_lt_one (fun _ => Complex.I) (by simp)
  have heq := congrFun (congrFun (Matrix.mul_nonsing_inv _
    ((H - ((E : ℂ) + η * Complex.I) • 1).isUnit_iff_isUnit_det.mp hu)) x) 0
  change ((H - ((E : ℂ) + η * Complex.I) • 1) *ᵥ
    (fun q => matrixResolvent H E η q 0)) x = _ at heq
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at heq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply] at heq
  rw [periodic_mulVec] at heq
  dsimp [H] at heq
  convert heq using 1 <;> ring

theorem finite_column_entry_bound {d m : ℕ} (coupling E η : ℝ) (hη : 0 < η)
    (ω : TorusConfiguration d m) (x : Torus d m) :
    ‖matrixResolvent (periodicHamiltonian coupling ω) E η x 0‖ ≤ η⁻¹ :=
  (matrix_entry_norm_le _ 0 x).trans (matrixResolvent_norm_pos _
    (periodicHamiltonian_isHermitian_proof d m coupling ω) E η hη)

end AndersonAC.SolS9Inf
