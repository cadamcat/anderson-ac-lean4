import AndersonAC.S9Inf.BoundaryPSD

/-! Anderson real symmetry and the actual own-site rank-one change. -/

noncomputable section

open OAI.Anderson
open scoped ComplexConjugate

namespace AndersonAC.SolS9Inf

def basis {d : ℕ} (x : Site d) : StateSpace d := lp.single 2 x (1 : ℂ)

def scalarGreen {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (z : ℂ) : ℂ :=
  inner ℂ (basis x) (green (hamiltonian coupling ω) z (basis y))

theorem inner_basis_left {d : ℕ} (x : Site d) (v : StateSpace d) :
    inner ℂ (basis x) v = v x := by
  simp [basis, lp.inner_single_left]

theorem inner_star_basis_right {d : ℕ} (x : Site d) (v : StateSpace d) :
    inner ℂ (star v) (basis x) = v x := by
  simp [basis, lp.inner_single_right, lp.star_apply]

theorem star_basis {d : ℕ} (x : Site d) : star (basis x) = basis x := by
  classical
  apply lp.ext
  funext y
  by_cases hy : y = x <;> simp [basis, lp.star_apply, lp.single_apply, Pi.single_apply, hy]

theorem basis_ne_zero {d : ℕ} (x : Site d) : basis x ≠ 0 := by
  intro h
  have heq := congrArg (fun v : StateSpace d => v x) h
  simpa [basis] using heq

theorem hamiltonian_star {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (v : StateSpace d) : hamiltonian coupling ω (star v) = star (hamiltonian coupling ω v) := by
  apply lp.ext
  funext x
  simp [hamiltonian_apply, lp.star_apply, mul_comm]

/-- The Anderson Green kernel is complex symmetric, although the
upper-half-plane Green operator is not self-adjoint. -/
theorem scalarGreen_symmetric {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (hz : z.im ≠ 0) (x y : Site d) :
    scalarGreen coupling ω x y z = scalarGreen coupling ω y x z := by
  let T := hamiltonian coupling ω
  let A := T - z • (1 : StateSpace d →L[ℂ] StateSpace d)
  have hT : IsSelfAdjoint T := hamiltonian_isSelfAdjoint coupling ω
  have hA : IsUnit A := shifted_isUnit T hT z hz
  have hsym : T.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hbilinT (u v : StateSpace d) :
      inner ℂ (star u) (T v) = inner ℂ (star (T u)) v := by
    calc
      _ = inner ℂ (T (star u)) v := (hsym (star u) v).symm
      _ = inner ℂ (star (T u)) v :=
        congrArg (fun q : StateSpace d => inner ℂ q v) (hamiltonian_star coupling ω u)
  have hbilin : ∀ u v : StateSpace d, inner ℂ (star u) (A v) = inner ℂ (star (A u)) v := by
    intro u v
    dsimp [A]
    simp only [ContinuousLinearMap.sub_apply, smul_apply, ContinuousLinearMap.one_apply,
      inner_sub_right, inner_smul_right, star_sub, star_smul, inner_sub_left, inner_smul_left]
    rw [hbilinT]
    simp
  have hleft (u : StateSpace d) : A (green T z u) = u := unit_inverse_apply_left A hA u
  have hb := hbilin (green T z (basis x)) (green T z (basis y))
  rw [hleft, hleft, star_basis, inner_star_basis_right, inner_basis_left] at hb
  simpa [scalarGreen, inner_basis_left, T] using hb.symm

theorem scalarGreen_two_site_psd {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (hz : 0 < z.im) (x y : Site d) :
    (twoSiteIm (scalarGreen coupling ω x x z) (scalarGreen coupling ω x y z)
      (scalarGreen coupling ω y y z)).PosSemidef := by
  apply green_two_site_psd _ (hamiltonian_isSelfAdjoint coupling ω) z hz (basis x) (basis y)
  exact scalarGreen_symmetric coupling ω z hz.ne' x y

/-- Updating the normalized own-site sample changes the actual
Hamiltonian by a rank-one operator at that site. -/
theorem hamiltonian_update {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x : Site d) (s : SingleSite) :
    hamiltonian coupling (Function.update ω x s) = hamiltonian coupling ω +
      ((coupling * ((s : ℝ) - (ω x : ℝ)) : ℝ) : ℂ) •
        InnerProductSpace.rankOne ℂ (basis x) (basis x) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  simp only [ContinuousLinearMap.add_apply, smul_apply, InnerProductSpace.rankOne_apply,
    inner_basis_left, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  by_cases hy : y = x
  · subst y
    simp [hamiltonian_apply, potential, basis, lp.single_apply]
    ring
  · simp [hamiltonian_apply, potential, Function.update_of_ne hy,
      basis, lp.single_apply, Pi.single_apply, hy]

end AndersonAC.SolS9Inf
