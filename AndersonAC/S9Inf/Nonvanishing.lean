import AndersonAC.S9Inf.BoundaryRankOne
import AndersonAC.S9Inf.ShortestPaths

/-! Off-diagonal nonidentity from shortest paths and a finite resolvent
recurrence; no infinite series exchange is required. -/

noncomputable section

open OAI.Anderson
open scoped ENNReal

namespace AndersonAC.SolS9Inf

section Hilbert

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_green_apply_le (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) (v : K) : ‖green T z v‖ ≤ ‖v‖ / z.im := by
  by_cases hq : ‖green T z v‖ = 0
  · rw [hq]
    exact div_nonneg (norm_nonneg _) hz.le
  have hqpos : 0 < ‖green T z v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
  have hbound : z.im * ‖green T z v‖ ^ 2 ≤ ‖v‖ * ‖green T z v‖ := by
    rw [← green_quadratic_im T hT z hz.ne' v]
    exact (RCLike.im_le_norm (inner ℂ v (green T z v))).trans
      (norm_inner_le_norm (𝕜 := ℂ) v (green T z v))
  apply (le_div_iff₀ hz).mpr
  apply (mul_le_mul_iff_right₀ hqpos).mp
  nlinarith only [hbound]

theorem green_apply_operator (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) (v : K) :
    green T z (T v) = v + z • green T z v := by
  have h := unit_inverse_apply_right (T - z • (1 : K →L[ℂ] K))
    (shifted_isUnit T hT z hz) v
  change green T z (T v - z • v) = v at h
  rw [map_sub, map_smul] at h
  exact sub_eq_iff_eq_add.mp h

end Hilbert

theorem scalarGreen_not_identically_zero {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) : ∃ z : ℂ, 0 < z.im ∧ scalarGreen coupling ω x y z ≠ 0 := by
  letI : Nontrivial (StateSpace d) := ⟨⟨basis y, 0, basis_ne_zero y⟩⟩
  by_contra hfalse
  push_neg at hfalse
  let T := hamiltonian coupling ω
  let ℓ := latticeDistance x y
  let R : ℝ := ‖T‖ ^ (ℓ + 1) + 1
  let z : ℂ := (R : ℂ) * Complex.I
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : 0 < z.im := by simpa [z] using hR
  have hT : IsSelfAdjoint T := hamiltonian_isSelfAdjoint coupling ω
  obtain ⟨hzero, hfirst, hcount⟩ := AndersonAC.SolS9.shortest_path_coefficient_proof coupling ω x y
  change (∀ n : ℕ, n < ℓ → ((T ^ n) (basis y)) x = 0) at hzero
  change ((T ^ ℓ) (basis y)) x = (-1 : ℂ) ^ ℓ * (shortestPathCount x y : ℂ) at hfirst
  have hGzero : (green T z (basis y)) x = 0 := by
    simpa [scalarGreen, inner_basis_left, T] using hfalse z hz
  have hpowers : ∀ n : ℕ, n ≤ ℓ → (green T z ((T ^ n) (basis y))) x = 0 := by
    intro n
    induction n with
    | zero => intro _; simpa using hGzero
    | succ n ih =>
      intro hn
      have hnlt : n < ℓ := by omega
      have hnle : n ≤ ℓ := by omega
      rw [pow_succ', ContinuousLinearMap.mul_apply, green_apply_operator T hT z hz.ne']
      simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hzero n hnlt, ih hnle, mul_zero, add_zero]
  have hread : (green T z ((T ^ (ℓ + 1)) (basis y))) x = ((T ^ ℓ) (basis y)) x := by
    rw [pow_succ', ContinuousLinearMap.mul_apply, green_apply_operator T hT z hz.ne']
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpowers ℓ le_rfl, mul_zero, add_zero]
  have hnormbasis : ‖basis y‖ = 1 := by simp [basis]
  have hbound : ‖(green T z ((T ^ (ℓ + 1)) (basis y))) x‖ ≤ ‖T‖ ^ (ℓ + 1) / R := by
    calc
      _ ≤ ‖green T z ((T ^ (ℓ + 1)) (basis y))‖ :=
        lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ x
      _ ≤ ‖(T ^ (ℓ + 1)) (basis y)‖ / R := by
        simpa [z] using norm_green_apply_le T hT z hz ((T ^ (ℓ + 1)) (basis y))
      _ ≤ (‖T ^ (ℓ + 1)‖ * ‖basis y‖) / R :=
        div_le_div_of_nonneg_right ((T ^ (ℓ + 1)).le_opNorm _) hR.le
      _ ≤ ‖T‖ ^ (ℓ + 1) / R := by
        rw [hnormbasis, mul_one]
        exact div_le_div_of_nonneg_right (norm_pow_le T (ℓ + 1)) hR.le
  have hratio : ‖T‖ ^ (ℓ + 1) / R < 1 := by
    apply (div_lt_one hR).mpr
    dsimp [R]
    linarith
  have hcountone : 1 ≤ (shortestPathCount x y : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcount))
  rw [hread, hfirst] at hbound
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast] at hbound
  exact (not_lt_of_ge hcountone) (lt_of_le_of_lt hbound hratio)

end AndersonAC.SolS9Inf

namespace AndersonAC.SolS9

theorem offDiagonal_not_identically_zero_proof {d : ℕ} (coupling : ℝ) (ω : OAI.Anderson.Configuration d)
    (x y : OAI.Anderson.Site d) (hxy : x ≠ y) :
    ∃ z : ℂ, 0 < z.im ∧ AndersonAC.SolS9Inf.scalarGreen coupling ω x y z ≠ 0 :=
  AndersonAC.SolS9Inf.scalarGreen_not_identically_zero coupling ω x y

end AndersonAC.SolS9
