import AndersonAC.S9Inf.CTWeightStatement

/-! Scalar bounds for the bounded exponential conjugating weights. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

private theorem distance_triangle {d : ℕ} (x y z : Site d) :
    latticeDistance x z ≤ latticeDistance x y + latticeDistance y z := by
  unfold latticeDistance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  calc
    Int.natAbs (x j - z j) = Int.natAbs ((x j - y j) + (y j - z j)) := by congr 2 <;> omega
    _ ≤ Int.natAbs (x j - y j) + Int.natAbs (y j - z j) := Int.natAbs_add_le _ _

private theorem distance_symm {d : ℕ} (x y : Site d) :
    latticeDistance x y = latticeDistance y x := by
  unfold latticeDistance
  apply Finset.sum_congr rfl
  intro j _
  calc
    Int.natAbs (x j - y j) = Int.natAbs (-(y j - x j)) := by congr 1; ring
    _ = Int.natAbs (y j - x j) := Int.natAbs_neg _

private theorem distance_step {d : ℕ} (x : Site d) (j : Fin d) :
    latticeDistance x (x + basisVector j) = 1 ∧ latticeDistance x (x - basisVector j) = 1 := by
  classical
  constructor
  · have h (k : Fin d) : x k - (x + basisVector j) k = -(basisVector j k) := by
      change x k - (x k + basisVector j k) = _
      ring
    simp only [latticeDistance, h, Int.natAbs_neg]
    simp [basisVector, Pi.single_apply, apply_ite]
  · have h (k : Fin d) : x k - (x - basisVector j) k = basisVector j k := by
      change x k - (x k - basisVector j k) = _
      ring
    simp only [latticeDistance, h]
    simp [basisVector, Pi.single_apply, apply_ite]

private theorem weight_ratio_near {d : ℕ} (y x u : Site d) (N : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hxu : latticeDistance x u ≤ 1) :
    |ctWeight y N a x / ctWeight y N a u - 1| ≤ Real.exp a - 1 := by
  have h1 := distance_triangle x u y
  have h2 := distance_triangle u x y
  rw [distance_symm u x] at h2
  have hmin1 : min (latticeDistance x y) N ≤ min (latticeDistance u y) N + 1 := by omega
  have hmin2 : min (latticeDistance u y) N ≤ min (latticeDistance x y) N + 1 := by omega
  have hr1 : (min (latticeDistance x y) N : ℝ) ≤ (min (latticeDistance u y) N : ℝ) + 1 :=
    by exact_mod_cast hmin1
  have hr2 : (min (latticeDistance u y) N : ℝ) ≤ (min (latticeDistance x y) N : ℝ) + 1 :=
    by exact_mod_cast hmin2
  let r := a * (min (latticeDistance x y) N : ℝ) - a * (min (latticeDistance u y) N : ℝ)
  have hrlo : -a ≤ r := by
    have h := mul_le_mul_of_nonneg_left hr2 ha
    dsimp [r]
    nlinarith only [h]
  have hrhi : r ≤ a := by
    have h := mul_le_mul_of_nonneg_left hr1 ha
    dsimp [r]
    nlinarith only [h]
  have hratio : ctWeight y N a x / ctWeight y N a u = Real.exp r := by
    simpa only [ctWeight, r, Nat.cast_min] using
      (Real.exp_sub (a * (min (latticeDistance x y) N : ℕ))
        (a * (min (latticeDistance u y) N : ℕ))).symm
  rw [hratio]
  apply abs_le.mpr
  have hlo := Real.exp_le_exp.mpr hrlo
  have hhi := Real.exp_le_exp.mpr hrhi
  have hsum : 2 ≤ Real.exp a + Real.exp (-a) := by
    linarith only [Real.add_one_le_exp a, Real.add_one_le_exp (-a)]
  constructor <;> linarith only [hlo, hhi, hsum]

theorem ctWeightBounds_proof : CTWeightBoundsStatement := by
  intro d y N a ha
  refine ⟨?_, ?_, ?_⟩
  · simp [ctWeight, latticeDistance]
  · intro x
    constructor
    · apply Real.one_le_exp_iff.mpr
      exact mul_nonneg ha (Nat.cast_nonneg _)
    · apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (min_le_right (latticeDistance x y) N)) ha
  · intro x j
    exact ⟨weight_ratio_near y x (x + basisVector j) N a ha (distance_step x j).1.le,
      weight_ratio_near y x (x - basisVector j) N a ha (distance_step x j).2.le⟩

end AndersonAC.SolS9Inf
