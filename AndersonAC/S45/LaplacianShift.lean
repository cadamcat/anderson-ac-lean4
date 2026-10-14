import AndersonAC.S45.Definitions

/-! Shift invariance of `qform (laplacian c)` for symmetric conductances `c`.
This is what the `TileCover.edge_symm` field supplies to the local-transfer proof. -/

noncomputable section
open Matrix
open scoped BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

theorem laplacian_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (c : RMat ι) (i : ι) :
    ∑ j, laplacian c i j = 0 := by
  have h : ∀ j, laplacian c i j = (if i = j then ∑ k, (if k = i then 0 else c i k) else 0) -
      (if j = i then 0 else c i j) := by
    intro j
    by_cases hij : i = j
    · subst hij; simp [laplacian]
    · simp [laplacian, hij, Ne.symm hij]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

theorem laplacian_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι] (c : RMat ι) (hc : c.IsSymm) :
    (laplacian c).IsSymm := by
  ext i j
  simp only [transpose_apply, laplacian]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    have := congrFun (congrFun hc i) j
    simp only [transpose_apply] at this
    rw [this]

/-- For symmetric conductances the Laplacian energy is invariant under constant shifts. -/
theorem qform_laplacian_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (c : RMat ι)
    (hc : c.IsSymm) (v : ι → ℝ) (a : ℝ) :
    qform (laplacian c) (fun i => v i + a) = qform (laplacian c) v := by
  have hconst : laplacian c *ᵥ (fun i => v i + a) = laplacian c *ᵥ v := by
    ext i
    simp only [mulVec, dotProduct, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      laplacian_row_sum, zero_mul, add_zero]
  have hcol : ∑ i, (laplacian c *ᵥ v) i = 0 := by
    have hs := laplacian_isSymm c hc
    simp only [mulVec, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i, laplacian c i j = 0 := by
      rw [← laplacian_row_sum c j]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrFun (congrFun hs j) i
      simpa [transpose_apply] using this
    rw [this, zero_mul]
  unfold qform
  rw [hconst]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hcol, mul_zero, add_zero]

end AndersonAC.AgentS45
