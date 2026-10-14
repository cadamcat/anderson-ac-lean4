import AndersonAC.S45.Definitions

/-! Bounded-overlap operator-norm estimate used in the transfer from tiles to
the whole sweep (05-local-sweeps.tex:592-600): if `A_T` is supported on
`S_T × S_T` and every site lies in at most `C` of the `S_T`, then
`‖∑_T A_T‖ ≤ C · max_T ‖A_T‖`. No sign assumption. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem sq_norm_mulVec_le (M : CMat P) (x : P → ℂ) :
    (∑ i, ‖(M *ᵥ x) i‖ ^ 2) ≤ ‖M‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec M ((WithLp.equiv 2 (P → ℂ)).symm x)
  have e1 : ∀ y : P → ℂ, ‖(WithLp.equiv 2 (P → ℂ)).symm y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
    intro y; rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.equiv 2 (P → ℂ)).symm (M *ᵥ x)‖ ≤
      ‖M‖ * ‖(WithLp.equiv 2 (P → ℂ)).symm x‖ := by simpa using h
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, e1, e1] at h3
  exact h3

theorem opNorm_le_of_sq (M : CMat P) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x : P → ℂ, (∑ i, ‖(M *ᵥ x) i‖ ^ 2) ≤ b ^ 2 * ∑ i, ‖x i‖ ^ 2) : ‖M‖ ≤ b := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hb fun x => ?_
  have e1 : ∀ y : EuclideanSpace ℂ P, ‖y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := fun y => by
    rw [EuclideanSpace.norm_sq_eq]
  have hx := h (WithLp.equiv 2 (P → ℂ) x)
  have hsq : ‖(toEuclideanCLM (n := P) (𝕜 := ℂ) M) x‖ ^ 2 ≤ (b * ‖x‖) ^ 2 := by
    rw [mul_pow, e1, e1]
    have : ∀ i, ((toEuclideanCLM (n := P) (𝕜 := ℂ) M) x) i = (M *ᵥ x.ofLp) i := fun i => by
      rw [← ofLp_toEuclideanCLM]
    simp only [this]
    exact hx
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hsq

theorem mask_apply' (S : Finset P) (A : CMat P) (i j : P) :
    mask S A i j = if i ∈ S ∧ j ∈ S then A i j else 0 := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [mask, pad, restrict, hi, hj]

theorem mask_mulVec_row (S : Finset P) (A : CMat P) (x : P → ℂ) {i : P} (hi : i ∉ S) :
    (mask S A *ᵥ x) i = 0 := by
  simp [Matrix.mulVec, dotProduct, mask_apply', hi]

theorem mask_mulVec_col (S : Finset P) (A : CMat P) (x : P → ℂ) :
    mask S A *ᵥ x = mask S A *ᵥ (fun j => if j ∈ S then x j else 0) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mask_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S <;> simp [hj]

theorem norm_sum_sq_le_card {ι : Type*} (F : Finset ι) (v : ι → ℂ) :
    ‖∑ T ∈ F, v T‖ ^ 2 ≤ F.card * ∑ T ∈ F, ‖v T‖ ^ 2 := by
  calc ‖∑ T ∈ F, v T‖ ^ 2 ≤ (∑ T ∈ F, ‖v T‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ F.card * ∑ T ∈ F, ‖v T‖ ^ 2 := sq_sum_le_card_mul_sum_sq

/-- Bounded overlap: `‖∑_T mask(S_T) A_T‖ ≤ C · max_T ‖mask(S_T) A_T‖`. -/
theorem norm_sum_mask_le {ι : Type*} [Fintype ι] (S : ι → Finset P) (C a : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hov : ∀ i, ((Finset.univ.filter fun T => i ∈ S T).card : ℝ) ≤ C)
    (A : ι → CMat P) (hA : ∀ T, ‖mask (S T) (A T)‖ ≤ a) :
    ‖∑ T, mask (S T) (A T)‖ ≤ C * a := by
  refine opNorm_le_of_sq _ _ (mul_nonneg hC ha) fun x => ?_
  set w : ι → P → ℂ := fun T => mask (S T) (A T) *ᵥ x with hw
  have hsum : (∑ T, mask (S T) (A T)) *ᵥ x = ∑ T, w T := by
    rw [Matrix.sum_mulVec]
  have hrow : ∀ i, ‖(∑ T, w T) i‖ ^ 2 ≤ C * ∑ T, ‖w T i‖ ^ 2 := by
    intro i
    set F := Finset.univ.filter fun T => i ∈ S T
    have h1 : (∑ T, w T) i = ∑ T ∈ F, w T i := by
      rw [Finset.sum_apply, Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      split_ifs with h
      · rfl
      · exact mask_mulVec_row _ _ _ h
    rw [h1]
    calc ‖∑ T ∈ F, w T i‖ ^ 2 ≤ F.card * ∑ T ∈ F, ‖w T i‖ ^ 2 := norm_sum_sq_le_card _ _
      _ ≤ C * ∑ T, ‖w T i‖ ^ 2 :=
          mul_le_mul (hov i) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hC
  have htile : ∀ T, (∑ i, ‖w T i‖ ^ 2) ≤ a ^ 2 * ∑ i ∈ S T, ‖x i‖ ^ 2 := by
    intro T
    have h := sq_norm_mulVec_le (mask (S T) (A T)) (fun j => if j ∈ S T then x j else 0)
    rw [← mask_mulVec_col] at h
    have e : (∑ i, ‖(fun j => if j ∈ S T then x j else 0) i‖ ^ 2) = ∑ i ∈ S T, ‖x i‖ ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S T)]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j => j ∉ S T) (fun j hj => by
        simp [(Finset.mem_filter.1 hj).2]), add_zero]
      refine Finset.sum_congr rfl fun j hj => by simp [hj]
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hA T) 2)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hcount : (∑ T, ∑ i ∈ S T, ‖x i‖ ^ 2) ≤ C * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter fun T => i ∈ S T)
      (by intro T i; simp)]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hov i) (sq_nonneg _)
  rw [hsum]
  calc (∑ i, ‖(∑ T, w T) i‖ ^ 2) ≤ ∑ i, C * ∑ T, ‖w T i‖ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = C * ∑ T, ∑ i, ‖w T i‖ ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ C * ∑ T, a ^ 2 * ∑ i ∈ S T, ‖x i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun T _ => htile T) hC
    _ = C * a ^ 2 * ∑ T, ∑ i ∈ S T, ‖x i‖ ^ 2 := by rw [← Finset.mul_sum]; ring
    _ ≤ C * a ^ 2 * (C * ∑ i, ‖x i‖ ^ 2) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (C * a) ^ 2 * ∑ i, ‖x i‖ ^ 2 := by ring

end AndersonAC.AgentS45
