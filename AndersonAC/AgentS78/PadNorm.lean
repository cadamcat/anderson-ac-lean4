import AndersonAC.S78.Definitions

/-!
Operator norms of matrices supported on an injectively indexed block: the Euclidean
operator norm of `N` equals that of its block `N.submatrix f f` when `N` vanishes
outside `range f × range f`. Used to move the `K` norms between the ambient torus
(S78), the active subtype (reset) and `Fin n` (S45).
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Inclusion matrix of an injective index map. -/
def inclMat (f : κ → ι) : Matrix ι κ ℂ := fun i k => if i = f k then 1 else 0

theorem inclMat_conj_mul (f : κ → ι) (hf : Function.Injective f) :
    (inclMat f)ᴴ * inclMat f = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inclMat, Matrix.one_apply]
  by_cases hkl : k = l
  · subst hkl; simp
  · rw [if_neg hkl]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : i = f k <;> by_cases h2 : i = f l <;> simp [h1, h2]
    all_goals first | exact fun h => hkl (hf h) | exact fun h => hkl (hf h).symm

theorem inclMat_block (f : κ → ι) (N : Matrix ι ι ℂ) :
    (inclMat f)ᴴ * N * inclMat f = N.submatrix f f := by
  ext k l
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, inclMat, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem inclMat_pad (f : κ → ι) (hf : Function.Injective f) (N : Matrix ι ι ℂ)
    (hN : ∀ i j, (∀ k, f k ≠ i) ∨ (∀ k, f k ≠ j) → N i j = 0) :
    inclMat f * N.submatrix f f * (inclMat f)ᴴ = N := by
  ext i j
  have hrow : ∀ (g : κ → ℂ), (∑ k, (if i = f k then (1 : ℂ) else 0) * g k) =
      if h : ∃ k, f k = i then g h.choose else 0 := by
    intro g
    split_ifs with h
    · rw [Finset.sum_eq_single h.choose]
      · simp [h.choose_spec]
      · intro b _ hb
        have : i ≠ f b := fun hi => hb (hf (hi.symm.trans h.choose_spec.symm))
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun k _ => ?_
      have : i ≠ f k := fun hi => h ⟨k, hi.symm⟩
      simp [this]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  have e1 : ∀ l, (∑ k, inclMat f i k * N (f k) (f l)) =
      if h : ∃ k, f k = i then N (f h.choose) (f l) else 0 := fun l => hrow (fun k => N (f k) (f l))
  simp only [e1]
  by_cases hi : ∃ k, f k = i
  · simp only [hi, dif_pos]
    rw [Finset.sum_eq_single (if h : ∃ k, f k = j then h.choose else hi.choose)]
    · by_cases hj : ∃ k, f k = j
      · simp only [hj, dif_pos, inclMat]
        rw [if_pos hj.choose_spec.symm]
        simp [hi.choose_spec, hj.choose_spec]
      · simp only [hj, dif_neg, not_false_eq_true, inclMat]
        have : j ≠ f hi.choose := fun h => hj ⟨hi.choose, h.symm⟩
        rw [if_neg this]
        simp only [star_zero, mul_zero]
        exact (hN i j (Or.inr fun k hk => hj ⟨k, hk⟩)).symm
    · intro b _ hb
      simp only [inclMat]
      by_cases hjb : j = f b
      · exfalso; apply hb
        have hj : ∃ k, f k = j := ⟨b, hjb.symm⟩
        simp only [hj, dif_pos]
        exact hf (hjb.symm.trans hj.choose_spec.symm)
      · simp [hjb]
    · simp
  · simp only [hi, dif_neg, not_false_eq_true, zero_mul, Finset.sum_const_zero]
    exact (hN i j (Or.inl fun k hk => hi ⟨k, hk⟩)).symm

theorem norm_inclMat_le (f : κ → ι) (hf : Function.Injective f) : ‖inclMat f‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (inclMat f)
  rw [inclMat_conj_mul f hf] at h
  have h1 : ‖(1 : Matrix κ κ ℂ)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (inclMat f)]

/-- The L2 operator norm of a block-supported matrix equals the norm of its block. -/
theorem norm_submatrix_of_support (f : κ → ι) (hf : Function.Injective f) (N : Matrix ι ι ℂ)
    (hN : ∀ i j, (∀ k, f k ≠ i) ∨ (∀ k, f k ≠ j) → N i j = 0) :
    ‖N.submatrix f f‖ = ‖N‖ := by
  have hP := norm_inclMat_le f hf
  have hPH : ‖(inclMat f)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hP
  apply le_antisymm
  · rw [← inclMat_block f N]
    calc ‖(inclMat f)ᴴ * N * inclMat f‖ ≤ ‖(inclMat f)ᴴ * N‖ * ‖inclMat f‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(inclMat f)ᴴ‖ * ‖N‖) * 1 := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * ‖N‖) * 1 := by gcongr
      _ = ‖N‖ := by ring
  · conv_lhs => rw [← inclMat_pad f hf N hN]
    calc ‖inclMat f * N.submatrix f f * (inclMat f)ᴴ‖
        ≤ ‖inclMat f * N.submatrix f f‖ * ‖(inclMat f)ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖inclMat f‖ * ‖N.submatrix f f‖) * 1 := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * ‖N.submatrix f f‖) * 1 := by gcongr
      _ = ‖N.submatrix f f‖ := by ring

/-- The S78 `matrixNorm` is the L2 operator norm. -/
theorem matrixNorm_eq_l2 (B : Matrix ι ι ℂ) : AndersonAC.S78.matrixNorm B = ‖B‖ := rfl

end AndersonAC.AgentS78
