import Mathlib

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex Cauchy–Schwarz for finite sums: `‖∑ aᵢbᵢ‖² ≤ (∑‖aᵢ‖²)(∑‖bᵢ‖²)`. -/
lemma complex_sum_mul_norm_sq_le {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖ ^ 2
      ≤ (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
  classical
  set s : ℂ := ∑ i, a i * b i with hs
  by_cases h0 : s = 0
  · rw [h0, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · have hApos : 0 < ‖s‖ := norm_pos_iff.mpr h0
    set u : ℂ := (‖s‖ : ℂ) / s with hu
    have hus : u * s = (‖s‖ : ℂ) := div_mul_cancel₀ _ h0
    have hre : (‖s‖ : ℝ) = ∑ i, (u * a i * b i).re := by
      have h1 : (u * s).re = ‖s‖ := by rw [hus, Complex.ofReal_re]
      rw [← h1, hs, Finset.mul_sum, ← Complex.coe_reAddGroupHom, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Complex.coe_reAddGroupHom]
      congr 1
      ring
    have hpt : ∀ i, (u * a i * b i).re ≤ ‖a i‖ * ‖u * b i‖ := by
      intro i
      calc (u * a i * b i).re
          ≤ ‖u * a i * b i‖ := Complex.re_le_norm _
        _ = ‖a i‖ * ‖u * b i‖ := by
            rw [show u * a i * b i = a i * (u * b i) by ring, norm_mul]
    have hsum : (‖s‖ : ℝ) ≤ ∑ i, ‖a i‖ * ‖u * b i‖ := by
      rw [hre]
      exact Finset.sum_le_sum (fun i _ => hpt i)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun i => ‖a i‖) (g := fun i => ‖u * b i‖)
    have hub : ∀ i, ‖u * b i‖ = ‖b i‖ := by
      intro i
      rw [norm_mul]
      have huabs : ‖u‖ = 1 := by
        rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos,
          div_self (ne_of_gt hApos)]
      rw [huabs, one_mul]
    simp_rw [hub] at hcs hsum
    calc ‖s‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖b i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hsum 2
      _ ≤ _ := hcs

/-- `Tr(XY)` as a double sum. -/
lemma trace_mul_eq_sum (X Y : Matrix n n ℂ) :
    Matrix.trace (X * Y) = ∑ p : n × n, X p.1 p.2 * Y p.2 p.1 := by
  unfold Matrix.trace Matrix.diag
  simp_rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]

/-- Diagonal entries of `Xᴴ * X` are real sums of squared norms. -/
lemma conjTranspose_mul_self_apply (X : Matrix n n ℂ) (j : n) :
    (Xᴴ * X) j j = ((∑ i, ‖X i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  have hterm : ∀ i : n, star (X i j) * X i j = ((‖X i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow]
    rfl
  exact (Finset.sum_congr rfl (fun k _ => hterm k)).trans
    (RCLike.ofReal_sum _ _).symm

/-- `Tr(XᴴX)` is the real sum of squared moduli. -/
lemma trace_conjTranspose_mul_self_eq (X : Matrix n n ℂ) :
    Matrix.trace (Xᴴ * X)
      = ((∑ p : n × n, ‖X p.1 p.2‖ ^ 2 : ℝ) : ℂ) := by
  unfold Matrix.trace Matrix.diag
  calc ∑ j, (Xᴴ * X) j j
      = ∑ j, ((∑ i, ‖X i j‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl (fun j _ => conjTranspose_mul_self_apply X j)
    _ = ((∑ j, ∑ i, ‖X i j‖ ^ 2 : ℝ) : ℂ) := (RCLike.ofReal_sum _ _).symm
    _ = ((∑ p : n × n, ‖X p.1 p.2‖ ^ 2 : ℝ) : ℂ) := by
        congr 1
        rw [Finset.sum_comm]
        have hprod : (∑ p : n × n, ‖X p.1 p.2‖ ^ 2)
            = ∑ i, ∑ j, ‖X i j‖ ^ 2 :=
          Fintype.sum_prod_type _
        rw [← hprod]

/-- Real part of `Tr(XᴴX)`. -/
lemma trace_conjTranspose_mul_self_re (X : Matrix n n ℂ) :
    (Matrix.trace (Xᴴ * X)).re = ∑ p : n × n, ‖X p.1 p.2‖ ^ 2 := by
  rw [trace_conjTranspose_mul_self_eq, Complex.ofReal_re]

/-- `Tr(XᴴX)` is real. -/
lemma trace_conjTranspose_mul_self_im (X : Matrix n n ℂ) :
    (Matrix.trace (Xᴴ * X)).im = 0 := by
  rw [trace_conjTranspose_mul_self_eq, Complex.ofReal_im]

/-- Nonnegativity of `Tr(XᴴX).re`. -/
lemma trace_conjTranspose_mul_self_re_nonneg (X : Matrix n n ℂ) :
    0 ≤ (Matrix.trace (Xᴴ * X)).re := by
  rw [trace_conjTranspose_mul_self_re]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- Swap reindexing for the `Y` factor. -/
lemma sum_swap_norm_sq (Y : Matrix n n ℂ) :
    (∑ p : n × n, ‖Y p.2 p.1‖ ^ 2) = ∑ p : n × n, ‖Y p.1 p.2‖ ^ 2 := by
  apply Fintype.sum_equiv (Equiv.prodComm n n)
  intro p
  rfl

/-- Dyson–Thompson Lemma 1: Cauchy–Schwarz for the trace,
`‖Tr(XY)‖² ≤ Tr(X†X)·Tr(Y†Y)`. -/
theorem trace_mul_norm_sq_le (X Y : Matrix n n ℂ) :
    ‖Matrix.trace (X * Y)‖ ^ 2
      ≤ (Matrix.trace (Xᴴ * X)).re * (Matrix.trace (Yᴴ * Y)).re := by
  classical
  rw [trace_mul_eq_sum, trace_conjTranspose_mul_self_re,
    trace_conjTranspose_mul_self_re]
  have h := complex_sum_mul_norm_sq_le (ι := n × n)
    (a := fun p : n × n => X p.1 p.2) (b := fun p : n × n => Y p.2 p.1)
  rw [sum_swap_norm_sq Y] at h
  exact h
