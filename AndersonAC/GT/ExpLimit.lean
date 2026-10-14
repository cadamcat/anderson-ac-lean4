import Mathlib

open Matrix Finset NormedSpace
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! Matrix exponential limits for Dyson's proof of Golden–Thompson:
`(1 + A/m)^m → exp A` and a perturbed version, via series comparison.
All norms are the `L∞` operator norm (submultiplicative, complete). -/

/-- Falling-factorial coefficient: `∏_{t<j} (1 - t/m)`, the ratio of the
binomial term to the exponential series term. -/
noncomputable def binomCoeff (m j : ℕ) : ℝ :=
  ∏ t ∈ Finset.range j, (1 - (t : ℝ) / (m : ℝ))

/-- Coefficients lie in `[0,1]` when `j ≤ m`. -/
lemma binomCoeff_mem_Icc (m j : ℕ) (hm : j ≤ m) :
    0 ≤ binomCoeff m j ∧ binomCoeff m j ≤ 1 := by
  revert hm
  induction j with
  | zero =>
    intro
    simp [binomCoeff]
  | succ j ih =>
    intro hm
    have hjm : j ≤ m := by omega
    obtain ⟨h0, h1⟩ := ih hjm
    have hfactor_nonneg : (0 : ℝ) ≤ 1 - (j : ℝ) / (m : ℝ) := by
      have hjm' : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : j ≤ m)
      have hmpos : (0 : ℝ) < (m : ℝ) := by
        have : 0 < m := by omega
        exact_mod_cast this
      have hle : (j : ℝ) / (m : ℝ) ≤ 1 := (div_le_one hmpos).mpr hjm'
      linarith
    have hfactor_le : (1 - (j : ℝ) / (m : ℝ)) ≤ 1 := by
      have : (0 : ℝ) ≤ (j : ℝ) / (m : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
    have hprod_eq : binomCoeff m (j + 1)
        = binomCoeff m j * (1 - (j : ℝ) / (m : ℝ)) := by
      unfold binomCoeff
      rw [Finset.prod_range_succ]
    rw [hprod_eq]
    refine ⟨mul_nonneg h0 hfactor_nonneg, ?_⟩
    calc binomCoeff m j * (1 - ↑j / ↑m)
        ≤ 1 * (1 - ↑j / ↑m) := mul_le_mul_of_nonneg_right h1 hfactor_nonneg
      _ = 1 - ↑j / ↑m := one_mul _
      _ ≤ 1 := hfactor_le

lemma binomCoeff_nonneg (m j : ℕ) (hm : j ≤ m) : 0 ≤ binomCoeff m j :=
  (binomCoeff_mem_Icc m j hm).1

lemma binomCoeff_le_one (m j : ℕ) (hm : j ≤ m) : binomCoeff m j ≤ 1 :=
  (binomCoeff_mem_Icc m j hm).2

/-- Each factor tends to 1. -/
lemma factor_tendsto_one (t : ℕ) :
    Filter.Tendsto (fun m : ℕ => (1 : ℝ) - (t : ℝ) / (m : ℝ))
      Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto (fun m : ℕ => (t : ℝ) / (m : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)
  have h := tendsto_const_nhds (x := (1 : ℝ)) (f := (Filter.atTop : Filter ℕ))
  have h2 := h.sub h0
  simpa using h2

/-- Finite products of the factors tend to 1. -/
lemma prod_tendsto_one (j : ℕ) :
    Filter.Tendsto (fun m : ℕ => ∏ t ∈ Finset.range j, (1 - (t : ℝ) / (m : ℝ)))
      Filter.atTop (nhds 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := ih.mul (factor_tendsto_one j)
    simpa [Finset.prod_range_succ] using h

/-- Coefficients tend to 1 for fixed `j`. -/
lemma binomCoeff_tendsto_one (j : ℕ) :
    Filter.Tendsto (fun m : ℕ => binomCoeff m j) Filter.atTop (nhds 1) :=
  prod_tendsto_one j

/-- `C(m,j) * j!` is the descending product (no constraints needed). -/
lemma choose_mul_factorial_eq_prod (m j : ℕ) :
    m.choose j * Nat.factorial j = ∏ t ∈ Finset.range j, (m - t) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hfact : Nat.factorial (j + 1) = (j + 1) * Nat.factorial j := Nat.factorial_succ j
    have hprod : (∏ t ∈ Finset.range (j + 1), (m - t))
        = (∏ t ∈ Finset.range j, (m - t)) * (m - j) := Finset.prod_range_succ _ _
    have hchoose := Nat.choose_succ_right_eq m j
    calc m.choose (j + 1) * Nat.factorial (j + 1)
        = m.choose (j + 1) * ((j + 1) * Nat.factorial j) := by rw [hfact]
      _ = (m.choose (j + 1) * (j + 1)) * Nat.factorial j := by rw [← mul_assoc]
      _ = (m.choose j * (m - j)) * Nat.factorial j := by rw [hchoose]
      _ = (m.choose j * Nat.factorial j) * (m - j) := by ring
      _ = (∏ t ∈ Finset.range j, (m - t)) * (m - j) := by rw [ih]
      _ = ∏ t ∈ Finset.range (j + 1), (m - t) := by
        exact (Finset.prod_range_succ _ _).symm

/-- Bridge: from `C*F = M*P` to `C*M⁻¹ = P*F⁻¹` (reals, nonzero). -/
lemma bridge_div_eq (C F M P : ℝ) (hF : F ≠ 0) (hM : M ≠ 0)
    (h : C * F = M * P) : C * (M⁻¹) = P * (F⁻¹) := by
  have e1 : C * (M⁻¹) = C / M := by rw [div_eq_mul_inv]
  have e2 : P * (F⁻¹) = P / F := by rw [div_eq_mul_inv]
  rw [e1, e2]
  have h' : C * F = P * M := by rw [mul_comm P M]; exact h
  exact (div_eq_div_iff hM hF).mpr h'

/-- Choose/power identity in the exact form needed for the expansion. -/
lemma choose_div_pow_eq (m j : ℕ) (hjm : j ≤ m) (hm : 0 < m) :
    ((m.choose j : ℕ) : ℝ) * (((m : ℝ))⁻¹) ^ j
      = (binomCoeff m j) * (((Nat.factorial j) : ℝ))⁻¹ := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hF : ((Nat.factorial j) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hM : ((m : ℝ) ^ j) ≠ 0 := pow_ne_zero j hmR
  -- Cast the Nat identity
  have hnat := choose_mul_factorial_eq_prod m j
  have hR : ((m.choose j : ℕ) : ℝ) * ((Nat.factorial j : ℕ) : ℝ)
      = ∏ t ∈ Finset.range j, (((m - t : ℕ)) : ℝ) := by
    exact_mod_cast hnat
  -- Nat-sub casts to real subs
  have hsub : ∀ t ∈ Finset.range j, ((((m - t : ℕ))) : ℝ) = (m : ℝ) - (t : ℝ) := by
    intro t ht
    have htm : t ≤ m := by
      have := Finset.mem_range.mp ht
      omega
    exact Nat.cast_sub htm
  have hprod_eq : (∏ t ∈ Finset.range j, ((((m - t : ℕ))) : ℝ))
      = ∏ t ∈ Finset.range j, ((m : ℝ) - (t : ℝ)) :=
    Finset.prod_congr rfl (fun t ht => hsub t ht)
  rw [hprod_eq] at hR
  -- Factor out m^j
  have hfactor : (∏ t ∈ Finset.range j, ((m : ℝ) - (t : ℝ)))
      = (m : ℝ) ^ j * binomCoeff m j := by
    have perterm : ∀ t ∈ Finset.range j,
        ((m : ℝ) - (t : ℝ)) = (m : ℝ) * (1 - (t : ℝ) / (m : ℝ)) := by
      intro t _
      field_simp
    rw [Finset.prod_congr rfl (fun t ht => perterm t ht)]
    rw [Finset.prod_mul_distrib]
    simp [binomCoeff, Finset.prod_const, Finset.card_range]
  rw [hfactor] at hR
  -- hR : C * F = m^j * c. Apply bridge to get C * (m^j)⁻¹ = c * F⁻¹,
  -- then convert (m^j)⁻¹ to (m⁻¹)^j.
  have hbridge := bridge_div_eq _ _ _ _ hF hM hR
  -- hbridge : C * ((m^j))⁻¹ = c * (F⁻¹). Goal has ((m⁻¹))^j. Convert.
  have hinv : ((((m : ℝ))⁻¹) ^ j) = (((m : ℝ) ^ j))⁻¹ := by rw [inv_pow]
  rw [hinv]
  exact hbridge

/-- Binomial expansion with complex choose-scalars (proved by induction,
to keep scalars in `ℂ` and avoid `Nat.cast`-matrix conversions). -/
lemma one_add_pow_eq (B : Matrix n n ℂ) (m : ℕ) :
    (1 + B) ^ m = ∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℂ) • (B ^ j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    have hterm : ∀ j ∈ Finset.range (m + 1),
        ((m.choose j : ℂ) • B ^ j) * (1 + B)
          = (m.choose j : ℂ) • B ^ j + (m.choose j : ℂ) • B ^ (j + 1) := by
      intro j _
      rw [smul_mul_assoc, mul_add, mul_one, ← pow_succ, smul_add]
    rw [Finset.sum_congr rfl (fun j hj => hterm j hj)]
    rw [Finset.sum_add_distrib]
    have eSa : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) • B ^ j)
        = (∑ j ∈ Finset.range m, (m.choose (j + 1) : ℂ) • B ^ (j + 1))
          + (m.choose 0 : ℂ) • B ^ 0 :=
      Finset.sum_range_succ' _ _
    have eSb : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) • B ^ (j + 1))
        = (∑ j ∈ Finset.range m, (m.choose j : ℂ) • B ^ (j + 1))
          + (m.choose m : ℂ) • B ^ (m + 1) :=
      Finset.sum_range_succ _ _
    have eRHS : (∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℂ) • B ^ j)
        = ((∑ j ∈ Finset.range m, ((m + 1).choose (j + 1) : ℂ) • B ^ (j + 1))
            + ((m + 1).choose (m + 1) : ℂ) • B ^ (m + 1))
          + ((m + 1).choose 0 : ℂ) • B ^ 0 := by
      rw [Finset.sum_range_succ']
      congr 1
      rw [Finset.sum_range_succ]
    rw [eSa, eSb, eRHS]
    have hmid : (∑ j ∈ Finset.range m, ((m + 1).choose (j + 1) : ℂ) • B ^ (j + 1))
        = (∑ j ∈ Finset.range m, (m.choose (j + 1) : ℂ) • B ^ (j + 1))
          + (∑ j ∈ Finset.range m, (m.choose j : ℂ) • B ^ (j + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hP : ((m + 1).choose (j + 1) : ℕ)
          = (m.choose (j + 1) + m.choose j : ℕ) := by
        have := Nat.choose_succ_succ' m j
        omega
      rw [hP]
      push_cast
      rw [add_smul]
    rw [hmid]
    have e0 : ((m.choose 0 : ℕ) : ℂ) = 1 := by simp
    have e0' : (((m + 1).choose 0 : ℕ) : ℂ) = 1 := by simp
    have em : ((m.choose m : ℕ) : ℂ) = 1 := by simp [Nat.choose_self]
    have em' : (((m + 1).choose (m + 1) : ℕ) : ℂ) = 1 := by simp [Nat.choose_self]
    rw [e0, e0', em, em']
    abel

/-- Complex scalar identity from the real one. -/
lemma choose_div_pow_eq_complex (m j : ℕ) (hjm : j ≤ m) (hm : 0 < m) :
    ((m.choose j : ℕ) : ℂ) * (((m : ℂ))⁻¹) ^ j
      = (((binomCoeff m j : ℝ)) : ℂ) * (((Nat.factorial j : ℕ) : ℂ))⁻¹ := by
  have hR := choose_div_pow_eq m j hjm hm
  have hC := congrArg ((↑) : ℝ → ℂ) hR
  simpa using hC

/-- Binomial term in `binomCoeff` form (proved entrywise to avoid
`smul`-associativity instance issues). -/
lemma binomial_term_eq (A : Matrix n n ℂ) (m j : ℕ) (hjm : j ≤ m) (hm : 0 < m) :
    ((m.choose j : ℕ) : ℂ) • ((((m : ℂ))⁻¹ • A) ^ j)
      = (((binomCoeff m j : ℝ)) : ℂ)
        • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) := by
  have hsp : ((((m : ℂ))⁻¹ • A) ^ j) = ((((m : ℂ))⁻¹) ^ j) • (A ^ j) :=
    smul_pow _ _ _
  rw [hsp]
  have hscalar : ((m.choose j : ℕ) : ℂ) * (((m : ℂ))⁻¹) ^ j
      = (((binomCoeff m j : ℝ)) : ℂ) * (((Nat.factorial j : ℕ) : ℂ))⁻¹ :=
    choose_div_pow_eq_complex m j hjm hm
  apply Matrix.ext
  intro i k
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, hscalar, mul_assoc]

/-- Norm of a real-cast difference. -/
lemma norm_ofReal_sub_one (c : ℝ) : ‖((((c : ℝ))) : ℂ) - 1‖ = |1 - c| := by
  have inner : ((((c : ℝ))) : ℂ) - 1 = ((((c - 1 : ℝ))) : ℂ) := by
    simp [Complex.ofReal_sub, Complex.ofReal_one]
  rw [inner, Complex.norm_real, Real.norm_eq_abs]
  exact abs_sub_comm c 1

/-- Expansion of `(1 + A/m)^m` in `binomCoeff` form (for `0 < m`). -/
lemma one_add_div_pow_eq_sum (A : Matrix n n ℂ) (m : ℕ) (hm : 0 < m) :
    (1 + ((m : ℂ))⁻¹ • A) ^ m
      = ∑ j ∈ Finset.range (m + 1),
        (((binomCoeff m j : ℝ)) : ℂ)
          • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) := by
  rw [one_add_pow_eq]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by
    have := Finset.mem_range.mp hj
    omega
  exact binomial_term_eq A m j hjm hm

/-- Head sums tend to zero for fixed `J`. -/
lemma head_sum_tendsto_zero (A : Matrix n n ℂ) (J : ℕ) :
    Filter.Tendsto
      (fun m : ℕ => ∑ j ∈ Finset.range (J + 1),
        |1 - binomCoeff m j| * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
      Filter.atTop (nhds 0) := by
  have hper : ∀ j ∈ Finset.range (J + 1),
      Filter.Tendsto
        (fun m : ℕ => |1 - binomCoeff m j|
          * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
        Filter.atTop (nhds 0) := by
    intro j _
    have hc := binomCoeff_tendsto_one j
    have h1 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) - binomCoeff m j)
        Filter.atTop (nhds 0) := by
      have hconst := tendsto_const_nhds (x := (1 : ℝ)) (f := (Filter.atTop : Filter ℕ))
      have hsub := hconst.sub hc
      simpa using hsub
    have habs : Filter.Tendsto (fun m : ℕ => |1 - binomCoeff m j|)
        Filter.atTop (nhds 0) := by
      have h := h1.abs
      simpa using h
    have hmul := habs.mul_const
      (‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
    simpa using hmul
  have hsum := tendsto_finsetSum _ hper
  simpa using hsum

/-- Per-term identity: `‖c•e - e‖ = |1-c|·‖e‖`. -/
lemma norm_binom_term_sub (m j : ℕ)
    (e : Matrix n n ℂ) :
    ‖((((binomCoeff m j : ℝ)) : ℂ) • e - e)‖
      = |1 - binomCoeff m j| * ‖e‖ := by
  have heq : (((binomCoeff m j : ℝ)) : ℂ) • e - e
      = ((((binomCoeff m j : ℝ)) : ℂ) - 1) • e := by
    rw [sub_smul, one_smul]
  rw [heq, norm_smul, norm_ofReal_sub_one]

/-- `(1 + A/m)^m → exp A`. -/
theorem one_add_div_pow_tendsto_exp (A : Matrix n n ℂ) :
    Filter.Tendsto (fun m : ℕ => (1 + ((m : ℂ))⁻¹ • A) ^ m)
      Filter.atTop (nhds (NormedSpace.exp A)) := by
  -- Exponential series setup.
  have hHasSum : HasSum (fun j : ℕ => ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))
      (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hSummNorm : Summable
      (fun j : ℕ => ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) A
  have hHasSumR := hSummNorm.hasSum
  have hPartR := hHasSumR.tendsto_sum_nat
  have hPartM := hHasSum.tendsto_sum_nat
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hPartR) (ε / 6) (by linarith)
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hPartM) (ε / 3) (by linarith)
  set J := max N₀ N₁ with hJdef
  have hJ0 : N₀ ≤ J := le_max_left _ _
  have hJ1 : N₁ ≤ J := le_max_right _ _
  have hHeadT := head_sum_tendsto_zero A J
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hHeadT) (ε / 3) (by linarith)
  refine ⟨max (max J N₂) 1, fun m hm => ?_⟩
  have hJm : J ≤ m := by
    have : max (max J N₂) 1 ≤ m := hm
    omega
  have hN₂m : N₂ ≤ m := by
    have : max (max J N₂) 1 ≤ m := hm
    omega
  have hm1 : 0 < m := by
    have : max (max J N₂) 1 ≤ m := hm
    omega
  have hm1' : 0 < m + 1 := by omega
  -- Subset for splitting.
  have hsub : Finset.range (J + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le hx (Nat.succ_le_succ hJm)))
  -- Head small.
  have hhead_dist := hN₂ m hN₂m
  have hhead_nn : 0 ≤ ∑ j ∈ Finset.range (J + 1),
      |1 - binomCoeff m j| * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hhead_lt : (∑ j ∈ Finset.range (J + 1),
      |1 - binomCoeff m j| * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) < ε / 3 := by
    have hde : dist (∑ j ∈ Finset.range (J + 1),
          |1 - binomCoeff m j| * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) 0
        < ε / 3 := hhead_dist
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hhead_nn] at hde
    exact hde
  -- Real partials close.
  have hr1 := hN₀ (m + 1) (by omega : N₀ ≤ m + 1)
  have hr2 := hN₀ (J + 1) (by omega : N₀ ≤ J + 1)
  rw [Real.dist_eq] at hr1 hr2
  -- Matrix partial close.
  have hmP := hN₁ (m + 1) (by omega : N₁ ≤ m + 1)
  -- Monotonicity of real partials.
  have hmono : (∑ j ∈ Finset.range (J + 1),
        ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
      ≤ (∑ j ∈ Finset.range (m + 1),
        ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => norm_nonneg _)
  -- Tail difference of real partials.
  have hsdR : (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
        ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖)
      + (∑ j ∈ Finset.range (J + 1),
        ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
      = (∑ j ∈ Finset.range (m + 1),
        ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) :=
    Finset.sum_sdiff hsub
  have htail_eq : (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
        ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖)
      = (∑ j ∈ Finset.range (m + 1),
        ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
        - (∑ j ∈ Finset.range (J + 1),
        ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) := by
    linarith [hsdR]
  have htail_lt : (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
        ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖) < ε / 3 := by
    rw [htail_eq]
    have habs : |(∑ j ∈ Finset.range (m + 1),
          ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
        - (∑ j ∈ Finset.range (J + 1),
          ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)| < ε / 3 := by
      have htri := abs_sub_le
        (∑ j ∈ Finset.range (m + 1),
          ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
        (∑' (i : ℕ), ‖((((Nat.factorial i : ℕ)) : ℂ))⁻¹ • (A ^ i)‖)
        (∑ j ∈ Finset.range (J + 1),
          ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
      have hsum : ε / 6 + ε / 6 = ε / 3 := by ring
      have hr2' : |(∑' (i : ℕ), ‖((((Nat.factorial i : ℕ)) : ℂ))⁻¹ • (A ^ i)‖)
          - (∑ j ∈ Finset.range (J + 1),
            ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)| < ε / 6 := by
        rw [abs_sub_comm]
        exact hr2
      calc |(∑ j ∈ Finset.range (m + 1),
              ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
            - (∑ j ∈ Finset.range (J + 1),
              ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)|
          ≤ |(∑ j ∈ Finset.range (m + 1),
              ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
            - (∑' (i : ℕ), ‖((((Nat.factorial i : ℕ)) : ℂ))⁻¹ • (A ^ i)‖)|
            + |(∑' (i : ℕ), ‖((((Nat.factorial i : ℕ)) : ℂ))⁻¹ • (A ^ i)‖)
            - (∑ j ∈ Finset.range (J + 1),
              ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)| := htri
        _ < ε / 6 + ε / 6 := add_lt_add hr1 hr2'
        _ = ε / 3 := hsum
    have hnn : 0 ≤ (∑ j ∈ Finset.range (m + 1),
          ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
        - (∑ j ∈ Finset.range (J + 1),
          ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) :=
      sub_nonneg.mpr hmono
    rw [abs_of_nonneg hnn] at habs
    exact habs
  -- Split the matrix difference.
  have hB := one_add_div_pow_eq_sum A m hm1
  have hdiff_eq : (∑ j ∈ Finset.range (m + 1),
        (((binomCoeff m j : ℝ)) : ℂ)
          • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
      - (∑ j ∈ Finset.range (m + 1),
        ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))
      = (∑ j ∈ Finset.range (J + 1),
        ((((binomCoeff m j : ℝ)) : ℂ)
          • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))
          - ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
        + (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
        ((((binomCoeff m x : ℝ)) : ℂ)
          • (((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x))
          - ((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x))) := by
    have hsd : (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
          ((((binomCoeff m x : ℝ)) : ℂ)
            • (((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x))
            - ((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)))
        + (∑ j ∈ Finset.range (J + 1),
          ((((binomCoeff m j : ℝ)) : ℂ)
            • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))
            - ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
        = (∑ j ∈ Finset.range (m + 1),
          ((((binomCoeff m j : ℝ)) : ℂ)
            • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))
            - ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))) :=
      Finset.sum_sdiff hsub
    have hsubd : (∑ j ∈ Finset.range (m + 1),
          ((((binomCoeff m j : ℝ)) : ℂ)
            • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))
            - ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
        = (∑ j ∈ Finset.range (m + 1),
          (((binomCoeff m j : ℝ)) : ℂ)
            • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
          - (∑ j ∈ Finset.range (m + 1),
          ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) :=
      Finset.sum_sub_distrib _ _
    rw [← hsubd, ← hsd, add_comm]
  -- Head matrix bound.
  have hheadM_le : ‖∑ j ∈ Finset.range (J + 1),
        ((((binomCoeff m j : ℝ)) : ℂ)
          • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))
          - ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))‖
      ≤ (∑ j ∈ Finset.range (J + 1),
        |1 - binomCoeff m j| * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖) := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro j _
    exact le_of_eq (norm_binom_term_sub m j _)
  -- Tail matrix bound (each term ≤ exp term).
  have htailM_le : ‖∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
        ((((binomCoeff m x : ℝ)) : ℂ)
          • (((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x))
          - ((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x))‖
      ≤ (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
        ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖) := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_binom_term_sub]
    have hxmem : x ∈ Finset.range (m + 1) :=
      (Finset.mem_sdiff.mp hx).1
    have hxm : x < m + 1 := Finset.mem_range.mp hxmem
    have hjm : x ≤ m := by omega
    obtain ⟨hc0, hc1⟩ := binomCoeff_mem_Icc m x hjm
    have habs1 : |1 - binomCoeff m x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc |1 - binomCoeff m x| * ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖
        ≤ 1 * ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖ :=
          mul_le_mul_of_nonneg_right habs1 (norm_nonneg _)
      _ = ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖ := one_mul _
  -- Combine.
  have hBsub_le : ‖(∑ j ∈ Finset.range (m + 1),
        (((binomCoeff m j : ℝ)) : ℂ)
          • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
      - (∑ j ∈ Finset.range (m + 1),
        ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))‖
      ≤ (∑ j ∈ Finset.range (J + 1),
        |1 - binomCoeff m j| * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
        + (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
        ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖) := by
    rw [hdiff_eq]
    exact le_trans (norm_add_le _ _) (add_le_add hheadM_le htailM_le)
  -- Final triangle.
  have hfin : dist ((1 + ((m : ℂ))⁻¹ • A) ^ m) (NormedSpace.exp A) < ε := by
    rw [hB, dist_eq_norm]
    have htri := norm_add_le
      ((∑ j ∈ Finset.range (m + 1),
        (((binomCoeff m j : ℝ)) : ℂ)
          • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
      - (∑ j ∈ Finset.range (m + 1),
        ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
      ((∑ j ∈ Finset.range (m + 1),
        ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) - NormedSpace.exp A)
    have heq : (∑ j ∈ Finset.range (m + 1),
          (((binomCoeff m j : ℝ)) : ℂ)
            • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
        - NormedSpace.exp A
        = ((∑ j ∈ Finset.range (m + 1),
          (((binomCoeff m j : ℝ)) : ℂ)
            • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
        - (∑ j ∈ Finset.range (m + 1),
          ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
        + ((∑ j ∈ Finset.range (m + 1),
          ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) - NormedSpace.exp A) := by
      abel
    rw [heq]
    have hPm : ‖(∑ j ∈ Finset.range (m + 1),
          ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) - NormedSpace.exp A‖
        < ε / 3 := by
      have hde : dist (∑ j ∈ Finset.range (m + 1),
            ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) (NormedSpace.exp A)
          < ε / 3 := hmP
      rwa [dist_eq_norm] at hde
    have hsum3 : ε / 3 + ε / 3 + ε / 3 = ε := by ring
    calc ‖((∑ j ∈ Finset.range (m + 1),
            (((binomCoeff m j : ℝ)) : ℂ)
              • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
          - (∑ j ∈ Finset.range (m + 1),
            ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
          + ((∑ j ∈ Finset.range (m + 1),
            ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) - NormedSpace.exp A)‖
        ≤ ‖(∑ j ∈ Finset.range (m + 1),
            (((binomCoeff m j : ℝ)) : ℂ)
              • (((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)))
          - (∑ j ∈ Finset.range (m + 1),
            ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j))‖
          + ‖(∑ j ∈ Finset.range (m + 1),
            ((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)) - NormedSpace.exp A‖ := htri
      _ < ((∑ j ∈ Finset.range (J + 1),
            |1 - binomCoeff m j| * ‖((((Nat.factorial j : ℕ)) : ℂ))⁻¹ • (A ^ j)‖)
          + (∑ x ∈ Finset.range (m + 1) \ Finset.range (J + 1),
            ‖((((Nat.factorial x : ℕ)) : ℂ))⁻¹ • (A ^ x)‖)) + ε / 3 :=
          add_lt_add_of_le_of_lt hBsub_le hPm
      _ < (ε / 3 + ε / 3) + ε / 3 :=
          add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_lt hhead_lt htail_lt) le_rfl
      _ = ε := hsum3
  exact hfin

/-- Difference of powers bound (with a `≥1` majorant to avoid `m-1`). -/
lemma pow_sub_pow_norm_le (X Y : Matrix n n ℂ) (m : ℕ) [Nonempty n] :
    ‖X ^ m - Y ^ m‖
      ≤ (m : ℝ) * ((max (max ‖X‖ ‖Y‖) 1) ^ m) * ‖X - Y‖ := by
  set K : ℝ := max (max ‖X‖ ‖Y‖) 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  have hKX : ‖X‖ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKY : ‖Y‖ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  induction m with
  | zero => simp
  | succ m ih =>
    have hdec : X ^ (m + 1) - Y ^ (m + 1)
        = X ^ m * (X - Y) + (X ^ m - Y ^ m) * Y := by
      noncomm_ring
    have hXm : ‖X ^ m‖ ≤ K ^ m :=
      le_trans (norm_pow_le _ _) (pow_le_pow_left₀ (norm_nonneg _) hKX _)
    have hKm : K ^ m ≤ K ^ (m + 1) :=
      pow_le_pow_right₀ hK1 (Nat.le_succ _)
    have hKm1 : K ^ m * K = K ^ (m + 1) := (pow_succ K m).symm
    have hd0 : 0 ≤ ‖X - Y‖ := norm_nonneg _
    have hKmd0 : 0 ≤ (m : ℝ) * K ^ m * ‖X - Y‖ :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hK0 _)) hd0
    have h1 : ‖X ^ m * (X - Y)‖ ≤ K ^ (m + 1) * ‖X - Y‖ := by
      calc ‖X ^ m * (X - Y)‖ ≤ ‖X ^ m‖ * ‖X - Y‖ := norm_mul_le _ _
        _ ≤ K ^ m * ‖X - Y‖ :=
            mul_le_mul_of_nonneg_right hXm hd0
        _ ≤ K ^ (m + 1) * ‖X - Y‖ :=
            mul_le_mul_of_nonneg_right hKm hd0
    have h2 : ‖(X ^ m - Y ^ m) * Y‖ ≤ (m : ℝ) * K ^ (m + 1) * ‖X - Y‖ := by
      calc ‖(X ^ m - Y ^ m) * Y‖ ≤ ‖X ^ m - Y ^ m‖ * ‖Y‖ := norm_mul_le _ _
        _ ≤ ((m : ℝ) * K ^ m * ‖X - Y‖) * ‖Y‖ :=
            mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ((m : ℝ) * K ^ m * ‖X - Y‖) * ‖Y‖ := rfl
        _ ≤ ((m : ℝ) * K ^ m * ‖X - Y‖) * K :=
            mul_le_mul_of_nonneg_left hKY (by positivity : (0:ℝ) ≤ _)
        _ = (m : ℝ) * K ^ (m + 1) * ‖X - Y‖ := by
            rw [pow_succ]; ring
    have h3 : ‖X ^ (m + 1) - Y ^ (m + 1)‖
        ≤ K ^ (m + 1) * ‖X - Y‖ + (m : ℝ) * K ^ (m + 1) * ‖X - Y‖ := by
      rw [hdec]
      exact le_trans (norm_add_le _ _) (add_le_add h1 h2)
    have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have heq : ((m : ℝ) + 1) * K ^ (m + 1) * ‖X - Y‖
        = K ^ (m + 1) * ‖X - Y‖ + (m : ℝ) * K ^ (m + 1) * ‖X - Y‖ := by
      ring
    rw [heq]
    exact h3

/-- Real geometric bound: `(1 + t/m)^m ≤ exp t`. -/
lemma geom_pow_le_exp (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (hm : 0 < m) :
    (1 + t / (m : ℝ)) ^ m ≤ Real.exp t := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have htm_nn : 0 ≤ t / (m : ℝ) :=
    div_nonneg ht (Nat.cast_nonneg _)
  have h1 : (1 + t / (m : ℝ)) ≤ Real.exp (t / (m : ℝ)) := by
    have h := Real.add_one_le_exp (t / (m : ℝ))
    linarith
  have h2 : (1 + t / (m : ℝ)) ^ m ≤ (Real.exp (t / (m : ℝ))) ^ m :=
    pow_le_pow_left₀ (by linarith) h1 _
  have h3 : (Real.exp (t / (m : ℝ))) ^ m = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [h3] at h2
  exact h2

/-- Norm of `(m:ℂ)⁻¹`. -/
lemma norm_nat_inv (m : ℕ) : ‖(((m : ℕ) : ℂ))⁻¹‖ = ((m : ℝ))⁻¹ := by
  rw [norm_inv]
  congr 1
  exact Complex.norm_natCast m

/-- Perturbed version: `(1 + H/m + R_m)^m → exp H` if `m • R_m → 0`. -/
theorem perturbed_pow_tendsto_exp (H : Matrix n n ℂ) (R : ℕ → Matrix n n ℂ) [Nonempty n]
    (hR : Filter.Tendsto (fun m : ℕ => (m : ℝ) • ‖R m‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m : ℕ => (1 + ((m : ℂ))⁻¹ • H + R m) ^ m)
      Filter.atTop (nhds (NormedSpace.exp H)) := by
  have hXlim := one_add_div_pow_tendsto_exp H
  -- Rewrite hypothesis with multiplication.
  have hR' : Filter.Tendsto (fun m : ℕ => (m : ℝ) * ‖R m‖) Filter.atTop (nhds 0) := by
    simpa [smul_eq_mul] using hR
  set E : ℝ := Real.exp (‖H‖ + 1) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hEg : Filter.Tendsto (fun m : ℕ => E * ((m : ℝ) * ‖R m‖))
      Filter.atTop (nhds 0) := by
    have hEconst := tendsto_const_nhds (x := E) (f := (Filter.atTop : Filter ℕ))
    have hmul := hEconst.mul hR'
    simpa using hmul
  -- Difference tends to zero via the power bound.
  have hDlim : Filter.Tendsto
      (fun m : ℕ => (1 + ((m : ℂ))⁻¹ • H + R m) ^ m - (1 + ((m : ℂ))⁻¹ • H) ^ m)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun m : ℕ => E * ((m : ℝ) * ‖R m‖)) ?_ hEg
    · -- Eventually the geometric majorant applies.
      have hev1 : ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) * ‖R m‖ < 1 :=
        hR'.eventually (gt_mem_nhds zero_lt_one)
      have hev0 : ∀ᶠ m : ℕ in Filter.atTop, 0 < m :=
        Filter.eventually_atTop.mpr ⟨1, fun m hm => by omega⟩
      filter_upwards [hev1, hev0] with m hm1 hm0
      have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm0)
      have hRle : ‖R m‖ ≤ 1 / (m : ℝ) := by
        have hpos : (0:ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0
        have heq : ‖R m‖ = ((m : ℝ) * ‖R m‖) * ((m : ℝ))⁻¹ := by
          field_simp
        rw [heq]
        have hle : ((m : ℝ) * ‖R m‖) * ((m : ℝ))⁻¹ ≤ 1 * ((m : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_of_lt hm1) (inv_nonneg.mpr hpos.le)
        rw [one_mul] at hle
        have h1m : (1:ℝ) / (m : ℝ) = ((m : ℝ))⁻¹ := by
          rw [div_eq_mul_inv, one_mul]
        rw [h1m]
        exact hle
      -- Majorants with `t = ‖H‖ + 1`.
      set t : ℝ := ‖H‖ + 1 with htdef
      have ht0 : 0 ≤ t := by positivity
      have hX0 : ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H‖ ≤ 1 + ‖H‖ / (m : ℝ) := by
        calc ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H‖
            ≤ ‖(1 : Matrix n n ℂ)‖ + ‖((m : ℂ))⁻¹ • H‖ := norm_add_le _ _
          _ = 1 + ‖((m : ℂ))⁻¹‖ * ‖H‖ := by rw [norm_one, norm_smul]
          _ = 1 + ((m : ℝ))⁻¹ * ‖H‖ := by rw [norm_nat_inv]
          _ = 1 + ‖H‖ / (m : ℝ) := by rw [div_eq_mul_inv, mul_comm]
      have hdiv : ‖H‖ / (m : ℝ) ≤ t / (m : ℝ) := by
        have hle : ‖H‖ ≤ t := by rw [htdef]; linarith
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (Nat.cast_nonneg _))
      have hXm : ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H‖ ≤ 1 + t / (m : ℝ) := by
        calc ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H‖
            ≤ 1 + ‖H‖ / (m : ℝ) := hX0
          _ ≤ 1 + t / (m : ℝ) := by linarith [hdiv]
      have hYm : ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H + R m‖ ≤ 1 + t / (m : ℝ) := by
        have h1 : ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H + R m‖
            ≤ (1 + ‖H‖ / (m : ℝ)) + 1 / (m : ℝ) :=
          le_trans (norm_add_le _ _) (add_le_add hX0 hRle)
        have h2 : (1 + ‖H‖ / (m : ℝ)) + 1 / (m : ℝ) = 1 + t / (m : ℝ) := by
          rw [htdef, add_div]
          ring
        rw [h2] at h1
        exact h1
      -- Majorant `K` and its power bound.
      set K : ℝ := max (max ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H + R m‖
        ‖(1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H‖) 1 with hKdef
      have hK1 : 1 ≤ K := le_max_right _ _
      have hK0 : 0 ≤ K := le_trans zero_le_one hK1
      have hKle : K ≤ 1 + t / (m : ℝ) :=
        max_le (max_le hYm hXm) (by
          have : (0:ℝ) ≤ t / (m : ℝ) :=
            div_nonneg ht0 (Nat.cast_nonneg _)
          linarith)
      have hKpow : K ^ m ≤ E := by
        calc K ^ m ≤ (1 + t / (m : ℝ)) ^ m :=
              pow_le_pow_left₀ hK0 hKle _
          _ ≤ Real.exp t := geom_pow_le_exp t ht0 m hm0
          _ = E := by rw [hEdef, htdef]
      -- Apply the power-difference bound.
      have hdiff := pow_sub_pow_norm_le
        ((1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H + R m)
        ((1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H) m
      have hRY : ((1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H + R m)
          - ((1 : Matrix n n ℂ) + ((m : ℂ))⁻¹ • H) = R m := by
        abel
      rw [hRY] at hdiff
      have hmR0 : 0 ≤ (m : ℝ) * ‖R m‖ :=
        mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      calc ‖(1 + ((m : ℂ))⁻¹ • H + R m) ^ m - (1 + ((m : ℂ))⁻¹ • H) ^ m‖
          ≤ (m : ℝ) * K ^ m * ‖R m‖ := hdiff
        _ = K ^ m * ((m : ℝ) * ‖R m‖) := by ring
        _ ≤ E * ((m : ℝ) * ‖R m‖) :=
            mul_le_mul_of_nonneg_right hKpow hmR0
  -- Add the vanishing difference to the unperturbed limit.
  have hadd := hXlim.add hDlim
  have hzero : NormedSpace.exp H + 0 = NormedSpace.exp H := add_zero _
  have hfun : (fun m : ℕ => (1 + ((m : ℂ))⁻¹ • H) ^ m
      + ((1 + ((m : ℂ))⁻¹ • H + R m) ^ m - (1 + ((m : ℂ))⁻¹ • H) ^ m))
      = (fun m : ℕ => (1 + ((m : ℂ))⁻¹ • H + R m) ^ m) := by
    funext m
    abel
  rw [hfun, hzero] at hadd
  exact hadd

/-- Subsequence along powers of two (Dyson's use). -/
theorem pow_two_subseq_tendsto_exp (A : Matrix n n ℂ) :
    Filter.Tendsto (fun k : ℕ => (1 + (((2 ^ k : ℕ) : ℂ))⁻¹ • A) ^ (2 ^ k))
      Filter.atTop (nhds (NormedSpace.exp A)) := by
  have hle : ∀ N : ℕ, N ≤ 2 ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      have h2k : 0 < 2 ^ k := pow_pos (by decide : (0:ℕ) < 2) k
      rw [pow_succ]
      omega
  have h2k_lim : Filter.Tendsto (fun k : ℕ => 2 ^ k) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with k hk
    exact le_trans hk (hle k)
  exact (one_add_div_pow_tendsto_exp A).comp h2k_lim
