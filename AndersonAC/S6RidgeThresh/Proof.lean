import AndersonAC.S6.Ridge

/-! Scalar ridge threshold existence and uniqueness. -/

noncomputable section

open Filter
open scoped ComplexOrder MatrixOrder Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

private theorem continuousOn_maxWeight {R : Type*} [Fintype R] [DecidableEq R]
    (g : R → ℝ → ℝ) (s : Set ℝ)
    (hg : ∀ i, ContinuousOn (fun τ => g i τ) s) :
    ContinuousOn (fun τ => AndersonAC.S6.maxWeight (fun i => g i τ)) s := by
  classical
  have hsup : ContinuousOn
      (fun τ : ℝ => (Finset.univ : Finset R).sup (fun i => Real.toNNReal (g i τ))) s := by
    induction (Finset.univ : Finset R) using Finset.induction_on with
    | empty =>
        simp only [Finset.sup_empty]
        exact continuousOn_const
    | @insert a t ha ih =>
        simp only [Finset.sup_insert]
        exact (continuous_real_toNNReal.continuousOn.comp' (hg a)
          (by intro x hx; exact Set.mem_univ _)).sup ih
  unfold AndersonAC.S6.maxWeight
  exact NNReal.continuous_coe.continuousOn.comp' hsup
    (by intro x hx; exact Set.mem_univ _)

private theorem le_maxWeight_of_nonneg {R : Type*} [Fintype R] [DecidableEq R]
    (m : R → ℝ) (i : R) (hi : 0 ≤ m i) :
    m i ≤ AndersonAC.S6.maxWeight m := by
  classical
  unfold AndersonAC.S6.maxWeight
  rw [← Real.coe_toNNReal (m i) hi]
  change Real.toNNReal (m i) ≤
    Finset.univ.sup (fun j => Real.toNNReal (m j))
  exact Finset.le_sup (f := fun j => Real.toNNReal (m j)) (Finset.mem_univ i)

private theorem maxWeight_le_of_forall_le {R : Type*} [Fintype R] [DecidableEq R]
    (m : R → ℝ) (a : ℝ) (ha : 0 ≤ a) (h : ∀ i, m i ≤ a) :
    AndersonAC.S6.maxWeight m ≤ a := by
  classical
  unfold AndersonAC.S6.maxWeight
  rw [← Real.coe_toNNReal a ha]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  exact Real.toNNReal_le_toNNReal (h i)

private theorem exists_eq_maxWeight_of_pos {R : Type*} [Fintype R] [DecidableEq R]
    (m : R → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : 0 < AndersonAC.S6.maxWeight m) :
    ∃ i, AndersonAC.S6.maxWeight m = m i := by
  classical
  have hne : (Finset.univ : Finset R).Nonempty := by
    by_contra h
    have hEq : (Finset.univ : Finset R) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [AndersonAC.S6.maxWeight, hEq] at hpos
  obtain ⟨i, hi, hsup⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset R) hne
      (fun i => Real.toNNReal (m i))
  refine ⟨i, ?_⟩
  unfold AndersonAC.S6.maxWeight
  rw [hsup, Real.coe_toNNReal (m i) (hm i)]

private theorem row_nonzero_of_leverage_pos {B R : Type*}
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) (τ : ℝ) (i : R) (hpos : 0 < AndersonAC.S6.leverage C τ i) :
    ∃ b, C i b ≠ 0 := by
  classical
  by_contra hrow
  push Not at hrow
  have hz : AndersonAC.S6.ridgeProjection C τ i i = 0 := by
    simp [AndersonAC.S6.ridgeProjection, Matrix.mul_apply, hrow]
  change 0 < (AndersonAC.S6.ridgeProjection C τ i i).re at hpos
  rw [hz] at hpos
  exact (lt_irrefl 0 hpos)

private theorem maxWeight_strict_decreasing {B R : Type*}
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hτ : τ₁ < τ₂) (hpos : 0 < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ₂)) :
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ₂) <
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ₁) := by
  classical
  have hcal₂ := AndersonAC.S6.ridge_calculus C τ₂ hτ₂
  rcases hcal₂ with ⟨_, _, _, _, hlev₂, _, _⟩
  obtain ⟨i, hi⟩ := exists_eq_maxWeight_of_pos
    (AndersonAC.S6.leverage C τ₂) (fun j => (hlev₂ j).1) hpos
  have hi_pos : 0 < AndersonAC.S6.leverage C τ₂ i := by rw [← hi]; exact hpos
  obtain ⟨b, hb⟩ := row_nonzero_of_leverage_pos C τ₂ i hi_pos
  have hstrict := (AndersonAC.S6.ridge_continuous_monotone C i).2.2 ⟨b, hb⟩
  have hrow : AndersonAC.S6.leverage C τ₂ i < AndersonAC.S6.leverage C τ₁ i :=
    hstrict (Set.mem_Ioi.mpr hτ₁) (Set.mem_Ioi.mpr hτ₂) hτ
  have hcal₁ := AndersonAC.S6.ridge_calculus C τ₁ hτ₁
  rcases hcal₁ with ⟨_, _, _, _, hlev₁, _, _⟩
  calc
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ₂) =
        AndersonAC.S6.leverage C τ₂ i := hi
    _ < AndersonAC.S6.leverage C τ₁ i := hrow
    _ ≤ AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ₁) :=
      le_maxWeight_of_nonneg _ i (hlev₁ i).1

private theorem gram_conjTranspose_le_norm_sq {B R : Type*}
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) :
    C * Cᴴ ≤ (‖C‖ ^ 2 : ℝ) • (1 : Matrix R R ℂ) := by
  classical
  let q : ℝ := ‖C‖
  let s : ℝ := q ^ 2
  have hs_nonneg : 0 ≤ s := sq_nonneg q
  by_cases hq : q = 0
  · have hC : C = 0 := norm_eq_zero.mp hq
    simp [hC]
  · have hs_pos : 0 < s := sq_pos_of_ne_zero hq
    have hpsd : (C * Cᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose C
    have hnorm : ‖C * Cᴴ‖ = s := by
      calc
        ‖C * Cᴴ‖ = ‖C‖ * ‖C‖ := by
          simpa [Matrix.l2_opNorm_conjTranspose] using
            (Matrix.l2_opNorm_conjTranspose_mul_self Cᴴ)
        _ = s := by simp [q, s, pow_two]
    have hscaled_norm : ‖s⁻¹ • (C * Cᴴ)‖ ≤ 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr hs_pos.le), hnorm]
      rw [inv_mul_cancel₀ hs_pos.ne']
    have hscaled_psd : (s⁻¹ • (C * Cᴴ)).PosSemidef :=
      Matrix.PosSemidef.smul hpsd (inv_nonneg.mpr hs_pos.le)
    have hscaled_order : s⁻¹ • (C * Cᴴ) ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hscaled_psd.nonneg).mp hscaled_norm
    have hmul := smul_le_smul_of_nonneg_left hscaled_order hs_nonneg
    have hresult : C * Cᴴ ≤ s • (1 : Matrix R R ℂ) := by
      simpa [smul_smul, hs_pos.ne'] using hmul
    simpa [q, s] using hresult

private theorem maxWeight_ridge_bound {B R : Type*}
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) :
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ) ≤ ‖C‖ ^ 2 / τ := by
  classical
  let A : Matrix B B ℂ := AndersonAC.S6.ridgeGram C τ
  let T : Matrix B B ℂ := (τ : ℂ) • (1 : Matrix B B ℂ)
  have hGram : (AndersonAC.S6.gram C).PosSemidef := by
    unfold AndersonAC.S6.gram
    exact Matrix.posSemidef_conjTranspose_mul_self C
  have hT : T.PosDef := by
    rw [show T = (τ : ℂ) • (1 : Matrix B B ℂ) by rfl,
      Matrix.smul_one_eq_diagonal]
    apply Matrix.PosDef.diagonal
    intro i
    simpa using hτ
  have hA : A.PosDef := by
    dsimp [A]
    unfold AndersonAC.S6.ridgeGram
    exact Matrix.PosDef.posSemidef_add hGram hT
  have hTA : T ≤ A := by
    rw [Matrix.le_iff]
    change (A - T).PosSemidef
    simpa [A, T, AndersonAC.S6.ridgeGram] using hGram
  have hInv : A⁻¹ ≤ T⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
    exact CStarAlgebra.ringInverse_le_ringInverse hTA hT.isStrictlyPositive
  have hConj : C * A⁻¹ * Cᴴ ≤ C * T⁻¹ * Cᴴ := by
    rw [Matrix.le_iff]
    have hFactor : C * T⁻¹ * Cᴴ - C * A⁻¹ * Cᴴ =
        C * (T⁻¹ - A⁻¹) * Cᴴ := by
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    rw [hFactor]
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (Matrix.le_iff.mp hInv).conjTranspose_mul_mul_same Cᴴ
  have hTinv : T⁻¹ = (τ⁻¹ : ℝ) • (1 : Matrix B B ℂ) := by
    apply Matrix.inv_eq_right_inv
    change ((τ : ℂ) • (1 : Matrix B B ℂ)) *
      ((τ⁻¹ : ℝ) • (1 : Matrix B B ℂ)) = 1
    ext i j
    simp [Matrix.mul_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, hτ.ne']
  have hScalar : C * T⁻¹ * Cᴴ = (τ⁻¹ : ℝ) • (C * Cᴴ) := by
    rw [hTinv]
    ext i j
    simp [Matrix.mul_apply, Matrix.smul_apply, mul_assoc, mul_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hCorder := gram_conjTranspose_le_norm_sq C
  have hCscaled : (τ⁻¹ : ℝ) • (C * Cᴴ) ≤
      (τ⁻¹ : ℝ) • ((‖C‖ ^ 2 : ℝ) • (1 : Matrix R R ℂ)) :=
    smul_le_smul_of_nonneg_left hCorder (inv_nonneg.mpr hτ.le)
  have hbound : C * A⁻¹ * Cᴴ ≤ (‖C‖ ^ 2 / τ : ℝ) • (1 : Matrix R R ℂ) := by
    calc
      C * A⁻¹ * Cᴴ ≤ C * T⁻¹ * Cᴴ := hConj
      _ = (τ⁻¹ : ℝ) • (C * Cᴴ) := hScalar
      _ ≤ (τ⁻¹ : ℝ) • ((‖C‖ ^ 2 : ℝ) • (1 : Matrix R R ℂ)) := hCscaled
      _ = (‖C‖ ^ 2 / τ : ℝ) • (1 : Matrix R R ℂ) := by
        rw [smul_smul]
        congr 1
        ring
  have hPoint : ∀ i : R, AndersonAC.S6.leverage C τ i ≤ ‖C‖ ^ 2 / τ := by
    intro i
    have hi := (Matrix.le_iff.mp hbound).diag_nonneg (i := i)
    have hcomplex : (C * A⁻¹ * Cᴴ) i i ≤ (‖C‖ ^ 2 / τ : ℝ) := by
      simpa [Matrix.smul_one_eq_diagonal] using hi
    have hre : ((C * A⁻¹ * Cᴴ) i i).re ≤ ‖C‖ ^ 2 / τ := by
      exact_mod_cast (Complex.le_def.mp hcomplex).1
    change (AndersonAC.S6.ridgeProjection C τ i i).re ≤ ‖C‖ ^ 2 / τ
    simpa [AndersonAC.S6.ridgeProjection, A] using hre
  unfold AndersonAC.S6.maxWeight
  rw [← Real.coe_toNNReal (‖C‖ ^ 2 / τ)
    (div_nonneg (sq_nonneg ‖C‖) hτ.le)]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  exact Real.toNNReal_le_toNNReal (hPoint i)

/-- The scalar portion of the ridge-threshold statement. -/
theorem ridgeThreshold_scalar_proof :
    ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
      (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l)
      (hlarge : 2 * l < AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C)),
      AndersonAC.S6.Planned.ridge_threshold C l hl hlarge := by
  intro B R instB instDecB instR instDecR C l hl hlarge
  classical
  let a : ℝ := 2 * l
  let f : ℝ → ℝ := fun τ =>
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlarge' : a < AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C) := by
    simpa [a] using hlarge
  have hlargeNN : Real.toNNReal a <
      (Finset.univ : Finset R).sup (fun i => Real.toNNReal (AndersonAC.S6.projectionWeight C i)) := by
    apply NNReal.coe_lt_coe.mp
    rw [Real.coe_toNNReal a ha.le]
    simpa [AndersonAC.S6.maxWeight] using hlarge'
  obtain ⟨i, hi, hpiNN⟩ := (Finset.lt_sup_iff).mp hlargeNN
  have hpi : a < AndersonAC.S6.projectionWeight C i := by
    have hcast : (Real.toNNReal a : ℝ) <
        (Real.toNNReal (AndersonAC.S6.projectionWeight C i) : ℝ) := by
      exact_mod_cast hpiNN
    rw [Real.coe_toNNReal a ha.le,
      Real.coe_toNNReal (AndersonAC.S6.projectionWeight C i)
        (AndersonAC.S6.projection_coordinate C i).1] at hcast
    exact hcast
  have hcoord : Continuous (fun M : Matrix R R ℂ => (M i i).re) := by fun_prop
  have hscalar : Tendsto (fun τ : ℝ => AndersonAC.S6.leverage C τ i)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (AndersonAC.S6.projectionWeight C i)) := by
    simpa [Function.comp_def, AndersonAC.S6.leverage, AndersonAC.S6.projectionWeight] using
      (hcoord.continuousAt (x := AndersonAC.S6.rangeProjection C)).tendsto.comp
        (AndersonAC.S6.ridge_limit C)
  have hne : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    simp
  haveI := hne
  have hev : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a < AndersonAC.S6.leverage C τ i :=
    hscalar.eventually (Ioi_mem_nhds hpi)
  have hposEv : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < τ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact Set.mem_Ioi.mp hτ
  obtain ⟨ε, hεlev, hεpos⟩ := (hev.and hposEv).exists
  have hcalε := AndersonAC.S6.ridge_calculus C ε hεpos
  rcases hcalε with ⟨_, _, _, _, hlevε, _, _⟩
  have hεlow : a < f ε := lt_of_lt_of_le hεlev (le_maxWeight_of_nonneg _ i (hlevε i).1)
  have hrows : ∀ j, ContinuousOn (fun τ => AndersonAC.S6.leverage C τ j) (Set.Ioi 0) :=
    fun j => (AndersonAC.S6.ridge_continuous_monotone C j).1
  have hfcont : ContinuousOn f (Set.Ioi 0) := by
    dsimp [f]
    exact continuousOn_maxWeight (fun j τ => AndersonAC.S6.leverage C τ j)
      (Set.Ioi 0) hrows
  let q2 : ℝ := ‖C‖ ^ 2
  let T : ℝ := max ε (q2 / a) + 1
  have hεT : ε < T := by
    dsimp [T]
    have hle := le_max_left ε (q2 / a)
    linarith
  have hqT : q2 / a < T := by
    dsimp [T]
    have hle := le_max_right ε (q2 / a)
    linarith
  have hTpos : 0 < T := lt_trans hεpos hεT
  have hqT' : q2 < T * a := (div_lt_iff₀ ha).mp hqT
  have hTlow : q2 / T < a := (div_lt_iff₀ hTpos).2 (by simpa [mul_comm] using hqT')
  have hTupper : f T < a := by
    dsimp [f, q2]
    exact lt_of_le_of_lt (maxWeight_ridge_bound C T hTpos) hTlow
  have hcontIcc : ContinuousOn f (Set.Icc ε T) :=
    hfcont.mono (by
      intro τ hτ
      exact Set.mem_Ioi.mpr (lt_of_lt_of_le hεpos hτ.1))
  have haIcc : a ∈ Set.Icc (f T) (f ε) := ⟨hTupper.le, hεlow.le⟩
  obtain ⟨r, hrmem, hfr⟩ :=
    (intermediate_value_Icc' hεT.le hcontIcc) haIcc
  have hrpos : 0 < r := lt_of_lt_of_le hεpos hrmem.1
  have hrSet : r ∈ {τ : ℝ | 0 < τ ∧ 2 * l ≤
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ)} := by
    change 0 < r ∧ a ≤ f r
    exact ⟨hrpos, by simp [hfr]⟩
  have hSetBound : ∀ τ ∈ {τ : ℝ | 0 < τ ∧ 2 * l ≤
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ)}, τ ≤ r := by
    intro τ hτ
    change 0 < τ ∧ a ≤ f τ at hτ
    rcases hτ with ⟨hτpos, hτlevel⟩
    by_contra hnot
    have hrt : r < τ := lt_of_not_ge hnot
    have hstrict := maxWeight_strict_decreasing C hrpos hτpos hrt
      (lt_of_lt_of_le ha hτlevel)
    have hstrict' : f τ < f r := hstrict
    rw [hfr] at hstrict'
    exact (not_lt_of_ge hτlevel) hstrict'
  have hthreshold : AndersonAC.S6.ridgeThreshold C l = r := by
    unfold AndersonAC.S6.ridgeThreshold
    apply le_antisymm
    · exact csSup_le ⟨r, hrSet⟩ hSetBound
    · exact le_csSup ⟨r, hSetBound⟩ hrSet
  refine ⟨?_, ?_, ?_⟩
  · rw [hthreshold]
    exact hrpos
  · rw [hthreshold]
    simpa [f] using hfr
  · intro τ hτpos hτeq
    rw [hthreshold]
    rcases lt_trichotomy τ r with hτr | hEq | hrτ
    · have hrlevelpos : 0 < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C r) := by
        change 0 < f r
        rw [hfr]
        exact ha
      have hstrict := maxWeight_strict_decreasing C hτpos hrpos hτr hrlevelpos
      have hstrict' : f r < f τ := hstrict
      have hτeq' : f τ = a := by simpa [f, a] using hτeq
      rw [hfr, hτeq'] at hstrict'
      exact False.elim (lt_irrefl a hstrict')
    · exact hEq
    · have hstrict := maxWeight_strict_decreasing C hrpos hτpos hrτ (by
        rw [hτeq]
        simpa [a] using ha)
      have hstrict' : f τ < f r := hstrict
      have hτeq' : f τ = a := by simpa [f, a] using hτeq
      rw [hτeq', hfr] at hstrict'
      exact False.elim (lt_irrefl a hstrict')

end AndersonAC.SolS6
