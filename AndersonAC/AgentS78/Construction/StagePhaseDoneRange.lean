import AndersonAC.AgentS78.Construction.StagePhaseDoneCore

/-!
# The DONE exit of a clearing attempt: localization of the scattering range. Lemma 6.2 (06-clearing.tex:184–257) on the torus index, for the cross block
`C = xCross` of a damped state `(A₀, M₀)` at an eliminated set `O ⊆ A₀`: if `M₀` differs from
direct hops `J` only between sites at zero terminal distance (terminals `univ \ A₀`), the
projection weights decay as `L² exp(−2 a t ρ)` with `ρ = (d_T(·, O) − 1)_+`,
`a = localizationRate d c`, `L = 2 √(K/c)`.

Same argument as `SolS6.range_localization_of_ward` (which is stated on `Fin n`): the torus
matrix `M̃ = M₀` on `A₀ × A₀`, zero elsewhere, is damped and invertible; the exterior equation
holds since the sources of the range lie at collapsed distance `≤ 1` from `O`; the weighted
commutator is small (`weighted_error_row_column_bounds`); `weighted_range_absorption`,
`damping_weight_transfer`, `projection_decay_of_weighted_range` conclude.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.DoneA

open AndersonAC.S78 AndersonAC.AgentS78 AndersonAC.AgentS78Geo
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {d m : ℕ}

theorem matNorm_le_of_vec {R : Type} [Fintype R] [DecidableEq R] (A : Matrix R R ℂ) (K : ℝ)
    (hK : 0 ≤ K) (h : ∀ x : EuclideanSpace ℂ R, ‖Matrix.toEuclideanLin A x‖ ≤ K * ‖x‖) :
    ‖A‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hK h

/-- The collapsed radius `(d_T(i, O) − 1)_+`. -/
def collRadius (A₀ O : Finset (Torus d m)) (i : Torus d m) : ℝ :=
  max (AndersonAC.S6.distanceToCore (terminalDistance (nnGraph d m) (Finset.univ \ A₀)) O i - 1) 0

/-- The torus matrix equal to `M₀` on `A₀ × A₀` and zero elsewhere. -/
def extM (A₀ : Finset (Torus d m)) (M₀ : Matrix (Torus d m) (Torus d m) ℝ) :
    Matrix (Torus d m) (Torus d m) ℝ := Matrix.of fun i k => if i ∈ A₀ ∧ k ∈ A₀ then M₀ i k else 0

/-- **Projection-weight decay** of the cross block at an eliminated set (Lemma 6.2). -/
theorem range_decay (A₀ O : Finset (Torus d m)) (M₀ : Matrix (Torus d m) (Torus d m) ℝ)
    (hsym : ∀ i k, M₀ i k = M₀ k i) (J : Matrix (Torus d m) (Torus d m) ℝ) (hJs : J.IsSymm)
    (hJ1 : ∀ a b, |J a b| ≤ 1) (hJadj : ∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b)
    (hhop : ∀ a ∈ A₀, ∀ b ∈ A₀, M₀ a b ≠ J a b →
      terminalDistance (nnGraph d m) (Finset.univ \ A₀) a b = 0)
    (hO : O ⊆ A₀) (t c K : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hcK : c ≤ K)
    (r : Torus d m → ℂ) (hr : ∀ i, c ≤ (r i).im ∧ (r i).im ≤ K) :
    ∀ i, AndersonAC.S6.projectionWeight (xCross t r A₀ (restrictM A₀ M₀) O) i ≤
      (2 * Real.sqrt (K / c)) ^ 2 * Real.exp (-2 * AndersonAC.SolS6.localizationRate d c * t *
        collRadius A₀ O i) := by
  have hG : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  set a := AndersonAC.SolS6.localizationRate d c with ha_def
  obtain ⟨ha, hrate⟩ := AndersonAC.SolS6.localization_rate_bound d c hc
  set L := 2 * Real.sqrt (K / c) with hL
  have hL0 : 0 ≤ L := by positivity
  set TD := terminalDistance (nnGraph d m) (Finset.univ \ A₀) with hTD
  set ρ := collRadius A₀ O with hρ
  set C := xCross t r A₀ (restrictM A₀ M₀) O with hC
  have hpos : ∀ i, 0 < (r i).im := fun i => hc.trans_le (hr i).1
  -- geometry of ρ
  have hnn : ∀ a b, 0 ≤ TD a b := fun a b => AndersonAC.AgentS78Geo.terminalDistance_nonneg _ _ _ _
  have hsymTD : ∀ a b, TD a b = TD b a := fun a b => terminalDistance_symm hG _ _ _
  have htri : ∀ a b c, TD a c ≤ TD a b + TD b c := fun a b c => terminalDistance_triangle hG _ _ _ _
  have hρlip : ∀ i k, |ρ i - ρ k| ≤ TD i k := by
    intro i k
    have h := distanceToCore_abs_sub_le TD hnn hsymTD htri O i k
    simp only [hρ, collRadius]
    exact (abs_max_sub_max_le_abs _ _ _).trans (by
      rw [show AndersonAC.S6.distanceToCore TD O i - 1 -
        (AndersonAC.S6.distanceToCore TD O k - 1) =
        AndersonAC.S6.distanceToCore TD O i - AndersonAC.S6.distanceToCore TD O k by ring]
      exact h)
  have hρ0 : ∀ i, 0 ≤ ρ i := fun i => le_max_right _ _
  -- the extended matrices
  set Mt := extM A₀ M₀ with hMt
  set Jt : Matrix (Torus d m) (Torus d m) ℝ := Matrix.of fun i k => if i ∈ A₀ ∧ k ∈ A₀ then J i k else 0
    with hJt
  set Kt := Mt - Jt with hKt
  have hMJK : Jt + Kt = Mt := by rw [hKt]; abel
  have hMts : Mt.IsSymm := Matrix.IsSymm.ext fun i k => by
    simp only [hMt, extM, Matrix.of_apply]
    by_cases h : i ∈ A₀ ∧ k ∈ A₀
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, hsym]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  have hJts : Jt.IsSymm := Matrix.IsSymm.ext fun i k => by
    simp only [hJt, Matrix.of_apply]
    by_cases h : i ∈ A₀ ∧ k ∈ A₀
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, hJs.apply]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  have hJt1 : ∀ i k, |Jt i k| ≤ 1 := fun i k => by
    simp only [hJt, Matrix.of_apply]; split_ifs
    · exact hJ1 i k
    · simp
  have hJtadj : ∀ i k, Jt i k ≠ 0 → (nnGraph d m).Adj i k := fun i k h => by
    simp only [hJt, Matrix.of_apply] at h; split_ifs at h
    · exact hJadj i k h
    · exact absurd rfl h
  have hdeg : ∀ i, ((Finset.univ.filter (fun k => Jt i k ≠ 0)).card : ℝ) ≤ 2 * d :=
    card_filter_le_of_adj d (fun u S hS => nnGraph_degree_le u S hS) id Function.injective_id Jt
      (fun i k h => hJtadj i k h)
  have hJρ : ∀ i k, Jt i k ≠ 0 → |ρ i - ρ k| ≤ 1 := fun i k h =>
    (hρlip i k).trans (terminalDistance_adj_le_one _ _ (hJtadj i k h))
  have hKρ : ∀ i k, Kt i k ≠ 0 → ρ i = ρ k := by
    intro i k h
    have hik : i ∈ A₀ ∧ k ∈ A₀ := by
      by_contra hn
      apply h
      simp only [hKt, hMt, hJt, extM, Matrix.sub_apply, Matrix.of_apply, if_neg hn, sub_zero]
    have hne : M₀ i k ≠ J i k := by
      intro he; apply h
      simp only [hKt, hMt, hJt, extM, Matrix.sub_apply, Matrix.of_apply, if_pos hik, he, sub_self]
    have h0 := hhop i hik.1 k hik.2 hne
    have := hρlip i k
    rw [h0] at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  have hKts : Kt.IsSymm := hMts.sub hJts
  -- the damped matrix and the weights
  set H := AndersonAC.S6.dampedMatrix (Jt + Kt) t r with hH
  have hHunit : IsUnit H.det := by
    rw [hH, hMJK]; exact damped_isUnit Mt hMts t c ht hc r (fun i => (hr i).1)
  set E := AndersonAC.S6.exponentialWeight a t ρ with hE
  set En := AndersonAC.S6.exponentialWeight (-a) t ρ with hEn
  set Err := E * H * En - H with hErr
  obtain ⟨_, hEnE⟩ := AndersonAC.SolS6.exponential_weight_inverse a t ρ
  have hcomm : E * H = (H + Err) * E := by
    symm
    calc (H + Err) * E = (E * H * En) * E := by rw [hErr]; noncomm_ring
      _ = E * H * (En * E) := by simp only [Matrix.mul_assoc]
      _ = E * H := by rw [hEnE, Matrix.mul_one]
  have herr : ‖Err‖ ≤ c * t / 4 := by
    obtain ⟨hrows, hcols⟩ := AndersonAC.SolS6.weighted_error_row_column_bounds d a t ρ Jt Kt r
      ha.le ht.le hJts hJt1 hdeg hJρ hKρ
    have hU := hrate t ht.le ht1
    have hct : 0 ≤ c * t / 4 := by positivity
    apply matNorm_le_of_vec _ _ hct
    intro x
    have := schur_vec Err (c * t / 4) (c * t / 4) hct hct (fun i => (hrows i).trans hU)
      (fun j => (hcols j).trans hU) x
    rwa [Real.sqrt_mul_self hct] at this
  have hHinv : ‖H⁻¹‖ ≤ (t * c)⁻¹ := by
    apply matNorm_le_of_vec _ _ (by positivity)
    intro y
    have hlow := damped_lower (Jt + Kt) (hJts.add hKts) t c ht.le r (fun i => (hr i).1)
      (Matrix.toEuclideanLin H⁻¹ y)
    have hHH : Matrix.toEuclideanLin H (Matrix.toEuclideanLin H⁻¹ y) = y := by
      have h := congrArg (fun A => Matrix.toEuclideanLin A y) (Matrix.mul_nonsing_inv H hHunit)
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
        LinearMap.comp_apply, LinearMap.id_apply] using h
    rw [← hH, hHH] at hlow
    have htc : 0 < t * c := mul_pos ht hc
    rw [inv_mul_eq_div, le_div_iff₀ htc]
    linarith
  have hsmall : ‖H⁻¹ * Err‖ ≤ 1 / 2 := by
    calc ‖H⁻¹ * Err‖ ≤ ‖H⁻¹‖ * ‖Err‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (t * c)⁻¹ * (c * t / 4) :=
        mul_le_mul hHinv herr (norm_nonneg _) (by positivity)
      _ = 1 / 4 := by field_simp
      _ ≤ 1 / 2 := by norm_num
  -- the damping weights
  set p := AndersonAC.S6.imagDamping r with hp
  have hpl : ∀ i, c ≤ p i := fun i => (hr i).1
  have hpu : ∀ i, p i ≤ K := fun i => (hr i).2
  have hp0 : ∀ i, 0 < p i := fun i => hpos i
  set D := AndersonAC.S6.sqrtDamping p with hD
  have hDunit : IsUnit D.det := AndersonAC.SolS6.sqrtDamping_unit p hp0
  have hsq0 : ∀ i, (Real.sqrt (p i) : ℂ) ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp0 i)).ne'
  set G := fullInv A₀ M₀ t r with hGdef
  have hEq := fullInv_eqns A₀ M₀ t r hsym ht hpos
  have hweighted : ∀ v ∈ AndersonAC.S6.matrixRange C,
      ‖Matrix.toEuclideanLin E v‖ ≤ L * ‖v‖ := by
    intro v hv
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hv
    set w := Matrix.toEuclideanLin D⁻¹ v with hw_def
    have hvw : v = Matrix.toEuclideanLin D w := by
      have h := congrArg (fun A => Matrix.toEuclideanLin A v) (Matrix.mul_nonsing_inv D hDunit)
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        Matrix.toLpLin_one, LinearMap.comp_apply, LinearMap.id_apply] using h.symm
    set y : {b // b ∈ O} → ℂ := fun b =>
      2 * Complex.I * (t : ℂ) * (Real.sqrt (p b) : ℂ) * z.ofLp b with hy
    have hwl : ∀ l, w.ofLp l = if l ∈ A₀ ∧ l ∉ O then ∑ b : {b // b ∈ O}, G l b * y b else 0 := by
      intro l
      rw [hw_def, toEuclideanLin_apply', hD, sqrtDamping_inv p hp0]
      rw [Finset.sum_eq_single l (fun k _ hk => by
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]) (fun h => absurd
        (Finset.mem_univ l) h)]
      rw [Matrix.diagonal_apply_eq, ← hz, toEuclideanLin_apply']
      simp only [hC, xCross_entry t r A₀ O M₀ hO]
      split_ifs with hl
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hsqr : ((Real.sqrt (r l).im : ℝ) : ℂ) ≠ 0 := hsq0 l
        rw [hy]
        simp only [hp, hGdef, AndersonAC.S6.imagDamping]
        field_simp
      · simp
    have hsrc : ∀ i, 0 < ρ i → (Matrix.toEuclideanLin H w).ofLp i = 0 := by
      intro i hi
      have hfar := far_of_radius_pos TD O i hi
      rw [toEuclideanLin_apply']
      have hHil : ∀ l, H i l = (Mt i l : ℂ) - (t : ℂ) * (if i = l then r i else 0) := by
        intro l
        rw [hH, hMJK]
        simp only [AndersonAC.S6.dampedMatrix, Matrix.sub_apply, Matrix.map_apply,
          Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
      by_cases hiA : i ∈ A₀
      · have hiO : i ∉ O := fun h => by
          have := hfar i h
          have h0 : TD i i = 0 := terminalDistance_self _ _ _
          linarith
        have hMO : ∀ l ∈ O, M₀ i l = 0 := by
          intro l hl
          by_contra hne
          have hlA := hO hl
          by_cases hJ : M₀ i l = J i l
          · have hadj := hJadj i l (hJ ▸ hne)
            have := hfar l hl
            have := terminalDistance_adj_le_one (nnGraph d m) (Finset.univ \ A₀) hadj
            linarith
          · have h0 := hhop i hiA l hlA hJ
            have := hfar l hl
            linarith
        have hkey : ∀ l, H i l * w.ofLp l =
            if l ∈ A₀ then dEnt t r M₀ i l * ∑ b : {b // b ∈ O}, G l b * y b else 0 := by
          intro l
          rw [hwl l, hHil l]
          by_cases hlA : l ∈ A₀
          · by_cases hlO : l ∈ O
            · have hd : dEnt t r M₀ i l = 0 := by
                unfold dEnt
                rw [hMO l hlO, if_neg (show ¬ (i = l) from fun h => hiO (by rw [h]; exact hlO))]
                simp
              simp only [show ¬(l ∈ A₀ ∧ l ∉ O) from fun h => h.2 hlO, if_false, if_pos hlA,
                mul_zero, hd, zero_mul]
            · simp [hlA, hlO, hiA, hMt, extM, dEnt]
          · simp [hlA]
        rw [Finset.sum_congr rfl fun l _ => hkey l, Finset.sum_ite_mem, Finset.univ_inter]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro b _
        have h1 : ∑ l ∈ A₀, dEnt t r M₀ i l * (G l b * y b) =
            (∑ l ∈ A₀, dEnt t r M₀ i l * G l b) * y b := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [h1, hEq i hiA b (hO b.2), if_neg (show ¬ (i = (b : Torus d m)) from fun h => hiO (h ▸ b.2)),
          zero_mul]
      · have hzero : ∀ l, H i l * w.ofLp l = 0 := by
          intro l
          rw [hHil l]
          have hM0 : Mt i l = 0 := by
            simp [hMt, extM, hiA]
          by_cases hil : i = l
          · rw [hwl l, if_neg (show ¬(l ∈ A₀ ∧ l ∉ O) from fun h => hiA (hil ▸ h.1)), mul_zero]
          · rw [hM0, if_neg hil]; simp
        exact Finset.sum_eq_zero fun l _ => hzero l
    have hsource : Matrix.toEuclideanLin E (Matrix.toEuclideanLin H w) =
        Matrix.toEuclideanLin H w := by
      ext i
      rw [toEuclideanLin_apply']
      rw [Finset.sum_eq_single i (fun k _ hk => by
        rw [hE]; simp [AndersonAC.S6.exponentialWeight, Matrix.diagonal_apply_ne _ (Ne.symm hk)])
        (fun h => absurd (Finset.mem_univ i) h)]
      rw [hE]
      simp only [AndersonAC.S6.exponentialWeight, Matrix.diagonal_apply_eq]
      by_cases hi : 0 < ρ i
      · rw [hsrc i hi, mul_zero]
      · have hz0 : ρ i = 0 := le_antisymm (le_of_not_gt hi) (hρ0 i)
        rw [hz0]; simp
    have hw := AndersonAC.SolS6.weighted_range_absorption H E Err w hHunit hcomm hsource hsmall
    exact AndersonAC.SolS6.damping_weight_transfer a t c K p ρ v w hc hcK hpl hpu hvw hw
  exact AndersonAC.SolS6.projection_decay_of_weighted_range C a t L ρ hL0 hweighted

end AndersonAC.AgentS78.DoneA
