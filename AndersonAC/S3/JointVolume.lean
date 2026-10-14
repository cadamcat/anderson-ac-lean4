import AndersonAC.S3.JointShell
import AndersonAC.S3.HelperStatements2

/-!
Joint energy-shell volume in the sliced coordinates `x_j = sin(k_j + ζ_j/2)`
(§3 of `03-initialization.tex`, lines 456–526).

The two dispersions `A_∓ = slicedDispersion (∓1) ζ` differ by the linear form
`b·x`, `b_j = 4 sin(ζ_j/2)`. The joint shell lies in the slab `|b·x| ≤ s₁+s₂`;
each hyperplane slice of the narrower shell has volume `O(min(s₁,s₂))` by
strong convexity (tangential slices included). The two geometric inputs are
the frozen helper statements `SlabSliceStatement` and `ConvexShellStatement`,
taken here as hypotheses until the helper proofs are integrated.
-/

noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped BigOperators ENNReal NNReal

namespace AndersonAC.S3

/-- The affine parametrization of the hyperplane `∑ b_j x_j = τ` by the
coordinates other than `j₀`, exactly as in `SlabSliceStatement`. -/
def slicePoint {n : ℕ} (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (τ : ℝ)
    (x' : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) j₀ ((τ - ∑ i, b (j₀.succAbove i) * x' i) / b j₀) x'

/-- The box-restricted energy shell of one sliced dispersion. -/
def boxShell {d : ℕ} (σ : ℝ) (ζ : Frequency d) (E s : ℝ) : Set (Frequency d) :=
  {x | (∀ j, |x j| ≤ 1 / 4) ∧ |slicedDispersion σ ζ x - E| ≤ s}

theorem slicedDispersion_continuous {d : ℕ} (σ : ℝ) (ζ : Frequency d) :
    Continuous (slicedDispersion σ ζ) := by
  unfold slicedDispersion
  fun_prop

theorem boxShell_isClosed {d : ℕ} (σ : ℝ) (ζ : Frequency d) (E s : ℝ) :
    IsClosed (boxShell σ ζ E s) := by
  have h1 : IsClosed {x : Frequency d | ∀ j, |x j| ≤ 1 / 4} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {x : Frequency d | |slicedDispersion σ ζ x - E| ≤ s} :=
    isClosed_le (by
      have := slicedDispersion_continuous σ ζ
      fun_prop) continuous_const
  exact h1.inter h2

theorem slicePoint_continuous {n : ℕ} (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (τ : ℝ) :
    Continuous (slicePoint b j₀ τ) := by
  apply continuous_pi
  intro j
  rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨i, rfl⟩
  · simp only [slicePoint, Fin.insertNth_apply_same]
    fun_prop
  · simp only [slicePoint, Fin.insertNth_apply_succAbove]
    fun_prop

theorem slicePoint_affine {n : ℕ} (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (τ : ℝ)
    (x y : Fin n → ℝ) (a c : ℝ) (hac : a + c = 1) :
    slicePoint b j₀ τ (a • x + c • y) = a • slicePoint b j₀ τ x + c • slicePoint b j₀ τ y := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove j₀ j with h | ⟨i, rfl⟩
  · rw [h]
    simp only [slicePoint, Fin.insertNth_apply_same, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hs : ∑ i, b (j₀.succAbove i) * (a * x i + c * y i) =
        a * ∑ i, b (j₀.succAbove i) * x i + c * ∑ i, b (j₀.succAbove i) * y i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs]
    have hτ : τ = a * τ + c * τ := by rw [← add_mul, hac, one_mul]
    conv_lhs => rw [hτ]
    ring
  · simp only [slicePoint, Fin.insertNth_apply_succAbove, Pi.add_apply, Pi.smul_apply]

theorem slicePoint_dist_sq {n : ℕ} (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (τ : ℝ)
    (x y : Fin n → ℝ) :
    ∑ i, (x i - y i) ^ 2 ≤ ∑ j, (slicePoint b j₀ τ x j - slicePoint b j₀ τ y j) ^ 2 := by
  rw [Fin.sum_univ_succAbove _ j₀]
  simp only [slicePoint, Fin.insertNth_apply_succAbove]
  linarith [sq_nonneg ((Fin.insertNth (α := fun _ => ℝ) j₀
      ((τ - ∑ i, b (j₀.succAbove i) * x i) / b j₀) x j₀) -
    (Fin.insertNth (α := fun _ => ℝ) j₀ ((τ - ∑ i, b (j₀.succAbove i) * y i) / b j₀) y j₀))]

theorem slicePoint_sq_le {n : ℕ} (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (τ : ℝ)
    (x : Fin n → ℝ) :
    ∑ i, x i ^ 2 ≤ ∑ j, slicePoint b j₀ τ x j ^ 2 := by
  rw [Fin.sum_univ_succAbove _ j₀]
  simp only [slicePoint, Fin.insertNth_apply_succAbove]
  linarith [sq_nonneg (Fin.insertNth (α := fun _ => ℝ) j₀
      ((τ - ∑ i, b (j₀.succAbove i) * x i) / b j₀) x j₀)]

/-- On the box, the sliced dispersion is at most `(d+1)/2`. -/
theorem slicedDispersion_le_on_box {d : ℕ} {σ : ℝ} (hσ : |σ| ≤ 1) (ζ : Frequency d)
    (hζ : ∀ j, |ζ j| ≤ 1 / 2) (x : Frequency d) (hx : ∀ j, |x j| ≤ 1 / 4) :
    slicedDispersion σ ζ x ≤ (d : ℝ) := by
  unfold slicedDispersion
  have h1 : 0 ≤ ∑ j, Real.cos (ζ j / 2) * Real.sqrt (1 - x j ^ 2) := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg _ (Real.sqrt_nonneg _)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have := (abs_le.mp (hζ j)).1
      linarith [Real.pi_gt_three]
    · have := (abs_le.mp (hζ j)).2
      linarith [Real.pi_gt_three]
  have h2 : |∑ j, Real.sin (ζ j / 2) * x j| ≤ (d : ℝ) / 4 := by
    calc |∑ j, Real.sin (ζ j / 2) * x j| ≤ ∑ j, |Real.sin (ζ j / 2) * x j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, (1 / 4 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          have := Real.abs_sin_le_one (ζ j / 2)
          have := hx j
          nlinarith [abs_nonneg (Real.sin (ζ j / 2)), abs_nonneg (x j)]
      _ = (d : ℝ) / 4 := by simp; ring
  have h3 : σ * 2 * ∑ j, Real.sin (ζ j / 2) * x j ≤ (d : ℝ) / 2 := by
    have := abs_le.mp h2
    have hσ' := abs_le.mp hσ
    calc σ * 2 * ∑ j, Real.sin (ζ j / 2) * x j ≤ |σ * 2 * ∑ j, Real.sin (ζ j / 2) * x j| :=
          le_abs_self _
      _ = |σ| * 2 * |∑ j, Real.sin (ζ j / 2) * x j| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ 1 * 2 * ((d : ℝ) / 4) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hσ (by norm_num)) h2 (abs_nonneg _)
          norm_num
      _ = (d : ℝ) / 2 := by ring
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- The pulled-back convex extension along a hyperplane slice. -/
def sliceEnergy {n : ℕ} (σ : ℝ) (ζ : Frequency (n + 1)) (b : Fin (n + 1) → ℝ)
    (j₀ : Fin (n + 1)) (τ : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  extendedDispersion σ ζ (WithLp.toLp 2 (slicePoint b j₀ τ (WithLp.ofLp y)))

theorem sliceEnergy_continuous {n : ℕ} (σ : ℝ) (ζ : Frequency (n + 1)) (b : Fin (n + 1) → ℝ)
    (j₀ : Fin (n + 1)) (τ : ℝ) : Continuous (sliceEnergy σ ζ b j₀ τ) := by
  unfold sliceEnergy
  exact (extended_dispersion_continuous σ ζ).comp
    ((PiLp.continuous_toLp 2 _).comp ((slicePoint_continuous b j₀ τ).comp
      (PiLp.continuous_ofLp 2 _)))

theorem sliceEnergy_strongConvex {n : ℕ} (σ : ℝ) (ζ : Frequency (n + 1))
    (hζ : ∀ j, |ζ j| ≤ 1 / 2) (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (τ : ℝ) :
    StrongConvexOn (Set.univ : Set (EuclideanSpace ℝ (Fin n))) 1 (sliceEnergy σ ζ b j₀ τ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c ha hc hac
  set P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y => WithLp.toLp 2 (slicePoint b j₀ τ (WithLp.ofLp y)) with hP
  have hPaff : P (a • x + c • y) = a • P x + c • P y := by
    simp only [hP, WithLp.ofLp_add, WithLp.ofLp_smul, slicePoint_affine b j₀ τ _ _ a c hac,
      WithLp.toLp_add, WithLp.toLp_smul]
  have hF := (extended_dispersion_strongConvex σ ζ hζ).2 (Set.mem_univ (P x))
    (Set.mem_univ (P y)) ha hc hac
  have hnorm : ‖x - y‖ ^ 2 ≤ ‖P x - P y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa [hP] using slicePoint_dist_sq b j₀ τ (WithLp.ofLp x) (WithLp.ofLp y)
  have hab : 0 ≤ a * c := mul_nonneg ha hc
  change extendedDispersion σ ζ (P (a • x + c • y)) ≤
    a • extendedDispersion σ ζ (P x) + c • extendedDispersion σ ζ (P y) - a * c * (1 / 2 * ‖x - y‖ ^ 2)
  rw [hPaff]
  have : a * c * (1 / 2 * ‖x - y‖ ^ 2) ≤ a * c * (1 / 2 * ‖P x - P y‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hab
    linarith
  simp only [smul_eq_mul] at hF ⊢
  linarith

/-- Volume of a hyperplane slice of one box-restricted energy shell: `O(s)`,
uniformly in the hyperplane (tangential slices included). Needs `n ≥ 2`. -/
theorem slice_shell_volume (hshell : ConvexShellStatement) {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ 1 → ∀ ζ : Frequency (n + 1), (∀ j, |ζ j| ≤ 1 / 2) →
      ∀ (b : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (τ E s : ℝ), 0 < s →
        volume {x' : Fin n → ℝ | slicePoint b j₀ τ x' ∈ boxShell σ ζ E s} ≤
          ENNReal.ofReal (C * s) := by
  obtain ⟨C₀, hC₀, hC⟩ := hshell n hn
  set ρ : ℝ := Real.sqrt (40 * ((n : ℝ) + 1)) with hρ
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hρsq : ρ ^ 2 = 40 * ((n : ℝ) + 1) := Real.sq_sqrt (by positivity)
  set R : ℝ := 2 * ρ with hR
  have hRpos : 0 < R := by positivity
  refine ⟨C₀ * R ^ (n - 2), by positivity, ?_⟩
  intro σ hσ ζ hζ b j₀ τ E s hs
  set T := {x' : Fin n → ℝ | slicePoint b j₀ τ x' ∈ boxShell σ ζ E s} with hT
  rcases Set.eq_empty_or_nonempty T with hTe | ⟨xb, hxb⟩
  · rw [hTe, measure_empty]; exact bot_le
  set G := sliceEnergy σ ζ b j₀ τ with hG
  -- Points of `T` lie in the ball of radius `ρ`.
  have hsmall : ∀ x' ∈ T, ∑ i, x' i ^ 2 ≤ ρ ^ 2 := by
    intro x' hx'
    have hbox := hx'.1
    have h1 := slicePoint_sq_le b j₀ τ x'
    have h2 : ∑ j, slicePoint b j₀ τ x' j ^ 2 ≤ ∑ _j : Fin (n + 1), (1 / 16 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have := abs_le.mp (hbox j)
      nlinarith
    simp at h2
    rw [hρsq]
    nlinarith
  have hGeq : ∀ x' ∈ T, G (WithLp.toLp 2 x') = slicedDispersion σ ζ (slicePoint b j₀ τ x') := by
    intro x' hx'
    simp only [hG, sliceEnergy]
    rw [extended_dispersion_eq σ ζ _ (fun j => by simpa using hx'.1 j)]
  have hGge : ∀ y, -6 * ((n : ℝ) + 1) + ‖y‖ ^ 2 / 4 ≤ G y := by
    intro y
    have h := extended_dispersion_ge (d := n + 1) hσ ζ hζ
      (WithLp.toLp 2 (slicePoint b j₀ τ (WithLp.ofLp y)))
    have hn' : ‖y‖ ^ 2 ≤ ‖(WithLp.toLp 2 (slicePoint b j₀ τ (WithLp.ofLp y)) :
        EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simpa using slicePoint_sq_le b j₀ τ (WithLp.ofLp y)
    push_cast at h
    simp only [hG, sliceEnergy]
    linarith
  have hGb : G (WithLp.toLp 2 xb) ≤ (n : ℝ) + 1 := by
    rw [hGeq xb hxb]
    have := slicedDispersion_le_on_box hσ ζ hζ _ hxb.1
    push_cast at this
    exact this
  -- A global minimizer of `G`, inside the ball of radius `ρ`.
  have hxbnorm : ‖(WithLp.toLp 2 xb : EuclideanSpace ℝ (Fin n))‖ ≤ ρ := by
    have h := hsmall xb hxb
    have : ‖(WithLp.toLp 2 xb : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ ρ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; simpa using h
    nlinarith [norm_nonneg (WithLp.toLp 2 xb : EuclideanSpace ℝ (Fin n))]
  obtain ⟨y₀, hy₀mem, hy₀min⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ).exists_isMinOn
    ⟨WithLp.toLp 2 xb, by simpa using hxbnorm⟩ (sliceEnergy_continuous σ ζ b j₀ τ).continuousOn
  have hglob : ∀ y, G y₀ ≤ G y := by
    intro y
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ
    · exact hy₀min hy
    · have hy' : ρ < ‖y‖ := by simpa using hy
      have hsq : ρ ^ 2 < ‖y‖ ^ 2 := by
        exact pow_lt_pow_left₀ hy' hρpos.le (by norm_num)
      have h1 := hGge y
      have h2 : G y₀ ≤ G (WithLp.toLp 2 xb) := hy₀min (by simpa using hxbnorm)
      nlinarith
  have hy₀norm : ‖y₀‖ ≤ ρ := by simpa using hy₀mem
  -- The slice set sits in the convex shell around the minimizer.
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹' T ⊆
      {y | dist y y₀ ≤ R ∧ |G y - E| ≤ s} := by
    intro y hy
    have hyT : WithLp.ofLp y ∈ T := hy
    refine ⟨?_, ?_⟩
    · have hyn : ‖y‖ ≤ ρ := by
        have h := hsmall _ hyT
        have : ‖y‖ ^ 2 ≤ ρ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]; simpa using h
        nlinarith [norm_nonneg (WithLp.toLp 2 xb : EuclideanSpace ℝ (Fin n))]
      rw [dist_eq_norm]
      calc ‖y - y₀‖ ≤ ‖y‖ + ‖y₀‖ := norm_sub_le _ _
        _ ≤ R := by rw [hR]; linarith
    · have h := hGeq _ hyT
      simp only [WithLp.toLp_ofLp] at h
      rw [h]
      exact hyT.2
  have hvol := hC G y₀ 1 R E s one_pos hRpos hs (sliceEnergy_strongConvex σ ζ hζ b j₀ τ) hglob
  calc volume T = volume ((WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹' T) :=
        ((PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
          (((boxShell_isClosed σ ζ E s).preimage (slicePoint_continuous b j₀ τ)).measurableSet.nullMeasurableSet)).symm
    _ ≤ volume {y | dist y y₀ ≤ R ∧ |G y - E| ≤ s} := measure_mono hsub
    _ ≤ ENNReal.ofReal (C₀ * R ^ (n - 2) * s / 1) := hvol
    _ = ENNReal.ofReal (C₀ * R ^ (n - 2) * s) := by rw [div_one]

/-- `|ζ| ≤ |4 sin(ζ/2)|` for `|ζ| ≤ 1/2`. -/
theorem abs_le_four_sin_half {ζ : ℝ} (hζ : |ζ| ≤ 1 / 2) : |ζ| ≤ |4 * Real.sin (ζ / 2)| := by
  have key : ∀ y : ℝ, 0 < y → y ≤ 1 / 2 → y ≤ 4 * Real.sin (y / 2) := by
    intro y hy hy'
    have h := Real.sin_gt_sub_cube (x := y / 2) (by linarith)
    have h2 : 0 ≤ y * (1 - y ^ 2 / 12) := mul_nonneg hy.le (by nlinarith)
    nlinarith
  rcases lt_trichotomy ζ 0 with h | h | h
  · have := key (-ζ) (by linarith) (by rw [abs_of_neg h] at hζ; linarith)
    rw [abs_of_neg h, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hs : Real.sin (ζ / 2) = -Real.sin (-ζ / 2) := by
      rw [show -ζ / 2 = -(ζ / 2) by ring, Real.sin_neg, neg_neg]
    rw [hs, abs_neg]
    calc -ζ ≤ 4 * Real.sin (-ζ / 2) := this
      _ ≤ 4 * |Real.sin (-ζ / 2)| := by
          apply mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
  · subst h; simp
  · have := key ζ h (by rw [abs_of_pos h] at hζ; linarith)
    rw [abs_of_pos h]
    exact this.trans (le_abs_self _)

/-- **Joint shell volume** (§3, lines 480–520): in the sliced coordinates, the
joint shell of the two dispersions has volume `O(s₁ s₂ / |ζ_{j₀}|)`, where `j₀`
is any coordinate with `ζ j₀ ≠ 0`. Uniform in `E` and in `ζ` with `|ζ_j| ≤ 1/2`;
no transversality assumption. -/
theorem sliced_joint_shell_volume (hslab : SlabSliceStatement) (hshell : ConvexShellStatement)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Frequency (n + 1), (∀ j, |ζ j| ≤ 1 / 2) →
      ∀ j₀ : Fin (n + 1), ζ j₀ ≠ 0 → ∀ E s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ →
        volume {x : Frequency (n + 1) | (∀ j, |x j| ≤ 1 / 4) ∧
            |slicedDispersion (-1) ζ x - E| ≤ s₁ ∧ |slicedDispersion 1 ζ x - E| ≤ s₂} ≤
          ENNReal.ofReal (C * s₁ * s₂ / |ζ j₀|) := by
  obtain ⟨C, hCpos, hCs⟩ := slice_shell_volume hshell hn
  refine ⟨4 * C, by positivity, ?_⟩
  intro ζ hζ j₀ hj₀ E s₁ s₂ hs₁ hs₂
  set b : Fin (n + 1) → ℝ := fun j => 4 * Real.sin (ζ j / 2) with hb
  have hζpos : 0 < |ζ j₀| := abs_pos.mpr hj₀
  have hbj : |ζ j₀| ≤ |b j₀| := abs_le_four_sin_half (hζ j₀)
  have hbpos : 0 < |b j₀| := hζpos.trans_le hbj
  have hb0 : b j₀ ≠ 0 := abs_pos.mp hbpos
  -- general slab step for a chosen narrower shell
  have step : ∀ (σ s : ℝ), |σ| ≤ 1 → 0 < s → s ≤ s₁ → s ≤ s₂ →
      {x : Frequency (n + 1) | (∀ j, |x j| ≤ 1 / 4) ∧
          |slicedDispersion (-1) ζ x - E| ≤ s₁ ∧ |slicedDispersion 1 ζ x - E| ≤ s₂} ⊆
        {x | x ∈ boxShell σ ζ E s ∧ |∑ j, b j * x j - 0| ≤ s₁ + s₂} →
      volume {x : Frequency (n + 1) | (∀ j, |x j| ≤ 1 / 4) ∧
          |slicedDispersion (-1) ζ x - E| ≤ s₁ ∧ |slicedDispersion 1 ζ x - E| ≤ s₂} ≤
        ENNReal.ofReal (4 * C * s₁ * s₂ / |ζ j₀|) := by
    intro σ s hσ hs hss₁ hss₂ hsub
    have hslab' := hslab n b j₀ (boxShell σ ζ E s) 0 (s₁ + s₂) (C * s) hb0
      (boxShell_isClosed σ ζ E s).measurableSet (by linarith) (by positivity)
      (fun τ => hCs σ hσ ζ hζ b j₀ τ E s hs)
    refine (measure_mono hsub).trans (hslab'.trans (ENNReal.ofReal_le_ofReal ?_))
    have h1 : 2 * (s₁ + s₂) * (C * s) ≤ 4 * C * s₁ * s₂ := by
      have : (s₁ + s₂) * s ≤ 2 * s₁ * s₂ := by
        rcases le_total s₁ s₂ with h | h
        · nlinarith
        · nlinarith
      nlinarith
    calc 2 * (s₁ + s₂) * (C * s) / |b j₀| ≤ 4 * C * s₁ * s₂ / |b j₀| :=
          div_le_div_of_nonneg_right h1 hbpos.le
      _ ≤ 4 * C * s₁ * s₂ / |ζ j₀| :=
          div_le_div_of_nonneg_left (by positivity) hζpos hbj
  have hslabpt : ∀ x : Frequency (n + 1), |slicedDispersion (-1) ζ x - E| ≤ s₁ →
      |slicedDispersion 1 ζ x - E| ≤ s₂ → |∑ j, b j * x j - 0| ≤ s₁ + s₂ := by
    intro x h₁ h₂
    rw [sub_zero]
    exact sliced_dispersion_slab ζ x E s₁ s₂ h₁ h₂
  rcases le_total s₁ s₂ with h | h
  · apply step (-1) s₁ (by norm_num) hs₁ le_rfl h
    intro x hx
    exact ⟨⟨hx.1, hx.2.1⟩, hslabpt x hx.2.1 hx.2.2⟩
  · apply step 1 s₂ (by norm_num) hs₂ h le_rfl
    intro x hx
    exact ⟨⟨hx.1, hx.2.2⟩, hslabpt x hx.2.1 hx.2.2⟩

/-- The lead's joint shell volume in the frozen statement form. -/
theorem jointShellX_of_helpers (hslab : SlabSliceStatement) (hshell : ConvexShellStatement) :
    JointShellXStatement :=
  fun _ hn => sliced_joint_shell_volume hslab hshell hn

end AndersonAC.S3
