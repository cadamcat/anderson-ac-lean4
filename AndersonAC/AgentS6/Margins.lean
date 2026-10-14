import AndersonAC.S6.Statements

/-! Scalar exponent margins of 06-clearing.tex: parameters (39–50), the heat-limit margin
(742–747, 749–757), the distortion identities (946–957) and the bias margins (1007–1020). -/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace AndersonAC.AgentS6

open AndersonAC.S6

theorem delta_eq : delta = 1 / 100 := rfl

theorem nu_nonneg (d : ℕ) : 0 ≤ nu d := by
  unfold nu delta; positivity

theorem nu_le (d : ℕ) (hd : 3 ≤ d) : nu d ≤ 1 / 30000000 := by
  unfold nu delta
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `x ↦ t^x` is antitone for `0 < t ≤ 1`. -/
theorem rpow_anti {t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hab : a ≤ b) : t ^ b ≤ t ^ a :=
  Real.rpow_le_rpow_of_exponent_ge ht ht1 hab

theorem rpow_le_one_of {t a : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ha : 0 ≤ a) : t ^ a ≤ 1 :=
  Real.rpow_le_one ht.le ht1 ha

/-- `t^a → 0` as `t → 0⁺` for `a > 0`. -/
theorem tendsto_rpow_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

end AndersonAC.AgentS6

namespace AndersonAC.S6

open AndersonAC.AgentS6

theorem parameter_margins (d : ℕ) (hd : 3 ≤ d) : Planned.parameter_margins d hd := by
  have hnu0 := nu_nonneg d
  have hnu1 := nu_le d hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hnu : nu d = (1 / 100000) * delta / d := rfl
  unfold Planned.parameter_margins
  simp only [delta, betaW, e0, eh] at *
  refine ⟨hnu0, by linarith, by norm_num, by linarith, by norm_num, by norm_num, by linarith,
    by norm_num, ?_, ?_⟩
  · rw [hnu]; field_simp; ring
  · rw [hnu]; field_simp; ring

/-- Heat-limit margin, 06-clearing.tex:742–747: `n_h l_*/r_* ≥ ½ t^{-(e_h-e_0-ν)}`. -/
theorem heat_limit_margin (d : ℕ) (hd : 3 ≤ d) : Planned.heat_limit_margin d hd := by
  unfold Planned.heat_limit_margin
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  set X : ℝ := t ^ (-1 - eh) with hX
  have hX2 : 2 ≤ X := by
    have h1 : t ^ (-1 : ℝ) ≤ X := rpow_anti ht0 (by linarith) (by unfold eh delta; norm_num)
    have h2 : (2 : ℝ) ≤ t ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      rw [le_inv_comm₀ (by norm_num) ht0]
      linarith
    linarith
  have hfloor : X / 2 ≤ (heatLimit t : ℝ) := by
    have := Nat.lt_floor_add_one X
    unfold heatLimit
    rw [← hX]
    linarith
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht0 _
  have hc : 0 < coreCap d t := Real.rpow_pos_of_pos ht0 _
  have key : X * leverageScale t / coreCap d t = t ^ (-(eh - e0 - nu d)) := by
    unfold leverageScale coreCap
    rw [hX, ← Real.rpow_add ht0, ← Real.rpow_sub ht0]
    congr 1; ring
  calc (1 / 2) * t ^ (-(eh - e0 - nu d)) = X / 2 * leverageScale t / coreCap d t := by
        rw [← key]; ring
    _ ≤ (heatLimit t : ℝ) * leverageScale t / coreCap d t := by
        gcongr

theorem distortion_margin_identities (t : ℝ) (ht : 0 < t) :
    Planned.distortion_margin_identities t ht := by
  unfold Planned.distortion_margin_identities entryBudget fourthCap betaW
  have hq : t ^ (1 + delta) / t = t ^ delta := by
    rw [div_eq_iff ht.ne', ← Real.rpow_add_one ht.ne']; ring_nf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_sub ht]
    congr 1; push_cast; ring
  · rw [hq, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, ← Real.rpow_sub ht]
    congr 1; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_sub ht]
    congr 1; push_cast; ring
  · rw [← Real.rpow_add ht]
    congr 1; ring

theorem prefix_interval_bound (l : ℝ) (Z : ℕ → ℝ) (hl : 0 ≤ l)
    (hprefix : ∀ s, |∑ k ∈ Finset.range s, Z k| ≤ l / 2) :
    Planned.prefix_interval_bound l Z hl hprefix := by
  intro k0 s hks
  rw [Finset.sum_Ico_eq_sub _ hks]
  have h1 := hprefix s
  have h2 := hprefix k0
  calc |∑ k ∈ Finset.range s, Z k - ∑ k ∈ Finset.range k0, Z k|
      ≤ |∑ k ∈ Finset.range s, Z k| + |∑ k ∈ Finset.range k0, Z k| := abs_sub _ _
    _ ≤ l := by linarith

theorem pivot_mass (n : ℕ) (F : Fin n → ℝ) (hF : ∀ k, 0 ≤ F k) :
    Planned.pivot_mass n F hF := by
  unfold Planned.pivot_mass
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) F
  simpa [Finset.card_univ, Fintype.card_fin] using this

theorem leverage_bias_margins (d : ℕ) (hd : 3 ≤ d) : Planned.leverage_bias_margins d hd := by
  have hnu1 := nu_le d hd
  have hδ : delta = 1 / 100 := rfl
  refine ⟨?_, ?_⟩
  · have h1 := tendsto_rpow_zero (a := (265 / 1000) * delta) (by rw [hδ]; norm_num)
    have h2 := tendsto_rpow_zero (a := (27 / 100) * delta) (by rw [hδ]; norm_num)
    have h3 := tendsto_rpow_zero (a := (34 / 100) * delta) (by rw [hδ]; norm_num)
    have h4 := tendsto_rpow_zero (a := 1 / 2 - (2 / 100) * delta) (by rw [hδ]; norm_num)
    have h5 := tendsto_rpow_zero (a := 1 / 2 + (48 / 100) * delta - nu d)
      (by rw [hδ]; linarith)
    have h6 := tendsto_rpow_zero (a := (345 / 1000) * delta) (by rw [hδ]; norm_num)
    have h7 := tendsto_rpow_zero (a := (42 / 100) * delta) (by rw [hδ]; norm_num)
    simpa using (((((h1.add h2).add h3).add h4).add h5).add h6).add h7
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hn : (heatLimit t : ℝ) ≤ t ^ (-1 - eh) :=
      Nat.floor_le (Real.rpow_nonneg ht0.le _)
    have hl : 0 ≤ (leverageScale t) ^ 2 / t := by
      unfold leverageScale; positivity
    calc (heatLimit t : ℝ) * (leverageScale t) ^ 2 / t
        = (heatLimit t : ℝ) * ((leverageScale t) ^ 2 / t) := by ring
      _ ≤ t ^ (-1 - eh) * ((leverageScale t) ^ 2 / t) := by gcongr
      _ = t ^ ((42 / 100) * delta) := by
        unfold leverageScale
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, ← Real.rpow_sub_one ht0.ne',
          ← Real.rpow_add ht0]
        congr 1; unfold eh e0; push_cast; ring
      _ ≤ t ^ ((27 / 100) * delta) := rpow_anti ht0 ht1.le (by rw [hδ]; norm_num)

theorem fourth_distortion {ι : Type*} [Fintype ι] (t : ℝ) (g0 hg : Matrix ι ι ℂ) (ht : 0 < t)
    (hbudget : BudgetsHold t g0 hg) : Planned.fourth_distortion t g0 hg ht hbudget := by
  intro i
  obtain ⟨hentry, hrow, -⟩ := hbudget
  set x : ι → ℝ := fun j => ‖scaledInverse t (hg - g0) i j‖ with hx
  have hxj : ∀ j, x j ≤ Real.sqrt t * entryBudget t := by
    intro j
    simp only [hx, scaledInverse, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
    exact mul_le_mul_of_nonneg_left (hentry i j) (Real.sqrt_nonneg t)
  have hx0 : ∀ j, 0 ≤ x j := fun j => norm_nonneg _
  have hsq : ∀ j, x j ^ 4 ≤ (Real.sqrt t * entryBudget t) ^ 2 * x j ^ 2 := by
    intro j
    have h1 : x j ^ 2 ≤ (Real.sqrt t * entryBudget t) ^ 2 :=
      pow_le_pow_left₀ (hx0 j) (hxj j) 2
    nlinarith [sq_nonneg (x j)]
  have hrowi : ∑ j, x j ^ 2 ≤ rowBudget t := hrow i
  calc fourthRow (scaledInverse t (hg - g0)) i = ∑ j, x j ^ 4 := rfl
    _ ≤ ∑ j, (Real.sqrt t * entryBudget t) ^ 2 * x j ^ 2 := Finset.sum_le_sum fun j _ => hsq j
    _ = (Real.sqrt t * entryBudget t) ^ 2 * ∑ j, x j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (Real.sqrt t * entryBudget t) ^ 2 * rowBudget t := by gcongr
    _ = t ^ (1 + (109 / 100) * delta) := by
      rw [mul_pow, Real.sq_sqrt ht.le]
      unfold entryBudget rowBudget
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, mul_assoc, ← Real.rpow_add ht,
        ← Real.rpow_one_add' ht.le]
      · congr 1; push_cast; ring
      · unfold delta; norm_num

theorem four_pow_add_le (x y : ℝ) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h1 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h2 : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have h3 : (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
  rw [h3]
  have h4 : ((x + y) ^ 2) ^ 2 ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith

theorem pivot_fourth {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (n : ℕ) (pivot : Fin n → ι)
    (g0 : Matrix ι ι ℂ) (g : Fin n → Matrix ι ι ℂ) (i : ι)
    (hinj : Function.Injective pivot)
    (hbudget : ∀ k, ‖g k i (pivot k) - g0 i (pivot k)‖ ≤ entryBudget t) :
    Planned.pivot_fourth t n pivot g0 g i hinj hbudget := by
  unfold Planned.pivot_fourth
  set s := Real.sqrt t
  have hs : 0 ≤ s := Real.sqrt_nonneg t
  have hentry : ∀ (A : Matrix ι ι ℂ) j, ‖scaledInverse t A i j‖ = s * ‖A i j‖ := by
    intro A j
    simp [scaledInverse, Matrix.smul_apply, Complex.norm_real,
      Real.norm_of_nonneg hs, s]
  have hterm : ∀ k, ‖scaledInverse t (g k) i (pivot k)‖ ^ 4 ≤
      8 * ‖scaledInverse t g0 i (pivot k)‖ ^ 4 + 8 * (s * entryBudget t) ^ 4 := by
    intro k
    rw [hentry, hentry]
    have htri : ‖g k i (pivot k)‖ ≤ ‖g0 i (pivot k)‖ + entryBudget t := by
      have := norm_le_insert' (g k i (pivot k)) (g0 i (pivot k))
      linarith [hbudget k, norm_sub_norm_le (g k i (pivot k)) (g0 i (pivot k))]
    have h1 : s * ‖g k i (pivot k)‖ ≤ s * ‖g0 i (pivot k)‖ + s * entryBudget t := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left htri hs
    have h0 : 0 ≤ s * ‖g k i (pivot k)‖ := mul_nonneg hs (norm_nonneg _)
    calc (s * ‖g k i (pivot k)‖) ^ 4 ≤ (s * ‖g0 i (pivot k)‖ + s * entryBudget t) ^ 4 :=
          pow_le_pow_left₀ h0 h1 4
      _ ≤ 8 * ((s * ‖g0 i (pivot k)‖) ^ 4 + (s * entryBudget t) ^ 4) :=
          four_pow_add_le _ _
      _ = _ := by ring
  have hinjsum : ∑ k, ‖scaledInverse t g0 i (pivot k)‖ ^ 4 ≤
      fourthRow (scaledInverse t g0) i := by
    unfold fourthRow
    rw [← Finset.sum_image (f := fun j => ‖scaledInverse t g0 i j‖ ^ 4)
      (fun a _ b _ h => hinj h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => by positivity)
  calc ∑ k, ‖scaledInverse t (g k) i (pivot k)‖ ^ 4
      ≤ ∑ k, (8 * ‖scaledInverse t g0 i (pivot k)‖ ^ 4 + 8 * (s * entryBudget t) ^ 4) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 8 * ∑ k, ‖scaledInverse t g0 i (pivot k)‖ ^ 4 + 8 * (n : ℝ) * (s * entryBudget t) ^ 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [Finset.card_univ]; ring
    _ ≤ _ := by linarith

end AndersonAC.S6

#print axioms AndersonAC.S6.parameter_margins
#print axioms AndersonAC.S6.heat_limit_margin
#print axioms AndersonAC.S6.distortion_margin_identities
#print axioms AndersonAC.S6.prefix_interval_bound
#print axioms AndersonAC.S6.pivot_mass
#print axioms AndersonAC.S6.leverage_bias_margins
#print axioms AndersonAC.S6.fourth_distortion
#print axioms AndersonAC.S6.pivot_fourth
