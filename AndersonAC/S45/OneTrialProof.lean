import AndersonAC.S45.MatrixConcentrationProof

/-! `AndersonAC.S45.one_trial` (paper §5.5, one local trial): each monitor's
centered martingale is controlled by Lemma 5.6; the predictable drift is below
half the budget for small `t`; a union over monitors costs the total dimension
`≤ C t^{-6d}`. Every exponent is a multiple of `η = 1/200000`, so with
`y = t^η` all monitor quantities are monomials in `y` and `logFactor t ≤ A / y`. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

def eta : ℝ := 1 / 200000

theorem power_def (t e : ℝ) : power t e = t ^ e := rfl

theorem eta_pos : 0 < eta := by norm_num [eta]

/-! ### Monomial bookkeeping -/

section Mono

variable {C A L y : ℝ}

/-- `L^a y^m ≤ A^3 y^s` when `a ≤ 3`, `a + s ≤ m`, `L y ≤ A`, `1 ≤ A`, `0 < y ≤ 1`, `0 ≤ L`. -/
theorem mono_le (hA : 1 ≤ A) (hy0 : 0 < y) (hy1 : y ≤ 1) (hL0 : 0 ≤ L) (hLy : L * y ≤ A)
    {a m s : ℕ} (ha : a ≤ 3) (hm : a + s ≤ m) : L ^ a * y ^ m ≤ A ^ 3 * y ^ s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h1 : L ^ a * y ^ (a + s + r) = (L * y) ^ a * (y ^ s * y ^ r) := by ring
  have hyr : y ^ r ≤ 1 := pow_le_one₀ hy0.le hy1
  have hys : 0 ≤ y ^ s := pow_nonneg hy0.le s
  have hLya : (L * y) ^ a ≤ A ^ a := pow_le_pow_left₀ (mul_nonneg hL0 hy0.le) hLy a
  have hAa : A ^ a ≤ A ^ 3 := pow_le_pow_right₀ hA ha
  rw [h1]
  calc (L * y) ^ a * (y ^ s * y ^ r) ≤ A ^ 3 * (y ^ s * 1) := by
        apply mul_le_mul (hLya.trans hAa) (mul_le_mul_of_nonneg_left hyr hys)
          (mul_nonneg hys (pow_nonneg hy0.le r)) (by positivity)
    _ = A ^ 3 * y ^ s := by ring

/-- Lower bound for the jump ratio `(y^p/2)/(C L^a y^q)`. -/
theorem jump_ratio (hC : 0 < C) (hA : 1 ≤ A) (hy0 : 0 < y) (hy1 : y ≤ 1) (hL1 : 1 ≤ L)
    (hLy : L * y ≤ A) {p a q : ℕ} (ha : a ≤ 3) (hq : a + (p + 4) ≤ q) :
    1 / (4 * C * A ^ 3 * y ^ 4) ≤ (y ^ p / 2) / (C * (L ^ a * y ^ q)) := by
  have hD : 0 < C * (L ^ a * y ^ q) := by positivity
  have hK : 0 < 4 * C * A ^ 3 * y ^ 4 := by positivity
  rw [div_le_div_iff₀ hK hD]
  have h := mono_le hA hy0 hy1 (by linarith) hLy ha hq
  have hyp : 0 ≤ y ^ p := pow_nonneg hy0.le p
  calc 1 * (C * (L ^ a * y ^ q)) ≤ C * (A ^ 3 * y ^ (p + 4)) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left h hC.le
    _ ≤ y ^ p / 2 * (4 * C * A ^ 3 * y ^ 4) := by
        have : C * (A ^ 3 * y ^ (p + 4)) = (C * A ^ 3 * y ^ (p + 4)) := by ring
        rw [this, pow_add]
        have h0 : 0 ≤ C * A ^ 3 * (y ^ p * y ^ 4) := by positivity
        nlinarith [h0]

/-- Lower bound for the variance ratio `(y^p/2)^2/(C L^e y^r)`. -/
theorem var_ratio (hC : 0 < C) (hA : 1 ≤ A) (hy0 : 0 < y) (hy1 : y ≤ 1) (hL1 : 1 ≤ L)
    (hLy : L * y ≤ A) {p e r : ℕ} (he : e ≤ 3) (hr : e + (2 * p + 4) ≤ r) :
    1 / (4 * C * A ^ 3 * y ^ 4) ≤ (y ^ p / 2) ^ 2 / (C * (L ^ e * y ^ r)) := by
  have hD : 0 < C * (L ^ e * y ^ r) := by positivity
  have hK : 0 < 4 * C * A ^ 3 * y ^ 4 := by positivity
  rw [div_le_div_iff₀ hK hD]
  have h := mono_le hA hy0 hy1 (by linarith) hLy he hr
  calc 1 * (C * (L ^ e * y ^ r)) ≤ C * (A ^ 3 * y ^ (2 * p + 4)) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left h hC.le
    _ = (y ^ p / 2) ^ 2 * (4 * C * A ^ 3 * y ^ 4) := by ring

end Mono

/-! ### The monitor quantities as monomials in `y = t^η` -/

section Monitor

variable {t : ℝ}

theorem power_eta_nat (ht : 0 < t) (k : ℕ) : power t (eta * k) = (power t eta) ^ k := by
  simp only [power_def]
  rw [Real.rpow_mul ht.le, Real.rpow_natCast]

theorem power_eq_y (ht : 0 < t) {e : ℝ} (k : ℕ) (hk : e = eta * k) :
    power t e = (power t eta) ^ k := by
  rw [hk, power_eta_nat ht]

def Aconst : ℝ := 1 + 1 / eta

theorem one_le_Aconst : 1 ≤ Aconst := by
  unfold Aconst; have := eta_pos; have : 0 < 1 / eta := by positivity
  linarith

theorem logFactor_ge_one (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ logFactor t := by
  unfold logFactor
  have : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  linarith

theorem logFactor_mul_y (ht : 0 < t) (ht1 : t ≤ 1) : logFactor t * power t eta ≤ Aconst := by
  have hy : 0 < power t eta := Real.rpow_pos_of_pos ht _
  have hy1 : power t eta ≤ 1 := Real.rpow_le_one ht.le ht1 eta_pos.le
  have hlog : Real.log (1 / t) ≤ (1 / t) ^ eta / eta :=
    Real.log_le_rpow_div (by positivity) eta_pos
  have hinv : (1 / t) ^ eta * power t eta = 1 := by
    simp only [power_def]
    rw [one_div, Real.inv_rpow ht.le, inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht eta))]
  unfold logFactor Aconst
  have he := eta_pos
  calc (1 + Real.log (1 / t)) * power t eta
      ≤ (1 + (1 / t) ^ eta / eta) * power t eta :=
        mul_le_mul_of_nonneg_right (by linarith) hy.le
    _ = power t eta + ((1 / t) ^ eta * power t eta) / eta := by ring
    _ = power t eta + 1 / eta := by rw [hinv]
    _ ≤ 1 + 1 / eta := by linarith

/-- The three facts about one monitor kind used by `one_trial`. -/
theorem monitor_facts {C : ℝ} (hC : 1 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1) (k : MonitorKind) :
    0 < monitorBudget t k ∧ 0 < C * monitorJump t k ∧ 0 < C * monitorVariance t k ∧
    1 / (4 * C * Aconst ^ 3 * power t eta ^ 4) ≤
      min ((monitorBudget t k / 2) ^ 2 / (C * monitorVariance t k))
        ((monitorBudget t k / 2) / (C * monitorJump t k)) ∧
    (6 * C * Aconst ^ 3 * power t eta ≤ 1 → C * monitorBias t k ≤ monitorBudget t k / 2) := by
  set y := power t eta with hydef
  set L := logFactor t with hLdef
  set A := Aconst with hAdef
  have hy0 : 0 < y := Real.rpow_pos_of_pos ht _
  have hy1 : y ≤ 1 := Real.rpow_le_one ht.le ht1 eta_pos.le
  have hL1 : 1 ≤ L := logFactor_ge_one ht ht1
  have hLy : L * y ≤ A := logFactor_mul_y ht ht1
  have hA : 1 ≤ A := one_le_Aconst
  have hC0 : 0 < C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have pw : ∀ (e : ℝ) (k : ℕ), e = eta * k → power t e = y ^ k :=
    fun e k hk => power_eq_y ht k hk
  have hsix : ∀ m : ℕ, 6 * C * A ^ 3 * y ≤ 1 → C * (A ^ 3 * y ^ (m + 1)) ≤ y ^ m / 6 := by
    intro m h
    have hym : 0 ≤ y ^ m := pow_nonneg hy0.le m
    have : C * (A ^ 3 * y ^ (m + 1)) = (6 * C * A ^ 3 * y) * y ^ m / 6 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right h hym
    linarith
  cases k with
  | lag =>
    have hb : monitorBudget t .lag = y ^ 880 := pw _ _ (by norm_num [delta, eta])
    have hJ : monitorJump t .lag = L ^ 1 * y ^ 1000 := by
      simp only [monitorJump, pow_one]; rw [pw _ 1000 (by norm_num [delta, eta])]
    have hV : monitorVariance t .lag = L ^ 3 * y ^ 2000 := by
      simp only [monitorVariance]; rw [pw _ 2000 (by norm_num [delta, eta])]
    rw [hb, hJ, hV]
    refine ⟨by positivity, by positivity, by positivity,
      le_min (var_ratio hC0 hA hy0 hy1 hL1 hLy (by norm_num) (by norm_num))
        (jump_ratio hC0 hA hy0 hy1 hL1 hLy (by norm_num) (by norm_num)), fun h => ?_⟩
    have h2b : power t (2 * S45.beta) = y ^ 1680 := pw _ _ (by norm_num [S45.beta, delta, eta])
    have hsq : Real.sqrt t = y ^ 100000 := by
      rw [Real.sqrt_eq_rpow]; exact pw _ _ (by norm_num [eta])
    have hd2 : power t (delta / 2) = y ^ 1000 := pw _ _ (by norm_num [delta, eta])
    simp only [monitorBias]
    rw [h2b, hsq, hd2]
    have e1 := mono_le hA hy0 hy1 hL0 hLy (a := 2) (m := 1680) (s := 881) (by norm_num)
      (by norm_num)
    have e2 := mono_le hA hy0 hy1 hL0 hLy (a := 2) (m := 100000) (s := 881) (by norm_num)
      (by norm_num)
    have e3 := mono_le hA hy0 hy1 hL0 hLy (a := 3) (m := 1000) (s := 881) (by norm_num)
      (by norm_num)
    have h6 := hsix 880 h
    have hsum : L ^ 2 * (y ^ 1680 + y ^ 100000) + L ^ 3 * y ^ 1000 ≤ 3 * (A ^ 3 * y ^ 881) := by
      nlinarith [e1, e2, e3]
    have hy880 : 0 ≤ y ^ 880 := pow_nonneg hy0.le _
    nlinarith [mul_le_mul_of_nonneg_left hsum hC0.le]
  | matrix =>
    have hb : monitorBudget t .matrix = y ^ 250 := pw _ _ (by norm_num [delta, eta])
    have hJ : monitorJump t .matrix = L ^ 0 * y ^ 500 := by
      simp only [monitorJump, pow_zero, one_mul]; exact pw _ _ (by norm_num [delta, eta])
    have hV : monitorVariance t .matrix = L ^ 1 * y ^ 1000 := by
      simp only [monitorVariance, pow_one]; rw [pw _ 1000 (by norm_num [delta, eta])]
    rw [hb, hJ, hV]
    refine ⟨by positivity, by positivity, by positivity,
      le_min (var_ratio hC0 hA hy0 hy1 hL1 hLy (by norm_num) (by norm_num))
        (jump_ratio hC0 hA hy0 hy1 hL1 hLy (by norm_num) (by norm_num)), fun h => ?_⟩
    have hβ : power t S45.beta = y ^ 840 := pw _ _ (by norm_num [S45.beta, delta, eta])
    simp only [monitorBias]
    rw [hβ]
    have e1 := mono_le hA hy0 hy1 hL0 hLy (a := 1) (m := 840) (s := 251) (by norm_num)
      (by norm_num)
    have h6 := hsix 250 h
    have hy250 : 0 ≤ y ^ 250 := pow_nonneg hy0.le _
    have e1' : L * y ^ 840 ≤ A ^ 3 * y ^ 251 := by simpa using e1
    nlinarith [mul_le_mul_of_nonneg_left e1' hC0.le]
  | row =>
    have hb : monitorBudget t .row = y ^ 1 := pw _ _ (by norm_num [delta, eta])
    have hJ : monitorJump t .row = L ^ 0 * y ^ 5 := by
      simp only [monitorJump, pow_zero, one_mul]; exact pw _ _ (by norm_num [kappa, delta, eta])
    have hV : monitorVariance t .row = L ^ 1 * y ^ 10 := by
      simp only [monitorVariance, pow_one]; rw [pw _ 10 (by norm_num [kappa, delta, eta])]
    rw [hb, hJ, hV]
    refine ⟨by positivity, by positivity, by positivity,
      le_min (var_ratio hC0 hA hy0 hy1 hL1 hLy (by norm_num) (by norm_num))
        (jump_ratio hC0 hA hy0 hy1 hL1 hLy (by norm_num) (by norm_num)), fun h => ?_⟩
    have hκ : power t kappa = y ^ 10 := pw _ _ (by norm_num [kappa, delta, eta])
    simp only [monitorBias]
    rw [hκ]
    have e1 := mono_le hA hy0 hy1 hL0 hLy (a := 1) (m := 10) (s := 2) (by norm_num)
      (by norm_num)
    have h6 := hsix 1 h
    have hy1' : 0 ≤ y ^ 1 := pow_nonneg hy0.le _
    have e1' : L * y ^ 10 ≤ A ^ 3 * y ^ 2 := by simpa using e1
    nlinarith [mul_le_mul_of_nonneg_left e1' hC0.le]

end Monitor

/-! ### The final scalar inequality -/

theorem eventually_tail (C ε : ℝ) (M : ℕ) (hε : 0 < ε) :
    ∃ Z : ℝ, ∀ z : ℝ, Z ≤ z →
      2 * C * z ^ M * Real.exp (-(ε * z ^ 4)) ≤ Real.exp (-z) := by
  have h1 : ∀ᶠ z in atTop, 2 * C * (z ^ M * Real.exp (-z)) ≤ 1 := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero M).const_mul (2 * C)
    rw [mul_zero] at ht
    exact ht.eventually (ge_mem_nhds one_pos)
  have h2 : ∀ᶠ z in atTop, 2 / ε ≤ z ^ 3 :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).eventually_ge_atTop _
  have h3 : ∀ᶠ z in atTop, (0 : ℝ) ≤ z := eventually_ge_atTop 0
  obtain ⟨Z, hZ⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨Z, fun z hz => ?_⟩
  obtain ⟨hz1, hz2, hz3⟩ := hZ z hz
  have hkey : z - ε * z ^ 4 ≤ -z := by
    have : 2 ≤ ε * z ^ 3 := by
      have := mul_le_mul_of_nonneg_left hz2 hε.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hε)] at this
    nlinarith [mul_le_mul_of_nonneg_right this hz3]
  have hpos : 0 ≤ z ^ M := pow_nonneg hz3 M
  have hC : 0 ≤ 2 * C * z ^ M ∨ 2 * C * z ^ M < 0 := le_or_gt 0 _
  rcases hC with hC | hC
  · calc 2 * C * z ^ M * Real.exp (-(ε * z ^ 4))
        = 2 * C * z ^ M * Real.exp (z - ε * z ^ 4) * Real.exp (-z) := by
          rw [mul_assoc _ (Real.exp _), ← Real.exp_add]; ring_nf
      _ ≤ 2 * C * z ^ M * Real.exp (-z) * Real.exp (-z) := by
          gcongr
      _ ≤ 1 * Real.exp (-z) := by
          gcongr
          calc 2 * C * z ^ M * Real.exp (-z) = 2 * C * (z ^ M * Real.exp (-z)) := by ring
            _ ≤ 1 := hz1
      _ = Real.exp (-z) := one_mul _
  · have : 2 * C * z ^ M * Real.exp (-(ε * z ^ 4)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC.le (Real.exp_pos _).le
    exact this.trans (Real.exp_pos _).le

/-! ### `one_trial` -/

theorem partialSum_centered {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : Filtration ℕ mΩ} {N : ℕ} (raw : ℕ → Ω → CMat (Fin N)) (n : ℕ) (ω : Ω) :
    partialSum raw n ω = partialSum (centered μ ℱ raw) n ω +
      ∑ k ∈ Finset.range n, μ[raw (k + 1) | ℱ k] ω := by
  simp only [partialSum, centered, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  abel

theorem one_trial_of (hT : AndersonAC.OpusS45.TraceHelpers) (hGT : GoldenThompson) :
    ∀ (d : ℕ) (C : ℝ), 1 ≤ C →
    ∃ c > 0, ∃ t0 > 0, ∀ (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (s : ℕ) (t : ℝ) (a : TrialInputs μ ℱ s d t C) (failure : Set Ω),
    0 < t → t < t0 → failure ⊆ a.crossing →
    μ failure ≤ ENNReal.ofReal (Real.exp (-power t (-c))) := by
  obtain ⟨cc, hcc, hconc⟩ := matrix_concentration_of hT hGT
  intro d C hC
  have hC0 : 0 < C := by linarith
  set A := Aconst with hAdef
  have hA : 1 ≤ A := one_le_Aconst
  set K := 4 * C * A ^ 3 with hKdef
  have hK : 0 < K := by positivity
  set ε := cc / K with hεdef
  have hε : 0 < ε := div_pos hcc hK
  set M : ℕ := 1200000 * d with hMdef
  obtain ⟨Z, hZ⟩ := eventually_tail C ε M hε
  set m := max (max Z 1) (6 * C * A ^ 3) with hmdef
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hm0 : 0 < m := by linarith
  set y0 := 1 / m with hy0def
  have hy0pos : 0 < y0 := by positivity
  have hy01 : y0 ≤ 1 := by rw [hy0def, div_le_one hm0]; exact hm1
  set t0 := y0 ^ (1 / eta) with ht0def
  have ht0pos : 0 < t0 := Real.rpow_pos_of_pos hy0pos _
  have ht01 : t0 ≤ 1 := Real.rpow_le_one hy0pos.le hy01 (by have := eta_pos; positivity)
  refine ⟨eta, eta_pos, t0, ht0pos, ?_⟩
  intro Ω _ μ _ ℱ s t a failure ht htt0 hfail
  have ht1 : t ≤ 1 := (htt0.trans_le ht01).le
  set y := power t eta with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos ht _
  have hyy0 : y < y0 := by
    have h := Real.rpow_lt_rpow ht.le htt0 eta_pos
    have e : t0 ^ eta = y0 := by
      rw [ht0def, one_div, Real.rpow_inv_rpow hy0pos.le (ne_of_gt eta_pos)]
    rw [e] at h
    exact h
  -- small-y consequences
  have hsmall : 6 * C * A ^ 3 * y ≤ 1 := by
    have h1 : 6 * C * A ^ 3 ≤ m := le_max_right _ _
    have h2 : y * m ≤ 1 := by
      have := mul_lt_mul_of_pos_right hyy0 hm0
      rw [hy0def, one_div_mul_cancel (ne_of_gt hm0)] at this
      exact this.le
    nlinarith [mul_le_mul_of_nonneg_left h1 hy0.le]
  set z := 1 / y with hzdef
  have hzZ : Z ≤ z := by
    have h1 : Z ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have h2 : m ≤ z := by
      rw [hzdef, le_div_iff₀ hy0]
      have := mul_lt_mul_of_pos_left hyy0 hm0
      rw [hy0def, mul_one_div_cancel (ne_of_gt hm0)] at this
      linarith
    linarith
  -- per-monitor events
  set b : Fin s → ℝ := fun i => monitorBudget t (a.kind i) with hbdef
  set E : Fin s → Set Ω := fun i =>
    {ω | ∃ N : ℕ, b i / 2 < ‖partialSum (centered μ ℱ (a.raw i)) N ω‖} with hEdef
  set B : Fin s → Set Ω := fun i => ⋃ N : ℕ,
    {ω | ¬ ‖∑ k ∈ Finset.range N, μ[a.raw i (k + 1) | ℱ k] ω‖ ≤
      C * monitorBias t (a.kind i)} with hBdef
  have hB0 : ∀ i, μ (B i) = 0 := by
    intro i
    refine measure_iUnion_null fun N => ?_
    have h := a.drift i N
    rw [ae_iff] at h
    exact h
  set Et : ℝ := Real.exp (-(ε * z ^ 4)) with hEtdef
  have hEi : ∀ i, μ (E i) ≤ ENNReal.ofReal (2 * (a.dimension i : ℝ) * Et) := by
    intro i
    obtain ⟨hbpos, hJpos, hVpos, hmin, -⟩ := monitor_facts hC ht ht1 (a.kind i)
    have h := hconc (Fin (a.dimension i)) Ω μ ℱ (centered μ ℱ (a.raw i)) (a.envelope i)
      (C * monitorJump t (a.kind i)) (C * monitorVariance t (a.kind i)) (b i / 2)
      hJpos hVpos (by simp only [hbdef]; positivity) (a.differences i)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [Fintype.card_fin]
    have hexp : Real.exp (-cc * min ((b i / 2) ^ 2 / (C * monitorVariance t (a.kind i)))
        (b i / 2 / (C * monitorJump t (a.kind i)))) ≤ Et := by
      rw [hEtdef]
      apply Real.exp_le_exp.2
      have h2 : ε * z ^ 4 = cc * (1 / (4 * C * A ^ 3 * y ^ 4)) := by
        rw [hεdef, hKdef, hzdef]; field_simp
      rw [h2, neg_mul]
      apply neg_le_neg
      exact mul_le_mul_of_nonneg_left hmin hcc.le
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  -- the crossing is inside the union
  have hsub : failure ⊆ (⋃ i, E i) ∪ ⋃ i, B i := by
    intro ω hω
    obtain ⟨i, N, hiN⟩ := hfail hω
    by_cases hB : ω ∈ B i
    · exact Or.inr (Set.mem_iUnion.2 ⟨i, hB⟩)
    · left
      refine Set.mem_iUnion.2 ⟨i, N, ?_⟩
      have hdrift : ‖∑ k ∈ Finset.range N, μ[a.raw i (k + 1) | ℱ k] ω‖ ≤
          C * monitorBias t (a.kind i) := by
        by_contra hc
        exact hB (Set.mem_iUnion.2 ⟨N, hc⟩)
      have hbias := (monitor_facts hC ht ht1 (a.kind i)).2.2.2.2 hsmall
      have hsplit := partialSum_centered (μ := μ) (ℱ := ℱ) (a.raw i) N ω
      have htri := norm_add_le (partialSum (centered μ ℱ (a.raw i)) N ω)
        (∑ k ∈ Finset.range N, μ[a.raw i (k + 1) | ℱ k] ω)
      rw [← hsplit] at htri
      show b i / 2 < _
      simp only [hbdef] at hiN ⊢
      linarith
  have hfin : μ failure ≤ ∑ i, μ (E i) := by
    calc μ failure ≤ μ ((⋃ i, E i) ∪ ⋃ i, B i) := measure_mono hsub
      _ ≤ μ (⋃ i, E i) + μ (⋃ i, B i) := measure_union_le _ _
      _ = μ (⋃ i, E i) := by rw [measure_iUnion_null hB0, add_zero]
      _ ≤ ∑ i, μ (E i) := measure_iUnion_fintype_le μ E
  -- final numeric bound
  have hdim : (∑ i, (a.dimension i : ℝ)) ≤ C * z ^ M := by
    have h := a.dimensions
    have e : power t (-6 * (d : ℝ)) = z ^ M := by
      have e1 : -6 * (d : ℝ) = eta * (-(M : ℝ)) := by
        rw [hMdef]; push_cast; norm_num [eta]; ring
      simp only [power_def]
      rw [e1, Real.rpow_mul ht.le, Real.rpow_neg (Real.rpow_nonneg ht.le _), Real.rpow_natCast,
        hzdef, hydef, power_def, one_div, inv_pow]
    rw [e] at h
    exact h
  have hnum : 2 * (∑ i, (a.dimension i : ℝ)) * Et ≤ Real.exp (-power t (-eta)) := by
    have hpz : power t (-eta) = z := by
      simp only [power_def]; rw [Real.rpow_neg ht.le, hzdef, hydef, power_def, one_div]
    rw [hpz]
    calc 2 * (∑ i, (a.dimension i : ℝ)) * Et ≤ 2 * (C * z ^ M) * Et := by
          gcongr
      _ = 2 * C * z ^ M * Real.exp (-(ε * z ^ 4)) := by rw [hEtdef]; ring
      _ ≤ Real.exp (-z) := hZ z hzZ
  calc μ failure ≤ ∑ i, μ (E i) := hfin
    _ ≤ ∑ i, ENNReal.ofReal (2 * (a.dimension i : ℝ) * Et) := Finset.sum_le_sum fun i _ => hEi i
    _ = ENNReal.ofReal (∑ i, 2 * (a.dimension i : ℝ) * Et) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        positivity
    _ = ENNReal.ofReal (2 * (∑ i, (a.dimension i : ℝ)) * Et) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-power t (-eta))) := ENNReal.ofReal_le_ofReal hnum

end AndersonAC.AgentS45
