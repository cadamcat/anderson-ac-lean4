import AndersonAC.AgentS78.InitialStageFull
import AndersonAC.AgentS78.InductionGe
import AndersonAC.AgentS78.Construction.PrefixInduction

open scoped BigOperators
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace AndersonAC.AgentS78.PrefixInduction

open AndersonAC.AgentS78
open AndersonAC.S78
open Filter
private theorem stageScale_pos {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (n m : ℕ) : 0 < stageScale u n m := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  unfold stageScale
  positivity

private theorem stageScale_half_step {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    {n m : ℕ} (hnm : n + 1 ≤ m) :
    stageScale u (n + 1) m ≤ (1 / 2 : ℝ) * stageScale u n m := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have hn0 : 0 < (4 : ℝ) ^ n := by positivity
  have hnp0 : 0 < (4 : ℝ) ^ (n + 1) := by positivity
  have hm0 : 0 < (4 : ℝ) ^ m := by positivity
  have hp : (4 : ℝ) ^ (n + 1) = (4 : ℝ) ^ n * 4 := by
    rw [pow_succ]
  have hpow : (4 : ℝ) ^ (n + 1) ≤ (4 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hnm
  have hrecip : 1 / (4 : ℝ) ^ m ≤ 1 / (4 : ℝ) ^ (n + 1) :=
    one_div_le_one_div_of_le hnp0 hpow
  have hz : u / (4 : ℝ) ^ m ≤ u / (4 : ℝ) ^ (n + 1) := by
    have hrecip' : ((4 : ℝ) ^ m)⁻¹ ≤ ((4 : ℝ) ^ (n + 1))⁻¹ := by
      simpa only [one_div] using hrecip
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrecip' hu0.le
  have hfirst : u / (4 : ℝ) ^ (n + 1) = (1 / 4 : ℝ) * (u / (4 : ℝ) ^ n) := by
    rw [hp]
    field_simp
  have hsecond : u / (4 : ℝ) ^ m ≤ (1 / 4 : ℝ) * (u / (4 : ℝ) ^ n) := hz.trans_eq hfirst
  have hnonneg : 0 ≤ u / (4 : ℝ) ^ m := by positivity
  unfold stageScale
  rw [hfirst]
  nlinarith [hsecond, hnonneg]

private theorem stageScale_ratio_bounds {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    {n m : ℕ} (hnm : n + 1 ≤ m) :
    (1 / 4 : ℝ) ≤ stageScale u (n + 1) m / stageScale u n m ∧
      stageScale u (n + 1) m / stageScale u n m ≤ 5 / 8 := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have hn0 : 0 < (4 : ℝ) ^ n := by positivity
  have hm0 : 0 < (4 : ℝ) ^ m := by positivity
  have hp : (4 : ℝ) ^ (n + 1) = (4 : ℝ) ^ n * 4 := by
    rw [pow_succ]
  have hpow : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (Nat.le_of_succ_le hnm)
  have hrecip : 1 / (4 : ℝ) ^ m ≤ 1 / (4 : ℝ) ^ n :=
    one_div_le_one_div_of_le hn0 hpow
  have hz : u / (4 : ℝ) ^ m ≤ u / (4 : ℝ) ^ n := by
    have hrecip' : ((4 : ℝ) ^ m)⁻¹ ≤ ((4 : ℝ) ^ n)⁻¹ := by
      simpa only [one_div] using hrecip
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrecip' hu0.le
  have hfirst : u / (4 : ℝ) ^ (n + 1) = (1 / 4 : ℝ) * (u / (4 : ℝ) ^ n) := by
    rw [hp]
    field_simp
  have hxpos : 0 < u / (4 : ℝ) ^ n := by positivity
  have hznonneg : 0 ≤ u / (4 : ℝ) ^ m := by positivity
  have hprev : 0 < stageScale u n m := stageScale_pos hu n m
  constructor
  · apply (le_div_iff₀ hprev).2
    unfold stageScale
    rw [hfirst]
    nlinarith [hznonneg]
  · apply (div_le_iff₀ hprev).2
    unfold stageScale
    rw [hfirst]
    nlinarith [hz]

private theorem stageScale_tendsto_bound (u : ℝ) (n m : ℕ)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hn : 1 ≤ n) (hnm : n ≤ m) :
    stageScale u n m ≤ (1 / 2 : ℝ) ^ n := by
  have hscale := AndersonAC.SolS78.stage_scale_comparison_proof u n m hu hnm
  have hpow : 2 / (4 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ n := by
    have hn4 : 0 < (4 : ℝ) ^ n := by positivity
    apply (div_le_iff₀ hn4).2
    have hp : (4 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    rw [mul_comm ((1 / 2 : ℝ) ^ n) ((4 : ℝ) ^ n), hp]
    cases n with
    | zero => omega
    | succ k =>
      rw [pow_succ]
      have hk : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      nlinarith
  exact hscale.2.trans hpow

private theorem stageScale_pow_decay {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    {n m k : ℕ} (hnk : n + k ≤ m) (α : ℝ) (hα : 0 < α) :
    stageScale u (n + k) m ^ α ≤ stageScale u n m ^ α * ((1 / 2 : ℝ) ^ α) ^ k := by
  let q : ℝ := (1 / 2 : ℝ) ^ α
  have hq0 : 0 ≤ q := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
      have hprev : n + k ≤ m := by omega
      have hstep : n + k + 1 ≤ m := by omega
      have ht0 : 0 < stageScale u (n + k) m := stageScale_pos hu (n + k) m
      have ht1 : 0 < stageScale u (n + k + 1) m := stageScale_pos hu (n + k + 1) m
      have hcontract := stageScale_half_step hu hstep
      have hpow : stageScale u (n + k + 1) m ^ α ≤ q * stageScale u (n + k) m ^ α := by
        calc
          stageScale u (n + k + 1) m ^ α ≤
              ((1 / 2 : ℝ) * stageScale u (n + k) m) ^ α :=
            Real.rpow_le_rpow ht1.le hcontract (le_of_lt hα)
          _ = q * stageScale u (n + k) m ^ α := by
            rw [Real.mul_rpow (by norm_num) ht0.le]
      calc
        stageScale u (n + (k + 1)) m ^ α ≤ q * stageScale u (n + k) m ^ α := by
          simpa [Nat.add_assoc, q] using hpow
        _ ≤ q * (stageScale u n m ^ α * q ^ k) :=
          mul_le_mul_of_nonneg_left (ih hprev) hq0
        _ = stageScale u n m ^ α * q ^ (k + 1) := by rw [pow_succ]; ring

private theorem sum_range_geometric_le (a q : ℝ) (ha : 0 ≤ a)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, a * q ^ i) ≤ a * (1 - q)⁻¹ := by
  have hs : Summable (fun i : ℕ => a * q ^ i) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left a
  calc
    (∑ i ∈ Finset.range k, a * q ^ i) ≤ ∑' i : ℕ, a * q ^ i :=
      hs.sum_le_tsum (Finset.range k) (fun i hi => mul_nonneg ha (pow_nonneg hq0 i))
    _ = a * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

private theorem stageScale_pow_sum_bound {u : ℝ}
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {n k m : ℕ}
    (hnk : n ≤ k) (hkm : k ≤ m) (α : ℝ) (hα : 0 < α) :
    (∑ j ∈ Finset.Ico n k, stageScale u j m ^ α) ≤
      stageScale u n m ^ α * (1 - (1 / 2 : ℝ) ^ α)⁻¹ := by
  let q : ℝ := (1 / 2 : ℝ) ^ α
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hα
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    (∑ j ∈ Finset.range (k - n), stageScale u (n + j) m ^ α) ≤
        ∑ j ∈ Finset.range (k - n), stageScale u n m ^ α * q ^ j :=
      Finset.sum_le_sum fun j hj => by
        have hjlt : j < k - n := Finset.mem_range.mp hj
        have hnj : n + j < k := by omega
        exact stageScale_pow_decay hu (by omega) α hα
    _ ≤ stageScale u n m ^ α * (1 - q)⁻¹ :=
      sum_range_geometric_le (stageScale u n m ^ α) q
        (Real.rpow_nonneg (stageScale_pos hu n m).le α) hq0 hq1 (k - n)
    _ = stageScale u n m ^ α * (1 - (1 / 2 : ℝ) ^ α)⁻¹ := by rfl

private theorem prod_one_sub_ge_one_sub_sum {ι : Type} (s : Finset ι) (e : ι → ℝ)
    (he0 : ∀ i ∈ s, 0 ≤ e i) (he1 : ∀ i ∈ s, e i ≤ 1) :
    1 - (∑ i ∈ s, e i) ≤ ∏ i ∈ s, (1 - e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha0 := he0 a (Finset.mem_insert_self a s)
      have ha1 := he1 a (Finset.mem_insert_self a s)
      have hs0 : ∀ i ∈ s, 0 ≤ e i := fun i hi => he0 i (Finset.mem_insert_of_mem hi)
      have hs1 : ∀ i ∈ s, e i ≤ 1 := fun i hi => he1 i (Finset.mem_insert_of_mem hi)
      have hsum0 : 0 ≤ ∑ i ∈ s, e i := Finset.sum_nonneg fun i hi => hs0 i hi
      have hih := ih hs0 hs1
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hmul := mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr ha1)
      nlinarith [hmul, mul_nonneg ha0 hsum0]

private theorem prod_error_factors_bounds {ι : Type} (s : Finset ι) (e : ι → ℝ)
    (he0 : ∀ i ∈ s, 0 ≤ e i)
    (hsum : (∑ i ∈ s, e i) ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ∏ i ∈ s, (1 - e i) ∧
      1 ≤ ∏ i ∈ s, (1 + e i) ∧ ∏ i ∈ s, (1 + e i) ≤ 2 := by
  classical
  have heSmall : ∀ i ∈ s, e i ≤ 1 / 2 := by
    intro i hi
    exact (Finset.single_le_sum (fun j hj => he0 j hj) hi).trans hsum
  have heLeOne : ∀ i ∈ s, e i ≤ 1 := fun i hi => (heSmall i hi).trans (by norm_num)
  have hprodLow := prod_one_sub_ge_one_sub_sum s e he0 heLeOne
  have hsum0 : 0 ≤ ∑ i ∈ s, e i := Finset.sum_nonneg fun i hi => he0 i hi
  have hQ : (1 / 2 : ℝ) ≤ ∏ i ∈ s, (1 - e i) := by linarith [hprodLow]
  have hQpos : 0 < ∏ i ∈ s, (1 - e i) := lt_of_lt_of_le (by norm_num) hQ
  have hPlo : 1 ≤ ∏ i ∈ s, (1 + e i) := by
    apply Finset.one_le_prod₀
    intro i hi
    linarith [he0 i hi]
  have hfactor : ∀ i ∈ s, 1 + e i ≤ (1 - e i)⁻¹ := by
    intro i hi
    have hpos : 0 < 1 - e i := by linarith [heSmall i hi]
    have hmul : (1 + e i) * (1 - e i) ≤ 1 := by nlinarith [sq_nonneg (e i)]
    have hdiv : 1 + e i ≤ 1 / (1 - e i) := (le_div_iff₀ hpos).2 hmul
    simpa only [one_div] using hdiv
  have hP : ∏ i ∈ s, (1 + e i) ≤ (∏ i ∈ s, (1 - e i))⁻¹ := by
    calc
      ∏ i ∈ s, (1 + e i) ≤ ∏ i ∈ s, ((1 - e i)⁻¹) :=
        Finset.prod_le_prod₀ (fun i hi => by linarith [he0 i hi]) hfactor
      _ = (∏ i ∈ s, (1 - e i))⁻¹ := by rw [Finset.prod_inv_distrib]
  have hinv : (∏ i ∈ s, (1 - e i))⁻¹ ≤ 2 := by
    have h : (∏ i ∈ s, (1 - e i))⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
      (inv_le_inv₀ hQpos (by norm_num : (0 : ℝ) < 1 / 2)).2 hQ
    norm_num at h ⊢
    exact h
  exact ⟨hQ, hPlo, hP.trans hinv⟩

private theorem stageScale_antitone {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    {n j m : ℕ} (hnj : n ≤ j) : stageScale u j m ≤ stageScale u n m := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have hn0 : 0 < (4 : ℝ) ^ n := by positivity
  have hj0 : 0 < (4 : ℝ) ^ j := by positivity
  have hpow : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ j :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hnj
  have hrecip : ((4 : ℝ) ^ j)⁻¹ ≤ ((4 : ℝ) ^ n)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hn0 hpow
  have hfirst : u / (4 : ℝ) ^ j ≤ u / (4 : ℝ) ^ n := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrecip hu0.le
  unfold stageScale
  exact add_le_add hfirst le_rfl

private theorem exists_half_rpow_small (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((1 / 2 : ℝ) ^ n) ^ α < ε := by
  let q : ℝ := (1 / 2 : ℝ) ^ α
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have htendsto : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have heq : (fun n : ℕ => ((1 / 2 : ℝ) ^ n) ^ α) = fun n => q ^ n := by
    funext n
    dsimp [q]
    rw [← Real.rpow_pow_comm (by norm_num) α n]
  have hsmall : ∀ᶠ n : ℕ in atTop, ((1 / 2 : ℝ) ^ n) ^ α < ε := by
    have h := htendsto.eventually (Iio_mem_nhds hε)
    simpa only [← heq] using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  exact ⟨N, fun n hn => hN n hn⟩

private theorem exists_scaled_half_rpow_small (α K ε : ℝ)
    (hα : 0 < α) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → K * ((1 / 2 : ℝ) ^ n) ^ α < ε := by
  have hden : 0 < K + 1 := by linarith
  obtain ⟨N, hN⟩ := exists_half_rpow_small α (ε / (K + 1)) hα (div_pos hε hden)
  refine ⟨N, ?_⟩
  intro n hn
  have hpow := hN n hn
  have hmul := mul_le_mul_of_nonneg_left hpow.le hK
  have hfracStrict : K * (ε / (K + 1)) < ε := by
    calc
      K * (ε / (K + 1)) = (K * ε) / (K + 1) := by ring
      _ < ε := (div_lt_iff₀ hden).2 (by nlinarith [mul_pos hε hden])
  exact lt_of_le_of_lt hmul hfracStrict

private theorem sum_eq_of_subset_zero {ι : Type} [DecidableEq ι]
    (A B : Finset ι) (hBA : B ⊆ A) (f : ι → ℝ)
    (hzero : ∀ i ∈ A, i ∉ B → f i = 0) :
    (∑ i ∈ A, f i) = ∑ i ∈ B, f i := by
  exact (Finset.sum_subset hBA hzero).symm

private theorem inverse_square_change (c C x a b : ℝ)
    (hc : 0 < c) (ha : c / 2 ≤ a) (hb : c / 2 ≤ b)
    (hdiff : |a - b| ≤ C * x) (hC : 0 ≤ C) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 / a ^ 2 ≤ (1 + (4 * C / c + 4 * (C / c) ^ 2) * x) / b ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hfactor : 1 ≤ (2 / c) * a := by
    have hca : c ≤ 2 * a := by nlinarith
    have hca' : 1 * c ≤ 2 * a := by nlinarith
    calc
      1 ≤ (2 * a) / c := (le_div_iff₀ hc).2 hca'
      _ = (2 / c) * a := by ring
  have hdelta : 0 ≤ C * x := mul_nonneg hC hx0
  have hdeltaScaled : C * x ≤ (2 * C / c * x) * a := by
    calc
      C * x = (C * x) * 1 := by ring
      _ ≤ (C * x) * ((2 / c) * a) := mul_le_mul_of_nonneg_left hfactor hdelta
      _ = (2 * C / c * x) * a := by ring
  have hbUpper : b ≤ (1 + 2 * C / c * x) * a := by
    have hab : b - a ≤ |a - b| := by
      have := le_abs_self (b - a)
      simpa only [abs_sub_comm] using this
    nlinarith [hab.trans (by linarith : |a - b| ≤ C * x), hdeltaScaled]
  have hv0 : 0 ≤ 2 * C / c * x := by positivity
  have hbase0 : 0 ≤ (1 + 2 * C / c * x) * a := by positivity
  have hsq : b ^ 2 ≤ ((1 + 2 * C / c * x) * a) ^ 2 := by
    nlinarith [sq_nonneg (b - (1 + 2 * C / c * x) * a)]
  have hxSq : x ^ 2 ≤ x := by nlinarith [sq_nonneg (x - 1 / 2)]
  let z : ℝ := C / c
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : 2 * C / c * x = 2 * z * x := by dsimp [z]; ring
  have hcoeff : (1 + 2 * C / c * x) ^ 2 ≤ 1 + (4 * C / c + 4 * (C / c) ^ 2) * x := by
    rw [hz1]
    calc
      (1 + 2 * z * x) ^ 2 = 1 + 4 * z * x + 4 * z ^ 2 * x ^ 2 := by ring
      _ ≤ 1 + 4 * z * x + 4 * z ^ 2 * x := by
        nlinarith [mul_le_mul_of_nonneg_left hxSq (sq_nonneg z)]
      _ = 1 + (4 * C / c + 4 * (C / c) ^ 2) * x := by dsimp [z]; ring
  have hmain : b ^ 2 ≤ (1 + (4 * C / c + 4 * (C / c) ^ 2) * x) * a ^ 2 := by
    calc
      b ^ 2 ≤ ((1 + 2 * C / c * x) * a) ^ 2 := hsq
      _ = (1 + 2 * C / c * x) ^ 2 * a ^ 2 := by ring
      _ ≤ (1 + (4 * C / c + 4 * (C / c) ^ 2) * x) * a ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg a)
  rw [div_le_div_iff₀ (sq_pos_of_pos ha0) (sq_pos_of_pos hb0)]
  nlinarith [hmain]

private theorem inverse_square_damping (c a : ℝ) (hc : 0 < c) (ha : c / 2 ≤ a) :
    1 / a ^ 2 ≤ 4 / c ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hhalf : 0 ≤ c / 2 := by positivity
  have haNonneg : 0 ≤ a := ha0.le
  have hsquare : (c / 2) ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hhalf haNonneg).2 ha
  rw [div_le_div_iff₀ (sq_pos_of_pos ha0) (sq_pos_of_pos hc)]
  nlinarith

private theorem inverseEnergy_nonneg_of_zero {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (y : ι → ℝ) (hD0 : D 0 = 0) :
    0 ≤ inverseEnergy A D y := by
  classical
  unfold inverseEnergy
  let f : (ι → ℝ) → ℝ := fun z => 2 * (∑ i ∈ A, y i * z i) - D z
  have hmem : 0 ∈ Set.range f := by
    refine ⟨0, ?_⟩
    simp [f, hD0]
  by_cases hb : BddAbove (Set.range f)
  · exact le_csSup hb hmem
  · rw [csSup_of_not_bddAbove hb]
    simp

private theorem damping_of_close {ι : Type} (A₀ A : Finset ι)
    (r₀ r : ι → ℂ) (c C δ : ℝ)
    (hc : 0 < c) (hC : c ≤ C) (hδ : δ ≤ c / 4)
    (hsub : A ⊆ A₀)
    (hbase : ∀ i ∈ A₀, c ≤ (r₀ i).im ∧ (r₀ i).im ≤ C ∧ ‖r₀ i‖ ≤ C)
    (hclose : ∀ i, ‖r i - r₀ i‖ ≤ δ) :
    ∀ i ∈ A, c / 2 ≤ (r i).im ∧ (r i).im ≤ 2 * C ∧ ‖r i‖ ≤ 2 * C := by
  intro i hi
  have h0 := hbase i (hsub hi)
  have hc0 := hclose i
  have him : |(r i).im - (r₀ i).im| ≤ ‖r i - r₀ i‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (r i - r₀ i)
  have hnorm : ‖r i‖ ≤ ‖r₀ i‖ + ‖r i - r₀ i‖ := by
    calc
      ‖r i‖ = ‖(r i - r₀ i) + r₀ i‖ := by congr 1 <;> abel
      _ ≤ ‖r i - r₀ i‖ + ‖r₀ i‖ := norm_add_le _ _
      _ = ‖r₀ i‖ + ‖r i - r₀ i‖ := by ring
  have himSmall : |(r i).im - (r₀ i).im| ≤ c / 4 := (him.trans hc0).trans hδ
  refine ⟨?_, ?_, ?_⟩
  · have h := (abs_le.mp himSmall).1
    nlinarith [h0.1]
  · have h := (abs_le.mp himSmall).2
    nlinarith [h0.2.1, hc, hC]
  · nlinarith [hnorm, hc0, hδ, h0.2.2, hc, hC]

private theorem tight_scalar_step (a θ τ e v θpow : ℝ)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (he0 : 0 ≤ e) (hv0 : 0 ≤ v)
    (he : e ≤ a / 16 * τ) (hv : v ≤ a / 16 * τ)
    (hmarg : a ≤ θpow - θ) :
    (1 + e) * (1 + θ * τ) * (1 + v) ≤ 1 + θpow * τ := by
  have hvSmall : v ≤ 1 := by
    calc
      v ≤ a / 16 * τ := hv
      _ ≤ a / 16 := by
        nlinarith [mul_nonneg (show 0 ≤ a / 16 by positivity) (sub_nonneg.mpr hτ1)]
      _ ≤ 1 := by linarith [ha1]
  have hev : e * v ≤ e := by
    calc
      e * v ≤ e * 1 := mul_le_mul_of_nonneg_left hvSmall he0
      _ = e := by ring
  have hextra : e + v + e * v ≤ 2 * (e + v) := by nlinarith [hev]
  have hbase : 1 + θ * τ ≤ 2 := by nlinarith [hθ0, hθ1, hτ0, hτ1]
  have hfactorNonneg : 0 ≤ e + v + e * v := by positivity
  have hmul :
      (1 + e) * (1 + θ * τ) * (1 + v) ≤ 1 + θ * τ + 4 * (e + v) := by
    calc
      (1 + e) * (1 + θ * τ) * (1 + v) =
          1 + θ * τ + (1 + θ * τ) * (e + v + e * v) := by ring
      _ ≤ 1 + θ * τ + 2 * (e + v + e * v) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hbase hfactorNonneg)
      _ ≤ 1 + θ * τ + 4 * (e + v) := by nlinarith [hextra]
  have hsum : 4 * (e + v) ≤ a / 2 * τ := by nlinarith [he, hv]
  have hmarg' := mul_le_mul_of_nonneg_left hmarg hτ0
  nlinarith [hmul, hsum, hmarg']
theorem prefix_deterministic_induction_ge (d : ℕ) (hd : 3 ≤ d) (cP CP cL CL C : ℝ)
    (hcP : 0 < cP) (hCP : cP ≤ CP) (hcL : 0 < cL) (hCL : 0 < CL) (hC : 1 ≤ C)
    (C₀ : ℝ) (hC₀ : 4 / cP ^ 2 + 1 ≤ C₀) :
    ∃ N : ℕ, ∀ m n₀ K u (H : PrefixStageInputs d m n₀ K u C),
      N ≤ n₀ → 4 * n₀ ≤ m → K ≤ m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      StageBounds d m n₀ n₀ u cP CP cL CL C₀ (H.state n₀) (H.r n₀) →
      matrixNorm (squareKernel (normalizedInverse (H.state n₀) (stageScale u n₀ m))) ≤ 1 / 4 →
      ∀ n, n₀ ≤ n → n ≤ K →
        StageBounds d m n₀ n u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀
          (H.state n) (H.r n) := by
  let η : ℝ := 0.10 * delta
  let σ : ℝ := 0.35 * delta
  let κ : ℝ := 0.005 * delta
  let ρ : ℝ := η - κ
  let A : ℝ := 4 / cP ^ 2
  let Dvar : ℝ := 4 * C / cP + 4 * (C / cP) ^ 2
  have hη : 0 < η := by norm_num [η, delta]
  have hσ : 0 < σ := by norm_num [σ, delta]
  have hκ : 0 < κ := by norm_num [κ, delta]
  have hκ1 : κ < 1 := by norm_num [κ, delta]
  have hρ : 0 < ρ := by norm_num [η, κ, ρ, delta]
  have hρη : ρ ≤ η := by norm_num [η, κ, ρ, delta]
  have hρσ : ρ ≤ σ := by norm_num [η, σ, κ, ρ, delta]
  have hρσκ : ρ ≤ σ - κ := by norm_num [η, σ, κ, ρ, delta]
  have hηeq : η = κ + ρ := by dsimp [η, κ, ρ]; ring
  have hσeq : σ = κ + (σ - κ) := by ring
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hCPpos : 0 < CP := hcP.trans_le hCP
  have hApos : 0 < A := by dsimp [A]; positivity
  have hC₀pos : 0 < C₀ := by
    have : 0 < 4 / cP ^ 2 + 1 := by positivity
    linarith
  have hDvar : 0 < Dvar := by dsimp [Dvar]; positivity
  obtain ⟨asharp, hasharp, hsharp⟩ :=
    AndersonAC.SolS78.sharp_diagonal_margin_proof κ hκ hκ1
  let a : ℝ := min asharp (1 / 2)
  have ha : 0 < a := lt_min hasharp (by norm_num)
  have haHalf : a ≤ 1 / 2 := min_le_right _ _
  have hsharp' : ∀ θ ∈ Set.Icc (0.25 : ℝ) 0.625, a ≤ θ ^ κ - θ := by
    intro θ hθ
    exact (min_le_left _ _).trans (hsharp θ hθ)
  let qη : ℝ := (1 / 2 : ℝ) ^ η
  let qσ : ℝ := (1 / 2 : ℝ) ^ σ
  have hqη0 : 0 ≤ qη := by positivity
  have hqσ0 : 0 ≤ qσ := by positivity
  have hqη1 : qη < 1 := by
    dsimp [qη]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hη
  have hqσ1 : qσ < 1 := by
    dsimp [qσ]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hσ
  let Aη : ℝ := C * (1 - qη)⁻¹
  let Aσ : ℝ := C * (1 - qσ)⁻¹
  have hAη : 0 < Aη := by dsimp [Aη]; positivity
  have hAσ : 0 < Aσ := by dsimp [Aσ]; positivity
  obtain ⟨Nη, hNη⟩ := exists_scaled_half_rpow_small ρ Aη (1 / 12) hρ
    (le_of_lt hAη) (by norm_num)
  obtain ⟨Nσ, hNσ⟩ := exists_scaled_half_rpow_small ρ Aσ (cP / 4) hρ
    (le_of_lt hAσ) (by positivity)
  obtain ⟨Ncoarse, hNcoarse⟩ := exists_scaled_half_rpow_small ρ (C * C₀) (3 / 16) hρ
    (by positivity) (by norm_num)
  obtain ⟨Nhigh, hNhigh⟩ := exists_scaled_half_rpow_small ρ C (a / 16) hρ
    (le_of_lt hCpos) (by positivity)
  obtain ⟨Nvar, hNvar⟩ := exists_scaled_half_rpow_small ρ Dvar (a / 16) hρ
    (le_of_lt hDvar) (by positivity)
  let N : ℕ := max 1 (max Nη (max Nσ (max Ncoarse (max Nhigh Nvar))))
  have hNpos : 1 ≤ N := by dsimp [N]; omega
  have hNηle : Nη ≤ N := by dsimp [N]; omega
  have hNσle : Nσ ≤ N := by dsimp [N]; omega
  have hNcoarsele : Ncoarse ≤ N := by dsimp [N]; omega
  have hNhighle : Nhigh ≤ N := by dsimp [N]; omega
  have hNvarle : Nvar ≤ N := by dsimp [N]; omega
  refine ⟨N, ?_⟩
  intro m n₀ K u H hnN hm hKm hu hInit hKinit n hn₀n hnK
  have hnm : n ≤ m := hnK.trans hKm
  have hn₀pos : 1 ≤ n₀ := le_trans hNpos hnN
  have hn₀m : n₀ ≤ m := by omega
  have hs₀pos : 0 < stageScale u n₀ m := stageScale_pos hu n₀ m
  have hs₀half : stageScale u n₀ m ≤ (1 / 2 : ℝ) ^ n₀ :=
    stageScale_tendsto_bound u n₀ m hu hn₀pos hn₀m
  have hs₀one : stageScale u n₀ m ≤ 1 := by
    have hpow : (1 / 2 : ℝ) ^ n₀ ≤ 1 :=
      pow_le_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    exact hs₀half.trans hpow
  have hsrho : stageScale u n₀ m ^ ρ ≤ ((1 / 2 : ℝ) ^ n₀) ^ ρ :=
    Real.rpow_le_rpow hs₀pos.le hs₀half (le_of_lt hρ)
  have hsmallη : Aη * stageScale u n₀ m ^ ρ < 1 / 12 := by
    calc
      Aη * stageScale u n₀ m ^ ρ ≤ Aη * ((1 / 2 : ℝ) ^ n₀) ^ ρ :=
        mul_le_mul_of_nonneg_left hsrho (le_of_lt hAη)
      _ < 1 / 12 := hNη n₀ (le_trans hNηle hnN)
  have hsmallσ : Aσ * stageScale u n₀ m ^ ρ < cP / 4 := by
    calc
      Aσ * stageScale u n₀ m ^ ρ ≤ Aσ * ((1 / 2 : ℝ) ^ n₀) ^ ρ :=
        mul_le_mul_of_nonneg_left hsrho (le_of_lt hAσ)
      _ < cP / 4 := hNσ n₀ (le_trans hNσle hnN)
  have hsmallCoarse : C * C₀ * stageScale u n₀ m ^ ρ < 3 / 16 := by
    calc
      C * C₀ * stageScale u n₀ m ^ ρ ≤ C * C₀ * ((1 / 2 : ℝ) ^ n₀) ^ ρ :=
        mul_le_mul_of_nonneg_left hsrho (by positivity)
      _ < 3 / 16 := hNcoarse n₀ (le_trans hNcoarsele hnN)
  have hsmallHigh : C * stageScale u n₀ m ^ ρ < a / 16 := by
    calc
      C * stageScale u n₀ m ^ ρ ≤ C * ((1 / 2 : ℝ) ^ n₀) ^ ρ :=
        mul_le_mul_of_nonneg_left hsrho (le_of_lt hCpos)
      _ < a / 16 := hNhigh n₀ (le_trans hNhighle hnN)
  have hsmallVar : Dvar * stageScale u n₀ m ^ ρ < a / 16 := by
    calc
      Dvar * stageScale u n₀ m ^ ρ ≤ Dvar * ((1 / 2 : ℝ) ^ n₀) ^ ρ :=
        mul_le_mul_of_nonneg_left hsrho (le_of_lt hDvar)
      _ < a / 16 := hNvar n₀ (le_trans hNvarle hnN)
  have hsηpow : stageScale u n₀ m ^ η ≤ stageScale u n₀ m ^ ρ :=
    Real.rpow_le_rpow_of_exponent_ge hs₀pos hs₀one hρη
  have hsσpow : stageScale u n₀ m ^ σ ≤ stageScale u n₀ m ^ ρ :=
    Real.rpow_le_rpow_of_exponent_ge hs₀pos hs₀one hρσ
  have hηMass : ∀ k, n₀ ≤ k → k ≤ m →
      C * (∑ j ∈ Finset.Ico n₀ k, stageScale u j m ^ η) ≤ 1 / 12 := by
    intro k h₀k hkm
    have hsum := stageScale_pow_sum_bound hu h₀k hkm η hη
    calc
      C * (∑ j ∈ Finset.Ico n₀ k, stageScale u j m ^ η) ≤
          C * (stageScale u n₀ m ^ η * (1 - qη)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hCpos.le
      _ = Aη * stageScale u n₀ m ^ η := by dsimp [Aη, qη]; ring
      _ ≤ Aη * stageScale u n₀ m ^ ρ := mul_le_mul_of_nonneg_left hsηpow (le_of_lt hAη)
      _ ≤ 1 / 12 := (le_of_lt hsmallη)
  have hσMass : ∀ k, n₀ ≤ k → k ≤ m →
      C * (∑ j ∈ Finset.Ico n₀ k, stageScale u j m ^ σ) ≤ cP / 4 := by
    intro k h₀k hkm
    have hsum := stageScale_pow_sum_bound hu h₀k hkm σ hσ
    calc
      C * (∑ j ∈ Finset.Ico n₀ k, stageScale u j m ^ σ) ≤
          C * (stageScale u n₀ m ^ σ * (1 - qσ)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hCpos.le
      _ = Aσ * stageScale u n₀ m ^ σ := by dsimp [Aσ, qσ]; ring
      _ ≤ Aσ * stageScale u n₀ m ^ ρ := mul_le_mul_of_nonneg_left hsσpow (le_of_lt hAσ)
      _ ≤ cP / 4 := (le_of_lt hsmallσ)
  have hInit' := hInit
  simp only [StageBounds] at hInit'
  rcases hInit' with ⟨hDampInit, hRowsInit, hNormInit, hKernelInit, hCountInit, hMetricInit, hFormsInit⟩
  have hDampBase : ∀ i ∈ (H.state n₀).active,
      cP ≤ (H.r n₀ i).im ∧ (H.r n₀ i).im ≤ CP ∧ ‖H.r n₀ i‖ ≤ CP := by
    intro i hi
    rcases hDampInit i hi with ⟨_, hlow, hup, hnorm⟩
    exact ⟨hlow, hup, hnorm⟩
  have hGradZero : gradientEnergy (nnGraph d m) (0 : Torus d m → ℝ) = 0 := by
    simp [gradientEnergy]
  have hLambdaNonneg : ∀ y, 0 ≤ inverseEnergy Finset.univ
      (gradientEnergy (nnGraph d m)) y := by
    intro y
    apply inverseEnergy_nonneg_of_zero
    exact hGradZero
  have hEnergyZero : ∀ j, endpointEnergy (H.state j) (H.r j)
      (stageScale u j m) (0 : Torus d m → ℝ) = 0 := by
    intro j
    simp [endpointEnergy, wardEnergy]
  let Eη : ℕ → ℝ := fun j => ∑ i ∈ Finset.Ico n₀ j, stageScale u i m ^ η
  let Eσ : ℕ → ℝ := fun j => ∑ i ∈ Finset.Ico n₀ j, stageScale u i m ^ σ
  let err : ℕ → ℝ := fun j => C * stageScale u j m ^ η
  let Pplus : ℕ → ℝ := fun j => ∏ i ∈ Finset.Ico n₀ j, (1 + err i)
  let Pminus : ℕ → ℝ := fun j => ∏ i ∈ Finset.Ico n₀ j, (1 - err i)
  let bAt : ℕ → ℝ := fun j => stageScale u n₀ m * stageScale u j m
  let X : ℕ → (Torus d m → ℝ) → ℝ := fun j y =>
    inverseEnergy (H.state j).active
      (endpointEnergy (H.state j) (H.r j) (stageScale u j m)) y
  let Lambda : (Torus d m → ℝ) → ℝ := fun y =>
    inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y
  let plain : ℕ → (Torus d m → ℝ) → ℝ := fun j y =>
    ∑ i ∈ (H.state j).active, (y i) ^ 2
  let diag : ℕ → (Torus d m → ℝ) → ℝ := fun j y =>
    ∑ i ∈ (H.state j).active, (y i) ^ 2 / (H.r j i).im ^ 2
  let Core : ℕ → Prop := fun j =>
    (∀ i, ‖H.r j i - H.r n₀ i‖ ≤ C * Eσ j) ∧
    matrixNorm (squareKernel (normalizedInverse (H.state j) (stageScale u j m))) ≤
      1 / 4 + C * Eη j ∧
    (H.state j).active ⊆ (H.state n₀).active ∧
    ∀ y, neutral (H.state j).active y →
      cL * bAt j * Pminus j * Lambda y ≤ X j y ∧
      X j y ≤ C₀ * plain j y + CL * Pplus j * bAt j * Lambda y ∧
      X j y ≤ (1 + stageScale u j m ^ κ) * diag j y +
        CL * Pplus j * stageScale u j m * Lambda y
  have hCore : ∀ k, n₀ + k ≤ K → Core (n₀ + k) := by
    intro k
    induction k with
    | zero =>
        intro hbound
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          simp [Eσ]
        · simpa [Eη] using hKinit
        · exact Finset.Subset.rfl
        · intro y hy
          rcases hFormsInit y hy with ⟨hlow, hcoarse, htight⟩
          refine ⟨?_, ?_, ?_⟩
          · simpa [Pminus, bAt, Lambda, X] using hlow
          · simpa [Pplus, bAt, Lambda, plain, X] using hcoarse
          · simpa [Pplus, diag, Lambda, X] using htight
    | succ k ih =>
        intro hbound
        let j : ℕ := n₀ + k
        have hj0 : n₀ ≤ j := by dsimp [j]; omega
        have hjm : j ≤ m := by dsimp [j]; omega
        have hjlt : j < K := by dsimp [j]; omega
        have hjCore : Core j := ih (by omega)
        rcases hjCore with ⟨hclose, hK, hsubset, hForms⟩
        have hcloseNext : ∀ i, ‖H.r (j + 1) i - H.r n₀ i‖ ≤ C * Eσ (j + 1) := by
          intro i
          have hstepPoint : ‖(H.r (j + 1) - H.r j) i‖ ≤ C * stageScale u j m ^ σ := by
            exact (norm_le_pi_norm (H.r (j + 1) - H.r j) i).trans
              (H.rStep j hj0 hjlt)
          calc
            ‖H.r (j + 1) i - H.r n₀ i‖ =
                ‖(H.r (j + 1) i - H.r j i) + (H.r j i - H.r n₀ i)‖ := by
                  congr 1 <;> abel
            _ ≤ ‖H.r (j + 1) i - H.r j i‖ + ‖H.r j i - H.r n₀ i‖ := norm_add_le _ _
            _ ≤ C * stageScale u j m ^ σ + C * Eσ j := add_le_add hstepPoint (hclose i)
            _ = C * Eσ (j + 1) := by
              dsimp [Eσ]
              rw [Finset.sum_Ico_succ_top (by omega)]
              ring
        have hKnext : matrixNorm (squareKernel
            (normalizedInverse (H.state (j + 1)) (stageScale u (j + 1) m))) ≤
              1 / 4 + C * Eη (j + 1) := by
          calc
            _ ≤ matrixNorm (squareKernel (normalizedInverse (H.state j) (stageScale u j m))) +
                C * stageScale u j m ^ η := H.normStep j hj0 hjlt
            _ ≤ (1 / 4 + C * Eη j) + C * stageScale u j m ^ η :=
              add_le_add hK le_rfl
            _ = 1 / 4 + C * Eη (j + 1) := by
              dsimp [Eη]
              rw [Finset.sum_Ico_succ_top (by omega)]
              ring
        have hsubsetNext : (H.state (j + 1)).active ⊆ (H.state n₀).active :=
          (H.nested j hj0 hjlt).trans hsubset
        have hσOld : C * Eσ j ≤ cP / 4 := hσMass j hj0 hjm
        have hσNext : C * Eσ (j + 1) ≤ cP / 4 := hσMass (j + 1) (by omega) (by omega)
        have hDampOld := damping_of_close (H.state n₀).active (H.state j).active
          (H.r n₀) (H.r j) cP CP (C * Eσ j) hcP hCP
          hσOld hsubset hDampBase hclose
        have hDampNext := damping_of_close (H.state n₀).active (H.state (j + 1)).active
          (H.r n₀) (H.r (j + 1)) cP CP (C * Eσ (j + 1)) hcP hCP
          hσNext hsubsetNext hDampBase hcloseNext
        have hnewSub : (H.state (j + 1)).active ⊆ (H.state j).active := H.nested j hj0 hjlt
        have hthetaBounds := stageScale_ratio_bounds hu (by omega : j + 1 ≤ m)
        let θ : ℝ := stageScale u (j + 1) m / stageScale u j m
        have hθlo : (1 / 4 : ℝ) ≤ θ := by simpa [θ] using hthetaBounds.1
        have hθhi : θ ≤ 5 / 8 := by simpa [θ] using hthetaBounds.2
        have hθ0 : 0 ≤ θ := le_trans (by norm_num) hθlo
        have hθ1 : θ ≤ 1 := hθhi.trans (by norm_num)
        have htjpos : 0 < stageScale u j m := stageScale_pos hu j m
        have htjle : stageScale u j m ≤ 1 := by
          exact (stageScale_antitone hu hj0).trans hs₀one
        have hθmul : θ * stageScale u j m = stageScale u (j + 1) m := by
          dsimp [θ]
          exact div_mul_cancel₀ _ (ne_of_gt htjpos)
        have hθIcc : θ ∈ Set.Icc (0.25 : ℝ) 0.625 := by
          constructor
          · norm_num at hθlo ⊢
            exact hθlo
          · norm_num at hθhi ⊢
            exact hθhi
        have hmarginθ : a ≤ θ ^ κ - θ := hsharp' θ hθIcc
        have hτ0 : 0 ≤ stageScale u j m ^ κ := Real.rpow_nonneg htjpos.le κ
        have hτ1 : stageScale u j m ^ κ ≤ 1 :=
          Real.rpow_le_one htjpos.le htjle hκ.le
        have hτnext : stageScale u (j + 1) m ^ κ = θ ^ κ * stageScale u j m ^ κ := by
          rw [← hθmul, Real.mul_rpow hθ0 htjpos.le]
        have hErrSum : (∑ i ∈ Finset.Ico n₀ (j + 1), err i) ≤ 1 / 2 := by
          change (∑ i ∈ Finset.Ico n₀ (j + 1), C * stageScale u i m ^ η) ≤ 1 / 2
          rw [← Finset.mul_sum]
          exact (hηMass (j + 1) (by omega) (by omega)).trans (by norm_num)
        have hErrNonneg : ∀ i ∈ Finset.Ico n₀ (j + 1), 0 ≤ err i := by
          intro i hi
          dsimp [err]
          exact mul_nonneg hCpos.le (Real.rpow_nonneg (stageScale_pos hu i m).le η)
        have hProducts := prod_error_factors_bounds (Finset.Ico n₀ (j + 1)) err
          hErrNonneg hErrSum
        have hPplusStep : Pplus (j + 1) = Pplus j * (1 + err j) := by
          dsimp [Pplus]
          rw [Finset.prod_Ico_succ_top (by omega)]
        have hPminusStep : Pminus (j + 1) = Pminus j * (1 - err j) := by
          dsimp [Pminus]
          rw [Finset.prod_Ico_succ_top (by omega)]
        have hErrCurrent : 0 ≤ err j ∧ err j ≤ 1 / 2 := by
          constructor
          · dsimp [err]; positivity
          · exact (Finset.single_le_sum hErrNonneg
              (Finset.mem_Ico.mpr ⟨hj0, Nat.lt_succ_self j⟩)).trans hErrSum
        have hPbounds : 1 / 2 ≤ Pminus (j + 1) ∧ 1 ≤ Pplus (j + 1) ∧
            Pplus (j + 1) ≤ 2 := by simpa [Pplus, Pminus] using hProducts
        have hEnergyZeroOld := hEnergyZero j
        have hnewEnergyZero := hEnergyZero (j + 1)
        have hnewXnonneg (y : Torus d m → ℝ) : 0 ≤ X (j + 1) y := by
          exact inverseEnergy_nonneg_of_zero (H.state (j + 1)).active
            (endpointEnergy (H.state (j + 1)) (H.r (j + 1)) (stageScale u (j + 1) m)) y
            hnewEnergyZero
        have hFormsNext : ∀ y, neutral (H.state (j + 1)).active y →
            cL * bAt (j + 1) * Pminus (j + 1) * Lambda y ≤ X (j + 1) y ∧
            X (j + 1) y ≤ C₀ * plain (j + 1) y +
              CL * Pplus (j + 1) * bAt (j + 1) * Lambda y ∧
            X (j + 1) y ≤ (1 + stageScale u (j + 1) m ^ κ) * diag (j + 1) y +
              CL * Pplus (j + 1) * stageScale u (j + 1) m * Lambda y := by
          intro y hy
          have hyPrev : neutral (H.state j).active y := by
            refine ⟨?_, ?_⟩
            · intro i hi
              apply hy.1
              intro hiNext
              exact hi (hnewSub hiNext)
            · have heq := sum_eq_of_subset_zero (H.state j).active (H.state (j + 1)).active
                hnewSub (fun i => y i) (fun i hi hiNot => hy.1 i hiNot)
              exact heq.trans hy.2
          have hsupport : ∀ i ∈ (H.state j).active,
              i ∉ (H.state (j + 1)).active → y i = 0 := by
            intro i hi hnot
            exact hy.1 i hnot
          have hPlainEq : plain j y = ∑ i ∈ (H.state (j + 1)).active, (y i) ^ 2 := by
            exact sum_eq_of_subset_zero (H.state j).active (H.state (j + 1)).active
              hnewSub (fun i => (y i) ^ 2) (fun i hi hnot => by simp [hy.1 i hnot])
          have hDiagRestrict : diag j y =
              ∑ i ∈ (H.state (j + 1)).active, (y i) ^ 2 / (H.r j i).im ^ 2 := by
            exact sum_eq_of_subset_zero (H.state j).active (H.state (j + 1)).active
              hnewSub (fun i => (y i) ^ 2 / (H.r j i).im ^ 2)
                (fun i hi hnot => by simp [hy.1 i hnot])
          have hOldDampOnNew : ∀ i ∈ (H.state (j + 1)).active,
              cP / 2 ≤ (H.r j i).im := by
            intro i hi
            exact (hDampOld i (hnewSub hi)).1
          have hNewDamp : ∀ i ∈ (H.state (j + 1)).active,
              cP / 2 ≤ (H.r (j + 1) i).im := by
            intro i hi
            exact (hDampNext i hi).1
          let oldDiag : ℝ := ∑ i ∈ (H.state (j + 1)).active,
              (y i) ^ 2 / (H.r j i).im ^ 2
          let θ' : ℝ := θ
          have hAffineRaw := H.affineStep j hj0 hjlt y hy
          have hAffine :
              (1 - err j) * (θ' * X j y + (1 - θ') * oldDiag) ≤ X (j + 1) y ∧
              X (j + 1) y ≤ (1 + err j) * (θ' * X j y + (1 - θ') * oldDiag) := by
            simpa [err, θ', oldDiag, X, η] using hAffineRaw
          have hOldX0 : 0 ≤ X j y := by
            exact inverseEnergy_nonneg_of_zero (H.state j).active
              (endpointEnergy (H.state j) (H.r j) (stageScale u j m)) y hEnergyZeroOld
          have hOldDiag0 : 0 ≤ oldDiag := by
            apply Finset.sum_nonneg
            intro i hi
            have hiPos := hOldDampOnNew i hi
            have hden : 0 < (H.r j i).im ^ 2 := sq_pos_of_pos
              (lt_of_lt_of_le (by positivity) hiPos)
            positivity
          have hTarget0 : 0 ≤ θ' * X j y + (1 - θ') * oldDiag := by
            have hθ' : 0 ≤ θ' := hθ0
            have hθone : 0 ≤ 1 - θ' := by linarith [hθ1]
            positivity
          have hTargetLower : θ' * X j y ≤ θ' * X j y + (1 - θ') * oldDiag := by
            have hθone : 0 ≤ 1 - θ' := by linarith [hθ1]
            exact le_add_of_nonneg_right (mul_nonneg hθone hOldDiag0)
          have hOneMinus : 0 ≤ 1 - err j := sub_nonneg.mpr (by linarith [hErrCurrent.2])
          have hAffineLower : (1 - err j) * θ' * X j y ≤ X (j + 1) y := by
            calc
              (1 - err j) * θ' * X j y = (1 - err j) * (θ' * X j y) := by ring
              _ ≤ (1 - err j) * (θ' * X j y + (1 - θ') * oldDiag) :=
                mul_le_mul_of_nonneg_left hTargetLower hOneMinus
              _ ≤ X (j + 1) y := hAffine.1
          have hLambdaNonnegY : 0 ≤ Lambda y := by
            exact inverseEnergy_nonneg_of_zero Finset.univ
              (gradientEnergy (nnGraph d m)) y hGradZero
          have hLowerOld := (hForms y hyPrev).1
          have hQstepScale :
              bAt (j + 1) * Pminus (j + 1) =
                θ' * bAt j * Pminus j * (1 - err j) := by
            rw [hPminusStep]
            dsimp [bAt, θ']
            calc
              stageScale u n₀ m * stageScale u (j + 1) m *
                  (Pminus j * (1 - err j)) =
                stageScale u n₀ m * (θ * stageScale u j m) *
                  (Pminus j * (1 - err j)) := by rw [hθmul]
              _ = θ * (stageScale u n₀ m * stageScale u j m) *
                    Pminus j * (1 - err j) := by ring
          have hCoeff0 : 0 ≤ (1 - err j) * θ' := mul_nonneg hOneMinus hθ0
          have hLowerNew : cL * bAt (j + 1) * Pminus (j + 1) * Lambda y ≤ X (j + 1) y := by
            calc
              cL * bAt (j + 1) * Pminus (j + 1) * Lambda y =
                  cL * (bAt (j + 1) * Pminus (j + 1)) * Lambda y := by ring
              _ = cL * (θ' * bAt j * Pminus j * (1 - err j)) * Lambda y := by
                    rw [hQstepScale]
              _ = (1 - err j) * θ' * (cL * bAt j * Pminus j * Lambda y) := by ring
              _ ≤ (1 - err j) * θ' * X j y :=
                mul_le_mul_of_nonneg_left hLowerOld hCoeff0
              _ ≤ X (j + 1) y := hAffineLower
          have hSnext0 : 0 ≤ plain (j + 1) y := by
            apply Finset.sum_nonneg
            intro i hi
            exact sq_nonneg (y i)
          have hDenInv : ∀ i ∈ (H.state (j + 1)).active,
              1 / (H.r j i).im ^ 2 ≤ 4 / cP ^ 2 := by
            intro i hi
            exact inverse_square_damping cP (H.r j i).im hcP (hOldDampOnNew i hi)
          have hDiagCoarse : oldDiag ≤ A * plain (j + 1) y := by
            dsimp [oldDiag, plain]
            calc
              (∑ i ∈ (H.state (j + 1)).active,
                  (y i) ^ 2 / (H.r j i).im ^ 2) ≤
                ∑ i ∈ (H.state (j + 1)).active, A * (y i) ^ 2 :=
                  Finset.sum_le_sum fun i hi => by
                    have h := mul_le_mul_of_nonneg_left (hDenInv i hi) (sq_nonneg (y i))
                    calc
                      (y i) ^ 2 / (H.r j i).im ^ 2 =
                          (y i) ^ 2 * (1 / (H.r j i).im ^ 2) := by ring
                      _ ≤ (y i) ^ 2 * (4 / cP ^ 2) := h
                      _ = A * (y i) ^ 2 := by dsimp [A]; ring
              _ = A * (∑ i ∈ (H.state (j + 1)).active, (y i) ^ 2) := by rw [Finset.mul_sum]
          have hPlainNextEq : plain (j + 1) y = plain j y := by
            dsimp [plain]
            exact hPlainEq.symm
          let Bcoef : ℝ := θ' * C₀ + (1 - θ') * A
          have hBcoef : Bcoef ≤ C₀ - 3 / 8 := by
            have hGap : 1 ≤ C₀ - A := by dsimp [A]; linarith
            dsimp [Bcoef]
            nlinarith [hθhi, hGap]
          have hEtaAt : stageScale u j m ^ η ≤ stageScale u n₀ m ^ ρ := by
            have htη : stageScale u j m ^ η ≤ stageScale u j m ^ ρ :=
              Real.rpow_le_rpow_of_exponent_ge htjpos htjle hρη
            have hmono : stageScale u j m ^ ρ ≤ stageScale u n₀ m ^ ρ :=
              Real.rpow_le_rpow htjpos.le (stageScale_antitone hu hj0) (le_of_lt hρ)
            exact htη.trans hmono
          have hEcoarse : err j * C₀ ≤ 3 / 16 := by
            dsimp [err]
            calc
              C * stageScale u j m ^ η * C₀ ≤ C * C₀ * stageScale u n₀ m ^ ρ := by
                calc
                  (C * stageScale u j m ^ η) * C₀ =
                      (C * C₀) * stageScale u j m ^ η := by ring
                  _ ≤ (C * C₀) * stageScale u n₀ m ^ ρ :=
                    mul_le_mul_of_nonneg_left hEtaAt (mul_nonneg hCpos.le hC₀pos.le)
              _ ≤ 3 / 16 := le_of_lt hsmallCoarse
          have hB0 : 0 ≤ Bcoef := by
            dsimp [Bcoef]
            positivity
          have hBtoC : Bcoef ≤ C₀ := by linarith [hBcoef]
          have hCoarseCoeff : (1 + err j) * Bcoef ≤ C₀ := by
            calc
              (1 + err j) * Bcoef = Bcoef + err j * Bcoef := by ring
              _ ≤ (C₀ - 3 / 8) + err j * C₀ :=
                add_le_add hBcoef (mul_le_mul_of_nonneg_left hBtoC hErrCurrent.1)
              _ ≤ C₀ := by nlinarith [hEcoarse]
          have hTargetCoarse :
              θ' * X j y + (1 - θ') * oldDiag ≤
                Bcoef * plain j y + CL * Pplus j * θ' * bAt j * Lambda y := by
            have hOldCoarse := (hForms y hyPrev).2.1
            calc
              θ' * X j y + (1 - θ') * oldDiag ≤
                  θ' * (C₀ * plain j y + CL * Pplus j * bAt j * Lambda y) +
                    (1 - θ') * (A * plain (j + 1) y) :=
                add_le_add (mul_le_mul_of_nonneg_left hOldCoarse hθ0)
                  (mul_le_mul_of_nonneg_left hDiagCoarse (by linarith [hθ1]))
              _ = Bcoef * plain j y + CL * Pplus j * θ' * bAt j * Lambda y := by
                rw [hPlainNextEq]
                dsimp [Bcoef]
                ring
          have hCoarseAddEq :
              (1 + err j) * (CL * Pplus j * θ' * bAt j * Lambda y) =
                CL * Pplus (j + 1) * bAt (j + 1) * Lambda y := by
            rw [hPplusStep]
            have hθmul' : θ' * stageScale u j m = stageScale u (j + 1) m := by
              simpa [θ'] using hθmul
            have hScaleProd : θ' * (stageScale u n₀ m * stageScale u j m) =
                stageScale u n₀ m * stageScale u (j + 1) m := by
              calc
                θ' * (stageScale u n₀ m * stageScale u j m) =
                    stageScale u n₀ m * (θ' * stageScale u j m) := by ring
                _ = stageScale u n₀ m * stageScale u (j + 1) m := by rw [hθmul']
            dsimp [bAt]
            calc
              (1 + err j) * (CL * Pplus j * θ' *
                  (stageScale u n₀ m * stageScale u j m) * Lambda y) =
                  CL * (Pplus j * (1 + err j)) *
                    (θ' * (stageScale u n₀ m * stageScale u j m)) * Lambda y := by ring
              _ = CL * (Pplus j * (1 + err j)) *
                    (stageScale u n₀ m * stageScale u (j + 1) m) * Lambda y := by
                rw [hScaleProd]
          have hCoarseNew : X (j + 1) y ≤
              C₀ * plain (j + 1) y + CL * Pplus (j + 1) * bAt (j + 1) * Lambda y := by
            calc
              X (j + 1) y ≤ (1 + err j) *
                  (θ' * X j y + (1 - θ') * oldDiag) := hAffine.2
              _ ≤ (1 + err j) *
                  (Bcoef * plain j y + CL * Pplus j * θ' * bAt j * Lambda y) :=
                mul_le_mul_of_nonneg_left hTargetCoarse (by positivity)
              _ = (1 + err j) * Bcoef * plain (j + 1) y +
                    (1 + err j) * (CL * Pplus j * θ' * bAt j * Lambda y) := by
                rw [hPlainNextEq]
                ring
              _ ≤ C₀ * plain (j + 1) y +
                    (1 + err j) * (CL * Pplus j * θ' * bAt j * Lambda y) :=
                add_le_add (mul_le_mul_of_nonneg_right hCoarseCoeff hSnext0) le_rfl
              _ = C₀ * plain (j + 1) y +
                    CL * Pplus (j + 1) * bAt (j + 1) * Lambda y := by rw [hCoarseAddEq]
          have hDiagOldEq : oldDiag = diag j y := hDiagRestrict.symm
          have hσAt : stageScale u j m ^ σ ≤ stageScale u n₀ m ^ ρ := by
            have htσ : stageScale u j m ^ σ ≤ stageScale u j m ^ ρ :=
              Real.rpow_le_rpow_of_exponent_ge htjpos htjle hρσ
            have hmono : stageScale u j m ^ ρ ≤ stageScale u n₀ m ^ ρ :=
              Real.rpow_le_rpow htjpos.le (stageScale_antitone hu hj0) (le_of_lt hρ)
            exact htσ.trans hmono
          have hErrRel : err j ≤ a / 16 * stageScale u j m ^ κ := by
            have htκ : 0 ≤ stageScale u j m ^ κ := Real.rpow_nonneg htjpos.le κ
            have hρj : stageScale u j m ^ ρ ≤ stageScale u n₀ m ^ ρ :=
              Real.rpow_le_rpow htjpos.le (stageScale_antitone hu hj0) (le_of_lt hρ)
            have hsplit : stageScale u j m ^ η =
                stageScale u j m ^ κ * stageScale u j m ^ ρ := by
              rw [hηeq, Real.rpow_add htjpos]
            calc
              err j = (C * stageScale u j m ^ κ) * stageScale u j m ^ ρ := by
                dsimp [err]
                rw [hsplit]
                ring
              _ ≤ (C * stageScale u j m ^ κ) * stageScale u n₀ m ^ ρ :=
                mul_le_mul_of_nonneg_left hρj (mul_nonneg hCpos.le htκ)
              _ ≤ (a / 16) * stageScale u j m ^ κ := by
                calc
                  (C * stageScale u j m ^ κ) * stageScale u n₀ m ^ ρ =
                      (C * stageScale u n₀ m ^ ρ) * stageScale u j m ^ κ := by ring
                  _ ≤ (a / 16) * stageScale u j m ^ κ :=
                    mul_le_mul_of_nonneg_right (le_of_lt hsmallHigh) htκ
          let v : ℝ := Dvar * stageScale u j m ^ σ
          have hv0 : 0 ≤ v := by dsimp [v]; positivity
          have hvRel : v ≤ a / 16 * stageScale u j m ^ κ := by
            have htκ : 0 ≤ stageScale u j m ^ κ := Real.rpow_nonneg htjpos.le κ
            have hσTail : stageScale u j m ^ (σ - κ) ≤ stageScale u n₀ m ^ ρ := by
              have hfirst : stageScale u j m ^ (σ - κ) ≤ stageScale u j m ^ ρ :=
                Real.rpow_le_rpow_of_exponent_ge htjpos htjle hρσκ
              have hsecond : stageScale u j m ^ ρ ≤ stageScale u n₀ m ^ ρ :=
                Real.rpow_le_rpow htjpos.le (stageScale_antitone hu hj0) (le_of_lt hρ)
              exact hfirst.trans hsecond
            have hsplit : stageScale u j m ^ σ =
                stageScale u j m ^ κ * stageScale u j m ^ (σ - κ) := by
              rw [hσeq, Real.rpow_add htjpos]
              congr 1
              ring
            calc
              v = (Dvar * stageScale u j m ^ κ) *
                    stageScale u j m ^ (σ - κ) := by
                dsimp [v]
                rw [hsplit]
                ring
              _ ≤ (Dvar * stageScale u j m ^ κ) * stageScale u n₀ m ^ ρ :=
                mul_le_mul_of_nonneg_left hσTail (mul_nonneg hDvar.le htκ)
              _ ≤ (a / 16) * stageScale u j m ^ κ := by
                calc
                  (Dvar * stageScale u j m ^ κ) * stageScale u n₀ m ^ ρ =
                      (Dvar * stageScale u n₀ m ^ ρ) * stageScale u j m ^ κ := by ring
                  _ ≤ (a / 16) * stageScale u j m ^ κ :=
                    mul_le_mul_of_nonneg_right (le_of_lt hsmallVar) htκ
          have hσAtOne : stageScale u j m ^ σ ≤ 1 :=
            Real.rpow_le_one htjpos.le htjle hσ.le
          have hDiffIm : ∀ i ∈ (H.state (j + 1)).active,
              |(H.r j i).im - (H.r (j + 1) i).im| ≤ C * stageScale u j m ^ σ := by
            intro i hi
            have hpoint : ‖(H.r (j + 1) - H.r j) i‖ ≤ C * stageScale u j m ^ σ := by
              exact (norm_le_pi_norm (H.r (j + 1) - H.r j) i).trans
                (H.rStep j hj0 hjlt)
            calc
              |(H.r j i).im - (H.r (j + 1) i).im| =
                  |(H.r j i - H.r (j + 1) i).im| := by simp
              _ ≤ ‖H.r j i - H.r (j + 1) i‖ := Complex.abs_im_le_norm _
              _ = ‖H.r (j + 1) i - H.r j i‖ := norm_sub_rev _ _
              _ = ‖(H.r (j + 1) - H.r j) i‖ := rfl
              _ ≤ C * stageScale u j m ^ σ := hpoint
          have hDiagRatio : diag j y ≤ (1 + v) * diag (j + 1) y := by
            rw [hDiagRestrict]
            calc
              (∑ i ∈ (H.state (j + 1)).active,
                  (y i) ^ 2 / (H.r j i).im ^ 2) ≤
                ∑ i ∈ (H.state (j + 1)).active,
                  (1 + v) * ((y i) ^ 2 / (H.r (j + 1) i).im ^ 2) :=
                  Finset.sum_le_sum fun i hi => by
                    have hchange := inverse_square_change cP C (stageScale u j m ^ σ)
                      (H.r j i).im (H.r (j + 1) i).im hcP
                      (hOldDampOnNew i hi) (hNewDamp i hi) (hDiffIm i hi)
                      hCpos.le (Real.rpow_nonneg htjpos.le σ) hσAtOne
                    have hterm := mul_le_mul_of_nonneg_left hchange (sq_nonneg (y i))
                    dsimp [v]
                    calc
                      (y i) ^ 2 / (H.r j i).im ^ 2 =
                          (y i) ^ 2 * (1 / (H.r j i).im ^ 2) := by ring
                      _ ≤ (y i) ^ 2 *
                          ((1 + Dvar * stageScale u j m ^ σ) /
                            (H.r (j + 1) i).im ^ 2) := hterm
                      _ = (1 + Dvar * stageScale u j m ^ σ) *
                          ((y i) ^ 2 / (H.r (j + 1) i).im ^ 2) := by ring
              _ = (1 + v) * diag (j + 1) y := by
                rw [← Finset.mul_sum]
          have hDiagNext0 : 0 ≤ diag (j + 1) y := by
            apply Finset.sum_nonneg
            intro i hi
            have hiDamp := hNewDamp i hi
            have hpos : 0 < (H.r (j + 1) i).im :=
              lt_of_lt_of_le (by positivity) hiDamp
            positivity
          have hTightCoeff := tight_scalar_step a θ (stageScale u j m ^ κ)
            (err j) v (θ ^ κ) ha haHalf hθ0 hθ1 hτ0 hτ1 hErrCurrent.1 hv0
            hErrRel hvRel hmarginθ
          have hOldTight := (hForms y hyPrev).2.2
          have hTargetTight :
              θ' * X j y + (1 - θ') * oldDiag ≤
                (1 + θ' * stageScale u j m ^ κ) * diag j y +
                  CL * Pplus j * θ' * stageScale u j m * Lambda y := by
            rw [hDiagOldEq]
            calc
              θ' * X j y + (1 - θ') * diag j y ≤
                  θ' * ((1 + stageScale u j m ^ κ) * diag j y +
                    CL * Pplus j * stageScale u j m * Lambda y) +
                    (1 - θ') * diag j y :=
                add_le_add (mul_le_mul_of_nonneg_left hOldTight hθ0) le_rfl
              _ = (1 + θ' * stageScale u j m ^ κ) * diag j y +
                    CL * Pplus j * θ' * stageScale u j m * Lambda y := by ring
          have hTargetTight' :
              θ' * X j y + (1 - θ') * oldDiag ≤
                (1 + θ' * stageScale u j m ^ κ) * (1 + v) * diag (j + 1) y +
                  CL * Pplus j * θ' * stageScale u j m * Lambda y := by
            calc
              _ ≤ (1 + θ' * stageScale u j m ^ κ) * diag j y +
                    CL * Pplus j * θ' * stageScale u j m * Lambda y := hTargetTight
              _ ≤ (1 + θ' * stageScale u j m ^ κ) * (1 + v) * diag (j + 1) y +
                    CL * Pplus j * θ' * stageScale u j m * Lambda y := by
                have hcoef : 0 ≤ 1 + θ' * stageScale u j m ^ κ := by positivity
                calc
                  _ ≤ (1 + θ' * stageScale u j m ^ κ) *
                      ((1 + v) * diag (j + 1) y) +
                      CL * Pplus j * θ' * stageScale u j m * Lambda y :=
                    add_le_add (mul_le_mul_of_nonneg_left hDiagRatio hcoef) le_rfl
                  _ = (1 + θ' * stageScale u j m ^ κ) * (1 + v) * diag (j + 1) y +
                      CL * Pplus j * θ' * stageScale u j m * Lambda y := by ring
          have hTightAddEq :
              (1 + err j) * (CL * Pplus j * θ' * stageScale u j m * Lambda y) =
                CL * Pplus (j + 1) * stageScale u (j + 1) m * Lambda y := by
            rw [hPplusStep]
            have hθmul' : θ' * stageScale u j m = stageScale u (j + 1) m := by
              simpa [θ'] using hθmul
            calc
              (1 + err j) * (CL * Pplus j * θ' * stageScale u j m * Lambda y) =
                  CL * (Pplus j * (1 + err j)) * (θ' * stageScale u j m) * Lambda y := by ring
              _ = CL * (Pplus j * (1 + err j)) * stageScale u (j + 1) m * Lambda y := by
                rw [hθmul'] <;> ring_nf
          have hTightNew : X (j + 1) y ≤
              (1 + stageScale u (j + 1) m ^ κ) * diag (j + 1) y +
                CL * Pplus (j + 1) * stageScale u (j + 1) m * Lambda y := by
            calc
              X (j + 1) y ≤ (1 + err j) *
                  (θ' * X j y + (1 - θ') * oldDiag) := hAffine.2
              _ ≤ (1 + err j) *
                  ((1 + θ' * stageScale u j m ^ κ) * (1 + v) * diag (j + 1) y +
                    CL * Pplus j * θ' * stageScale u j m * Lambda y) :=
                mul_le_mul_of_nonneg_left hTargetTight' (by positivity)
              _ = ((1 + err j) * (1 + θ' * stageScale u j m ^ κ) * (1 + v)) *
                    diag (j + 1) y +
                    (1 + err j) * (CL * Pplus j * θ' * stageScale u j m * Lambda y) := by ring
              _ ≤ (1 + (θ') ^ κ * stageScale u j m ^ κ) * diag (j + 1) y +
                    (1 + err j) * (CL * Pplus j * θ' * stageScale u j m * Lambda y) :=
                add_le_add (mul_le_mul_of_nonneg_right hTightCoeff hDiagNext0) le_rfl
              _ = (1 + stageScale u (j + 1) m ^ κ) * diag (j + 1) y +
                    CL * Pplus (j + 1) * stageScale u (j + 1) m * Lambda y := by
                rw [hτnext, hTightAddEq]
          exact ⟨hLowerNew, hCoarseNew, hTightNew⟩
        exact ⟨hcloseNext, hKnext, hsubsetNext, hFormsNext⟩
  have hCoreAt : Core n := by
    rw [← Nat.add_sub_of_le hn₀n]
    exact hCore (n - n₀) (by omega)
  rcases hCoreAt with ⟨hcloseN, hKN, hsubsetN, hFormsN⟩
  have hσN : C * Eσ n ≤ cP / 4 := hσMass n hn₀n hnm
  have hDampN := damping_of_close (H.state n₀).active (H.state n).active
    (H.r n₀) (H.r n) cP CP (C * Eσ n) hcP hCP
    hσN hsubsetN hDampBase hcloseN
  have hηN : C * Eη n ≤ 1 / 12 := hηMass n hn₀n hnm
  have hNormFinal : matrixNorm
      (squareKernel (normalizedInverse (H.state n) (stageScale u n m))) ≤ 1 / 3 := by
    calc
      _ ≤ 1 / 4 + C * Eη n := hKN
      _ ≤ 1 / 4 + 1 / 12 := add_le_add le_rfl hηN
      _ = 1 / 3 := by norm_num
  have hErrSumN : (∑ i ∈ Finset.Ico n₀ n, err i) ≤ 1 / 2 := by
    change (∑ i ∈ Finset.Ico n₀ n, C * stageScale u i m ^ η) ≤ 1 / 2
    rw [← Finset.mul_sum]
    exact (hηMass n hn₀n hnm).trans (by norm_num)
  have hErrNonnegN : ∀ i ∈ Finset.Ico n₀ n, 0 ≤ err i := by
    intro i hi
    dsimp [err]
    exact mul_nonneg hCpos.le (Real.rpow_nonneg (stageScale_pos hu i m).le η)
  have hProductsN := prod_error_factors_bounds (Finset.Ico n₀ n) err hErrNonnegN hErrSumN
  simp only [StageBounds]
  refine ⟨?_, H.rows n hn₀n hnK, hNormFinal, H.kernels n hn₀n hnK,
    H.counts n hn₀n hnK, H.metrics n hn₀n hnK, ?_⟩
  · intro i hi
    have hreset := H.reset n hn₀n hnK i hi
    have hdamp := hDampN i hi
    exact ⟨hreset, hdamp.1, hdamp.2.1, hdamp.2.2⟩
  · intro y hy
    rcases hFormsN y hy with ⟨hlow, hcoarse, htight⟩
    have hLambdaY : 0 ≤ Lambda y :=
      inverseEnergy_nonneg_of_zero Finset.univ (gradientEnergy (nnGraph d m)) y hGradZero
    have hQlow := hProductsN.1
    have hPbounds := hProductsN.2
    have hbAtN : 0 ≤ bAt n := by
      dsimp [bAt]
      exact mul_nonneg (stageScale_pos hu n₀ m).le (stageScale_pos hu n m).le
    have hPupper : Pplus n ≤ 2 := hPbounds.2
    have hLowerScale : cL / 2 * bAt n * Lambda y ≤
        cL * bAt n * Pminus n * Lambda y := by
      have hfac : 0 ≤ cL * bAt n * Lambda y :=
        mul_nonneg (mul_nonneg hcL.le hbAtN) hLambdaY
      calc
        cL / 2 * bAt n * Lambda y = (cL * bAt n * Lambda y) * (1 / 2 : ℝ) := by ring
        _ ≤ (cL * bAt n * Lambda y) * Pminus n :=
          mul_le_mul_of_nonneg_left hQlow hfac
        _ = cL * bAt n * Pminus n * Lambda y := by ring
    have hCoarseAdd : CL * Pplus n * bAt n * Lambda y ≤
        2 * CL * bAt n * Lambda y := by
      have hfac : 0 ≤ CL * bAt n * Lambda y :=
        mul_nonneg (mul_nonneg hCL.le hbAtN) hLambdaY
      calc
        CL * Pplus n * bAt n * Lambda y = Pplus n * (CL * bAt n * Lambda y) := by ring
        _ ≤ 2 * (CL * bAt n * Lambda y) := mul_le_mul_of_nonneg_right hPupper hfac
        _ = 2 * CL * bAt n * Lambda y := by ring
    have hTightAdd : CL * Pplus n * stageScale u n m * Lambda y ≤
        2 * CL * stageScale u n m * Lambda y := by
      have hfac : 0 ≤ CL * stageScale u n m * Lambda y :=
        mul_nonneg (mul_nonneg hCL.le (stageScale_pos hu n m).le) hLambdaY
      calc
        CL * Pplus n * stageScale u n m * Lambda y =
            Pplus n * (CL * stageScale u n m * Lambda y) := by ring
        _ ≤ 2 * (CL * stageScale u n m * Lambda y) :=
          mul_le_mul_of_nonneg_right hPupper hfac
        _ = 2 * CL * stageScale u n m * Lambda y := by ring
    refine ⟨?_, ?_, ?_⟩
    · exact hLowerScale.trans hlow
    · exact hcoarse.trans (add_le_add le_rfl hCoarseAdd)
    · exact htight.trans (add_le_add le_rfl hTightAdd)

end AndersonAC.AgentS78.PrefixInduction
