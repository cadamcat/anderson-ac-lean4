import AndersonAC.AgentS78.Construction.StagePhaseTraceRun
import AndersonAC.AgentS78.Construction.StagePhaseStartDs

/-!
# Clearing-phase package: damping drift and the scale-radius window

agent-s78phase2 (DISPATCH 04:08:18, `clearingPhasePackage_of`).

* `broad_of_hist`: along a stage history the damping moves by at most
  `Σ t_{n+1}^{.35δ}` on **every** site (`StageStep.r_close`), so all sites keep
  `cP/2 ≤ Im r`, `‖r‖ ≤ 2 CP` once `n₀` is large (the initial damping `ρ` satisfies
  `cP ≤ Im ρ`, `‖ρ‖ ≤ CP` by the stage bounds at `n₀`, all sites active).
* `ds_window`: `Ds = 2^9 t_j^{-8-ν}` lies in `[2 clearRadius, 2^25 clearRadius]` for `j ≤ m`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem stageScale_le_two_pow {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {n : ℕ} (hn : n ≤ m) :
    stageScale u n m ≤ 2 * (1 / 4 : ℝ) ^ n := by
  unfold stageScale
  have h1 : u / (4 : ℝ) ^ n ≤ (1 / 4 : ℝ) ^ n := by
    rw [one_div_pow, div_eq_mul_inv, one_div]; exact mul_le_of_le_one_left (by positivity) hu.2
  have h2 : u / (4 : ℝ) ^ m ≤ (1 / 4 : ℝ) ^ n := by
    refine le_trans ?_ (h1)
    exact div_le_div_of_nonneg_left (by linarith [hu.1]) (by positivity)
      (pow_le_pow_right₀ (by norm_num) hn)
  linarith

/-- The sum of the damping steps of a history from `n₀` is uniformly small. -/
theorem drift_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (m n₀ k : ℕ) (u : ℝ), u ∈ Set.Ioc (1 / 4 : ℝ) 1 → N ≤ n₀ → k ≤ m →
      (∑ n ∈ Finset.Ico n₀ k, stageScale u (n + 1) m ^ (0.35 * delta)) ≤ ε := by
  set a : ℝ := 0.35 * delta with ha
  have ha0 : 0 < a := by rw [ha]; norm_num [delta]
  set q : ℝ := (1 / 4 : ℝ) ^ a with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha0
  have hC : 0 < (2 : ℝ) ^ a / (1 - q) := div_pos (by positivity) (by linarith)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hq1
  refine ⟨N, fun m n₀ k u hu hN0 hkm => ?_⟩
  have hterm : ∀ n ∈ Finset.Ico n₀ k, stageScale u (n + 1) m ^ a ≤ (2 : ℝ) ^ a * q ^ (n + 1) := by
    intro n hn
    have hn' : n + 1 ≤ m := by have := (Finset.mem_Ico.mp hn).2; omega
    have hpos := stageScale_pos' hu (n + 1) m
    calc stageScale u (n + 1) m ^ a ≤ (2 * (1 / 4 : ℝ) ^ (n + 1)) ^ a :=
          Real.rpow_le_rpow hpos.le (stageScale_le_two_pow hu hn') ha0.le
      _ = (2 : ℝ) ^ a * q ^ (n + 1) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), hq]
          congr 1
          rw [← Real.rpow_natCast ((1 / 4 : ℝ)) (n + 1),
            ← Real.rpow_natCast ((1 / 4 : ℝ) ^ a) (n + 1), ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num), mul_comm]
  calc (∑ n ∈ Finset.Ico n₀ k, stageScale u (n + 1) m ^ a)
      ≤ ∑ n ∈ Finset.Ico n₀ k, (2 : ℝ) ^ a * q ^ (n + 1) := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ a * q * ∑ n ∈ Finset.Ico n₀ k, q ^ n := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ (2 : ℝ) ^ a * q * (q ^ n₀ / (1 - q)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) (by positivity)
    _ ≤ (2 : ℝ) ^ a * (q ^ N / (1 - q)) := by
        have h1 : q ^ n₀ ≤ q ^ N := pow_le_pow_of_le_one hq0 hq1.le hN0
        have h2 : (2 : ℝ) ^ a * q * (q ^ n₀ / (1 - q)) ≤ (2 : ℝ) ^ a * (q ^ n₀ / (1 - q)) := by
          have : 0 ≤ (2 : ℝ) ^ a * (q ^ n₀ / (1 - q)) := by
            have : 0 < 1 - q := by linarith
            positivity
          nlinarith
        refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact div_le_div_of_nonneg_right h1 (by linarith)
    _ ≤ ε := by
        have h3 : q ^ N < ε / ((2 : ℝ) ^ a / (1 - q)) := hN
        have h4 : 0 < 1 - q := by linarith
        rw [lt_div_iff₀ hC] at h3
        have : (2 : ℝ) ^ a * (q ^ N / (1 - q)) = q ^ N * ((2 : ℝ) ^ a / (1 - q)) := by ring
        linarith

/-- **Damping on every site along a history.** -/
theorem broad_of_hist {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ} {k : ℕ} {s : Endpoint (Torus d m)}
    {rk : Torus d m → ℂ} (hist : BoundaryHist n₀ u E ρ Cb k s rk) (hk : n₀ ≤ k) (ε : ℝ)
    (hsum : (∑ n ∈ Finset.Ico n₀ k, stageScale u (n + 1) m ^ (0.35 * delta)) ≤ ε) :
    ∀ i, ‖rk i - ρ‖ ≤ ε := by
  obtain ⟨state, r, h0, hr0, hk1, hk2, hst, -⟩ := hist
  have key : ∀ k', n₀ ≤ k' → k' ≤ k → ∀ i, ‖r k' i - ρ‖ ≤
      ∑ n ∈ Finset.Ico n₀ k', stageScale u (n + 1) m ^ (0.35 * delta) := by
    intro k' hk' hk'k
    induction k', hk' using Nat.le_induction with
    | base => intro i; rw [hr0]; simp
    | succ k' hk' ih =>
      intro i
      obtain ⟨S⟩ := hst k' hk' (by omega)
      have hc := S.r_close
      have hi : ‖r (k' + 1) i - r k' i‖ ≤ stageScale u (k' + 1) m ^ (0.35 * delta) := by
        have := norm_le_pi_norm (r (k' + 1) - r k') i
        simp only [Pi.sub_apply] at this
        exact this.trans hc
      rw [Finset.sum_Ico_succ_top hk']
      calc ‖r (k' + 1) i - ρ‖ = ‖(r (k' + 1) i - r k' i) + (r k' i - ρ)‖ := by ring_nf
        _ ≤ ‖r (k' + 1) i - r k' i‖ + ‖r k' i - ρ‖ := norm_add_le _ _
        _ ≤ _ := by linarith [ih (by omega) i]
  intro i
  rw [← hk2]
  exact (key k hk le_rfl i).trans hsum

/-- The initial damping satisfies the stage bounds of the history's initial stage. -/
theorem rho_bounds_of_hist {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ} {k : ℕ} {s : Endpoint (Torus d m)}
    {rk : Torus d m → ℂ} (hist : BoundaryHist n₀ u E ρ Cb k s rk) (hk : n₀ ≤ k) (hkm : k ≤ m)
    {cP CP cL CL C₀ : ℝ}
    (hSBh : ∀ k s rk, n₀ ≤ k → k ≤ m → BoundaryHist n₀ u E ρ Cb k s rk →
      StageBounds d m n₀ k u cP CP cL CL C₀ s rk) :
    cP ≤ ρ.im ∧ ‖ρ‖ ≤ CP := by
  obtain ⟨state, r, h0, hr0, hk1, hk2, hst, hph, hre, hro, hke, hco, hme⟩ := hist
  have h0' : BoundaryHist n₀ u E ρ Cb n₀ (initialEndpoint d m E (stageScale u n₀ m) ρ)
      (fun _ => ρ) :=
    ⟨state, r, h0, hr0, h0, hr0, fun n h1 h2 => absurd h2 (by omega),
      fun n h1 h2 => hph n h1 (by omega), fun n h1 h2 => hre n h1 (by omega),
      fun n h1 h2 => hro n h1 (by omega), fun n h1 h2 => hke n h1 (by omega),
      fun n h1 h2 => hco n h1 (by omega), fun n h1 h2 => hme n h1 (by omega)⟩
  have hSB := hSBh n₀ _ _ le_rfl (hk.trans hkm) h0'
  obtain ⟨-, h1, -, h3⟩ := hSB.1 (fun _ => 0) (Finset.mem_univ _)
  exact ⟨h1, h3⟩

/-- **Broad damping on every site** from a history, the stage bounds and small drift. -/
theorem broad_all_of_hist {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ} {k : ℕ} {s : Endpoint (Torus d m)}
    {rk : Torus d m → ℂ} (hist : BoundaryHist n₀ u E ρ Cb k s rk) (hk : n₀ ≤ k) (hkm : k ≤ m)
    {cP CP cL CL C₀ : ℝ} (hcP : 0 < cP)
    (hSBh : ∀ k s rk, n₀ ≤ k → k ≤ m → BoundaryHist n₀ u E ρ Cb k s rk →
      StageBounds d m n₀ k u cP CP cL CL C₀ s rk)
    (hsum : (∑ n ∈ Finset.Ico n₀ k, stageScale u (n + 1) m ^ (0.35 * delta)) ≤ cP / 2) :
    ∀ i, cP / 2 ≤ (rk i).im ∧ ‖rk i‖ ≤ CP + cP / 2 := by
  obtain ⟨hρ1, hρ2⟩ := rho_bounds_of_hist hist hk hkm hSBh
  have hd := broad_of_hist hist hk (cP / 2) hsum
  intro i
  have h1 := hd i
  have him : |(rk i - ρ).im| ≤ cP / 2 := (Complex.abs_im_le_norm _).trans h1
  rw [Complex.sub_im] at him
  refine ⟨by linarith [(abs_le.mp him).1], ?_⟩
  calc ‖rk i‖ = ‖(rk i - ρ) + ρ‖ := by ring_nf
    _ ≤ ‖rk i - ρ‖ + ‖ρ‖ := norm_add_le _ _
    _ ≤ CP + cP / 2 := by linarith

/-- **The scale-radius window** for `Ds = 2^9 t_j^{-8-ν}`. -/
theorem ds_window {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {j : ℕ} (hj : j ≤ m) :
    2 * clearRadius d m j u ≤ 512 * stageScale u j m ^ (-8 - nu d) ∧
      512 * stageScale u j m ^ (-8 - nu d) ≤ 2 ^ 25 * clearRadius d m j u := by
  set t := stageScale u j m with ht
  have htp : 0 < t := stageScale_pos' hu j m
  have hsplit : t ^ (-8 - nu d) = t ^ (-nu d) * (t ^ (8 : ℕ))⁻¹ := by
    rw [show (-8 - nu d) = -nu d + (-(8 : ℝ)) by ring, Real.rpow_add htp]
    congr 1
    rw [Real.rpow_neg htp.le]
    norm_cast
  have hR : separationRadius j = ((4 : ℝ) ^ j) ^ (8 : ℕ) := by
    unfold separationRadius; rw [← pow_mul, mul_comm]
  have hν : 0 < t ^ (-nu d) := Real.rpow_pos_of_pos htp _
  -- t · 4^j ∈ (1/4, 2]
  have h4 : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
  have hup : t * (4 : ℝ) ^ j ≤ 2 := by
    have := stageScale_le_two_pow (m := m) hu hj
    rw [ht]
    calc stageScale u j m * (4 : ℝ) ^ j ≤ 2 * (1 / 4 : ℝ) ^ j * (4 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right this h4.le
      _ = 2 := by rw [mul_assoc, ← mul_pow]; norm_num
  have hlo : 1 / 4 ≤ t * (4 : ℝ) ^ j := by
    rw [ht]; unfold stageScale
    have : u / (4 : ℝ) ^ j * (4 : ℝ) ^ j = u := by field_simp
    have h2 : 0 ≤ u / (4 : ℝ) ^ m * (4 : ℝ) ^ j := by
      have : 0 < u := by linarith [hu.1]
      positivity
    nlinarith [hu.1]
  have hx0 : 0 < t * (4 : ℝ) ^ j := by positivity
  unfold clearRadius
  rw [← ht, hsplit, hR]
  have e1 : ((4 : ℝ) ^ j) ^ (8 : ℕ) = (t * (4 : ℝ) ^ j) ^ (8 : ℕ) * (t ^ (8 : ℕ))⁻¹ := by
    rw [mul_pow, mul_comm (t ^ 8), mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  rw [e1]
  have hti : 0 < (t ^ (8 : ℕ))⁻¹ := by positivity
  have hp8 : (t * (4 : ℝ) ^ j) ^ (8 : ℕ) ≤ 2 ^ 8 := pow_le_pow_left₀ hx0.le hup 8
  have hq8 : (1 / 4 : ℝ) ^ (8 : ℕ) ≤ (t * (4 : ℝ) ^ j) ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) hlo 8
  constructor
  · have : 2 * (t ^ (-nu d) * ((t * (4 : ℝ) ^ j) ^ (8 : ℕ) * (t ^ (8 : ℕ))⁻¹)) ≤
        2 * (t ^ (-nu d) * (2 ^ 8 * (t ^ (8 : ℕ))⁻¹)) := by gcongr
    refine this.trans (le_of_eq ?_); ring
  · have : 2 ^ 25 * (t ^ (-nu d) * ((1 / 4 : ℝ) ^ (8 : ℕ) * (t ^ (8 : ℕ))⁻¹)) ≤
        2 ^ 25 * (t ^ (-nu d) * ((t * (4 : ℝ) ^ j) ^ (8 : ℕ) * (t ^ (8 : ℕ))⁻¹)) := by gcongr
    refine le_trans (le_of_eq ?_) this; ring

/-- The halo of `Ds = 2^9 t_j^{-8-ν}` fits in the torus for `j ≤ m`, `2 ≤ m`. -/
theorem ds_embedded {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {j : ℕ} (hj : j ≤ m) (hm : 2 ≤ m) :
    400 * (512 * stageScale u j m ^ (-8 - nu d)) < (OAI.Anderson.sideLength m : ℝ) := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  set a : ℝ := (4 : ℝ) ^ (-((j : ℝ) + 1)) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos h4 _
  have hta : a ≤ stageScale u j m := by
    have hu0 : 1 / 4 < u := hu.1
    have h1 : a = (1 / 4) / (4 : ℝ) ^ j := by
      rw [ha, Real.rpow_neg h4.le, Real.rpow_add h4, Real.rpow_one, Real.rpow_natCast]
      field_simp
    rw [h1]
    unfold stageScale
    have : (1 / 4) / (4 : ℝ) ^ j ≤ u / (4 : ℝ) ^ j :=
      div_le_div_of_nonneg_right hu0.le (by positivity)
    have : 0 ≤ u / (4 : ℝ) ^ m := div_nonneg (by linarith) (by positivity)
    linarith
  have hneg : -8 - nu d ≤ 0 := by linarith [nu_nonneg d]
  have hstep1 : stageScale u j m ^ (-8 - nu d) ≤ a ^ (-8 - nu d) :=
    Real.rpow_le_rpow_of_nonpos hapos hta hneg
  have hstep2 : a ^ (-8 - nu d) = (4 : ℝ) ^ (((j : ℝ) + 1) * (8 + nu d)) := by
    rw [ha, ← Real.rpow_mul h4.le]; congr 1; ring
  have hexp : ((j : ℝ) + 1) * (8 + nu d) ≤ ((9 * m + 9 : ℕ) : ℝ) := by
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj
    have := nu_le_one d
    have := nu_nonneg d
    push_cast
    nlinarith
  have hstep3 : (4 : ℝ) ^ (((j : ℝ) + 1) * (8 + nu d)) ≤ (4 : ℝ) ^ (9 * m + 9) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hfin : 400 * (512 * (4 : ℝ) ^ (9 * m + 9)) < (4 : ℝ) ^ (20 * m) := by
    have h1 : (4 : ℝ) ^ (20 * m) = (4 : ℝ) ^ (9 * m + 9) * (4 : ℝ) ^ (11 * m - 9) := by
      rw [← pow_add]; congr 1; omega
    have h2 : (4 : ℝ) ^ (13 : ℕ) ≤ (4 : ℝ) ^ (11 * m - 9) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [h1]
    have h3 : (0 : ℝ) < (4 : ℝ) ^ (9 * m + 9) := by positivity
    nlinarith
  have hL : (OAI.Anderson.sideLength m : ℝ) = (4 : ℝ) ^ (20 * m) := by
    simp [OAI.Anderson.sideLength]
  rw [hL]
  calc 400 * (512 * stageScale u j m ^ (-8 - nu d)) ≤ 400 * (512 * (4 : ℝ) ^ (9 * m + 9)) := by
        have := hstep1.trans (hstep2.le.trans hstep3)
        linarith
    _ < _ := hfin

end AndersonAC.AgentS78
