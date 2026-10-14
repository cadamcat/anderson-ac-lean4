import AndersonAC.AgentS6Cap.Energy
import AndersonAC.AgentS6.RowBias

/-! Scalar energy envelopes for a single monitored row. -/

noncomputable section
open scoped BigOperators

namespace AndersonAC.AgentS6

open AndersonAC.S6

private theorem heatLimit_upper {t : ℝ} (ht : 0 < t) :
    (heatLimit t : ℝ) ≤ t ^ (-1 - eh) := by
  unfold heatLimit
  exact Nat.floor_le (Real.rpow_nonneg ht.le _)

theorem heatError_sq {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t * entryBudget t) ^ 2 = t ^ (1 + (84 / 100) * delta) := by
  rw [mul_pow, Real.sq_sqrt ht.le, entryBudget, ← Real.rpow_natCast,
    ← Real.rpow_mul ht.le]
  calc
    _ = t ^ (1 : ℝ) * t ^ ((42 / 100) * delta * 2) := by simp
    _ = t ^ (1 + (42 / 100) * delta * 2) :=
      (Real.rpow_add ht 1 ((42 / 100) * delta * 2)).symm
    _ = t ^ (1 + (84 / 100) * delta) := by congr 1 <;> ring

private theorem heatError_mass_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (N : ℕ) (hN : (N : ℝ) ≤ heatLimit t) :
    (N : ℝ) * (Real.sqrt t * entryBudget t) ^ 2 ≤ t ^ ((27 / 100) * delta) := by
  have hN' : (N : ℝ) ≤ t ^ (-1 - eh) := (hN.trans (heatLimit_upper ht))
  have hpow : t ^ (-1 - eh) * t ^ (1 + (84 / 100) * delta) =
      t ^ ((84 / 100) * delta - eh) := by
    rw [(Real.rpow_add ht (-1 - eh) (1 + (84 / 100) * delta)).symm]
    congr 1
    ring
  have hexp : (27 / 100) * delta ≤ (84 / 100) * delta - eh := by
    norm_num [delta, eh]
  calc
    (N : ℝ) * (Real.sqrt t * entryBudget t) ^ 2 ≤
        t ^ (-1 - eh) * t ^ (1 + (84 / 100) * delta) := by
          rw [heatError_sq ht]
          exact mul_le_mul_of_nonneg_right hN' (Real.rpow_nonneg ht.le _)
    _ = t ^ ((84 / 100) * delta - eh) := hpow
    _ ≤ t ^ ((27 / 100) * delta) :=
      AndersonAC.AgentS6.rpow_anti ht ht1 hexp

private theorem initial_pivot_mass_small
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ht1 : t ≤ 1)
    (ω : Ω) (i : Fin n)
    (hstart : fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) :
    ∑ k ∈ Finset.range (q.stop ω),
      ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 ≤ t ^ ((27 / 100) * delta) := by
  have hN : (q.stop ω : ℝ) ≤ t ^ (-1 - eh) := by
    calc
      (q.stop ω : ℝ) ≤ heatLimit t := by exact_mod_cast q.finite_stop ω
      _ ≤ t ^ (-1 - eh) := heatLimit_upper ht
  have hprod : (q.stop ω : ℝ) * fourthRow (scaledInverse t (g0 ω)) i ≤
      t ^ (delta - eh) := by
    have hrow0 : 0 ≤ fourthRow (scaledInverse t (g0 ω)) i := by
      unfold fourthRow
      positivity
    have hprod' : (q.stop ω : ℝ) * fourthRow (scaledInverse t (g0 ω)) i ≤
        (4 / 5) * (t ^ (-1 - eh) * t ^ (1 + delta)) := by
      rw [fourthCap] at hstart
      calc
        _ ≤ t ^ (-1 - eh) * ((4 / 5) * t ^ (1 + delta)) := by
          exact mul_le_mul hN hstart hrow0 (by positivity)
        _ = _ := by ring
    have heq : t ^ (-1 - eh) * t ^ (1 + delta) = t ^ (delta - eh) := by
      rw [(Real.rpow_add ht (-1 - eh) (1 + delta)).symm]
      congr 1
      ring
    calc
      _ ≤ (4 / 5) * (t ^ (-1 - eh) * t ^ (1 + delta)) := hprod'
      _ = (4 / 5) * t ^ (delta - eh) := by rw [heq]
      _ ≤ t ^ (delta - eh) := by
        have hp : 0 ≤ t ^ (delta - eh) := Real.rpow_nonneg ht.le _
        nlinarith
  have hroot : Real.sqrt ((q.stop ω : ℝ) *
      fourthRow (scaledInverse t (g0 ω)) i) ≤ t ^ ((delta - eh) / 2) := by
    calc
      _ ≤ Real.sqrt (t ^ (delta - eh)) := Real.sqrt_le_sqrt hprod
      _ = t ^ ((delta - eh) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
        congr 1
        ring
  have hexp : (27 / 100) * delta ≤ (delta - eh) / 2 := by
    norm_num [delta, eh]
  calc
    _ ≤ Real.sqrt ((q.stop ω : ℝ) * fourthRow (scaledInverse t (g0 ω)) i) :=
      initial_pivot_row_energy_bound q ω i
    _ ≤ t ^ ((delta - eh) / 2) := hroot
    _ ≤ t ^ ((27 / 100) * delta) :=
      AndersonAC.AgentS6.rpow_anti ht ht1 hexp

theorem running_entry_energy_small
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ht1 : t ≤ 1)
    (ω : Ω) (i : Fin n)
    (hstart : fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) :
    ∑ k ∈ Finset.range (q.stop ω),
      (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
        (Real.sqrt t * entryBudget t) ^ 2) ≤ 2 * t ^ ((27 / 100) * delta) := by
  have hu := initial_pivot_mass_small q ht ht1 ω i hstart
  have he := heatError_mass_small ht ht1 (q.stop ω) (by exact_mod_cast q.finite_stop ω)
  calc
    _ = (∑ k ∈ Finset.range (q.stop ω),
          ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2) +
          (q.stop ω : ℝ) * (Real.sqrt t * entryBudget t) ^ 2 := by
            simp [Finset.sum_add_distrib, Finset.sum_const]
    _ ≤ t ^ ((27 / 100) * delta) + t ^ ((27 / 100) * delta) := add_le_add hu he
    _ = _ := by ring

theorem heatV_norm_small
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t c K : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hK : 0 < K) (ω : Ω) (i : Fin n) (k : ℕ)
    (hrun : k < q.stop ω) (hbroad : BroadBounds c K (r ω))
    (hstart : fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) :
    ‖heatV q k ω i‖ ≤ 2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) := by
  have hN : (q.stop ω : ℝ) ≤ t ^ (-1 - eh) := by
    calc
      (q.stop ω : ℝ) ≤ heatLimit t := by exact_mod_cast q.finite_stop ω
      _ ≤ t ^ (-1 - eh) := heatLimit_upper ht
  have hU : ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 ≤ t ^ (1 / 2 : ℝ) := by
    have hsingle : ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 4 ≤
        fourthRow (scaledInverse t (g0 ω)) i := by
      unfold fourthRow
      exact Finset.single_le_sum
        (f := fun j => ‖scaledInverse t (g0 ω) i j‖ ^ 4) (s := Finset.univ)
        (fun j _ => by positivity) (Finset.mem_univ _)
    have hsingle' : (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2) ^ 2 ≤
        fourthRow (scaledInverse t (g0 ω)) i := by
      convert hsingle using 1 <;> ring
    have hUroot : ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 ≤
        Real.sqrt (fourthRow (scaledInverse t (g0 ω)) i) := by
      apply AndersonAC.AgentS6.le_sqrt_of_sq
      · positivity
      · exact hsingle'
    have hrow : fourthRow (scaledInverse t (g0 ω)) i ≤ t ^ (1 + delta) := by
      calc
        _ ≤ (4 / 5) * fourthCap t := hstart
        _ ≤ t ^ (1 + delta) := by
          unfold fourthCap
          have hp : 0 ≤ t ^ (1 + delta) := Real.rpow_nonneg ht.le _
          nlinarith
    have hroot : Real.sqrt (fourthRow (scaledInverse t (g0 ω)) i) ≤ t ^ (1 / 2 : ℝ) := by
      calc
        _ ≤ Real.sqrt (t ^ (1 + delta)) := Real.sqrt_le_sqrt hrow
        _ = t ^ ((1 + delta) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
          congr 1
          ring
        _ ≤ t ^ (1 / 2 : ℝ) :=
          AndersonAC.AgentS6.rpow_anti ht ht1 (by unfold delta; norm_num)
    exact hUroot.trans hroot
  have herr : (Real.sqrt t * entryBudget t) ^ 2 ≤ t ^ (1 / 2 : ℝ) := by
    rw [heatError_sq ht]
    exact AndersonAC.AgentS6.rpow_anti ht ht1 (by unfold delta; norm_num)
  have hsmall :
      ‖heatV q k ω i‖ ^ 2 ≤ 4 * (K / c) * t ^ (1 / 2 : ℝ) := by
    by_cases hi : i ∈ (q.state k ω).active
    · obtain ⟨hx, -, -, -, -⟩ := q.heat k ω hrun
      have hv := heatV_sq_le_initial_entry q ω k i hrun hi hbroad
      have hs := add_le_add hU herr
      calc
        ‖heatV q k ω i‖ ^ 2 ≤ (K / c) * 2 *
            (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
              (Real.sqrt t * entryBudget t) ^ 2) := hv
        _ ≤ (K / c) * 2 * (2 * t ^ (1 / 2 : ℝ)) := by
          have hs' :
              ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
                (Real.sqrt t * entryBudget t) ^ 2 ≤ 2 * t ^ (1 / 2 : ℝ) := by
            calc
              _ ≤ t ^ (1 / 2 : ℝ) + t ^ (1 / 2 : ℝ) := hs
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_left hs' (by positivity)
        _ = 4 * (K / c) * t ^ (1 / 2 : ℝ) := by ring
    · simp [heatV, hi]
      positivity
  have htarget :
      (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ)) ^ 2 =
        4 * (K / c) * t ^ (1 / 2 : ℝ) := by
    have hrpow : (t ^ (1 / 4 : ℝ)) ^ 2 = t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1
      norm_num
    calc
      (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ)) ^ 2 =
          4 * (Real.sqrt (K / c)) ^ 2 * (t ^ (1 / 4 : ℝ)) ^ 2 := by ring
      _ = 4 * (K / c) * t ^ (1 / 2 : ℝ) := by
        rw [Real.sq_sqrt (div_nonneg hK.le hc.le), hrpow]
  have htarget0 : 0 ≤ 2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) := by positivity
  have hsq : ‖heatV q k ω i‖ ^ 2 ≤
      (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ)) ^ 2 := by rw [htarget]; exact hsmall
  have hroot := AndersonAC.AgentS6.le_sqrt_of_sq
    (‖heatV q k ω i‖) _ (norm_nonneg _) hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg htarget0] at hroot
  exact hroot

theorem running_heatV_energy_small
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t c K : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hK : 1 ≤ K) (ω : Ω) (i : Fin n)
    (hbroad : BroadBounds c K (r ω))
    (hstart : fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) :
    ∑ k ∈ (Finset.range (q.stop ω)).filter (fun k => i ∈ (q.state k ω).active),
      ‖heatV q k ω i‖ ^ 2 ≤ (4 * (K / c)) * t ^ ((27 / 100) * delta) := by
  have hmass := running_entry_energy_small q ht ht1 ω i hstart
  let S : Finset ℕ := (Finset.range (q.stop ω)).filter
    (fun k => i ∈ (q.state k ω).active)
  have hmass' : ∑ k ∈ S,
        (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
          (Real.sqrt t * entryBudget t) ^ 2) ≤ 2 * t ^ ((27 / 100) * delta) := by
    apply le_trans ?_ hmass
    exact Finset.sum_le_sum_of_subset_of_nonneg (by
      dsimp [S]
      exact Finset.filter_subset _ _) (by
      intro k hk hkn
      positivity)
  have hsum : ∑ k ∈ S, ‖heatV q k ω i‖ ^ 2 ≤
      (K / c) * 2 * ∑ k ∈ S,
        (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
          (Real.sqrt t * entryBudget t) ^ 2) := by
    calc
      ∑ k ∈ S, ‖heatV q k ω i‖ ^ 2 ≤
          ∑ k ∈ S, (K / c) * 2 *
            (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
              (Real.sqrt t * entryBudget t) ^ 2) := by
            apply Finset.sum_le_sum
            intro k hk
            have hrun : k < q.stop ω := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
            have hi := (Finset.mem_filter.mp hk).2
            exact heatV_sq_le_initial_entry q ω k i hrun hi hbroad
      _ = (K / c) * 2 * ∑ k ∈ S,
            (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
              (Real.sqrt t * entryBudget t) ^ 2) := by
            rw [← Finset.mul_sum]
  calc
    _ ≤ (K / c) * 2 * ∑ k ∈ S,
        (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
          (Real.sqrt t * entryBudget t) ^ 2) := hsum
    _ ≤ (K / c) * 2 * (2 * t ^ ((27 / 100) * delta)) := by
          gcongr
    _ = (4 * (K / c)) * t ^ ((27 / 100) * delta) := by ring

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.running_entry_energy_small
#print axioms AndersonAC.AgentS6.heatV_norm_small
#print axioms AndersonAC.AgentS6.running_heatV_energy_small
