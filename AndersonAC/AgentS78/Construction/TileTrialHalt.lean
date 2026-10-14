import AndersonAC.AgentS78.Construction.TileTrialFirst

/-!
# the tile block halts almost surely

05:872–905: each retry fails with probability at most `p = exp(−t^{−c}) < 1`, so a tile has
infinitely many failures with probability zero; after the cutoff (`j > ⌊m/2⌋`, including the
final sweep) the block aborts at a first-trial failure and has no retry.

* `tile_steps_le`: a deterministic step count. While the block of tile `T` (with `N = |T|`
  slots) is running at local step `k`, its trial number `a` satisfies
  `k ≤ (2N + 2) a + 2N` (potential `Ψ = (2N+2) a + 2·(entries of π_{j,T,a} revealed) +
  [no exposed site]` grows by at least one per step); after the cutoff `a = 0`.
* `tile_halting_bound`: from the retry estimates `TileRetryStatement`,
  `sourcesLaw (notHalted M (tileBlock P j T) x k) ≤ ε k` with
  `ε k = p^{⌊(k − 2N)/(2N+2)⌋} → 0`, uniformly in the good record `x` (the form consumed by
  `all_blocks_reached`, Reached.lean).
-/

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw)

section Steps
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

/-- Number of slots of the tile. -/
abbrev tileN : ℕ := (tileSites (P.cover j) T).card

/-- Revealed entries of the current trial's order. -/
def haltCurCount (s : RunRecord d m × TileScratch d m) : ℕ :=
  s.2.orderCount (tileOrderIndex j T s.2.attempt)

/-- The step potential. -/
def stepPot (s : RunRecord d m × TileScratch d m) : ℕ :=
  (2 * tileN P j T + 2) * s.2.attempt + 2 * haltCurCount P j T s +
    (if s.2.site = none then 1 else 0)

/-- Step invariant of the running block. -/
def StepInv (s : RunRecord d m × TileScratch d m) : Prop :=
  haltCurCount P j T s ≤ tileN P j T ∧
    (∀ b, s.2.attempt < b → s.2.orderCount (tileOrderIndex j T b) = 0) ∧
    (m / 2 < j → s.2.attempt = 0)

theorem stepPot_le (s : RunRecord d m × TileScratch d m) (h : StepInv P j T s) :
    stepPot P j T s ≤ (2 * tileN P j T + 2) * s.2.attempt + 2 * tileN P j T + 1 := by
  unfold stepPot
  have := h.1
  split_ifs <;> omega

theorem failTrial_cases (s : RunRecord d m × TileScratch d m) :
    (m / 2 < j ∧ (failTrial P j T s).2.halted = true ∧
      (failTrial P j T s).2.attempt = s.2.attempt ∧
      (failTrial P j T s).2.orderCount = s.2.orderCount) ∨
    (¬ m / 2 < j ∧ (failTrial P j T s).2.attempt = s.2.attempt + 1 ∧
      (failTrial P j T s).2.site = none ∧
      (failTrial P j T s).2.orderCount = s.2.orderCount) := by
  by_cases hj : m / 2 < j
  · left; refine ⟨hj, ?_⟩; unfold failTrial; simp [hj]
  · right; refine ⟨hj, ?_⟩; unfold failTrial; simp [hj, trialScratch]

theorem stepInv_of_same (s s' : RunRecord d m × TileScratch d m)
    (ha : s'.2.attempt = s.2.attempt) (ho : s'.2.orderCount = s.2.orderCount)
    (hI : StepInv P j T s) : StepInv P j T s' := by
  refine ⟨?_, ?_, ?_⟩
  · unfold haltCurCount; rw [ha, ho]; exact hI.1
  · intro b hb; rw [ho]; exact hI.2.1 b (by rw [← ha]; exact hb)
  · intro hj; rw [ha]; exact hI.2.2 hj

theorem scalarStep_cases (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ) :
    ((scalarStep P j T s i ζ).2.attempt = s.2.attempt ∧ (scalarStep P j T s i ζ).2.site = none ∧
      (scalarStep P j T s i ζ).2.orderCount = s.2.orderCount ∧
      (scalarStep P j T s i ζ).2.halted = s.2.halted) ∨
    scalarStep P j T s i ζ = failTrial P j T s := by
  unfold scalarStep
  dsimp only
  split_ifs
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr rfl

/-- After a scalar step from an exposed site, the invariant holds and, unless the block
halted, the potential grew. -/
theorem scalarStep_pot (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ)
    (hsite : s.2.site = some i) (hI : StepInv P j T s) :
    StepInv P j T (scalarStep P j T s i ζ) ∧
      ((scalarStep P j T s i ζ).2.halted = false →
        stepPot P j T s + 1 ≤ stepPot P j T (scalarStep P j T s i ζ)) := by
  rcases scalarStep_cases P j T s i ζ with ⟨ha, hs, ho, -⟩ | hf
  · refine ⟨stepInv_of_same P j T s _ ha ho hI, fun _ => ?_⟩
    unfold stepPot haltCurCount; rw [ha, ho, hs, hsite]; simp
  · rw [hf]
    rcases failTrial_cases P j T s with ⟨_, hh, ha, ho⟩ | ⟨hj, ha, hs, ho⟩
    · exact ⟨stepInv_of_same P j T s _ ha ho hI, fun h => absurd (hh.symm.trans h) (by simp)⟩
    · have hz : (failTrial P j T s).2.orderCount (tileOrderIndex j T (s.2.attempt + 1)) = 0 := by
        rw [ho]; exact hI.2.1 _ (Nat.lt_succ_self _)
      refine ⟨⟨?_, ?_, ?_⟩, fun _ => ?_⟩
      · unfold haltCurCount; rw [ha, hz]; exact Nat.zero_le _
      · intro b hb; rw [ho]; exact hI.2.1 b (by omega)
      · intro h; exact absurd h hj
      · have hle := stepPot_le P j T s hI
        unfold stepPot haltCurCount at hle ⊢
        rw [ha, hz, hs, hsite] at *
        simp only [reduceCtorEq, if_false, if_true, add_zero] at hle ⊢
        have := hI.1
        unfold haltCurCount at this
        nlinarith

/-- One running step: the invariant is kept and, unless the block halts, the potential grows
by at least one. -/
theorem tile_step_pot (s : RunRecord d m × TileScratch d m) (a : Answer (Torus d m))
    (hrun : s.2.halted = false) (hI : StepInv P j T s) :
    StepInv P j T ((tileBlock P j T).update s a) ∧
      (((tileBlock P j T).update s a).2.halted = false →
        stepPot P j T s + 1 ≤ stepPot P j T ((tileBlock P j T).update s a)) := by
  rw [tileBlock_update_running P j T s a hrun]
  rcases hsite : s.2.site with _ | i
  · -- no exposed site: reveal the next order entry, or accept
    by_cases hlt : haltCurCount P j T s < tileN P j T
    · have hq : tileQuery P j T s = Query.nextOrder (tileOrderIndex j T s.2.attempt) := by
        unfold tileQuery; rw [hsite]; simp only; unfold haltCurCount at hlt; rw [if_pos hlt]
      rw [hq]
      set oa := tileOrderIndex j T s.2.attempt with hoa
      set r := tileStep P j T (s.1, logQuery (Query.nextOrder oa) s.2) (Query.nextOrder oa) a
        with hr
      have hra : r.2.attempt = s.2.attempt := rfl
      have hro : ∀ o, r.2.orderCount o = s.2.orderCount o + if o = oa then 1 else 0 := by
        intro o; show (logQuery (Query.nextOrder oa) s.2).orderCount o = _
        simp [logQuery, eq_comm]
      have hcur : haltCurCount P j T r = haltCurCount P j T s + 1 := by
        unfold haltCurCount; rw [hra, hro]; simp [hoa]
      refine ⟨⟨?_, ?_, ?_⟩, fun _ => ?_⟩
      · rw [hcur]; omega
      · intro b hb; rw [hra] at hb; rw [hro]
        have hne : tileOrderIndex j T b ≠ oa := by
          intro h; have := (tileOrderIndex_injective h).2.2; omega
        rw [if_neg hne, hI.2.1 b hb]
      · intro hj; rw [hra]; exact hI.2.2 hj
      · unfold stepPot; rw [hcur, hra, hsite]
        split_ifs <;> omega
    · have hq : tileQuery P j T s = Query.decision := by
        unfold tileQuery; rw [hsite]; simp only; unfold haltCurCount at hlt; rw [if_neg hlt]
      rw [hq]
      refine ⟨stepInv_of_same P j T s _ (by simp [tileStep, logQuery, hsite]) ?_ hI, fun h => ?_⟩
      · funext o; simp [tileStep, logQuery, hsite]
      · simp [tileStep, logQuery, hsite] at h
  · -- an exposed site: one scalar query (or a skip)
    have hnot : ∀ o, tileQuery P j T s ≠ Query.nextOrder o := by
      intro o h; unfold tileQuery at h; rw [hsite] at h; simp only at h
      split_ifs at h
    have hlogc : (logQuery (tileQuery P j T s) s.2).orderCount = s.2.orderCount := by
      funext o; simp [logQuery, hnot o]
    set s₀ : RunRecord d m × TileScratch d m := (s.1, logQuery (tileQuery P j T s) s.2) with hs₀
    have hI₀ : StepInv P j T s₀ := stepInv_of_same P j T s s₀ rfl hlogc hI
    have hpot₀ : stepPot P j T s₀ = stepPot P j T s := by
      have e1 : s₀.2.attempt = s.2.attempt := rfl
      have e2 : s₀.2.orderCount = s.2.orderCount := hlogc
      have e3 : s₀.2.site = s.2.site := rfl
      unfold stepPot haltCurCount; rw [e1, e2, e3]
    have hsite₀ : s₀.2.site = some i := hsite
    rcases hqc : tileQuery P j T s with ⟨i', h⟩ | k | ⟨i', h⟩ | o | _
    · simp only [tileStep, hsite₀]
      have := scalarStep_pot P j T s₀ i (tileIncrement P j (Query.trueDigit i' h) a) hsite₀ hI₀
      rw [hpot₀] at this; exact this
    · simp only [tileStep, hsite₀]
      have := scalarStep_pot P j T s₀ i (tileIncrement P j (Query.auxiliary k) a) hsite₀ hI₀
      rw [hpot₀] at this; exact this
    · simp only [tileStep, hsite₀]
      have := scalarStep_pot P j T s₀ i (tileIncrement P j (Query.trueSuffix i' h) a) hsite₀ hI₀
      rw [hpot₀] at this; exact this
    · exact absurd hqc (hnot o)
    · simp only [tileStep, hsite₀]
      refine ⟨stepInv_of_same P j T s₀ _ rfl rfl hI₀, fun _ => ?_⟩
      rw [← hpot₀]; unfold stepPot haltCurCount; rw [hsite₀]; simp

/-- **Deterministic step count.** While the block is running at local step `k`, its trial
number `a` satisfies `k ≤ (2N+2) a + 2N`; after the cutoff, `a = 0`. -/
theorem tile_steps_le (M : ℕ → ℕ) (x : RunRecord d m) (ω : RandomSources (Torus d m) M)
    (k : ℕ) (hrun : ∀ k' ≤ k, (localState M (tileBlock P j T) x k' ω).2.halted = false) :
    k ≤ (2 * tileN P j T + 2) * (localState M (tileBlock P j T) x k ω).2.attempt +
        2 * tileN P j T ∧
      (m / 2 < j → (localState M (tileBlock P j T) x k ω).2.attempt = 0) := by
  have key : ∀ k, (∀ k' ≤ k, (localState M (tileBlock P j T) x k' ω).2.halted = false) →
      StepInv P j T (localState M (tileBlock P j T) x k ω) ∧
        k + 1 ≤ stepPot P j T (localState M (tileBlock P j T) x k ω) := by
    intro k
    induction k with
    | zero =>
      intro h0
      have h := h0 0 le_rfl
      rw [localState_zero] at h ⊢
      by_cases hab : x.aborted = true
      · simp [tileBlock, hab, initScratch] at h
      · have hab' : x.aborted = false := by simpa using hab
        simp only [tileBlock, hab', Bool.false_eq_true, if_false]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp [haltCurCount, stepPot, initScratch]
    | succ k ih =>
      intro hk
      obtain ⟨hI, hP⟩ := ih fun k' hk' => hk k' (Nat.le_succ_of_le hk')
      have step := fun ans => tile_step_pot P j T (localState M (tileBlock P j T) x k ω) ans
        (hk k (Nat.le_succ k)) hI
      have hk1 := hk (k + 1) (le_refl _)
      rw [localState_succ] at hk1 ⊢
      refine ⟨(step _).1, ?_⟩
      have h2 := (step _).2 hk1
      omega
  obtain ⟨hI, hP⟩ := key k hrun
  have hle := stepPot_le P j T _ hI
  exact ⟨by omega, hI.2.2⟩

end Steps

/-- An aborted record enters a halted block. -/
theorem notHalted_aborted {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hab : x.aborted = true) (k : ℕ) : notHalted M (tileBlock P j T) x k = ∅ := by
  ext ω
  simp only [notHalted, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
  refine ⟨0, Nat.zero_le _, ?_⟩
  simp [localState_zero, tileBlock, hab, initScratch]

/-- **block reachability (tile): the tile block halts.** For each `C ≥ 1`, given the retry estimates
`TileRetryStatement d C`, there is `N` such that for every box with `n₀ ≥ N`,
`u ∈ (1/4, 1]`, plan, sweep index `n₀ < j ≤ m + 1`, tile and order sizes, there is
`ε → 0` (independent of the record) with
`sourcesLaw (notHalted M (tileBlock P j T) x k) ≤ ε k` for every good record `x`. -/
theorem tile_halting_bound (d : ℕ) (C : ℝ) (hcore : TileRetryStatement d C) :
    ∃ N : ℕ, ∀ n₀ ≥ N, ∀ (m : ℕ) (u : ℝ), u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ (P : TilePlan d m), P.n₀ = n₀ → P.u = u →
      ∀ j, n₀ < j → j ≤ m + 1 → ∀ (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ),
      TileOrderSizes P j T M →
      ∃ ε : ℕ → ℝ, (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ x ∈ TileGood C P j T, ∀ k,
          sourcesLaw (Torus d m) M (notHalted M (tileBlock P j T) x k) ≤
            ENNReal.ofReal (ε k) := by
  obtain ⟨c, hc, t0, ht0, hcore⟩ := hcore
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < t0 / 8)
    (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨max N₁ 1, ?_⟩
  intro n₀ hn₀ m u hu P hPn hPu j hj hjm T M hM
  have hu' : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 := hPu ▸ hu
  have htpos := sweepScale_pos_first (lt_trans (by norm_num) hu'.1) m j
  have htle := sweepScale_le hu' (by omega : 0 < j) hjm
  have hjN : N₁ ≤ j := by have := le_max_left N₁ 1; omega
  have hsmall : sweepScale P.u m j < t0 := by
    have h4 : (4 : ℝ) ^ N₁ ≤ (4 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hjN
    have hq : (1 / 4 : ℝ) ^ N₁ = 1 / (4 : ℝ) ^ N₁ := by rw [one_div_pow]
    rw [hq] at hN₁
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ N₁ := by positivity
    have : 8 / (4 : ℝ) ^ j ≤ 8 / (4 : ℝ) ^ N₁ := by
      apply div_le_div_of_nonneg_left (by norm_num) h4pos h4
    have h8 : 8 / (4 : ℝ) ^ N₁ < t0 := by
      rw [div_lt_iff₀ h4pos]; rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 8), div_mul_eq_mul_div,
        one_mul, div_lt_iff₀ h4pos] at hN₁; linarith
    linarith
  set p : ℝ := Real.exp (-S45.power (sweepScale P.u m j) (-c)) with hp
  have hp0 : 0 ≤ p := (Real.exp_pos _).le
  have hp1 : p < 1 := by
    have hpos : 0 < S45.power (sweepScale P.u m j) (-c) := by
      unfold S45.power; exact Real.rpow_pos_of_pos htpos _
    rw [hp, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  set N := tileN P j T with hN
  set K : ℕ → ℕ := fun k => (k - 2 * N) / (2 * N + 2) with hK
  refine ⟨fun k => p ^ K k, fun k => pow_nonneg hp0 _, ?_, ?_⟩
  · have hKt : Tendsto K atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b * (2 * N + 2) + 2 * N, fun k hk => ?_⟩
      simp only [hK]
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hp0 hp1).comp hKt
  · intro x hx k
    by_cases hab : x.aborted = true
    · rw [notHalted_aborted P j T M x hab]; simp
    have hab' : x.aborted = false := by simpa using hab
    -- not halted at step k ⇒ trial number at least K k
    have hsub : notHalted M (tileBlock P j T) x k ⊆ reachedAttempt P j T M x (K k) := by
      intro ω hω
      have hs := (tile_steps_le P j T M x ω k hω).1
      rw [← hN] at hs
      refine ⟨k, ?_⟩
      show (k - 2 * N) / (2 * N + 2) ≤ _
      exact Nat.div_le_of_le_mul (by omega)
    by_cases hcut : j ≤ m / 2
    · calc sourcesLaw (Torus d m) M (notHalted M (tileBlock P j T) x k)
          ≤ sourcesLaw (Torus d m) M (reachedAttempt P j T M x (K k)) := measure_mono hsub
        _ ≤ ENNReal.ofReal (p ^ K k) :=
          hcore m P j T M x hu' (hPn ▸ hj) hcut hM hab' (hx hab') hsmall (K k)
    · -- after the cutoff there is no retry
      have hcut' : m / 2 < j := by omega
      rcases Nat.eq_zero_or_pos (K k) with h0 | hpos
      · simp only [h0, pow_zero, ENNReal.ofReal_one]; exact prob_le_one
      · have hempty : notHalted M (tileBlock P j T) x k = ∅ := by
          ext ω
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hω
          have h1 := tile_steps_le P j T M x ω k hω
          have ha := h1.2 hcut'
          have hk : k ≤ 2 * N := by have := h1.1; rw [ha, ← hN] at this; simpa using this
          have : K k = 0 := by
            simp only [hK]; rw [Nat.sub_eq_zero_of_le hk, Nat.zero_div]
          omega
        rw [hempty]; simp

end AndersonAC.AgentS78
