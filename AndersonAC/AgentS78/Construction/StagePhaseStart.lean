import AndersonAC.AgentS78.Construction.StagePhase

/-!
# The clearing-phase invariant at the sweep end (hand-over from the tile phase)

`ClearPhaseData.ofSweep`: the post-sweep endpoint `sw` of stage `j` with its single-state
assembly facts (07-assembly.tex:950–975, eq. assembly-initial-data: lag, rows, comparison,
damping, Combes–Thomas decay, terminal metric, active count), the sweep conclusions
`SweepFacts` relative to the previous boundary endpoint and its history give the
clearing-phase data with `k = 0` (the empty prefix of committed clearings), with
`Ds = t_j^{−8−ν}`. Also used unchanged for the non-clearing stages `⌊m/2⌋ < j ≤ m`.
`embedded_of_stage`: `400 t_j^{−8−ν} < L = 4^{20m}` for `j ≤ m`, `m ≥ 2`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem nu_le_one (d : ℕ) : nu d ≤ 1 := by
  unfold nu delta
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · have : (1 : ℝ) ≤ d := by exact_mod_cast h
    rw [div_le_one (by positivity)]
    nlinarith

theorem nu_nonneg (d : ℕ) : 0 ≤ nu d := by
  unfold nu delta; positivity

/-- The halo radius of a stage fits in the torus. -/
theorem embedded_of_stage {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {j : ℕ} (hj : j ≤ m)
    (hm : 2 ≤ m) : 400 * stageScale u j m ^ (-8 - nu d) < (OAI.Anderson.sideLength m : ℝ) := by
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
  have hfin : 400 * (4 : ℝ) ^ (9 * m + 9) < (4 : ℝ) ^ (20 * m) := by
    have h1 : (4 : ℝ) ^ (20 * m) = (4 : ℝ) ^ (9 * m + 9) * (4 : ℝ) ^ (11 * m - 9) := by
      rw [← pow_add]; congr 1; omega
    have h2 : (4 : ℝ) ^ (5 : ℕ) ≤ (4 : ℝ) ^ (11 * m - 9) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [h1]
    have h3 : (0 : ℝ) < (4 : ℝ) ^ (9 * m + 9) := by positivity
    nlinarith
  have hL : (OAI.Anderson.sideLength m : ℝ) = (4 : ℝ) ^ (20 * m) := by
    simp [OAI.Anderson.sideLength]
  rw [hL]
  calc 400 * stageScale u j m ^ (-8 - nu d) ≤ 400 * (4 : ℝ) ^ (9 * m + 9) := by
        have := hstep1.trans (hstep2.le.trans hstep3)
        linarith
    _ < _ := hfin

/-- **Clearing-phase data at the sweep end** (`k = 0`). -/
def ClearPhaseData.ofSweep {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} {j : ℕ}
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hn₀ : 1 ≤ n₀) (hnj : n₀ < j) (hj : j ≤ m) (hm : 2 ≤ m)
    (hCA : 1 ≤ CA) (hcA : 0 < cA) (hPA : 0 ≤ PA)
    (old sw : Endpoint (Torus d m)) (rOld : Torus d m → ℂ)
    (hist : BoundaryHist n₀ u E ρ C (j - 1) old rOld)
    (sweep : SweepFacts C (stageScale u (j - 1) m) (stageScale u j m) old sw rOld)
    (damping : ∀ i, cA ≤ (rOld i).im ∧ (rOld i).im ≤ CA ∧ ‖rOld i‖ ≤ CA)
    (physical : IsDampedEndpoint sw rOld (stageScale u j m))
    (activeCount : Fintype.card (Torus d m) ≤ 2 * sw.active.card)
    (metric : ∀ y z, physicalDistance d m y z / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ sw.active) y z)
    (resolventDecay : ∀ i i', ‖normalizedInverse sw (stageScale u j m) i i'‖ ≤
      CA / Real.sqrt (stageScale u j m) * Real.exp (-cA * stageScale u j m *
        max (physicalDistance d m i i' / 2 - stageScale u j m ^ (-1.03 : ℝ)) 0))
    (initialComparison : ∀ f,
      cA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f ≤
        endpointEnergy sw rOld (stageScale u j m) f ∧
      endpointEnergy sw rOld (stageScale u j m) f ≤
        CA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f)
    (initialRows : ∀ i, rowFour (normalizedInverse sw (stageScale u j m)) i ≤
      0.7 * stageScale u j m ^ (1 + delta))
    (initialLag : ∀ i ∈ sw.active, ‖sw.g i i - rOld i‖ ≤ CA * stageScale u j m ^ (0.42 * delta))
    (x : RunRecord d m) (hx : x.endpoint = sw) (hr : x.r = rOld) :
    ClearPhaseData n₀ u E ρ C CA cA PA j x where
  old := old
  rOld := rOld
  k := 0
  I :=
    { state := fun _ => sw
      anchor := fun a => a.elim0
      C := CA
      c := cA
      P := PA
      Ds := stageScale u j m ^ (-8 - nu d)
      positive := by
        have ht := stageScale_pos' hu j m
        have hm1 : 1 ≤ m := by omega
        have hj1 : stageScale u j m ≤ 1 := stageScale_le_one hu (by omega) hm1
        have hn1 : stageScale u n₀ m ≤ 1 := stageScale_le_one hu hn₀ hm1
        have hb := stageScale_pos' hu n₀ m
        refine ⟨ht, hj1, mul_pos hb ht, ?_, hcA, hCA, hPA⟩
        nlinarith
      scaleRadius := ⟨le_rfl, by
        have := Real.rpow_pos_of_pos (stageScale_pos' hu j m) (-8 - nu d)
        nlinarith⟩
      embedded := embedded_of_stage hu hj hm
      damping := damping
      physical := fun _ => physical
      nested := fun a => a.elim0
      activeCount := fun _ => activeCount
      distinct := fun a => a.elim0
      removedNonempty := fun a => a.elim0
      removedSize := fun a => a.elim0
      removedLocal := fun a => a.elim0
      haloOverlap := fun y => by
        have h0 : overlap (fun a : Fin 0 => cube d m (Fin.elim0 a) (200 * stageScale u j m ^
            (-8 - nu d))) y = 0 := by
          unfold overlap; simp
        rw [h0]
        have := Real.rpow_pos_of_pos (stageScale_pos' hu j m) (-(d : ℝ) * nu d)
        push_cast
        nlinarith
      metric := fun _ => metric
      resolventDecay := fun _ => resolventDecay
      initialComparison := initialComparison
      initialRows := initialRows
      initialLag := initialLag
      entryChange := fun a => a.elim0
      rowChange := fun a => a.elim0
      totalChange := fun a => a.elim0
      decay := fun a => a.elim0 }
  hist := hist
  sweep := sweep
  last := hx.symm
  frozen := hr
  constC := rfl
  constc := rfl
  constP := rfl

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The active count and the terminal metric at the end of a stage history. -/
theorem BoundaryHist.count_metric {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C : ℝ} {k : ℕ}
    {s : Endpoint (Torus d m)} {rk : Torus d m → ℂ} (hist : BoundaryHist n₀ u E ρ C k s rk)
    (hk : n₀ ≤ k) :
    Fintype.card (Torus d m) ≤ 2 * s.active.card ∧
    ∀ y z, physicalDistance d m y z / 2 - stageScale u k m ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ s.active) y z := by
  obtain ⟨state, r, -, -, hk1, -, -, -, -, -, -, hco, hme⟩ := hist
  rw [← hk1]
  exact ⟨hco k hk le_rfl, hme k hk le_rfl⟩

/-- **Clearing-phase data at the sweep end**, with the active count and the terminal metric
inherited from the previous boundary (the sweep keeps the active set and the scale
decreases). -/
def ClearPhaseData.ofSweep' {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} {j : ℕ}
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hn₀ : 1 ≤ n₀) (hnj : n₀ < j) (hj : j ≤ m) (hm : 2 ≤ m)
    (hCA : 1 ≤ CA) (hcA : 0 < cA) (hPA : 0 ≤ PA)
    (old sw : Endpoint (Torus d m)) (rOld : Torus d m → ℂ)
    (hist : BoundaryHist n₀ u E ρ C (j - 1) old rOld)
    (sweep : SweepFacts C (stageScale u (j - 1) m) (stageScale u j m) old sw rOld)
    (damping : ∀ i, cA ≤ (rOld i).im ∧ (rOld i).im ≤ CA ∧ ‖rOld i‖ ≤ CA)
    (physical : IsDampedEndpoint sw rOld (stageScale u j m))
    (resolventDecay : ∀ i i', ‖normalizedInverse sw (stageScale u j m) i i'‖ ≤
      CA / Real.sqrt (stageScale u j m) * Real.exp (-cA * stageScale u j m *
        max (physicalDistance d m i i' / 2 - stageScale u j m ^ (-1.03 : ℝ)) 0))
    (initialComparison : ∀ f,
      cA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f ≤
        endpointEnergy sw rOld (stageScale u j m) f ∧
      endpointEnergy sw rOld (stageScale u j m) f ≤
        CA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f)
    (initialRows : ∀ i, rowFour (normalizedInverse sw (stageScale u j m)) i ≤
      0.7 * stageScale u j m ^ (1 + delta))
    (initialLag : ∀ i ∈ sw.active, ‖sw.g i i - rOld i‖ ≤ CA * stageScale u j m ^ (0.42 * delta))
    (x : RunRecord d m) (hx : x.endpoint = sw) (hr : x.r = rOld) :
    ClearPhaseData n₀ u E ρ C CA cA PA j x :=
  ClearPhaseData.ofSweep hu hn₀ hnj hj hm hCA hcA hPA old sw rOld hist sweep damping physical
    (by rw [sweep.active]; exact (hist.count_metric (by omega)).1)
    (fun y z => by
      rw [sweep.active]
      refine le_trans ?_ ((hist.count_metric (by omega)).2 y z)
      have h1 : stageScale u j m ≤ stageScale u (j - 1) m := stageScale_anti hu m (by omega)
      have h2 : stageScale u (j - 1) m ^ (-1.03 : ℝ) ≤ stageScale u j m ^ (-1.03 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (stageScale_pos' hu j m) h1 (by norm_num)
      linarith)
    resolventDecay initialComparison initialRows initialLag x hx hr

end AndersonAC.AgentS78
