import AndersonAC.AgentS78.Construction.StagePhaseRec

/-!
# The clearing indices of the schedule on the full clearing-phase invariant. `ClearPhaseR … j r x`: on non-aborted records, clearing-phase data `D` with the
record clauses `ClearRecPos … j r x D.I.anchor`, the scale-radius window
`2 clearRadius ≤ D.I.Ds ≤ Ctr clearRadius`, and the broad damping `cP ≤ Im r`, `‖r‖ ≤ CP`.

`clearOpR_hInv`: the clearing index `opIndex j 2 y` maps `ClearPhaseR … j (rank y)` into
`ClearPhaseR … j (rank y + 1)` along real local answers, given the DONE statements
(`ClearingDoneStatement`, through its per-constant instance, and `ClearingDoneHopsStatement`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-- **The clearing-phase invariant with its record clauses** (scan position `r`). -/
def ClearPhaseR (cP CP Ctr : ℝ) (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C CA cA PA : ℝ) (j r : ℕ)
    (x : RunRecord d m) : Prop :=
  x.aborted = false → ∃ D : ClearPhaseData n₀ u E ρ C CA cA PA j x,
    ClearRecPos Ctr n₀ u j r x D.I.anchor ∧ 2 * clearRadius d m j u ≤ D.I.Ds ∧
    D.I.Ds ≤ Ctr * clearRadius d m j u ∧ ∀ i, cP ≤ (x.r i).im ∧ ‖x.r i‖ ≤ CP

theorem ClearPhaseR.toPhase {cP CP Ctr : ℝ} {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ}
    {j r : ℕ} {x : RunRecord d m} (h : ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j r x) :
    ClearPhase n₀ u E ρ C CA cA PA j x := fun hab => ⟨(h hab).choose⟩

theorem ClearPhaseR.mono {cP CP Ctr : ℝ} {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ}
    {j r r' : ℕ} {x : RunRecord d m} (h : ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j r x)
    (hr : r ≤ r') : ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j r' x := fun hab => by
  obtain ⟨D, h1, h2, h3, h4⟩ := h hab
  exact ⟨D, h1.mono hr, h2, h3, h4⟩

/-- The per-constant instance of `ClearingDoneStatement`. -/
def ClearingDoneInst (d : ℕ) (cP CP Ctr CA cA PA : ℝ) (N : ℕ) (t₀ : ℝ) : Prop :=
  ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (y : Torus d m) (x : RunRecord d m)
    (D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
    N ≤ n₀ → n₀ < j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    stageScale u j m < t₀ →
    2 * clearRadius d m j u ≤ D.I.Ds → D.I.Ds ≤ Ctr * clearRadius d m j u →
    (∀ i, cP ≤ (x.r i).im ∧ ‖x.r i‖ ≤ CP) →
    ClearRec Ctr n₀ u j x D.I.anchor → x.aborted = false →
    ∀ s : RunRecord d m × ClearScratch d m,
      BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s →
      s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
      ClearingStepFacts D.I (clearingDoneExit x s.2).endpoint y

/-- **One clearing attempt keeps `ClearPhaseR`** (block form; the scan position advances). -/
theorem clearingBlockR_keeps {cP CP Ctr CA cA PA : ℝ} {N : ℕ} {t₀ : ℝ}
    (hdone : ClearingDoneInst d cP CP Ctr CA cA PA N t₀) (hhops : ClearingDoneHopsStatement d)
    (hCtr : 2 ≤ Ctr) {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C : ℝ} (j : ℕ) (y : Torus d m)
    (hN : N ≤ n₀) (hj : n₀ < j) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (ht : stageScale u j m < t₀) (ht4 : stageScale u j m ≤ 1 / 4)
    (x : RunRecord d m) (hx : ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j (siteRank d m y).val x)
    (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j ((siteRank d m y).val + 1)
      (clearingExit (d := d) (m := m) j y s) := by
  intro hab'
  have hx1 := (clr_reach n₀ j u y x s hs).1
  have habx : x.aborted = false := by
    have : (clearingExit (d := d) (m := m) j y s).aborted = x.aborted := by
      rcases clr_exit_cases j y s with h | h | h <;> rw [h, hx1] <;> rfl
    rw [← this]; exact hab'
  obtain ⟨D, hpos, hDs1, hDs2, hbroad⟩ := hx habx
  have ht0 : 0 < stageScale u j m := stageScale_pos' hu j m
  rcases clr_exit_trichotomy n₀ j u y x s hs with h | ⟨hne, h⟩ | ⟨-, hsch, hne, hf, hdn, h⟩
  · rw [h]
    exact ⟨D, hpos.mono (Nat.le_succ _), hDs1, hDs2, hbroad⟩
  · rw [h]
    exact ⟨D.transfer _ rfl rfl, clearRecPos_fail n₀ j u Ctr y x D.I.anchor hpos s hs hne,
      hDs1, hDs2, hbroad⟩
  · rw [h]
    have hDx : IsDampedEndpoint x.endpoint x.r (stageScale u j m) := by
      have := D.I.physical (Fin.last D.k)
      rw [D.last, ← D.frozen] at this
      exact this
    have hfacts := hdone n₀ j u E ρ C y x D hN hj hsch hu ht hDs1 hDs2 hbroad hpos.base habx s hs
      hne hf hdn
    exact ⟨D.snoc _ y hfacts rfl,
      clearRecPos_done hhops n₀ j u Ctr hCtr y x D.I.anchor hpos hDx s hs habx hsch hne hf hdn
        hj.le ht0 ht4, hDs1, hDs2, hbroad⟩

/-- **Clearing indices keep `ClearPhaseR`** (schedule form, real local answers). -/
theorem clearOpR_hInv {cP CP Ctr CA cA PA : ℝ} {N : ℕ} {t₀ : ℝ}
    (hdone : ClearingDoneInst d cP CP Ctr CA cA PA N t₀) (hhops : ClearingDoneHopsStatement d)
    (hCtr : 2 ≤ Ctr) (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C : ℝ} (j : ℕ) (y : Torus d m)
    (hN : N ≤ n₀) (hj : n₀ < j) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (ht : stageScale u j m < t₀) (ht4 : stageScale u j m ≤ 1 / 4)
    (x : RunRecord d m) (hx : ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j (siteRank d m y).val x)
    (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hrun : ∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) (opIndex d m j 2 y)).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
        (opIndex d m j 2 y)) x k' ω) = false) :
    ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j ((siteRank d m y).val + 1)
      ((scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) (opIndex d m j 2 y)).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
          (opIndex d m j 2 y)) x k ω)) := by
  have hreach := localState_reach (tileOrderSize P) _ x ω k hrun
  revert hreach
  generalize localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
    (opIndex d m j 2 y)) x k ω = s
  intro hreach
  rw [scheduleBlocks_opIndex _ j 2 y (by norm_num), runOp_two] at hreach ⊢
  split_ifs at hreach ⊢ with h1
  · obtain ⟨s0, hs0, rfl⟩ := blockReach_embed (clrOf n₀ u j y) (clearEmbed ts₀) clearProj
      (fun _ => rfl) x s hreach
    exact clearingBlockR_keeps hdone hhops hCtr j y hN hj hu ht ht4 x hx s0 hs0
  · rw [simpleBlock_exit_reach _ _ x s hreach]; exact hx.mono (Nat.le_succ _)

end AndersonAC.AgentS78
