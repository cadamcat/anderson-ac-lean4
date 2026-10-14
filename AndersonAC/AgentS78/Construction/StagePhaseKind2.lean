import AndersonAC.AgentS78.Construction.StagePhaseRecOp
import AndersonAC.AgentS78.Construction.StagePhaseDoneProof
import AndersonAC.AgentS78.Construction.StagePhaseHops

/-!
# Kind 2 of the run invariant, conditional only on the analytic DONE statement

agent-s78phase2. `clearOpR_hInv_of_analytic`: for the run's broad damping `(cP, CP)` and a trace
constant `Ctr ≥ 2` there are assembly constants `(CA₀, cA₀, PA₀)` such that for all admissible
`(CA, cA, PA)` there are `N, t₀` with: every clearing index `opIndex j 2 y` of a box with
`n₀ ≥ N`, `n₀ < j`, `t_j < t₀` maps `ClearPhaseR … j (rank y)` into `ClearPhaseR … j (rank y + 1)`
along real local answers. The only open input is `ClearingDoneAnalyticStatement d`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

/-- **Clearing indices keep `ClearPhaseR`, given the analytic DONE statement.** -/
theorem clearOpR_hInv_of_analytic {d : ℕ} (hd : 3 ≤ d) (hA : ClearingDoneAnalyticStatement d)
    (cP CP : ℝ) (hcP : 0 < cP) (hCP : cP ≤ CP) (Ctr : ℝ) (hCtr : 2 ≤ Ctr) :
    ∃ CA₀ cA₀ PA₀ : ℝ, 1 ≤ CA₀ ∧ 0 < cA₀ ∧ 0 ≤ PA₀ ∧
    ∀ CA cA PA : ℝ, CA₀ ≤ CA → 0 < cA → cA ≤ cA₀ → PA₀ ≤ PA →
    ∃ N : ℕ, ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {m : ℕ} (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
      {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C : ℝ} (j : ℕ) (y : Torus d m),
      N ≤ n₀ → n₀ < j → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → stageScale u j m < t₀ →
      stageScale u j m ≤ 1 / 4 →
      ∀ x : RunRecord d m, ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j (siteRank d m y).val x →
      ∀ (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P)),
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) (opIndex d m j 2 y)).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
          (opIndex d m j 2 y)) x k' ω) = false) →
      ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j ((siteRank d m y).val + 1)
        ((scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) (opIndex d m j 2 y)).exit
          (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
            (opIndex d m j 2 y)) x k ω)) := by
  obtain ⟨CA₀, cA₀, PA₀, h1, h2, h3, hmain⟩ :=
    clearingDone_of_analytic hd (clearingDoneHops_proof d) hA cP CP hcP hCP Ctr hCtr
  refine ⟨CA₀, cA₀, PA₀, h1, h2, h3, fun CA cA PA hCA hcA hcA' hPA => ?_⟩
  obtain ⟨N, t₀, ht₀, hdone⟩ := hmain CA cA PA hCA hcA hcA' hPA
  refine ⟨N, t₀, ht₀, ?_⟩
  intro m P ts₀ cl₀ n₀ u E ρ C j y hN hj hu ht ht4 x hx k ω hrun
  exact clearOpR_hInv (fun n₀ j u E ρ C y x D => hdone n₀ j u E ρ C y x D)
    (clearingDoneHops_proof d) hCtr P ts₀ cl₀ j y hN hj hu ht ht4 x hx k ω hrun

end AndersonAC.AgentS78
