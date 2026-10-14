import AndersonAC.AgentS78.Construction.PrefixSteps
import AndersonAC.AgentS78.Construction.Record
import AndersonAC.AgentS78.Construction.PrefixInductionInitial

/-!
# WP10 construction, C5b: the stage-boundary invariant of the run

`BoundaryInv n₀ u E ρ C k x`: the committed endpoint and damping of `x` end a stage history
from the §3 initial endpoint (damping `ρ`) up to stage `k`: one `StageStep` per stage `n < k`
(sweep, committed clearings, reset: `stage_step_of_sections`) and the boundary facts at each
stage `n ≤ k`. This is the hypothesis list of `prefix_of_steps`. With the frozen prefix
induction `PrefixStageBoundsStatement` (luna-s78prefix) it gives the stage bounds of the
committed endpoint (`stageBounds_of_boundaryInv`), the standing input of the next sweep.
The stage-end block must extend the history by one stage (a separate package).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- **A stage history** from the §3 initial endpoint ending at `(s, rk)` at stage `k`. -/
def BoundaryHist (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (k : ℕ) (s : Endpoint (Torus d m))
    (rk : Torus d m → ℂ) : Prop :=
  ∃ (state : ℕ → Endpoint (Torus d m)) (r : ℕ → Torus d m → ℂ),
    state n₀ = initialEndpoint d m E (stageScale u n₀ m) ρ ∧ r n₀ = (fun _ => ρ) ∧
    state k = s ∧ r k = rk ∧
    (∀ n, n₀ ≤ n → n < k → Nonempty (StageStep d m C (stageScale u n m)
      (stageScale u (n + 1) m) (state n) (state (n + 1)) (r n) (r (n + 1)))) ∧
    (∀ n, n₀ ≤ n → n ≤ k → IsDampedEndpoint (state n) (r n) (stageScale u n m)) ∧
    (∀ n, n₀ ≤ n → n ≤ k → ∀ i ∈ (state n).active, (state n).g i i = r n i) ∧
    (∀ n, n₀ ≤ n → n ≤ k → ∀ i,
      rowFour (normalizedInverse (state n) (stageScale u n m)) i ≤ stageScale u n m ^ (1 + delta)) ∧
    (∀ n, n₀ ≤ n → n ≤ k →
      constantKernel (state n).active (endpointEnergy (state n) (r n) (stageScale u n m))) ∧
    (∀ n, n₀ ≤ n → n ≤ k → Fintype.card (Torus d m) ≤ 2 * (state n).active.card) ∧
    (∀ n, n₀ ≤ n → n ≤ k → ∀ y z,
      physicalDistance d m y z / 2 - stageScale u n m ^ (-1.03 : ℝ) ≤
        terminalDistance (nnGraph d m) (Finset.univ \ (state n).active) y z)

/-- **The stage-boundary invariant** at stage `k`: the committed endpoint ends a history. -/
def BoundaryInv (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (k : ℕ) (x : RunRecord d m) : Prop :=
  BoundaryHist n₀ u E ρ C k x.endpoint x.r

/-- **Stage bounds at a stage boundary of the run.** -/
theorem stageBounds_of_boundaryInv {e₂ C : ℝ} (hC : 1 ≤ C)
    (hpre : PrefixStageBoundsStatement d e₂ (8 * C + 4)) :
    ∃ (N : ℕ) (cP CP cL CL C₀ : ℝ), 0 < cP ∧ cP ≤ CP ∧ 0 < cL ∧ 0 < CL ∧ 0 < C₀ ∧
      ∀ n₀ : ℕ, N ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m → ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      ∃ ρ : ℝ → ℂ, ContinuousOn ρ (OAI.Anderson.energyWindow d e₂) ∧
      ∀ E ∈ OAI.Anderson.energyWindow d e₂,
        IsDampedEndpoint (initialEndpoint d m E (stageScale u n₀ m) (ρ E)) (fun _ => ρ E)
          (stageScale u n₀ m) ∧
        ∀ k : ℕ, n₀ ≤ k → k ≤ m → ∀ x : RunRecord d m,
          1 ≤ n₀ → C * stageScale u n₀ m ^ (0.10 * delta) ≤ 1 / 4 →
          BoundaryInv n₀ u E (ρ E) C k x →
          StageBounds d m n₀ k u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀ x.endpoint x.r := by
  obtain ⟨N, cP, CP, cL, CL, C₀, h1, h2, h3, h4, h5, hmain⟩ := hpre
  refine ⟨N, cP, CP, cL, CL, C₀, h1, h2, h3, h4, h5, fun n₀ hN m hm u hu => ?_⟩
  obtain ⟨ρ, hρ, hE⟩ := hmain n₀ hN m hm u hu
  refine ⟨ρ, hρ, fun E hEw => ⟨(hE E hEw).1, ?_⟩⟩
  intro k hk hkm x hn₀ hsmall hinv
  obtain ⟨state, r, h0, hr0, hk1, hk2, hstep, hphys, hreset, hrows, hker, hcount, hmet⟩ := hinv
  have := (hE E hEw).2 k hkm (prefix_of_steps hu hC hn₀ hkm state r hsmall
    (fun n h1 h2 => (hstep n h1 h2).some) hphys hreset hrows hker hcount hmet) h0 hr0 k hk le_rfl
  rw [← hk1, ← hk2]
  exact this

/-- `stageBounds_of_boundaryInv` with the prefix induction proved (luna-s78prefix). -/
theorem stageBounds_of_boundaryInv' {e₂ C : ℝ} (hd : 3 ≤ d) (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hC : 1 ≤ C) :
    type_of% (stageBounds_of_boundaryInv (d := d) hC (prefixStageBounds_proof d hd e₂ he₂
      (8 * C + 4) (by linarith))) :=
  stageBounds_of_boundaryInv (d := d) hC (prefixStageBounds_proof d hd e₂ he₂ (8 * C + 4)
    (by linarith))

end AndersonAC.AgentS78
