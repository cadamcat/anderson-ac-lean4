import AndersonAC.AgentS78.Construction.TileCore

/-!
# WP10 construction, C4a core, piece A3b: no failure without a budget crossing

agent-s78trial (2026-10-14). Frozen statement `TileTransferStatement` (05:844–860 with
Lemma `local-transfer` 05:538–564 and Lemma `local-prospective` 05:155–239): at a running slot
whose prefix was reached by accepted slot steps, if the candidate update keeps the local
budgets of the trial (`S45.localBudget` of its records since the trial start), then its update
denominator is nonzero and the whole included prefix stays valid. Together with A3a
(TileCoreA3.lean, a budget violation is a monitored crossing) it gives
`TileFailCrossingStatement`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

/-- **A3b (frozen).** -/
def TileTransferStatement (d : ℕ) (C : ℝ) : Prop :=
  ∃ t0 > 0, ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x → sweepScale P.u m j < t0 →
    ∀ (k : ℕ) (ω : RandomSources (Torus d m) M) (q : S45.Sequence (Port d m)),
      k < slotCount P j T → slotSeq P j T M x k ω = some q →
      activeIn P j T x (tileSlot P j T M k ω) →
      ((tileSlot P j T M k ω, false) : Port d m) ∈ (q.state q.length).live →
      let c := candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω)
      let t := sweepScale P.u m j
      let r := portR (sweepTheta P.u m j) x.r
      let K := Finset.Ico x.sweep.length c.length
      S45.localBudget (P.cover j).cover T (c.Jrecord t r K) (c.Lrecord t r K)
        (c.lagRecord t r K) (c.rowRecord t r Finset.univ K) (c.rowRecord t r S45.reserves K) →
      stepDen t r (q.state q.length) (tileSlot P j T M k ω, false) (tileXi P j T M x k ω) ≠ 0 ∧
        c.valid t r (stageD0 P j x) c.length

end AndersonAC.AgentS78
