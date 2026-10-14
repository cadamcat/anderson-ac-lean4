import AndersonAC.AgentS78.Construction.TileStartAlgebraicProof
import AndersonAC.AgentS78.Construction.TileStartDecay

/-!
# WP10 tile phase: the duplicated stage start, v3 proposal (live ports, corrected hypotheses)

agent-s78start (2026-10-14). Proposed replacement of `TileStartStatement` (false as frozen,
INTERFACE-ISSUES agent-s78start): the stage-start clauses on the live ports
(`StartAlgebraicLive ∧ StartDecayLive`) and validity at `k = 0`, under the stage bounds at
`j − 1` plus the damped identity, the physical identity and the cover facts
(`b`, energy, site, distance). `tileStartV3_of_decay` proves it from the decay contract
`TileStartDecayStatement`; the algebraic part is proved (`tileStartAlgebraic_proof`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- **The duplicated stage start, v3 proposal.** -/
def TileStartV3Statement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
  ∃ C' ≥ 1, ∃ t0 > 0, ∀ (m n₀ : ℕ) (u E : ℝ) (P : TilePlan d m) (j : ℕ) (z : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m + 1 →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ z.endpoint z.r →
    IsDampedEndpoint z.endpoint z.r (sweepScale u m j) →
    PhysicalIdentity E z →
    (P.cover j).cover.energy = gradientEnergy (nnGraph d m) →
    (P.cover j).b = stageScale u n₀ m * sweepScale u m j →
    (P.cover j).cover.site = Prod.fst →
    (P.cover j).dist = pullDist (id : Port d m → Port d m) →
    StartAlgebraicLive C' P j (sweepStartLiveState (sweepTheta P.u m j) z) z.r ∧
    StartDecayLive C' P j (sweepStartLiveState (sweepTheta P.u m j) z) z.r ∧
    (sweepStartMap (sweepTheta P.u m j) (sweepScale P.u m j) z).sweep.valid
      (sweepScale P.u m j) (portR (sweepTheta P.u m j) z.r)
      (stageD0 P j (sweepStartMap (sweepTheta P.u m j) (sweepScale P.u m j) z)) 0

/-- **v3 from the decay contract** (the algebraic part is `tileStartAlgebraic_proof`). -/
theorem tileStartV3_of_decay (hd : 3 ≤ d) (hdec : TileStartDecayStatement d) :
    TileStartV3Statement d := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀
  obtain ⟨Ca, hCa, ta, hta, ha⟩ := tileStartAlgebraic_proof d hd cP CP cL CL C₀ hcP hCP hcL hCL hC₀
  obtain ⟨Cd, hCd, td, htd, hdc⟩ := hdec cP CP cL CL C₀ hcP hCP hcL hCL hC₀
  refine ⟨max Ca Cd, le_max_of_le_left hCa, min ta td, lt_min hta htd, ?_⟩
  intro m n₀ u E P j z hn₀ hu' hu hj0 hj ht hSB hD hphys hen hb hsite hdist
  have hta' : sweepScale u m j < ta := ht.trans_le (min_le_left _ _)
  have htd' : sweepScale u m j < td := ht.trans_le (min_le_right _ _)
  obtain ⟨h1, h3⟩ := ha (max Ca Cd) (le_max_left _ _) m n₀ u P j z hn₀ hu' hu hj0 hj hta' hSB hD
    hen hb hsite
  exact ⟨h1, hdc (max Ca Cd) (le_max_right _ _) m n₀ u E P j z hn₀ hu' hu hj0 hj htd' hSB hD
    hphys hdist, h3⟩

end AndersonAC.AgentS78
