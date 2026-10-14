import AndersonAC.AgentS78.Construction.TilePhaseRun
import AndersonAC.AgentS78.StageStep
import AndersonAC.AgentS78.Construction.PhysicalIdentity
import AndersonAC.AgentS78.Construction.TileCoverStatement

/-!
# WP10 construction, tile phase: the analytic contracts of (a) and (c)

agent-s78tphase (2026-10-14). Frozen statements for the remaining analytic pieces of the tile
phase (requested in DISPATCH-REQUESTS):

* `SweepSchurStatement` — the duplicated-port sweep identity (04:190–228): deleting every bit
  port of the active sites from the start lift of a damped endpoint `(M, g)` at `t`, with
  scalars `ξ`, leaves on the reserve ports `√θ (M + diag ζ − θt·r)⁻¹` on the active block,
  `ζ_i = √(1 − θ) ξ` the physical increment of site `i`. Pure linear algebra
  (Sherman–Morrison per step). It gives `IsDampedEndpoint` of the post-sweep endpoint once
  the sweep records `M + diag ζ` (INTERFACE-ISSUES 01:13, the `endpoint.M` defect).
* `TileStartStatement C` — the duplicated stage start (04:73–88 Lemma `duplication`,
  05:320–337): from the stage history at `j − 1` the analytic start clauses and validity at
  `k = 0` hold for the start lift (`StartClauses` is the adapter that follows TileGoodCore
  v3).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

open Classical in
/-- **The duplicated-port sweep identity (contract).** -/
def SweepSchurStatement : Prop :=
  ∀ (d m : ℕ) (t θ : ℝ) (x : RunRecord d m) (q : S45.Sequence (Port d m)),
    0 < t → 0 < θ → θ < 1 →
    IsDampedEndpoint x.endpoint x.r t →
    q.wellFormed t (portR θ x.r) →
    q.state 0 = sweepStartLiveState θ x →
    (∀ k < q.length, ∃ i, q.pivot k = some ((i, false) : Port d m)) →
    (∀ p : Port d m, p ∈ (q.state q.length).live ↔ p.1 ∈ x.endpoint.active ∧ p.2 = true) →
    let ζ : Torus d m → ℝ := fun i => ∑ k ∈ Finset.range q.length,
      if q.pivot k = some ((i, false) : Port d m) then Real.sqrt (1 - θ) * q.scalar k else 0
    let B : Matrix x.endpoint.active x.endpoint.active ℂ :=
      (x.endpoint.M + Matrix.diagonal fun i => ((ζ i : ℝ) : ℂ)).submatrix Subtype.val Subtype.val -
        ((θ * t : ℝ) : ℂ) • Matrix.diagonal fun i : x.endpoint.active => x.r i.val
    let G : Matrix x.endpoint.active x.endpoint.active ℂ := fun i k =>
      (q.state q.length).g ((i.val, true) : Port d m) ((k.val, true) : Port d m) /
        (Real.sqrt θ : ℂ)
    B * G = 1 ∧ G * B = 1

/-- **The duplicated stage start (contract, v3; amended 2026-10-14 after agent-s78start's
audit of 01:50:07).** For all stage-bound constants there are `C' ≥ 1` and `t0 > 0` such that
the start lift of a record whose committed endpoint satisfies the stage bounds at `j − 1`, the
damped identity at `t = t_{j−1}` and the physical identity, satisfies the v3 start clauses
(`StartClauses`: on the active-site ports `startV3`, plus `prefix_decay`) with constant `C'`
and is valid at `k = 0`, for every tile plan whose cover of sweep `j` satisfies the plan facts
with `C'`, with the torus gradient energy, `b = t_{n₀} t`, site `Prod.fst` and the physical
port distance. -/
def TileStartStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
  ∃ C' ≥ 1, ∃ t0 > 0, ∀ (m n₀ : ℕ) (u E : ℝ) (P : TilePlan d m) (j : ℕ) (z : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m + 1 →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ z.endpoint z.r →
    IsDampedEndpoint z.endpoint z.r (sweepScale u m j) →
    PhysicalIdentity E z →
    PlanClauses C' P j →
    (P.cover j).cover.energy = gradientEnergy (nnGraph d m) →
    (P.cover j).b = stageScale u n₀ m * sweepScale u m j →
    (P.cover j).cover.site = Prod.fst →
    (P.cover j).dist = pullDist (id : Port d m → Port d m) →
    StartClauses C' P j z.endpoint z.r (sweepStartLiveState (sweepTheta P.u m j) z) ∧
    (sweepStartMap (sweepTheta P.u m j) (sweepScale P.u m j) z).sweep.valid
      (sweepScale P.u m j) (portR (sweepTheta P.u m j) z.r)
      (stageD0 P j (sweepStartMap (sweepTheta P.u m j) (sweepScale P.u m j) z)) 0

end AndersonAC.AgentS78
