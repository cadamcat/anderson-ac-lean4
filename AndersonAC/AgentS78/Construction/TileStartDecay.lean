import AndersonAC.AgentS78.Construction.TileStartAlgebraic
import AndersonAC.AgentS78.Construction.PhysicalIdentity

/-!
# WP10 tile phase: the decay clauses of the duplicated stage start (contract, v3 proposal)

agent-s78start (2026-10-14). The three decay clauses of `StartClauses` (`start_decay`,
`start_far_decay`, `prefix_decay`), stated on the live ports. They are Combes–Thomas bounds
(05:62–100, Lemma `locality`; 05:458–462 for the prefixes) and need the locality of the endpoint
matrix: `PhysicalIdentity E z` (02-state:231–247, the real part of `M` on the active set is the
terminal Schur complement of the nearest-neighbour `H − E + installed`), and the cover distance
`pullDist id` (physical distance of the sites). Not derivable from `StageBounds` alone
(INTERFACE-ISSUES agent-s78start (4)). Requested as a separate package.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- **Decay clauses of the duplicated stage start on the live ports** (v3 proposal). -/
structure StartDecayLive (C : ℝ) (P : TilePlan d m) (j : ℕ) (a : S45.LiveState (Port d m))
    (r : Torus d m → ℂ) : Prop where
  start_decay : ∀ p q : a.live,
    ‖(liveStartState P j a r).h (sweepScale P.u m j) p q‖ ≤
      C / Real.sqrt (sweepScale P.u m j) *
        Real.exp (-(sweepScale P.u m j) ^ 3 * (P.cover j).dist p.1 q.1 / C)
  start_far_decay : ∀ p q : a.live, C * S45.power (sweepScale P.u m j) (-2) < (P.cover j).dist p.1 q.1 →
    ‖(liveStartState P j a r).h (sweepScale P.u m j) p q‖ ≤
      C / Real.sqrt (sweepScale P.u m j) *
        Real.exp (-(sweepScale P.u m j) * (P.cover j).dist p.1 q.1 / C)
  prefix_decay : ∀ (q : S45.Sequence (Port d m)),
    q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) r) →
    q.state 0 = a →
    (∀ k < q.length, ∀ y, q.pivot k = some y → y.2 = false) →
    ∀ k ≤ q.length,
      q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) r)
        ((startState P j a r).D (sweepScale P.u m j)) k →
      (∀ p q' : (q.state k).live,
        ‖((q.state k).state (portR (sweepTheta P.u m j) r)).h (sweepScale P.u m j) p q'‖ ≤
          C / Real.sqrt (sweepScale P.u m j) *
            Real.exp (-(sweepScale P.u m j) ^ 3 * (P.cover j).dist p.1 q'.1 / C)) ∧
      (∀ p q' : (q.state k).live,
        C * S45.power (sweepScale P.u m j) (-2) < (P.cover j).dist p.1 q'.1 →
        ‖((q.state k).state (portR (sweepTheta P.u m j) r)).h (sweepScale P.u m j) p q'‖ ≤
          C / Real.sqrt (sweepScale P.u m j) *
            Real.exp (-(sweepScale P.u m j) * (P.cover j).dist p.1 q'.1 / C))

/-- **Decay contract (v3 proposal)**: for all constants `C ≥ C'` (uniform), the start lift of a
record with stage bounds at `j − 1`, the damped identity and the physical identity satisfies
the live decay clauses in the physical distance of the cover. -/
def TileStartDecayStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
  ∃ C' ≥ 1, ∃ t0 > 0, ∀ C ≥ C', ∀ (m n₀ : ℕ) (u E : ℝ) (P : TilePlan d m) (j : ℕ)
    (z : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m + 1 →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ z.endpoint z.r →
    IsDampedEndpoint z.endpoint z.r (sweepScale u m j) →
    PhysicalIdentity E z →
    (P.cover j).dist = pullDist (id : Port d m → Port d m) →
    StartDecayLive C P j (sweepStartLiveState (sweepTheta P.u m j) z) z.r

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-! ## Sub-contracts of the decay clauses (DISPATCH, agent-s78start) -/

/-- The physical damping factor `ϑ_i` at a prefix (04:46–55): `θ` once the bit port of `i` is
deleted, `1` before. -/
noncomputable def prefixVartheta {d m : ℕ} (θ : ℝ) (L : Finset (Port d m)) (i : Torus d m) : ℝ :=
  haveI := Classical.dec
  if ((i, false) : Port d m) ∈ L then 1 else θ

/-- **(P1) The prefix Schur identity** (04:46–80, eq:sweep-physical-prefix): along a
well-formed bit-pivot sequence from the start lift of a damped endpoint, every prefix state is
the port lift of the inverse of `M_A + diag ζ − t diag(ϑ r)` for some real `ζ` (the inserted
increments). This is the invariant of `sweepSchur_proof` (lane/agent-s78schur 009e745),
stated at every prefix. -/
def PrefixPhysStatement : Prop :=
  ∀ (d m : ℕ) (t θ : ℝ) (x : RunRecord d m) (q : S45.Sequence (Port d m)),
    0 < t → 0 < θ → θ < 1 →
    IsDampedEndpoint x.endpoint x.r t →
    q.wellFormed t (portR θ x.r) →
    q.state 0 = sweepStartLiveState θ x →
    (∀ k < q.length, ∀ y, q.pivot k = some y → y.2 = false) →
    ∀ k ≤ q.length, ∃ (ζ : Torus d m → ℝ) (G : Matrix (Torus d m) (Torus d m) ℂ),
      (x.endpoint.M.submatrix (Subtype.val : x.endpoint.active → Torus d m) Subtype.val +
          Matrix.diagonal (fun i : x.endpoint.active => ((ζ i.val : ℝ) : ℂ)) -
          ((t : ℝ) : ℂ) • Matrix.diagonal (fun i : x.endpoint.active =>
            ((prefixVartheta θ (q.state k).live i.val : ℝ) : ℂ) * x.r i.val)) *
        G.submatrix Subtype.val Subtype.val = 1 ∧
      ∀ p p' : Port d m, p ∈ (q.state k).live → p' ∈ (q.state k).live →
        (q.state k).g p p' = ((S45.splitPorts (Torus d m) θ).weight p : ℂ) *
          ((S45.splitPorts (Torus d m) θ).weight p' : ℂ) * G p.1 p'.1

/-- **(P2) Combes–Thomas on the torus active block** (05:62–100, Lemma `locality` with the
metric input and `physical_decay`): if the real part of the endpoint matrix is the active Schur
complement of the nearest-neighbour `H − E + installed` (`PhysicalIdentity`), then for every real
diagonal shift `D` and damping `c₀ t ≤ τ ≤ C₀ t` the inverse of `M_A + diag(D − iτ)` decays in the
physical distance at rate `t³`, and at rate `t` beyond `C t^{-2}`. -/
def ActiveCTStatement (d : ℕ) : Prop :=
  ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ C ≥ 1, ∃ t0 > 0, ∀ (m : ℕ) (t E : ℝ) (x : RunRecord d m)
    (D τ : Torus d m → ℝ) (G : Matrix (Torus d m) (Torus d m) ℂ), 0 < t → t < t0 →
    PhysicalIdentity E x →
    (∀ y z, physicalDistance d m y z / 2 - t ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) y z) →
    (∀ i ∈ x.endpoint.active, c₀ * t ≤ τ i ∧ τ i ≤ C₀ * t) →
    (x.endpoint.M.submatrix (Subtype.val : x.endpoint.active → Torus d m) Subtype.val +
        Matrix.diagonal (fun i : x.endpoint.active =>
          ((D i.val : ℝ) : ℂ) - Complex.I * ((τ i.val : ℝ) : ℂ))) *
      G.submatrix Subtype.val Subtype.val = 1 →
    ∀ i ∈ x.endpoint.active, ∀ k ∈ x.endpoint.active,
      ‖(Real.sqrt t : ℂ) * G i k‖ ≤
          C / Real.sqrt t * Real.exp (-t ^ 3 * physicalDistance d m i k / C) ∧
      (C * S45.power t (-2) < physicalDistance d m i k →
        ‖(Real.sqrt t : ℂ) * G i k‖ ≤
          C / Real.sqrt t * Real.exp (-t * physicalDistance d m i k / C))

end AndersonAC.AgentS78
