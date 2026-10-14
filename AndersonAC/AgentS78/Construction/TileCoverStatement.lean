import AndersonAC.AgentS78.Construction.TileBlock

/-!
# WP10 construction: the §5 tile covers (statement)

agent-s78cover (2026-10-14), request of agent-s78con2 (DISPATCH-REQUESTS 00:20:11 UTC,
INTERFACE-ISSUES 00:20:11 (a), (b) and 00:14:36 (4)).
Paper (authoritative): refs/tex/05-local-sweeps.tex:240–256 (tiles, cubes `Q, Q'`, cutoff
`χ`, local pair space and extension `B_T`), 05:338–343 (`M = L_tile^d` slots),
02-state.tex:330–332 (`Λ`, the full-torus nearest-neighbour energy), 05:44–45 and 05:60–63
(ports at one site have distance zero; the physical distance `dist`).

## Design: one torus tiling, restricted to any injective family of ports

The construction serves both designs of INTERFACE-ISSUES 00:20:11 (b):

* `TorusTiling d m`: a deterministic tiling of the physical torus at scale `t` (it depends only
  on `d, m, t`): tiles (a partition of the sites), inner cubes `Q` and outer cubes `Q'` (as site
  sets) and the cutoffs `χ`.
* For **every** finite port type `P` with an injective map `ι : P → Port d m` (a subtype of the
  active ports, the ports `initialPorts (Fin n)` of an enumeration of the active sites, or all
  ports with `ι = id`) and every `b > 0`, the restriction is an `S45.TileCover` on `P` with
  site map `(ι ·).1`, energy `Λ = S78.gradientEnergy (nnGraph d m)`, distance
  `pullDist ι` (physical distance of the sites), the same tile index set as the tiling
  (`e : Fin cov.count ≃ Fin τ.count`) and tiles/inner sets the preimages of the tiling's.
  All constants are uniform in `m, t, b, P, ι`.

Hence (i) record-dependent covers are `ι = ` the inclusion of the stage-start active ports, and
(ii) the record-independent `TilePlan` cover is `ι = id`, whose restriction to the active ports
is again an instance with the same tile indices.

Not part of this statement (separate obligations, see NOTES.md):
* `start_comparison` (`D₀ ≍ W` with `W = spatialEnergy (ι ·).1 b Λ`, 05:328): this is the
  stage-boundary comparison `X ≍ W*` dualised (Lemma `dual-forms`, 02-state:356–383), which
  depends on the record, not on the cover; the cover only fixes `W` to the paper's form.
* `b = t_{n₀} t ≤ t` is the caller's choice; the cover works for every `b > 0`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- `Λ`, the full-torus nearest-neighbour energy (02-state.tex:330–332): the sum of
`|v_i - v_j|²` over unordered nearest-neighbour edges. -/
def torusEnergy (d m : ℕ) : S45.Form (Torus d m) := gradientEnergy (nnGraph d m)

/-- The distance of ports along `ι`: the physical distance of their sites (05:44–45, 05:60–63;
ports at one site have distance zero). -/
def pullDist {d m : ℕ} {P : Type*} (ι : P → Port d m) : P → P → ℝ :=
  fun x y => physicalDistance d m (ι x).1 (ι y).1

/-- A deterministic tiling of the torus (05:240–245): tiles `T` (a partition of the sites), the
concentric cubes `Q ⊇ T` (`inner`) and `Q' ⊇ Q` (`outer`), and the cutoff `χ_T` (one on `Q`,
zero at the boundary of `Q'` and outside it). -/
structure TorusTiling (d m : ℕ) where
  count : ℕ
  tile : Fin count → Finset (Torus d m)
  inner : Fin count → Finset (Torus d m)
  outer : Fin count → Finset (Torus d m)
  cutoff : Fin count → Torus d m → ℝ

/-- **The §5 tile covers.** For `d`, a constant `C ≥ 1` such that for every torus `m` and every
scale `0 < t ≤ 2` there is a torus tiling `τ` with tile and cube cardinalities `≤ C t^{-6d}`
and tile diameters `≤ C t^{-6}` (physical distance), whose restriction along every injective
family of ports `ι : P → Port d m` satisfies the shell bounds and is, for every `b > 0`, an
`S45.TileCover` with constant `C`, site map `(ι ·).1`, energy `Λ`, distance `pullDist ι`, the
tiling's tile indices, and tiles / inner sets the preimages of the tiling's. -/
def TileCoverStatement (d : ℕ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), 0 < t → t ≤ 2 →
    ∃ τ : TorusTiling d m,
      (∀ x, ∃! T, x ∈ τ.tile T) ∧
      (∀ T, ((τ.tile T).card : ℝ) ≤ C * S45.power t (-6 * (d : ℝ))) ∧
      (∀ T, ((τ.inner T).card : ℝ) ≤ C * S45.power t (-6 * (d : ℝ))) ∧
      (∀ T, ∀ x ∈ τ.tile T, ∀ y ∈ τ.tile T,
        physicalDistance d m x y ≤ C * S45.power t (-6)) ∧
      ∀ (P : Type) [Fintype P] [DecidableEq P] (ι : P → Port d m), Function.Injective ι →
        S45.ShellBounds d C (pullDist ι) ∧
        ∀ b : ℝ, 0 < b →
          ∃ cov : S45.TileCover (P := P) (I := Torus d m) d t b C (pullDist ι),
            cov.site = (fun x => (ι x).1) ∧ cov.energy = torusEnergy d m ∧
            ∃ e : Fin cov.count ≃ Fin τ.count,
              (∀ T x, x ∈ cov.tile T ↔ (ι x).1 ∈ τ.tile (e T)) ∧
              (∀ T x, x ∈ cov.inner T ↔ (ι x).1 ∈ τ.inner (e T)) ∧
              (∀ T, ((cov.inner T).card : ℝ) ≤ C * S45.power t (-6 * (d : ℝ)))

end AndersonAC.AgentS78
