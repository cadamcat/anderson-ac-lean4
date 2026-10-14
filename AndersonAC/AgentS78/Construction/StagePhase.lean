import AndersonAC.AgentS78.Construction.BoundaryExtend
import AndersonAC.AgentS78.StageFromSections

/-!
# the clearing-phase invariant of a stage

Stage `j` (post-sweep index, `n₀ < j`) runs: tiles of the sweep into `j`, the sweep end, the
clearing attempts (`j ≤ ⌊m/2⌋`), the stage operation `guardMap (stageMap P j)` (reset at
`t_j`, cutoff, start lift). Between the sweep end and the stage operation the committed record
`x` carries `ClearPhaseData … j x`:

* `hist`: a stage history `BoundaryHist … (j − 1) old rOld` of the previous boundary endpoint
  (it gives the stage bounds through `stageBounds_of_hist`);
* `sweep`: the S78-form conclusions of the ordinary sweep from `(old, rOld)` at
  `t = t_{j−1}` to the post-sweep endpoint `sw = I.state 0` at `t' = t_j`
  (`SweepFacts`; the `sweep_step` half of `AgentS78.sweep_from_S45`);
* `I`: an `AssemblyInput` at `(t_j, b = t_{n₀} t_j, rOld)` of the committed clearings of the
  stage, starting at `sw`, whose last state is the record's endpoint; `x.r = rOld` (the
  damping is frozen during the stage, 07-assembly.tex:939–1030);
* constants `I.C = CA`, `I.c = cA`, `I.P = PA` fixed for the run (committed_assembly is
  applied with them).

At the sweep end of a stage the invariant holds with `k = 0` (`I` has the single state `sw`);
a non-clearing stage (`⌊m/2⌋ < j ≤ m`) keeps `k = 0` until its stage operation. A DONE
clearing extends `I` by one state; a FAIL keeps the endpoint.

`StagePhaseGood.lean` adds the clearing good-set condition.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- **Sweep handover** of a stage: the S78-form sweep conclusions relative to the previous
boundary endpoint `(old, rOld)` at `t`, for the post-sweep endpoint `sw` at `t'`
(the first component of `sweep_from_S45`'s conclusion, with its constant `C' ≤ C`). -/
structure SweepFacts (C t t' : ℝ) (old sw : Endpoint (Torus d m)) (rOld : Torus d m → ℂ) :
    Prop where
  active : sw.active = old.active
  affine : ∀ y, neutral old.active y →
    (1 - C * t ^ (0.10 * delta)) * stageTarget old rOld t t' old.active y ≤ Xof sw rOld t' y ∧
    Xof sw rOld t' y ≤ (1 + C * t ^ (0.10 * delta)) * stageTarget old rOld t t' old.active y
  K : Kn sw t' ≤ Kn old t + C * t ^ (0.10 * delta)

/-- **Clearing-phase data** of the committed record `x` of stage `j`. -/
structure ClearPhaseData (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C CA cA PA : ℝ) (j : ℕ)
    (x : RunRecord d m) where
  old : Endpoint (Torus d m)
  rOld : Torus d m → ℂ
  k : ℕ
  I : AssemblyInput d m k (stageScale u j m) (stageScale u n₀ m * stageScale u j m) rOld
  hist : BoundaryHist n₀ u E ρ C (j - 1) old rOld
  sweep : SweepFacts C (stageScale u (j - 1) m) (stageScale u j m) old (I.state 0) rOld
  last : I.state (Fin.last k) = x.endpoint
  frozen : x.r = rOld
  constC : I.C = CA
  constc : I.c = cA
  constP : I.P = PA

/-- **The clearing-phase invariant**: every non-aborted record carries clearing-phase data. -/
def ClearPhase (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C CA cA PA : ℝ) (j : ℕ) (x : RunRecord d m) :
    Prop :=
  x.aborted = false → Nonempty (ClearPhaseData n₀ u E ρ C CA cA PA j x)

/-- The endpoint after the diagonal reset of `s` on its active block by the correction
`ζ` (Proposition 7.4 on the active set: `g' = (M_A − t diag(r_A + ζ))⁻¹`, zero off `A`). -/
def resetEndpoint (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (ζ : s.active → ℂ) (t : ℝ) :
    Endpoint (Torus d m) where
  active := s.active
  M := s.M
  g := padM s.active (resetInverse (s.M.submatrix (fun a : s.active => a.val)
    (fun a : s.active => a.val)) ((fun a : s.active => r a.val) + ζ) t)

end AndersonAC.AgentS78
