import AndersonAC.AgentS78.Construction.StagePhaseReset

/-!
# Frozen sub-contract: the inverse-row bound at the reset (07-assembly.tex:1017–1019)

"The committed endpoint has `‖K‖ < 1/2` once the total summable increments are chosen small.
Lemma inverse-row, applied with its lag and the terminal metric, gives
`‖(Id − K)⁻¹‖_{∞→∞} ≤ C log(1/t)`."

`ResetRowStatement d`: for an `AssemblyInput` with fixed constants, at small scale, if the last
committed state has `‖K‖ ≤ 1/2` and lag `≤ t^{.36δ}` on its active sites, then
`ResetRowBound CR` holds for its active block, with `CR, t₀` depending only on `d` and the
constants. Intended route: transport the active block to `S45.State (Fin n)` (`toS45`,
S45Join.lean) and apply `AgentS45.inverse_row_proof` (lane/luna-s45loc d1e2547) with the
physical distance on the active sites (`ShellBounds`), the Ward identity of a damped endpoint
(`ward_of_damped`, WardDamped.lean), the entry bound and far decay from
`AssemblyInput.resolventDecay` at the last state, and `logFactor t ≤ 2 log(1/t)` for small `t`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **Inverse-row bound for the committed endpoint of a stage.** -/
def ResetRowStatement (d : ℕ) : Prop :=
  ∀ CA cA PA : ℝ, 1 ≤ CA → 0 < cA → 0 ≤ PA →
  ∃ CR t₀ : ℝ, 0 < t₀ ∧ ∀ {m : ℕ} (k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
    (I : AssemblyInput d m k t b r), I.C = CA → I.c = cA → I.P = PA → t < t₀ →
    Kn (I.state (Fin.last k)) t ≤ 1 / 2 →
    (∀ i ∈ (I.state (Fin.last k)).active,
      ‖(I.state (Fin.last k)).g i i - r i‖ ≤ t ^ (0.36 * delta)) →
    ResetRowBound CR (I.state (Fin.last k)) r t

end AndersonAC.AgentS78
