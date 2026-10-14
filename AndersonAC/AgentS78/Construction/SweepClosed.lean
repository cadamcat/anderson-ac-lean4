import AndersonAC.AgentS78.Construction.SweepTransport
import AndersonAC.AgentS78.Construction.SweepRowTail
import AndersonAC.AgentS78.Construction.SweepEndReserve

/-!
# Sweep contracts from transport and row-tail bounds

`finalSweep_closed`: the final residual sweep record, unconditional.
`sweepEnd_of_terminalCT`: the digit sweep end, conditional only on `TerminalCTStatement`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

variable {d : ℕ}

/-- **The final residual sweep record**, unconditional. -/
theorem finalSweep_closed (d : ℕ) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∀ Cb : ℝ, FinalSweepStatementSB d C Cb CP cP (cP / 2) cP CP cL CL C₀ :=
  finalSweep_proof (sweepTransportFull_proof d) (sweepRowTailFull_proof d)

/-- The constants of the final record, unconditional. -/
theorem finalSweep_exists_closed (d : ℕ) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
    ∃ Cr cp cg : ℝ, 0 < cp ∧ 0 < cg ∧ ∀ C : ℝ, 1 ≤ C → ∀ Cb : ℝ,
      FinalSweepStatementSB d C Cb Cr cp cg cP CP cL CL C₀ :=
  finalSweep_exists (sweepTransportFull_proof d) (sweepRowTailFull_proof d)

/-- **The digit sweep end**, conditional only on the terminal Combes–Thomas bound. -/
theorem sweepEnd_of_terminalCT (hCT : TerminalCTStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∃ Cb₀ > (0 : ℝ), ∀ Cb ≥ Cb₀, ∃ CA₀ > (0 : ℝ), ∃ cA₀ > (0 : ℝ), ∀ CA ≥ CA₀, ∀ cA : ℝ,
      0 < cA → cA ≤ cA₀ → SweepEndStatement d C Cb CA cA cP CP cL CL C₀ :=
  sweepEnd_proof'' (sweepTransport_proof d) (sweepRowTail_proof d) hCT

end AndersonAC.AgentS78
