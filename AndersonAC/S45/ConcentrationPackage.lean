import AndersonAC.S45.Concentration
import AndersonAC.S45.Ville

/-! WP06 assembly: `ConcentrationInput` from Golden–Thompson and the five
deterministic trace facts. Ville's inequality is proved (`ville_proof`, muse-s45ville).
Once `GTStatement` (muse-gt) and `TraceHelpers` (luna-s45trace) are proved,
`Packages.concentration_proof` is `concentrationInput_of gt_proof trace_proof`. -/

namespace AndersonAC.OpusS45

open AndersonAC.Blueprint

/-- Lemma 5.6 (`05-local-sweeps.tex:686`) with `c = 1/4`, conditional only on
Golden–Thompson and the deterministic trace facts. -/
theorem maximal_of (hGT : GTStatement) (hT : TraceHelpers) : MaximalStatement :=
  maximal_of_helpers hGT hT ville_proof

theorem concentrationInput_of (hGT : GTStatement) (hT : TraceHelpers) : ConcentrationInput :=
  ⟨hGT, maximal_of hGT hT⟩

end AndersonAC.OpusS45
