import AndersonAC.S45.ConcentrationFinal
import AndersonAC.GT.Interface
import AndersonAC.Blueprint.Interfaces

/-! `Packages.concentration` follows from Golden–Thompson and Lemma 5.6 with
`c = 1/4`; `AgentS45.concentration_of_gt` supplies the deterministic trace facts
and Ville's inequality. -/

theorem AndersonAC.Blueprint.Packages.concentration :
    AndersonAC.Blueprint.ConcentrationInput :=
  AndersonAC.AgentS45.concentration_of_gt AndersonAC.MuseGT.goldenThompson_proof

/-- The S45 forms without the Golden–Thompson hypothesis. -/
theorem AndersonAC.AgentS45.goldenThompson_S45 : AndersonAC.S45.GoldenThompson :=
  fun N A B hA hB => AndersonAC.MuseGT.goldenThompson_proof N A B hA hB

#print axioms AndersonAC.Blueprint.Packages.concentration
#print axioms AndersonAC.AgentS45.goldenThompson_S45
