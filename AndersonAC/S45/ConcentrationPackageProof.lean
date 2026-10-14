import AndersonAC.S45.ConcentrationFinal
import AndersonAC.GT.Interface
import AndersonAC.Blueprint.Interfaces

/-! WP06: `Packages.concentration`. Golden–Thompson from muse-gt
(`AndersonAC.MuseGT.goldenThompson_proof`); Lemma 5.6 with c = 1/4 from
`AgentS45.concentration_of_gt` (Ville from muse-s45ville, trace facts from luna-s45trace). -/

theorem AndersonAC.Blueprint.Packages.concentration :
    AndersonAC.Blueprint.ConcentrationInput :=
  AndersonAC.AgentS45.concentration_of_gt AndersonAC.MuseGT.goldenThompson_proof

/-- The S45 forms without the Golden–Thompson hypothesis. -/
theorem AndersonAC.AgentS45.goldenThompson_S45 : AndersonAC.S45.GoldenThompson :=
  fun N A B hA hB => AndersonAC.MuseGT.goldenThompson_proof N A B hA hB

#print axioms AndersonAC.Blueprint.Packages.concentration
#print axioms AndersonAC.AgentS45.goldenThompson_S45
