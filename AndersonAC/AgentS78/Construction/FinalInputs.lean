import AndersonAC.S45.ConcentrationFinal
import AndersonAC.GT.Interface

/-! Inputs to the construction. The clearing trial bound
(`clearingTrialZ_proof`) takes `ConcentrationInput` (Lemma 5.6), proved from
Golden–Thompson (`MuseGT.goldenThompson_proof`) and the trace helpers. -/

namespace AndersonAC.AgentS78

theorem concentrationInput_closed : AndersonAC.Blueprint.ConcentrationInput :=
  AndersonAC.AgentS45.concentrationInput_proof AndersonAC.MuseGT.goldenThompson_proof

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.concentrationInput_closed
