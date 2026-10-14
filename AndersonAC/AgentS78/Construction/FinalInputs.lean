import AndersonAC.S45.ConcentrationFinal
import AndersonAC.GT.Interface

/-! Blueprint inputs the WP10 construction consumes, closed (lead, agent-s78con4).
C4b (`clearingTrialZ_proof`) takes `ConcentrationInput` (Lemma 5.6); it is proved from
Golden–Thompson (`MuseGT.goldenThompson_proof`) and the trace helpers. -/

namespace AndersonAC.AgentS78

theorem concentrationInput_closed : AndersonAC.Blueprint.ConcentrationInput :=
  AndersonAC.AgentS45.concentrationInput_proof AndersonAC.MuseGT.goldenThompson_proof

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.concentrationInput_closed
