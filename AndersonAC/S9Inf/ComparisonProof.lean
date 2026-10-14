import AndersonAC.S9Inf.FiniteInfiniteComparison
import AndersonAC.S9Shell.CubeShell

namespace AndersonAC.SolS9

theorem finite_infinite_resolvent_comparison_proof :
    AndersonAC.SolS9Inf.FiniteInfiniteComparisonStatement :=
  AndersonAC.SolS9Inf.finite_infinite_comparison_of_shell
    AndersonAC.SolS9Inf.latticeCubeShell_proof

end AndersonAC.SolS9
