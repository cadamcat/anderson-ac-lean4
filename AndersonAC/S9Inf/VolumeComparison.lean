import AndersonAC.S9Vol.VolumeError

/-! The owned volume-error limit, reusing the accepted scalar helper. -/

namespace AndersonAC.SolS9

theorem volume_comparison_error_tendsto_proof :
    AndersonAC.SolS9Inf.VolumeComparisonErrorStatement :=
  AndersonAC.SolS9Inf.volumeComparisonError_proof

end AndersonAC.SolS9
