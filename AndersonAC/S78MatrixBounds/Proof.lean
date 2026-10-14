import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78MatrixBounds.Diagonal
import AndersonAC.S78MatrixBounds.RowFourOutput
import AndersonAC.S78MatrixBounds.SquareOutput

set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

/-- The three matrix outputs of the committed assembly, with constants chosen
uniformly before the volume and number of operations. -/
theorem assemblyMatrixBounds_proof : AssemblyMatrixBounds := by
  intro d hd C c P hC hc hP
  obtain ⟨Cdiag, tDiag, hCdiag, htDiag, hDiag⟩ :=
    assembly_diagonal_bound d hd C c P hC hc hP
  obtain ⟨Crow, tRow, hCrow, htRow, hRow⟩ :=
    assembly_rowFour_output d hd C c P hC hc hP
  obtain ⟨tSquare, htSquare, hSquare⟩ :=
    assembly_square_kernel_output d hd C c P hC hc hP
  let C' : ℝ := Cdiag + Crow + 1
  let t₀ : ℝ := min tDiag (min tRow tSquare)
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hCdiagLe : Cdiag ≤ C' := by dsimp [C']; linarith [hCdiag]
  have hCrowLe : Crow ≤ C' := by dsimp [C']; linarith [hCrow]
  have ht₀ : 0 < t₀ := by dsimp [t₀]; exact lt_min htDiag (lt_min htRow htSquare)
  refine ⟨C', t₀, hC', ht₀, ?_⟩
  intro m k t b r I hIC hIc hIP htSmall a
  have htDiagSmall : t < tDiag := lt_of_lt_of_le htSmall (min_le_left _ _)
  have htTail : t < min tRow tSquare := lt_of_lt_of_le htSmall (min_le_right _ _)
  have htRowSmall : t < tRow := lt_of_lt_of_le htTail (min_le_left _ _)
  have htSquareSmall : t < tSquare := lt_of_lt_of_le htTail (min_le_right _ _)
  rcases I.positive with ⟨ht, ht1, hb, hbt, hcI, hCI, hPI⟩
  have hpowDiag : 0 ≤ t ^ (0.42 * delta - (d : ℝ) * nu d) :=
    Real.rpow_nonneg ht.le _
  have hpowRow : 0 ≤ t ^ (0.0225 * delta - (d : ℝ) * nu d) :=
    Real.rpow_nonneg ht.le _
  have hpowScale : 0 ≤ t ^ ((1 + delta) / 4) :=
    Real.rpow_nonneg ht.le _
  have hdiagResult := hDiag m k t b r I hIC hIc hIP htDiagSmall a
  have hrowResult := hRow m k t b r I hIC hIc hIP htRowSmall a
  have hsquareResult := hSquare m k t b r I hIC hIc hIP htSquareSmall a
  refine ⟨hsquareResult, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    have h := hdiagResult i hi
    calc
      ‖(I.state a).g i i - r i‖ ≤
          Cdiag * t ^ (0.42 * delta - (d : ℝ) * nu d) := h
      _ ≤ C' * t ^ (0.42 * delta - (d : ℝ) * nu d) :=
        mul_le_mul_of_nonneg_right hCdiagLe hpowDiag
  · intro i
    refine ⟨?_, hrowResult.2 i⟩
    have h := hrowResult.1 i
    have hcoef : (0.7 : ℝ) ^ (1 / 4 : ℝ) +
        Crow * t ^ (0.0225 * delta - (d : ℝ) * nu d) ≤
        (0.7 : ℝ) ^ (1 / 4 : ℝ) +
        C' * t ^ (0.0225 * delta - (d : ℝ) * nu d) := by
      nlinarith [mul_le_mul_of_nonneg_right hCrowLe hpowRow]
    have hroot : rowL4Root (fun j => normalizedInverse (I.state a) t i j) ≤
        ((0.7 : ℝ) ^ (1 / 4 : ℝ) +
          C' * t ^ (0.0225 * delta - (d : ℝ) * nu d)) *
            t ^ ((1 + delta) / 4) := by
      calc
        _ ≤ ((0.7 : ℝ) ^ (1 / 4 : ℝ) +
            Crow * t ^ (0.0225 * delta - (d : ℝ) * nu d)) *
              t ^ ((1 + delta) / 4) := h
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hpowScale
    simpa [rowL4Root, rowFour] using hroot

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assemblyMatrixBounds_proof
