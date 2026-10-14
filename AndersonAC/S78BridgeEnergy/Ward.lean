import AndersonAC.S78.Definitions
import AndersonAC.S2.Definitions
import AndersonAC.S2.WardAlgebra
import AndersonAC.S78Var.WardRows

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.S2

/-- Real part of a complex symmetric zero-imag matrix is symmetric. -/
private theorem realPart_symm {S : Type} [Fintype S] [DecidableEq S]
    (M : Matrix S S ℂ) (hsym : ∀ i j, M i j = M j i) :
    (Matrix.IsSymm fun i j => (M i j).re) := by
  apply Matrix.IsSymm.ext
  intro i j
  show (M j i).re = (M i j).re
  rw [hsym j i]

/-- A complex matrix with zero imaginary part equals the real embedding. -/
private theorem complex_eq_realMatrix {S : Type} [Fintype S] [DecidableEq S]
    (M : Matrix S S ℂ) (hreal : ∀ i j, (M i j).im = 0) :
    M = AndersonAC.S2.realMatrix (fun i j => (M i j).re) := by
  ext i j
  apply Complex.ext
  · rfl
  · simp [AndersonAC.S2.realMatrix]
    exact hreal i j

/-- Subtype row-two bound for a damped endpoint.
`GS` is the active-subtype inverse; the Ward identity comes from
`S2.unnormalized_ward` via the real part. No full-matrix transfer is needed:
later weight sums range over active sites only. -/
theorem subtype_rowTwo_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t c Cg : ℝ)
    (ht : 0 < t) (hc : 0 < c)
    (hlow : ∀ k, c ≤ (r k).im)
    (hs : IsDampedEndpoint s r t)
    (hIm : ∀ i : {x : ι // x ∈ s.active}, ((s.g.submatrix
      (fun i : {x : ι // x ∈ s.active} => (i.val : ι))
      (fun i : {x : ι // x ∈ s.active} => (i.val : ι))) i i).im ≤ Cg) :
    ∀ a : {x : ι // x ∈ s.active},
      rowTwo ((Real.sqrt t : ℂ) •
        s.g.submatrix (fun i : {x : ι // x ∈ s.active} => (i.val : ι))
          (fun i : {x : ι // x ∈ s.active} => (i.val : ι))) a ≤ Cg / c := by
  classical
  rcases hs with ⟨hM, _hzero, hInv⟩
  let S := {x : ι // x ∈ s.active}
  let MS : Matrix S S ℂ :=
    s.M.submatrix (fun i : S => (i.val : ι)) (fun i : S => (i.val : ι))
  let GS : Matrix S S ℂ :=
    s.g.submatrix (fun i : S => (i.val : ι)) (fun i : S => (i.val : ι))
  let rS : S → ℂ := fun i => r (i.val : ι)
  have hMSsym : ∀ i j : S, MS i j = MS j i := fun i j => (hM _ _).1
  have hMSreal : ∀ i j : S, (MS i j).im = 0 := fun i j => (hM _ _).2
  let R : Matrix S S ℝ := fun i j => (MS i j).re
  have hRsym : R.IsSymm := realPart_symm MS hMSsym
  have hMeq : MS = AndersonAC.S2.realMatrix R := by
    have h := complex_eq_realMatrix MS hMSreal
    simpa [R, AndersonAC.S2.realMatrix] using h
  have hB : AndersonAC.S2.dampedMatrix R t rS =
      MS - (t : ℂ) • Matrix.diagonal rS := by
    simp [AndersonAC.S2.dampedMatrix, hMeq]
  have hBG : (MS - (t : ℂ) • Matrix.diagonal rS) * GS = 1 := hInv.1
  have hGres : GS = AndersonAC.S2.resolvent R t rS := by
    have hBG' : AndersonAC.S2.dampedMatrix R t rS * GS = 1 := hB.symm ▸ hBG
    simp only [AndersonAC.S2.resolvent]
    exact (Matrix.inv_eq_right_inv hBG').symm
  have hlowS : ∀ i : S, 0 < (rS i).im := fun i => hc.trans_le (hlow _)
  have hWardS : (t : ℂ) • (GS * Matrix.diagonal (fun i => ((rS i).im : ℂ)) *
      GS.conjTranspose) = AndersonAC.Blueprint.matrixImag GS := by
    have h := AndersonAC.SolS2.unnormalized_ward R hRsym (ht := ht) rS hlowS
    have hEq : AndersonAC.S2.hermitianImaginary GS =
        AndersonAC.Blueprint.matrixImag GS := by
      simp [AndersonAC.S2.hermitianImaginary, AndersonAC.Blueprint.matrixImag, one_div]
    rw [← hGres] at h
    simpa [hEq] using h
  intro a
  exact AndersonAC.SolS78Var.ward_rowTwo_bound GS t rS c Cg ht hc
    (fun k => hlow _) hWardS a (hIm a)

end AndersonAC.S78BridgeEnergy
