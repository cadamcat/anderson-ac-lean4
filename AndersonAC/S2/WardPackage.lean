import AndersonAC.Blueprint.FiniteInputs
import AndersonAC.S2.WardAlgebra

/-! Sorry-free proof of the frozen WP03 package interface. -/

noncomputable section
open AndersonAC.S2 AndersonAC.SolS2
open scoped Matrix.Norms.L2Operator

namespace AndersonAC.Blueprint.Packages

theorem ward : WardInput := by
  intro N M hMsym hMreal t ht r c hc hp
  let R : Matrix (Fin N) (Fin N) ℝ := fun i j => (M i j).re
  have hR : R.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact congrArg Complex.re ((show M.IsSymm from hMsym).apply i j)
  have hRM : realMatrix R = M := by
    ext i j
    apply Complex.ext
    · rfl
    · exact (hMreal i j).symm
  let G := resolvent R t r
  have hu := damped_invertible R hR ht r (fun i => hc.trans_le (hp i))
  have hd := (dampedMatrix R t r).isUnit_iff_isUnit_det.mp hu
  have hBG : dampedMatrix R t r * G = 1 := (dampedMatrix R t r).mul_nonsing_inv hd
  have hGB : G * dampedMatrix R t r = 1 := (dampedMatrix R t r).nonsing_inv_mul hd
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · change (M - (t : ℂ) • Matrix.diagonal r) * G = 1 ∧
      G * (M - (t : ℂ) • Matrix.diagonal r) = 1
    simpa only [dampedMatrix, hRM] using And.intro hBG hGB
  · exact (resolvent_symmetric R hR t r).1
  · simpa only [opNorm, ← Matrix.cstar_norm_def] using resolvent_norm_bound R hR ht hc r hp
  · simpa only [matrixImag, hermitianImaginary, one_div] using
      unnormalized_ward R hR ht r (fun i => hc.trans_le (hp i))

end AndersonAC.Blueprint.Packages
