import AndersonAC.S9Fin.HelperStatements

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9 Filter

namespace AndersonAC.SolS9

/-- The generic diffuse-diagonal result is applied before the finite intersection
and before any adaptive certificate set is selected. -/
theorem true_principal_invertible_ae_of_diagonal (hD : DiagonalInvertibilityStatement)
    (d m : ℕ) (coupling E : ℝ) (hcoupling : 0 < coupling) :
    ∀ᵐ ω ∂torusLaw d m, allPrincipalInvertible (periodicHamiltonian coupling ω) E := by
  classical
  change ∀ᵐ ω ∂torusLaw d m, ∀ A : Finset (Torus d m), _
  apply ae_all_iff.mpr
  intro A
  let K : Matrix A A ℂ := fun x y =>
    -(∑ j : Fin d,
      ((if (y : Torus d m) = (x : Torus d m) + torusBasisVector j then (1 : ℂ) else 0) +
       (if (y : Torus d m) = (x : Torus d m) - torusBasisVector j then (1 : ℂ) else 0))) -
      (if x = y then (E : ℂ) else 0)
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Torus d m => uniformSite) (fun i => i ∈ A)
  have hres : MeasurePreserving (fun ω : TorusConfiguration d m => fun i : A => ω i)
      (torusLaw d m) (Measure.pi (fun _ : A => uniformSite)) := by
    have hfi : Subtype.fintype (fun i : Torus d m => i ∈ A) = Finset.Subtype.fintype A :=
      Subsingleton.elim _ _
    have hpi := congrArg (fun I : Fintype A =>
      @Measure.pi A (fun _ => SingleSite) I (fun _ => inferInstance) (fun _ => uniformSite)) hfi
    convert (measurePreserving_fst.comp hsplit) using 1
    all_goals first | rfl | exact hpi | exact hpi.symm | (ext ω i; rfl)
  have hg := hres.quasiMeasurePreserving.ae (hD A K coupling hcoupling)
  filter_upwards [hg] with ω hω
  convert hω using 1
  congr 1
  ext i j
  change periodicHamiltonian coupling ω i j - (E : ℂ) *
      (if (i : Torus d m) = (j : Torus d m) then 1 else 0) =
    K i j + (coupling : ℂ) * (if i = j then ((ω i : ℝ) : ℂ) else 0)
  by_cases hij : i = j
  · subst j
    simp only [periodicHamiltonian, K, ite_true, mul_one]
    push_cast
    ring
  · have hval : (i : Torus d m) ≠ (j : Torus d m) := by
      intro h
      exact hij (Subtype.ext h)
    simp [periodicHamiltonian, K, hij, hval]

end AndersonAC.SolS9
