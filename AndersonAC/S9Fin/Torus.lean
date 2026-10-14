import AndersonAC.S9Fin.Scalar

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9

namespace AndersonAC.SolS9

def torusTranslationEquiv {d m : ℕ} (a : Torus d m) :
    TorusConfiguration d m ≃ᵐ TorusConfiguration d m :=
  (MeasurableEquiv.piCongrLeft (fun _ : Torus d m => SingleSite) (Equiv.addLeft a)).symm

@[simp]
lemma torusTranslationEquiv_apply {d m : ℕ} (a : Torus d m)
    (ω : TorusConfiguration d m) (x : Torus d m) :
    torusTranslationEquiv a ω x = ω (a + x) := rfl

lemma torusTranslation_measurePreserving {d m : ℕ} (a : Torus d m) :
    MeasurePreserving (torusTranslationEquiv a) (torusLaw d m) (torusLaw d m) := by
  exact MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (fun _ : Torus d m => uniformSite) (Equiv.addLeft a))

lemma periodicHamiltonian_translation {d m : ℕ} (a : Torus d m)
    (coupling : ℝ) (ω : TorusConfiguration d m) :
    periodicHamiltonian coupling (torusTranslationEquiv a ω) =
      (periodicHamiltonian coupling ω).submatrix (Equiv.addLeft a) (Equiv.addLeft a) := by
  classical
  ext x y
  change periodicHamiltonian coupling (torusTranslationEquiv a ω) x y =
    periodicHamiltonian coupling ω (a + x) (a + y)
  have hp (j : Fin d) : a + y = (a + x) + torusBasisVector j ↔
      y = x + torusBasisVector j := by rw [add_assoc, add_left_cancel_iff]
  have hm (j : Fin d) : a + y = (a + x) - torusBasisVector j ↔
      y = x - torusBasisVector j := by rw [add_sub_assoc, add_left_cancel_iff]
  simp only [periodicHamiltonian,
    hp, hm, add_left_cancel_iff, torusTranslationEquiv_apply]

lemma matrixResolvent_translation {d m : ℕ} (a : Torus d m)
    (coupling E η : ℝ) (ω : TorusConfiguration d m) :
    matrixResolvent (periodicHamiltonian coupling (torusTranslationEquiv a ω)) E η =
      (matrixResolvent (periodicHamiltonian coupling ω) E η).submatrix
        (Equiv.addLeft a) (Equiv.addLeft a) := by
  unfold matrixResolvent
  rw [periodicHamiltonian_translation]
  have heq : (periodicHamiltonian coupling ω).submatrix (Equiv.addLeft a) (Equiv.addLeft a) -
        ((E : ℂ) + η * Complex.I) • 1 =
      (periodicHamiltonian coupling ω - ((E : ℂ) + η * Complex.I) • 1).submatrix
        (Equiv.addLeft a) (Equiv.addLeft a) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [heq, Matrix.inv_submatrix_equiv]

lemma scalarQ_translation {d m : ℕ} (a : Torus d m)
    (coupling E η : ℝ) (ω : TorusConfiguration d m) (x : Torus d m) :
    scalarQ (periodicHamiltonian coupling (torusTranslationEquiv a ω)) E η x =
      scalarQ (periodicHamiltonian coupling ω) E η (a + x) := by
  unfold scalarQ
  rw [matrixResolvent_translation]
  rfl

lemma torus_site_expectation (d m : ℕ) (coupling E η ε : ℝ)
    (b : CertificateBounds) (a : Torus d m) :
    (∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η a)
      ∂torusLaw d m) =
      ∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η 0)
        ∂torusLaw d m := by
  have h := (torusTranslation_measurePreserving a).integral_comp'
    (fun ω => truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η 0))
  simpa only [scalarQ_translation, add_zero] using h

theorem torus_root_expectation_proof (d m : ℕ) (coupling E η ε : ℝ) (b : CertificateBounds) :
    (∫ ω, (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
      Fintype.card (Torus d m) ∂torusLaw d m) =
      ∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η 0) ∂torusLaw d m := by
  rw [integral_div, integral_finsetSum]
  · simp only [torus_site_expectation, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card (Torus d m) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_div_cancel_left₀ _ hc
  · intro i _
    exact truncatedReadout_torus_integrable d m coupling E η ε b i

end AndersonAC.SolS9
