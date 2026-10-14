import AndersonAC.S2.Definitions
import AndersonAC.S9Diag.Diag

/-! The common null set for all true principal blocks in §2.
The determinant/Fubini proof is the shared §9 diffuse-diagonal helper.
Here it is extended to signed nonzero coupling and transported to principal
coordinate marginals before any adaptive set is chosen. -/

noncomputable section
open MeasureTheory OAI.Anderson Filter

namespace AndersonAC.SolS2

theorem diffuse_diagonal_invertible (n : Type) [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (coupling : ℝ) (hcoupling : coupling ≠ 0) :
    ∀ᵐ ω : n → SingleSite ∂Measure.pi (fun _ => uniformSite),
      IsUnit (K + (coupling : ℂ) • Matrix.diagonal (fun i => ((ω i : ℝ) : ℂ))) := by
  rcases lt_or_gt_of_ne hcoupling with hneg | hpos
  · have h := AndersonAC.SolS9.diagonalInvertibility_proof n (-K) (-coupling)
      (neg_pos.mpr hneg)
    filter_upwards [h] with ω hω
    simp only [Complex.ofReal_neg, neg_smul, ← neg_add] at hω
    exact (IsUnit.neg_iff _).mp hω
  · exact AndersonAC.SolS9.diagonalInvertibility_proof n K coupling hpos

theorem uniform_principal_restriction_preserving (n : Type) [Fintype n]
    [DecidableEq n] (U : Finset n) :
    MeasurePreserving (fun ω : n → SingleSite => fun i : U => ω i)
      (Measure.pi (fun _ : n => uniformSite))
      (Measure.pi (fun _ : U => uniformSite)) := by
  classical
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : n => uniformSite) (fun i => i ∈ U)
  have hfi : Subtype.fintype (fun i : n => i ∈ U) = Finset.Subtype.fintype U :=
    Subsingleton.elim _ _
  have hpi := congrArg (fun I : Fintype U =>
    @Measure.pi U (fun _ => SingleSite) I (fun _ => inferInstance) (fun _ => uniformSite)) hfi
  convert (measurePreserving_fst.comp hsplit) using 1
  all_goals first | rfl | exact hpi | exact hpi.symm

theorem principal_diagonal_invertible (n : Type) [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (coupling : ℝ) (hcoupling : coupling ≠ 0) :
    ∀ᵐ ω : n → SingleSite ∂Measure.pi (fun _ => uniformSite),
      ∀ U : Finset n, IsUnit
        ((K + (coupling : ℂ) • Matrix.diagonal (fun i => ((ω i : ℝ) : ℂ))).submatrix
          (fun i : U => (i : n)) (fun i : U => (i : n))) := by
  classical
  apply ae_all_iff.mpr
  intro U
  have hunit := diffuse_diagonal_invertible U
    (K.submatrix Subtype.val Subtype.val) coupling hcoupling
  have hres := uniform_principal_restriction_preserving n U
  have h := hres.quasiMeasurePreserving.ae hunit
  filter_upwards [h] with ω hω
  convert hω using 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : (i : n) ≠ (j : n) := fun h => hij (Subtype.ext h)
    simp [hij, hval]

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2

theorem true_principal_invertible (d m : ℕ) (coupling E : ℝ) (hcoupling : coupling ≠ 0) :
    ∀ᵐ ω ∂torusLaw d m, ∀ U : Finset (Torus d m),
      IsUnit ((hamiltonian coupling ω - (E : ℂ) • 1).submatrix
        (fun i : {i // i ∈ U} => i.val) (fun i : {i // i ∈ U} => i.val)) := by
  classical
  let K : Matrix (Torus d m) (Torus d m) ℂ := fun i j =>
    -(∑ k : Fin d,
      ((if j = i + torusBasisVector k then (1 : ℂ) else 0) +
       (if j = i - torusBasisVector k then (1 : ℂ) else 0))) -
      (if i = j then (E : ℂ) else 0)
  have h := principal_diagonal_invertible (Torus d m) K coupling hcoupling
  have hmatrix (ω : Configuration d m) :
      hamiltonian coupling ω - (E : ℂ) • 1 =
        K + (coupling : ℂ) • Matrix.diagonal (fun i => ((ω i : ℝ) : ℂ)) := by
    ext i j
    change periodicHamiltonian coupling ω i j -
        (E : ℂ) * (if i = j then 1 else 0) =
      K i j + (coupling : ℂ) * (if i = j then ((ω i : ℝ) : ℂ) else 0)
    by_cases hij : i = j
    · subst j
      simp only [periodicHamiltonian, K, ite_true, mul_one]
      push_cast
      ring
    · simp [periodicHamiltonian, K, hij]
  filter_upwards [h] with ω hω
  intro U
  rw [hmatrix]
  exact hω U

end AndersonAC.S2
