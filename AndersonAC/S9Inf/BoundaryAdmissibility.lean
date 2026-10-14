import AndersonAC.S9Inf.OffDiagonalBoundary
import AndersonAC.S9Inf.Propagation

/-! Fubini gives a deterministic full-measure set of admissible energies. -/

noncomputable section

open MeasureTheory OAI.Anderson Filter
open scoped Topology

namespace AndersonAC.SolS9Inf

def boundaryGood {d : ℕ} (coupling : ℝ) (ω : Configuration d) (E : ℝ) : Prop :=
  (∀ x : Site d, ∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g) ∧
  ∀ x y : Site d, x ≠ y →
    ∃ a : ℂ, hasBoundary (scalarGreen coupling ω x y) E a ∧ a ≠ 0

theorem measurableSet_boundaryGood {d : ℕ} (coupling : ℝ) :
    MeasurableSet {p : Configuration d × ℝ | boundaryGood coupling p.1 p.2} := by
  rw [show {p : Configuration d × ℝ | boundaryGood coupling p.1 p.2} =
      (⋂ x : Site d, {p | ∃ g : ℂ, hasBoundary (scalarGreen coupling p.1 x x) p.2 g}) ∩
        (⋂ x : Site d, ⋂ y : Site d, {p | x ≠ y →
          ∃ a : ℂ, hasBoundary (scalarGreen coupling p.1 x y) p.2 a ∧ a ≠ 0}) from by
        ext p; simp only [boundaryGood, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun x =>
      (scalarGreen_boundary_joint_measurable_of_potential potentialStrongContinuity_proof
        coupling x x).1
  · apply MeasurableSet.iInter
    intro x
    apply MeasurableSet.iInter
    intro y
    by_cases hxy : x ≠ y
    · rw [show {p : Configuration d × ℝ | x ≠ y →
          ∃ a : ℂ, hasBoundary (scalarGreen coupling p.1 x y) p.2 a ∧ a ≠ 0} =
          {p | ∃ a : ℂ, hasBoundary (scalarGreen coupling p.1 x y) p.2 a ∧ a ≠ 0} from by
            ext p; exact ⟨fun h => h hxy, fun h _ => h⟩]
      exact (scalarGreen_boundary_joint_measurable_of_potential potentialStrongContinuity_proof
        coupling x y).2.2.2
    · simp only [hxy, false_implies, Set.setOf_true]
      exact MeasurableSet.univ

theorem scalarGreen_finite_boundary_ae {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x : Site d) (R : AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω))
    (B : AndersonAC.Blueprint.BoundaryInput) :
    ∀ᵐ E ∂volume, ∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g := by
  filter_upwards [B.finite (R.spectral.vectorMeasure (basis x))
    (R.spectral.finite_vectorMeasure (basis x))] with E hE
  obtain ⟨g, hg⟩ := hE
  refine ⟨g, hg.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  symm
  exact R.resolvent_eq (basis x) ((E : ℂ) + (η : ℂ) * Complex.I)
    (by simpa using (show 0 < η from hη))

theorem boundaryGood_ae_energy {d : ℕ} (coupling : ℝ)
    (R : ∀ ω : Configuration d,
      AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω))
    (B : AndersonAC.Blueprint.BoundaryInput) :
    ∀ᵐ E ∂volume, ∀ᵐ ω ∂disorderLaw d, boundaryGood coupling ω E := by
  apply (Measure.ae_ae_comm (measurableSet_boundaryGood coupling)).mp
  apply ae_of_all
  intro ω
  have hf : ∀ᵐ E ∂volume, ∀ x : Site d,
      ∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g :=
    ae_all_iff.mpr (fun x => scalarGreen_finite_boundary_ae coupling ω x (R ω) B)
  have ho : ∀ᵐ E ∂volume, ∀ x y : Site d, x ≠ y →
      ∃ a : ℂ, hasBoundary (scalarGreen coupling ω x y) E a ∧ a ≠ 0 := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    by_cases hxy : x ≠ y
    · filter_upwards [AndersonAC.SolS9.offDiagonal_boundary_nonzero_proof
        coupling ω x y hxy (R ω) B] with E hE
      exact fun _ => hE
    · exact ae_of_all _ (fun _ h => False.elim (hxy h))
  filter_upwards [hf, ho] with E hE hEoff
  exact ⟨hE, hEoff⟩

theorem all_sites_positive_ae_energy_of_root_probability {d : ℕ} (hd : 0 < d)
    (coupling : ℝ) (hcoupling : 0 < coupling)
    (R : ∀ ω : Configuration d,
      AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω))
    (B : AndersonAC.Blueprint.BoundaryInput) (I : Set ℝ)
    (hroot : ∀ᵐ E ∂volume.restrict I,
      0 < disorderLaw d {ω | positiveScalarBoundary coupling E 0 ω}) :
    ∀ᵐ E ∂volume.restrict I, ∀ᵐ ω ∂disorderLaw d,
      ∀ x : Site d, positiveScalarBoundary coupling E x ω := by
  have hgood := ae_restrict_of_ae (s := I) (boundaryGood_ae_energy coupling R B)
  filter_upwards [hgood, hroot] with E hEgood hEroot
  apply all_sites_positive_of_root_probability hd coupling E hcoupling hEroot
  · exact hEgood.mono (fun ω hω => hω.1)
  · exact hEgood.mono (fun ω hω => hω.2)

end AndersonAC.SolS9Inf
