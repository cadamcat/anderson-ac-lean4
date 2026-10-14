import AndersonAC.S9Inf.GreenContinuous
import AndersonAC.S9Inf.BoundaryMeasurable

/-! Configuration and height measurability of actual Green entries. -/

noncomputable section

open Filter OAI.Anderson MeasureTheory
open scoped Topology

namespace AndersonAC.SolS9Inf

theorem continuous_scalarGreen_of_potential
    (hpot : PotentialStrongContinuityStatement)
    {d : ℕ} {Ω : Type*} [TopologicalSpace Ω]
    (coupling : ℝ) (ω : Ω → Configuration d) (hω : Continuous ω)
    (z : Ω → ℂ) (hz : Continuous z) (hpos : ∀ a, 0 < (z a).im)
    (x y : Site d) : Continuous (fun a => scalarGreen coupling (ω a) x y (z a)) := by
  have hstrong : ∀ v : StateSpace d,
      Continuous (fun a => hamiltonian coupling (ω a) v) := by
    intro v
    change Continuous (fun a => hopping d v + (coupling : ℂ) • potentialOperator (ω a) v)
    convert (continuous_const (y := hopping d v)).add
      ((continuous_const (y := (coupling : ℂ))).smul ((hpot v).comp hω)) using 1
    ext a
    simp
  exact continuous_const.inner (continuous_green_of_strong _
    (fun a => hamiltonian_isSelfAdjoint coupling (ω a)) hstrong z hz hpos (basis y))

theorem measurable_scalarGreen_of_potential
    (hpot : PotentialStrongContinuityStatement) {d : ℕ}
    (coupling : ℝ) (x y : Site d) (z : ℂ) (hz : 0 < z.im) :
    Measurable (fun ω : Configuration d => scalarGreen coupling ω x y z) :=
  (continuous_scalarGreen_of_potential hpot coupling id continuous_id
    (fun _ => z) continuous_const (fun _ => hz) x y).measurable

theorem continuousOn_height_scalarGreen_of_potential
    (hpot : PotentialStrongContinuityStatement) {d : ℕ}
    (coupling E : ℝ) (ω : Configuration d) (x y : Site d) :
    ContinuousOn (fun η : ℝ => scalarGreen coupling ω x y
      ((E : ℂ) + (η : ℂ) * Complex.I)) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_scalarGreen_of_potential hpot (Ω := Set.Ioi (0 : ℝ))
    coupling (fun _ => ω) continuous_const
    (fun η => (E : ℂ) + ((η : ℝ) : ℂ) * Complex.I) ?_ ?_ x y
  · exact continuous_const.add ((Complex.continuous_ofReal.comp
      (continuous_subtype_val : Continuous (fun η : Set.Ioi (0 : ℝ) => (η : ℝ)))).mul
      continuous_const)
  · intro η
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    exact η.property

theorem scalarGreen_boundary_measurable_of_potential
    (hpot : PotentialStrongContinuityStatement) {d : ℕ}
    (coupling E : ℝ) (x y : Site d) :
    MeasurableSet {ω : Configuration d | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling ω x y) E w} ∧
    MeasurableSet {ω : Configuration d | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling ω x y) E w ∧ 0 < w.im} ∧
    MeasurableSet {ω : Configuration d | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling ω x y) E w ∧ w.im = 0} ∧
    MeasurableSet {ω : Configuration d | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling ω x y) E w ∧ w ≠ 0} := by
  apply boundaryEventMeasurability_proof (Configuration d)
    (fun ω η => scalarGreen coupling ω x y ((E : ℂ) + (η : ℂ) * Complex.I))
  · intro η hη
    apply measurable_scalarGreen_of_potential hpot
    simpa using hη
  · intro ω
    exact continuousOn_height_scalarGreen_of_potential hpot coupling E ω x y

theorem continuous_height_joint_scalarGreen_of_potential
    (hpot : PotentialStrongContinuityStatement) {d : ℕ}
    (coupling η : ℝ) (hη : 0 < η) (x y : Site d) :
    Continuous (fun p : Configuration d × ℝ => scalarGreen coupling p.1 x y
      ((p.2 : ℂ) + (η : ℂ) * Complex.I)) := by
  apply continuous_scalarGreen_of_potential hpot coupling Prod.fst continuous_fst
  · exact (Complex.continuous_ofReal.comp continuous_snd).add continuous_const
  · intro p
    simpa using hη

theorem scalarGreen_boundary_joint_measurable_of_potential
    (hpot : PotentialStrongContinuityStatement) {d : ℕ}
    (coupling : ℝ) (x y : Site d) :
    MeasurableSet {p : Configuration d × ℝ | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling p.1 x y) p.2 w} ∧
    MeasurableSet {p : Configuration d × ℝ | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling p.1 x y) p.2 w ∧ 0 < w.im} ∧
    MeasurableSet {p : Configuration d × ℝ | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling p.1 x y) p.2 w ∧ w.im = 0} ∧
    MeasurableSet {p : Configuration d × ℝ | ∃ w : ℂ,
      hasBoundary (scalarGreen coupling p.1 x y) p.2 w ∧ w ≠ 0} := by
  apply boundaryEventMeasurability_proof (Configuration d × ℝ)
    (fun p η => scalarGreen coupling p.1 x y ((p.2 : ℂ) + (η : ℂ) * Complex.I))
  · intro η hη
    exact (continuous_height_joint_scalarGreen_of_potential hpot coupling η hη x y).measurable
  · intro p
    exact continuousOn_height_scalarGreen_of_potential hpot coupling p.2 p.1 x y

theorem scalarGreen_boundary_im_nonneg {d : ℕ} (coupling E : ℝ)
    (ω : Configuration d) (x : Site d) (g : ℂ)
    (hg : hasBoundary (scalarGreen coupling ω x x) E g) : 0 ≤ g.im := by
  apply ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hg)
  filter_upwards [self_mem_nhdsWithin] with η hη
  apply green_quadratic_im_nonneg _ (hamiltonian_isSelfAdjoint coupling ω)
  simpa using (show 0 < η from hη)

end AndersonAC.SolS9Inf
