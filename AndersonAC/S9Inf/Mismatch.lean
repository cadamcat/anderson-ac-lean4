import AndersonAC.S9Inf.BoundaryRankOne
import AndersonAC.S9Inf.MismatchCore
import AndersonAC.S9Inf.UpdateLaw
import AndersonAC.S9Inf.AndersonGreen

/-! Actual Anderson own-site sections for fixed-energy positivity propagation. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9Inf

def positiveScalarBoundary {d : ℕ} (coupling E : ℝ) (x : Site d)
    (ω : Configuration d) : Prop :=
  ∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g ∧ 0 < g.im

def zeroScalarBoundary {d : ℕ} (coupling E : ℝ) (y : Site d)
    (ω : Configuration d) : Prop :=
  ∃ k : ℂ, hasBoundary (scalarGreen coupling ω y y) E k ∧ k.im = 0

theorem scalarGreen_mismatch_null_of_measurable {d : ℕ} (coupling E : ℝ)
    (hcoupling : 0 < coupling) (x y : Site d)
    (hmeas : MeasurableSet {ω : Configuration d |
      positiveScalarBoundary coupling E x ω ∧ zeroScalarBoundary coupling E y ω})
    (hadmissible : ∀ᵐ ω ∂disorderLaw d,
      (∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g) ∧
      (∃ k : ℂ, hasBoundary (scalarGreen coupling ω y y) E k) ∧
      ∃ a : ℂ, hasBoundary (scalarGreen coupling ω x y) E a ∧ a ≠ 0) :
    disorderLaw d {ω | positiveScalarBoundary coupling E x ω ∧
      zeroScalarBoundary coupling E y ω} = 0 := by
  classical
  let U := fun p : Configuration d × SingleSite => Function.update p.1 x p.2
  let bad := U ⁻¹' {ω | positiveScalarBoundary coupling E x ω ∧
    zeroScalarBoundary coupling E y ω}
  let good : Set (Configuration d × SingleSite) := {p |
    (∃ g : ℂ, hasBoundary (scalarGreen coupling (U p) x x) E g) ∧
    (∃ k : ℂ, hasBoundary (scalarGreen coupling (U p) y y) E k) ∧
    ∃ a : ℂ, hasBoundary (scalarGreen coupling (U p) x y) E a ∧ a ≠ 0}
  have hU := updateSite_measurePreserving x
  rw [← hU.map_eq, Measure.map_apply hU.measurable hmeas]
  change (disorderLaw d).prod uniformSite bad = 0
  apply null_of_subsingleton_admissible_sections (disorderLaw d) uniformSite bad good
    (hU.measurable hmeas) (hU.quasiMeasurePreserving.ae hadmissible)
  intro ω s hs t ht
  obtain ⟨g, hg, hgpos⟩ := hs.2.1
  obtain ⟨k, hk, hkzero⟩ := hs.2.2
  obtain ⟨a, ha, hane⟩ := hs.1.2.2
  obtain ⟨kt, hkt, hktzero⟩ := ht.2.2
  have hpsd := scalarGreen_boundary_psd coupling (U (ω, s)) x y E g a k hg ha hk
  have hnew := scalarGreen_update_boundary coupling (U (ω, s)) x y t E g a k
    hg ha hk hgpos
  have hnew' : hasBoundary (scalarGreen coupling (U (ω, t)) y y) E
      (k - ((coupling * ((t : ℝ) - (s : ℝ)) : ℝ) : ℂ) * a ^ 2 /
        (1 + ((coupling * ((t : ℝ) - (s : ℝ)) : ℝ) : ℂ) * g)) := by
    simpa [U, Function.update_idem] using hnew
  have hrank := tendsto_nhds_unique hkt hnew'
  have hzero := rank_one_zero_boundary_forces_no_change g a k kt
    (coupling * ((t : ℝ) - (s : ℝ))) hgpos hane hkzero hktzero hpsd hrank
  have hst : (t : ℝ) - (s : ℝ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hcoupling.ne'
  exact (Subtype.ext (sub_eq_zero.mp hst)).symm

end AndersonAC.SolS9Inf

namespace AndersonAC.SolS9

open AndersonAC.SolS9Inf

theorem positivity_mismatch_null_of_potential
    (hpot : PotentialStrongContinuityStatement)
    (d : ℕ) (coupling E : ℝ) (hcoupling : 0 < coupling)
    (x y : Site d) (hxy : x ≠ y)
    (hadmissible : ∀ᵐ ω ∂disorderLaw d,
      (∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g) ∧
      (∃ k : ℂ, hasBoundary (scalarGreen coupling ω y y) E k) ∧
      ∃ a : ℂ, hasBoundary (scalarGreen coupling ω x y) E a ∧ a ≠ 0) :
    disorderLaw d {ω | positiveScalarBoundary coupling E x ω ∧
      zeroScalarBoundary coupling E y ω} = 0 := by
  apply scalarGreen_mismatch_null_of_measurable coupling E hcoupling x y
    _ hadmissible
  exact (scalarGreen_boundary_measurable_of_potential hpot coupling E x x).2.1.inter
    (scalarGreen_boundary_measurable_of_potential hpot coupling E y y).2.2.1

end AndersonAC.SolS9
