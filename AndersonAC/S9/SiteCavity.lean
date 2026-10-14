import AndersonAC.S9.ScalarCavity
import AndersonAC.S9.Resolution
import AndersonAC.S9.OwnSite
import AndersonAC.S9Inf.Model

noncomputable section
open OAI.Anderson MeasureTheory Filter
open scoped Topology

namespace AndersonAC.SolS9

def zeroSite : SingleSite := ⟨0, by simp⟩

def cavityOperator {d : ℕ} (coupling : ℝ) (x : Site d)
    (ξ : ComplementConfiguration d x) : StateSpace d →L[ℂ] StateSpace d :=
  hamiltonian coupling (restoreSite x ξ zeroSite)

def siteCavity {d : ℕ} (coupling : ℝ) (x : Site d)
    (ξ : ComplementConfiguration d x) : ℂ → ℂ :=
  rankOneCavity (cavityOperator coupling x ξ) (siteVector x)

theorem restoreSite_update {d : ℕ} (x : Site d) (ξ : ComplementConfiguration d x)
    (s : SingleSite) : restoreSite x ξ s = Function.update (restoreSite x ξ zeroSite) x s := by
  classical
  funext y
  by_cases hy : y = x <;> simp [restoreSite, hy, Function.update_of_ne]

theorem siteVector_norm {d : ℕ} (x : Site d) : ‖siteVector x‖ = 1 := by
  simp [siteVector, AndersonAC.Blueprint.delta, lp.norm_single]

theorem cavity_hamiltonian {d : ℕ} (coupling : ℝ) (x : Site d)
    (ξ : ComplementConfiguration d x) (s : SingleSite) :
    hamiltonian coupling (restoreSite x ξ s) = cavityOperator coupling x ξ +
      ((coupling * (s : ℝ) : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (siteVector x) (siteVector x) := by
  rw [restoreSite_update, AndersonAC.SolS9Inf.hamiltonian_update]
  simp [cavityOperator, restoreSite, zeroSite, siteVector,
    AndersonAC.SolS9Inf.basis, AndersonAC.Blueprint.delta]

theorem siteCavity_im_pos {d : ℕ} (coupling : ℝ) (x : Site d)
    (ξ : ComplementConfiguration d x) (z : ℂ) (hz : 0 < z.im) :
    0 < (siteCavity coupling x ξ z).im := by
  apply rankOneCavity_im_pos _ (hamiltonian_isSelfAdjoint _ _) _ _ _ hz
  intro h
  have := siteVector_norm x
  simp [h] at this

theorem siteCavity_identity {d : ℕ} (coupling : ℝ) (x : Site d)
    (ξ : ComplementConfiguration d x) (s : SingleSite) (z : ℂ) (hz : 0 < z.im) :
    AndersonAC.Blueprint.diagonalGreen coupling (restoreSite x ξ s) x z =
      ((coupling * (s : ℝ) : ℝ) - siteCavity coupling x ξ z)⁻¹ := by
  unfold AndersonAC.Blueprint.diagonalGreen
  rw [cavity_hamiltonian]
  exact (rank_one_cavity_identity _ (hamiltonian_isSelfAdjoint _ _)
    _ (siteVector_norm x) (coupling * (s : ℝ)) z hz)

theorem siteCavity_finite_ae {d : ℕ} (coupling : ℝ) (x : Site d)
    (ξ : ComplementConfiguration d x) (R : AndersonAC.Blueprint.ResolvedOperator
      (cavityOperator coupling x ξ)) (B : AndersonAC.Blueprint.BoundaryInput) :
    ∀ᵐ E ∂volume, finiteBoundary (siteCavity coupling x ξ) E := by
  let μ := R.spectral.vectorMeasure (siteVector x)
  have hμ := R.spectral.finite_vectorMeasure (siteVector x)
  have hnonzero : ∃ z : ℂ, 0 < z.im ∧
      AndersonAC.Blueprint.borelTransform μ z - AndersonAC.Blueprint.borelTransform 0 z ≠ 0 := by
    refine ⟨Complex.I, by simp, ?_⟩
    rw [show AndersonAC.Blueprint.borelTransform 0 Complex.I = 0 by
      simp [AndersonAC.Blueprint.borelTransform], sub_zero, ← R.resolvent_eq _ _ (by simp)]
    apply ne_of_apply_ne Complex.im
    apply ne_of_gt
    exact resolvent_im_pos _ (hamiltonian_isSelfAdjoint _ _) _ (by simp) _
      (by intro h; have := siteVector_norm x; simp [h] at this)
  filter_upwards [B.difference_nonzero μ 0 hμ inferInstance hnonzero] with E hE
  obtain ⟨w, hw, hwne⟩ := hE
  refine ⟨-w⁻¹, ?_⟩
  have hg : verticalBoundary
      (fun z => inner ℂ (siteVector x) (operatorResolvent (cavityOperator coupling x ξ) z (siteVector x))) E w := by
    apply hw.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    simp only [show AndersonAC.Blueprint.borelTransform 0 ((E : ℂ) + η * Complex.I) = 0 by
      simp [AndersonAC.Blueprint.borelTransform], sub_zero]
    exact (R.resolvent_eq _ _ (by simpa using hη)).symm
  exact (hg.inv₀ hwne).neg

end AndersonAC.SolS9
