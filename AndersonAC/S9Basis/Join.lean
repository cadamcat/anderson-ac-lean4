import AndersonAC.S9.HelperStatements

/-! The basis spectral measures have uniformly compact support and measurable
moments.  The compact-moment kernel principle then gives the required kernel
measurability. -/

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal lp

namespace AndersonAC.SolS9

private def basisNeighborExpansion {d : ℕ} (F : Set (Site d)) : Set (Site d) :=
  F ∪ ⋃ j : Fin d,
    ((fun y : Site d => y - basisVector j) '' F ∪
      (fun y : Site d => y + basisVector j) '' F)

private theorem hamiltonian_support_finite {d : ℕ} (coupling : ℝ)
    (ω : Configuration d) (f : StateSpace d)
    (hf : {y : Site d | f y ≠ 0}.Finite) :
    {y : Site d | (hamiltonian coupling ω f) y ≠ 0}.Finite := by
  classical
  let F : Set (Site d) := {y | f y ≠ 0}
  have hF : F.Finite := hf
  have hExpanded : (basisNeighborExpansion F).Finite := by
    unfold basisNeighborExpansion
    apply hF.union
    exact Set.finite_iUnion fun j =>
      (hF.image (fun y : Site d => y - basisVector j)).union
        (hF.image (fun y : Site d => y + basisVector j))
  apply hExpanded.subset
  intro y hy
  by_contra hyOut
  have hnotF : y ∉ F := by
    intro h
    exact hyOut (Or.inl h)
  have hnotNbr (j : Fin d) :
      y ∉ ((fun z : Site d => z - basisVector j) '' F ∪
        (fun z : Site d => z + basisVector j) '' F) := by
    intro h
    exact hyOut (Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hdiag : f y = 0 := by
    by_contra h
    exact hnotF h
  have hplus (j : Fin d) : f (y + basisVector j) = 0 := by
    by_contra h
    apply hnotNbr j
    exact Or.inl ⟨y + basisVector j, h, by simp⟩
  have hminus (j : Fin d) : f (y - basisVector j) = 0 := by
    by_contra h
    apply hnotNbr j
    exact Or.inr ⟨y - basisVector j, h, by simp⟩
  have hz : (hamiltonian coupling ω f) y = 0 := by
    rw [hamiltonian_apply]
    simp [hdiag, hplus, hminus]
  exact hy hz

private theorem basisPower_support_finite {d : ℕ} (coupling : ℝ)
    (x : Site d) (n : ℕ) :
    ∀ ω : Configuration d,
      {y : Site d | ((hamiltonian coupling ω ^ n) (siteVector x)) y ≠ 0}.Finite := by
  classical
  induction n with
  | zero =>
      intro ω
      have hsingle : {y : Site d | siteVector x y ≠ 0} = {x} := by
        ext y
        by_cases h : y = x <;> simp [siteVector, AndersonAC.Blueprint.delta, h]
      rw [pow_zero, ContinuousLinearMap.one_apply, hsingle]
      exact Set.finite_singleton x
  | succ n ih =>
      intro ω
      rw [pow_succ']
      simpa only [ContinuousLinearMap.mul_apply] using
        hamiltonian_support_finite coupling ω
          ((hamiltonian coupling ω ^ n) (siteVector x)) (ih ω)

private theorem siteVector_norm {d : ℕ} (x : Site d) :
    ‖siteVector x‖ = 1 := by
  simp [siteVector, AndersonAC.Blueprint.delta, lp.norm_single]

private theorem inner_siteVector_apply {d : ℕ} (x : Site d)
    (f : StateSpace d) : inner ℂ (siteVector x) f = f x := by
  change inner ℂ (lp.single 2 x (1 : ℂ)) f = f x
  rw [lp.inner_single_left]
  simp

private theorem basisPower_coord_measurable {d : ℕ} (coupling : ℝ)
    (x : Site d) (n : ℕ) :
    ∀ y : Site d, Measurable (fun ω : Configuration d =>
      ((hamiltonian coupling ω ^ n) (siteVector x)) y) := by
  induction n with
  | zero =>
      intro y
      simp only [pow_zero, ContinuousLinearMap.one_apply]
      exact measurable_const
  | succ n ih =>
      intro y
      simp only [pow_succ', ContinuousLinearMap.mul_apply]
      simp only [OAI.Anderson.hamiltonian_apply]
      have hsum : Measurable (fun ω : Configuration d =>
          ∑ j : Fin d,
            (((hamiltonian coupling ω ^ n) (siteVector x)) (y + basisVector j) +
              ((hamiltonian coupling ω ^ n) (siteVector x)) (y - basisVector j))) := by
        exact Finset.univ.measurable_fun_sum fun j hj =>
          (ih (y + basisVector j)).add (ih (y - basisVector j))
      have hpot : Measurable (fun ω : Configuration d =>
          ((coupling * potential ω y : ℝ) : ℂ)) := by
        exact Complex.measurable_ofReal.comp
          (measurable_const.mul (potential_measurable y))
      convert (Measurable.neg hsum).add (hpot.mul (ih y)) using 1
      ext ω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply]
      push_cast
      ring

/-- Apply the compact-moment kernel contract to the scalar spectral measures
of the lattice basis vectors. -/
theorem BasisMeasureMeasurableJoin_proof :
    BasisMeasureMeasurableJoin := by
  intro hkernel d coupling S x A hA
  let μ : Configuration d → Measure ℝ :=
    fun ω => (S ω).vectorMeasure (siteVector x)
  let M : ℝ := 2 * (d : ℝ) + |coupling|
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hprob : ∀ ω, IsProbabilityMeasure (μ ω) := by
    intro ω
    constructor
    change (S ω).vectorMeasure (siteVector x) Set.univ = 1
    rw [(S ω).vectorMeasure_univ, siteVector_norm]
    norm_num
  have hsupport : ∀ ω, μ ω (Set.Icc (-M) M)ᶜ = 0 := by
    intro ω
    have hnorm : ‖hamiltonian coupling ω‖ ≤ M := by
      dsimp [M]
      exact (norm_hamiltonian_le coupling ω)
    have hinterval :
        Set.Icc (-‖hamiltonian coupling ω‖) ‖hamiltonian coupling ω‖ ⊆
          Set.Icc (-M) M := by
      intro t ht
      exact ⟨(neg_le_neg hnorm).trans ht.1, ht.2.trans hnorm⟩
    have hcomplement : (Set.Icc (-M) M)ᶜ ⊆
        (Set.Icc (-‖hamiltonian coupling ω‖) ‖hamiltonian coupling ω‖)ᶜ := by
      intro t ht hin
      exact ht (hinterval hin)
    change (S ω).vectorMeasure (siteVector x) (Set.Icc (-M) M)ᶜ = 0
    exact measure_mono_null hcomplement ((S ω).vectorMeasure_supported (siteVector x))
  have hmoments : ∀ n : ℕ, Measurable (fun ω => ∫ t : ℝ, t ^ n ∂μ ω) := by
    intro n
    have hcoord := basisPower_coord_measurable coupling x n x
    have hmoment : ∀ ω : Configuration d,
        (∫ t : ℝ, t ^ n ∂μ ω) =
          (((hamiltonian coupling ω ^ n) (siteVector x)) x).re := by
      intro ω
      change (∫ t : ℝ, t ^ n ∂(S ω).vectorMeasure (siteVector x)) = _
      rw [(S ω).vectorMeasure_moments]
      rw [inner_siteVector_apply]
    have hreal : Measurable (Complex.re ∘ fun ω : Configuration d =>
        ((hamiltonian coupling ω ^ n) (siteVector x)) x) := by
      exact Complex.continuous_re.measurable.comp hcoord
    have hmomentFun : (fun ω : Configuration d => ∫ t : ℝ, t ^ n ∂μ ω) =
        (Complex.re ∘ fun ω : Configuration d =>
          ((hamiltonian coupling ω ^ n) (siteVector x)) x) := by
      funext ω
      exact hmoment ω
    rw [hmomentFun]
    exact hreal
  simpa only [μ] using
    hkernel (Configuration d) μ M hM hprob hsupport hmoments A hA

end AndersonAC.SolS9
