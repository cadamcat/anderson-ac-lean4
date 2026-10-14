import AndersonAC.S9FiniteAvg.Kernel
import AndersonAC.S9FiniteAvg.RankOne
import AndersonAC.S9FiniteAvg.Split
import AndersonAC.S9Fin.FiniteAveragingStatement

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9
open scoped Matrix ComplexConjugate

namespace AndersonAC.SolS9

universe u
variable {n : Type u} [Fintype n] [DecidableEq n]

def randomSiteMatrix (K : Matrix n n ℂ) (coupling : ℝ) (ω : n → SingleSite) :
    Matrix n n ℂ :=
  K + Matrix.diagonal (fun j => ((coupling * (ω j : ℝ) : ℝ) : ℂ))

def siteBaseMatrix (K : Matrix n n ℂ) (coupling : ℝ) (i : n)
    (tail : OtherSiteIndex i → SingleSite) : Matrix n n ℂ :=
  K + Matrix.diagonal (fun j =>
    (((if hj : j = i then (0 : ℝ) else coupling * (tail ⟨j, hj⟩ : ℝ)) : ℝ) : ℂ))

lemma real_diagonal_isHermitian (d : n → ℝ) :
    (Matrix.diagonal (fun j => (d j : ℂ))).IsHermitian := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [Matrix.IsHermitian, Matrix.diagonal_apply]
  · simp [Matrix.IsHermitian, Matrix.diagonal_apply, hjk, eq_comm]

lemma randomSiteMatrix_isHermitian (K : Matrix n n ℂ) (hK : K.IsHermitian)
    (coupling : ℝ) (ω : n → SingleSite) :
    (randomSiteMatrix K coupling ω).IsHermitian := by
  exact hK.add (real_diagonal_isHermitian (fun j => coupling * (ω j : ℝ)))

lemma randomSiteMatrix_eq_contract (K : Matrix n n ℂ) (coupling : ℝ)
    (ω : n → SingleSite) :
    randomSiteMatrix K coupling ω =
      K + (coupling : ℂ) • Matrix.diagonal (fun j => ((ω j : ℝ) : ℂ)) := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [randomSiteMatrix, Matrix.diagonal_apply]
  · simp [randomSiteMatrix, Matrix.diagonal_apply, hjk]

lemma siteBaseMatrix_isHermitian (K : Matrix n n ℂ) (hK : K.IsHermitian)
    (coupling : ℝ) (i : n) (tail : OtherSiteIndex i → SingleSite) :
    (siteBaseMatrix K coupling i tail).IsHermitian := by
  exact hK.add (real_diagonal_isHermitian (fun j =>
    if hj : j = i then 0 else coupling * (tail ⟨j, hj⟩ : ℝ)))

lemma randomSiteMatrix_split (K : Matrix n n ℂ) (coupling : ℝ) (i : n)
    (head : OwnSiteIndex i → SingleSite) (tail : OtherSiteIndex i → SingleSite) :
    randomSiteMatrix K coupling ((siteSplitEquiv i).symm (head, tail)) =
      siteBaseMatrix K coupling i tail +
        ((coupling * (head ⟨i, rfl⟩ : ℝ) : ℝ) : ℂ) • siteProjection i := by
  have hpotential (j : n) :
      ((coupling * (((siteSplitEquiv i).symm (head, tail) j : SingleSite) : ℝ) : ℝ) : ℂ) =
        if hj : j = i then
          ((coupling * (head ⟨i, rfl⟩ : ℝ) : ℝ) : ℂ)
        else ((coupling * (tail ⟨j, hj⟩ : ℝ) : ℝ) : ℂ) := by
    by_cases hj : j = i
    · subst j
      rw [siteSplitEquiv_symm_apply_own i head tail ⟨i, rfl⟩]
      simp
    · rw [siteSplitEquiv_symm_apply_other i head tail ⟨j, hj⟩]
      simp [hj]
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hji : j = i
    · subst j
      simp [randomSiteMatrix, siteBaseMatrix, siteProjection, hpotential]
    · simp [randomSiteMatrix, siteBaseMatrix, siteProjection, hji, hpotential]
  · simp [randomSiteMatrix, siteBaseMatrix, siteProjection, Matrix.diagonal_apply, hjk]

lemma finiteScalarAveraging_head (K : Matrix n n ℂ) (hK : K.IsHermitian)
    (coupling E η : ℝ) (hc : 0 < coupling) (hη : 0 < η) (i : n)
    (tail : OtherSiteIndex i → SingleSite) :
    (∫ head : OwnSiteIndex i → SingleSite,
      scalarQ (randomSiteMatrix K coupling ((siteSplitEquiv i).symm (head, tail))) E η i
        ∂ownSiteLaw i) ≤ Real.pi / (2 * coupling) := by
  let H₀ := siteBaseMatrix K coupling i tail
  let z := (matrixResolvent H₀ E η i i)⁻¹
  let γ := -z.im
  let g : SingleSite → ℝ := fun s =>
    γ / ((coupling * (s : ℝ) + z.re) ^ 2 + γ ^ 2)
  have hH₀ : H₀.IsHermitian := by
    exact siteBaseMatrix_isHermitian K hK coupling i tail
  have hγ : 0 < γ := by
    simpa [γ, z, H₀] using matrixResolvent_inverse_diagonal_im_neg H₀ hH₀ E η hη i
  have hgcont : Continuous g := by
    dsimp [g]
    have hden : ∀ s : SingleSite,
        (coupling * (s : ℝ) + z.re) ^ 2 + γ ^ 2 ≠ 0 := by
      intro s
      positivity
    exact continuous_const.div (by fun_prop) hden
  have hkernel :
      (fun head : OwnSiteIndex i → SingleSite =>
        scalarQ (randomSiteMatrix K coupling ((siteSplitEquiv i).symm (head, tail))) E η i) =
      fun head => g (head ⟨i, rfl⟩) := by
    funext head
    have hpert := randomSiteMatrix_split K coupling i head tail
    have hfull : (randomSiteMatrix K coupling ((siteSplitEquiv i).symm (head, tail))).IsHermitian :=
      randomSiteMatrix_isHermitian K hK coupling ((siteSplitEquiv i).symm (head, tail))
    have h := scalarQ_rankOne_cauchy_kernel H₀
      (randomSiteMatrix K coupling ((siteSplitEquiv i).symm (head, tail))) hH₀ hfull
      E η (coupling * (head ⟨i, rfl⟩ : ℝ)) hη i hpert
    simpa [g, γ, z, H₀, Complex.add_re, Complex.ofReal_re] using h
  rw [hkernel, integral_ownSite_eval i g hgcont.aestronglyMeasurable]
  exact uniformSite_cauchy_integral_bound coupling z.re γ hc hγ

theorem finiteScalarAveraging_proof : FiniteScalarAveragingStatement.{u} := by
  unfold FiniteScalarAveragingStatement
  intro n hn hne K hK coupling E η hc hη i
  let μ := Measure.pi (fun _ : n => uniformSite)
  let μtail := Measure.pi (fun _ : OtherSiteIndex i => uniformSite)
  letI : IsProbabilityMeasure (ownSiteLaw i) := by
    dsimp [ownSiteLaw]
    infer_instance
  letI : IsProbabilityMeasure μtail := by
    dsimp [μtail]
    infer_instance
  let f : (n → SingleSite) → ℝ := fun ω => scalarQ (randomSiteMatrix K coupling ω) E η i
  have hM : Measurable (fun ω : n → SingleSite => randomSiteMatrix K coupling ω) := by
    unfold randomSiteMatrix
    fun_prop
  have hfmeas : Measurable f := scalarQ_measurable _ hM E η i
  have hfbound (ω : n → SingleSite) : ‖f ω‖ ≤ η⁻¹ := by
    dsimp [f]
    change |scalarQ (randomSiteMatrix K coupling ω) E η i| ≤ η⁻¹
    rw [abs_of_nonneg
      (scalarQ_nonneg _ (randomSiteMatrix_isHermitian K hK coupling ω) E η hη i)]
    calc
      scalarQ (randomSiteMatrix K coupling ω) E η i ≤
          ‖(matrixResolvent (randomSiteMatrix K coupling ω) E η) i i‖ := by
        exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
      _ ≤ matrixOpNorm (matrixResolvent (randomSiteMatrix K coupling ω) E η) :=
        matrix_entry_norm_le _ i i
      _ ≤ η⁻¹ := matrixResolvent_norm_pos _
        (randomSiteMatrix_isHermitian K hK coupling ω) E η hη
  have hfint : Integrable f μ :=
    Integrable.of_bound hfmeas.aestronglyMeasurable (η⁻¹)
      (Filter.Eventually.of_forall hfbound)
  have hcontract :
      (fun ω : n → SingleSite =>
        scalarQ (K + (coupling : ℂ) • Matrix.diagonal (fun j => ((ω j : ℝ) : ℂ))
          : Matrix n n ℂ) E η i) = f := by
    funext ω
    dsimp [f]
    exact congrArg (fun H : Matrix n n ℂ => scalarQ H E η i)
      (randomSiteMatrix_eq_contract K coupling ω).symm
  rw [hcontract]
  let F : ((OwnSiteIndex i → SingleSite) × (OtherSiteIndex i → SingleSite)) → ℝ :=
    fun p => f ((siteSplitEquiv i).symm p)
  have hchange :
      (∫ ω, f ω ∂μ) =
        ∫ p, F p ∂(ownSiteLaw i).prod μtail := by
    simpa [F, μ, μtail] using
      (measurePreserving_siteSplitEquiv i).integral_comp' F
  have hFint : Integrable F ((ownSiteLaw i).prod μtail) := by
    have h := (measurePreserving_siteSplitEquiv i).symm.integrable_comp_of_integrable hfint
    simpa [F, μtail, Function.comp_def] using h
  have hFubini := integral_prod_symm F hFint
  let A : (OtherSiteIndex i → SingleSite) → ℝ := fun tail =>
    ∫ head : OwnSiteIndex i → SingleSite,
      f ((siteSplitEquiv i).symm (head, tail)) ∂ownSiteLaw i
  have hAint : Integrable A μtail := by
    have h := hFint.integral_prod_right
    simpa [A, F, μtail] using h
  have hA_bound (tail : OtherSiteIndex i → SingleSite) :
      A tail ≤ Real.pi / (2 * coupling) := by
    exact finiteScalarAveraging_head K hK coupling E η hc hη i tail
  calc
    (∫ ω, f ω ∂μ) = ∫ tail, A tail ∂μtail := by
      rw [hchange, hFubini]
    _ ≤ ∫ tail, Real.pi / (2 * coupling) ∂μtail :=
      integral_mono_ae hAint (integrable_const _) (Filter.Eventually.of_forall hA_bound)
    _ = Real.pi / (2 * coupling) := by simp [μtail]

end AndersonAC.SolS9
