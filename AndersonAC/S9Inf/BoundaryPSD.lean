import AndersonAC.S9Inf.Resolvent

/-! Positive imaginary two-site forms and their boundary limits. -/

noncomputable section

open Matrix Filter
open scoped Topology ComplexConjugate

namespace AndersonAC.SolS9Inf

def twoSiteIm (g a k : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun i j =>
    if i = 0 then (if j = 0 then g.im else a.im)
    else (if j = 0 then a.im else k.im))

section Hilbert

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem green_two_site_psd (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) (v w : K)
    (hsym : inner ℂ v (green T z w) = inner ℂ w (green T z v)) :
    (twoSiteIm (inner ℂ v (green T z v)) (inner ℂ v (green T z w))
      (inner ℂ w (green T z w))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (twoSiteIm _ _ _)ᴴ = twoSiteIm _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoSiteIm, Matrix.conjTranspose]
  · intro u
    have hq := green_quadratic_im_nonneg T hT z hz
      ((u 0 : ℂ) • v + (u 1 : ℂ) • w)
    have heq : star u ⬝ᵥ (twoSiteIm (inner ℂ v (green T z v))
        (inner ℂ v (green T z w)) (inner ℂ w (green T z w))) *ᵥ u =
        (inner ℂ ((u 0 : ℂ) • v + (u 1 : ℂ) • w)
          (green T z ((u 0 : ℂ) • v + (u 1 : ℂ) • w))).im := by
      simp [twoSiteIm, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
        map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, ← hsym, Complex.mul_im]
      ring
    exact heq.symm ▸ hq

end Hilbert

/-- Closedness of the positive quadratic forms passes their positivity to
the finite scalar boundary values. -/
theorem two_site_boundary_psd {ι : Type*} (l : Filter ι) [l.NeBot]
    (g a k : ι → ℂ) (G A K : ℂ)
    (hg : Tendsto g l (𝓝 G)) (ha : Tendsto a l (𝓝 A)) (hk : Tendsto k l (𝓝 K))
    (hpsd : ∀ᶠ i in l, (twoSiteIm (g i) (a i) (k i)).PosSemidef) :
    (twoSiteIm G A K).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (twoSiteIm _ _ _)ᴴ = twoSiteIm _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoSiteIm, Matrix.conjTranspose]
  · intro u
    have hgim := Complex.continuous_im.continuousAt.tendsto.comp hg
    have haim := Complex.continuous_im.continuousAt.tendsto.comp ha
    have hkim := Complex.continuous_im.continuousAt.tendsto.comp hk
    have hlim : Tendsto (fun i => star u ⬝ᵥ (twoSiteIm (g i) (a i) (k i)) *ᵥ u) l
        (𝓝 (star u ⬝ᵥ (twoSiteIm G A K) *ᵥ u)) := by
      simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, twoSiteIm] using
        ((tendsto_const_nhds.mul
          ((hgim.mul tendsto_const_nhds).add (haim.mul tendsto_const_nhds))).add
          (tendsto_const_nhds.mul
            ((haim.mul tendsto_const_nhds).add (hkim.mul tendsto_const_nhds))))
    apply ge_of_tendsto hlim
    filter_upwards [hpsd] with i hi
    exact hi.dotProduct_mulVec_nonneg u

end AndersonAC.SolS9Inf
