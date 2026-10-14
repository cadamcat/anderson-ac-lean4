import AndersonAC.S9Inf.Model

/-! The actual rank-one kernel formula and its finite boundary passage. -/

noncomputable section

open OAI.Anderson Filter
open scoped Topology

namespace AndersonAC.SolS9Inf

theorem scalarGreen_update {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (s : SingleSite) (z : ℂ) (hz : z.im ≠ 0) :
    scalarGreen coupling (Function.update ω x s) y y z =
      scalarGreen coupling ω y y z -
        ((coupling * ((s : ℝ) - (ω x : ℝ)) : ℝ) : ℂ) *
          scalarGreen coupling ω x y z ^ 2 /
        (1 + ((coupling * ((s : ℝ) - (ω x : ℝ)) : ℝ) : ℂ) *
          scalarGreen coupling ω x x z) := by
  let h : ℝ := coupling * ((s : ℝ) - (ω x : ℝ))
  let A := hamiltonian coupling ω - z • (1 : StateSpace d →L[ℂ] StateSpace d)
  have hA : IsUnit A := shifted_isUnit _ (hamiltonian_isSelfAdjoint coupling ω) z hz
  have hchange : hamiltonian coupling (Function.update ω x s) -
      z • (1 : StateSpace d →L[ℂ] StateSpace d) =
      A + (h : ℂ) • InnerProductSpace.rankOne ℂ (basis x) (basis x) := by
    rw [hamiltonian_update]
    dsimp [A, h]
    abel
  have hB : IsUnit (A + (h : ℂ) • InnerProductSpace.rankOne ℂ (basis x) (basis x)) := by
    rw [← hchange]
    exact shifted_isUnit _ (hamiltonian_isSelfAdjoint coupling (Function.update ω x s)) z hz
  have hvec := inverse_rank_one_apply A hA (basis x) (basis y) (basis_ne_zero x) (h : ℂ) hB
  have hscalar := congrArg (fun v : StateSpace d => inner ℂ (basis y) v) hvec
  rw [← hchange] at hscalar
  simp only [inner_sub_right, inner_smul_right] at hscalar
  change scalarGreen coupling (Function.update ω x s) y y z =
    scalarGreen coupling ω y y z -
      ((h : ℂ) * scalarGreen coupling ω x y z /
        (1 + (h : ℂ) * scalarGreen coupling ω x x z)) * scalarGreen coupling ω y x z
      at hscalar
  rw [← scalarGreen_symmetric coupling ω z hz x y] at hscalar
  simpa only [h, pow_two, div_mul_eq_mul_div, mul_assoc] using hscalar

def hasBoundary (f : ℂ → ℂ) (E : ℝ) (w : ℂ) : Prop :=
  Tendsto (fun η : ℝ => f ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 w)

theorem real_rank_one_denominator_ne_zero (g : ℂ) (h : ℝ) (hg : 0 < g.im) :
    1 + (h : ℂ) * g ≠ 0 := by
  intro heq
  have hi := congrArg Complex.im heq
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at hi
  have hh : h = 0 := (mul_eq_zero.mp hi).resolve_right hg.ne'
  simp [hh] at heq

theorem scalarGreen_update_boundary {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (s : SingleSite) (E : ℝ) (g a k : ℂ)
    (hg : hasBoundary (scalarGreen coupling ω x x) E g)
    (ha : hasBoundary (scalarGreen coupling ω x y) E a)
    (hk : hasBoundary (scalarGreen coupling ω y y) E k) (hgim : 0 < g.im) :
    hasBoundary (scalarGreen coupling (Function.update ω x s) y y) E
      (k - ((coupling * ((s : ℝ) - (ω x : ℝ)) : ℝ) : ℂ) * a ^ 2 /
        (1 + ((coupling * ((s : ℝ) - (ω x : ℝ)) : ℝ) : ℂ) * g)) := by
  let h : ℝ := coupling * ((s : ℝ) - (ω x : ℝ))
  have hd := real_rank_one_denominator_ne_zero g h hgim
  have hlim := hk.sub (((tendsto_const_nhds (x := (h : ℂ))).mul (ha.pow 2)).div
    ((tendsto_const_nhds (x := (1 : ℂ))).add
      ((tendsto_const_nhds (x := (h : ℂ))).mul hg)) hd)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  symm
  apply scalarGreen_update
  simpa using (ne_of_gt (show 0 < η from hη))

theorem scalarGreen_boundary_psd {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (E : ℝ) (g a k : ℂ)
    (hg : hasBoundary (scalarGreen coupling ω x x) E g)
    (ha : hasBoundary (scalarGreen coupling ω x y) E a)
    (hk : hasBoundary (scalarGreen coupling ω y y) E k) :
    (twoSiteIm g a k).PosSemidef := by
  apply two_site_boundary_psd (𝓝[>] (0 : ℝ)) _ _ _ g a k hg ha hk
  filter_upwards [self_mem_nhdsWithin] with η hη
  apply scalarGreen_two_site_psd
  simpa using (show 0 < η from hη)

end AndersonAC.SolS9Inf
