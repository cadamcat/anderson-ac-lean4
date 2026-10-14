import AndersonAC.S3.ConvexExtension
import AndersonAC.S3.HelperStatements

/-!
Joint energy-shell volumes near the band bottom (§3, lines 456–526 of
`03-initialization.tex`): in the coordinates `x_j = sin(k_j + ζ_j/2)` the two
dispersions differ by a linear functional, the joint shell lies in a slab of
width `O(max(s₁,s₂)/|ζ|)`, and each hyperplane slice of the narrower shell has
volume `O(min(s₁,s₂))` by strong convexity (including tangential slices).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace AndersonAC.S3

/-! ### Quadratic lower bound and coercivity of the convex extension -/

theorem extended_coordinate_lower (sign ζ u : ℝ) (hζ : |ζ| ≤ 1 / 2) :
    slicedCoordinate sign ζ 0 + slicedCoordinateDeriv sign ζ 0 * u + u ^ 2 / 2 ≤
      extendedCoordinate sign ζ u := by
  set a := slicedCoordinate sign ζ 0
  set a' := slicedCoordinateDeriv sign ζ 0
  set F : ℝ → ℝ := fun u => extendedCoordinate sign ζ u - (a + a' * u + u ^ 2 / 2) with hFdef
  have hF0 : F 0 = 0 := by simp [F, a, extendedCoordinate]
  have hD0 : extendedCoordinateDeriv sign ζ 0 = a' := by simp [a', extendedCoordinateDeriv]
  have hquad : ∀ u, HasDerivAt (fun x : ℝ => a + a' * x + x ^ 2 / 2) (a' + u) u := by
    intro u
    have hbase1 := ((hasDerivAt_const u a).add ((hasDerivAt_id u).const_mul a'))
    have h1 : HasDerivAt (fun x : ℝ => a + a' * x) a' u := by
      convert hbase1 using 1
      · ext x
        simp only [Pi.add_apply, id_eq]
      · simp
    have hbase2 := (((hasDerivAt_id u).pow 2).div_const (2 : ℝ))
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) u u := by
      convert hbase2 using 1
      · ext x
        simp only [Pi.pow_apply, id_eq]
      · simp
    have h := h1.add h2
    have hfun : (fun x : ℝ => a + a' * x) + (fun x : ℝ => x ^ 2 / 2) =
        (fun x : ℝ => a + a' * x + x ^ 2 / 2) := by
      funext x
      simp only [Pi.add_apply]
    rw [hfun] at h
    exact h
  have hFd : ∀ u, HasDerivAt F (extendedCoordinateDeriv sign ζ u - a' - u) u := by
    intro u
    have h := (extended_coordinate_hasDerivAt sign ζ u).sub (hquad u)
    have hfun : (extendedCoordinate sign ζ - fun x => a + a' * x + x ^ 2 / 2) = F := by
      funext x; simp [F, Pi.sub_apply]
    rw [hfun] at h
    convert h using 1
    ring
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun u => (hFd u).continuousAt
  have growth {u v : ℝ} (huv : u ≤ v) :
      v - u ≤ extendedCoordinateDeriv sign ζ v - extendedCoordinateDeriv sign ζ u :=
    extended_coordinate_derivative_growth sign ζ hζ huv
  suffices hF : 0 ≤ F u by
    have hFu : F u = extendedCoordinate sign ζ u - (a + a' * u + u ^ 2 / 2) := rfl
    linarith
  rcases lt_trichotomy u 0 with hu | hu | hu
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope F
      (fun u => extendedCoordinateDeriv sign ζ u - a' - u) hu hFc.continuousOn
      (fun x _ => hFd x)
    have hg := growth hc.2.le
    rw [hD0] at hg
    have hneg : extendedCoordinateDeriv sign ζ c - a' - c ≤ 0 := by linarith
    rw [hcd, hF0] at hneg
    have hpos : 0 < 0 - u := by linarith
    have := (div_nonpos_iff.mp hneg)
    rcases this with h | h
    · linarith [h.1, h.2]
    · nlinarith [h.1, h.2]
  · subst hu; simp [hF0]
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope F
      (fun u => extendedCoordinateDeriv sign ζ u - a' - u) hu hFc.continuousOn
      (fun x _ => hFd x)
    have hg := growth hc.1.le
    rw [hD0] at hg
    have hnn : 0 ≤ extendedCoordinateDeriv sign ζ c - a' - c := by linarith
    rw [hcd, hF0] at hnn
    have hpos : 0 < u - 0 := by linarith
    have := (div_nonneg_iff.mp hnn)
    rcases this with h | h
    · linarith [h.1]
    · linarith [h.2]

theorem extended_coordinate_ge {sign : ℝ} (hsign : |sign| ≤ 1) (ζ u : ℝ) (hζ : |ζ| ≤ 1 / 2) :
    -6 + u ^ 2 / 4 ≤ extendedCoordinate sign ζ u := by
  have h := extended_coordinate_lower sign ζ u hζ
  have ha : slicedCoordinate sign ζ 0 = -2 * Real.cos (ζ / 2) := by
    simp [slicedCoordinate]
  have ha' : slicedCoordinateDeriv sign ζ 0 = sign * 2 * Real.sin (ζ / 2) := by
    simp [slicedCoordinateDeriv]
  rw [ha, ha'] at h
  have hc := Real.cos_le_one (ζ / 2)
  have hs1 := Real.sin_le_one (ζ / 2)
  have hs2 := Real.neg_one_le_sin (ζ / 2)
  have hsg := abs_le.mp hsign
  have hprod : |sign * 2 * Real.sin (ζ / 2) * u| ≤ 2 * |u| := by
    rw [abs_mul, abs_mul, abs_mul]
    have : |Real.sin (ζ / 2)| ≤ 1 := Real.abs_sin_le_one _
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have := mul_le_mul hsign this (abs_nonneg _) zero_le_one
    nlinarith [abs_nonneg u, abs_nonneg sign]
  have hl := neg_abs_le (sign * 2 * Real.sin (ζ / 2) * u)
  have hsq : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  nlinarith [abs_nonneg u, sq_nonneg (|u| / 2 - 2)]

theorem extended_dispersion_ge {d : ℕ} {sign : ℝ} (hsign : |sign| ≤ 1) (ζ : Frequency d)
    (hζ : ∀ j, |ζ j| ≤ 1 / 2) (x : EuclideanSpace ℝ (Fin d)) :
    -6 * (d : ℝ) + ‖x‖ ^ 2 / 4 ≤ extendedDispersion sign ζ x := by
  unfold extendedDispersion
  rw [EuclideanSpace.real_norm_sq_eq]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
    (fun j _ => extended_coordinate_ge hsign (ζ j) (x j) (hζ j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_div] at h
  linarith

theorem extended_dispersion_continuous {d : ℕ} (sign : ℝ) (ζ : Frequency d) :
    Continuous (extendedDispersion sign ζ) := by
  unfold extendedDispersion
  refine continuous_finsetSum _ fun j _ => ?_
  exact (extended_coordinate_continuous sign (ζ j)).comp (PiLp.continuous_apply 2 _ j)

/-- Strong convexity with a global minimizer gives quadratic growth away from it. -/
theorem strongConvex_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {c : ℝ} (hg : StrongConvexOn Set.univ c g) {y₀ : E}
    (hmin : ∀ y, g y₀ ≤ g y) (y : E) : c / 4 * ‖y - y₀‖ ^ 2 ≤ g y - g y₀ := by
  obtain ⟨_, huni⟩ := hg
  have h := huni (Set.mem_univ y) (Set.mem_univ y₀)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
  have hm := hmin ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y₀)
  simp only [smul_eq_mul] at h
  nlinarith [h, hm]

end AndersonAC.S3
