import AndersonAC.S2.InverseCoreStatement

noncomputable section
open scoped ComplexOrder
open AndersonAC.S2
universe u

namespace AndersonAC.SolS2

section Projection
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma constantProjection_mulVec_formula (x : ι → ℂ) :
    constantProjection.mulVec x =
      fun _ => (Fintype.card ι : ℂ)⁻¹ * ∑ i, x i := by
  ext i
  simp [constantProjection, Matrix.mulVec, dotProduct, Finset.mul_sum]

lemma constantProjection_mulVec_const (c : ℂ) :
    constantProjection.mulVec (fun _ : ι => c) = fun _ => c := by
  classical
  by_cases hι : Nonempty ι
  · have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [constantProjection_mulVec_formula]
    ext i
    simp [Finset.sum_const, hcard]
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    funext i
    exact isEmptyElim i

lemma constantProjection_mulVec_sum (x : ι → ℂ) :
    ∑ i, (constantProjection.mulVec x) i = ∑ i, x i := by
  classical
  by_cases hι : Nonempty ι
  · have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [constantProjection_mulVec_formula]
    simp [hcard]
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    simp

lemma constantProjection_mulVec_of_sum_eq_zero {x : ι → ℂ}
    (hx : ∑ i, x i = 0) : constantProjection.mulVec x = 0 := by
  rw [constantProjection_mulVec_formula, hx]
  ext i
  simp

lemma constantProjection_mulVec_idem (x : ι → ℂ) :
    constantProjection.mulVec (constantProjection.mulVec x) =
      constantProjection.mulVec x := by
  calc
    constantProjection.mulVec (constantProjection.mulVec x) =
        constantProjection.mulVec
          (fun _ => (Fintype.card ι : ℂ)⁻¹ * ∑ i, x i) := by
      rw [constantProjection_mulVec_formula x]
    _ = fun _ => (Fintype.card ι : ℂ)⁻¹ * ∑ i, x i :=
      constantProjection_mulVec_const _
    _ = constantProjection.mulVec x := by
      rw [constantProjection_mulVec_formula x]

lemma sum_mulVec_eq_zero {D : Matrix ι ι ℂ} (hD : ConnectedLaplacian D)
    (x : ι → ℂ) : ∑ i, (D.mulVec x) i = 0 := by
  have hone : D.mulVec (fun _ : ι => (1 : ℂ)) = 0 :=
    (hD.2 (fun _ : ι => (1 : ℂ))).2 ⟨1, rfl⟩
  have hcomm := hD.1.isHermitian.star_dotProduct_mulVec_comm
    (fun _ : ι => (1 : ℂ)) x
  have hstar : star (star (fun _ : ι => (1 : ℂ)) ⬝ᵥ D.mulVec x) = 0 := by
    rw [hcomm]
    simp [hone]
  have hdot : star (fun _ : ι => (1 : ℂ)) ⬝ᵥ D.mulVec x = 0 := star_eq_zero.mp hstar
  simpa [dotProduct] using hdot

lemma regularized_mulVec_injective {D : Matrix ι ι ℂ}
    (hD : ConnectedLaplacian D) :
    Function.Injective ((D + constantProjection).mulVec) := by
  intro x y hxy
  have hsub : (D + constantProjection).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hxy
  have hproj : constantProjection.mulVec (x - y) = 0 := by
    have h := congrArg constantProjection.mulVec hsub
    rw [Matrix.add_mulVec] at h
    rw [Matrix.mulVec_add,
      constantProjection_mulVec_of_sum_eq_zero (sum_mulVec_eq_zero hD (x - y)),
      constantProjection_mulVec_idem] at h
    simpa using h
  have hDzero : D.mulVec (x - y) = 0 := by
    have h := hsub
    rw [Matrix.add_mulVec, hproj] at h
    simpa using h
  obtain ⟨c, hc⟩ := (hD.2 (x - y)).mp hDzero
  have hconst : constantProjection.mulVec (x - y) = x - y := by
    rw [hc]
    exact constantProjection_mulVec_const c
  have hzero : x - y = 0 := by
    rw [← hconst]
    exact hproj
  exact sub_eq_zero.mp hzero

lemma quadraticForm_nonneg {D : Matrix ι ι ℂ} (hD : ConnectedLaplacian D)
    (x : ι → ℂ) : 0 ≤ quadraticForm D x := by
  have h := (Complex.nonneg_iff.mp (hD.1.dotProduct_mulVec_nonneg x)).1
  simpa [quadraticForm, pairing, dotProduct] using h

lemma pairing_sub_left (x y z : ι → ℂ) :
    pairing (x - y) z = pairing x z - pairing y z := by
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [sub_mul]

lemma pairing_sub_right (x y z : ι → ℂ) :
    pairing x (y - z) = pairing x y - pairing x z := by
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_sub]

lemma pairing_swap (x y : ι → ℂ) : pairing x y = star (pairing y x) := by
  simp [pairing, dotProduct, mul_comm]

lemma pairing_mulVec_hermitian {D : Matrix ι ι ℂ} (hD : D.IsHermitian)
    (x y : ι → ℂ) :
    pairing x (D.mulVec y) = pairing (D.mulVec x) y := by
  have h := congrArg star (hD.star_dotProduct_mulVec_comm x y)
  simpa [pairing, dotProduct, mul_comm] using h

lemma quadraticForm_completion {D : Matrix ι ι ℂ} (hD : D.IsHermitian)
    (x f : ι → ℂ) :
    2 * (pairing x (D.mulVec f)).re - quadraticForm D f =
      quadraticForm D x - quadraticForm D (f - x) := by
  have hcross : (pairing f (D.mulVec x)).re =
      (pairing x (D.mulVec f)).re := by
    calc
      (pairing f (D.mulVec x)).re = (star (pairing (D.mulVec x) f)).re := by
        rw [pairing_swap]
      _ = (pairing (D.mulVec x) f).re := by simp
      _ = (pairing x (D.mulVec f)).re := by
        rw [← pairing_mulVec_hermitian hD x f]
  have hexpand : pairing (f - x) (D.mulVec (f - x)) =
      pairing f (D.mulVec f) - pairing f (D.mulVec x) -
        pairing x (D.mulVec f) + pairing x (D.mulVec x) := by
    simp only [Matrix.mulVec_sub, pairing_sub_left, pairing_sub_right]
    ring
  unfold quadraticForm
  rw [hexpand]
  simp only [Complex.sub_re, Complex.add_re]
  linarith [hcross]

end Projection

theorem InverseCore_proof : InverseCore := by
  intro ι instFin instDec D hD y hy
  let x : ι → ℂ := (D + constantProjection)⁻¹.mulVec y
  have hAinj : Function.Injective ((D + constantProjection).mulVec) :=
    regularized_mulVec_injective hD
  have hAunit : IsUnit (D + constantProjection) :=
    Matrix.mulVec_injective_iff_isUnit.mp hAinj
  letI : Invertible (D + constantProjection) := hAunit.invertible
  have hAx : (D + constantProjection).mulVec x = y := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hPy : constantProjection.mulVec y = 0 :=
    constantProjection_mulVec_of_sum_eq_zero (by simpa [Neutral] using hy)
  have hPx : constantProjection.mulVec x = 0 := by
    have h := congrArg constantProjection.mulVec hAx
    rw [Matrix.add_mulVec, Matrix.mulVec_add,
      constantProjection_mulVec_of_sum_eq_zero (sum_mulVec_eq_zero hD x),
      constantProjection_mulVec_idem, hPy] at h
    simpa using h
  have hDx : D.mulVec x = y := by
    simpa [Matrix.add_mulVec, hPx] using hAx
  have hxneutral : Neutral x := by
    change ∑ i, x i = 0
    rw [← constantProjection_mulVec_sum x, hPx]
    simp
  have hpseudo : (laplacianPseudoInverse D).mulVec y = x := by
    unfold laplacianPseudoInverse
    rw [Matrix.sub_mulVec, hPy]
    simp [x]
  have hq : quadraticForm (laplacianPseudoInverse D) y = quadraticForm D x := by
    unfold quadraticForm
    rw [hpseudo, ← hDx, ← pairing_mulVec_hermitian hD.1.isHermitian x x]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [hpseudo] using hDx
  · simpa only [hpseudo] using hxneutral
  · let S : Set ℝ := Set.range
      (fun f : ι → ℂ => 2 * (pairing y f).re - quadraticForm D f)
    have hbound (f : ι → ℂ) :
        2 * (pairing y f).re - quadraticForm D f ≤ quadraticForm D x := by
      rw [← hDx, ← pairing_mulVec_hermitian hD.1.isHermitian x f,
        quadraticForm_completion hD.1.isHermitian x f]
      exact sub_le_self _ (quadraticForm_nonneg hD (f - x))
    have hpair : (pairing y x).re = quadraticForm D x := by
      rw [← hDx, ← pairing_mulVec_hermitian hD.1.isHermitian x x]
      rfl
    have hmem : quadraticForm D x ∈ S := by
      change ∃ f, 2 * (pairing y f).re - quadraticForm D f = quadraticForm D x
      exact ⟨x, by rw [hpair]; ring⟩
    have hS : S.Nonempty := ⟨quadraticForm D x, hmem⟩
    have hSbound : BddAbove S := by
      refine ⟨quadraticForm D x, ?_⟩
      intro z hz
      rcases hz with ⟨f, rfl⟩
      exact hbound f
    have hsSup : sSup S = quadraticForm D x := by
      apply le_antisymm
      · apply csSup_le hS
        intro z hz
        rcases hz with ⟨f, rfl⟩
        exact hbound f
      · exact le_csSup hSbound hmem
    exact hq.trans hsSup.symm

end AndersonAC.SolS2
