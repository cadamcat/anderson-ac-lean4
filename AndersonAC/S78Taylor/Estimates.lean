import AndersonAC.S78Taylor.Resolvent

open Matrix WithLp
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace AndersonAC.SolS78
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma sandwich_diag_norm (g B : Matrix ι ι ℂ) (Q : ℝ)
    (hQ : 0 ≤ Q) (hsym : g.transpose = g)
    (hrow : ∀ i, ‖toLp 2 (g i)‖ ^ 2 ≤ Q) :
    ‖fun i => (g * B * g) i i‖ ≤ Q * ‖B‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  let v : ι → ℂ := g i
  have hsym' : ∀ j, g j i = g i j := by
    intro j
    exact congrArg (fun A : Matrix ι ι ℂ => A i j) hsym
  have he : (g * B * g) i i = v ⬝ᵥ B *ᵥ v := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, mulVec, dotProduct, v, hsym']
  have hn : ‖toLp 2 (star v)‖ = ‖toLp 2 v‖ := by
    simp only [EuclideanSpace.norm_eq, Pi.star_apply, norm_star]
  have hi : v ⬝ᵥ B *ᵥ v = inner ℂ (toLp 2 (star v)) (toLp 2 (B *ᵥ v)) := by
    rw [EuclideanSpace.inner_toLp_toLp, star_star, dotProduct_comm]
  rw [he, hi]
  calc
    ‖inner ℂ (toLp 2 (star v)) (toLp 2 (B *ᵥ v))‖ ≤
        ‖toLp 2 (star v)‖ * ‖toLp 2 (B *ᵥ v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖toLp 2 v‖ * (‖B‖ * ‖toLp 2 v‖) := by
      rw [hn]
      exact mul_le_mul_of_nonneg_left (B.l2_opNorm_mulVec (toLp 2 v)) (norm_nonneg _)
    _ = ‖toLp 2 v‖ ^ 2 * ‖B‖ := by ring
    _ ≤ Q * ‖B‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

lemma resolvent_difference (M : Matrix ι ι ℂ) (r z w : ι → ℂ) (t : ℝ)
    (hz : IsUnit (M - (t : ℂ) • diagonal (r + z)).det)
    (hw : IsUnit (M - (t : ℂ) • diagonal (r + w)).det) :
    resetInverse M (r + z) t - resetInverse M (r + w) t =
      (t : ℂ) • (resetInverse M (r + z) t * diagonal (z - w) *
        resetInverse M (r + w) t) := by
  let A := M - (t : ℂ) • diagonal (r + z)
  let B := M - (t : ℂ) • diagonal (r + w)
  let G := resetInverse M (r + z) t
  let H := resetInverse M (r + w) t
  have hGA : G * A = 1 := Matrix.nonsing_inv_mul _ hz
  have hBH : B * H = 1 := Matrix.mul_nonsing_inv _ hw
  have hBA : B - A = (t : ℂ) • diagonal (z - w) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [A, B, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, diagonal_apply_eq,
        Pi.add_apply, Pi.sub_apply]
      ring
    · simp [A, B, hij]
  change G - H = (t : ℂ) • (G * diagonal (z - w) * H)
  calc
    G - H = G * (B - A) * H := by
      rw [mul_sub, sub_mul, Matrix.mul_assoc, hBH, mul_one, hGA, one_mul]
    _ = _ := by rw [hBA]; simp only [Matrix.mul_smul, Matrix.smul_mul]

lemma resolvent_taylor_matrix (M : Matrix ι ι ℂ) (r z : ι → ℂ) (t : ℝ)
    (h0 : IsUnit (M - (t : ℂ) • diagonal r).det)
    (hz : IsUnit (M - (t : ℂ) • diagonal (r + z)).det) :
    resetInverse M (r + z) t = resetInverse M r t +
      (t : ℂ) • (resetInverse M r t * diagonal z * resetInverse M r t) +
      (t : ℂ) ^ 2 • (resetInverse M r t *
        (diagonal z * resetInverse M (r + z) t * diagonal z) * resetInverse M r t) := by
  let g := resetInverse M r t
  let G := resetInverse M (r + z) t
  let Z := diagonal z
  have hl : G - g = (t : ℂ) • (G * Z * g) := by
    simpa using resolvent_difference M r z 0 t hz (by simpa using h0)
  have hr : G - g = (t : ℂ) • (g * Z * G) := by
    have h : g - G = (t : ℂ) • (g * diagonal (-z) * G) := by
      simpa only [add_zero, zero_sub] using resolvent_difference M r 0 z t (by simpa using h0) hz
    have hnZ : diagonal (-z) = -Z := by
      ext i j
      by_cases hij : i = j <;> simp [Z, hij]
    rw [hnZ, mul_neg, neg_mul, smul_neg] at h
    simpa only [neg_sub, neg_neg] using congrArg Neg.neg h
  change G = g + (t : ℂ) • (g * Z * g) + (t : ℂ) ^ 2 • (g * (Z * G * Z) * g)
  calc
    G = g + (t : ℂ) • (g * Z * G) := by rw [← hr]; abel
    _ = g + (t : ℂ) • (g * Z * g) + (t : ℂ) • (g * Z * (G - g)) := by
      rw [mul_sub, smul_sub]
      abel
    _ = g + (t : ℂ) • (g * Z * g) + (t : ℂ) ^ 2 • (g * (Z * G * Z) * g) := by
      rw [hl, Matrix.mul_smul, smul_smul, pow_two]
      simp only [Matrix.mul_assoc]

lemma linear_diag (g : Matrix ι ι ℂ) (z : ι → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hsym : g.transpose = g) :
    (fun i => ((t : ℂ) • (g * diagonal z * g)) i i) =
      (squareKernel ((Real.sqrt t : ℂ) • g)).mulVec z := by
  ext i
  have hs : ∀ j, g j i = g i j := fun j => congrArg (fun A : Matrix ι ι ℂ => A i j) hsym
  change (t : ℂ) * (g * diagonal z * g) i i = ∑ j, ((Real.sqrt t : ℂ) * g i j) ^ 2 * z j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, hs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ht' : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt ht
  rw [mul_pow, ht']
  ring

end AndersonAC.SolS78
