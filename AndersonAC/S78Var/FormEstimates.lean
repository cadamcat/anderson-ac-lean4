import AndersonAC.S78Var.FrobeniusBounds
import AndersonAC.S78Var.OperatorBounds
import AndersonAC.S78Comm.Commutator

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

def weight {ι : Type} [DecidableEq ι] (p : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => (Real.sqrt (p i) : ℂ)

def weightInv {ι : Type} [DecidableEq ι] (p : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => (Real.sqrt (p i) : ℂ)⁻¹

def comm {ι : Type} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι ℂ) (f : ι → ℝ) :=
  Matrix.diagonal (fun i => (f i : ℂ)) * h - h * Matrix.diagonal (fun i => (f i : ℂ))

theorem weight_inverse {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) : weight p * weightInv p = 1 ∧ weightInv p * weight p = 1 := by
  have hn : ∀ i, (Real.sqrt (p i) : ℂ) ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hp i)))
  constructor <;> simp [weight, weightInv, Matrix.diagonal_mul_diagonal, hn]

theorem weight_norm {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (c C : ℝ) (hc : 0 < c) (hp : ∀ i, c ≤ p i ∧ p i ≤ C) :
    ‖weight p‖ ≤ Real.sqrt C ∧ ‖weightInv p‖ ≤ (Real.sqrt c)⁻¹ := by
  constructor
  · rw [weight, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hp i).2
  · rw [weightInv, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_anti₀ (Real.sqrt_pos.mpr hc) (Real.sqrt_le_sqrt (hp i).1)

theorem wardEnergy_nonneg {ι : Type} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (h : Matrix ι ι ℂ) (f : ι → ℝ) :
    0 ≤ AndersonAC.S78.wardEnergy Finset.univ p h f := by
  unfold AndersonAC.S78.wardEnergy
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (hp i) (hp j)) (sq_nonneg _)) (sq_nonneg _)

theorem weighted_comm_sq {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (h : Matrix ι ι ℂ) (f : ι → ℝ) :
    hsSq (weight p * comm h f * weight p) =
      2 * AndersonAC.S78.wardEnergy Finset.univ p h f := by
  simp only [hsSq, weight, comm, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : ∀ i j, (f i : ℂ) * h i j - h i j * (f j : ℂ) =
      ((f i - f j : ℝ) : ℂ) * h i j := fun i j => by push_cast; ring
  simp only [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    Real.sq_sqrt (hp _), sq_abs]
  simp only [AndersonAC.S78.wardEnergy]
  rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The p weights stay inside the two operator conjugations. -/
theorem ward_form_conjugation {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h h' A B : Matrix ι ι ℂ) (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (s si d : ℝ) (hs : 0 ≤ s) (hsi : 0 ≤ si) (hd : 0 ≤ d)
    (hS : ‖weight p‖ ≤ s) (hSi : ‖weightInv p‖ ≤ si)
    (hA : ‖A - 1‖ ≤ d) (hB : ‖B - 1‖ ≤ d)
    (hcomm : ∀ f, comm h' f = A * comm h f * B) :
    ∀ f, AndersonAC.S78.wardEnergy Finset.univ p h' f ≤
      (1 + s * si * d) ^ 4 * AndersonAC.S78.wardEnergy Finset.univ p h f := by
  intro f
  obtain ⟨hPPi, hPiP⟩ := weight_inverse p hp
  let U := weight p * A * weightInv p
  let V := weightInv p * B * weight p
  have hU : ‖U‖ ≤ 1 + s * si * d := by
    have he : U = 1 + weight p * (A - 1) * weightInv p := by
      dsimp [U]; rw [mul_sub, sub_mul, mul_one, hPPi]; abel
    calc ‖U‖ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖weight p * (A - 1) * weightInv p‖ := by rw [he]; exact norm_add_le _ _
      _ ≤ 1 + (‖weight p‖ * ‖A - 1‖) * ‖weightInv p‖ := by
        apply add_le_add (by simp)
        exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 + s * si * d := by
        have hh := mul_le_mul (mul_le_mul hS hA (norm_nonneg _) hs) hSi (norm_nonneg _) (mul_nonneg hs hd)
        nlinarith
  have hV : ‖V‖ ≤ 1 + s * si * d := by
    have he : V = 1 + weightInv p * (B - 1) * weight p := by
      dsimp [V]; rw [mul_sub, sub_mul, mul_one, hPiP]; abel
    calc ‖V‖ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖weightInv p * (B - 1) * weight p‖ := by rw [he]; exact norm_add_le _ _
      _ ≤ 1 + (‖weightInv p‖ * ‖B - 1‖) * ‖weight p‖ := by
        apply add_le_add (by simp)
        exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 + s * si * d := by
        have hh := mul_le_mul (mul_le_mul hSi hB (norm_nonneg _) hsi) hS (norm_nonneg _) (mul_nonneg hsi hd)
        nlinarith
  have he : weight p * comm h' f * weight p = U * (weight p * comm h f * weight p) * V := by
    dsimp [U, V]
    rw [hcomm f]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (weightInv p) (weight p), hPiP, one_mul]
    rw [← Matrix.mul_assoc (weight p) (weightInv p), hPPi, one_mul]
  have hh := hsSq_two_mul U (weight p * comm h f * weight p) V
    (1 + s * si * d) (by positivity) hU hV
  rw [← he, weighted_comm_sq p (fun i => (hp i).le), weighted_comm_sq p (fun i => (hp i).le)] at hh
  nlinarith

theorem ward_form_weight {ι : Type} [Fintype ι] (p p' : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, 0 ≤ p' i) (u : ℝ) (hu : 0 ≤ u)
    (hrel : ∀ i, p' i ≤ u * p i) (h : Matrix ι ι ℂ) (f : ι → ℝ) :
    AndersonAC.S78.wardEnergy Finset.univ p' h f ≤
      u ^ 2 * AndersonAC.S78.wardEnergy Finset.univ p h f := by
  simp only [AndersonAC.S78.wardEnergy]
  rw [← mul_assoc, mul_comm (u ^ 2), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hh := mul_le_mul (hrel i) (hrel j) (hp' j) (mul_nonneg hu (hp i))
  calc p' i * p' j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2
      ≤ ((u * p i) * (u * p j)) * ‖h i j‖ ^ 2 * (f i - f j) ^ 2 := by
        gcongr
    _ = _ := by ring

theorem one_add_pow_six {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε) ^ 6 ≤ 1 + 63 * ε := by
  have h2 : ε ^ 2 ≤ ε := by nlinarith
  have hn (n : ℕ) : ε ^ (n + 1) ≤ ε ^ n := by
    calc ε ^ (n + 1) = ε ^ n * ε := pow_succ _ _
      _ ≤ ε ^ n * 1 := mul_le_mul_of_nonneg_left hε1 (pow_nonneg hε _)
      _ = ε ^ n := mul_one _
  have h3 := (hn 2).trans h2
  have h4 := (hn 3).trans h3
  have h5 := (hn 4).trans h4
  have h6 := (hn 5).trans h5
  linear_combination 15 * h2 + 20 * h3 + 15 * h4 + 6 * h5 + h6

theorem ward_form_bounds {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h h' L R A B : Matrix ι ι ℂ) (p p' : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hp' : ∀ i, 0 < p' i)
    (s si d ε : ℝ) (hs : 0 ≤ s) (hsi : 0 ≤ si) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1)
    (hS : ‖weight p‖ ≤ s) (hSi : ‖weightInv p‖ ≤ si)
    (hL : ‖L - 1‖ ≤ d) (hR : ‖R - 1‖ ≤ d)
    (hA : ‖A - 1‖ ≤ d) (hB : ‖B - 1‖ ≤ d)
    (hcomm : ∀ f, comm h' f = L * comm h f * R)
    (hcomm' : ∀ f, comm h f = A * comm h' f * B)
    (he : s * si * d ≤ ε)
    (hrel : ∀ i, p' i ≤ (1 + ε) * p i ∧ p i ≤ (1 + ε) * p' i) :
    ∀ f, AndersonAC.S78.wardEnergy Finset.univ p' h' f ≤
        (1 + 63 * ε) * AndersonAC.S78.wardEnergy Finset.univ p h f ∧
      AndersonAC.S78.wardEnergy Finset.univ p h f ≤
        (1 + 63 * ε) * AndersonAC.S78.wardEnergy Finset.univ p' h' f := by
  intro f
  have hD := wardEnergy_nonneg p (fun i => (hp i).le) h f
  have hD' := wardEnergy_nonneg p' (fun i => (hp' i).le) h' f
  have hc1 := ward_form_conjugation h h' L R p hp s si d hs hsi hd hS hSi hL hR hcomm f
  have hc2 := ward_form_conjugation h' h A B p hp s si d hs hsi hd hS hSi hA hB hcomm' f
  have hw1 := ward_form_weight p p' (fun i => (hp i).le) (fun i => (hp' i).le)
    (1 + ε) (by positivity) (fun i => (hrel i).1) h' f
  have hw2 := ward_form_weight p' p (fun i => (hp' i).le) (fun i => (hp i).le)
    (1 + ε) (by positivity) (fun i => (hrel i).2) h' f
  have hfac : (1 + s * si * d) ^ 4 ≤ (1 + ε) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  constructor
  · calc AndersonAC.S78.wardEnergy Finset.univ p' h' f
        ≤ (1 + ε) ^ 2 * AndersonAC.S78.wardEnergy Finset.univ p h' f := hw1
      _ ≤ (1 + ε) ^ 2 * ((1 + s * si * d) ^ 4 * AndersonAC.S78.wardEnergy Finset.univ p h f) :=
        mul_le_mul_of_nonneg_left hc1 (sq_nonneg _)
      _ ≤ (1 + ε) ^ 2 * ((1 + ε) ^ 4 * AndersonAC.S78.wardEnergy Finset.univ p h f) := by gcongr
      _ = (1 + ε) ^ 6 * AndersonAC.S78.wardEnergy Finset.univ p h f := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_add_pow_six hε hε1) hD
  · calc AndersonAC.S78.wardEnergy Finset.univ p h f
        ≤ (1 + s * si * d) ^ 4 * AndersonAC.S78.wardEnergy Finset.univ p h' f := hc2
      _ ≤ (1 + ε) ^ 4 * AndersonAC.S78.wardEnergy Finset.univ p h' f :=
        mul_le_mul_of_nonneg_right hfac (wardEnergy_nonneg p (fun i => (hp i).le) h' f)
      _ ≤ (1 + ε) ^ 4 * ((1 + ε) ^ 2 * AndersonAC.S78.wardEnergy Finset.univ p' h' f) :=
        mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = (1 + ε) ^ 6 * AndersonAC.S78.wardEnergy Finset.univ p' h' f := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_add_pow_six hε hε1) hD'

theorem signed_relative_of_mutual {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu : y ≤ (1 + θ) * x)
    (hr : x ≤ (1 + θ) * y) : (1 - θ) * x ≤ y ∧ y ≤ (1 + θ) * x := by
  refine ⟨?_, hu⟩
  have hh := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 1 - θ)
  nlinarith [mul_nonneg (sq_nonneg θ) hy]

end AndersonAC.SolS78Var
