import AndersonAC.S78.SchurForms

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

theorem endpoint_square_change_proof (z a : ℂ) :
    (z + a) ^ 2 - z ^ 2 = 2 * z * a + a ^ 2 := by ring

theorem endpoint_modulus_change_proof (z a : ℂ) :
    ‖z + a‖ ^ 2 - ‖z‖ ^ 2 = 2 * (star z * a).re + ‖a‖ ^ 2 := by
  change ‖z + a‖ ^ 2 - ‖z‖ ^ 2 = 2 * ((starRingEnd ℂ) z * a).re + ‖a‖ ^ 2
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Weighted Cauchy--Schwarz for the cross term in a squared-kernel change. -/
theorem weighted_square_change {ι : Type} (S : Finset ι) (w : ι → ℝ)
    (h a : ι → ℂ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    |∑ i ∈ S, w i * (‖h i + a i‖ ^ 2 - ‖h i‖ ^ 2)| ≤
      2 * Real.sqrt (∑ i ∈ S, w i * ‖h i‖ ^ 2) *
        Real.sqrt (∑ i ∈ S, w i * ‖a i‖ ^ 2) + ∑ i ∈ S, w i * ‖a i‖ ^ 2 := by
  let H := fun i => Real.sqrt (w i) * ‖h i‖
  let A := fun i => Real.sqrt (w i) * ‖a i‖
  have hpoint : ∀ i ∈ S,
      |w i * (‖h i + a i‖ ^ 2 - ‖h i‖ ^ 2)| ≤ 2 * (H i * A i) + (A i) ^ 2 := by
    intro i hi
    have hcross : |(star (h i) * a i).re| ≤ ‖h i‖ * ‖a i‖ := by
      calc
        _ ≤ ‖star (h i) * a i‖ := Complex.abs_re_le_norm _
        _ = _ := by rw [norm_mul, norm_star]
    have hinc : |‖h i + a i‖ ^ 2 - ‖h i‖ ^ 2| ≤ 2 * ‖h i‖ * ‖a i‖ + ‖a i‖ ^ 2 := by
      rw [endpoint_modulus_change_proof]
      calc
        _ ≤ |2 * (star (h i) * a i).re| + |‖a i‖ ^ 2| := abs_add_le _ _
        _ = 2 * |(star (h i) * a i).re| + ‖a i‖ ^ 2 := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_nonneg (sq_nonneg ‖a i‖)]
        _ ≤ _ := by nlinarith
    rw [abs_mul, abs_of_nonneg (hw i hi)]
    calc
      w i * |‖h i + a i‖ ^ 2 - ‖h i‖ ^ 2| ≤
          w i * (2 * ‖h i‖ * ‖a i‖ + ‖a i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hinc (hw i hi)
      _ = 2 * (H i * A i) + (A i) ^ 2 := by
        dsimp [H, A]
        ring_nf
        rw [Real.sq_sqrt (hw i hi)]
        ring
  have hH : (∑ i ∈ S, (H i) ^ 2) = ∑ i ∈ S, w i * ‖h i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [H]
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hA : (∑ i ∈ S, (A i) ^ 2) = ∑ i ∈ S, w i * ‖a i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt S H A
  rw [hH, hA] at hcauchy
  calc
    _ ≤ ∑ i ∈ S, |w i * (‖h i + a i‖ ^ 2 - ‖h i‖ ^ 2)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le S (fun i => w i * (‖h i + a i‖ ^ 2 - ‖h i‖ ^ 2)))
    _ ≤ ∑ i ∈ S, (2 * (H i * A i) + (A i) ^ 2) := Finset.sum_le_sum hpoint
    _ = 2 * (∑ i ∈ S, H i * A i) + ∑ i ∈ S, w i * ‖a i‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hA]
    _ ≤ _ := by nlinarith

/-- Survivor-edge energy changes cost the geometric mean of the old and
difference energies, plus the difference energy. -/
theorem ward_energy_change {ι : Type} (S : Finset ι) (p : ι → ℝ)
    (h a : Matrix ι ι ℂ) (f : ι → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i) :
    |wardEnergy S p (h + a) f - wardEnergy S p h f| ≤
      2 * Real.sqrt (wardEnergy S p h f) * Real.sqrt (wardEnergy S p a f) +
        wardEnergy S p a f := by
  let w := fun q : ι × ι => (1 / 2 : ℝ) * p q.1 * p q.2 * (f q.1 - f q.2) ^ 2
  have hw : ∀ q ∈ S.product S, 0 ≤ w q := by
    intro q hq
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hq
    have hiP := hp q.1 hi
    have hjP := hp q.2 hj
    dsimp [w]
    positivity
  have hform : ∀ g : Matrix ι ι ℂ,
      wardEnergy S p g f = ∑ q ∈ S.product S, w q * ‖g q.1 q.2‖ ^ 2 := by
    intro g
    unfold wardEnergy
    dsimp only [Matrix] at g ⊢
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, w (i, j) * ‖g i j‖ ^ 2 := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [w]
        ring
      _ = _ := (Finset.sum_product S S (fun q : ι × ι => w q * ‖g q.1 q.2‖ ^ 2)).symm
  have hdelta : (∑ q ∈ S.product S, w q * (‖h q.1 q.2 + a q.1 q.2‖ ^ 2 - ‖h q.1 q.2‖ ^ 2)) =
      wardEnergy S p (h + a) f - wardEnergy S p h f := by
    rw [hform, hform, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    change w q * (‖h q.1 q.2 + a q.1 q.2‖ ^ 2 - ‖h q.1 q.2‖ ^ 2) = _
    rw [mul_sub]
    rfl
  have hbound := weighted_square_change (S.product S) w
    (fun q => h q.1 q.2) (fun q => a q.1 q.2) hw
  rw [hdelta, ← hform h, ← hform a] at hbound
  exact hbound

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.endpoint_modulus_change_proof
#print axioms AndersonAC.SolS78.weighted_square_change
#print axioms AndersonAC.SolS78.ward_energy_change
