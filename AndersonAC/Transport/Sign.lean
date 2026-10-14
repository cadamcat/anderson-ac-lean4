import AndersonAC.Blueprint.Transport

noncomputable section

open OAI.Anderson
open scoped ENNReal NNReal lp

namespace AndersonAC.LunaTransport

def siteSum {d : ℕ} (x : Site d) : ℤ := ∑ j : Fin d, x j

def parity {d : ℕ} (x : Site d) : ℂ := (-1 : ℂ) ^ siteSum x

lemma siteSum_add {d : ℕ} (x y : Site d) : siteSum (x + y) = siteSum x + siteSum y := by
  simp [siteSum, Pi.add_apply, Finset.sum_add_distrib]

lemma siteSum_basisVector {d : ℕ} (j : Fin d) :
    siteSum (basisVector j : Site d) = 1 := by
  simp [siteSum, basisVector, Pi.single_apply]

lemma parity_add {d : ℕ} (x y : Site d) :
    parity (x + y) = parity x * parity y := by
  unfold parity
  rw [siteSum_add]
  exact zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) _ _

lemma parity_basisVector {d : ℕ} (j : Fin d) :
    parity (basisVector j : Site d) = -1 := by
  simp [parity, siteSum_basisVector]

lemma parity_neg_basisVector {d : ℕ} (j : Fin d) :
    parity (-(basisVector j : Site d)) = -1 := by
  simp [parity, siteSum, basisVector, Pi.single_apply]

lemma parity_norm {d : ℕ} (x : Site d) : ‖parity x‖ = 1 := by
  simp [parity, norm_zpow]

lemma parity_sq {d : ℕ} (x : Site d) : parity x * parity x = 1 := by
  have hi : (parity x)⁻¹ = parity x := by
    unfold parity
    rw [← inv_zpow]
    norm_num
  have hne : parity x ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [parity_norm]; norm_num)
  calc
    parity x * parity x = parity x * (parity x)⁻¹ := by rw [hi]
    _ = 1 := mul_inv_cancel₀ hne

lemma parity_add_basisVector {d : ℕ} (x : Site d) (j : Fin d) :
    parity (x + basisVector j) = -parity x := by
  rw [parity_add, parity_basisVector]
  ring

lemma parity_sub_basisVector {d : ℕ} (x : Site d) (j : Fin d) :
    parity (x - basisVector j) = -parity x := by
  rw [sub_eq_add_neg, parity_add, parity_neg_basisVector]
  ring

def parityLinear {d : ℕ} : StateSpace d →ₗ[ℂ] StateSpace d where
  toFun f := ⟨fun x => parity x * f x,
    (lp.memℓp f).mono' (fun x => by
      rw [norm_mul, parity_norm, one_mul])⟩
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by
    ext x
    change parity x * (c * f x) = c * (parity x * f x)
    ring

def parityUnitary {d : ℕ} : StateSpace d ≃ₗᵢ[ℂ] StateSpace d where
  toFun := parityLinear
  invFun := parityLinear
  left_inv f := by
    ext x
    change parity x * (parity x * f x) = f x
    rw [← mul_assoc, parity_sq, one_mul]
  right_inv f := by
    ext x
    change parity x * (parity x * f x) = f x
    rw [← mul_assoc, parity_sq, one_mul]
  map_add' f g := parityLinear.map_add f g
  map_smul' c f := parityLinear.map_smul c f
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    apply tsum_congr
    intro x
    simp [parityLinear, parity_norm]

@[simp] lemma parityUnitary_apply {d : ℕ} (f : StateSpace d) (x : Site d) :
    parityUnitary f x = parity x * f x := rfl

lemma hopping_apply_formula {d : ℕ} (f : StateSpace d) (x : Site d) :
    hopping d f x = -(∑ j : Fin d,
      (f (x + basisVector j) + f (x - basisVector j))) := by
  let ω : Configuration d := fun _ => ⟨0, by norm_num⟩
  simpa [hamiltonian] using (hamiltonian_apply (0 : ℝ) ω f x)

lemma parity_conj_hopping_apply {d : ℕ} (f : StateSpace d) (x : Site d) :
    parity x * hopping d (parityUnitary f) x = -hopping d f x := by
  rw [hopping_apply_formula, hopping_apply_formula]
  simp_rw [parityUnitary_apply, parity_add_basisVector, parity_sub_basisVector]
  calc
    parity x * (-(∑ j : Fin d,
        (-parity x * f (x + basisVector j) +
          -parity x * f (x - basisVector j)))) =
        parity x * (-(∑ j : Fin d,
          -(parity x * (f (x + basisVector j) + f (x - basisVector j))))) := by
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = parity x * (parity x *
        (∑ j : Fin d, (f (x + basisVector j) + f (x - basisVector j)))) := by
      congr 1
      simp [Finset.mul_sum]
    _ = ∑ j : Fin d, (f (x + basisVector j) + f (x - basisVector j)) := by
      rw [← mul_assoc, parity_sq, one_mul]
    _ = - -∑ j : Fin d, (f (x + basisVector j) + f (x - basisVector j)) := by
      simp

lemma boundedPotentialOperator_apply {d : ℕ} (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) (f : StateSpace d) (x : Site d) :
    Blueprint.boundedPotentialOperator V M hM hV f x = (V x : ℂ) * f x := rfl

lemma simonHamiltonian_apply {d : ℕ} (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) (f : StateSpace d) (x : Site d) :
    Blueprint.simonHamiltonian V M hM hV f x =
      -hopping d f x + (V x : ℂ) * f x := by
  simp [Blueprint.simonHamiltonian, boundedPotentialOperator_apply]

lemma shiftedHamiltonian_apply {d : ℕ} (a b : ℝ) (ω : Configuration d)
    (f : StateSpace d) (x : Site d) :
    Blueprint.shiftedHamiltonian a b ω f x =
      hopping d f x +
        ((Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b *
          potential ω x : ℝ) : ℂ) * f x := by
  change hamiltonian (Blueprint.intervalCoupling a b) ω f x +
      (Blueprint.intervalCenter a b : ℂ) * f x = _
  rw [hamiltonian_apply, hopping_apply_formula]
  simp only [Blueprint.intervalCenter, Blueprint.intervalCoupling]
  push_cast
  ring

lemma parityUnitary_symm_apply {d : ℕ} (f : StateSpace d) :
    (parityUnitary (d := d)).symm f = parityUnitary f := by
  apply (parityUnitary (d := d)).injective
  calc
    parityUnitary (parityUnitary.symm f) = f := parityUnitary.apply_symm_apply f
    _ = parityUnitary (parityUnitary f) := (parityUnitary.right_inv f).symm

lemma parity_conjugate_apply {d : ℕ} (T : Blueprint.Operator d)
    (f : StateSpace d) (x : Site d) :
    Blueprint.conjugate (parityUnitary (d := d)) T f x =
      parity x * T (parityUnitary f) x := by
  simp [Blueprint.conjugate, parityUnitary_symm_apply]

lemma affinePotential_bound {d : ℕ} (a b : ℝ) (ω : Configuration d) :
    ∀ x, |Blueprint.affineConfiguration a b ω x| ≤
      |Blueprint.intervalCenter a b| + |Blueprint.intervalCoupling a b| := by
  intro x
  unfold Blueprint.affineConfiguration
  calc
    |Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * potential ω x|
      ≤ |Blueprint.intervalCenter a b| +
          |Blueprint.intervalCoupling a b * potential ω x| := abs_add_le _ _
    _ = |Blueprint.intervalCenter a b| +
          |Blueprint.intervalCoupling a b| * |potential ω x| := by rw [abs_mul]
    _ ≤ |Blueprint.intervalCenter a b| + |Blueprint.intervalCoupling a b| := by
      have hp := abs_potential_le_one ω x
      have hc := abs_nonneg (Blueprint.intervalCoupling a b)
      nlinarith

theorem signTransportCore : Blueprint.SignTransportInput := by
  intro d
  refine ⟨parityUnitary, ?_⟩
  intro a b ω
  let M := |Blueprint.intervalCenter a b| + |Blueprint.intervalCoupling a b|
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hV : ∀ x, |Blueprint.affineConfiguration a b ω x| ≤ M := by
    exact affinePotential_bound a b ω
  refine ⟨M, hM, hV, ?_⟩
  ext f x
  rw [simonHamiltonian_apply, parity_conjugate_apply, shiftedHamiltonian_apply]
  rw [mul_add, parity_conj_hopping_apply]
  simp only [parityUnitary_apply]
  simp only [Blueprint.affineConfiguration, Complex.ofReal_add, Complex.ofReal_mul]
  congr 1
  have h : parity x * ((↑(Blueprint.intervalCenter a b) +
      ↑(Blueprint.intervalCoupling a b) * ↑(potential ω x) : ℂ) *
      (parity x * (f x : ℂ))) =
      (parity x * parity x) *
        ((↑(Blueprint.intervalCenter a b) +
          ↑(Blueprint.intervalCoupling a b) * ↑(potential ω x) : ℂ) * f x) := by
    ring
  rw [h, parity_sq, one_mul]

end AndersonAC.LunaTransport

namespace AndersonAC.Blueprint.Packages

theorem signTransport : AndersonAC.Blueprint.SignTransportInput :=
  AndersonAC.LunaTransport.signTransportCore


end AndersonAC.Blueprint.Packages
