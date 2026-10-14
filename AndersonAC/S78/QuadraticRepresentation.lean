import AndersonAC.S78.VariationalInputs
import AndersonAC.S78.InverseComparison

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- A quadratic form on the retained coordinates has the required real
symmetric matrix representation, including an empty retained set. -/
theorem finite_real_form_of_quadratic {ι : Type} (A : Finset ι)
    (Q : QuadraticForm ℝ (A → ℝ)) :
    FiniteRealForm A (fun f : ι → ℝ => Q (fun i : A => f i.val)) := by
  classical
  refine ⟨Q.toMatrix', Q.isSymm_toMatrix', ?_⟩
  intro f
  let x : A → ℝ := fun i => f i.val
  calc
    Q x = Q.associated x x := (QuadraticMap.associated_eq_self_apply ℝ Q x).symm
    _ = Matrix.toBilin' Q.toMatrix' x x := by
      change _ = Matrix.toLinearMap₂' ℝ (LinearMap.toMatrix₂' ℝ Q.associated) x x
      rw [Matrix.toLinearMap₂'_toMatrix']
    _ = realForm A Q.toMatrix' f := Matrix.toBilin'_apply _ _ _

/-- Every padded Ward energy is a finite real quadratic form. -/
theorem finite_real_form_ward {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h : Matrix ι ι ℂ) : FiniteRealForm A (wardEnergy A p h) := by
  classical
  let L : A → A → (A → ℝ) →ₗ[ℝ] ℝ := fun i j =>
    (LinearMap.proj i : (A → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  let Q : QuadraticForm ℝ (A → ℝ) := (1 / 2 : ℝ) •
    ∑ i : A, ∑ j : A, (p i.val * p j.val * ‖h i.val j.val‖ ^ 2) •
      QuadraticMap.linMulLin (L i j) (L i j)
  have hQ : ∀ f : ι → ℝ, Q (fun i : A => f i.val) = wardEnergy A p h f := by
    intro f
    simp only [Q, QuadraticMap.smul_apply, QuadraticMap.sum_apply,
      QuadraticMap.linMulLin_apply, L, LinearMap.sub_apply, LinearMap.proj_apply,
      smul_eq_mul]
    unfold wardEnergy
    simp only [← Finset.sum_coe_sort A]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have heq : wardEnergy A p h = fun f : ι → ℝ => Q (fun i : A => f i.val) :=
    funext (fun f => (hQ f).symm)
  rw [heq]
  exact finite_real_form_of_quadratic A Q

theorem finite_real_form_add {ι : Type} (A : Finset ι)
    (D E : (ι → ℝ) → ℝ) (hD : FiniteRealForm A D) (hE : FiniteRealForm A E) :
    FiniteRealForm A (fun f => D f + E f) := by
  classical
  obtain ⟨Q, hQ, hD⟩ := hD
  obtain ⟨R, hR, hE⟩ := hE
  refine ⟨Q + R, by rw [Matrix.transpose_add, hQ, hR], ?_⟩
  intro f
  change D f + E f = realForm A (Q + R) f
  rw [hD f, hE f]
  unfold realForm
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem finite_real_form_sub {ι : Type} (A : Finset ι)
    (D E : (ι → ℝ) → ℝ) (hD : FiniteRealForm A D) (hE : FiniteRealForm A E) :
    FiniteRealForm A (fun f => D f - E f) := by
  classical
  obtain ⟨Q, hQ, hD⟩ := hD
  obtain ⟨R, hR, hE⟩ := hE
  refine ⟨Q - R, by rw [Matrix.transpose_sub, hQ, hR], ?_⟩
  intro f
  change D f - E f = realForm A (Q - R) f
  rw [hD f, hE f]
  unfold realForm
  simp only [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- Padding a form by zero on additional coordinates preserves finite real
representability. The coordinate restriction is an actual linear map. -/
theorem finite_real_form_pad {ι : Type} (A B : Finset ι) (hAB : A ⊆ B)
    (D : (ι → ℝ) → ℝ) (hD : FiniteRealForm A D) : FiniteRealForm B D := by
  classical
  obtain ⟨Q, hQ, hD⟩ := hD
  let L : (B → ℝ) →ₗ[ℝ] (A → ℝ) := LinearMap.pi fun i : A =>
    (LinearMap.proj ⟨i.val, hAB i.property⟩ : (B → ℝ) →ₗ[ℝ] ℝ)
  let E := Q.toQuadraticForm'.comp L
  have hE : ∀ f : ι → ℝ, E (fun i : B => f i.val) = D f := by
    intro f
    change Matrix.toBilin' Q (fun i : A => f i.val) (fun i : A => f i.val) = D f
    rw [Matrix.toBilin'_apply]
    exact (hD f).symm
  have heq : D = fun f : ι → ℝ => E (fun i : B => f i.val) :=
    funext (fun f => (hE f).symm)
  rw [heq]
  exact finite_real_form_of_quadratic B E

/-- Zero-extension of a charge changes neither its linear pairing nor its
inverse form when the retained set is enlarged. -/
theorem inverse_energy_change_active {ι : Type} (A B : Finset ι) (hAB : A ⊆ B)
    (D : (ι → ℝ) → ℝ) (y : ι → ℝ) (hy : ∀ i ∈ B, i ∉ A → y i = 0) :
    inverseEnergy B D y = inverseEnergy A D y := by
  have hsum : ∀ f : ι → ℝ, (∑ i ∈ B, y i * f i) = ∑ i ∈ A, y i * f i := by
    intro f
    exact (Finset.sum_subset hAB (fun i hi hni => by rw [hy i hi hni, zero_mul])).symm
  unfold inverseEnergy
  simp_rw [hsum]

/-- The homogeneity used by reciprocal inverse comparison holds for the
actual Ward form without additional matrix assumptions. -/
theorem ward_energy_homogeneous {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h : Matrix ι ι ℂ) (s : ℝ) (f : ι → ℝ) :
    wardEnergy A p h (fun i => s * f i) = s ^ 2 * wardEnergy A p h f := by
  unfold wardEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.finite_real_form_ward
#print axioms AndersonAC.SolS78.finite_real_form_pad
#print axioms AndersonAC.SolS78.inverse_energy_change_active
#print axioms AndersonAC.SolS78.ward_energy_homogeneous
