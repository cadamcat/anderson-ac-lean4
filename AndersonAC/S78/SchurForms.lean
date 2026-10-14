import AndersonAC.S78.Definitions

set_option autoImplicit false
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- The extension set in every variational Schur problem is nonempty. -/
theorem schur_values_nonempty {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (f : ι → ℝ) :
    (D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i}).Nonempty :=
  ⟨D f, f, (by intro i hi; rfl), rfl⟩

/-- Variational Schur minimization preserves a pointwise form inequality. -/
theorem schur_energy_mono {ι : Type} (A : Finset ι)
    (D E : (ι → ℝ) → ℝ) (f : ι → ℝ)
    (hD : BddBelow (D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i}))
    (h : ∀ F, D F ≤ E F) : schurEnergy A D f ≤ schurEnergy A E f := by
  apply le_csInf (schur_values_nonempty A E f)
  rintro x ⟨F, hF, rfl⟩
  exact (csInf_le hD ⟨F, hF, rfl⟩).trans (h F)

/-- Adding a form supported on the survivors commutes with Schur minimization.
The boundedness premise belongs to the original energy, not to the error form. -/
theorem schur_energy_add_supported {ι : Type} (A : Finset ι)
    (D L : (ι → ℝ) → ℝ) (f : ι → ℝ)
    (hD : BddBelow (D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i}))
    (hL : ∀ F, (∀ i ∈ A, F i = f i) → L F = L f) :
    schurEnergy A (fun F => D F + L F) f = schurEnergy A D f + L f := by
  let e : ℝ ≃o ℝ :=
    { toFun := fun x => x + L f
      invFun := fun x => x - L f
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_rel_iff' := by intro x y; exact add_le_add_iff_right (L f) }
  have heq : (fun F => D F + L F) '' {F : ι → ℝ | ∀ i ∈ A, F i = f i} =
      e '' (D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i}) := by
    ext x
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨D F, ⟨F, hF, rfl⟩, by change D F + L f = D F + L F; rw [hL F hF]⟩
    · rintro ⟨y, ⟨F, hF, rfl⟩, rfl⟩
      exact ⟨F, hF, by change D F + L F = D F + L f; rw [hL F hF]⟩
  unfold schurEnergy
  rw [heq]
  exact (e.map_csInf' (schur_values_nonempty A D f) hD).symm

/-- A form already supported on the retained coordinates is unchanged. -/
theorem schur_energy_of_supported {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (f : ι → ℝ)
    (hD : ∀ F, (∀ i ∈ A, F i = f i) → D F = D f) :
    schurEnergy A D f = D f := by
  have heq : D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i} = {D f} := by
    ext x
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact Set.mem_singleton_iff.mpr (hD F hF)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨f, (by intro i hi; rfl), hx.symm⟩
  unfold schurEnergy
  rw [heq, csInf_singleton]

/-- Ward energy uses only the retained physical coordinates. -/
theorem ward_energy_supported {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h : Matrix ι ι ℂ) (f F : ι → ℝ) (hF : ∀ i ∈ A, F i = f i) :
    wardEnergy A p h F = wardEnergy A p h f := by
  unfold wardEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hF i hi, hF j hj]

/-- The empty elimination in the assembly induction. -/
theorem schur_ward_energy_self {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h : Matrix ι ι ℂ) (f : ι → ℝ) :
    schurEnergy A (wardEnergy A p h) f = wardEnergy A p h f := by
  exact schur_energy_of_supported A (wardEnergy A p h) f
    (fun F hF => ward_energy_supported A p h f F hF)

/-- Positive damping makes every variational Ward energy nonnegative. -/
theorem ward_energy_nonneg {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h : Matrix ι ι ℂ) (f : ι → ℝ) (hp : ∀ i ∈ A, 0 ≤ p i) :
    0 ≤ wardEnergy A p h f := by
  unfold wardEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hiP := hp i hi
  have hjP := hp j hj
  positivity

/-- Nonnegative forms have well-defined, nonnegative variational minima. -/
theorem schur_energy_nonneg {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (hD : ∀ F, 0 ≤ D F) (f : ι → ℝ) :
    0 ≤ schurEnergy A D f := by
  apply le_csInf (schur_values_nonempty A D f)
  rintro x ⟨F, hF, rfl⟩
  exact hD F

/-- Eliminating in two nested steps gives the same variational Schur form.
No minimizing extension is chosen in this identity. -/
theorem schur_energy_nested {ι : Type} (A B : Finset ι) (hAB : A ⊆ B)
    (D : (ι → ℝ) → ℝ) (hD : ∀ F, 0 ≤ D F) (f : ι → ℝ) :
    schurEnergy A (schurEnergy B D) f = schurEnergy A D f := by
  have hbdd : ∀ Q : Finset ι, ∀ F : ι → ℝ,
      BddBelow (D '' {H : ι → ℝ | ∀ i ∈ Q, H i = F i}) :=
    fun Q F => ⟨0, by rintro x ⟨H, hH, rfl⟩; exact hD H⟩
  apply le_antisymm
  · apply schur_energy_mono A (schurEnergy B D) D f
    · exact ⟨0, by
        rintro x ⟨F, hF, rfl⟩
        exact schur_energy_nonneg B D hD F⟩
    · intro F
      exact csInf_le (hbdd B F) ⟨F, (by intro i hi; rfl), rfl⟩
  · apply le_csInf (schur_values_nonempty A (schurEnergy B D) f)
    rintro x ⟨F, hF, rfl⟩
    apply le_csInf (schur_values_nonempty B D F)
    rintro x ⟨H, hH, rfl⟩
    apply csInf_le (hbdd A f)
    exact ⟨H, (fun i hi => (hH i (hAB hi)).trans (hF i hi)), rfl⟩

/-- Restricting a Ward form to surviving edges can only decrease its energy. -/
theorem ward_energy_mono_active {ι : Type} (A B : Finset ι) (hAB : A ⊆ B)
    (p : ι → ℝ) (h : Matrix ι ι ℂ) (f : ι → ℝ) (hp : ∀ i ∈ B, 0 ≤ p i) :
    wardEnergy A p h f ≤ wardEnergy B p h f := by
  classical
  unfold wardEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2) ≤
        ∑ i ∈ A, ∑ j ∈ B, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum_of_subset_of_nonneg hAB
      intro j hj hjA
      have hiP := hp i (hAB hi)
      have hjP := hp j hj
      positivity
    _ ≤ ∑ i ∈ B, ∑ j ∈ B, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hAB
      intro i hi hiA
      apply Finset.sum_nonneg
      intro j hj
      have hiP := hp i hi
      have hjP := hp j hj
      positivity

/-- The old energy carried through removed sites is nonnegative. This is
the lower bound on B_a in the assembly energy split. -/
theorem schur_ward_bridge_nonneg {ι : Type} (A B : Finset ι) (hAB : A ⊆ B)
    (p : ι → ℝ) (h : Matrix ι ι ℂ) (f : ι → ℝ) (hp : ∀ i ∈ B, 0 ≤ p i) :
    0 ≤ schurEnergy A (wardEnergy B p h) f - wardEnergy A p h f := by
  apply sub_nonneg.mpr
  apply le_csInf (schur_values_nonempty A (wardEnergy B p h) f)
  rintro x ⟨F, hF, rfl⟩
  rw [← ward_energy_supported A p h f F hF]
  exact ward_energy_mono_active A B hAB p h F hp

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.schur_energy_mono
#print axioms AndersonAC.SolS78.schur_energy_add_supported
#print axioms AndersonAC.SolS78.schur_energy_of_supported

#print axioms AndersonAC.SolS78.schur_ward_energy_self
#print axioms AndersonAC.SolS78.ward_energy_nonneg
#print axioms AndersonAC.SolS78.schur_energy_nested
#print axioms AndersonAC.SolS78.schur_ward_bridge_nonneg
