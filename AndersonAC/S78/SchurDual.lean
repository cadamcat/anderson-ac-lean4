import AndersonAC.S78.SchurForms

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- Increasing an energy decreases its finite variational inverse form. -/
theorem inverse_energy_antitone {ι : Type} (A : Finset ι)
    (D E : (ι → ℝ) → ℝ) (y : ι → ℝ)
    (hD : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f)) (hDE : ∀ f, D f ≤ E f) :
    inverseEnergy A E y ≤ inverseEnergy A D y := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨f, rfl⟩
  exact (sub_le_sub_left (hDE f) _).trans (le_csSup hD ⟨f, rfl⟩)

/-- Schur minimization preserves the inverse form of a retained charge.
The two boundedness hypotheses ensure that real sInf/sSup represent the
variational energies rather than their default values for unbounded sets. -/
theorem inverse_energy_schur {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (y : ι → ℝ)
    (hbelow : ∀ f : ι → ℝ,
      BddBelow (D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i}))
    (habove : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f)) :
    inverseEnergy A (schurEnergy A D) y = inverseEnergy A D y := by
  have hupper : ∀ f : ι → ℝ,
      2 * (∑ i ∈ A, y i * f i) - schurEnergy A D f ≤ inverseEnergy A D y := by
    intro f
    have hlow : 2 * (∑ i ∈ A, y i * f i) - inverseEnergy A D y ≤
        schurEnergy A D f := by
      apply le_csInf (schur_values_nonempty A D f)
      rintro x ⟨F, hF, rfl⟩
      have hlin : (∑ i ∈ A, y i * F i) = ∑ i ∈ A, y i * f i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hF i hi]
      have hbound := le_csSup habove (Set.mem_range_self F)
      change 2 * (∑ i ∈ A, y i * F i) - D F ≤ inverseEnergy A D y at hbound
      rw [hlin] at hbound
      linarith
    linarith
  have hschur : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - schurEnergy A D f) :=
    ⟨inverseEnergy A D y, by rintro x ⟨f, rfl⟩; exact hupper f⟩
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro x ⟨f, rfl⟩; exact hupper f)
  · apply inverse_energy_antitone A (schurEnergy A D) D y hschur
    intro f
    exact csInf_le (hbelow f) ⟨f, (by intro i hi; rfl), rfl⟩

/-- Rescaling a quadratic form rescales its inverse by the reciprocal.
This is the scalar step in the assembly inverse comparison. -/
theorem inverse_energy_scale {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (y : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hhom : ∀ (s : ℝ) (f : ι → ℝ), D (fun i => s * f i) = s ^ 2 * D f)
    (habove : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f)) :
    inverseEnergy A (fun f => a * D f) y = a⁻¹ * inverseEnergy A D y := by
  let e : ℝ ≃o ℝ :=
    { toFun := fun x => x / a
      invFun := fun x => x * a
      left_inv := by intro x; exact div_mul_cancel₀ x ha.ne'
      right_inv := by intro x; exact mul_div_cancel_right₀ x ha.ne'
      map_rel_iff' := by intro x z; exact div_le_div_iff_of_pos_right ha }
  have hlin : ∀ (s : ℝ) (f : ι → ℝ),
      (∑ i ∈ A, y i * (s * f i)) = s * ∑ i ∈ A, y i * f i := by
    intro s f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have heq : (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - a * D f) =
      e '' (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - D f) := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨2 * (∑ i ∈ A, y i * (a * f i)) - D (fun i => a * f i),
        ⟨(fun i => a * f i), rfl⟩, ?_⟩
      change (2 * (∑ i ∈ A, y i * (a * f i)) - D (fun i => a * f i)) / a = _
      rw [hlin, hhom]
      field_simp [ha.ne']
    · rintro ⟨z, ⟨f, rfl⟩, rfl⟩
      refine ⟨(fun i => a⁻¹ * f i), ?_⟩
      change 2 * (∑ i ∈ A, y i * (a⁻¹ * f i)) - a * D (fun i => a⁻¹ * f i) =
        (2 * (∑ i ∈ A, y i * f i) - D f) / a
      rw [hlin, hhom]
      field_simp [ha.ne']
  unfold inverseEnergy
  rw [heq, ← e.map_csSup' (Set.range_nonempty _) habove]
  change (sSup (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - D f)) / a = _
  rw [div_eq_mul_inv, mul_comm]

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.inverse_energy_antitone
#print axioms AndersonAC.SolS78.inverse_energy_schur
#print axioms AndersonAC.SolS78.inverse_energy_scale
