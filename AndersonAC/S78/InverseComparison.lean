import AndersonAC.S78.SchurDual

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- The dual upper bound survives increasing the energy. -/
theorem inverse_energy_bddAbove_mono {ι : Type} (A : Finset ι)
    (D E : (ι → ℝ) → ℝ) (y : ι → ℝ)
    (hD : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f)) (hDE : ∀ f, D f ≤ E f) :
    BddAbove (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - E f) := by
  obtain ⟨b, hb⟩ := hD
  refine ⟨b, ?_⟩
  rintro x ⟨f, rfl⟩
  exact (sub_le_sub_left (hDE f) _).trans (hb (Set.mem_range_self f))

/-- Positive rescaling keeps the dual optimization bounded. -/
theorem inverse_energy_scale_bddAbove {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (y : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hhom : ∀ (s : ℝ) (f : ι → ℝ), D (fun i => s * f i) = s ^ 2 * D f)
    (habove : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f)) :
    BddAbove (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - a * D f) := by
  obtain ⟨b, hb⟩ := habove
  refine ⟨a⁻¹ * b, ?_⟩
  rintro x ⟨f, rfl⟩
  have hlin : (∑ i ∈ A, y i * (a * f i)) = a * ∑ i ∈ A, y i * f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h := hb (Set.mem_range_self (fun i => a * f i))
  rw [hlin, hhom] at h
  apply (le_inv_mul_iff₀ ha).mpr
  nlinarith

/-- Relative quadratic-form bounds give reciprocal inverse-form bounds. -/
theorem relative_inverse_comparison {ι : Type} (A : Finset ι)
    (D E : (ι → ℝ) → ℝ) (y : ι → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hhom : ∀ (s : ℝ) (f : ι → ℝ), D (fun i => s * f i) = s ^ 2 * D f)
    (habove : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f))
    (hcompare : ∀ f, (1 - ε) * D f ≤ E f ∧ E f ≤ (1 + ε) * D f) :
    (1 + ε)⁻¹ * inverseEnergy A D y ≤ inverseEnergy A E y ∧
      inverseEnergy A E y ≤ (1 - ε)⁻¹ * inverseEnergy A D y := by
  have hminus : 0 < 1 - ε := sub_pos.mpr hε1
  have hplus : 0 < 1 + ε := by linarith
  have hlow := inverse_energy_scale_bddAbove A D y (1 - ε) hminus hhom habove
  have hE := inverse_energy_bddAbove_mono A (fun f => (1 - ε) * D f) E y hlow
    (fun f => (hcompare f).1)
  constructor
  · rw [← inverse_energy_scale A D y (1 + ε) hplus hhom habove]
    exact inverse_energy_antitone A E (fun f => (1 + ε) * D f) y hE
      (fun f => (hcompare f).2)
  · rw [← inverse_energy_scale A D y (1 - ε) hminus hhom habove]
    exact inverse_energy_antitone A (fun f => (1 - ε) * D f) E y hlow
      (fun f => (hcompare f).1)

/-- The final inverse comparison in the assembly induction, once its Schur
identity and relative energy estimate have been established. -/
theorem schur_relative_inverse_comparison {ι : Type} (A : Finset ι)
    (D E : (ι → ℝ) → ℝ) (y : ι → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hD : ∀ f, 0 ≤ D f)
    (hhom : ∀ (s : ℝ) (f : ι → ℝ), D (fun i => s * f i) = s ^ 2 * D f)
    (habove : BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f))
    (hcompare : ∀ f, (1 - ε) * D f ≤ E f ∧ E f ≤ (1 + ε) * D f) :
    (1 + ε)⁻¹ * inverseEnergy A D y ≤ inverseEnergy A (schurEnergy A E) y ∧
      inverseEnergy A (schurEnergy A E) y ≤ (1 - ε)⁻¹ * inverseEnergy A D y := by
  have hminus : 0 < 1 - ε := sub_pos.mpr hε1
  have hlow := inverse_energy_scale_bddAbove A D y (1 - ε) hminus hhom habove
  have hE := inverse_energy_bddAbove_mono A (fun f => (1 - ε) * D f) E y hlow
    (fun f => (hcompare f).1)
  have hEnonneg : ∀ f, 0 ≤ E f := fun f =>
    (mul_nonneg hminus.le (hD f)).trans (hcompare f).1
  rw [inverse_energy_schur A E y (fun f =>
    ⟨0, by rintro x ⟨F, hF, rfl⟩; exact hEnonneg F⟩) hE]
  exact relative_inverse_comparison A D E y ε hε0 hε1 hhom habove hcompare

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.inverse_energy_scale_bddAbove
#print axioms AndersonAC.SolS78.relative_inverse_comparison
#print axioms AndersonAC.SolS78.schur_relative_inverse_comparison
