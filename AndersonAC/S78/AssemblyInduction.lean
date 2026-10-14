import AndersonAC.S78.SchurForms

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- A Schur form depends only on the retained values. -/
theorem schur_energy_supported {ι : Type} (A : Finset ι)
    (D : (ι → ℝ) → ℝ) (f F : ι → ℝ) (hF : ∀ i ∈ A, F i = f i) :
    schurEnergy A D F = schurEnergy A D f := by
  have heq : {H : ι → ℝ | ∀ i ∈ A, H i = F i} =
      {H : ι → ℝ | ∀ i ∈ A, H i = f i} := by
    ext H
    constructor
    · intro h i hi
      exact (h i hi).trans (hF i hi)
    · intro h i hi
      exact (h i hi).trans (hF i hi).symm
  unfold schurEnergy
  rw [heq]

/-- One step of the assembly Schur identity. L is padded from the survivors,
so it is constant over the extension set of the next elimination. -/
theorem assembly_schur_step {ι : Type} (A B : Finset ι) (hAB : A ⊆ B)
    (D L old next : (ι → ℝ) → ℝ) (hD : ∀ f, 0 ≤ D f)
    (hL : ∀ f F, (∀ i ∈ A, F i = f i) → L F = L f)
    (hold : ∀ f, old f = schurEnergy B D f)
    (hnext : ∀ f, next f = schurEnergy A old f + L f) :
    ∀ f, next f = schurEnergy A (fun F => D F + L F) f := by
  intro f
  rw [hnext f, show old = schurEnergy B D from funext hold,
    schur_energy_nested A B hAB D hD f]
  exact (schur_energy_add_supported A D L f
    ⟨0, by rintro x ⟨F, hF, rfl⟩; exact hD F⟩ (hL f)).symm

/-- The deterministic prefix identity used in Proposition 7.3. Analytic
estimates enter only through nonnegativity of each accumulated initial form;
this theorem supplies the elimination bookkeeping. -/
theorem assembly_schur_prefix {ι : Type} (active : ℕ → Finset ι)
    (energy error : ℕ → (ι → ℝ) → ℝ)
    (hnested : ∀ n, active (n + 1) ⊆ active n)
    (hinitial : ∀ f F, (∀ i ∈ active 0, F i = f i) → energy 0 F = energy 0 f)
    (hsupport : ∀ n f F, (∀ i ∈ active (n + 1), F i = f i) → error n F = error n f)
    (hstep : ∀ n f, energy (n + 1) f = schurEnergy (active (n + 1)) (energy n) f + error n f)
    (hpositive : ∀ n f, 0 ≤ energy 0 f + ∑ a ∈ Finset.range n, error a f) :
    ∀ n f, energy n f = schurEnergy (active n)
      (fun F => energy 0 F + ∑ a ∈ Finset.range n, error a F) f := by
  intro n
  induction n with
  | zero =>
      intro f
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      exact (schur_energy_of_supported (active 0) (energy 0) f (hinitial f)).symm
  | succ n ih =>
      intro f
      have h := assembly_schur_step (active (n + 1)) (active n) (hnested n)
        (fun F => energy 0 F + ∑ a ∈ Finset.range n, error a F)
        (error n) (energy n) (energy (n + 1)) (hpositive n) (hsupport n) ih (hstep n) f
      simpa only [Finset.sum_range_succ, add_assoc] using h

/-- Each actual operation error is padded from its final surviving sites. -/
theorem operation_energy_error_supported {d m k : ℕ} {t b : ℝ}
    {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) (a : Fin k)
    (f F : Torus d m → ℝ) (hF : ∀ i ∈ (I.state a.succ).active, F i = f i) :
    operationEnergyError I a F = operationEnergyError I a f := by
  unfold operationEnergyError
  rw [show endpointEnergy (I.state a.succ) r t F =
      endpointEnergy (I.state a.succ) r t f from
        ward_energy_supported _ _ _ f F hF,
    schur_energy_supported (I.state a.succ).active _ f F hF]

/-- A sufficiently small relative error preserves the constant kernel. -/
theorem constant_kernel_of_absolute_error {ι : Type} (A : Finset ι)
    (D S : (ι → ℝ) → ℝ) (ε : ℝ) (hε : ε < 1)
    (hD : ∀ f, 0 ≤ D f) (hkernel : constantKernel A D)
    (herror : ∀ f, |S f| ≤ ε * D f) :
    (∀ f, 0 ≤ D f + S f) ∧ constantKernel A (fun f => D f + S f) := by
  have hlow : ∀ f, (1 - ε) * D f ≤ D f + S f := by
    intro f
    have he := herror f
    linarith [neg_abs_le (S f)]
  have hpositive : ∀ f, 0 ≤ D f + S f := fun f =>
    (mul_nonneg (sub_pos.mpr hε).le (hD f)).trans (hlow f)
  refine ⟨hpositive, ?_⟩
  intro f
  rw [← hkernel f]
  constructor
  · intro hf
    have hDf : D f ≤ 0 := by
      have hprod : (1 - ε) * D f ≤ 0 := by simpa only [hf] using hlow f
      by_contra h
      exact (not_lt_of_ge hprod) (mul_pos (sub_pos.mpr hε) (lt_of_not_ge h))
    exact le_antisymm hDf (hD f)
  · intro hf
    have hs : S f = 0 := by
      apply abs_eq_zero.mp
      have he : |S f| ≤ 0 := by simpa only [hf, mul_zero] using herror f
      exact le_antisymm he (abs_nonneg _)
    simp only [hf, hs, add_zero]

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_schur_step
#print axioms AndersonAC.SolS78.assembly_schur_prefix
#print axioms AndersonAC.SolS78.operation_energy_error_supported
#print axioms AndersonAC.SolS78.constant_kernel_of_absolute_error
