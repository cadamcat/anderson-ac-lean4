import AndersonAC.S78.EnergyChange
import AndersonAC.S78.EndpointAlgebra
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.AssemblyForms

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

theorem ward_energy_matrix_congr {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h H : Matrix ι ι ℂ) (f : ι → ℝ)
    (hH : ∀ i ∈ A, ∀ j ∈ A, h i j = H i j) : wardEnergy A p h f = wardEnergy A p H f := by
  unfold wardEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hH i hi j hj]

theorem ward_energy_difference_congr {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h : Matrix ι ι ℂ) (f F : ι → ℝ)
    (hF : ∀ i ∈ A, ∀ j ∈ A, F i - F j = f i - f j) :
    wardEnergy A p h F = wardEnergy A p h f := by
  unfold wardEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hF i hi j hj]

/-- The near survivor cross term costs half the difference-energy exponent. -/
theorem ward_local_change_bound {ι : Type} (A : Finset ι) (p : ι → ℝ)
    (h a : Matrix ι ι ℂ) (f : ι → ℝ) (W C₀ C₁ t α : ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) (hW : 0 ≤ W) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 ≤ α)
    (hold : wardEnergy A p h f ≤ C₀ * W)
    (hdiff : wardEnergy A p a f ≤ C₁ * t ^ α * W) :
    |wardEnergy A p (h + a) f - wardEnergy A p h f| ≤
      (2 * Real.sqrt C₀ * Real.sqrt C₁ + C₁) * t ^ (α / 2) * W := by
  have htroot : Real.sqrt (t ^ α) = t ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hroots : Real.sqrt (C₀ * W) * Real.sqrt (C₁ * t ^ α * W) =
      Real.sqrt C₀ * Real.sqrt C₁ * t ^ (α / 2) * W := by
    rw [← Real.sqrt_mul (mul_nonneg hC₀ hW),
      show (C₀ * W) * (C₁ * t ^ α * W) = (C₀ * C₁ * t ^ α) * W ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg hW,
      Real.sqrt_mul (mul_nonneg hC₀ hC₁), Real.sqrt_mul hC₀, htroot]
  have hpow : t ^ α ≤ t ^ (α / 2) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  calc
    _ ≤ 2 * Real.sqrt (wardEnergy A p h f) * Real.sqrt (wardEnergy A p a f) +
        wardEnergy A p a f := ward_energy_change A p h a f hp
    _ ≤ 2 * Real.sqrt (C₀ * W) * Real.sqrt (C₁ * t ^ α * W) + C₁ * t ^ α * W := by
      gcongr
    _ = 2 * (Real.sqrt C₀ * Real.sqrt C₁ * t ^ (α / 2) * W) + C₁ * t ^ α * W := by
      rw [mul_assoc, hroots]
    _ ≤ 2 * (Real.sqrt C₀ * Real.sqrt C₁ * t ^ (α / 2) * W) + C₁ * t ^ (α / 2) * W := by
      gcongr
    _ = _ := by ring

theorem survivor_local_change_bound {ι : Type} [DecidableEq ι]
    (old next : Endpoint ι) (r : ι → ℂ) (t : ℝ) (B : Finset ι) (hB : B ⊆ next.active)
    (f : ι → ℝ) (W C₀ C₁ α : ℝ) (hp : ∀ i ∈ B, 0 ≤ (r i).im)
    (hW : 0 ≤ W) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 ≤ α)
    (hold : wardEnergy B (fun i => (r i).im) (normalizedInverse old t) f ≤ C₀ * W)
    (hdiff : wardEnergy B (fun i => (r i).im) (survivorDifference old next t) f ≤ C₁ * t ^ α * W) :
    |wardEnergy B (fun i => (r i).im) (normalizedInverse next t) f -
      wardEnergy B (fun i => (r i).im) (normalizedInverse old t) f| ≤
        (2 * Real.sqrt C₀ * Real.sqrt C₁ + C₁) * t ^ (α / 2) * W := by
  have heq := ward_energy_matrix_congr B (fun i => (r i).im) (normalizedInverse next t)
    (normalizedInverse old t + survivorDifference old next t) f
    (survivor_difference_identity old next t B hB)
  rw [heq]
  exact ward_local_change_bound B _ _ _ f W C₀ C₁ t α hp hW hC₀ hC₁ ht ht1 hα hold hdiff

/-- The old near-edge energy is controlled by the current prefix comparison
applied to the localized extension of the one initial spatial split. -/
theorem assembly_old_near_energy (hcut : LocalCutoffInput) (d : ℕ) (hd : 3 ≤ d) :
    ∃ Ccut : ℝ, 0 < Ccut ∧ ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
      (I : AssemblyInput d m k t b r) (a : Fin k) (Cpre : ℝ), 0 ≤ Cpre →
      (∀ F, endpointEnergy (I.state a.castSucc) r t F ≤
        Cpre * spatialEnergy (nnGraph d m) (I.state 0).active b F) →
      ∀ (f α v : Torus d m → ℝ), (∀ i ∈ (I.state 0).active, f i = α i + v i) →
      wardEnergy (cube d m (I.anchor a) (100 * I.Ds) ∩ (I.state a.succ).active)
        (fun i => (r i).im) (normalizedInverse (I.state a.castSucc) t) f ≤
        Cpre * Ccut * ((∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) +
          b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) := by
  obtain ⟨Ccut, hCcut, hcut⟩ := hcut d hd
  refine ⟨Ccut, hCcut, ?_⟩
  intro m k t b r I a Cpre hCpre hpre f α v hsplit
  have ht := I.positive.1
  have ht1 := I.positive.2.1
  have hν : 0 ≤ nu d := by unfold nu delta; positivity
  have hR : 1 ≤ I.Ds := by
    have hpow : 1 ≤ t ^ (-8 - nu d) := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith : -8 - nu d ≤ 0))
    exact hpow.trans I.scaleRadius.1
  obtain ⟨F, hF, hW⟩ := hcut m (I.anchor a) (100 * I.Ds) b (I.state 0).active α v
    (by linarith) (by linarith [I.embedded]) I.positive.2.2.1
  let B := cube d m (I.anchor a) (100 * I.Ds) ∩ (I.state a.succ).active
  have hB : B ⊆ (I.state a.castSucc).active := fun i hi => I.nested a (Finset.mem_inter.mp hi).2
  have hB₀ : B ⊆ (I.state 0).active := fun i hi =>
    assembly_active_subset_initial I a.succ (Finset.mem_inter.mp hi).2
  have hFdifference : ∀ i ∈ B, ∀ j ∈ B, F i - F j = f i - f j := by
    intro i hi j hj
    rw [hsplit i (hB₀ hi), hsplit j (hB₀ hj)]
    exact hF i (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hB₀ hi⟩)
      j (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hj).1, hB₀ hj⟩)
  have hc := I.positive.2.2.2.2.1
  calc
    _ = wardEnergy B (fun i => (r i).im) (normalizedInverse (I.state a.castSucc) t) F :=
      (ward_energy_difference_congr B _ _ f F hFdifference).symm
    _ ≤ endpointEnergy (I.state a.castSucc) r t F :=
      ward_energy_mono_active B _ hB _ _ F (fun i hi => hc.le.trans (I.damping i).1)
    _ ≤ Cpre * spatialEnergy (nnGraph d m) (I.state 0).active b F := hpre F
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hW hCpre
      simpa only [show 2 * (100 * I.Ds) = 200 * I.Ds by ring, mul_assoc] using h

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.ward_local_change_bound
#print axioms AndersonAC.SolS78.survivor_local_change_bound
#print axioms AndersonAC.SolS78.assembly_old_near_energy
