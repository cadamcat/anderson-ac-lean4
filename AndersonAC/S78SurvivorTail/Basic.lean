import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.EnergyInputs
import AndersonAC.S78.EndpointAlgebra
import AndersonAC.S78.EnergyChange

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.S78SurvivorTail
open AndersonAC.S78
open AndersonAC.SolS78

/-- Difference of squared moduli costs the cross term plus the square. -/
theorem normSq_sub_le (z a : ℂ) :
    |‖z + a‖ ^ 2 - ‖z‖ ^ 2| ≤ 2 * ‖z‖ * ‖a‖ + ‖a‖ ^ 2 := by
  have hcross : |(star z * a).re| ≤ ‖z‖ * ‖a‖ := by
    calc |(star z * a).re| ≤ ‖star z * a‖ := Complex.abs_re_le_norm _
      _ = ‖z‖ * ‖a‖ := by rw [norm_mul, norm_star]
  have h_eq : ‖z + a‖ ^ 2 - ‖z‖ ^ 2 = 2 * (star z * a).re + ‖a‖ ^ 2 := by
    have h := AndersonAC.SolS78.endpoint_modulus_change_proof z a
    linarith
  have h1 : |2 * (star z * a).re| = 2 * |(star z * a).re| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : |(‖a‖ ^ 2 : ℝ)| = ‖a‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
  calc |‖z + a‖ ^ 2 - ‖z‖ ^ 2|
      = |2 * (star z * a).re + ‖a‖ ^ 2| := by rw [h_eq]
    _ ≤ |2 * (star z * a).re| + |‖a‖ ^ 2| := abs_add_le _ _
    _ = 2 * |(star z * a).re| + ‖a‖ ^ 2 := by rw [h1, h2]
    _ ≤ _ := by nlinarith [hcross, sq_nonneg (‖a‖)]

-- Symmetry is used to keep the old/new kernels on the retained pairs.
theorem old_symmetric_of_physical {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (i j : Torus d m) :
    normalizedInverse (I.state a.castSucc) t i j =
      normalizedInverse (I.state a.castSucc) t j i :=
  normalized_endpoint_symmetric _ _ _ (I.physical _) i j

theorem new_symmetric_of_physical {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (i j : Torus d m) :
    normalizedInverse (I.state a.succ) t i j =
      normalizedInverse (I.state a.succ) t j i :=
  normalized_endpoint_symmetric _ _ _ (I.physical _) i j

/-- Ward energy as a single product sum. -/
theorem wardEnergy_prod {d m : ℕ} (S : Finset (Torus d m)) (p : Torus d m → ℝ)
    (h : Matrix (Torus d m) (Torus d m) ℂ) (f : Torus d m → ℝ) :
    wardEnergy S p h f = (1 / 2 : ℝ) * ∑ q ∈ S.product S,
      p q.1 * p q.2 * ‖h q.1 q.2‖ ^ 2 * (f q.1 - f q.2) ^ 2 := by
  unfold wardEnergy
  congr 1
  exact (Finset.sum_product' S S (fun i j => p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2)).symm

/-- The survivor tail is exactly the far-pair difference, since the near
cube part is subtracted. -/
theorem tail_eq_far_sum {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) :
    assemblySurvivorTail I a f = (1 / 2 : ℝ) *
      ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
      (r q.1).im * (r q.2).im *
        (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) *
        (f q.1 - f q.2) ^ 2 := by
  classical
  have hNsub : assemblyNearSites I a ⊆ (I.state a.succ).active :=
    Finset.inter_subset_right
  have hprod : (assemblyNearSites I a).product (assemblyNearSites I a) ⊆
      (I.state a.succ).active.product (I.state a.succ).active :=
    Finset.product_subset_product hNsub hNsub
  have hE : endpointEnergy (I.state a.succ) r t f =
      wardEnergy (I.state a.succ).active (fun i => (r i).im)
        (normalizedInverse (I.state a.succ) t) f := rfl
  have hAnew := wardEnergy_prod (d := d) (m := m)
    (I.state a.succ).active (fun i => (r i).im)
    (normalizedInverse (I.state a.succ) t) f
  have hAold := wardEnergy_prod (d := d) (m := m)
    (I.state a.succ).active (fun i => (r i).im)
    (normalizedInverse (I.state a.castSucc) t) f
  have hNnew := wardEnergy_prod (d := d) (m := m)
    (assemblyNearSites I a) (fun i => (r i).im)
    (normalizedInverse (I.state a.succ) t) f
  have hNold := wardEnergy_prod (d := d) (m := m)
    (assemblyNearSites I a) (fun i => (r i).im)
    (normalizedInverse (I.state a.castSucc) t) f
  have hsplit_new : ∑ q ∈ (I.state a.succ).active.product (I.state a.succ).active,
        (r q.1).im * (r q.2).im *
          ‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 * (f q.1 - f q.2) ^ 2 =
      (∑ q ∈ (I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a),
        (r q.1).im * (r q.2).im *
          ‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 * (f q.1 - f q.2) ^ 2) +
      ∑ q ∈ (assemblyNearSites I a).product (assemblyNearSites I a),
        (r q.1).im * (r q.2).im *
          ‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 * (f q.1 - f q.2) ^ 2 := by
    rw [Finset.sum_sdiff hprod]
  have hsplit_old : ∑ q ∈ (I.state a.succ).active.product (I.state a.succ).active,
        (r q.1).im * (r q.2).im *
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2 * (f q.1 - f q.2) ^ 2 =
      (∑ q ∈ (I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a),
        (r q.1).im * (r q.2).im *
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2 * (f q.1 - f q.2) ^ 2) +
      ∑ q ∈ (assemblyNearSites I a).product (assemblyNearSites I a),
        (r q.1).im * (r q.2).im *
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2 * (f q.1 - f q.2) ^ 2 := by
    rw [Finset.sum_sdiff hprod]
  simp only [assemblySurvivorTail, assemblyNearChange, hE, hAnew, hAold, hNnew, hNold,
    hsplit_new, hsplit_old]
  have hring : ∀ (a b e g : ℝ),
      (1 / 2 : ℝ) * (a + e) - (1 / 2) * (b + g) - ((1 / 2) * e - (1 / 2) * g) =
      (1 / 2) * a - (1 / 2) * b := fun a b e g => by ring
  rw [hring]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun q _ => by ring)

end AndersonAC.S78SurvivorTail
