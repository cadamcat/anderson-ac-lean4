import AndersonAC.S78Moment.Moments
import AndersonAC.S78Moment.Translation
import AndersonAC.S78.AssemblySummation

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

theorem physical_distance_shift (d m : ℕ) (x y a : Torus d m) :
    physicalDistance d m (x + a) (y + a) = physicalDistance d m x y := by
  have hle : ∀ x y a : Torus d m,
      (nnGraph d m).dist (x + a) (y + a) ≤ (nnGraph d m).dist x y := by
    intro x y a
    obtain ⟨p, hp⟩ := nnGraph_connected_proof.exists_walk_length_eq_dist x y
    have h := (nnGraph d m).dist_le (p.map (nnGraph_shiftHom a))
    change (nnGraph d m).dist (x + a) (y + a) ≤ (p.map (nnGraph_shiftHom a)).length at h
    rw [SimpleGraph.Walk.length_map] at h
    exact h.trans_eq hp
  have hforward := hle x y a
  have hback := hle (x + a) (y + a) (-a)
  simp only [add_neg_cancel_right] at hback
  unfold physicalDistance
  exact_mod_cast le_antisymm hforward hback

/-- Symmetric nonnegative kernels with bounded row sums control the local
mass part of the common spatial split. -/
theorem pair_energy_of_row_bound {ι : Type} [Fintype ι]
    (w : ι → ι → ℝ) (M : ℝ) (α : ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hsym : ∀ i j, w i j = w j i)
    (hrow : ∀ i, (∑ j, w i j) ≤ M) :
    (∑ i, ∑ j, w i j * (α i - α j) ^ 2) ≤ 4 * M * ∑ i, (α i) ^ 2 := by
  let Y := ∑ i, ∑ j, w i j * (α i) ^ 2
  have hleft : Y ≤ M * ∑ i, (α i) ^ 2 := by
    calc
      Y = ∑ i, (α i) ^ 2 * ∑ j, w i j := by
        simp only [Y, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i, (α i) ^ 2 * M := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
      _ = M * ∑ i, (α i) ^ 2 := by rw [← Finset.sum_mul, mul_comm]
  have hright : (∑ i, ∑ j, w i j * (α j) ^ 2) = Y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsym i j]
  calc
    _ ≤ ∑ i, ∑ j, (2 * w i j * (α i) ^ 2 + 2 * w i j * (α j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hs : (α i - α j) ^ 2 ≤ 2 * (α i) ^ 2 + 2 * (α j) ^ 2 := by
        nlinarith [sq_nonneg (α i + α j)]
      exact (mul_le_mul_of_nonneg_left hs (hw i j)).trans_eq (by ring)
    _ = 2 * Y + 2 * (∑ i, ∑ j, w i j * (α j) ^ 2) := by
      simp only [Y, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    _ ≤ _ := by rw [hright]; linarith

/-- Translation of shortest paths converts an exponential displacement
moment into a full gradient-energy bound. -/
theorem exponential_gradient_energy (d m : ℕ) (c t : ℝ) (v : Torus d m → ℝ) :
    (∑ i, ∑ j, Real.exp (-c * t * physicalDistance d m i j) * (v i - v j) ^ 2) ≤
      (∑ u, Real.exp (-c * t * physicalDistance d m 0 u) * physicalDistance d m 0 u ^ 2) *
        gradientEnergy (nnGraph d m) v := by
  have hreindex : ∀ i : Torus d m,
      (∑ j, Real.exp (-c * t * physicalDistance d m i j) * (v i - v j) ^ 2) =
        ∑ u, Real.exp (-c * t * physicalDistance d m 0 u) * (v (i + u) - v i) ^ 2 := by
    intro i
    calc
      _ = ∑ u, Real.exp (-c * t * physicalDistance d m i (i + u)) * (v i - v (i + u)) ^ 2 :=
        (Equiv.sum_comp (Equiv.addLeft i) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        have hd : physicalDistance d m i (i + u) = physicalDistance d m 0 u := by
          simpa only [zero_add, add_comm u i] using physical_distance_shift d m 0 u i
        rw [hd]
        congr 1
        ring
  calc
    _ = ∑ i, ∑ u, Real.exp (-c * t * physicalDistance d m 0 u) * (v (i + u) - v i) ^ 2 := by
      exact Finset.sum_congr rfl fun i hi => hreindex i
    _ = ∑ u, Real.exp (-c * t * physicalDistance d m 0 u) *
        ∑ i, (v (i + u) - v i) ^ 2 := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ u, Real.exp (-c * t * physicalDistance d m 0 u) *
        (physicalDistance d m 0 u ^ 2 * gradientEnergy (nnGraph d m) v) :=
      Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left
        (translation_energy_proof d m v u) (Real.exp_pos _).le
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

/-- A global exponential envelope costs only a fixed polynomial factor
against the mass and gradient parts of the one common spatial split. -/
theorem exponential_split_energy (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
      ∀ α v : Torus d m → ℝ,
      (∑ i, ∑ j, Real.exp (-c * t * physicalDistance d m i j) *
        ((α i + v i) - (α j + v j)) ^ 2) ≤
      C * t ^ (-(d : ℝ) - 2) * ((∑ i, (α i) ^ 2) + gradientEnergy (nnGraph d m) v) := by
  obtain ⟨C₀, hC₀, h₀⟩ := lattice_exponential_moments_proof d 0 c hc
  obtain ⟨C₂, hC₂, h₂⟩ := lattice_exponential_moments_proof d 2 c hc
  simp only [pow_zero, mul_one, Nat.cast_zero, sub_zero] at h₀
  refine ⟨8 * C₀ + 2 * C₂, by positivity, ?_⟩
  intro m t ht ht1 α v
  let K := fun i j : Torus d m => Real.exp (-c * t * physicalDistance d m i j)
  let U := ∑ i, ∑ j, K i j * (α i - α j) ^ 2
  let V := ∑ i, ∑ j, K i j * (v i - v j) ^ 2
  let A := ∑ i, (α i) ^ 2
  let E := gradientEnergy (nnGraph d m) v
  have hA : 0 ≤ A := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hE : 0 ≤ E := gradient_energy_nonneg _ _
  have hU : U ≤ 4 * (C₀ * t ^ (-(d : ℝ))) * A := by
    apply pair_energy_of_row_bound K _ α (fun i j => (Real.exp_pos _).le) _
      (fun i => h₀ m t ht ht1 i)
    intro i j
    simp only [K, physicalDistance, SimpleGraph.dist_comm]
  have hV : V ≤ C₂ * t ^ (-(d : ℝ) - 2) * E := by
    exact (exponential_gradient_energy d m c t v).trans
      (mul_le_mul_of_nonneg_right (h₂ m t ht ht1 0) hE)
  have hUV : (∑ i, ∑ j, K i j * ((α i + v i) - (α j + v j)) ^ 2) ≤ 2 * U + 2 * V := by
    calc
      _ ≤ ∑ i, ∑ j, (2 * K i j * (α i - α j) ^ 2 + 2 * K i j * (v i - v j) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hs : ((α i + v i) - (α j + v j)) ^ 2 ≤
            2 * (α i - α j) ^ 2 + 2 * (v i - v j) ^ 2 := by
          nlinarith [sq_nonneg ((α i - α j) - (v i - v j))]
        exact (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le).trans_eq (by ring)
      _ = _ := by simp only [U, V, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
  have hpow : t ^ (-(d : ℝ)) ≤ t ^ (-(d : ℝ) - 2) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  calc
    _ ≤ 2 * U + 2 * V := hUV
    _ ≤ 2 * (4 * (C₀ * t ^ (-(d : ℝ))) * A) + 2 * (C₂ * t ^ (-(d : ℝ) - 2) * E) := by linarith
    _ = 8 * C₀ * t ^ (-(d : ℝ)) * A + 2 * C₂ * t ^ (-(d : ℝ) - 2) * E := by ring
    _ ≤ 8 * C₀ * t ^ (-(d : ℝ) - 2) * A + 2 * C₂ * t ^ (-(d : ℝ) - 2) * E := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ hA
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (8 * C₀ + 2 * C₂) * t ^ (-(d : ℝ) - 2) * (A + E) := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 8 * C₀ * t ^ (-(d : ℝ) - 2)) hE,
        mul_nonneg (by positivity : 0 ≤ 2 * C₂ * t ^ (-(d : ℝ) - 2)) hA]

/-- Distinct operation anchors can be summed through one torus moment;
the resulting kernel retains exponential decay in the pair displacement. -/
theorem anchored_exponential_sum (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
      ∀ (κ : Type) [Fintype κ] (z : κ → Torus d m), Function.Injective z →
      ∀ i j : Torus d m,
      (∑ a : κ, Real.exp (-c * t * (physicalDistance d m i (z a) + physicalDistance d m j (z a)))) ≤
        C * t ^ (-(d : ℝ)) * Real.exp (-(c / 2) * t * physicalDistance d m i j) := by
  obtain ⟨C, hC, hmoment⟩ := lattice_exponential_moments_proof d 0 (c / 2) (by positivity)
  simp only [pow_zero, mul_one, Nat.cast_zero, sub_zero] at hmoment
  refine ⟨C, hC, ?_⟩
  intro m t ht ht1 κ _ z hz i j
  classical
  let E := Real.exp (-(c / 2) * t * physicalDistance d m i j)
  let radial := fun x : Torus d m => Real.exp (-(c / 2) * t * physicalDistance d m i x)
  have hpoint : ∀ a : κ,
      Real.exp (-c * t * (physicalDistance d m i (z a) + physicalDistance d m j (z a))) ≤ E * radial (z a) := by
    intro a
    have htri : physicalDistance d m i j ≤ physicalDistance d m i (z a) + physicalDistance d m (z a) j := by
      unfold physicalDistance
      exact_mod_cast nnGraph_connected_proof.dist_triangle (u := i) (v := z a) (w := j)
    have hcomm : physicalDistance d m (z a) j = physicalDistance d m j (z a) := by
      simp only [physicalDistance, SimpleGraph.dist_comm]
    rw [hcomm] at htri
    have hj0 : 0 ≤ physicalDistance d m j (z a) := by unfold physicalDistance; positivity
    have hgeom : physicalDistance d m i j + physicalDistance d m i (z a) ≤
        2 * (physicalDistance d m i (z a) + physicalDistance d m j (z a)) := by linarith
    dsimp [E, radial]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hgeom (by positivity : 0 ≤ c * t / 2)
    nlinarith
  have hanchor : (∑ a : κ, radial (z a)) ≤ ∑ x : Torus d m, radial x := by
    calc
      _ = ∑ x ∈ Finset.univ.image z, radial x :=
        (Finset.sum_image (f := radial) (fun a ha b hb hab => hz hab)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro x hx hnx
        exact (Real.exp_pos _).le)
  calc
    _ ≤ ∑ a : κ, E * radial (z a) := Finset.sum_le_sum fun a ha => hpoint a
    _ = E * ∑ a : κ, radial (z a) := (Finset.mul_sum ..).symm
    _ ≤ E * ∑ x : Torus d m, radial x := mul_le_mul_of_nonneg_left hanchor (Real.exp_pos _).le
    _ ≤ E * (C * t ^ (-(d : ℝ))) := mul_le_mul_of_nonneg_left (hmoment m t ht ht1 i) (Real.exp_pos _).le
    _ = _ := by dsimp [E]; ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.physical_distance_shift
#print axioms AndersonAC.SolS78.exponential_gradient_energy
#print axioms AndersonAC.SolS78.exponential_split_energy
#print axioms AndersonAC.SolS78.anchored_exponential_sum
