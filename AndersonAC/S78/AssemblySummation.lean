import AndersonAC.S78.Definitions

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

theorem gradient_energy_nonneg {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (v : ι → ℝ) : 0 ≤ gradientEnergy G v := by
  classical
  unfold gradientEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> positivity

theorem spatial_energy_nonneg {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (hb : 0 < b) (f : ι → ℝ) : 0 ≤ spatialEnergy G A b f := by
  unfold spatialEnergy
  apply le_csInf
  · exact ⟨(∑ i ∈ A, (f i) ^ 2) + b⁻¹ * gradientEnergy G 0,
      f, 0, (by intro i hi; simp), rfl⟩
  · rintro e ⟨α, v, hsplit, rfl⟩
    exact add_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _)
      (mul_nonneg (inv_nonneg.mpr hb.le) (gradient_energy_nonneg G v))

/-- The common spatial split is minimized only after all operation errors
have been summed. This lemma performs that last infimum step. -/
theorem spatial_bound_of_all_splits {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b B S : ℝ) (hB : 0 ≤ B) (f : ι → ℝ)
    (hbound : ∀ α v : ι → ℝ, (∀ i ∈ A, f i = α i + v i) →
      |S| ≤ B * ((∑ i ∈ A, (α i) ^ 2) + b⁻¹ * gradientEnergy G v)) :
    |S| ≤ B * spatialEnergy G A b f := by
  by_cases hB0 : B = 0
  · have h := hbound f 0 (by intro i hi; simp)
    simpa only [hB0, zero_mul] using h
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hquot : |S| / B ≤ spatialEnergy G A b f := by
      unfold spatialEnergy
      apply le_csInf
      · exact ⟨(∑ i ∈ A, (f i) ^ 2) + b⁻¹ * gradientEnergy G 0,
          f, 0, (by intro i hi; simp), rfl⟩
      · rintro e ⟨α, v, hsplit, rfl⟩
        apply (div_le_iff₀ hBp).mpr
        simpa only [mul_comm B] using hbound α v hsplit
    simpa only [mul_comm B] using (div_le_iff₀ hBp).mp hquot

/-- Pointwise halo overlap bounds the sum of all retained local masses. -/
theorem sum_local_weights_overlap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Q : κ → Finset ι) (A : Finset ι) (w : ι → ℝ) (M : ℝ)
    (hw : ∀ i ∈ A, 0 ≤ w i) (hM : ∀ i, (overlap Q i : ℝ) ≤ M) :
    (∑ a : κ, ∑ i ∈ Q a ∩ A, w i) ≤ M * ∑ i ∈ A, w i := by
  classical
  have hlocal : ∀ a : κ, (∑ i ∈ Q a ∩ A, w i) =
      ∑ i ∈ A, if i ∈ Q a then w i else 0 := by
    intro a
    have hset : Q a ∩ A = A.filter fun i => i ∈ Q a := by ext i; simp [and_comm]
    rw [hset, Finset.sum_filter]
  simp_rw [hlocal]
  rw [Finset.sum_comm]
  calc
    (∑ i ∈ A, ∑ a : κ, if i ∈ Q a then w i else 0) =
        ∑ i ∈ A, (overlap Q i : ℝ) * w i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, overlap]
      apply congrArg (fun S : Finset κ => (S.card : ℝ) * w i)
      ext a
      simp
    _ ≤ ∑ i ∈ A, M * w i :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hM i) (hw i hi)
    _ = M * ∑ i ∈ A, w i := (Finset.mul_sum ..).symm

/-- A cube family with bounded vertex overlap also has bounded overlap of
its internal edge energies. -/
theorem sum_cube_gradients_overlap {κ : Type} [Fintype κ] (d m : ℕ)
    (Q : κ → Finset (Torus d m)) (v : Torus d m → ℝ) (M : ℝ)
    (hM : ∀ i, (overlap Q i : ℝ) ≤ M) :
    (∑ a : κ, cubeGradient d m (Q a) v) ≤ M * gradientEnergy (nnGraph d m) v := by
  classical
  let w := fun i : Torus d m => ∑ j : Torus d m,
    if (nnGraph d m).Adj i j then (v i - v j) ^ 2 else 0
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  have hlocal : ∀ a, cubeGradient d m (Q a) v ≤ (1 / 2 : ℝ) * ∑ i ∈ Q a, w i := by
    intro a
    unfold cubeGradient
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro j hj hnj
    split_ifs <;> positivity
  have hweights := sum_local_weights_overlap Q Finset.univ w M (fun i hi => hw i) hM
  simp only [Finset.inter_univ] at hweights
  calc
    (∑ a : κ, cubeGradient d m (Q a) v) ≤ ∑ a : κ, (1 / 2 : ℝ) * ∑ i ∈ Q a, w i :=
      Finset.sum_le_sum fun a ha => hlocal a
    _ = (1 / 2 : ℝ) * (∑ a : κ, ∑ i ∈ Q a, w i) := (Finset.mul_sum ..).symm
    _ ≤ (1 / 2 : ℝ) * (M * ∑ i, w i) := mul_le_mul_of_nonneg_left hweights (by norm_num)
    _ = M * gradientEnergy (nnGraph d m) v := by unfold gradientEnergy; dsimp [w]; ring

/-- The actual assembly halo-overlap field controls the one common split. -/
theorem assembly_split_overlap {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (α v : Torus d m → ℝ) :
    (∑ a : Fin k, ((∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) +
      b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v)) ≤
    I.C * t ^ (-(d : ℝ) * nu d) *
      ((∑ i ∈ (I.state 0).active, (α i) ^ 2) + b⁻¹ * gradientEnergy (nnGraph d m) v) := by
  have hα := sum_local_weights_overlap (fun a => cube d m (I.anchor a) (200 * I.Ds))
    (I.state 0).active (fun i => (α i) ^ 2) _ (fun i hi => sq_nonneg _) I.haloOverlap
  have hv := sum_cube_gradients_overlap d m (fun a => cube d m (I.anchor a) (200 * I.Ds))
    v _ I.haloOverlap
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    _ ≤ I.C * t ^ (-(d : ℝ) * nu d) * (∑ i ∈ (I.state 0).active, (α i) ^ 2) +
        b⁻¹ * (I.C * t ^ (-(d : ℝ) * nu d) * gradientEnergy (nnGraph d m) v) :=
      add_le_add hα (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr I.positive.2.2.1.le))
    _ = _ := by ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.spatial_bound_of_all_splits
#print axioms AndersonAC.SolS78.sum_local_weights_overlap
#print axioms AndersonAC.SolS78.assembly_split_overlap
