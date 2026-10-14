import AndersonAC.S78.WeightedEndpoints
import AndersonAC.S78.LocalSurvivorEnergy
import AndersonAC.S78.AssemblySmallness
import AndersonAC.S78.EnergyInputs

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

theorem masked_pair_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Finset ι) (u : ι → ι → ℝ) :
    (∑ i, ∑ j, if i ∈ B ∧ j ∈ B then u i j else 0) =
      ∑ i ∈ B, ∑ j ∈ B, u i j := by
  classical
  have hinner : ∀ i ∈ B,
      (∑ j ∈ B, u i j) = ∑ j, if i ∈ B ∧ j ∈ B then u i j else 0 := by
    intro i hi
    calc
      _ = ∑ j ∈ B, if i ∈ B ∧ j ∈ B then u i j else 0 :=
        Finset.sum_congr rfl (fun j hj => by simp [hi, hj])
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
        intro j _ hj
        simp [hj])
  symm
  calc
    _ = ∑ i ∈ B, ∑ j, if i ∈ B ∧ j ∈ B then u i j else 0 :=
      Finset.sum_congr rfl hinner
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
      intro i _ hi
      simp [hi])

theorem ward_energy_of_damping_upper {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Finset ι) (p : ι → ℝ) (h : Matrix ι ι ℂ) (C : ℝ)
    (hp : ∀ i ∈ B, 0 ≤ p i ∧ p i ≤ C) (f : ι → ℝ) :
    wardEnergy B p h f ≤ C ^ 2 / 2 *
      (∑ i ∈ B, ∑ j ∈ B, ‖h i j‖ ^ 2 * (f i - f j) ^ 2) := by
  unfold wardEnergy
  calc
    _ ≤ (1 / 2 : ℝ) *
        (∑ i ∈ B, ∑ j ∈ B, C ^ 2 * ‖h i j‖ ^ 2 * (f i - f j) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hC : 0 ≤ C := (hp i hi).1.trans (hp i hi).2
      have hprod : p i * p j ≤ C ^ 2 := by
        simpa only [pow_two] using mul_le_mul (hp i hi).2 (hp j hj).2 (hp j hj).1 hC
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem assembly_local_split_nonneg {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (α v : Torus d m → ℝ) :
    0 ≤ assemblyLocalSplit I a α v := by
  unfold assemblyLocalSplit
  apply add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply mul_nonneg (inv_nonneg.mpr I.positive.2.2.1.le)
  unfold cubeGradient
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> positivity

/-- The actual near survivor difference has the small weighted energy
needed before applying Cauchy--Schwarz to its cross term. -/
theorem assembly_near_difference_energy (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cloc : ℝ, 0 < Cloc ∧
    ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) (I : AssemblyInput d m k t b r)
      (a : Fin k) (f α v : Torus d m → ℝ),
      (∀ i ∈ (I.state 0).active, f i = α i + v i) →
      wardEnergy (assemblyNearSites I a) (fun i => (r i).im)
        (survivorDifference (I.state a.castSucc) (I.state a.succ) t) f ≤
        Cloc * I.C ^ 3 * t ^ (0.25 * delta) * assemblyLocalSplit I a α v := by
  classical
  obtain ⟨Cloc, hCloc, hloc⟩ := weighted_local_energy_proof d hd
  refine ⟨Cloc, hCloc, ?_⟩
  intro m k t b r I a f α v hsplit
  have ht := I.positive.1
  have hCpos : 0 < I.C := lt_of_lt_of_le (by norm_num) I.positive.2.2.2.2.2.1
  let B := assemblyNearSites I a
  let H := survivorDifference (I.state a.castSucc) (I.state a.succ) t
  let w : Matrix (Torus d m) (Torus d m) ℝ :=
    fun i j => if i ∈ B ∧ j ∈ B then ‖H i j‖ ^ 2 else 0
  have hB₀ : B ⊆ (I.state 0).active := fun i hi =>
    assembly_active_subset_initial I a.succ (Finset.mem_inter.mp hi).2
  have hDs : 1 ≤ I.Ds := by
    have hν : 0 ≤ nu d := by unfold nu delta; positivity
    have hpow : 1 ≤ t ^ (-8 - nu d) := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_ge I.positive.1 I.positive.2.1
          (by linarith : -8 - nu d ≤ 0))
    exact hpow.trans I.scaleRadius.1
  have hwle : ∀ i j, w i j ≤ ‖H i j‖ ^ 2 := by
    intro i j
    dsimp [w]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hrow : ∀ i, (∑ j, w i j) ≤ I.C * t ^ (0.25 * delta) := by
    intro i
    exact (Finset.sum_le_sum (fun j _ => hwle i j)).trans (I.rowChange a i)
  have htotal : (∑ i, ∑ j, w i j) ≤ I.C * t ^ (-1 - 0.47 * delta) := by
    exact (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hwle i j))).trans
      (I.totalChange a)
  have hsym := survivor_difference_symmetric (I.state a.castSucc) (I.state a.succ) r t
    (I.physical a.castSucc) (I.physical a.succ)
  have hw : ∀ i j, 0 ≤ w i j ∧ w i j = w j i := by
    intro i j
    constructor
    · dsimp [w]; split_ifs <;> positivity
    · have heq : H i j = H j i := hsym i j
      dsimp only [w]
      rw [heq]
      simp only [and_comm]
  have hsupp : ∀ i j,
      i ∉ cube d m (I.anchor a) (100 * I.Ds) ∩ (I.state 0).active ∨
      j ∉ cube d m (I.anchor a) (100 * I.Ds) ∩ (I.state 0).active → w i j = 0 := by
    intro i j h
    have hsub : B ⊆ cube d m (I.anchor a) (100 * I.Ds) ∩ (I.state 0).active :=
      fun x hx => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hB₀ hx⟩
    have hn : ¬ (i ∈ B ∧ j ∈ B) := by
      rintro ⟨hi, hj⟩
      exact h.elim (fun hn => hn (hsub hi)) (fun hn => hn (hsub hj))
    simp [w, hn]
  have hweighted := hloc m (I.anchor a) (100 * I.Ds) b
    (I.C * t ^ (0.25 * delta)) (I.C * t ^ (-1 - 0.47 * delta))
    (I.state 0).active w α v (by linarith) (by linarith [I.embedded])
    I.positive.2.2.1 (by positivity) (by positivity) hw hsupp hrow htotal
  have hsum : (∑ i, ∑ j, w i j * ((α i + v i) - (α j + v j)) ^ 2) =
      ∑ i ∈ B, ∑ j ∈ B, ‖H i j‖ ^ 2 * (f i - f j) ^ 2 := by
    calc
      _ = ∑ i, ∑ j, if i ∈ B ∧ j ∈ B then
          ‖H i j‖ ^ 2 * ((α i + v i) - (α j + v j)) ^ 2 else 0 := by
        simp only [w, ite_mul, zero_mul]
      _ = ∑ i ∈ B, ∑ j ∈ B,
          ‖H i j‖ ^ 2 * ((α i + v i) - (α j + v j)) ^ 2 := masked_pair_sum B _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hsplit i (hB₀ hi), ← hsplit j (hB₀ hj)]
  rw [hsum, show 2 * (100 * I.Ds) = 200 * I.Ds by ring] at hweighted
  have hcoeff := survivor_weight_coefficient I.C t b I.positive.2.2.2.2.2.1
    I.positive.1 I.positive.2.1 I.positive.2.2.2.1
  have hW := assembly_local_split_nonneg I a α v
  have hweighted' : (∑ i ∈ B, ∑ j ∈ B, ‖H i j‖ ^ 2 * (f i - f j) ^ 2) ≤
      Cloc * (2 * I.C * t ^ (0.25 * delta)) * assemblyLocalSplit I a α v := by
    exact hweighted.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoeff hCloc.le) hW)
  have hp : ∀ i ∈ B, 0 ≤ (r i).im ∧ (r i).im ≤ I.C :=
    fun i _ => ⟨I.positive.2.2.2.2.1.le.trans (I.damping i).1, (I.damping i).2.1⟩
  calc
    _ ≤ I.C ^ 2 / 2 * (∑ i ∈ B, ∑ j ∈ B, ‖H i j‖ ^ 2 * (f i - f j) ^ 2) :=
      ward_energy_of_damping_upper B _ H I.C hp f
    _ ≤ I.C ^ 2 / 2 *
        (Cloc * (2 * I.C * t ^ (0.25 * delta)) * assemblyLocalSplit I a α v) :=
      mul_le_mul_of_nonneg_left hweighted' (by positivity)
    _ = _ := by ring

theorem assembly_near_change_bound (hcut : LocalCutoffInput)
    (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ Cnear : ℝ, 0 < Cnear ∧
    ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) (I : AssemblyInput d m k t b r),
    I.C = C → ∀ (a : Fin k),
    (∀ F, endpointEnergy (I.state a.castSucc) r t F ≤
      (2 * C) * spatialEnergy (nnGraph d m) (I.state 0).active b F) →
    ∀ (f α v : Torus d m → ℝ),
    (∀ i ∈ (I.state 0).active, f i = α i + v i) →
    |assemblyNearChange I a f| ≤
      Cnear * t ^ (0.125 * delta) * assemblyLocalSplit I a α v := by
  obtain ⟨Cloc, hCloc, hdiff⟩ := assembly_near_difference_energy d hd
  obtain ⟨Ccut, hCcut, hold⟩ := assembly_old_near_energy hcut d hd
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  refine ⟨2 * Real.sqrt (2 * C * Ccut) * Real.sqrt (Cloc * C ^ 3) + Cloc * C ^ 3,
    by positivity, ?_⟩
  intro m k t b r I hIC a hpre f α v hsplit
  have hW := assembly_local_split_nonneg I a α v
  have hOld : wardEnergy (assemblyNearSites I a) (fun i => (r i).im)
      (normalizedInverse (I.state a.castSucc) t) f ≤
      (2 * C * Ccut) * assemblyLocalSplit I a α v :=
    hold m k t b r I a (2 * C) (by positivity) hpre f α v hsplit
  have hDiff : wardEnergy (assemblyNearSites I a) (fun i => (r i).im)
      (survivorDifference (I.state a.castSucc) (I.state a.succ) t) f ≤
      (Cloc * C ^ 3) * t ^ (0.25 * delta) * assemblyLocalSplit I a α v := by
    simpa only [hIC] using hdiff m k t b r I a f α v hsplit
  have h := survivor_local_change_bound (I.state a.castSucc) (I.state a.succ) r t
    (assemblyNearSites I a) (fun i hi => (Finset.mem_inter.mp hi).2) f
    (assemblyLocalSplit I a α v) (2 * C * Ccut) (Cloc * C ^ 3) (0.25 * delta)
    (fun i _ => I.positive.2.2.2.2.1.le.trans (I.damping i).1)
    hW (by positivity) (by positivity) I.positive.1 I.positive.2.1
    (by norm_num [delta]) hOld hDiff
  simpa only [assemblyNearChange, show (0.25 * delta) / 2 = 0.125 * delta by ring] using h

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_near_difference_energy
#print axioms AndersonAC.SolS78.assembly_near_change_bound
