import AndersonAC.AgentS6.TrialStep
import AndersonAC.AgentS6.LeverageFacts
import AndersonAC.L64.Inputs

noncomputable section
open Matrix Finset ComplexConjugate

namespace AndersonAC.AgentS6Row

open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extend an active block by the identity on inactive coordinates. -/
def extendBlock (A : Finset ι) (S : Matrix A A ℂ) : Matrix ι ι ℂ :=
  fun i j => if hi : i ∈ A then if hj : j ∈ A then S ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else if i = j then 1 else 0

lemma extendBlock_active (A : Finset ι) (S : Matrix A A ℂ) (i j : A) :
    extendBlock A S i j = S i j := by simp [extendBlock, i.2, j.2]

lemma extendBlock_symm (A : Finset ι) (S : Matrix A A ℂ) (hS : Sᵀ = S) :
    (extendBlock A S)ᵀ = extendBlock A S := by
  ext i j
  simp only [Matrix.transpose_apply]
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
  · simp only [extendBlock, dif_pos hi, dif_pos hj]
    exact congrFun (congrFun hS ⟨i, hi⟩) ⟨j, hj⟩
  · have hji : j ≠ i := fun h => hj (h ▸ hi)
    simp [extendBlock, hi, hj, hji]
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [extendBlock, hi, hj, hij]
  · simp only [extendBlock, dif_neg hi, dif_neg hj]
    congr 1
    exact propext eq_comm

lemma extendBlock_unitary (A : Finset ι) (S : Matrix A A ℂ) (hS : Sᴴ * S = 1) :
    (extendBlock A S)ᴴ * extendBlock A S = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · have he : ∑ k, star (extendBlock A S k i) * extendBlock A S k j =
          ∑ k : A, star (S k ⟨i, hi⟩) * S k ⟨j, hj⟩ := by
        calc
          _ = ∑ k ∈ A, star (extendBlock A S k i) * extendBlock A S k j := by
            symm
            apply Finset.sum_subset (Finset.subset_univ A)
            intro k hk hka
            have hki : k ≠ i := fun h => hka (h ▸ hi)
            simp [extendBlock, hka, hki]
          _ = _ := by
            rw [← Finset.sum_coe_sort A (fun k : ι => star (extendBlock A S k i) * extendBlock A S k j)]
            exact Finset.sum_congr rfl fun k _ => by simp [extendBlock, k.2, hi, hj]
      rw [he]
      have hh := congrFun (congrFun hS ⟨i, hi⟩) ⟨j, hj⟩
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Subtype.ext_iff] using hh
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k ∈ A
      · simp [extendBlock, hk, hj]
      · have hki : k ≠ i := fun h => hk (h ▸ hi)
        simp [extendBlock, hk, hki]
  · rw [Finset.sum_eq_single i]
    · by_cases hj : j ∈ A
      · have hij : i ≠ j := fun h => hi (h ▸ hj)
        simp [extendBlock, hi, hj, hij]
      · simp [extendBlock, hi, hj]
    · intro k _ hki
      by_cases hk : k ∈ A <;> simp [extendBlock, hk, hi, hki]
    · simp

/-- Scattering matrix with inactive coordinates retained as identity rows. -/
def ambientScattering {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core) :
    Matrix ι ι ℂ := extendBlock s.active (scattering t (fun i : s.active => r i) (trialInverse t r s))

lemma ambientScattering_unitary {core : Finset ι} {t : ℝ} (ht : 0 < t)
    (r : ι → ℂ) (hr : ∀ i, 0 < (r i).im) (s : TrialState core) :
    (ambientScattering t r s)ᴴ * ambientScattering t r s = 1 := by
  apply extendBlock_unitary
  exact AndersonAC.L64.scat_unitary _ (fun i : s.active => (hr i).le)
    (AndersonAC.L64.ward_left s.symmetric
      (AndersonAC.L64.isUnit_det_damped s.M t (fun i : s.active => r i)
        s.symmetric ht (fun i => hr i)))

lemma ambientScattering_symm {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core) :
    (ambientScattering t r s)ᵀ = ambientScattering t r s := by
  apply extendBlock_symm
  exact AndersonAC.L64.scat_transpose _ (AndersonAC.L64.resolvent_transpose s.symmetric)

lemma ambientCross_eq {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (i : ι) (hi : i ∉ core) :
    AndersonAC.L64.crossRow (ambientScattering t r s) core i = trialCross t r s i := by
  funext b
  have hb := s.core_active b.2
  have hib : i ≠ (b : ι) := fun h => hi (h ▸ b.2)
  by_cases ha : i ∈ s.active <;>
    simp [AndersonAC.L64.crossRow, ambientScattering, extendBlock, trialCross, ha, hi, hb, hib]

lemma ambientGram_eq {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core) :
    AndersonAC.L64.gram (ambientScattering t r s) core coreᶜ = AndersonAC.S6.gram (trialCross t r s) := by
  ext b b'
  simp only [AndersonAC.L64.gram, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    AndersonAC.S6.gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  calc
    _ = ∑ i ∈ coreᶜ, star (trialCross t r s i b) * trialCross t r s i b' := by
      apply Finset.sum_congr rfl
      intro i hi
      have he := ambientCross_eq t r s i (Finset.mem_compl.mp hi)
      rw [congrFun he b, congrFun he b']
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ coreᶜ)
      intro i _ hi
      have hic : i ∈ core := by simpa using hi
      have hzero : ∀ b : core, trialCross t r s i b = 0 := by
        intro b
        simp [trialCross, s.core_active hic, hic]
      simp [hzero]

lemma ambientLeverage_eq {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (τ : ℝ) (i : ι) (hi : i ∉ core) :
    AndersonAC.L64.ridgeLev (ambientScattering t r s) core coreᶜ τ i = trialWeights t r s τ i := by
  unfold AndersonAC.L64.ridgeLev trialWeights leverage ridgeProjection ridgeGram
  rw [ambientGram_eq, ambientCross_eq t r s i hi]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Pi.star_apply]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext b
  congr 1
  funext b'
  ring

end AndersonAC.AgentS6Row
