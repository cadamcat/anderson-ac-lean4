import AndersonAC.AgentS6.TrialStep
import AndersonAC.S6.Scattering

/-! The trial cross block is a block of the unitary scattering matrix, hence has operator norm
at most one (06-clearing.tex:59–79, 680–682: "since `𝒞` is a block of a unitary matrix,
`m_* ≤ τ⁻¹`"). Needed for the initial ridge `τ = l_*^{-2}`. -/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

namespace AndersonAC.AgentS6

open AndersonAC.S6

theorem norm_le_one_of_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (h : ‖Xᴴ * X‖ ≤ 1) : ‖X‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg X]

theorem norm_diagonal_le_one {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℂ)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖(Matrix.diagonal v : Matrix n n ℂ)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr hv

theorem trialCross_norm_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {core : Finset ι}
    {t : ℝ} (ht : 0 < t) (r : ι → ℂ) (hr : ∀ i, 0 < (r i).im) (s : TrialState core) :
    ‖trialCross t r s‖ ≤ 1 := by
  classical
  set A := {i // i ∈ s.active}
  set B := {b // b ∈ core}
  set g := trialInverse t r s
  set S : Matrix A A ℂ := scattering t (fun i : A => r i) g
  set P : Matrix ι A ℂ := Matrix.of fun i a => if (i = (a : ι) ∧ i ∉ core) then 1 else 0
  set J : Matrix A B ℂ := Matrix.of fun a b => if (a : ι) = (b : ι) then 1 else 0
  -- unitarity of S
  have hDu : IsUnit (dampedMatrix s.M t (fun i : A => r i)).det :=
    damped_isUnit s.M s.symmetric ht _ (fun i => hr i)
  have hinv : AndersonAC.Blueprint.twoSidedInverse
      (s.M.map Complex.ofReal - (t : ℂ) • Matrix.diagonal (fun i : A => r i)) g :=
    ⟨Matrix.mul_nonsing_inv _ hDu, Matrix.nonsing_inv_mul _ hDu⟩
  have hMt : (s.M.map Complex.ofReal)ᵀ = s.M.map Complex.ofReal := by
    rw [← Matrix.transpose_map]; congr 1; exact s.symmetric
  have hunit := (AndersonAC.SolS6.scattering_from_inverse (s.M.map Complex.ofReal) g t
    (fun i : A => r i) hMt (fun i j => by simp) (fun i => (hr i).le) hinv).2
  have hSS : Sᴴ * S = 1 := by
    exact mul_eq_one_comm.mp hunit
  -- factorization
  have hfac : trialCross t r s = P * S * J := by
    ext i b
    simp only [Matrix.mul_apply, P, J, Matrix.of_apply]
    unfold trialCross
    by_cases hi : i ∈ s.active
    · rw [dif_pos hi]
      by_cases hc : i ∈ core
      · rw [if_pos hc]
        symm
        refine Finset.sum_eq_zero fun a' _ => ?_
        rw [Finset.sum_eq_zero]; · simp
        intro a _
        simp [hc]
      · rw [if_neg hc]
        rw [Finset.sum_eq_single (⟨b, s.core_active b.2⟩ : A)]
        · rw [Finset.sum_eq_single (⟨i, hi⟩ : A)]
          · simp [hc]; rfl
          · intro a _ ha
            have : i ≠ (a : ι) := fun h => ha (Subtype.ext h.symm)
            simp [this]
          · simp
        · intro a' _ ha'
          have : ¬ ((a' : ι) = (b : ι)) := fun h => ha' (Subtype.ext h)
          simp [this]
        · simp
    · rw [dif_neg hi]
      symm
      refine Finset.sum_eq_zero fun a' _ => ?_
      rw [Finset.sum_eq_zero]; · simp
      intro a _
      have : i ≠ (a : ι) := fun h => hi (h ▸ a.2)
      simp [this]
  have hP : ‖P‖ ≤ 1 := by
    apply norm_le_one_of_conjTranspose_mul_self
    have : Pᴴ * P = Matrix.diagonal (fun a : A => if (a : ι) ∉ core then 1 else 0) := by
      ext a a'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, P, Matrix.of_apply, Matrix.diagonal_apply]
      by_cases haa : a = a'
      · subst haa
        rw [if_pos rfl, Finset.sum_eq_single (a : ι)]
        · by_cases hc : (a : ι) ∈ core <;> simp [hc]
        · intro i _ hi; simp [hi]
        · simp
      · rw [if_neg haa]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases h1 : i = (a : ι)
        · have h2 : i ≠ (a' : ι) := fun h => haa (Subtype.ext (h1.symm.trans h))
          simp [h2]
        · simp [h1]
    rw [this]
    exact norm_diagonal_le_one _ fun a => by split_ifs <;> simp
  have hJ : ‖J‖ ≤ 1 := by
    apply norm_le_one_of_conjTranspose_mul_self
    have : Jᴴ * J = Matrix.diagonal (fun _ : B => (1 : ℂ)) := by
      ext b b'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, J, Matrix.of_apply, Matrix.diagonal_apply]
      rw [Finset.sum_eq_single (⟨b, s.core_active b.2⟩ : A)]
      · by_cases hbb : b = b'
        · subst hbb; simp
        · have : ¬ ((b : ι) = (b' : ι)) := fun h => hbb (Subtype.ext h)
          simp [this, hbb]
      · intro a _ ha
        have : ¬ ((a : ι) = (b : ι)) := fun h => ha (Subtype.ext h)
        simp [this]
      · simp
    rw [this]
    exact norm_diagonal_le_one _ fun _ => by simp
  have hS : ‖S‖ ≤ 1 := by
    apply norm_le_one_of_conjTranspose_mul_self
    rw [hSS, ← Matrix.diagonal_one]
    exact norm_diagonal_le_one _ fun _ => by simp
  rw [hfac]
  calc ‖P * S * J‖ ≤ ‖P * S‖ * ‖J‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖P‖ * ‖S‖) * ‖J‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ 1 := by
      have h1 : ‖P‖ * ‖S‖ ≤ 1 := by nlinarith [norm_nonneg P, norm_nonneg S]
      nlinarith [norm_nonneg J, norm_nonneg (P * S), mul_nonneg (norm_nonneg P) (norm_nonneg S)]

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.trialCross_norm_le_one
