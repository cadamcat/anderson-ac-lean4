import AndersonAC.AgentS78.PadNorm
import AndersonAC.S78.InverseComparison
import AndersonAC.S78FiniteForm.Proof

/-!
WP10 reset join (07-assembly.tex:806–928 consumed by Proposition 7.5): the S78
`diagonal_reset` acts on the active block `M_A` (type `↥A`); its `ResetOutput`
transports to the ambient endpoints `fin` (before) and `new` (after reset), giving the
`StageStep` fields `new_K` and `new_inv` and the diagonal relation `g'_ii = r'_i`.
Ward energies are finite real forms, so `finiteFormInput_proof` supplies the
`BddAbove` needed by `relative_inverse_comparison`.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Zero padding of an active-block matrix. -/
def padM (A : Finset ι) (X : Matrix A A ℂ) : Matrix ι ι ℂ :=
  fun i j => if hi : i ∈ A then if hj : j ∈ A then X ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

/-- Zero padding of an active-block vector. -/
def padV (A : Finset ι) (z : A → ℂ) : ι → ℂ := fun i => if hi : i ∈ A then z ⟨i, hi⟩ else 0

theorem padM_val (A : Finset ι) (X : Matrix A A ℂ) (a b : A) : padM A X a.val b.val = X a b := by
  simp [padM, a.property, b.property]

theorem padM_submatrix (A : Finset ι) (X : Matrix A A ℂ) :
    (padM A X).submatrix (fun a : A => a.val) (fun a : A => a.val) = X := by
  ext a b; exact padM_val A X a b

theorem padM_support (A : Finset ι) (X : Matrix A A ℂ) :
    ∀ i j, (∀ k : A, k.val ≠ i) ∨ (∀ k : A, k.val ≠ j) → padM A X i j = 0 := by
  intro i j h
  rcases h with h | h
  · have hi : i ∉ A := fun hi => h ⟨i, hi⟩ rfl
    simp [padM, hi]
  · have hj : j ∉ A := fun hj => h ⟨j, hj⟩ rfl
    by_cases hi : i ∈ A <;> simp [padM, hi, hj]

theorem norm_padM (A : Finset ι) (X : Matrix A A ℂ) : ‖padM A X‖ = ‖X‖ := by
  rw [← norm_submatrix_of_support (fun a : A => a.val) Subtype.val_injective (padM A X)
    (padM_support A X), padM_submatrix]

theorem padM_sub (A : Finset ι) (X Y : Matrix A A ℂ) : padM A (X - Y) = padM A X - padM A Y := by
  ext i j; by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [padM, hi, hj]

theorem padM_squareKernel (A : Finset ι) (s : ℂ) (X : Matrix A A ℂ) :
    squareKernel (s • padM A X) = padM A (squareKernel (s • X)) := by
  ext i j; by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [padM, squareKernel, hi, hj]

/-- Ward energy of a padded block is the block Ward energy. -/
theorem wardEnergy_padM (A : Finset ι) (p : ι → ℝ) (s : ℂ) (X : Matrix A A ℂ) (f : ι → ℝ) :
    wardEnergy A p (s • padM A X) f =
      wardEnergy Finset.univ (fun a : A => p a.val) (s • X) (fun a : A => f a.val) := by
  unfold wardEnergy
  congr 1
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [padM_val]

/-- Ward energies are finite symmetric real quadratic forms on the active set. -/
theorem wardEnergy_finiteRealForm (A : Finset ι) (p : ι → ℝ) (h : Matrix ι ι ℂ) :
    AndersonAC.SolS78.FiniteRealForm A (wardEnergy A p h) := by
  classical
  let W : A → A → ℝ := fun a b => p a.val * p b.val * ‖h a.val b.val‖ ^ 2
  let w : A → A → ℝ := fun a b => (W a b + W b a) / 2
  have hsym : ∀ a b, w a b = w b a := by intro a b; simp only [w]; ring
  refine ⟨Matrix.of fun a b => (if a = b then ∑ c, w a c else 0) - w a b, ?_, ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    by_cases hab : a = b
    · subst hab; rfl
    · rw [if_neg hab, if_neg (Ne.symm hab), hsym]
  · intro f
    set g : A → ℝ := fun a => f a.val with hg
    have hL : wardEnergy A p h f = (1 / 2) * ∑ a : A, ∑ b : A, W a b * (g a - g b) ^ 2 := by
      unfold wardEnergy
      congr 1
      rw [← Finset.sum_coe_sort A]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_coe_sort A]
    have h1 : ∑ a : A, ∑ b : A, W a b * (g a - g b) ^ 2 =
        ∑ a : A, ∑ b : A, w a b * (g a - g b) ^ 2 := by
      have hswap : ∑ a : A, ∑ b : A, W b a * (g a - g b) ^ 2 =
          ∑ a : A, ∑ b : A, W a b * (g a - g b) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
      have : ∑ a : A, ∑ b : A, w a b * (g a - g b) ^ 2 =
          (1 / 2) * (∑ a : A, ∑ b : A, W a b * (g a - g b) ^ 2) +
          (1 / 2) * (∑ a : A, ∑ b : A, W b a * (g a - g b) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [w]; ring
      rw [this, hswap]; ring
    have h2 : ∑ a : A, ∑ b : A, w a b * (g a - g b) ^ 2 =
        2 * ∑ a : A, g a * (∑ c, w a c) * g a - 2 * ∑ a : A, ∑ b : A, w a b * g a * g b := by
      have hA : ∑ a : A, ∑ b : A, w a b * g a ^ 2 = ∑ a : A, g a * (∑ c, w a c) * g a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      have hB : ∑ a : A, ∑ b : A, w a b * g b ^ 2 = ∑ a : A, g a * (∑ c, w a c) * g a := by
        rw [Finset.sum_comm, ← hA]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hsym]
      have e : ∀ a b : A, w a b * (g a - g b) ^ 2 =
          w a b * g a ^ 2 + w a b * g b ^ 2 - 2 * (w a b * g a * g b) := by intro a b; ring
      simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]
      ring
    have hR : AndersonAC.SolS78.realForm A (Matrix.of fun a b => (if a = b then ∑ c, w a c else 0) - w a b) f =
        ∑ a : A, g a * (∑ c, w a c) * g a - ∑ a : A, ∑ b : A, w a b * g a * g b := by
      unfold AndersonAC.SolS78.realForm
      simp only [Matrix.of_apply]
      have e : ∀ a b : A, f a.val * ((if a = b then ∑ c, w a c else 0) - w a b) * f b.val =
          (if a = b then g a * (∑ c, w a c) * g b else 0) - w a b * g a * g b := by
        intro a b; simp only [hg]; split_ifs <;> ring
      simp_rw [e, Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    rw [hL, h1, h2, hR]
    ring

theorem wardEnergy_hom (A : Finset ι) (p : ι → ℝ) (h : Matrix ι ι ℂ) (c : ℝ) (f : ι → ℝ) :
    wardEnergy A p h (fun i => c * f i) = c ^ 2 * wardEnergy A p h f := by
  unfold wardEnergy
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem wardEnergy_nonneg (A : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ A, 0 ≤ p i) (h : Matrix ι ι ℂ)
    (f : ι → ℝ) : 0 ≤ wardEnergy A p h f := by
  unfold wardEnergy
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_)
  have := hp i hi; have := hp j hj
  positivity

/-- **Reset join.** The S78 `ResetOutput` of the active block, transported to the
ambient endpoints before (`fin`) and after (`new`) the diagonal reset. -/
theorem reset_step (A : Finset ι) (MA : Matrix A A ℂ) (rOld : ι → ℂ) (ζ : A → ℂ) (t C' : ℝ)
    (fin new : Endpoint ι) (hfa : fin.active = A) (hna : new.active = A)
    (hfg : fin.g = padM A (resetInverse MA (fun a => rOld a.val) t))
    (hng : new.g = padM A (resetInverse MA ((fun a => rOld a.val) + ζ) t))
    (hR : ResetOutput MA (fun a => rOld a.val) ζ t C')
    (hp : ∀ i ∈ A, 0 ≤ (rOld i).im) (hC' : 0 ≤ C') (hε : C' * ‖ζ‖ < 1)
    (hker : constantKernel A (endpointEnergy fin rOld t)) :
    (∀ i ∈ new.active, new.g i i = (rOld + padV A ζ) i) ∧
    matrixNorm (squareKernel (normalizedInverse new t)) ≤
      matrixNorm (squareKernel (normalizedInverse fin t)) + C' * ‖ζ‖ ∧
    ∀ y, neutral new.active y →
      (1 + C' * ‖ζ‖)⁻¹ * inverseEnergy fin.active (endpointEnergy fin rOld t) y ≤
        inverseEnergy new.active (endpointEnergy new (rOld + padV A ζ) t) y ∧
      inverseEnergy new.active (endpointEnergy new (rOld + padV A ζ) t) y ≤
        (1 - C' * ‖ζ‖)⁻¹ * inverseEnergy fin.active (endpointEnergy fin rOld t) y := by
  obtain ⟨hdiag, -, -, -, hK, hE⟩ := hR
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hna] at hi
    rw [hng]
    have := hdiag ⟨i, hi⟩
    simp only [padM, hi, dif_pos] at this ⊢
    rw [this]
    simp [padV, hi]
  · rw [matrixNorm_eq_l2, matrixNorm_eq_l2]
    simp only [normalizedInverse, hng, hfg, padM_squareKernel]
    rw [matrixNorm_eq_l2] at hK
    set X' := squareKernel ((Real.sqrt t : ℂ) • resetInverse MA ((fun a => rOld a.val) + ζ) t)
    set X := squareKernel ((Real.sqrt t : ℂ) • resetInverse MA (fun a => rOld a.val) t)
    have h1 := norm_sub_norm_le (padM A X') (padM A X)
    rw [← padM_sub, norm_padM A (X' - X)] at h1
    linarith
  · intro y hy
    have hεnn : 0 ≤ C' * ‖ζ‖ := mul_nonneg hC' (norm_nonneg _)
    have hFin : ∀ f, endpointEnergy fin rOld t f =
        wardEnergy Finset.univ (fun a : A => (rOld a.val).im)
          ((Real.sqrt t : ℂ) • resetInverse MA (fun a => rOld a.val) t) (fun a : A => f a.val) := by
      intro f
      unfold endpointEnergy normalizedInverse
      rw [hfa, hfg, wardEnergy_padM]
    have hNew : ∀ f, endpointEnergy new (rOld + padV A ζ) t f =
        wardEnergy Finset.univ (fun a : A => (((fun a : A => rOld a.val) + ζ) a).im)
          ((Real.sqrt t : ℂ) • resetInverse MA ((fun a => rOld a.val) + ζ) t) (fun a : A => f a.val) := by
      intro f
      unfold endpointEnergy normalizedInverse
      rw [hna, hng, wardEnergy_padM]
      congr 2
      funext a
      simp [padV, a.property]
    have hcompare : ∀ f, (1 - C' * ‖ζ‖) * endpointEnergy fin rOld t f ≤
        endpointEnergy new (rOld + padV A ζ) t f ∧
        endpointEnergy new (rOld + padV A ζ) t f ≤ (1 + C' * ‖ζ‖) * endpointEnergy fin rOld t f := by
      intro f
      rw [hFin, hNew]
      exact hE (fun a : A => f a.val)
    have hhom : ∀ (c : ℝ) (f : ι → ℝ), endpointEnergy fin rOld t (fun i => c * f i) =
        c ^ 2 * endpointEnergy fin rOld t f := fun c f => wardEnergy_hom _ _ _ c f
    have hnn : ∀ f, 0 ≤ endpointEnergy fin rOld t f := by
      intro f
      unfold endpointEnergy
      rw [hfa]
      exact wardEnergy_nonneg A _ hp _ f
    have hfr : AndersonAC.SolS78.FiniteRealForm A (endpointEnergy fin rOld t) := by
      unfold endpointEnergy
      rw [hfa]
      exact wardEnergy_finiteRealForm A _ _
    have hyA : neutral A y := hna ▸ hy
    have habove := (AndersonAC.SolS78.finiteFormInput_proof ι A _ hfr hnn hker).1 y hyA
    have := AndersonAC.SolS78.relative_inverse_comparison A (endpointEnergy fin rOld t)
      (endpointEnergy new (rOld + padV A ζ) t) y (C' * ‖ζ‖) hεnn hε hhom habove hcompare
    rw [hfa, hna]
    exact this

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- A damped endpoint's inverse is the padded reset inverse of its active block, so the
`hfg` hypothesis of `stage_step_of_sections` follows from `AssemblyInput.physical`. -/
theorem g_eq_padM_resetInverse {ι : Type} [Fintype ι] [DecidableEq ι] (s : Endpoint ι)
    (r : ι → ℂ) (t : ℝ) (hD : IsDampedEndpoint s r t) :
    s.g = padM s.active (resetInverse (s.M.submatrix (fun a : s.active => a.val)
      (fun a : s.active => a.val)) (fun a => r a.val) t) := by
  obtain ⟨-, hz, hBG⟩ := hD
  dsimp only at hBG
  have hinv := Matrix.inv_eq_right_inv hBG.1
  ext i j
  by_cases hi : i ∈ s.active
  · by_cases hj : j ∈ s.active
    · simp only [padM, hi, hj, dif_pos, resetInverse]
      rw [hinv]
      rfl
    · simp [padM, hi, hj, hz i j (Or.inr hj)]
  · simp [padM, hi, hz i j (Or.inl hi)]

end AndersonAC.AgentS78
