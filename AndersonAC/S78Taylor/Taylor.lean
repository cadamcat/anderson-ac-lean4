import AndersonAC.S78Taylor.Estimates

open Matrix WithLp
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace AndersonAC.SolS78
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma perturb_damping (r z : ι → ℂ) (c : ℝ) (hr : ∀ i, c ≤ (r i).im)
    (hz : ‖z‖ ≤ c / 2) : ∀ i, c / 2 ≤ ((r + z) i).im := by
  intro i
  have hzi : |(z i).im| ≤ c / 2 := (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm z i).trans hz)
  have hi := hr i
  simp only [Pi.add_apply, Complex.add_im]
  linarith [neg_abs_le (z i).im]

lemma perturb_inverse_bound (M : Matrix ι ι ℂ) (r z : ι → ℂ) (t c : ℝ)
    (hM : M.IsHermitian) (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (hz : ‖z‖ ≤ c / 2) : ‖resetInverse M (r + z) t‖ ≤ 2 / (t * c) := by
  have h := damped_inverse_norm M (r + z) t (c / 2) hM ht (by positivity)
    (perturb_damping r z c hr hz)
  convert h using 1 <;> field_simp [ht.ne', hc.ne'] <;> ring

lemma perturb_inverse_difference_bound (M : Matrix ι ι ℂ) (r z w : ι → ℂ) (t c : ℝ)
    (hM : M.IsHermitian) (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (hz : ‖z‖ ≤ c / 2) (hw : ‖w‖ ≤ c / 2) :
    ‖resetInverse M (r + z) t - resetInverse M (r + w) t‖ ≤
      4 / (t * c ^ 2) * ‖z - w‖ := by
  have huz := damped_isUnit M (r + z) t (c / 2) hM ht (by positivity) (perturb_damping r z c hr hz)
  have huw := damped_isUnit M (r + w) t (c / 2) hM ht (by positivity) (perturb_damping r w c hr hw)
  rw [resolvent_difference M r z w t huz huw, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht]
  calc
    t * ‖resetInverse M (r + z) t * diagonal (z - w) * resetInverse M (r + w) t‖ ≤
        t * (‖resetInverse M (r + z) t‖ * ‖diagonal (z - w)‖ * ‖resetInverse M (r + w) t‖) := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ t * ((2 / (t * c)) * ‖z - w‖ * (2 / (t * c))) := by
      rw [Matrix.l2_opNorm_diagonal]
      gcongr
      · exact perturb_inverse_bound M r z t c hM ht hc hr hz
      · exact perturb_inverse_bound M r w t c hM ht hc hr hw
    _ = _ := by field_simp [ht.ne', hc.ne'] <;> ring

lemma middle_quadratic (G : Matrix ι ι ℂ) (z : ι → ℂ) (L : ℝ) (hG : ‖G‖ ≤ L) :
    ‖diagonal z * G * diagonal z‖ ≤ L * ‖z‖ ^ 2 := by
  calc
    _ ≤ ‖diagonal z‖ * ‖G‖ * ‖diagonal z‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖z‖ * L * ‖z‖ := by rw [Matrix.l2_opNorm_diagonal]; gcongr
    _ = _ := by ring

lemma middle_difference (M : Matrix ι ι ℂ) (r z w : ι → ℂ) (t c a : ℝ)
    (hM : M.IsHermitian) (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (ha : 0 ≤ a) (hac : a ≤ c / 2) (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ a) :
    ‖diagonal z * resetInverse M (r + z) t * diagonal z -
      diagonal w * resetInverse M (r + w) t * diagonal w‖ ≤
      6 / (t * c) * a * ‖z - w‖ := by
  let G := resetInverse M (r + z) t
  let H := resetInverse M (r + w) t
  have hG : ‖G‖ ≤ 2 / (t * c) := perturb_inverse_bound M r z t c hM ht hc hr (hz.trans hac)
  have hH : ‖H‖ ≤ 2 / (t * c) := perturb_inverse_bound M r w t c hM ht hc hr (hw.trans hac)
  have hdiff : ‖G - H‖ ≤ 4 / (t * c ^ 2) * ‖z - w‖ :=
    perturb_inverse_difference_bound M r z w t c hM ht hc hr (hz.trans hac) (hw.trans hac)
  have he : diagonal z * G * diagonal z - diagonal w * H * diagonal w =
      diagonal (z - w) * G * diagonal z + diagonal w * (G - H) * diagonal z +
      diagonal w * H * diagonal (z - w) := by
    have hD : diagonal (z - w) = diagonal z - diagonal w := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hD]
    noncomm_ring
  rw [he]
  have h1 : ‖diagonal (z - w) * G * diagonal z‖ ≤ ‖z - w‖ * (2 / (t * c)) * a := by
    calc
      _ ≤ ‖diagonal (z - w)‖ * ‖G‖ * ‖diagonal z‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by simp only [Matrix.l2_opNorm_diagonal]; gcongr
  have h2 : ‖diagonal w * (G - H) * diagonal z‖ ≤ a * (4 / (t * c ^ 2) * ‖z - w‖) * a := by
    calc
      _ ≤ ‖diagonal w‖ * ‖G - H‖ * ‖diagonal z‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by simp only [Matrix.l2_opNorm_diagonal]; gcongr
  have h3 : ‖diagonal w * H * diagonal (z - w)‖ ≤ a * (2 / (t * c)) * ‖z - w‖ := by
    calc
      _ ≤ ‖diagonal w‖ * ‖H‖ * ‖diagonal (z - w)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by simp only [Matrix.l2_opNorm_diagonal]; gcongr
  calc
    _ ≤ ‖diagonal (z - w) * G * diagonal z‖ + ‖diagonal w * (G - H) * diagonal z‖ +
        ‖diagonal w * H * diagonal (z - w)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖z - w‖ * (2 / (t * c)) * a + a * (4 / (t * c ^ 2) * ‖z - w‖) * a +
        a * (2 / (t * c)) * ‖z - w‖ := by gcongr
    _ ≤ _ := by
      have hsmall : 4 * a ≤ 2 * c := by linarith
      have hmul := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ a * ‖z - w‖)
      -- Clear the positive denominators before the scalar estimate.
      have heq : (‖z - w‖ * (2 / (t * c)) * a + a * (4 / (t * c ^ 2) * ‖z - w‖) * a +
          a * (2 / (t * c)) * ‖z - w‖) * (t * c ^ 2) =
          4 * c * a * ‖z - w‖ + 4 * a ^ 2 * ‖z - w‖ := by field_simp [ht.ne', hc.ne'] <;> ring
      have heq' : (6 / (t * c) * a * ‖z - w‖) * (t * c ^ 2) = 6 * c * a * ‖z - w‖ := by
        field_simp [ht.ne', hc.ne'] <;> ring
      apply le_of_mul_le_mul_right (a := t * c ^ 2) _ (by positivity)
      rw [heq, heq']
      nlinarith

/-- Uniform Taylor bound with explicit constants. -/
theorem reset_taylor_proof (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ C' a₀ : ℝ, 0 < C' ∧ 0 < a₀ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ),
      0 < t → (∀ i j, M i j = M j i ∧ (M i j).im = 0) →
      (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ (resetInverse M r t i i).im ≤ C) →
      ∃ R : (ι → ℂ) → (ι → ℂ),
      (∀ z, ‖z‖ ≤ a₀ →
        (fun i => resetInverse M (r + z) t i i) =
          (fun i => resetInverse M r t i i) +
          (squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t)).mulVec z + R z) ∧
      (∀ z, ‖z‖ ≤ a₀ → ‖R z‖ ≤ C' * ‖z‖ ^ 2) ∧
      (∀ a z w, 0 ≤ a → a ≤ a₀ → ‖z‖ ≤ a → ‖w‖ ≤ a → ‖R z - R w‖ ≤ C' * a * ‖z - w‖) := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨6 * C / c ^ 2, c / 2, by positivity, by positivity, ?_⟩
  intro ι _ _ M r t ht hM hr
  let g := resetInverse M r t
  let B : (ι → ℂ) → Matrix ι ι ℂ := fun z => diagonal z * resetInverse M (r + z) t * diagonal z
  let R : (ι → ℂ) → ι → ℂ := fun z => (t : ℂ) ^ 2 • (fun i => (g * B z * g) i i)
  have hherm := real_symmetric_hermitian M hM
  have hlow : ∀ i, c ≤ (r i).im := fun i => (hr i).1
  have hsym : g.transpose = g := damped_inverse_symmetric M r t (fun i j => (hM i j).1)
  have hrow : ∀ i, ‖toLp 2 (g i)‖ ^ 2 ≤ C / (t * c) :=
    damped_inverse_row M r t c C hM ht hc hlow (fun i => (hr i).2.2)
  have hQ : 0 ≤ C / (t * c) := by positivity
  have hscalar : ‖(t : ℂ) ^ 2‖ = t ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨R, ?_, ?_, ?_⟩
  · intro z hz
    have h0 := damped_isUnit M r t c hherm ht hc hlow
    have huz := damped_isUnit M (r + z) t (c / 2) hherm ht (by positivity)
      (perturb_damping r z c hlow hz)
    have he := congrArg (fun A : Matrix ι ι ℂ => fun i => A i i) (resolvent_taylor_matrix M r z t h0 huz)
    have hl := linear_diag g z t ht.le hsym
    change (fun i => resetInverse M (r + z) t i i) = (fun i => g i i) +
      (squareKernel ((Real.sqrt t : ℂ) • g)).mulVec z + R z
    rw [← hl]
    exact he
  · intro z hz
    have hG := perturb_inverse_bound M r z t c hherm ht hc hlow hz
    calc
      ‖R z‖ = t ^ 2 * ‖fun i => (g * B z * g) i i‖ := by
        change ‖(t : ℂ) ^ 2 • (fun i : ι => (g * B z * g) i i)‖ = _
        rw [norm_smul, hscalar]
      _ ≤ t ^ 2 * (C / (t * c) * ‖B z‖) := by
        gcongr
        exact sandwich_diag_norm g (B z) _ hQ hsym hrow
      _ ≤ t ^ 2 * (C / (t * c) * ((2 / (t * c)) * ‖z‖ ^ 2)) := by
        gcongr
        exact middle_quadratic _ z _ hG
      _ = (2 * C / c ^ 2) * ‖z‖ ^ 2 := by field_simp [ht.ne', hc.ne'] <;> ring
      _ ≤ (6 * C / c ^ 2) * ‖z‖ ^ 2 := by gcongr; linarith
  · intro a z w ha hac hz hw
    have he : R z - R w = (t : ℂ) ^ 2 • (fun i => (g * (B z - B w) * g) i i) := by
      simp only [R, ← smul_sub, mul_sub, sub_mul]
      rfl
    rw [he, norm_smul, hscalar]
    calc
      _ ≤ t ^ 2 * (C / (t * c) * ‖B z - B w‖) := by
        gcongr
        exact sandwich_diag_norm g (B z - B w) _ hQ hsym hrow
      _ ≤ t ^ 2 * (C / (t * c) * ((6 / (t * c)) * a * ‖z - w‖)) := by
        gcongr
        exact middle_difference M r z w t c a hherm ht hc hlow ha hac hz hw
      _ = (6 * C / c ^ 2) * a * ‖z - w‖ := by field_simp [ht.ne', hc.ne'] <;> ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.reset_taylor_proof
