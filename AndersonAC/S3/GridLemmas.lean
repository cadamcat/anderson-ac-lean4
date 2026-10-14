import AndersonAC.S3.HelperStatements
import AndersonAC.S3.HelperStatements2

/-!
Infrastructure for the WP05 grid bounds: Lipschitz bounds (sup metric on
`Frequency d`) for the dispersions and their truncated resolvents, and the
grid-average/integral comparison in the form used by the lead.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal

namespace AndersonAC.S3

variable {d : ℕ}

theorem abs_dispersion_sub_le (x y : Frequency d) :
    |dispersion x - dispersion y| ≤ 2 * d * dist x y := by
  unfold dispersion
  have h : |(-2 * ∑ j, Real.cos (x j)) - (-2 * ∑ j, Real.cos (y j))| =
      2 * |∑ j, (Real.cos (x j) - Real.cos (y j))| := by
    rw [Finset.sum_sub_distrib, show (-2 * ∑ j, Real.cos (x j)) - (-2 * ∑ j, Real.cos (y j)) =
      -2 * (∑ j, Real.cos (x j) - ∑ j, Real.cos (y j)) by ring, abs_mul]
    norm_num
  rw [h]
  have h2 : |∑ j, (Real.cos (x j) - Real.cos (y j))| ≤ ∑ _j : Fin d, dist x y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← Real.dist_eq]
    exact dist_le_pi_dist x y j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  nlinarith

theorem abs_perturbedDispersion_sub_le (a φ x y : Frequency d) :
    |perturbedDispersion a φ x - perturbedDispersion a φ y| ≤
      2 * (∑ j, |a j|) * dist x y := by
  unfold perturbedDispersion
  have h : |(-2 * ∑ j, a j * Real.cos (x j + φ j)) - (-2 * ∑ j, a j * Real.cos (y j + φ j))| =
      2 * |∑ j, a j * (Real.cos (x j + φ j) - Real.cos (y j + φ j))| := by
    have : (-2 * ∑ j, a j * Real.cos (x j + φ j)) - (-2 * ∑ j, a j * Real.cos (y j + φ j)) =
        -2 * ∑ j, a j * (Real.cos (x j + φ j) - Real.cos (y j + φ j)) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, abs_mul]
    norm_num
  rw [h]
  have h2 : |∑ j, a j * (Real.cos (x j + φ j) - Real.cos (y j + φ j))| ≤
      ∑ j, |a j| * dist x y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [show x j + φ j - (y j + φ j) = x j - y j by ring, ← Real.dist_eq]
    exact dist_le_pi_dist x y j
  rw [← Finset.sum_mul] at h2
  nlinarith

theorem norm_inv_le_of_im {w : ℂ} {v : ℝ} (hv : 0 < v) (hw : v ≤ |w.im|) : ‖w⁻¹‖ ≤ v⁻¹ := by
  have h : v ≤ ‖w‖ := hw.trans (Complex.abs_im_le_norm w)
  rw [norm_inv]
  exact inv_anti₀ hv h

theorem resolvent_im (g : ℝ) (z : ℂ) : |((g : ℂ) - z).im| = |z.im| := by
  simp

/-- Lipschitz bound for a truncated resolvent `κ ↦ (g κ - z)⁻¹`. -/
theorem resolvent_dist_le {X : Type*} [PseudoMetricSpace X] (g : X → ℝ) (Lg : ℝ)
    (hg : ∀ x y, |g x - g y| ≤ Lg * dist x y) {z : ℂ} (hz : 0 < z.im) (x y : X) :
    dist (((g x : ℂ) - z)⁻¹) (((g y : ℂ) - z)⁻¹) ≤ Lg / z.im ^ 2 * dist x y := by
  have hx : ((g x : ℂ) - z) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hy : ((g y : ℂ) - z) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  rw [dist_eq_norm, inv_sub_inv hx hy, norm_div, norm_mul]
  have h1 : ‖((g y : ℂ) - z) - ((g x : ℂ) - z)‖ = |g x - g y| := by
    rw [show ((g y : ℂ) - z) - ((g x : ℂ) - z) = ((g y - g x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hnx : z.im ≤ ‖(g x : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((g x : ℂ) - z); simp at this; linarith [le_abs_self z.im]
  have hny : z.im ≤ ‖(g y : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((g y : ℂ) - z); simp at this; linarith [le_abs_self z.im]
  rw [h1, div_le_iff₀ (by positivity)]
  have hd := hg x y
  have hLd : 0 ≤ Lg * dist x y := (abs_nonneg _).trans hd
  calc |g x - g y| ≤ Lg * dist x y := hd
    _ = Lg / z.im ^ 2 * dist x y * z.im ^ 2 := by field_simp
    _ ≤ Lg / z.im ^ 2 * dist x y * (‖(g x : ℂ) - z‖ * ‖(g y : ℂ) - z‖) := by
        apply mul_le_mul_of_nonneg_left _ (by
          have : 0 ≤ Lg / z.im ^ 2 * dist x y := by
            rw [div_mul_eq_mul_div]; positivity
          exact this)
        rw [sq]; exact mul_le_mul hnx hny hz.le (norm_nonneg _)

theorem resolvent_norm_le {X : Type*} (g : X → ℝ) {z : ℂ} (hz : 0 < z.im) (x : X) :
    ‖((g x : ℂ) - z)⁻¹‖ ≤ (z.im)⁻¹ :=
  norm_inv_le_of_im hz (by simp [abs_of_pos hz])

/-- Lipschitz bound for the squared truncated resolvent. -/
theorem resolvent_sq_dist_le {X : Type*} [PseudoMetricSpace X] (g : X → ℝ) (Lg : ℝ)
    (hg : ∀ x y, |g x - g y| ≤ Lg * dist x y) {z : ℂ} (hz : 0 < z.im) (x y : X) :
    dist (((g x : ℂ) - z)⁻¹ ^ 2) (((g y : ℂ) - z)⁻¹ ^ 2) ≤ 2 * Lg / z.im ^ 3 * dist x y := by
  set p := ((g x : ℂ) - z)⁻¹
  set q := ((g y : ℂ) - z)⁻¹
  have hp : ‖p‖ ≤ (z.im)⁻¹ := resolvent_norm_le g hz x
  have hq : ‖q‖ ≤ (z.im)⁻¹ := resolvent_norm_le g hz y
  have hpq := resolvent_dist_le g Lg hg hz x y
  rw [dist_eq_norm] at hpq ⊢
  rw [show p ^ 2 - q ^ 2 = (p - q) * (p + q) by ring, norm_mul]
  have hsum : ‖p + q‖ ≤ 2 * (z.im)⁻¹ := (norm_add_le _ _).trans (by linarith)
  have h0 : 0 ≤ Lg / z.im ^ 2 * dist x y := (norm_nonneg _).trans hpq
  calc ‖p - q‖ * ‖p + q‖ ≤ (Lg / z.im ^ 2 * dist x y) * (2 * (z.im)⁻¹) :=
        mul_le_mul hpq hsum (norm_nonneg _) h0
    _ = 2 * Lg / z.im ^ 3 * dist x y := by field_simp

/-- The quadrature helper in the form used here (real Lipschitz constant). -/
theorem grid_quadrature_apply (hQ : PeriodicGridQuadratureStatement) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L →
      ∀ (f : Frequency d → ℂ) (c : ℝ), 0 ≤ c → (∀ x y, dist (f x) (f y) ≤ c * dist x y) →
        ‖gridAvg (fun k : Torus d L => f (gridAngle k)) -
          ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ∫ k in torusCube d, f k‖ ≤ C * c / L := by
  obtain ⟨C, hC, h⟩ := hQ d
  refine ⟨C, hC, fun L _ hL hE f c hc hf => ?_⟩
  have hlip : LipschitzWith (Real.toNNReal c) f :=
    LipschitzWith.of_dist_le_mul fun x y => by rw [Real.coe_toNNReal c hc]; exact hf x y
  have := h L hL hE f (Real.toNNReal c) hlip
  rwa [Real.coe_toNNReal c hc] at this

end AndersonAC.S3
