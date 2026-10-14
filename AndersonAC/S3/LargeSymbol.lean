import AndersonAC.S3.SymbolStatements
import AndersonAC.S3.Dispersion

/-! Large-frequency absolute-product estimate (§3, `03-initialization.tex`).

The proof keeps the finite-grid symbol separate from its continuum cutoff. The
0.20/0.21 Lipschitz cutoff leaves one resolvent uniformly bounded off its
support; on its support, grid quadrature and the joint-shell layer cake apply.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal

namespace AndersonAC.S3

/-- An energy cutoff: it is one below `3/100` and vanishes above `1/25`. -/
def largeCutoff {d : ℕ} (x : Frequency d) : ℝ :=
  max (min ((1 / 25 - laplacianSymbol x) / (1 / 100)) 1) 0

private theorem largeCutoff_lipschitz {d : ℕ} :
    LipschitzWith (Real.toNNReal (200 * d)) (largeCutoff (d := d)) := by
  have hEnergy : LipschitzWith (Real.toNNReal (2 * d))
      (fun x : Frequency d => laplacianSymbol x) := by
    refine LipschitzWith.of_dist_le' ?_
    intro x y
    rw [Real.dist_eq]
    have hx : laplacianSymbol x = dispersion x + 2 * d := by
      linarith [dispersion_identity_proof x]
    have hy : laplacianSymbol y = dispersion y + 2 * d := by
      linarith [dispersion_identity_proof y]
    rw [hx, hy]
    calc
      |dispersion x + 2 * d - (dispersion y + 2 * d)| =
          |dispersion x - dispersion y| := by congr 1 <;> ring
      _ ≤ 2 * d * dist x y := abs_dispersion_sub_le x y
  have hr : LipschitzWith (Real.toNNReal (200 * d)) (fun x : Frequency d =>
      (1 / 25 - laplacianSymbol x) / (1 / 100)) := by
    refine LipschitzWith.of_dist_le' ?_
    intro x y
    rw [Real.dist_eq]
    have h := hEnergy.dist_le_mul x y
    rw [Real.dist_eq] at h
    have heq : (1 / 25 - laplacianSymbol x) / (1 / 100) -
        (1 / 25 - laplacianSymbol y) / (1 / 100) =
          100 * (laplacianSymbol y - laplacianSymbol x) := by
      field_simp
      ring
    rw [heq, abs_mul]
    have h' : |laplacianSymbol x - laplacianSymbol y| ≤
        2 * d * dist x y := by
      simpa only [Real.coe_toNNReal (2 * d) (by positivity)] using h
    have hcomm : |laplacianSymbol y - laplacianSymbol x| ≤
        2 * d * dist x y := by simpa [abs_sub_comm] using h'
    have h100 := mul_le_mul_of_nonneg_left hcomm (by norm_num : (0 : ℝ) ≤ 100)
    norm_num at h100 ⊢
    nlinarith
  exact (hr.min_const 1).max_const 0

theorem largeCutoff_bounds {d : ℕ} (x : Frequency d) :
    0 ≤ largeCutoff x ∧ largeCutoff x ≤ 1 := by
  constructor
  · exact le_max_right _ _
  · unfold largeCutoff
    exact max_le (min_le_right _ _) (by norm_num)

theorem largeCutoff_one_of_le {d : ℕ} {x : Frequency d}
    (hx : laplacianSymbol x ≤ 3 / 100) : largeCutoff x = 1 := by
  unfold largeCutoff
  have : 1 ≤ (1 / 25 - laplacianSymbol x) / (1 / 100) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 100)]
    norm_num
    linarith
  rw [min_eq_right this]
  norm_num

theorem largeCutoff_pos_implies {d : ℕ} {x : Frequency d}
    (hx : 0 < largeCutoff x) : laplacianSymbol x < 1 / 25 := by
  unfold largeCutoff at hx
  have hraw : 0 < (1 / 25 - laplacianSymbol x) / (1 / 100) := by
    by_contra h
    have hle : (1 / 25 - laplacianSymbol x) / (1 / 100) ≤ 0 := le_of_not_gt h
    have hmin : min ((1 / 25 - laplacianSymbol x) / (1 / 100)) 1 ≤ 0 :=
      (min_le_left _ _).trans hle
    rw [max_eq_right hmin] at hx
    linarith
  have hnum : 0 < 1 / 25 - laplacianSymbol x := by
    by_contra hn
    have hnle : 1 / 25 - laplacianSymbol x ≤ 0 := le_of_not_gt hn
    have hdiv : (1 / 25 - laplacianSymbol x) / (1 / 100) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnle (by norm_num)
    linarith
  linarith

private theorem largeCutoff_lt_one_implies {d : ℕ} {x : Frequency d}
    (hx : largeCutoff x < 1) : 3 / 100 < laplacianSymbol x := by
  by_contra h
  have hEnergy : laplacianSymbol x ≤ 3 / 100 := le_of_not_gt h
  have hc := largeCutoff_one_of_le hEnergy
  rw [hc] at hx
  norm_num at hx

/-- Every centered grid angle lies in the fundamental frequency cube. -/
private theorem gridAngle_abs_le_pi {L : ℕ} [NeZero L] (k : ZMod L) :
    |2 * Real.pi * (if 2 * k.val < L then (k.val : ℝ) else (k.val : ℝ) - L) / L| ≤ Real.pi := by
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (NeZero.pos L)
  have hval : (k.val : ℝ) < (L : ℝ) := by exact_mod_cast k.val_lt
  by_cases h : 2 * k.val < L
  · have h' : 2 * (k.val : ℝ) < (L : ℝ) := by exact_mod_cast h
    have hv0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
    rw [if_pos h]
    have hratio : 0 ≤ 2 * Real.pi * (k.val : ℝ) / (L : ℝ) ∧
        2 * Real.pi * (k.val : ℝ) / (L : ℝ) ≤ Real.pi := by
      constructor
      · positivity
      · rw [div_le_iff₀ hLpos]
        nlinarith [Real.pi_pos]
    exact abs_le.mpr ⟨by linarith, hratio.2⟩
  · have h' : (L : ℝ) ≤ 2 * (k.val : ℝ) := by
      have hn : L ≤ 2 * k.val := Nat.le_of_not_lt h
      exact_mod_cast hn
    rw [if_neg h]
    have hlow : -(L : ℝ) / 2 ≤ (k.val : ℝ) - (L : ℝ) := by linarith
    have hupp : (k.val : ℝ) - (L : ℝ) ≤ 0 := by linarith
    have hratio : -Real.pi ≤
        2 * Real.pi * ((k.val : ℝ) - (L : ℝ)) / (L : ℝ) ∧
        2 * Real.pi * ((k.val : ℝ) - (L : ℝ)) / (L : ℝ) ≤ 0 := by
      constructor
      · rw [le_div_iff₀ hLpos]
        nlinarith [Real.pi_pos]
      · exact (div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hupp) (by linarith))
    exact abs_le.mpr ⟨hratio.1, by linarith [Real.pi_pos, hratio.2]⟩

private theorem norm_inv_le_of_re {w : ℂ} {v : ℝ} (hv : 0 < v)
    (hw : v ≤ |w.re|) : ‖w⁻¹‖ ≤ v⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hv (hw.trans (Complex.abs_re_le_norm w))

private theorem largeResolvent_le_67 {d : ℕ} {E t : ℝ} {r : ℂ}
    (hbeta : E + 2 * d + t * r.re ≤ 3 / 200)
    (x : Frequency d) (hlap : 3 / 100 ≤ laplacianSymbol x) :
    ‖((dispersion x : ℂ) - E - t * r)⁻¹‖ ≤ 67 := by
  have hgap : 1 / 67 < laplacianSymbol x - (E + 2 * d + t * r.re) := by
    calc
      1 / 67 < 3 / 200 := by norm_num
      _ ≤ laplacianSymbol x - (E + 2 * d + t * r.re) := by linarith
  have heq : (((dispersion x : ℂ) - E - t * r).re) =
      laplacianSymbol x - (E + 2 * d + t * r.re) := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.zero_im]
    rw [dispersion_identity_proof]
    ring
  have hreal : (1 / 67 : ℝ) ≤ |(((dispersion x : ℂ) - E - t * r).re)| := by
    rw [heq, abs_of_pos (by linarith [hgap])]
    exact hgap.le
  have := norm_inv_le_of_re (w := ((dispersion x : ℂ) - E - t * r))
    (by norm_num : (0 : ℝ) < 1 / 67) hreal
  norm_num at this ⊢
  exact this

private def largeResolvent {d : ℕ} (E t : ℝ) (r : ℂ) (x : Frequency d) : ℂ :=
  ((dispersion x : ℂ) - E - t * r)⁻¹

private def largePhi {d : ℕ} (E t : ℝ) (r : ℂ) (x : Frequency d) : ℝ :=
  dispersion x - E - t * r.re

private theorem largeResolvent_eq_phi {d : ℕ} (E t : ℝ) (r : ℂ)
    (x : Frequency d) :
    largeResolvent E t r x =
      (((largePhi E t r x : ℝ) : ℂ) - (t * r.im) * Complex.I)⁻¹ := by
  unfold largeResolvent largePhi
  congr 1
  apply Complex.ext
  · simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
  · simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]

private theorem largeResolvent_le_truncated {d : ℕ} {E t a₀ : ℝ} {r : ℂ}
    (ht : 0 < t) (ha : a₀ ≤ r.im) (ha₀ : 0 < a₀) (x : Frequency d) :
    ‖largeResolvent E t r x‖ ≤
      (max |largePhi E t r x| (t * r.im))⁻¹ := by
  have hv : 0 < t * r.im := mul_pos ht (lt_of_lt_of_le ha₀ ha)
  rw [largeResolvent_eq_phi, norm_inv]
  have hnorm : max |largePhi E t r x| (t * r.im) ≤
      ‖((largePhi E t r x : ℝ) : ℂ) - (t * r.im) * Complex.I‖ := by
    apply max_le
    · have hr := Complex.abs_re_le_norm
        (((largePhi E t r x : ℝ) : ℂ) - (t * r.im) * Complex.I)
      simpa [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im] using hr
    · have hi := Complex.abs_im_le_norm
        (((largePhi E t r x : ℝ) : ℂ) - (t * r.im) * Complex.I)
      simpa [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, abs_of_pos ht,
        abs_of_pos (lt_of_lt_of_le ha₀ ha)] using hi
  exact inv_anti₀ (lt_of_lt_of_le hv (le_max_right _ _)) hnorm

private theorem real_mul_lipschitz_bound {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Kf Kg M N : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : ∀ x y, |f x - f y| ≤ Kf * dist x y)
    (hg : ∀ x y, |g x - g y| ≤ Kg * dist x y)
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ N) :
    ∀ x y, |f x * g x - f y * g y| ≤ (Kf * N + Kg * M) * dist x y := by
  intro x y
  rw [show f x * g x - f y * g y =
      (f x - f y) * g x + f y * (g x - g y) by ring]
  have h₁ : |f x - f y| * |g x| ≤ (Kf * dist x y) * N :=
    mul_le_mul (hf x y) (hgb x) (abs_nonneg _) (mul_nonneg hKf (dist_nonneg))
  have h₂ : |f y| * |g x - g y| ≤ M * (Kg * dist x y) :=
    mul_le_mul (hfb y) (hg x y) (abs_nonneg _) hM
  calc
    |(f x - f y) * g x + f y * (g x - g y)|
        ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
    _ = |f x - f y| * |g x| + |f y| * |g x - g y| := by rw [abs_mul, abs_mul]
    _ ≤ (Kf * dist x y) * N + M * (Kg * dist x y) := add_le_add h₁ h₂
    _ = (Kf * N + Kg * M) * dist x y := by ring

private theorem largeResolvent_norm_le {d : ℕ} {E t a₀ : ℝ} {r : ℂ}
    (ht : 0 < t) (ha : a₀ ≤ r.im) (ha₀ : 0 < a₀) (x : Frequency d) :
    ‖largeResolvent E t r x‖ ≤ (t * a₀)⁻¹ := by
  have hz : 0 < ((E : ℂ) + t * r).im := by
    simp
    exact mul_pos ht (lt_of_lt_of_le ha₀ ha)
  have heq : largeResolvent E t r x =
      ((dispersion x : ℂ) - ((E : ℂ) + t * r))⁻¹ := by
    unfold largeResolvent
    congr 1
    push_cast
    ring
  rw [heq]
  calc ‖((dispersion x : ℂ) - ((E : ℂ) + t * r))⁻¹‖
      ≤ (((E : ℂ) + t * r).im)⁻¹ := resolvent_norm_le dispersion hz x
    _ ≤ (t * a₀)⁻¹ := by
      apply inv_anti₀ (mul_pos ht ha₀)
      simp
      exact mul_le_mul_of_nonneg_left ha ht.le

private theorem abs_norm_sub_le_dist (u v : ℂ) :
    |‖u‖ - ‖v‖| ≤ dist u v := by
  rw [dist_eq_norm]
  exact abs_norm_sub_norm_le u v

private theorem largeResolvent_norm_lipschitz {d : ℕ} {E t a₀ : ℝ} {r : ℂ}
    (ht : 0 < t) (ha : a₀ ≤ r.im) (ha₀ : 0 < a₀) :
    LipschitzWith (Real.toNNReal (2 * d / (t * a₀) ^ 2))
      (fun x : Frequency d => ‖largeResolvent E t r x‖) := by
  have hz : 0 < ((E : ℂ) + t * r).im := by
    simp
    exact mul_pos ht (lt_of_lt_of_le ha₀ ha)
  have hres := resolvent_dist_le dispersion (2 * d) abs_dispersion_sub_le hz
  have hv : t * a₀ ≤ ((E : ℂ) + t * r).im := by
    simp
    exact mul_le_mul_of_nonneg_left ha ht.le
  have hvpos : 0 < t * a₀ := mul_pos ht ha₀
  have heq (x : Frequency d) : largeResolvent E t r x =
      ((dispersion x : ℂ) - ((E : ℂ) + t * r))⁻¹ := by
    unfold largeResolvent
    congr 1
    push_cast
    ring
  refine LipschitzWith.of_dist_le' ?_
  intro x y
  rw [Real.dist_eq]
  rw [heq x, heq y]
  calc |‖((dispersion x : ℂ) - ((E : ℂ) + t * r))⁻¹‖ -
        ‖((dispersion y : ℂ) - ((E : ℂ) + t * r))⁻¹‖|
      ≤ dist (((dispersion x : ℂ) - ((E : ℂ) + t * r))⁻¹)
          (((dispersion y : ℂ) - ((E : ℂ) + t * r))⁻¹) := abs_norm_sub_le_dist _ _
    _ ≤ (2 * d) / (((E : ℂ) + t * r).im) ^ 2 * dist x y := hres x y
    _ ≤ (2 * d) / (t * a₀) ^ 2 * dist x y := by
      have hcoef : (2 * d) / (((E : ℂ) + t * r).im) ^ 2 ≤
          (2 * d) / (t * a₀) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity : 0 ≤ (2 * d : ℝ))
        · positivity
        · nlinarith [hv]
      exact mul_le_mul_of_nonneg_right hcoef (dist_nonneg)

private theorem gridAvgReal_coe {d L : ℕ} [NeZero L] (f : Torus d L → ℝ) :
    gridAvg (fun k => (f k : ℂ)) = (gridAvgReal f : ℂ) := by
  simp [gridAvg, gridAvgReal]

private theorem gridAvgReal_le_of_gridQuadrature
    {d L : ℕ} [NeZero L]
    (C : ℝ)
    (hquadC : ∀ (L' : ℕ) [NeZero L'], 4 ≤ L' → Even L' →
      ∀ (f : Frequency d → ℂ) (K : ℝ≥0), LipschitzWith K f →
        ‖gridAvg (fun k : Torus d L' => f (gridAngle k)) -
          ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ∫ x in torusCube d, f x‖ ≤ C * K / L')
    (hL : 4 ≤ L) (hEven : Even L) (f : Frequency d → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ x y, |f x - f y| ≤ c * dist x y) :
    gridAvgReal (fun k : Torus d L => f (gridAngle k)) ≤
      ((2 * Real.pi) ^ d)⁻¹ * (∫ x in torusCube d, f x) + C * c / L := by
  have hlip : LipschitzWith (Real.toNNReal c) (fun x : Frequency d => (f x : ℂ)) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.coe_toNNReal c hc]
      have hdist : dist ((f x : ℝ) : ℂ) ((f y : ℝ) : ℂ) = |f x - f y| := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [hdist]
      exact hf x y
  have h := @hquadC L (inferInstance : NeZero L) hL hEven
    (fun x => (f x : ℂ)) (Real.toNNReal c) hlip
  have hcast : gridAvg (fun k => (f (gridAngle k) : ℂ)) =
      (gridAvgReal (fun k => f (gridAngle k)) : ℂ) :=
    gridAvgReal_coe (d := d) (L := L)
      (fun k : Torus d L => f (gridAngle k))
  have hint : ∫ x in torusCube d, (f x : ℂ) =
      ((∫ x in torusCube d, f x : ℝ) : ℂ) := integral_complex_ofReal
  rw [hcast, hint] at h
  have habs : |gridAvgReal (fun k : Torus d L => f (gridAngle k)) -
      ((2 * Real.pi) ^ d)⁻¹ * ∫ x in torusCube d, f x| ≤ C * c / L := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    rw [Real.coe_toNNReal c hc] at h
    exact h
  have hdiff := (abs_le.mp habs).2
  calc
    gridAvgReal (fun k : Torus d L => f (gridAngle k)) =
        (gridAvgReal (fun k : Torus d L => f (gridAngle k)) -
          ((2 * Real.pi) ^ d)⁻¹ * (∫ x in torusCube d, f x)) +
          ((2 * Real.pi) ^ d)⁻¹ * (∫ x in torusCube d, f x) := by ring
    _ ≤ C * c / L + ((2 * Real.pi) ^ d)⁻¹ * (∫ x in torusCube d, f x) :=
      add_le_add_left hdiff (((2 * Real.pi) ^ d)⁻¹ * ∫ x in torusCube d, f x)
    _ = ((2 * Real.pi) ^ d)⁻¹ * (∫ x in torusCube d, f x) + C * c / L := by ring

private theorem gridAngle_coordinate_bound {d L : ℕ} [NeZero L]
    (k : Torus d L) (j : Fin d) : |gridAngle k j| ≤ Real.pi := by
  let kj : ZMod L := k j
  have h := gridAngle_abs_le_pi (L := L) kj
  simpa [gridAngle, kj] using h

private theorem sin_021_gt_tenth : (1 / 10 : ℝ) < Real.sin (21 / 200) := by
  have h := Real.sin_gt_sub_cube (x := 21 / 200) (by norm_num)
  norm_num at h ⊢
  linarith

private theorem largeLaplacian_gt_of_coord {d : ℕ} (x : Frequency d)
    (j : Fin d) (hcoord : 21 / 100 ≤ |x j|)
    (hbound : |x j| ≤ Real.pi + 21 / 100) :
    1 / 25 < laplacianSymbol x := by
  have ha : 21 / 200 ≤ |x j| / 2 := by linarith
  have hb : |x j| / 2 ≤ Real.pi / 2 + 21 / 200 := by linarith
  have hs : (1 / 10 : ℝ) < Real.sin (|x j| / 2) := by
    by_cases hhalf : |x j| / 2 ≤ Real.pi / 2
    · have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hhalf ha
      exact (sin_021_gt_tenth.trans_le hmono)
    · have hu : 0 < |x j| / 2 - Real.pi / 2 := by linarith
      have hu' : |x j| / 2 - Real.pi / 2 ≤ 21 / 200 := by linarith
      have hcos := Real.one_sub_sq_div_two_le_cos
        (x := |x j| / 2 - Real.pi / 2)
      have hsin : Real.sin (|x j| / 2) =
          Real.cos (|x j| / 2 - Real.pi / 2) := by
        let u : ℝ := |x j| / 2 - Real.pi / 2
        have harg : |x j| / 2 = u + Real.pi / 2 := by dsimp [u]; ring
        calc
          Real.sin (|x j| / 2) = Real.sin (u + Real.pi / 2) := by rw [harg]
          _ = Real.cos u := Real.sin_add_pi_div_two u
          _ = Real.cos (|x j| / 2 - Real.pi / 2) := by simp [u]
      rw [hsin]
      nlinarith [sq_nonneg (Real.pi / 2 - (|x j| / 2 - Real.pi / 2))]
  have hsq : Real.sin (x j / 2) ^ 2 = Real.sin (|x j| / 2) ^ 2 := by
    by_cases hx : 0 ≤ x j
    · rw [abs_of_nonneg hx]
    · have hx' : x j < 0 := lt_of_not_ge hx
      rw [abs_of_neg hx']
      have harg : -x j / 2 = -(x j / 2) := by ring
      rw [harg, Real.sin_neg]
      ring
  unfold laplacianSymbol
  have hterm : (1 / 10 : ℝ) ^ 2 < Real.sin (x j / 2) ^ 2 := by
    rw [hsq]
    have hprod := mul_pos (sub_pos.mpr hs) (by linarith [hs] :
      0 < Real.sin (|x j| / 2) + 1 / 10)
    nlinarith
  have hsum : Real.sin (x j / 2) ^ 2 ≤
      ∑ i : Fin d, Real.sin (x i / 2) ^ 2 := by
    exact Finset.single_le_sum (f := fun i => Real.sin (x i / 2) ^ 2)
      (fun i _ => sq_nonneg (Real.sin (x i / 2))) (Finset.mem_univ j)
  nlinarith

private theorem largeCutoff_coordinate_lt {d : ℕ} {x : Frequency d}
    (hcut : 0 < largeCutoff x) (j : Fin d)
    (hbound : |x j| ≤ Real.pi + 21 / 100) : |x j| < 21 / 100 := by
  have hEnergy := largeCutoff_pos_implies hcut
  by_contra h
  have hj : 21 / 100 ≤ |x j| := le_of_not_gt h
  have hh := largeLaplacian_gt_of_coord x j hj hbound
  linarith

private theorem largeShift_energy_eq {d L : ℕ} [NeZero L]
    (hF : TorusFourierStatement) (hL : 4 ≤ L) (ζ k : Torus d L) :
    laplacianSymbol (gridAngle (ζ - k)) =
      laplacianSymbol (gridAngle k - gridAngle ζ) := by
  rcases hF d L hL with ⟨_, _, _, _, hadd, hneg⟩
  have hdisp : dispersion (gridAngle (ζ - k)) =
      dispersion (gridAngle k - gridAngle ζ) := by
    unfold dispersion
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨n, hn⟩ := hadd ζ (-k) j
    obtain ⟨m, hm⟩ := hneg k j
    have hangle : gridAngle (ζ - k) j =
        (gridAngle ζ j - gridAngle k j) + (n + m : ℤ) * (2 * Real.pi) := by
      have h1 : gridAngle (ζ - k) j =
          gridAngle ζ j + gridAngle (-k) j + 2 * Real.pi * n := by
        simpa only [sub_eq_add_neg] using hn
      rw [hm] at h1
      calc
        gridAngle (ζ - k) j =
            gridAngle ζ j + (-gridAngle k j + 2 * Real.pi * m) + 2 * Real.pi * n := h1
        _ = (gridAngle ζ j - gridAngle k j) + (n + m : ℤ) * (2 * Real.pi) := by
          push_cast
          ring
    rw [hangle]
    have hper := Real.cos_add_int_mul_two_pi
      (gridAngle ζ j - gridAngle k j) (n + m)
    have hcos : Real.cos ((gridAngle ζ j - gridAngle k j) +
          (n + m : ℤ) * (2 * Real.pi)) =
        Real.cos (gridAngle ζ j - gridAngle k j) := by
      exact hper
    rw [hcos]
    have harg : gridAngle k j - gridAngle ζ j =
        -(gridAngle ζ j - gridAngle k j) := by ring
    change Real.cos (gridAngle ζ j - gridAngle k j) =
      Real.cos (gridAngle k j - gridAngle ζ j)
    rw [harg, Real.cos_neg]
  have hleft := dispersion_identity_proof (gridAngle (ζ - k))
  have hright := dispersion_identity_proof (gridAngle k - gridAngle ζ)
  linarith

private def largeOmega {d : ℕ} (θ : Frequency d) : Set (Frequency d) :=
  {x | (∀ j, |x j| ≤ 21 / 100) ∧ (∀ j, |x j - θ j| ≤ 21 / 100)}

private theorem torusCube_coordinate_bound {d : ℕ} {x : Frequency d}
    (hx : x ∈ torusCube d) (j : Fin d) : |x j| ≤ Real.pi := by
  have hj : x j ∈ Set.Ico (-Real.pi) Real.pi := by
    have hx' := Set.mem_pi.mp hx
    exact hx' j (Set.mem_univ j)
  have h := Set.mem_Ico.mp hj
  exact abs_le.mpr ⟨h.1, h.2.le⟩

private theorem largeOmega_measurable {d : ℕ} (θ : Frequency d) :
    MeasurableSet (largeOmega θ) := by
  have h1 : ∀ j : Fin d, MeasurableSet {x : Frequency d | |x j| ≤ 21 / 100} := by
    intro j
    have hc : Continuous (fun x : Frequency d => |x j|) :=
      continuous_abs.comp (continuous_apply j)
    exact isClosed_le hc continuous_const |>.measurableSet
  have h2 : ∀ j : Fin d, MeasurableSet
      {x : Frequency d | |x j - θ j| ≤ 21 / 100} := by
    intro j
    have hc : Continuous (fun x : Frequency d => |x j - θ j|) := by
      fun_prop
    exact isClosed_le hc continuous_const |>.measurableSet
  have hA' : MeasurableSet (⋂ j : Fin d, {x : Frequency d | |x j| ≤ 21 / 100}) :=
    MeasurableSet.iInter fun j => h1 j
  have hA : MeasurableSet {x : Frequency d | ∀ j, |x j| ≤ 21 / 100} := by
    convert hA' using 1
    ext x
    simp
  have hB' : MeasurableSet (⋂ j : Fin d, {x : Frequency d | |x j - θ j| ≤ 21 / 100}) :=
    MeasurableSet.iInter fun j => h2 j
  have hB : MeasurableSet {x : Frequency d | ∀ j, |x j - θ j| ≤ 21 / 100} := by
    convert hB' using 1
    ext x
    simp
  have hEq : largeOmega θ =
      {x : Frequency d | ∀ j, |x j| ≤ 21 / 100} ∩
        {x : Frequency d | ∀ j, |x j - θ j| ≤ 21 / 100} := by
    ext x
    simp [largeOmega]
  rw [hEq]
  exact hA.inter hB

private theorem largeOmega_subset_cube {d : ℕ} (θ : Frequency d) :
    largeOmega θ ⊆ torusCube d := by
  intro x hx
  apply Set.mem_pi.mpr
  intro j hj
  have h := hx.1 j
  have hpi : 21 / 100 < Real.pi := by nlinarith [Real.pi_gt_three]
  exact ⟨by have := (abs_le.mp h).1; linarith,
    by have := (abs_le.mp h).2; linarith⟩

private theorem largeOmega_coordinate_bounds {d : ℕ} {θ x : Frequency d}
    (hx : x ∈ largeOmega θ) (j : Fin d) :
    |x j| ≤ 21 / 100 ∧ |x j - θ j| ≤ 21 / 100 :=
  ⟨hx.1 j, hx.2 j⟩

private theorem laplacianSymbol_bounds {d : ℕ} (x : Frequency d) :
    0 ≤ laplacianSymbol x ∧ laplacianSymbol x ≤ 4 * d := by
  unfold laplacianSymbol
  constructor
  · positivity
  · have hsum : ∑ j : Fin d, Real.sin (x j / 2) ^ 2 ≤ d := by
      calc
        ∑ j : Fin d, Real.sin (x j / 2) ^ 2 ≤ ∑ _j : Fin d, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ =>
            (sq_le_one_iff_abs_le_one _).2 (Real.abs_sin_le_one (x j / 2))
        _ = d := by simp
    nlinarith

private theorem torusCube_measurable {d : ℕ} :
    MeasurableSet (torusCube d) := by
  exact MeasurableSet.pi countable_univ (fun _ _ => measurableSet_Ico)

private theorem gridAvgReal_add {d L : ℕ} [NeZero L]
    (f g : Torus d L → ℝ) :
    gridAvgReal (fun k => f k + g k) = gridAvgReal f + gridAvgReal g := by
  unfold gridAvgReal
  rw [Finset.sum_add_distrib]
  ring

private theorem gridAvgReal_mul_left {d L : ℕ} [NeZero L]
    (c : ℝ) (f : Torus d L → ℝ) :
    gridAvgReal (fun k => c * f k) = c * gridAvgReal f := by
  unfold gridAvgReal
  rw [← Finset.mul_sum]
  ring

private theorem gridAvgReal_mono {d L : ℕ} [NeZero L]
    {f g : Torus d L → ℝ} (h : ∀ k, f k ≤ g k) :
    gridAvgReal f ≤ gridAvgReal g := by
  unfold gridAvgReal
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => h k) (by positivity)

set_option maxHeartbeats 0
/-- Window-uniform displacement decay for the absolute product, from the five
frozen helper contracts. -/
theorem largeSymbolDecayW_of_helpers
    (hF : TorusFourierStatement)
    (hQ : PeriodicGridQuadratureStatement)
    (hBottomInput : BottomResolventStatement)
    (hJointInput : JointShellKStatement)
    (hLayer : LayerCakeStatement) : LargeSymbolDecayWStatement := by
  classical
  intro d hd w hw a₀ B ha₀ haB
  let w' : ℝ := min w (1 / 100)
  have hw'pos : 0 < w' := lt_min hw (by norm_num)
  have hw'le : w' ≤ w := min_le_left _ _
  have hw'upper : w' ≤ 1 / 100 := min_le_right _ _
  obtain ⟨ε, Cbottom, cbottom, hε, hCbottom, hcbottom, hBottom⟩ :=
    hBottomInput d hd (w' / 2) (3 / 200) (by positivity) (by linarith) (by norm_num)
  obtain ⟨Cquad, hCquad, hquad⟩ := hQ d
  obtain ⟨Cjoint, hCjoint, hJoint⟩ := hJointInput d hd
  let S : ℝ := 4 * d + 1
  let M : ℝ := max 1 (S / a₀)
  let Mbottom : ℝ := max 1 (2 / a₀)
  let Klog : ℝ := (Real.log M / Real.log 2 + 3) / Real.log 2
  let Kbottom : ℝ := Real.log Mbottom / Real.log 2 + 1
  let Koff : ℝ := 2 * d / a₀ ^ 2
  let Kon : ℝ := 400 * d / a₀ ^ 2 + 4 * d / a₀ ^ 3
  let C : ℝ := 16 * Cjoint * Klog ^ 2 +
    Real.pi * (134 * Cbottom * Kbottom) / Real.log 2 +
    Real.pi * (134 * Cquad * Koff + Cquad * Kon) / Real.log 2 ^ 2
  let t₁ : ℝ := min 1 (w' / (2 * B))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 1 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hMbottom : 1 ≤ Mbottom := by dsimp [Mbottom]; exact le_max_left _ _
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogMbottom : 0 ≤ Real.log Mbottom := Real.log_nonneg hMbottom
  have hKlog : 0 < Klog := by dsimp [Klog]; positivity
  have hKbottom : 0 < Kbottom := by dsimp [Kbottom]; positivity
  have hKoff : 0 ≤ Koff := by dsimp [Koff]; positivity
  have hKon : 0 ≤ Kon := by dsimp [Kon]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 < B := lt_of_lt_of_le ha₀ haB
  have ht₁ : 0 < t₁ := by
    dsimp [t₁]
    apply lt_min
    · norm_num
    · positivity
  refine ⟨C, t₁, hC, ht₁, ?_⟩
  intro t ht ht₁' L _hLinst hL hEven hLbig E hElow hEhigh r hr ζ j₀ hθ
  letI : NeZero L := _hLinst
  have htLe1 : t ≤ 1 := ht₁'.trans (min_le_left _ _)
  have htLeB : t ≤ w' / (2 * B) := ht₁'.trans (min_le_right _ _)
  have htB : t * B ≤ w' / 2 := by
    calc
      t * B ≤ (w' / (2 * B)) * B := mul_le_mul_of_nonneg_right htLeB hB.le
      _ = w' / 2 := by field_simp [ne_of_gt hB]
  have htPosB : 0 < t * B := mul_pos ht hB
  have hrParts : |r.re| ≤ B ∧ a₀ ≤ r.im ∧ r.im ≤ B := by
    simpa [rectangle] using hr
  rcases hrParts with ⟨hrRe, hrImLo, hrImHi⟩
  let β : ℝ := E + 2 * d + t * r.re
  let v : ℝ := t * r.im
  have htre : |t * r.re| ≤ t * B := by
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hrRe ht.le
  have htreRange : -w' / 2 ≤ t * r.re ∧ t * r.re ≤ w' / 2 := by
    have h := abs_le.mp htre
    constructor <;> linarith
  have hβlo : w' / 2 ≤ β := by
    dsimp [β]
    linarith [htreRange.1, hw'le]
  have hβhi : β ≤ 3 / 200 := by
    dsimp [β]
    linarith [htreRange.2, hw'upper]
  have hv : 0 < v := by dsimp [v]; exact mul_pos ht (lt_of_lt_of_le ha₀ hrImLo)
  have hvlo : t * a₀ ≤ v := by dsimp [v]; exact mul_le_mul_of_nonneg_left hrImLo ht.le
  have hvhi : v ≤ 1 := by
    dsimp [v]
    nlinarith [mul_le_mul_of_nonneg_left hrImHi ht.le, htB, hw'upper]
  have hβmem : β ∈ Set.Icc (w' / 2) (3 / 200) := ⟨hβlo, hβhi⟩
  have hBottomBound := hBottom β hβmem v hv hvhi
  let θ : Frequency d := gridAngle ζ
  let δ : ℝ := |gridAngle ζ j₀|
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact abs_pos.mpr (by simpa [θ] using hθ)
  have hδle : δ ≤ Real.pi := by
    dsimp [δ]
    exact gridAngle_coordinate_bound ζ j₀
  let V : ℝ := Cjoint / δ
  have hV : 0 < V := by dsimp [V]; exact div_pos hCjoint hδpos
  let φ₁ : Frequency d → ℝ := fun x => largePhi E t r x
  let φ₂ : Frequency d → ℝ := fun x => largePhi E t r (x - θ)
  let Ω : Set (Frequency d) := largeOmega θ
  let p : Frequency d → ℝ := fun x =>
    largeCutoff x * largeCutoff (x - θ) *
      ‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖
  let g : Frequency d → ℝ := fun x =>
    (max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹
  have hphiBeta (x : Frequency d) :
      φ₁ x = dispersion x + 2 * d - β ∧
      φ₂ x = dispersion (x - θ) + 2 * d - β := by
    constructor <;> dsimp [φ₁, φ₂, largePhi, β] <;> ring
  have hThetaBound (j : Fin d) : |θ j| ≤ Real.pi := by
    dsimp [θ]
    exact gridAngle_coordinate_bound ζ j
  let Kcut : ℝ := 200 * d
  let Kres : ℝ := 2 * d / (t * a₀) ^ 2
  let Mres : ℝ := (t * a₀)⁻¹
  let KcutProd : ℝ := 400 * d
  let KresProd : ℝ := 2 * Kres * Mres
  let Kprod : ℝ := KcutProd * Mres ^ 2 + KresProd
  have hKcut : 0 ≤ Kcut := by dsimp [Kcut]; positivity
  have hKres : 0 ≤ Kres := by dsimp [Kres]; positivity
  have hMres : 0 ≤ Mres := by dsimp [Mres]; positivity
  have hKcutProd : 0 ≤ KcutProd := by dsimp [KcutProd]; positivity
  have hKresProd : 0 ≤ KresProd := by dsimp [KresProd]; positivity
  have hKprod : 0 ≤ Kprod := by dsimp [Kprod]; positivity
  have hcutLip : ∀ x y : Frequency d,
      |largeCutoff x - largeCutoff y| ≤ Kcut * dist x y := by
    intro x y
    have h := largeCutoff_lipschitz.dist_le_mul x y
    rw [Real.dist_eq] at h
    simpa [Kcut, Real.coe_toNNReal (200 * d) (by positivity)] using h
  have hcutShiftLip : ∀ x y : Frequency d,
      |largeCutoff (x - θ) - largeCutoff (y - θ)| ≤ Kcut * dist x y := by
    intro x y
    have h := hcutLip (x - θ) (y - θ)
    simpa [dist_eq_norm] using h
  have hcutAbs (x : Frequency d) : |largeCutoff x| ≤ 1 := by
    rcases largeCutoff_bounds x with ⟨hlo, hhi⟩
    rw [abs_of_nonneg hlo]
    exact hhi
  have hcutShiftAbs (x : Frequency d) : |largeCutoff (x - θ)| ≤ 1 :=
    hcutAbs (x - θ)
  have hresLip : ∀ x y : Frequency d,
      |‖largeResolvent E t r x‖ - ‖largeResolvent E t r y‖| ≤ Kres * dist x y := by
    intro x y
    have h := (largeResolvent_norm_lipschitz (E := E) ht hrImLo ha₀).dist_le_mul x y
    rw [Real.dist_eq] at h
    simpa [Kres, Real.coe_toNNReal (2 * d / (t * a₀) ^ 2) (by positivity)] using h
  have hresShiftLip : ∀ x y : Frequency d,
      |‖largeResolvent E t r (x - θ)‖ - ‖largeResolvent E t r (y - θ)‖| ≤
        Kres * dist x y := by
    intro x y
    have h := hresLip (x - θ) (y - θ)
    simpa [dist_eq_norm] using h
  have hresAbs (x : Frequency d) : ‖largeResolvent E t r x‖ ≤ Mres := by
    simpa [Mres] using largeResolvent_norm_le ht hrImLo ha₀ x
  have hresShiftAbs (x : Frequency d) : ‖largeResolvent E t r (x - θ)‖ ≤ Mres :=
    hresAbs (x - θ)
  have hcutProdLip : ∀ x y : Frequency d,
      |(largeCutoff x * largeCutoff (x - θ)) -
        (largeCutoff y * largeCutoff (y - θ))| ≤ KcutProd * dist x y := by
    intro x y
    have h := real_mul_lipschitz_bound
      (fun x => largeCutoff x) (fun x => largeCutoff (x - θ)) Kcut Kcut 1 1
      hKcut hKcut (by norm_num) (by norm_num) hcutLip hcutShiftLip hcutAbs hcutShiftAbs x y
    have hcoeff : Kcut * 1 + Kcut * 1 = KcutProd := by dsimp [Kcut, KcutProd]; ring
    rw [hcoeff] at h
    exact h
  have hcutProdAbs (x : Frequency d) :
      |largeCutoff x * largeCutoff (x - θ)| ≤ 1 := by
    rw [abs_mul]
    have h := mul_le_mul (hcutAbs x) (hcutShiftAbs x) (abs_nonneg _) (by norm_num)
    simpa using h
  have hresProdLip : ∀ x y : Frequency d,
      |(‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖) -
        (‖largeResolvent E t r y‖ * ‖largeResolvent E t r (y - θ)‖)| ≤
          KresProd * dist x y := by
    intro x y
    have h := real_mul_lipschitz_bound
      (fun x => ‖largeResolvent E t r x‖)
      (fun x => ‖largeResolvent E t r (x - θ)‖) Kres Kres Mres Mres
      hKres hKres hMres hMres hresLip hresShiftLip
      (fun x => by simpa [abs_of_nonneg (norm_nonneg _)] using hresAbs x)
      (fun x => by simpa [abs_of_nonneg (norm_nonneg _)] using hresShiftAbs x) x y
    have hcoeff : Kres * Mres + Kres * Mres = KresProd := by dsimp [KresProd]; ring
    rw [hcoeff] at h
    exact h
  have hresProdAbs (x : Frequency d) :
      |‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖| ≤ Mres ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      ‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖ ≤ Mres * Mres :=
        mul_le_mul (hresAbs x) (hresShiftAbs x) (norm_nonneg _)
          hMres
      _ = Mres ^ 2 := by ring
  have hpLip : ∀ x y : Frequency d, |p x - p y| ≤ Kprod * dist x y := by
    intro x y
    have h := real_mul_lipschitz_bound
      (fun x => largeCutoff x * largeCutoff (x - θ))
      (fun x => ‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖)
      KcutProd KresProd 1 (Mres ^ 2) hKcutProd hKresProd (by norm_num) (sq_nonneg _)
      hcutProdLip hresProdLip hcutProdAbs hresProdAbs x y
    have hpeq (x : Frequency d) : p x =
        (largeCutoff x * largeCutoff (x - θ)) *
          (‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖) := by
      dsimp [p]
      ring
    rw [hpeq x, hpeq y]
    simpa [Kprod] using h
  have hpLipWith : LipschitzWith (Real.toNNReal Kprod) p :=
    LipschitzWith.of_dist_le' (fun x y => by
      rw [Real.dist_eq]
      exact hpLip x y)
  have hpContinuous : Continuous p := hpLipWith.continuous
  have hGridRes := gridAvgReal_le_of_gridQuadrature (d := d) (L := L)
    Cquad hquad hL hEven (fun x => ‖largeResolvent E t r x‖) Kres hKres hresLip
  have hGridP := gridAvgReal_le_of_gridQuadrature (d := d) (L := L)
    Cquad hquad hL hEven p Kprod hKprod hpLip
  have hfac : ((2 * Real.pi) ^ d)⁻¹ ≤ 1 := by
    have hbase : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hpow : 1 ≤ (2 * Real.pi) ^ d := one_le_pow₀ hbase
    exact inv_le_one_of_one_le₀ hpow
  have hRbottom (x : Frequency d) :
      largeResolvent E t r x =
        (((dispersion x + 2 * d - β : ℝ) : ℂ) - v * Complex.I)⁻¹ := by
    have hphi : largePhi E t r x = dispersion x + 2 * d - β := by
      dsimp [largePhi, β]
      ring
    rw [largeResolvent_eq_phi, hphi]
    simp [v]
  have hBottomInt :
      (∫ x in torusCube d, ‖largeResolvent E t r x‖) ≤
        Cbottom * Real.log (2 / v) := by
    have heq : (fun x : Frequency d => ‖largeResolvent E t r x‖) =
        (fun x => ‖(((dispersion x + 2 * d - β : ℝ) : ℂ) - v * Complex.I)⁻¹‖) := by
      funext x
      rw [hRbottom]
    rw [heq]
    exact hBottomBound.1
  have hRnonneg : 0 ≤ ∫ x in torusCube d, ‖largeResolvent E t r x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hAvgRes : gridAvgReal (fun k : Torus d L =>
      ‖gridResolvent E t r k‖) ≤
        Cbottom * Real.log (2 / v) + Cquad * Kres / L := by
    have hGridRewrite : gridAvgReal (fun k : Torus d L =>
        ‖gridResolvent E t r k‖) =
        gridAvgReal (fun k : Torus d L => ‖largeResolvent E t r (gridAngle k)‖) := by
      rfl
    calc
      gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖)
          = gridAvgReal (fun k : Torus d L => ‖largeResolvent E t r (gridAngle k)‖) := hGridRewrite
      _ ≤ ((2 * Real.pi) ^ d)⁻¹ *
              (∫ x in torusCube d, ‖largeResolvent E t r x‖) + Cquad * Kres / L := hGridRes
      _ ≤ Cbottom * Real.log (2 / v) + Cquad * Kres / L := by
        have hfactor : ((2 * Real.pi) ^ d)⁻¹ *
            ∫ x in torusCube d, ‖largeResolvent E t r x‖ ≤
              ∫ x in torusCube d, ‖largeResolvent E t r x‖ :=
          mul_le_of_le_one_left hRnonneg hfac
        have hbase : ((2 * Real.pi) ^ d)⁻¹ *
            ∫ x in torusCube d, ‖largeResolvent E t r x‖ ≤
              Cbottom * Real.log (2 / v) := hfactor.trans hBottomInt
        calc
          ((2 * Real.pi) ^ d)⁻¹ *
              (∫ x in torusCube d, ‖largeResolvent E t r x‖) + Cquad * Kres / L
              = Cquad * Kres / L +
                ((2 * Real.pi) ^ d)⁻¹ *
                  (∫ x in torusCube d, ‖largeResolvent E t r x‖) := by ring
          _ ≤ Cquad * Kres / L + Cbottom * Real.log (2 / v) :=
            add_le_add_right hbase (Cquad * Kres / L)
          _ = Cbottom * Real.log (2 / v) + Cquad * Kres / L := by ring
  have hΩmeas : MeasurableSet Ω := by dsimp [Ω]; exact largeOmega_measurable θ
  have hΩcube : Ω ⊆ torusCube d := by dsimp [Ω]; exact largeOmega_subset_cube θ
  have hpSupport : ∀ x, x ∈ torusCube d →
      0 < largeCutoff x → 0 < largeCutoff (x - θ) → x ∈ Ω := by
    intro x hx hcx hcy
    have hxb (j : Fin d) : |x j| ≤ Real.pi := torusCube_coordinate_bound hx j
    have hxbound (j : Fin d) : |x j| ≤ Real.pi + 21 / 100 := by linarith [hxb j]
    have hxsmall (j : Fin d) : |x j| < 21 / 100 :=
      largeCutoff_coordinate_lt hcx j (hxbound j)
    have hybound (j : Fin d) : |x j - θ j| ≤ Real.pi + 21 / 100 := by
      calc
        |x j - θ j| = |x j + -θ j| := by congr 1 <;> ring
        _ ≤ |x j| + |θ j| := by simpa using abs_add_le (x j) (-θ j)
        _ ≤ Real.pi + 21 / 100 := by linarith [hxsmall j, hThetaBound j]
    have hysmall (j : Fin d) : |x j - θ j| < 21 / 100 :=
      largeCutoff_coordinate_lt hcy j (hybound j)
    change (∀ j, |x j| ≤ 21 / 100) ∧ (∀ j, |x j - θ j| ≤ 21 / 100)
    exact ⟨fun j => (hxsmall j).le, fun j => (hysmall j).le⟩
  have hPhi1Cont : Continuous φ₁ := by
    dsimp [φ₁, largePhi]
    unfold dispersion
    fun_prop
  have hPhi2Cont : Continuous φ₂ := by
    dsimp [φ₂]
    have hshift : Continuous (fun x : Frequency d => x - θ) :=
      continuous_id.sub continuous_const
    exact hPhi1Cont.comp hshift
  have hPhi1Meas : Measurable φ₁ := hPhi1Cont.measurable
  have hPhi2Meas : Measurable φ₂ := hPhi2Cont.measurable
  have hSbound : ∀ x ∈ Ω, |φ₁ x| ≤ S ∧ |φ₂ x| ≤ S := by
    intro x hx
    have hLap1 := laplacianSymbol_bounds x
    have hLap2 := laplacianSymbol_bounds (x - θ)
    have hβlo' : 0 ≤ β := by linarith [hβlo]
    have hβhi' : β ≤ 1 := by linarith [hβhi]
    rcases hphiBeta x with ⟨hφ₁, hφ₂⟩
    have hφ₁lap : φ₁ x = laplacianSymbol x - β := by
      calc
        φ₁ x = dispersion x + 2 * d - β := hφ₁
        _ = laplacianSymbol x - β := by linarith [dispersion_identity_proof x]
    have hφ₂lap : φ₂ x = laplacianSymbol (x - θ) - β := by
      calc
        φ₂ x = dispersion (x - θ) + 2 * d - β := hφ₂
        _ = laplacianSymbol (x - θ) - β :=
          by linarith [dispersion_identity_proof (x - θ)]
    constructor
    · rw [hφ₁lap, abs_le]
      constructor <;> dsimp [S] <;> linarith [hLap1.1, hLap1.2, hβlo', hβhi']
    · rw [hφ₂lap, abs_le]
      constructor <;> dsimp [S] <;> linarith [hLap2.1, hLap2.2, hβlo', hβhi']
  have hThetaNonzero : θ j₀ ≠ 0 := by simpa [θ] using hθ
  have hJointIndex : (-θ) j₀ ≠ 0 := by simpa using hThetaNonzero
  have hShell : ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ →
      volume {x | x ∈ Ω ∧ |φ₁ x| ≤ s₁ ∧ |φ₂ x| ≤ s₂} ≤
        ENNReal.ofReal (V * s₁ * s₂) := by
    intro s₁ s₂ hs₁ hs₂
    have hJ := hJoint (-θ) j₀ hJointIndex (β - 2 * d) s₁ s₂ hs₁ hs₂
    have hsubset : {x | x ∈ Ω ∧ |φ₁ x| ≤ s₁ ∧ |φ₂ x| ≤ s₂} ⊆
        {x : Frequency d | (∀ j, |x j| ≤ 21 / 100) ∧
          (∀ j, |x j + (-θ) j| ≤ 21 / 100) ∧
          |dispersion x - (β - 2 * d)| ≤ s₁ ∧
          |dispersion (x + (-θ)) - (β - 2 * d)| ≤ s₂} := by
      intro x hx
      rcases hx with ⟨hxΩ, h₁, h₂⟩
      have hxΩ' : (∀ j, |x j| ≤ 21 / 100) ∧
          (∀ j, |x j - θ j| ≤ 21 / 100) := by
        simpa [Ω, largeOmega] using hxΩ
      rcases hxΩ' with ⟨hxsmall, hysmall⟩
      have hφ₁eq : φ₁ x = dispersion x - (β - 2 * d) := by
        rw [(hphiBeta x).1]
        ring
      have hφ₂eq : φ₂ x = dispersion (x + (-θ)) - (β - 2 * d) := by
        rw [(hphiBeta x).2]
        rw [sub_eq_add_neg]
        ring
      refine ⟨hxsmall, ?_, ?_, ?_⟩
      · intro j
        simpa [sub_eq_add_neg] using hysmall j
      · simpa [hφ₁eq] using h₁
      · simpa [hφ₂eq] using h₂
    have hJvol := measure_mono (μ := volume) hsubset
    have hneg : |(-θ) j₀| = δ := by
      dsimp [δ, θ]
      simp [abs_neg]
    have hScale : Cjoint * s₁ * s₂ / |(-θ) j₀| ≤ V * s₁ * s₂ := by
      calc
        Cjoint * s₁ * s₂ / |(-θ) j₀| =
            (Cjoint / δ) * (s₁ * s₂) := by rw [hneg]; ring
        _ = V * s₁ * s₂ := by dsimp [V]; ring
        _ ≤ V * s₁ * s₂ := le_rfl
    exact hJvol.trans (hJ.trans (ENNReal.ofReal_le_ofReal hScale))
  have hvS : v ≤ S := by dsimp [S]; nlinarith [hvhi]
  have hLayerBound := hLayer (Frequency d) volume Ω φ₁ φ₂ V S v
    hΩmeas hPhi1Meas hPhi2Meas hV.le hv hvS hSbound hShell
  have hpNonneg (x : Frequency d) : 0 ≤ p x := by
    have h1 := largeCutoff_bounds x
    have h2 := largeCutoff_bounds (x - θ)
    dsimp [p]
    exact mul_nonneg (mul_nonneg (mul_nonneg h1.1 h2.1) (norm_nonneg _)) (norm_nonneg _)
  have hpLeG (x : Frequency d) (hx : x ∈ Ω) : p x ≤ g x := by
    have hp1 := largeCutoff_bounds x
    have hp2 := largeCutoff_bounds (x - θ)
    have hq1 := largeResolvent_le_truncated (E := E) ht hrImLo ha₀ x
    have hq2 := largeResolvent_le_truncated (E := E) ht hrImLo ha₀ (x - θ)
    have hq1' : ‖largeResolvent E t r x‖ ≤ (max |φ₁ x| v)⁻¹ := by
      simpa [φ₁, largePhi, v] using hq1
    have hq2' : ‖largeResolvent E t r (x - θ)‖ ≤ (max |φ₂ x| v)⁻¹ := by
      simpa [φ₂, largePhi, v] using hq2
    have hcutprod : 0 ≤ largeCutoff x * largeCutoff (x - θ) ∧
        largeCutoff x * largeCutoff (x - θ) ≤ 1 := by
      constructor
      · exact mul_nonneg hp1.1 hp2.1
      · calc
          largeCutoff x * largeCutoff (x - θ) ≤ 1 * largeCutoff (x - θ) :=
            mul_le_mul_of_nonneg_right hp1.2 hp2.1
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hp2.2 (by norm_num)
          _ = 1 := by norm_num
    have hnormprod : 0 ≤ ‖largeResolvent E t r x‖ *
        ‖largeResolvent E t r (x - θ)‖ ∧
        ‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖ ≤
          (max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹ := by
      constructor
      · positivity
      · exact mul_le_mul hq1' hq2' (norm_nonneg _) (by positivity)
    calc
      p x = (largeCutoff x * largeCutoff (x - θ)) *
          (‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖) := by
            dsimp [p]
            ring
      _ ≤ 1 * (‖largeResolvent E t r x‖ * ‖largeResolvent E t r (x - θ)‖) :=
            mul_le_mul_of_nonneg_right hcutprod.2 hnormprod.1
      _ ≤ 1 * ((max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹) :=
            mul_le_mul_of_nonneg_left hnormprod.2 (by norm_num)
      _ = g x := by simp [g]
  have hpLIntegrableEq :
      (∫ x in Ω, p x) = ENNReal.toReal (∫⁻ x in Ω, ENNReal.ofReal (p x)) := by
    exact integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall hpNonneg) hpContinuous.aestronglyMeasurable
  have hpLintegralLe : ∫⁻ x in Ω, ENNReal.ofReal (p x) ≤
      ∫⁻ x in Ω, ENNReal.ofReal (g x) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hΩmeas] with x hx
    exact ENNReal.ofReal_le_ofReal (hpLeG x hx)
  have hpIntegralLe : ∫ x in Ω, p x ≤
      16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 := by
    rw [hpLIntegrableEq]
    calc
      (∫⁻ x in Ω, ENNReal.ofReal (p x)).toReal ≤
          (ENNReal.ofReal (16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2)).toReal :=
        ENNReal.toReal_mono (ENNReal.ofReal_ne_top) (hpLintegralLe.trans hLayerBound)
      _ = 16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 :=
        ENNReal.toReal_ofReal (by positivity)
  have hpCubeEq : (∫ x in torusCube d, p x) = ∫ x in Ω, p x := by
    have hAE : p =ᵐ[volume.restrict (torusCube d)] (largeOmega θ).indicator p := by
      filter_upwards [ae_restrict_mem torusCube_measurable] with x hxCube
      by_cases hcx : 0 < largeCutoff x
      · by_cases hcy : 0 < largeCutoff (x - θ)
        · have hxΩ := hpSupport x hxCube hcx hcy
          have hxΩ' : x ∈ largeOmega θ := by simpa [Ω] using hxΩ
          change p x = (if x ∈ largeOmega θ then p x else 0)
          simp [hxΩ']
        · have hz : largeCutoff (x - θ) = 0 := by
            have hle := largeCutoff_bounds (x - θ)
            exact le_antisymm (le_of_not_gt hcy) hle.1
          change p x = (if x ∈ largeOmega θ then p x else 0)
          simp [p, hz]
      · have hz : largeCutoff x = 0 := by
          have hle := largeCutoff_bounds x
          exact le_antisymm (le_of_not_gt hcx) hle.1
        change p x = (if x ∈ largeOmega θ then p x else 0)
        simp [p, hz]
    calc
      (∫ x in torusCube d, p x) =
          ∫ x in torusCube d, (largeOmega θ).indicator p x := integral_congr_ae hAE
      _ = ∫ x in torusCube d ∩ Ω, p x := by rw [setIntegral_indicator hΩmeas]
      _ = ∫ x in Ω, p x := by rw [Set.inter_eq_right.mpr hΩcube]
  have hpCubeBound : ∫ x in torusCube d, p x ≤
      16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 := by
    rw [hpCubeEq]
    exact hpIntegralLe
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hLinv : (L : ℝ)⁻¹ ≤ t ^ 8 := by
    calc
      (L : ℝ)⁻¹ ≤ (t⁻¹ ^ 8)⁻¹ := inv_anti₀ (by positivity) hLbig
      _ = t ^ 8 := by rw [inv_pow, inv_inv]
  have hInv2 : t⁻¹ ^ 2 * (L : ℝ)⁻¹ ≤ 1 := by
    calc
      t⁻¹ ^ 2 * (L : ℝ)⁻¹ ≤ t⁻¹ ^ 2 * t ^ 8 :=
        mul_le_mul_of_nonneg_left hLinv (by positivity)
      _ = t ^ 6 := by field_simp <;> ring
      _ ≤ 1 := pow_le_one₀ ht.le htLe1
  have hInv3 : t⁻¹ ^ 3 * (L : ℝ)⁻¹ ≤ 1 := by
    calc
      t⁻¹ ^ 3 * (L : ℝ)⁻¹ ≤ t⁻¹ ^ 3 * t ^ 8 :=
        mul_le_mul_of_nonneg_left hLinv (by positivity)
      _ = t ^ 5 := by field_simp <;> ring
      _ ≤ 1 := pow_le_one₀ ht.le htLe1
  have hKresDiv : Kres / L ≤ Koff := by
    have heq : Kres / L = Koff * (t⁻¹ ^ 2 * (L : ℝ)⁻¹) := by
      dsimp [Kres, Koff]
      field_simp [ne_of_gt ht, ne_of_gt ha₀, ne_of_gt hLpos]
      <;> ring
    rw [heq]
    calc
      Koff * (t⁻¹ ^ 2 * (L : ℝ)⁻¹) ≤ Koff * 1 :=
        mul_le_mul_of_nonneg_left hInv2 hKoff
      _ = Koff := by ring
  have hKprodDiv : Kprod / L ≤ Kon := by
    have heq : Kprod / L =
        (400 * d / a₀ ^ 2) * (t⁻¹ ^ 2 * (L : ℝ)⁻¹) +
          (4 * d / a₀ ^ 3) * (t⁻¹ ^ 3 * (L : ℝ)⁻¹) := by
      dsimp [Kprod, KcutProd, KresProd, Kres, Mres]
      field_simp [ne_of_gt ht, ne_of_gt ha₀, ne_of_gt hLpos]
      <;> ring
    rw [heq]
    calc
      (400 * d / a₀ ^ 2) * (t⁻¹ ^ 2 * (L : ℝ)⁻¹) +
          (4 * d / a₀ ^ 3) * (t⁻¹ ^ 3 * (L : ℝ)⁻¹)
          ≤ 400 * d / a₀ ^ 2 + 4 * d / a₀ ^ 3 := by
            have hc₁ : 0 ≤ 400 * d / a₀ ^ 2 := by positivity
            have hc₂ : 0 ≤ 4 * d / a₀ ^ 3 := by positivity
            exact add_le_add
              (calc
                (400 * d / a₀ ^ 2) * (t⁻¹ ^ 2 * (L : ℝ)⁻¹) ≤
                    (400 * d / a₀ ^ 2) * 1 := mul_le_mul_of_nonneg_left hInv2 hc₁
                _ = 400 * d / a₀ ^ 2 := by ring)
              (calc
                (4 * d / a₀ ^ 3) * (t⁻¹ ^ 3 * (L : ℝ)⁻¹) ≤
                    (4 * d / a₀ ^ 3) * 1 := mul_le_mul_of_nonneg_left hInv3 hc₂
                _ = 4 * d / a₀ ^ 3 := by ring)
      _ = Kon := by rfl
  have hErrRes : Cquad * Kres / L ≤ Cquad * Koff := by
    calc
      Cquad * Kres / L = Cquad * (Kres / L) := by ring
      _ ≤ Cquad * Koff := mul_le_mul_of_nonneg_left hKresDiv hCquad.le
  have hErrP : Cquad * Kprod / L ≤ Cquad * Kon := by
    calc
      Cquad * Kprod / L = Cquad * (Kprod / L) := by ring
      _ ≤ Cquad * Kon := mul_le_mul_of_nonneg_left hKprodDiv hCquad.le
  have hAvgResBound : gridAvgReal (fun k : Torus d L =>
      ‖gridResolvent E t r k‖) ≤ Cbottom * Real.log (2 / v) + Cquad * Koff := by
    exact le_trans hAvgRes (by nlinarith [hErrRes])
  have hAvgPBound : gridAvgReal (fun k : Torus d L => p (gridAngle k)) ≤
      16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 + Cquad * Kon := by
    have hpIntNonneg : 0 ≤ ∫ x in torusCube d, p x :=
      integral_nonneg fun x => hpNonneg x
    have hfacP : ((2 * Real.pi) ^ d)⁻¹ * ∫ x in torusCube d, p x ≤
        ∫ x in torusCube d, p x := mul_le_of_le_one_left hpIntNonneg hfac
    calc
      gridAvgReal (fun k : Torus d L => p (gridAngle k))
          ≤ ((2 * Real.pi) ^ d)⁻¹ * (∫ x in torusCube d, p x) + Cquad * Kprod / L := hGridP
      _ ≤ (∫ x in torusCube d, p x) + Cquad * Kon :=
        add_le_add hfacP hErrP
      _ ≤ 16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 + Cquad * Kon :=
        add_le_add hpCubeBound (le_rfl : Cquad * Kon ≤ Cquad * Kon)
  have hshiftAvg : gridAvgReal (fun k : Torus d L =>
      ‖gridResolvent E t r (ζ - k)‖) =
      gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) := by
    unfold gridAvgReal
    congr 1
    exact Fintype.sum_equiv (Equiv.subLeft ζ) _ _ (fun _ => rfl)
  have hPointProduct (k : Torus d L) :
      ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖ ≤
        p (gridAngle k) + 67 *
          (‖gridResolvent E t r k‖ + ‖gridResolvent E t r (ζ - k)‖) := by
    have hShiftLap := largeShift_energy_eq hF hL ζ k
    have hShiftDisp : dispersion (gridAngle (ζ - k)) =
        dispersion (gridAngle k - θ) := by
      have h1 := dispersion_identity_proof (gridAngle (ζ - k))
      have h2 := dispersion_identity_proof (gridAngle k - θ)
      linarith [hShiftLap]
    have hfirst : largeResolvent E t r (gridAngle k) = gridResolvent E t r k := rfl
    have hsecond : largeResolvent E t r (gridAngle k - θ) =
        gridResolvent E t r (ζ - k) := by
      unfold largeResolvent gridResolvent
      rw [hShiftDisp]
    let a : ℝ := ‖gridResolvent E t r k‖
    let b : ℝ := ‖gridResolvent E t r (ζ - k)‖
    let c₁ : ℝ := largeCutoff (gridAngle k)
    let c₂ : ℝ := largeCutoff (gridAngle k - θ)
    have hc₁ := largeCutoff_bounds (gridAngle k)
    have hc₂ := largeCutoff_bounds (gridAngle k - θ)
    have hcut2eq : c₂ = largeCutoff (gridAngle (ζ - k)) := by
      dsimp [c₂, largeCutoff]
      rw [hShiftLap]
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have ha67 : c₁ < 1 → a ≤ 67 := by
      intro hcut
      have henergy := largeCutoff_lt_one_implies hcut
      have h := largeResolvent_le_67 (E := E) (t := t) (r := r)
        hβhi (gridAngle k) henergy.le
      simpa [a, largeResolvent, gridResolvent] using h
    have hb67 : c₂ < 1 → b ≤ 67 := by
      intro hcut
      have henergy := largeCutoff_lt_one_implies (by simpa [hcut2eq] using hcut)
      have h := largeResolvent_le_67 (E := E) (t := t) (r := r)
        hβhi (gridAngle (ζ - k)) henergy.le
      simpa [b, largeResolvent, gridResolvent] using h
    have hresid : (1 - c₁ * c₂) * (a * b) ≤ 67 * (a + b) := by
      have hmul : c₁ * c₂ ≤ 1 := by
        calc
          c₁ * c₂ ≤ 1 * c₂ := mul_le_mul_of_nonneg_right hc₁.2 hc₂.1
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hc₂.2 (by norm_num)
          _ = 1 := by norm_num
      have hcoef0 : 0 ≤ 1 - c₁ * c₂ := by
        linarith
      have hcoef1 : 1 - c₁ * c₂ ≤ 1 := by nlinarith [mul_nonneg hc₁.1 hc₂.1]
      by_cases hc₁lt : c₁ < 1
      · have hfirst67 := ha67 hc₁lt
        have hleft : (1 - c₁ * c₂) * (a * b) ≤ a * b := by
          calc
            (1 - c₁ * c₂) * (a * b) ≤ 1 * (a * b) :=
              mul_le_mul_of_nonneg_right hcoef1 (mul_nonneg ha hb)
            _ = a * b := by ring
        calc
          (1 - c₁ * c₂) * (a * b) ≤ a * b := hleft
          _ ≤ 67 * (a + b) := by
            have hab : a * b ≤ 67 * b :=
              mul_le_mul_of_nonneg_right hfirst67 hb
            nlinarith [hab, ha, hb]
      · have hc₁eq : c₁ = 1 := le_antisymm hc₁.2 (le_of_not_gt hc₁lt)
        by_cases hc₂lt : c₂ < 1
        · have hsecond67 := hb67 hc₂lt
          have hleft : (1 - c₁ * c₂) * (a * b) ≤ a * b := by
            calc
              (1 - c₁ * c₂) * (a * b) ≤ 1 * (a * b) :=
                mul_le_mul_of_nonneg_right hcoef1 (mul_nonneg ha hb)
              _ = a * b := by ring
          rw [hc₁eq] at hleft
          calc
            (1 - c₁ * c₂) * (a * b) ≤ a * b := by simpa [hc₁eq] using hleft
            _ ≤ 67 * (a + b) := by
              have hab : a * b ≤ 67 * a := by
                calc
                  a * b ≤ a * 67 := mul_le_mul_of_nonneg_left hsecond67 ha
                  _ = 67 * a := by ring
              nlinarith [hab, ha, hb]
        · have hc₂eq : c₂ = 1 := le_antisymm hc₂.2 (le_of_not_gt hc₂lt)
          rw [hc₁eq, hc₂eq]
          norm_num
          positivity
    have hsample : p (gridAngle k) = c₁ * c₂ * (a * b) := by
      dsimp [p, c₁, c₂, a, b]
      rw [hfirst, hsecond]
      ring
    have hdecomp : a * b = c₁ * c₂ * (a * b) + (1 - c₁ * c₂) * (a * b) := by ring
    rw [hsample]
    nlinarith [hdecomp, hresid]
  have hAvgProduct : gridAvgReal (fun k : Torus d L =>
      ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) ≤
      gridAvgReal (fun k : Torus d L => p (gridAngle k)) +
        134 * gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) := by
    calc
      gridAvgReal (fun k : Torus d L =>
          ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖)
          ≤ gridAvgReal (fun k : Torus d L => p (gridAngle k) + 67 *
              (‖gridResolvent E t r k‖ + ‖gridResolvent E t r (ζ - k)‖)) :=
            gridAvgReal_mono hPointProduct
      _ = gridAvgReal (fun k : Torus d L => p (gridAngle k)) +
            67 * (gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) +
              gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r (ζ - k)‖)) := by
          rw [gridAvgReal_add, gridAvgReal_mul_left, gridAvgReal_add]
      _ = gridAvgReal (fun k : Torus d L => p (gridAngle k)) +
            134 * gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) := by
          rw [hshiftAvg]
          ring
  let Llog : ℝ := Real.log (2 / t)
  have h2t : 2 ≤ 2 / t := by
    rw [le_div_iff₀ ht]
    nlinarith [htLe1]
  have hlog2t : Real.log 2 ≤ Llog := by
    dsimp [Llog]
    exact Real.log_le_log (by norm_num) h2t
  have hLlog : 0 < Llog := lt_of_lt_of_le hlog2 hlog2t
  let ALog : ℝ := Real.log M / Real.log 2
  let BLog : ℝ := Llog / Real.log 2
  have hALog : 0 ≤ ALog := by dsimp [ALog]; positivity
  have hBLog : 1 ≤ BLog := by
    dsimp [BLog]
    exact (le_div_iff₀ hlog2).2 (by simpa using hlog2t)
  have hlogRatio : Real.log (S / v) ≤ Real.log M + Llog := by
    have hInv : v⁻¹ ≤ (t * a₀)⁻¹ := inv_anti₀ (mul_pos ht ha₀) hvlo
    have hRatio : S / v ≤ M * (2 / t) := by
      have h1 : S / v ≤ S / (t * a₀) := by
        calc
          S / v = S * v⁻¹ := by ring
          _ ≤ S * (t * a₀)⁻¹ := mul_le_mul_of_nonneg_left hInv (by positivity)
          _ = S / (t * a₀) := by ring
      have hEq : S / (t * a₀) = (S / a₀) * (1 / t) := by
        field_simp [ne_of_gt ht, ne_of_gt ha₀]
        <;> ring
      have hInvT : 1 / t ≤ 2 / t :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) ht.le
      have hST : S / a₀ ≤ M := le_max_right _ _
      calc
        S / v ≤ S / (t * a₀) := h1
        _ = (S / a₀) * (1 / t) := hEq
        _ ≤ (S / a₀) * (2 / t) :=
          mul_le_mul_of_nonneg_left hInvT (by positivity)
        _ ≤ M * (2 / t) :=
          mul_le_mul_of_nonneg_right hST (by positivity)
    have hlog := Real.log_le_log (by positivity : 0 < S / v) hRatio
    rw [Real.log_mul (by positivity : M ≠ 0) (by positivity : 2 / t ≠ 0)] at hlog
    simpa [Llog] using hlog
  have hdivLog : Real.log (S / v) / Real.log 2 ≤ ALog + BLog := by
    have h := div_le_div_of_nonneg_right hlogRatio hlog2.le
    have hsplit : (Real.log M + Llog) / Real.log 2 = ALog + BLog := by
      dsimp [ALog, BLog]
      rw [add_div]
    exact h.trans_eq hsplit
  have hAB : ALog + BLog + 2 ≤ (ALog + 3) * BLog := by
    have hprod := mul_nonneg (by linarith : 0 ≤ ALog + 2)
      (by linarith : 0 ≤ BLog - 1)
    nlinarith
  have hKlogEq : Klog * Llog = (ALog + 3) * BLog := by
    dsimp [Klog, ALog, BLog, Llog]
    field_simp [ne_of_gt hlog2]
    <;> ring
  have hBracket : Real.log (S / v) / Real.log 2 + 2 ≤ Klog * Llog := by
    calc
      Real.log (S / v) / Real.log 2 + 2 ≤ ALog + BLog + 2 := by linarith [hdivLog]
      _ ≤ (ALog + 3) * BLog := hAB
      _ = Klog * Llog := hKlogEq.symm
  have hBracketNonneg : 0 ≤ Real.log (S / v) / Real.log 2 + 2 := by
    have harg : 1 ≤ S / v := (one_le_div₀ hv).2 hvS
    have hlog : 0 ≤ Real.log (S / v) := Real.log_nonneg harg
    positivity
  have hLogSquare :
      (Real.log (S / v) / Real.log 2 + 2) ^ 2 ≤ (Klog * Llog) ^ 2 := by
    have hRhs : 0 ≤ Klog * Llog := mul_nonneg hKlog.le hLlog.le
    have hprod := mul_nonneg (sub_nonneg.mpr hBracket)
      (add_nonneg hRhs hBracketNonneg)
    nlinarith
  have hLayerLog : 16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 ≤
      16 * V * Klog ^ 2 * Llog ^ 2 := by
    calc
      16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 ≤
          16 * V * (Klog * Llog) ^ 2 :=
        mul_le_mul_of_nonneg_left hLogSquare (by positivity)
      _ = 16 * V * Klog ^ 2 * Llog ^ 2 := by ring
  let Mbot : ℝ := max 1 (2 / a₀)
  let Kbot : ℝ := Real.log Mbot / Real.log 2 + 1
  have hMbot : 1 ≤ Mbot := by dsimp [Mbot]; exact le_max_left _ _
  have hlogMbot : 0 ≤ Real.log Mbot := Real.log_nonneg hMbot
  have hKbot : 0 < Kbot := by dsimp [Kbot]; positivity
  have hBottomLog : Real.log (2 / v) ≤ Kbot * Llog := by
    have hRatio : 2 / v ≤ Mbot * (2 / t) := by
      have hInv : v⁻¹ ≤ (t * a₀)⁻¹ := inv_anti₀ (mul_pos ht ha₀) hvlo
      have h1 : 2 / v ≤ 2 / (t * a₀) := by
        calc
          2 / v = 2 * v⁻¹ := by ring
          _ ≤ 2 * (t * a₀)⁻¹ := mul_le_mul_of_nonneg_left hInv (by norm_num)
          _ = 2 / (t * a₀) := by ring
      have hEq : 2 / (t * a₀) = (2 / a₀) * (1 / t) := by
        field_simp [ne_of_gt ht, ne_of_gt ha₀]
        <;> ring
      have hInvT : 1 / t ≤ 2 / t :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) ht.le
      calc
        2 / v ≤ 2 / (t * a₀) := h1
        _ = (2 / a₀) * (1 / t) := hEq
        _ ≤ (2 / a₀) * (2 / t) :=
          mul_le_mul_of_nonneg_left hInvT (by positivity)
        _ ≤ Mbot * (2 / t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hlog := Real.log_le_log (by positivity : 0 < 2 / v) hRatio
    rw [Real.log_mul (by positivity : Mbot ≠ 0) (by positivity : 2 / t ≠ 0)] at hlog
    have hlog2t' : Real.log (2 / v) ≤ Real.log Mbot + Llog := by simpa [Llog] using hlog
    have hA : 0 ≤ Real.log Mbot / Real.log 2 := div_nonneg hlogMbot hlog2.le
    have hmul : Real.log Mbot + Llog ≤ Kbot * Llog := by
      calc
        Real.log Mbot + Llog =
            (Real.log Mbot / Real.log 2) * Real.log 2 + Llog := by
              field_simp [ne_of_gt hlog2]
              <;> ring
        _ ≤ (Real.log Mbot / Real.log 2) * Llog + Llog :=
          add_le_add_left (mul_le_mul_of_nonneg_left hlog2t hA) Llog
        _ = Kbot * Llog := by dsimp [Kbot]; ring
    exact hlog2t'.trans hmul
  let Aoff : ℝ := 134 * Cbottom * Kbot
  let Doff : ℝ := 134 * Cquad * Koff + Cquad * Kon
  have hAoff : 0 ≤ Aoff := by dsimp [Aoff]; positivity
  have hDoff : 0 ≤ Doff := by dsimp [Doff]; positivity
  have hlogProd : Real.log 2 * Llog ≤ Llog ^ 2 := by
    nlinarith [sq_nonneg (Llog - Real.log 2)]
  have hAoffBound : Aoff * Llog ≤ Aoff / Real.log 2 * Llog ^ 2 := by
    calc
      Aoff * Llog = (Aoff / Real.log 2) * (Real.log 2 * Llog) := by
        field_simp [ne_of_gt hlog2]
        <;> ring
      _ ≤ (Aoff / Real.log 2) * Llog ^ 2 :=
        mul_le_mul_of_nonneg_left hlogProd (by positivity)
  have hDoffBound : Doff ≤ Doff / Real.log 2 ^ 2 * Llog ^ 2 := by
    have hratio : 1 ≤ Llog ^ 2 / Real.log 2 ^ 2 := by
      rw [one_le_div (by positivity : 0 < Real.log 2 ^ 2)]
      nlinarith [hlogProd]
    calc
      Doff = Doff * 1 := by ring
      _ ≤ Doff * (Llog ^ 2 / Real.log 2 ^ 2) :=
        mul_le_mul_of_nonneg_left hratio hDoff
      _ = Doff / Real.log 2 ^ 2 * Llog ^ 2 := by ring
  have hδAoff : δ * (Aoff * Llog) ≤
      Real.pi * (Aoff / Real.log 2) * Llog ^ 2 := by
    calc
      δ * (Aoff * Llog) ≤ Real.pi * (Aoff * Llog) :=
        mul_le_mul_of_nonneg_right hδle (mul_nonneg hAoff hLlog.le)
      _ ≤ Real.pi * (Aoff / Real.log 2 * Llog ^ 2) :=
        mul_le_mul_of_nonneg_left hAoffBound Real.pi_pos.le
      _ = Real.pi * (Aoff / Real.log 2) * Llog ^ 2 := by ring
  have hδDoff : δ * Doff ≤
      Real.pi * Doff / Real.log 2 ^ 2 * Llog ^ 2 := by
    calc
      δ * Doff ≤ Real.pi * Doff :=
        mul_le_mul_of_nonneg_right hδle hDoff
      _ ≤ Real.pi * (Doff / Real.log 2 ^ 2 * Llog ^ 2) :=
        mul_le_mul_of_nonneg_left hDoffBound Real.pi_pos.le
      _ = Real.pi * Doff / Real.log 2 ^ 2 * Llog ^ 2 := by ring
  have hAvgTarget : gridAvgReal (fun k : Torus d L =>
      ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) ≤
      16 * V * Klog ^ 2 * Llog ^ 2 + Aoff * Llog + Doff := by
    have hOff := mul_le_mul_of_nonneg_left hAvgResBound (by norm_num : (0 : ℝ) ≤ 134)
    calc
      gridAvgReal (fun k : Torus d L =>
          ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖)
          ≤ gridAvgReal (fun k : Torus d L => p (gridAngle k)) +
              134 * gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) := hAvgProduct
      _ ≤ (16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 + Cquad * Kon) +
              134 * (Cbottom * Real.log (2 / v) + Cquad * Koff) :=
            add_le_add hAvgPBound hOff
      _ ≤ 16 * V * Klog ^ 2 * Llog ^ 2 + Aoff * Llog + Doff := by
            dsimp [Aoff, Doff]
            nlinarith [hLayerLog, hBottomLog]
  change gridAvgReal (fun k : Torus d L =>
      ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) ≤
        C * Llog ^ 2 / δ
  rw [le_div_iff₀ hδpos]
  calc
    gridAvgReal (fun k : Torus d L =>
        ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) * δ
        ≤ (16 * V * Klog ^ 2 * Llog ^ 2 + Aoff * Llog + Doff) * δ :=
          mul_le_mul_of_nonneg_right hAvgTarget hδpos.le
    _ = 16 * Cjoint * Klog ^ 2 * Llog ^ 2 +
          δ * (Aoff * Llog) + δ * Doff := by
        dsimp [V]
        field_simp [ne_of_gt hδpos]
        <;> ring
    _ ≤ 16 * Cjoint * Klog ^ 2 * Llog ^ 2 +
          Real.pi * (Aoff / Real.log 2) * Llog ^ 2 +
          Real.pi * Doff / Real.log 2 ^ 2 * Llog ^ 2 := by
        nlinarith [hδAoff, hδDoff]
    _ = C * Llog ^ 2 := by
        dsimp [C, Aoff, Doff]
        ring

/-- The original fixed-η absolute-product estimate follows from the stronger
window-uniform displacement-decay form. -/
theorem largeSymbol_of_helpers
    (hF : TorusFourierStatement)
    (hQ : PeriodicGridQuadratureStatement)
    (hBottomInput : BottomResolventStatement)
    (hJointInput : JointShellKStatement)
    (hLayer : LayerCakeStatement) : LargeSymbolStatement :=
  largeSymbol_of_decay
    (largeSymbolDecay_of_W
      (largeSymbolDecayW_of_helpers hF hQ hBottomInput hJointInput hLayer))

end AndersonAC.S3
