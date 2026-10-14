import AndersonAC.S3.GapComparison
import AndersonAC.S3.SymbolComparison
import AndersonAC.S3.CirculantStatements
import AndersonAC.S3.Assembly

/-!
The inverse-form comparators of Proposition 3.6 (§3, lines 690–735,
`eq:initial-comparisons`), from the circulant calculus, the two-sided gap and the
symbol-level bounds. Matrices are identified entrywise, so the decidability
instances of `1` and of the matrix inverse never need to agree syntactically.
-/

noncomputable section
open scoped BigOperators

namespace AndersonAC.S3

variable {d L : ℕ} [NeZero L]

/-- The circulant identity kernel. -/
def deltaKernel (d L : ℕ) : Torus d L → ℂ := fun x => if x = 0 then 1 else 0

theorem fourier_deltaKernel (ζ : Torus d L) : fourier (deltaKernel d L) ζ = 1 := by
  unfold fourier deltaKernel character
  rw [Finset.sum_eq_single (0 : Torus d L)]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Entrywise form of matrix equality with any decidability instance on `1`. -/
theorem circulant_delta_eq_one_apply [DecidableEq (Torus d L)] (i j : Torus d L) :
    circulant (deltaKernel d L) i j = (1 : Matrix (Torus d L) (Torus d L) ℂ) i j := by
  unfold circulant deltaKernel
  by_cases h : i = j
  · subst h; simp
  · have : i - j ≠ 0 := sub_ne_zero.mpr h
    simp [h, this, Matrix.one_apply]

/-- The symbol `Fc(ζ) = t · gridAvg (conj R(k) · R(k+ζ))` of the matrix `F`. -/
def fcSymbol (E t : ℝ) (r : ℂ) (ζ : Torus d L) : ℂ :=
  t * gridAvg (fun k : Torus d L => star (gridResolvent E t r k) * gridResolvent E t r (k + ζ))

theorem fcSymbol_conj (E t : ℝ) (r : ℂ) (ζ : Torus d L) :
    star (fcSymbol E t r ζ) = fcSymbol E t r ζ := by
  unfold fcSymbol gridAvg
  rw [Complex.star_def, map_mul, map_mul, Complex.conj_ofReal, map_inv₀, Complex.conj_natCast,
    map_sum]
  congr 2
  refine Fintype.sum_equiv (Equiv.neg (Torus d L) |>.trans (Equiv.subRight ζ)) _ _ (fun k => ?_)
  simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.subRight_apply, map_mul,
    Complex.star_def, Complex.conj_conj]
  rw [show -k - ζ + ζ = -k by abel, gridResolvent_neg,
    show -k - ζ = -(k + ζ) by abel, gridResolvent_neg]
  ring

theorem fcSymbol_im (E t : ℝ) (r : ℂ) (ζ : Torus d L) : (fcSymbol E t r ζ).im = 0 := by
  have h := fcSymbol_conj E t r ζ
  have := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at this
  linarith

theorem fcSymbol_re (E t : ℝ) (r : ℂ) (ζ : Torus d L) :
    (fcSymbol E t r ζ).re = (fSymbol E t r ζ).re := by
  unfold fcSymbol fSymbol
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, gridAvg_re, gridAvg_re]
  congr 2
  funext k
  rw [← Complex.conj_re (star (gridResolvent E t r k) * gridResolvent E t r (k + ζ))]
  congr 1
  simp [Complex.star_def, mul_comm]

theorem fcSymbol_zero (hL : 4 ≤ L) {E t : ℝ} {r : ℂ} (ht : 0 < t) (hp : 0 < r.im)
    (hr : scalarMap (d := d) (L := L) E t r = r) : fcSymbol E t r (0 : Torus d L) = 1 := by
  have hn := initial_normalization (d := d) hL E t r ht hp hr
  unfold fcSymbol
  have e : (fun k : Torus d L => star (gridResolvent E t r k) * gridResolvent E t r (k + 0)) =
      fun k => ((‖gridResolvent E t r k‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    rw [add_zero, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e]
  have : gridAvg (fun k : Torus d L => ((‖gridResolvent E t r k‖ ^ 2 : ℝ) : ℂ)) =
      ((gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖ ^ 2) : ℝ) : ℂ) := by
    simp [gridAvg, gridAvgReal]
  rw [this, ← Complex.ofReal_mul, hn, Complex.ofReal_one]

theorem circulant_add (m m' : Torus d L → ℂ) :
    circulant m + circulant m' = circulant (fun x => m x + m' x) := by
  ext i j; simp [circulant]

theorem circulant_sub (m m' : Torus d L → ℂ) :
    circulant m - circulant m' = circulant (fun x => m x - m' x) := by
  ext i j; simp [circulant]

theorem kernel_fourier_sub (m m' : Torus d L → ℂ) (ζ : Torus d L) :
    fourier (fun x => m x - m' x) ζ = fourier m ζ - fourier m' ζ := by
  unfold fourier; rw [← Finset.sum_sub_distrib]; congr 1; funext x; ring

theorem kernel_fourier_add (m m' : Torus d L → ℂ) (ζ : Torus d L) :
    fourier (fun x => m x + m' x) ζ = fourier m ζ + fourier m' ζ := by
  unfold fourier; rw [← Finset.sum_add_distrib]; congr 1; funext x; ring

theorem fourier_const_mul (a : ℂ) (m : Torus d L → ℂ) (ζ : Torus d L) :
    fourier (fun x => a * m x) ζ = a * fourier m ζ := by
  unfold fourier; rw [Finset.mul_sum]; congr 1; funext x; ring

/-- Inverse on constants of a circulant whose symbol vanishes exactly at `0`. -/
theorem inverseOnConstants_circulant (hC : CirculantCalculusStatement) (hL : 4 ≤ L)
    [DecidableEq (Torus d L)] (m : Torus d L → ℂ)
    (hm0 : fourier m 0 = 0) (hmne : ∀ ζ, ζ ≠ 0 → fourier m ζ ≠ 0) :
    ∃ mX : Torus d L → ℂ, inverseOnConstants (circulant m) = circulant mX ∧
      ∀ ζ, fourier mX ζ = if ζ = 0 then 0 else (fourier m ζ)⁻¹ := by
  obtain ⟨-, -, -, hsurj, hinj, hmul, -, -, -, -, ⟨hP, hPsym⟩, -, -⟩ := hC d L hL
  set mP : Torus d L → ℂ := fun _ => ((Fintype.card (Torus d L) : ℂ))⁻¹ with hmP
  set s : Torus d L → ℂ := fun ζ => fourier m ζ + (if ζ = 0 then 1 else 0) with hs
  have hsne : ∀ ζ, s ζ ≠ 0 := by
    intro ζ
    by_cases h : ζ = 0
    · simp [hs, h, hm0]
    · simp [hs, h, hmne ζ h]
  obtain ⟨m', hm'⟩ := hsurj (fun ζ => (s ζ)⁻¹)
  obtain ⟨m'', hprod, hm''⟩ := hmul (fun x => m x + mP x) m'
  have hm''1 : m'' = deltaKernel d L := by
    apply hinj
    intro ζ
    rw [hm'', fourier_deltaKernel, hm', kernel_fourier_add, hPsym]
    convert mul_inv_cancel₀ (hsne ζ) using 2
    by_cases h : ζ = 0 <;> simp [hs, h]
  have hDP : circulant m + meanProjection (Torus d L) = circulant (fun x => m x + mP x) := by
    rw [hP, circulant_add]
  have hinv : (circulant m + meanProjection (Torus d L))⁻¹ = circulant m' := by
    apply Matrix.inv_eq_right_inv
    rw [hDP, hprod, hm''1]
    ext i j
    exact circulant_delta_eq_one_apply i j
  refine ⟨fun x => m' x - mP x, ?_, ?_⟩
  · unfold inverseOnConstants
    rw [hinv, hP, circulant_sub]
  · intro ζ
    rw [kernel_fourier_sub, hm', hPsym]
    by_cases h : ζ = 0
    · simp [hs, h, hm0]
    · simp [hs, h]

theorem angle1_zero : angle1 L (0 : ZMod L) = 0 := by
  simp [angle1]

theorem gridAngle_zero : gridAngle (0 : Torus d L) = 0 := by
  funext j; rw [gridAngle_apply]; exact angle1_zero

theorem angle1_eq_zero {x : ZMod L} (h : angle1 L x = 0) : x = 0 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hx := x.val_lt
  unfold angle1 at h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exfalso; have := Real.pi_pos; linarith
    · split_ifs at h with hc
      · have : x.val = 0 := by exact_mod_cast h
        exact (ZMod.val_eq_zero x).mp this
      · have : (x.val : ℝ) = L := by linarith
        have : x.val = L := by exact_mod_cast this
        omega
  · exact absurd h hL.ne'

theorem exists_gridAngle_ne {ζ : Torus d L} (hζ : ζ ≠ 0) : ∃ j, gridAngle ζ j ≠ 0 := by
  by_contra h
  push Not at h
  apply hζ
  funext j
  exact angle1_eq_zero (h j)

theorem laplacianSymbol_eq_sum (k : Frequency d) : laplacianSymbol k = ∑ j, hsq (k j) := by
  unfold laplacianSymbol hsq; rw [Finset.mul_sum]

theorem laplacianSymbol_bounds {L : ℕ} [NeZero L] (ζ : Torus d L) (j₀ : Fin d)
    (hmax : ∀ j, |gridAngle ζ j| ≤ |gridAngle ζ j₀|) :
    4 / Real.pi ^ 2 * |gridAngle ζ j₀| ^ 2 ≤ laplacianSymbol (gridAngle ζ) ∧
      laplacianSymbol (gridAngle ζ) ≤ d * |gridAngle ζ j₀| ^ 2 := by
  rw [laplacianSymbol_eq_sum]
  set s := |gridAngle ζ j₀|
  constructor
  · have h1 : hsq (gridAngle ζ j₀) ≤ ∑ j, hsq (gridAngle ζ j) :=
      Finset.single_le_sum (fun j _ => hsq_nonneg _) (Finset.mem_univ j₀)
    refine le_trans ?_ h1
    have hb := angle1_bounds (ζ j₀)
    rw [← gridAngle_apply] at hb
    have hs : s / 2 ≤ Real.pi / 2 := by
      have : s ≤ Real.pi := abs_le.mpr ⟨hb.1, hb.2.le⟩
      linarith
    have hsin := Real.mul_le_sin (x := s / 2) (by positivity) hs
    have e : hsq (gridAngle ζ j₀) = 4 * Real.sin (s / 2) ^ 2 := by
      unfold hsq
      rcases le_or_gt 0 (gridAngle ζ j₀) with h | h
      · simp [s, abs_of_nonneg h]
      · rw [show s = -gridAngle ζ j₀ from abs_of_neg h, neg_div, Real.sin_neg, neg_sq]
    rw [e]
    have hpi := Real.pi_pos
    have h2 : 2 / Real.pi * (s / 2) = s / Real.pi := by field_simp
    rw [h2] at hsin
    have h3 : (s / Real.pi) ^ 2 ≤ Real.sin (s / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsin 2
    have h4 : 4 / Real.pi ^ 2 * s ^ 2 = 4 * (s / Real.pi) ^ 2 := by field_simp
    linarith
  · calc ∑ j, hsq (gridAngle ζ j) ≤ ∑ _j : Fin d, s ^ 2 := by
          refine Finset.sum_le_sum fun j _ => (hsq_le_sq _).trans ?_
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hmax j) 2
      _ = d * s ^ 2 := by simp

theorem resolvent_z_ne {E t : ℝ} {r : ℂ} (ht : 0 < t) (hp : 0 < r.im) (k : Torus d L) :
    (dispersion (gridAngle k) : ℂ) ≠ (E : ℂ) + t * r := by
  intro h
  have h' := congrArg Complex.im h
  simp only [Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    zero_mul, add_zero, zero_add] at h'
  nlinarith [mul_pos ht hp]

theorem initialG_eq (hF : TorusFourierStatement) (hL : 4 ≤ L) {E t : ℝ} {r : ℂ} (ht : 0 < t)
    (hp : 0 < r.im) :
    initialG (d := d) (L := L) E t r = freeGreen ((E : ℂ) + t * r) := by
  obtain ⟨hinv, -⟩ := (hF d L hL).1 _ (resolvent_z_ne ht hp)
  unfold initialG initialMatrix
  apply Matrix.inv_eq_right_inv
  convert hinv.1 using 3

theorem initialF_eq (hF : TorusFourierStatement) (hL : 4 ≤ L) {E t : ℝ} {r : ℂ} (ht : 0 < t)
    (hp : 0 < r.im) :
    initialF (d := d) (L := L) E t r =
      circulant (fun x => ((t * ‖freeGreen (d := d) (L := L) ((E : ℂ) + t * r) x 0‖ ^ 2 : ℝ) : ℂ)) := by
  ext i j
  simp only [initialF, initialH, initialG_eq hF hL ht hp, circulant, Matrix.smul_apply,
    smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [freeGreen_sub _ i j, mul_pow, sq_abs, Real.sq_sqrt ht.le]

theorem fourier_kernelF (hC : CirculantCalculusStatement) (hL : 4 ≤ L) {E t : ℝ} {r : ℂ}
    (ht : 0 < t) (hp : 0 < r.im) (ζ : Torus d L) :
    fourier (fun x => ((t * ‖freeGreen (d := d) (L := L) ((E : ℂ) + t * r) x 0‖ ^ 2 : ℝ) : ℂ)) ζ =
      fcSymbol E t r ζ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h8⟩ := hC d L hL
  have e : (fun x => ((t * ‖freeGreen (d := d) (L := L) ((E : ℂ) + t * r) x 0‖ ^ 2 : ℝ) : ℂ)) =
      fun x => (t : ℂ) * ((‖freeGreen (d := d) (L := L) ((E : ℂ) + t * r) x 0‖ ^ 2 : ℝ) : ℂ) := by
    funext x; push_cast; ring
  rw [e, fourier_const_mul, h8 _ (resolvent_z_ne ht hp) ζ]
  unfold fcSymbol
  congr 2
  funext k
  simp only [gridResolvent, sub_add_eq_sub_sub]

theorem initialD_eq (hF : TorusFourierStatement) (hL : 4 ≤ L) {E t : ℝ} {r : ℂ} (ht : 0 < t)
    (hp : 0 < r.im) :
    initialD (d := d) (L := L) E t r = circulant (fun x => (r.im : ℂ) ^ 2 *
      (deltaKernel d L x - ((t * ‖freeGreen (d := d) (L := L) ((E : ℂ) + t * r) x 0‖ ^ 2 : ℝ) : ℂ))) := by
  unfold initialD
  rw [initialF_eq hF hL ht hp]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, circulant, deltaKernel]
  by_cases h : i = j
  · subst h; simp
  · have : i - j ≠ 0 := sub_ne_zero.mpr h
    simp [h, this, Matrix.one_apply]

theorem sum_eq_zero_of_neutral (hC : CirculantCalculusStatement) {L : ℕ} [NeZero L] (hL : 4 ≤ L)
    {y : Torus d L → ℂ} (hy : neutral y) : fourier y 0 = 0 := by
  obtain ⟨-, -, h3, -⟩ := hC d L hL
  rw [h3]; exact hy

/-- Form of a circulant whose symbol is real and given by `σ`. -/
theorem form_circulant_real (hC : CirculantCalculusStatement) {L : ℕ} [NeZero L] (hL : 4 ≤ L)
    (m : Torus d L → ℂ) (σ : Torus d L → ℝ) (hσ : ∀ ζ, fourier m ζ = (σ ζ : ℂ))
    (y : Torus d L → ℂ) :
    form (circulant m) y = gridAvgReal (fun ζ => σ ζ * ‖fourier y ζ‖ ^ 2) := by
  obtain ⟨h1, -⟩ := hC d L hL
  rw [h1]
  congr 1; funext ζ; rw [hσ, Complex.ofReal_re]

set_option maxHeartbeats 8000000 in
/-- **The inverse-form comparators** of Proposition 3.6 (`eq:initial-comparisons`), at any
fixed point in the rectangle, for every window edge `w > 0`. -/
theorem initial_comparators (hF : TorusFourierStatement) (hC : CirculantCalculusStatement)
    (hLD : LargeSymbolDecayWStatement) (hd : 3 ≤ d) {w a₀ B : ℝ} (hw : 0 < w) (ha₀ : 0 < a₀)
    (haB : a₀ ≤ B) :
    ∃ c C C₀ t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < C₀ ∧ 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, w ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          scalarMap (d := d) (L := L) E t r = r →
          connectedLaplacian (initialD (d := d) (L := L) E t r) ∧
          ∀ y : Torus d L → ℂ, neutral y →
            c * t ^ 2 * form laplacianPlus y ≤ form (initialX E t r) y ∧
            c * normSq y ≤ form (initialX E t r) y ∧
            form (initialX E t r) y ≤ C₀ * normSq y + C * t ^ 2 * form laplacianPlus y ∧
            form (initialX E t r) y ≤
              (1 + Real.rpow t kappa) * r.im ^ (-2 : ℤ) * normSq y +
                C * t * form laplacianPlus y := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hpi := Real.pi_pos
  have hB0 : 0 < B := lt_of_lt_of_le ha₀ haB
  obtain ⟨c₁, C₁, t₁, hc₁, hC₁, ht₁, hgap⟩ := gap_two_sided hLD hd hw ha₀ haB
  set M : ℝ := 80000 * (2 : ℝ) ^ (1 / 80000 : ℝ) with hM
  have hM0 : 0 < M := by positivity
  set σ₀ : ℝ := min 1 (1 / (2 * C₁ * M ^ 2 + 1)) with hσ₀
  have hσ₀0 : 0 < σ₀ := lt_min one_pos (by positivity)
  set c : ℝ := min (1 / (C₁ * B ^ 2 * Real.pi ^ 2)) (1 / (C₁ * B ^ 2)) with hc
  set C₀ : ℝ := 1 / (a₀ ^ 2 * c₁) with hC₀
  set C : ℝ := 2 * d / (a₀ ^ 2 * c₁) with hCdef
  refine ⟨c, C, C₀, min t₁ (σ₀ ^ 80000), lt_min (by positivity) (by positivity), by positivity,
    by positivity, by positivity, ?_⟩
  intro t ht ht₀ L _ hL4 hLe hLb E hE1 hE2 r hr hfix
  have htt₁ : t ≤ t₁ := ht₀.trans (min_le_left _ _)
  have hrim : 0 < r.im := rectangle_im_pos ha₀ hr
  obtain ⟨hrre, hrim1, hrim2⟩ := hr
  set p := r.im with hpdef
  -- smallness of `t` through `τ = t^{1/80000}`
  set τ : ℝ := t ^ (1 / 80000 : ℝ) with hτ
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos ht _
  have hτσ : τ ≤ σ₀ := by
    have h := Real.rpow_le_rpow ht.le (ht₀.trans (min_le_right _ _))
      (by norm_num : (0 : ℝ) ≤ 1 / 80000)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hσ₀0.le, show ((80000 : ℕ) : ℝ) * (1 / 80000) = 1
      by norm_num, Real.rpow_one] at h
  have hτ1 : τ ≤ 1 := hτσ.trans (min_le_left _ _)
  have hτpow : ∀ k : ℕ, τ ^ k = t ^ ((k : ℝ) / 80000) := by
    intro k; rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; ring
  have ht_eq : t = τ ^ 80000 := by rw [hτpow]; norm_num
  have ht1 : t ≤ 1 := by rw [ht_eq]; exact pow_le_one₀ hτ0.le hτ1
  have hκ : Real.rpow t kappa = τ ^ 4 := by
    rw [hτpow]; unfold kappa delta; norm_num
  have hκ1 : t ^ kappa ≤ 1 := Real.rpow_le_one ht.le ht1 (by unfold kappa delta; norm_num)
  have hκ0 : (0 : ℝ) ≤ kappa := by unfold kappa delta; norm_num
  -- symbols
  set u : Torus d L → ℝ := fun ζ => 1 - (fSymbol E t r ζ).re with hu
  have hfc : ∀ ζ : Torus d L, fcSymbol E t r ζ = (((fSymbol E t r ζ).re : ℝ) : ℂ) := by
    intro ζ
    apply Complex.ext
    · simp [fcSymbol_re]
    · simp [fcSymbol_im]
  have hu0 : u 0 = 0 := by
    have := fcSymbol_zero (d := d) hL4 ht hrim hfix
    rw [hfc] at this
    have h1 : (fSymbol E t r (0 : Torus d L)).re = 1 := by exact_mod_cast this
    simp [hu, h1]
  -- per-frequency data
  have hfreq : ∀ ζ : Torus d L, ζ ≠ 0 → ∃ s ℓ : ℝ, 0 < s ∧ ℓ = laplacianSymbol (gridAngle ζ) ∧
      4 / Real.pi ^ 2 * s ^ 2 ≤ ℓ ∧ ℓ ≤ d * s ^ 2 ∧
      c₁ * min 1 (s ^ 2 / t ^ 2) ≤ u ζ ∧ u ζ ≤ C₁ * min 1 (s ^ 2 / t ^ 2) ∧
      (t ≤ s ^ 2 → 1 - t ^ kappa / 2 ≤ u ζ) := by
    intro ζ hζ
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => |gridAngle ζ j|)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have hmax : ∀ j, |gridAngle ζ j| ≤ |gridAngle ζ j₀| := fun j => hj₀ j (Finset.mem_univ _)
    obtain ⟨j, hj⟩ := exists_gridAngle_ne hζ
    have hθ0 : gridAngle ζ j₀ ≠ 0 := by
      intro h0
      have := hmax j
      rw [h0, abs_zero] at this
      exact hj (abs_nonpos_iff.mp this)
    obtain ⟨hlo, hup, hdec⟩ := hgap t ht htt₁ L hL4 hLe hLb E hE1 hE2 r ⟨hrre, hrim1, hrim2⟩
      hfix ζ j₀ hθ0 hmax
    obtain ⟨hl1, hl2⟩ := laplacianSymbol_bounds ζ j₀ hmax
    set s := |gridAngle ζ j₀|
    have hs0 : 0 < s := abs_pos.mpr hθ0
    refine ⟨s, _, hs0, rfl, hl1, hl2, hlo, hup, fun hts => ?_⟩
    -- the sharp regime
    have hsq : Real.sqrt t ≤ s := by
      rw [← Real.sqrt_sq hs0.le]; exact Real.sqrt_le_sqrt hts
    have hsqt : Real.sqrt t = τ ^ 40000 := by
      rw [Real.sqrt_eq_rpow, hτpow]; norm_num
    have hlog : Real.log (2 / t) ≤ M / τ := by
      have h := Real.log_le_rpow_div (x := 2 / t) (by positivity) (ε := 1 / 80000) (by norm_num)
      rw [Real.div_rpow (by norm_num) ht.le] at h
      calc Real.log (2 / t) ≤ 2 ^ (1 / 80000 : ℝ) / t ^ (1 / 80000 : ℝ) / (1 / 80000) := h
        _ = M / τ := by rw [hM, hτ]; field_simp
    have hlog0 : 0 ≤ Real.log (2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    have hF1 : ‖fSymbol E t r ζ‖ ≤ C₁ * M ^ 2 * τ ^ 39998 := by
      refine hdec.trans ?_
      have h1 : C₁ * t * Real.log (2 / t) ^ 2 / s ≤ C₁ * t * (M / τ) ^ 2 / Real.sqrt t := by
        apply div_le_div₀ (by positivity) _ (Real.sqrt_pos.mpr ht) hsq
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2) (by positivity)
      refine h1.trans (le_of_eq ?_)
      rw [hsqt, ht_eq]
      field_simp
    have hτs : C₁ * M ^ 2 * τ ^ 39998 ≤ τ ^ 4 / 2 := by
      have h1 : τ ^ 39998 = τ ^ 4 * τ ^ 39994 := by rw [← pow_add]
      have h2 : τ ^ 39994 ≤ τ := pow_le_of_le_one hτ0.le hτ1 (by norm_num)
      have h3 : τ ≤ 1 / (2 * C₁ * M ^ 2 + 1) := hτσ.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h3
      rw [h1]
      have h4 : 0 ≤ τ ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ C₁ * M ^ 2 * τ ^ 4 by positivity)]
    have hre : (fSymbol E t r ζ).re ≤ t ^ kappa / 2 := by
      have := Complex.re_le_norm (fSymbol E t r ζ)
      have hk : t ^ kappa = τ ^ 4 := hκ
      rw [hk]; linarith
    simp only [hu]; linarith
  -- the matrices
  set mF : Torus d L → ℂ := fun x =>
    ((t * ‖freeGreen (d := d) (L := L) ((E : ℂ) + t * r) x 0‖ ^ 2 : ℝ) : ℂ) with hmF
  set mD : Torus d L → ℂ := fun x => (p : ℂ) ^ 2 * (deltaKernel d L x - mF x) with hmD
  have hDeq : initialD (d := d) (L := L) E t r = circulant mD := initialD_eq hF hL4 ht hrim
  have hmDsym : ∀ ζ, fourier mD ζ = ((p ^ 2 * u ζ : ℝ) : ℂ) := by
    intro ζ
    rw [hmD, fourier_const_mul, kernel_fourier_sub, fourier_deltaKernel, hmF,
      fourier_kernelF hC hL4 ht hrim, hfc]
    simp [hu]
  have hupos : ∀ ζ, ζ ≠ 0 → 0 < u ζ := by
    intro ζ hζ
    obtain ⟨s, ℓ, hs0, -, -, -, hlo, -⟩ := hfreq ζ hζ
    have hm : 0 < min 1 (s ^ 2 / t ^ 2) := lt_min one_pos (by positivity)
    exact lt_of_lt_of_le (mul_pos hc₁ hm) hlo
  have hune : ∀ ζ, 0 ≤ u ζ := by
    intro ζ; by_cases h : ζ = 0
    · rw [h, hu0]
    · exact (hupos ζ h).le
  have hp0 : 0 < p := hrim
  obtain ⟨mX, hX, hXsym⟩ := inverseOnConstants_circulant hC hL4 mD
    (by rw [hmDsym, hu0]; simp)
    (fun ζ hζ => by rw [hmDsym]; exact_mod_cast (mul_pos (pow_pos hp0 2) (hupos ζ hζ)).ne')
  have hXeq : initialX (d := d) (L := L) E t r = circulant mX := by
    unfold initialX; rw [hDeq]; convert hX using 2
  obtain ⟨-, h2, -, -, hinj, -, -, -, -, h5, ⟨hP, hPsym⟩, ⟨mΛ, hΛ, hΛsym⟩, -⟩ := hC d L hL4
  have hℓ0 : laplacianSymbol (gridAngle (0 : Torus d L)) = 0 := by
    rw [gridAngle_zero]; simp [laplacianSymbol]
  have hℓpos : ∀ ζ : Torus d L, ζ ≠ 0 → 0 < laplacianSymbol (gridAngle ζ) := by
    intro ζ hζ
    obtain ⟨s, ℓ, hs0, hℓ, hl1, -⟩ := hfreq ζ hζ
    rw [← hℓ]; exact lt_of_lt_of_le (by positivity) hl1
  obtain ⟨mΛX, hΛX, hΛXsym⟩ := inverseOnConstants_circulant hC hL4 mΛ
    (by rw [hΛsym, hℓ0]; simp)
    (fun ζ hζ => by rw [hΛsym]; exact_mod_cast (hℓpos ζ hζ).ne')
  have hΛPeq : laplacianPlus (d := d) (L := L) = circulant mΛX := by
    unfold laplacianPlus; rw [hΛ]; convert hΛX using 2
  -- real symbols of `X` and `Λ⁺`
  set Xs : Torus d L → ℝ := fun ζ => if ζ = 0 then 0 else (p ^ 2 * u ζ)⁻¹ with hXs
  set Ls : Torus d L → ℝ := fun ζ => if ζ = 0 then 0 else (laplacianSymbol (gridAngle ζ))⁻¹
    with hLs
  have hXsym' : ∀ ζ, fourier mX ζ = (Xs ζ : ℂ) := by
    intro ζ; rw [hXsym, hmDsym]; by_cases h : ζ = 0 <;> simp [hXs, h]
  have hLsym' : ∀ ζ, fourier mΛX ζ = (Ls ζ : ℂ) := by
    intro ζ; rw [hΛXsym, hΛsym]; by_cases h : ζ = 0 <;> simp [hLs, h]
  -- pointwise symbol bounds
  have hpt : ∀ ζ : Torus d L, ζ ≠ 0 →
      c * t ^ 2 * Ls ζ ≤ Xs ζ ∧ c ≤ Xs ζ ∧ Xs ζ ≤ C₀ + C * t ^ 2 * Ls ζ ∧
      Xs ζ ≤ (1 + t ^ kappa) * (p ^ 2)⁻¹ + C * t * Ls ζ := by
    intro ζ hζ
    obtain ⟨s, ℓ, hs0, hℓ, hl1, hl2, hlo, hup, hsharp⟩ := hfreq ζ hζ
    obtain ⟨b1, b2, b3, b4⟩ := symbol_bounds hd1 hc₁ hC₁ ha₀ hrim1 hrim2 ht ht1 hs0 hl1 hl2
      hlo hup hκ0 hsharp hκ1
    simp only [hXs, hLs, if_neg hζ]
    rw [← hℓ]
    have hℓp : 0 < ℓ := lt_of_lt_of_le (by positivity) hl1
    refine ⟨le_trans ?_ b1, le_trans (min_le_right _ _) b2, b3.trans ?_, b4⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (by positivity)) (by positivity)
    · have : d / (a₀ ^ 2 * c₁) ≤ C := by
        rw [hCdef]; apply div_le_div_of_nonneg_right _ (by positivity); linarith
      have h0 : 0 ≤ t ^ 2 * ℓ⁻¹ := by positivity
      rw [hC₀]
      nlinarith [mul_le_mul_of_nonneg_right this h0]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- Hermitian
    rw [hDeq]; apply h5; intro ζ; rw [hmDsym, Complex.ofReal_im]
  · intro f
    have hform : form (initialD (d := d) (L := L) E t r) f =
        gridAvgReal (fun ζ => p ^ 2 * u ζ * ‖fourier f ζ‖ ^ 2) := by
      rw [hDeq]; exact form_circulant_real hC hL4 mD _ hmDsym f
    rw [hform]
    have hnn : ∀ ζ, 0 ≤ p ^ 2 * u ζ * ‖fourier f ζ‖ ^ 2 := fun ζ => by
      have := hune ζ; positivity
    refine ⟨gridAvgReal_nonneg hnn, ⟨fun h0 => ?_, fun ⟨c', hc'⟩ => ?_⟩⟩
    · -- zero energy forces a constant
      have hsum : ∑ ζ, p ^ 2 * u ζ * ‖fourier f ζ‖ ^ 2 = 0 := by
        unfold gridAvgReal at h0
        rcases mul_eq_zero.mp h0 with h | h
        · exfalso; have : (0 : ℝ) < (Fintype.card (Torus d L) : ℝ)⁻¹ := by positivity
          linarith
        · exact h
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun ζ _ => hnn ζ)).mp hsum
      have hf0 : ∀ ζ, ζ ≠ 0 → fourier f ζ = 0 := by
        intro ζ hζ
        have := hz ζ (Finset.mem_univ _)
        have hpos : 0 < p ^ 2 * u ζ := mul_pos (pow_pos hp0 2) (hupos ζ hζ)
        have : ‖fourier f ζ‖ ^ 2 = 0 := by
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · exact h
        exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
      refine ⟨fourier f 0 * ((Fintype.card (Torus d L) : ℂ))⁻¹, ?_⟩
      apply hinj
      intro ζ
      have e : (fun _ : Torus d L => fourier f 0 * ((Fintype.card (Torus d L) : ℂ))⁻¹) =
          fun x => fourier f 0 * (fun _ : Torus d L => ((Fintype.card (Torus d L) : ℂ))⁻¹) x :=
        rfl
      rw [e, fourier_const_mul, hPsym]
      by_cases h : ζ = 0
      · subst h; simp
      · simp [h, hf0 ζ h]
    · -- constants have zero energy
      have hfz : ∀ ζ, ζ ≠ 0 → fourier f ζ = 0 := by
        intro ζ hζ
        have e : f = fun x => (c' * (Fintype.card (Torus d L) : ℂ)) *
            (fun _ : Torus d L => ((Fintype.card (Torus d L) : ℂ))⁻¹) x := by
          rw [hc']; funext x
          have : (Fintype.card (Torus d L) : ℂ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          field_simp
        rw [e, fourier_const_mul, hPsym, if_neg hζ, mul_zero]
      unfold gridAvgReal
      rw [Finset.sum_eq_zero, mul_zero]
      intro ζ _
      by_cases h : ζ = 0
      · rw [h, hu0]; ring
      · rw [hfz ζ h]; simp
  · intro y hy
    have hy0 : fourier y 0 = 0 := sum_eq_zero_of_neutral hC hL4 hy
    have hfX : form (initialX (d := d) (L := L) E t r) y =
        gridAvgReal (fun ζ => Xs ζ * ‖fourier y ζ‖ ^ 2) := by
      rw [hXeq]; exact form_circulant_real hC hL4 mX Xs hXsym' y
    have hfL : form (laplacianPlus (d := d) (L := L)) y =
        gridAvgReal (fun ζ => Ls ζ * ‖fourier y ζ‖ ^ 2) := by
      rw [hΛPeq]; exact form_circulant_real hC hL4 mΛX Ls hLsym' y
    have hN : normSq y = gridAvgReal (fun ζ => ‖fourier y ζ‖ ^ 2) := h2 y
    rw [hfX, hfL, hN]
    have hzero : ∀ ζ : Torus d L, ζ = 0 → ‖fourier y ζ‖ ^ 2 = 0 := by
      intro ζ h; rw [h, hy0]; simp
    have hrpow : r.im ^ (-2 : ℤ) = (p ^ 2)⁻¹ := by
      rw [zpow_neg]; norm_cast
    rw [hrpow]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← gridAvgReal_mul_left]
      apply gridAvgReal_mono; intro ζ
      by_cases h : ζ = 0
      · rw [hzero ζ h]; simp
      · have := (hpt ζ h).1
        nlinarith [sq_nonneg ‖fourier y ζ‖]
    · rw [← gridAvgReal_mul_left]
      apply gridAvgReal_mono; intro ζ
      by_cases h : ζ = 0
      · rw [hzero ζ h]; simp
      · have := (hpt ζ h).2.1
        nlinarith [sq_nonneg ‖fourier y ζ‖]
    · rw [← gridAvgReal_mul_left, ← gridAvgReal_mul_left, ← gridAvgReal_add]
      apply gridAvgReal_mono; intro ζ
      by_cases h : ζ = 0
      · rw [hzero ζ h]; simp
      · have := (hpt ζ h).2.2.1
        nlinarith [sq_nonneg ‖fourier y ζ‖]
    · rw [← gridAvgReal_mul_left, ← gridAvgReal_mul_left, ← gridAvgReal_add]
      apply gridAvgReal_mono; intro ζ
      by_cases h : ζ = 0
      · rw [hzero ζ h]; simp
      · have := (hpt ζ h).2.2.2
        have hk : Real.rpow t kappa = t ^ kappa := rfl
        rw [hk]
        nlinarith [sq_nonneg ‖fourier y ζ‖]

end AndersonAC.S3
