import AndersonAC.S3.Comparators

/-!
The normalized initialization endpoint (`initialization_normalized` in the planned
`Statements.lean`, consumed by WP10): Proposition 3.6 at the startup scale
`t = startupT n₀ m u`, `L = sideLength m`, with uniqueness and continuity of the
scalar fixed point and the inverse-form comparators. Stated here with the same
elaboration environment (classical decidability) as the planned statement.
-/

noncomputable section
open scoped BigOperators
open AndersonAC.Blueprint
attribute [local instance] Classical.propDecidable

namespace AndersonAC.S3

variable {d : ℕ}

/-- The scalar map is a `1/2`-contraction on the rectangle under the derivative bound. -/
theorem scalar_contraction {L : ℕ} [NeZero L] {E t a₀ B : ℝ} (ht : 0 < t) (ha : 0 < a₀)
    (hderiv : ∀ r ∈ rectangle a₀ B,
      ‖(t : ℂ) * gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2)‖ ≤ 1 / 2)
    {x y : ℂ} (hx : x ∈ rectangle a₀ B) (hy : y ∈ rectangle a₀ B) :
    ‖scalarMap (d := d) (L := L) E t y - scalarMap (d := d) (L := L) E t x‖ ≤ 1 / 2 * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun r => (t : ℂ) * gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2))
    (fun z hz => (scalarMap_hasDerivAt ht (rectangle_im_pos ha hz)).hasDerivWithinAt)
    (fun z hz => hderiv z hz) (rectangle_convex a₀ B) hx hy

/-- Dependence of the scalar map on the energy. -/
theorem scalarMap_energy_lip {L : ℕ} [NeZero L] {E E' t a₀ : ℝ} (ht : 0 < t) (ha : 0 < a₀)
    {ρ : ℂ} (hρ : a₀ ≤ ρ.im) :
    ‖scalarMap (d := d) (L := L) E t ρ - scalarMap (d := d) (L := L) E' t ρ‖ ≤
      |E - E'| / (t * a₀) ^ 2 := by
  have hv : 0 < t * ρ.im := mul_pos ht (lt_of_lt_of_le ha hρ)
  have hva : t * a₀ ≤ t * ρ.im := mul_le_mul_of_nonneg_left hρ ht.le
  unfold scalarMap
  have e : gridAvg (gridResolvent (d := d) (L := L) E t ρ) -
      gridAvg (gridResolvent (d := d) (L := L) E' t ρ) =
      gridAvg (fun k : Torus d L => gridResolvent E t ρ k - gridResolvent E' t ρ k) := by
    unfold gridAvg; rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [e]
  refine (norm_gridAvg_le _).trans ?_
  have hpt : ∀ k : Torus d L, ‖gridResolvent E t ρ k - gridResolvent E' t ρ k‖ ≤
      |E - E'| / (t * a₀) ^ 2 := by
    intro k
    have hw : ∀ e : ℝ, t * a₀ ≤ ‖(dispersion (gridAngle k) : ℂ) - e - t * ρ‖ := by
      intro e
      have h := Complex.abs_im_le_norm ((dispersion (gridAngle k) : ℂ) - e - t * ρ)
      have him : ((dispersion (gridAngle k) : ℂ) - e - t * ρ).im = -(t * ρ.im) := by simp
      rw [him, abs_neg, abs_of_pos hv] at h
      linarith
    have hta : 0 < t * a₀ := mul_pos ht ha
    have hne : ∀ e : ℝ, (dispersion (gridAngle k) : ℂ) - e - t * ρ ≠ 0 := fun e h0 => by
      have := hw e; rw [h0, norm_zero] at this; linarith
    unfold gridResolvent
    rw [inv_sub_inv (hne E) (hne E'), norm_div, norm_mul]
    have hnum : ‖((dispersion (gridAngle k) : ℂ) - E' - t * ρ) -
        ((dispersion (gridAngle k) : ℂ) - E - t * ρ)‖ = |E - E'| := by
      rw [show ((dispersion (gridAngle k) : ℂ) - E' - t * ρ) -
        ((dispersion (gridAngle k) : ℂ) - E - t * ρ) = ((E - E' : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hnum, sq]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      (mul_le_mul (hw E) (hw E') hta.le (norm_nonneg _))
  refine (gridAvgReal_mono hpt).trans (le_of_eq ?_)
  unfold gridAvgReal
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Torus d L) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The objects of Proposition 3.6 at a fixed point, given the grid bounds. -/
theorem fixed_point_package (hF : TorusFourierStatement) {L : ℕ} [NeZero L] (hL4 : 4 ≤ L)
    {E t : ℝ} {r : ℂ} (htpos : 0 < t) (htle1 : t ≤ 1) (hrim : 0 < r.im)
    (hfix : scalarMap (d := d) (L := L) E t r = r)
    (hR1 : gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) ≤ t ^ (-(1 / 5 : ℝ)))
    (hQ : ∀ ζ : Torus d L, t * ‖gridAvg (fun k : Torus d L =>
      gridResolvent E t r k * gridResolvent E t r (ζ - k))‖ ≤ 1 / 10 * t ^ (1 / 2 : ℝ)) :
    twoSidedInverse (initialMatrix (d := d) (L := L) E t r) (initialG E t r) ∧
    (∀ i : Torus d L, initialG E t r i i = r) ∧
    opNorm (initialK (d := d) (L := L) E t r) ≤ 1 / 10 ∧
    (∀ i : Torus d L, fourthRow E t r i ≤ (1 / 10) * Real.rpow t (1 + delta)) := by
  set z : ℂ := (E : ℂ) + (t : ℂ) * r with hz
  have hzne : ∀ k : Torus d L, (dispersion (gridAngle k) : ℂ) ≠ z := resolvent_z_ne htpos hrim
  have hRz : ∀ k : Torus d L, ((dispersion (gridAngle k) : ℂ) - z)⁻¹ = gridResolvent E t r k := by
    intro k
    simp only [gridResolvent, hz, sub_add_eq_sub_sub]
  obtain ⟨hFinv, hFop, hFrow, hFsym, -, -⟩ := hF d L hL4
  obtain ⟨hinv, hdiag⟩ := hFinv z hzne
  have hGeq : initialG (d := d) (L := L) E t r = freeGreen z := initialG_eq hF hL4 htpos hrim
  set G : Matrix (Torus d L) (Torus d L) ℂ := freeGreen z with hGdef
  set g : Torus d L → ℂ := fun x => (t : ℂ) * freeGreen z x 0 ^ 2 with hg
  have hsqrt : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt htpos.le]
  have hK : entrywiseSquare (((Real.sqrt t : ℝ) : ℂ) • G) = circulant g := by
    ext i j
    simp only [entrywiseSquare, Matrix.smul_apply, smul_eq_mul, circulant, hg, hGdef]
    rw [mul_pow, hsqrt, freeGreen_sub z i j]
  have hsym : ∀ ζ, fourier g ζ = (t : ℂ) * gridAvg (fun k : Torus d L =>
      gridResolvent E t r k * gridResolvent E t r (ζ - k)) := by
    intro ζ
    have h := hFsym z hzne ζ
    have : fourier g ζ = (t : ℂ) * fourier (fun x => freeGreen z x 0 ^ 2) ζ := by
      simp only [fourier, hg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, h]
    congr 2
    funext k
    rw [hRz, hRz]
  have hsymle : ∀ ζ, ‖fourier g ζ‖ ≤ 1 / 10 * t ^ (1 / 2 : ℝ) := by
    intro ζ
    rw [hsym, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    exact hQ ζ
  have hhalf : t ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one htpos.le htle1 (by norm_num)
  have hhalf : t ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one htpos.le htle1 (by norm_num)
  have hKeq : initialK (d := d) (L := L) E t r = entrywiseSquare (((Real.sqrt t : ℝ) : ℂ) • G) := by
    unfold initialK initialH; rw [hGeq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hGeq]; unfold initialMatrix; convert hinv using 3
  · intro i
    rw [hGeq]
    refine (hdiag i).trans ?_
    rw [← hfix]
    simp only [scalarMap]
    congr 1
    funext k
    exact hRz k
  · rw [hKeq, hK]
    have := hFop g (1 / 10) fun ζ => (hsymle ζ).trans (by nlinarith)
    convert this using 2
  · intro i
    have hfr : fourthRow (d := d) (L := L) E t r i =
        ∑ j, ‖((Real.sqrt t : ℝ) : ℂ) * G i j‖ ^ 4 := by
      unfold fourthRow initialH; rw [hGeq]; rfl
    rw [hfr]
    show _ ≤ 1 / 10 * t ^ (1 + 1 / 100 : ℝ)
    have hrow : ∑ j, ‖((Real.sqrt t : ℝ) : ℂ) * G i j‖ ^ 4 = ∑ j, ‖circulant g i j‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have : circulant g i j = (((Real.sqrt t : ℝ) : ℂ) * G i j) ^ 2 := by
        have := congrFun (congrFun hK i) j
        simpa [entrywiseSquare] using this.symm
      rw [this, norm_pow]
      ring
    rw [hrow, hFrow g i]
    -- `‖ĝ‖² ≤ sup‖ĝ‖ · ‖ĝ‖` and the convolution identity
    set A : Torus d L → ℝ := fun k => ‖gridResolvent E t r k‖ with hA
    have hpt : ∀ ζ : Torus d L, ‖fourier g ζ‖ ^ 2 ≤
        (1 / 10 * t ^ (1 / 2 : ℝ)) * (t * gridAvgReal (fun k => A k * A (ζ - k))) := by
      intro ζ
      have h1 := hsymle ζ
      have h2 : ‖fourier g ζ‖ ≤ t * gridAvgReal (fun k => A k * A (ζ - k)) := by
        rw [hsym, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
        apply mul_le_mul_of_nonneg_left _ htpos.le
        refine (norm_gridAvg_le _).trans (le_of_eq ?_)
        congr 1
        funext k
        rw [norm_mul]
      have h0 := norm_nonneg (fourier g ζ)
      rw [sq]
      exact mul_le_mul h1 h2 h0 (by positivity)
    have hA0 : 0 ≤ gridAvgReal A := gridAvgReal_nonneg fun k => norm_nonneg _
    calc gridAvgReal (fun ζ => ‖fourier g ζ‖ ^ 2)
        ≤ gridAvgReal (fun ζ => (1 / 10 * t ^ (1 / 2 : ℝ)) *
            (t * gridAvgReal (fun k => A k * A (ζ - k)))) := gridAvgReal_mono hpt
      _ = (1 / 10 * t ^ (1 / 2 : ℝ)) * (t * gridAvgReal A ^ 2) := by
          rw [gridAvgReal_mul_left, gridAvgReal_mul_left, gridAvgReal_conv]
      _ ≤ (1 / 10 * t ^ (1 / 2 : ℝ)) * (t * (t ^ (-(1 / 5 : ℝ))) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ htpos.le
          exact pow_le_pow_left₀ hA0 hR1 2
      _ = 1 / 10 * t ^ (11 / 10 : ℝ) := by
          rw [← Real.rpow_natCast (t ^ (-(1 / 5 : ℝ))) 2, ← Real.rpow_mul htpos.le]
          have e : t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
          conv_lhs => rw [show t * (t ^ (-(1 / 5 : ℝ) * ((2 : ℕ) : ℝ))) =
            t ^ (1 : ℝ) * (t ^ (-(1 / 5 : ℝ) * ((2 : ℕ) : ℝ))) by rw [Real.rpow_one]]
          rw [← Real.rpow_add htpos, mul_assoc, ← Real.rpow_add htpos]
          norm_num
      _ ≤ 1 / 10 * t ^ (1 + 1 / 100 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.rpow_le_rpow_of_exponent_ge htpos htle1 (by norm_num)

set_option maxHeartbeats 8000000 in
/-- **Proposition 3.6, normalized endpoint** (the planned `initialization_normalized`),
from the torus Fourier algebra, the circulant calculus, the window-parametric grid
bounds and the large-frequency decay. -/
theorem initialization_normalized_of (hF : TorusFourierStatement)
    (hC : CirculantCalculusStatement) (hG : GridBoundsWStatement)
    (hLD : LargeSymbolDecayWStatement) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    ∃ (nmin : ℕ) (a₀ B c C C₀ : ℝ), 1 ≤ nmin ∧
      0 < a₀ ∧ 0 < B ∧ 0 < c ∧ 0 < C ∧ 0 < C₀ ∧
      ∀ n₀ : ℕ, nmin ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m →
      ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      ∃ r : ℝ → ℂ, ContinuousOn r (energyWindow d e₂) ∧
      ∀ E ∈ energyWindow d e₂,
        let t := startupT n₀ m u
        let L := sideLength m
        r E ∈ rectangle a₀ B ∧
        scalarMap (d := d) (L := L) E t (r E) = r E ∧
        (∀ r' ∈ rectangle a₀ B, scalarMap (d := d) (L := L) E t r' = r' → r' = r E) ∧
        twoSidedInverse (initialMatrix (d := d) (L := L) E t (r E)) (initialG E t (r E)) ∧
        (∀ i : Torus d L, initialG E t (r E) i i = r E) ∧
        opNorm (initialK (d := d) (L := L) E t (r E)) ≤ 1 / 10 ∧
        (∀ i : Torus d L, fourthRow E t (r E) i ≤ (1 / 10) * Real.rpow t (1 + delta)) ∧
        connectedLaplacian (initialD (d := d) (L := L) E t (r E)) ∧
        (∀ y : Torus d L → ℂ, neutral y →
          c * t ^ 2 * form laplacianPlus y ≤ form (initialX E t (r E)) y ∧
          c * normSq y ≤ form (initialX E t (r E)) y ∧
          form (initialX E t (r E)) y ≤ C₀ * normSq y + C * t ^ 2 * form laplacianPlus y ∧
          form (initialX E t (r E)) y ≤
            (1 + Real.rpow t kappa) * (r E).im ^ (-2 : ℤ) * normSq y +
              C * t * form laplacianPlus y) := by
  set w : ℝ := min (e₂ / 2) (1 / 200) with hwdef
  have hw0 : 0 < w := lt_min (by linarith [he₂.1]) (by norm_num)
  obtain ⟨a₀, B, ha₀, haB, hGd⟩ := hG d hd w hw0
  have hB0 : 0 < B := lt_of_lt_of_le ha₀ haB
  obtain ⟨tG, htG, hGt⟩ := hGd (1 / 10) (by norm_num)
  obtain ⟨c, C, C₀, tC, hc, hC, hC₀, htC, hcomp⟩ := initial_comparators hF hC hLD hd hw0 ha₀ haB
  set t₀ : ℝ := min tG tC with ht₀def
  have ht₀ : 0 < t₀ := lt_min htG htC
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 / min t₀ 1) (by norm_num : (1 : ℝ) < 4)
  have hmin : 0 < min t₀ 1 := lt_min ht₀ one_pos
  refine ⟨N + 1, a₀, B, c, C, C₀, by omega, ha₀, hB0, hc, hC, hC₀, ?_⟩
  intro n₀ hn₀ m hm u hu
  -- the interface parameter
  set t : ℝ := OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u with htdef
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have h4n : (0 : ℝ) < 4 ^ n₀ := by positivity
  have h4m : (0 : ℝ) < 4 ^ m := by positivity
  have hmn : (4 : ℝ) ^ n₀ ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
  have htpos : 0 < t := by
    simp only [htdef, OAI.Anderson.scaleHeight]; positivity
  have htlow : 1 / (4 : ℝ) ^ (n₀ + 1) < t := by
    have h1 : u / (4 : ℝ) ^ n₀ ≤ t := by
      simp only [htdef, OAI.Anderson.scaleHeight]
      have : 0 ≤ u / (4 : ℝ) ^ m := by positivity
      linarith
    have h2 : 1 / (4 : ℝ) ^ (n₀ + 1) < u / (4 : ℝ) ^ n₀ := by
      rw [pow_succ, div_lt_div_iff₀ (by positivity) h4n]
      nlinarith [hu.1]
    linarith
  have hthigh : t ≤ min t₀ 1 := by
    have h1 : t ≤ 2 / (4 : ℝ) ^ n₀ := by
      simp only [htdef, OAI.Anderson.scaleHeight]
      have e1 : u / (4 : ℝ) ^ n₀ ≤ 1 / 4 ^ n₀ := div_le_div_of_nonneg_right hu.2 h4n.le
      have e2 : u / (4 : ℝ) ^ m ≤ 1 / 4 ^ n₀ :=
        (div_le_div_of_nonneg_right hu.2 h4m.le).trans (div_le_div_of_nonneg_left (by norm_num) h4n hmn)
      have : (2 : ℝ) / 4 ^ n₀ = 1 / 4 ^ n₀ + 1 / 4 ^ n₀ := by ring
      linarith
    have h2 : (2 : ℝ) / 4 ^ n₀ ≤ min t₀ 1 := by
      rw [div_le_iff₀ h4n]
      have hNn : (4 : ℝ) ^ N ≤ 4 ^ n₀ := pow_le_pow_right₀ (by norm_num) (by omega)
      have := (div_lt_iff₀ hmin).mp hN
      nlinarith
    linarith
  have htle1 : t ≤ 1 := hthigh.trans (min_le_right _ _)
  have htt₀ : t ≤ t₀ := hthigh.trans (min_le_left _ _)
  -- the torus side length
  set L : ℕ := sideLength m with hLdef
  have hm1 : 1 ≤ m := by omega
  have hL4 : 4 ≤ L := by
    simp only [hLdef, sideLength, OAI.Anderson.sideLength]
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (20 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLeven : Even L := by
    simp only [hLdef, sideLength, OAI.Anderson.sideLength]
    exact (Nat.even_pow' (by omega)).mpr (by decide)
  have hLbig : t⁻¹ ^ 8 ≤ (L : ℝ) := by
    have h1 : t⁻¹ ≤ (4 : ℝ) ^ (n₀ + 1) := by
      rw [inv_le_comm₀ htpos (by positivity)]
      simpa using htlow.le
    calc t⁻¹ ^ 8 ≤ ((4 : ℝ) ^ (n₀ + 1)) ^ 8 := pow_le_pow_left₀ (by positivity) h1 8
      _ = (4 : ℝ) ^ (8 * (n₀ + 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ (4 : ℝ) ^ (20 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (L : ℝ) := by simp [hLdef, sideLength, OAI.Anderson.sideLength]
  have htG' : t ≤ tG := htt₀.trans (min_le_left _ _)
  have htC' : t ≤ tC := htt₀.trans (min_le_right _ _)
  have hEw : ∀ E ∈ energyWindow d e₂, w ≤ E + 2 * d ∧ E + 2 * d ≤ 1 / 100 := by
    intro E hE
    have hw1 : w ≤ e₂ / 2 := min_le_left _ _
    have hw2 : w ≤ 1 / 200 := min_le_right _ _
    unfold energyWindow at hE
    by_cases h3 : d = 3
    · subst h3
      simp only [OAI.Anderson.energyWindow_three, Set.mem_Ioo] at hE
      push_cast
      constructor <;> linarith [hE.1, hE.2, he₂.2]
    · rw [OAI.Anderson.energyWindow_of_four_le (by omega)] at hE
      simp only [OAI.Anderson.higherDimWindow, Set.mem_Ioo] at hE
      constructor <;> linarith [hE.1, hE.2]
  have hbnd := fun E (hE : E ∈ energyWindow d e₂) =>
    hGt t htpos htG' L hL4 hLeven hLbig E (hEw E hE).1 (hEw E hE).2
  have hex : ∀ E ∈ energyWindow d e₂, ∃ r ∈ rectangle a₀ B,
      scalarMap (d := d) (L := L) E t r = r := by
    intro E hE
    exact rect_scalar_fixed_point (d := d) (L := L) (E := E) htpos ha₀ haB
      (fun r hr => (hbnd E hE r hr).1) (fun r hr => (hbnd E hE r hr).2.1)
  choose! rf hrf_mem hrf_fix using hex
  have huniq : ∀ E ∈ energyWindow d e₂, ∀ r' ∈ rectangle a₀ B,
      scalarMap (d := d) (L := L) E t r' = r' → r' = rf E := by
    intro E hE r' hr' hfix'
    have h := scalar_contraction (d := d) (L := L) (E := E) htpos ha₀
      (fun r hr => (hbnd E hE r hr).2.1) (hrf_mem E hE) hr'
    rw [hfix', hrf_fix E hE] at h
    have : ‖r' - rf E‖ = 0 := by
      have h0 := norm_nonneg (r' - rf E)
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨rf, ?_, fun E hE => ?_⟩
  · -- continuity: the fixed point is Lipschitz in the energy
    have hlip : ∀ E ∈ energyWindow d e₂, ∀ E' ∈ energyWindow d e₂,
        dist (rf E) (rf E') ≤ 2 / (t * a₀) ^ 2 * dist E E' := by
      intro E hE E' hE'
      have h1 := scalar_contraction (d := d) (L := L) (E := E) htpos ha₀
        (fun r hr => (hbnd E hE r hr).2.1) (hrf_mem E' hE') (hrf_mem E hE)
      have h2 := scalarMap_energy_lip (d := d) (L := L) (E := E) (E' := E') htpos ha₀
        (hrf_mem E' hE').2.1
      rw [hrf_fix E hE] at h1
      rw [hrf_fix E' hE'] at h2
      rw [dist_eq_norm, Real.dist_eq]
      have h3 : ‖rf E - rf E'‖ ≤ ‖rf E - scalarMap (d := d) (L := L) E t (rf E')‖ +
          ‖scalarMap (d := d) (L := L) E t (rf E') - rf E'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have e : 2 / (t * a₀) ^ 2 * |E - E'| = 2 * (|E - E'| / (t * a₀) ^ 2) := by ring
      rw [e]
      linarith
    refine LipschitzOnWith.continuousOn (K := Real.toNNReal (2 / (t * a₀) ^ 2)) ?_
    refine LipschitzOnWith.of_dist_le_mul fun E hE E' hE' => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    exact hlip E hE E' hE'
  dsimp only
  obtain ⟨-, -, hR1, hQ⟩ := hbnd E hE (rf E) (hrf_mem E hE)
  have hrim : 0 < (rf E).im := rectangle_im_pos ha₀ (hrf_mem E hE)
  obtain ⟨hinv, hdiag, hK, hrow⟩ := fixed_point_package (d := d) hF hL4 htpos htle1 hrim
    (hrf_fix E hE) hR1 hQ
  obtain ⟨hconn, hforms⟩ := hcomp t htpos htC' L hL4 hLeven hLbig E (hEw E hE).1 (hEw E hE).2
    (rf E) (hrf_mem E hE) (hrf_fix E hE)
  exact ⟨hrf_mem E hE, hrf_fix E hE, huniq E hE, hinv, hdiag, hK, hrow, hconn, hforms⟩

end AndersonAC.S3
