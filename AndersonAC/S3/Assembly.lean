import AndersonAC.S3.HelperStatements
import AndersonAC.S3.HelperStatements2

/-!
Algebraic assembly of initialization package (`InitializationInput`, Proposition 3.6 of §3):
the scalar fixed point by contraction on the rectangle, the inverse by the
torus Fourier algebra, and the two smallness bounds from the circulant
symbol `Q(ζ) = t · gridAvg_k R(k) R(ζ-k)`.

The analytic input is isolated in `GridBoundsStatement` (grid-level bounds
near the band bottom); the algebraic input is `TorusFourierStatement`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal
open AndersonAC.Blueprint

namespace AndersonAC.S3

/-- Grid-level analytic bounds near the band bottom: the scalar map preserves the
rectangle and is a `1/2`-contraction (through its derivative `t · gridAvg R²`), the
absolute grid average of `R` is at most `t^{-1/5}`, and the circulant symbol of the
entrywise square is at most `δ t^{1/2}`. Here `E + 2d ∈ [1/400, 1/100]`. -/
def GridBoundsStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ a₀ B : ℝ, 0 < a₀ ∧ a₀ ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
      ∀ E : ℝ, 1 / 400 ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 →
        ∀ r ∈ rectangle a₀ B,
          scalarMap (d := d) (L := L) E t r ∈ rectangle a₀ B ∧
          ‖(t : ℂ) * gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2)‖ ≤ 1 / 2 ∧
          gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) ≤ t ^ (-(1 / 5 : ℝ)) ∧
          ∀ ζ : Torus d L, t * ‖gridAvg (fun k : Torus d L =>
            gridResolvent E t r k * gridResolvent E t r (ζ - k))‖ ≤ δ * t ^ (1 / 2 : ℝ)

/-- `GridBoundsStatement` for every lower window edge `w > 0` (constants depend on `w`). -/
def GridBoundsWStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ w : ℝ, 0 < w → ∃ a₀ B : ℝ, 0 < a₀ ∧ a₀ ≤ B ∧ ∀ δ : ℝ, 0 < δ →
    ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
      ∀ E : ℝ, w ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 →
        ∀ r ∈ rectangle a₀ B,
          scalarMap (d := d) (L := L) E t r ∈ rectangle a₀ B ∧
          ‖(t : ℂ) * gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2)‖ ≤ 1 / 2 ∧
          gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) ≤ t ^ (-(1 / 5 : ℝ)) ∧
          ∀ ζ : Torus d L, t * ‖gridAvg (fun k : Torus d L =>
            gridResolvent E t r k * gridResolvent E t r (ζ - k))‖ ≤ δ * t ^ (1 / 2 : ℝ)

theorem resolvent_den_ne {E t : ℝ} {r : ℂ} (ht : 0 < t) (hr : 0 < r.im) (x : ℝ) :
    (x : ℂ) - E - t * r ≠ 0 := by
  intro h
  have h' := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.zero_im] at h'
  nlinarith [mul_pos ht hr]

theorem rectangle_im_pos {a₀ B : ℝ} (ha : 0 < a₀) {r : ℂ} (hr : r ∈ rectangle a₀ B) :
    0 < r.im := lt_of_lt_of_le ha hr.2.1

theorem rectangle_convex (a₀ B : ℝ) : Convex ℝ (rectangle a₀ B) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have hx1' := abs_le.mp hx1
  have hy1' := abs_le.mp hy1
  refine ⟨?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [abs_le]
    constructor <;> nlinarith
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    nlinarith
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    nlinarith

theorem rectangle_isClosed (a₀ B : ℝ) : IsClosed (rectangle a₀ B) := by
  have h1 : IsClosed {r : ℂ | |r.re| ≤ B} :=
    isClosed_le (Complex.continuous_re.abs) continuous_const
  have h2 : IsClosed {r : ℂ | a₀ ≤ r.im} := isClosed_le continuous_const Complex.continuous_im
  have h3 : IsClosed {r : ℂ | r.im ≤ B} := isClosed_le Complex.continuous_im continuous_const
  have : rectangle a₀ B = {r : ℂ | |r.re| ≤ B} ∩ ({r : ℂ | a₀ ≤ r.im} ∩ {r : ℂ | r.im ≤ B}) := by
    ext r; simp [rectangle]
  rw [this]
  exact h1.inter (h2.inter h3)

theorem rectangle_norm_le {a₀ B : ℝ} {r : ℂ} (ha : 0 < a₀) (hr : r ∈ rectangle a₀ B) :
    ‖r‖ ≤ 2 * B := by
  obtain ⟨h1, h2, h3⟩ := hr
  calc ‖r‖ ≤ |r.re| + |r.im| := Complex.norm_le_abs_re_add_abs_im r
    _ ≤ B + B := by
        have : |r.im| = r.im := abs_of_pos (by linarith)
        rw [this]; linarith
    _ = 2 * B := by ring

theorem scalarMap_hasDerivAt {d L : ℕ} [NeZero L] {E t : ℝ} {r : ℂ} (ht : 0 < t)
    (hr : 0 < r.im) :
    HasDerivAt (fun r => scalarMap (d := d) (L := L) E t r)
      ((t : ℂ) * gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2)) r := by
  unfold scalarMap gridAvg
  have hsum : HasDerivAt (fun r => ∑ k : Torus d L, gridResolvent E t r k)
      (∑ k : Torus d L, (t : ℂ) * gridResolvent E t r k ^ 2) r := by
    apply HasDerivAt.fun_sum
    intro k _
    have hne := resolvent_den_ne (E := E) ht hr (dispersion (gridAngle k))
    have hlin : HasDerivAt (fun r : ℂ => (dispersion (gridAngle k) : ℂ) - E - t * r) (-(t : ℂ)) r := by
      have := ((hasDerivAt_id r).const_mul (t : ℂ)).const_sub ((dispersion (gridAngle k) : ℂ) - E)
      simpa using this
    have h := hlin.inv hne
    unfold gridResolvent
    convert h using 1
    field_simp
  have := hsum.const_mul ((Fintype.card (Torus d L) : ℂ)⁻¹)
  convert this using 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- Contraction fixed point in the rectangle. -/
theorem rect_scalar_fixed_point {d L : ℕ} [NeZero L] {E t a₀ B : ℝ} (ht : 0 < t) (ha : 0 < a₀)
    (hab : a₀ ≤ B)
    (hmaps : ∀ r ∈ rectangle a₀ B, scalarMap (d := d) (L := L) E t r ∈ rectangle a₀ B)
    (hderiv : ∀ r ∈ rectangle a₀ B,
      ‖(t : ℂ) * gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2)‖ ≤ 1 / 2) :
    ∃ r ∈ rectangle a₀ B, scalarMap (d := d) (L := L) E t r = r := by
  set s := rectangle a₀ B
  set f := fun r => scalarMap (d := d) (L := L) E t r with hf
  have hsf : MapsTo f s s := fun r hr => hmaps r hr
  have hlip : ∀ x ∈ s, ∀ y ∈ s, ‖f y - f x‖ ≤ 1 / 2 * ‖y - x‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun r => (t : ℂ) * gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2))
      (fun z hz => (scalarMap_hasDerivAt ht (rectangle_im_pos ha hz)).hasDerivWithinAt)
      (fun z hz => hderiv z hz) (rectangle_convex a₀ B) hx hy
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hsf.restrict f s s) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    change ‖f x - f y‖ ≤ ((1 / 2 : ℝ≥0) : ℝ) * ‖(x : ℂ) - y‖
    have := hlip x x.2 y y.2
    rw [norm_sub_rev (f x), norm_sub_rev (x : ℂ)]
    simpa using this
  have hmem : (⟨0, a₀⟩ : ℂ) ∈ s := ⟨by simp; linarith, le_rfl, hab⟩
  obtain ⟨y, hy, hfix, -⟩ := hcontr.exists_fixedPoint' (rectangle_isClosed a₀ B).isComplete
    hsf hmem (edist_ne_top _ _)
  exact ⟨y, hy, hfix⟩

theorem periodicHamiltonian_zero_eq {d m : ℕ} (ω : OAI.Anderson.TorusConfiguration d m) :
    OAI.Anderson.periodicHamiltonian 0 ω =
      freeHopping (d := d) (L := OAI.Anderson.sideLength m) := by
  ext x y
  simp only [OAI.Anderson.periodicHamiltonian, freeHopping, basisStep,
    OAI.Anderson.torusBasisVector, zero_mul, Complex.ofReal_zero, ite_self, add_zero]
  congr 1

theorem norm_gridAvg_le {d L : ℕ} [NeZero L] (v : Torus d L → ℂ) :
    ‖gridAvg v‖ ≤ gridAvgReal (fun k => ‖v k‖) := by
  unfold gridAvg gridAvgReal
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem gridAvgReal_conv {d L : ℕ} [NeZero L] (a : Torus d L → ℝ) :
    gridAvgReal (fun ζ : Torus d L => gridAvgReal (fun k => a k * a (ζ - k))) =
      gridAvgReal a ^ 2 := by
  unfold gridAvgReal
  rw [← Finset.mul_sum]
  have h : ∑ ζ : Torus d L, ∑ k : Torus d L, a k * a (ζ - k) =
      (∑ k : Torus d L, a k) * ∑ k : Torus d L, a k := by
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight k) _ _ (fun _ => rfl)
  rw [h]
  ring

theorem freeGreen_sub {d L : ℕ} [NeZero L] (z : ℂ) (i j : Torus d L) :
    freeGreen z i j = freeGreen z (i - j) 0 := by
  simp [freeGreen]

theorem gridAvgReal_nonneg {d L : ℕ} [NeZero L] {a : Torus d L → ℝ} (ha : ∀ k, 0 ≤ a k) :
    0 ≤ gridAvgReal a := by
  unfold gridAvgReal
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => ha k)

theorem gridAvgReal_mono {d L : ℕ} [NeZero L] {a b : Torus d L → ℝ} (h : ∀ k, a k ≤ b k) :
    gridAvgReal a ≤ gridAvgReal b := by
  unfold gridAvgReal
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => h k) (by positivity)

theorem gridAvgReal_mul_left {d L : ℕ} [NeZero L] (c : ℝ) (a : Torus d L → ℝ) :
    gridAvgReal (fun k => c * a k) = c * gridAvgReal a := by
  unfold gridAvgReal
  rw [← Finset.mul_sum]
  ring

/-- **Assembly of initialization package** from the grid bounds and the torus Fourier algebra, with `e₂ = 1/200`. -/
theorem initialization_of_gridBounds (hF : TorusFourierStatement) (hG : GridBoundsStatement) :
    InitializationInput (1 / 200) := by
  intro d hd
  obtain ⟨a₀, B, ha₀, haB, hGd⟩ := hG d hd
  obtain ⟨t₀, ht₀, hGt⟩ := hGd (1 / 10) (by norm_num)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 / min t₀ 1) (by norm_num : (1 : ℝ) < 4)
  have hmin : 0 < min t₀ 1 := lt_min ht₀ one_pos
  refine ⟨N + 1, a₀, 2 * B, ha₀, by linarith, ?_⟩
  intro n₀ m hn₀ hm u hu E hE
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
  set L : ℕ := OAI.Anderson.sideLength m with hLdef
  have hm1 : 1 ≤ m := by omega
  have hL4 : 4 ≤ L := by
    simp only [hLdef, OAI.Anderson.sideLength]
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (20 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLeven : Even L := by
    simp only [hLdef, OAI.Anderson.sideLength]
    exact (Nat.even_pow' (by omega)).mpr (by decide)
  have hLbig : t⁻¹ ^ 8 ≤ (L : ℝ) := by
    have h1 : t⁻¹ ≤ (4 : ℝ) ^ (n₀ + 1) := by
      rw [inv_le_comm₀ htpos (by positivity)]
      simpa using htlow.le
    calc t⁻¹ ^ 8 ≤ ((4 : ℝ) ^ (n₀ + 1)) ^ 8 := pow_le_pow_left₀ (by positivity) h1 8
      _ = (4 : ℝ) ^ (8 * (n₀ + 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ (4 : ℝ) ^ (20 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (L : ℝ) := by simp [hLdef, OAI.Anderson.sideLength]
  -- the energy window
  have hEw : 1 / 400 ≤ E + 2 * d ∧ E + 2 * d ≤ 1 / 100 := by
    by_cases h3 : d = 3
    · subst h3
      simp only [OAI.Anderson.energyWindow_three, Set.mem_Ioo] at hE
      push_cast
      constructor <;> linarith [hE.1, hE.2]
    · rw [OAI.Anderson.energyWindow_of_four_le (by omega)] at hE
      simp only [OAI.Anderson.higherDimWindow, Set.mem_Ioo] at hE
      constructor <;> linarith [hE.1, hE.2]
  have hbounds := hGt t htpos htt₀ L hL4 hLeven hLbig E hEw.1 hEw.2
  -- the scalar fixed point
  obtain ⟨r, hr, hfix⟩ := rect_scalar_fixed_point (d := d) (L := L) (E := E) htpos ha₀ haB
    (fun r hr => (hbounds r hr).1) (fun r hr => (hbounds r hr).2.1)
  obtain ⟨-, -, hR1, hQ⟩ := hbounds r hr
  have hrim : 0 < r.im := rectangle_im_pos ha₀ hr
  set z : ℂ := (E : ℂ) + (t : ℂ) * r with hz
  have hzne : ∀ k : Torus d L, (dispersion (gridAngle k) : ℂ) ≠ z := by
    intro k h
    have h' := congrArg Complex.im h
    simp only [hz, Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add] at h'
    nlinarith [mul_pos htpos hrim]
  have hRz : ∀ k : Torus d L, ((dispersion (gridAngle k) : ℂ) - z)⁻¹ = gridResolvent E t r k := by
    intro k
    simp only [gridResolvent, hz, sub_add_eq_sub_sub]
  obtain ⟨hFinv, hFop, hFrow, hFsym, -, -⟩ := hF d L hL4
  obtain ⟨hinv, hdiag⟩ := hFinv z hzne
  set G : Matrix (Torus d L) (Torus d L) ℂ := freeGreen z with hGdef
  -- the circulant symbol of the entrywise square
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
  refine ⟨r, G, ?_, hr.2.1, ?_, ?_, ?_, ?_⟩
  · exact rectangle_norm_le ha₀ hr
  · -- the inverse
    have hmat : OAI.Anderson.periodicHamiltonian 0 (fun _ => ⟨0, by norm_num⟩) - (E : ℂ) • 1 -
        ((t : ℝ) : ℂ) • Matrix.diagonal (fun _ => r) =
        freeHopping (d := d) (L := L) - z • (1 : Matrix (Torus d L) (Torus d L) ℂ) := by
      rw [periodicHamiltonian_zero_eq]
      ext x y
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
        smul_eq_mul, hz]
      split_ifs <;> ring
    rw [htdef] at hmat
    rw [hmat]
    exact hinv
  · intro i
    refine (hdiag i).trans ?_
    rw [← hfix]
    simp only [scalarMap]
    congr 1
    funext k
    exact hRz k
  · rw [hK]
    refine hFop g _ fun ζ => (hsymle ζ).trans ?_
    nlinarith
  · intro i
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


/-- **Assembly of initialization package for every window parameter** `e₂ ∈ (0, 1/100)`. -/
theorem initializationInput_of_gridBoundsW (hF : TorusFourierStatement)
    (hG : GridBoundsWStatement) {e₂ : ℝ} (he : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    InitializationInput e₂ := by
  intro d hd
  set w : ℝ := min (e₂ / 2) (1 / 200) with hwdef
  have hw0 : 0 < w := lt_min (by linarith [he.1]) (by norm_num)
  obtain ⟨a₀, B, ha₀, haB, hGd⟩ := hG d hd w hw0
  obtain ⟨t₀, ht₀, hGt⟩ := hGd (1 / 10) (by norm_num)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 / min t₀ 1) (by norm_num : (1 : ℝ) < 4)
  have hmin : 0 < min t₀ 1 := lt_min ht₀ one_pos
  refine ⟨N + 1, a₀, 2 * B, ha₀, by linarith, ?_⟩
  intro n₀ m hn₀ hm u hu E hE
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
  set L : ℕ := OAI.Anderson.sideLength m with hLdef
  have hm1 : 1 ≤ m := by omega
  have hL4 : 4 ≤ L := by
    simp only [hLdef, OAI.Anderson.sideLength]
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (20 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLeven : Even L := by
    simp only [hLdef, OAI.Anderson.sideLength]
    exact (Nat.even_pow' (by omega)).mpr (by decide)
  have hLbig : t⁻¹ ^ 8 ≤ (L : ℝ) := by
    have h1 : t⁻¹ ≤ (4 : ℝ) ^ (n₀ + 1) := by
      rw [inv_le_comm₀ htpos (by positivity)]
      simpa using htlow.le
    calc t⁻¹ ^ 8 ≤ ((4 : ℝ) ^ (n₀ + 1)) ^ 8 := pow_le_pow_left₀ (by positivity) h1 8
      _ = (4 : ℝ) ^ (8 * (n₀ + 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ (4 : ℝ) ^ (20 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (L : ℝ) := by simp [hLdef, OAI.Anderson.sideLength]
  -- the energy window
  have hEw : w ≤ E + 2 * d ∧ E + 2 * d ≤ 1 / 100 := by
    have hw1 : w ≤ e₂ / 2 := min_le_left _ _
    have hw2 : w ≤ 1 / 200 := min_le_right _ _
    by_cases h3 : d = 3
    · subst h3
      simp only [OAI.Anderson.energyWindow_three, Set.mem_Ioo] at hE
      push_cast
      constructor <;> linarith [hE.1, hE.2, he.2]
    · rw [OAI.Anderson.energyWindow_of_four_le (by omega)] at hE
      simp only [OAI.Anderson.higherDimWindow, Set.mem_Ioo] at hE
      constructor <;> linarith [hE.1, hE.2]
  have hbounds := hGt t htpos htt₀ L hL4 hLeven hLbig E hEw.1 hEw.2
  -- the scalar fixed point
  obtain ⟨r, hr, hfix⟩ := rect_scalar_fixed_point (d := d) (L := L) (E := E) htpos ha₀ haB
    (fun r hr => (hbounds r hr).1) (fun r hr => (hbounds r hr).2.1)
  obtain ⟨-, -, hR1, hQ⟩ := hbounds r hr
  have hrim : 0 < r.im := rectangle_im_pos ha₀ hr
  set z : ℂ := (E : ℂ) + (t : ℂ) * r with hz
  have hzne : ∀ k : Torus d L, (dispersion (gridAngle k) : ℂ) ≠ z := by
    intro k h
    have h' := congrArg Complex.im h
    simp only [hz, Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add] at h'
    nlinarith [mul_pos htpos hrim]
  have hRz : ∀ k : Torus d L, ((dispersion (gridAngle k) : ℂ) - z)⁻¹ = gridResolvent E t r k := by
    intro k
    simp only [gridResolvent, hz, sub_add_eq_sub_sub]
  obtain ⟨hFinv, hFop, hFrow, hFsym, -, -⟩ := hF d L hL4
  obtain ⟨hinv, hdiag⟩ := hFinv z hzne
  set G : Matrix (Torus d L) (Torus d L) ℂ := freeGreen z with hGdef
  -- the circulant symbol of the entrywise square
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
  refine ⟨r, G, ?_, hr.2.1, ?_, ?_, ?_, ?_⟩
  · exact rectangle_norm_le ha₀ hr
  · -- the inverse
    have hmat : OAI.Anderson.periodicHamiltonian 0 (fun _ => ⟨0, by norm_num⟩) - (E : ℂ) • 1 -
        ((t : ℝ) : ℂ) • Matrix.diagonal (fun _ => r) =
        freeHopping (d := d) (L := L) - z • (1 : Matrix (Torus d L) (Torus d L) ℂ) := by
      rw [periodicHamiltonian_zero_eq]
      ext x y
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
        smul_eq_mul, hz]
      split_ifs <;> ring
    rw [htdef] at hmat
    rw [hmat]
    exact hinv
  · intro i
    refine (hdiag i).trans ?_
    rw [← hfix]
    simp only [scalarMap]
    congr 1
    funext k
    exact hRz k
  · rw [hK]
    refine hFop g _ fun ζ => (hsymle ζ).trans ?_
    nlinarith
  · intro i
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

end AndersonAC.S3
