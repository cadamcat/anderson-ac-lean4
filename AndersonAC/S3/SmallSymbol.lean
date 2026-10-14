import AndersonAC.S3.SymbolStatements
import AndersonAC.S3.Reciprocal

/-! Small-frequency cancellation for the §3 Fourier symbol. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal Interval

namespace AndersonAC.S3

private def interpolationWeight (u θ : ℝ) : ℂ :=
  ((1 - u : ℝ) : ℂ) + (u : ℂ) * Complex.exp ((-θ) * Complex.I)

private theorem exp_sub_angle_re (x y : ℝ) :
    (Complex.exp (((x : ℂ) - y) * Complex.I)).re = Real.cos (x - y) := by
  rw [Complex.exp_re]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]

private theorem exp_add_angle_re (x y : ℝ) :
    (Complex.exp (((x : ℂ) + y) * Complex.I)).re = Real.cos (x + y) := by
  rw [Complex.exp_re]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

private theorem interpolation_cos_identity (u θ κ : ℝ) :
    (1 - u) * Real.cos κ + u * Real.cos (κ - θ) =
      ‖interpolationWeight u θ‖ * Real.cos (κ + (interpolationWeight u θ).arg) := by
  let w := interpolationWeight u θ
  have hshift : Complex.exp (κ * Complex.I) * Complex.exp ((-θ) * Complex.I) =
      Complex.exp ((κ - θ) * Complex.I) := by
    calc
      Complex.exp (κ * Complex.I) * Complex.exp ((-θ) * Complex.I) =
          Complex.exp (κ * Complex.I + (-θ) * Complex.I) := by rw [← Complex.exp_add]
      _ = Complex.exp ((κ - θ) * Complex.I) := by congr 1 <;> push_cast <;> ring
  have hprod : Complex.exp (κ * Complex.I) * w =
      (‖w‖ : ℂ) * Complex.exp ((κ + w.arg) * Complex.I) := by
    calc
      Complex.exp (κ * Complex.I) * w =
          (‖w‖ : ℂ) * (Complex.exp (κ * Complex.I) * Complex.exp (w.arg * Complex.I)) := by
            have hw : w = (‖w‖ : ℂ) * Complex.exp (w.arg * Complex.I) :=
              (Complex.norm_mul_exp_arg_mul_I w).symm
            calc
              Complex.exp (κ * Complex.I) * w =
                  Complex.exp (κ * Complex.I) * ((‖w‖ : ℂ) * Complex.exp (w.arg * Complex.I)) :=
                    congrArg (fun z : ℂ => Complex.exp (κ * Complex.I) * z) hw
              _ = (‖w‖ : ℂ) * (Complex.exp (κ * Complex.I) * Complex.exp (w.arg * Complex.I)) := by ring
      _ = (‖w‖ : ℂ) * Complex.exp ((κ + w.arg) * Complex.I) := by
            congr 1
            calc
              Complex.exp (κ * Complex.I) * Complex.exp (w.arg * Complex.I) =
                  Complex.exp (κ * Complex.I + w.arg * Complex.I) := by rw [← Complex.exp_add]
              _ = Complex.exp ((κ + w.arg) * Complex.I) := by congr 1 <;> push_cast <;> ring
  have hseg : Complex.exp (κ * Complex.I) * w =
      ((1 - u : ℝ) : ℂ) * Complex.exp (κ * Complex.I) +
        (u : ℂ) * Complex.exp ((κ - θ) * Complex.I) := by
    calc
      Complex.exp (κ * Complex.I) * w =
          Complex.exp (κ * Complex.I) *
            (((1 - u : ℝ) : ℂ) + (u : ℂ) * Complex.exp ((-θ) * Complex.I)) := rfl
      _ = ((1 - u : ℝ) : ℂ) * Complex.exp (κ * Complex.I) +
          (u : ℂ) * (Complex.exp (κ * Complex.I) * Complex.exp ((-θ) * Complex.I)) := by ring
      _ = ((1 - u : ℝ) : ℂ) * Complex.exp (κ * Complex.I) +
          (u : ℂ) * Complex.exp ((κ - θ) * Complex.I) := by rw [hshift]
  have hexpκ : (Complex.exp (κ * Complex.I)).re = Real.cos κ :=
    Complex.exp_ofReal_mul_I_re κ
  have hexpκθ : (Complex.exp ((κ - θ) * Complex.I)).re = Real.cos (κ - θ) :=
    exp_sub_angle_re κ θ
  have hexpφ : (Complex.exp ((κ + w.arg) * Complex.I)).re = Real.cos (κ + w.arg) :=
    exp_add_angle_re κ w.arg
  have hleft : (Complex.exp (κ * Complex.I) * w).re =
      (1 - u) * Real.cos κ + u * Real.cos (κ - θ) := by
    rw [hseg, Complex.add_re, Complex.mul_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hexpκ, hexpκθ,
      zero_mul, sub_zero, mul_zero]
  have hright : ((‖w‖ : ℂ) * Complex.exp ((κ + w.arg) * Complex.I)).re =
      ‖w‖ * Real.cos (κ + w.arg) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hexpφ, zero_mul, sub_zero, mul_zero]
  have h := congrArg Complex.re hprod
  rw [hleft, hright] at h
  exact h

private theorem interpolation_amplitude_close (u θ : ℝ) (hu : u ∈ Set.Icc 0 1) :
    |‖interpolationWeight u θ‖ - 1| ≤ |θ| := by
  let w := interpolationWeight u θ
  have hexp : ‖Complex.exp ((-θ) * Complex.I) - 1‖ ≤ |θ| := by
    calc
      ‖Complex.exp ((-θ) * Complex.I) - 1‖ =
          ‖Complex.exp (Complex.I * (-θ)) - 1‖ := by congr 1 <;> congr 1 <;> ring
      _ ≤ |θ| := by simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -θ))
  have hsub : w - 1 = (u : ℂ) * (Complex.exp ((-θ) * Complex.I) - 1) := by
    dsimp [w, interpolationWeight]
    push_cast
    ring
  have hwdist : ‖w - 1‖ ≤ |θ| := by
    rw [hsub]
    rw [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc
      |u| * ‖Complex.exp ((-θ) * Complex.I) - 1‖ ≤ u * |θ| := by
        rw [abs_of_nonneg hu.1]
        exact mul_le_mul_of_nonneg_left hexp hu.1
      _ ≤ |θ| := by
        calc
          u * |θ| ≤ 1 * |θ| := mul_le_mul_of_nonneg_right hu.2 (abs_nonneg θ)
          _ = |θ| := one_mul _
  have hnorm := (abs_norm_sub_norm_le w (1 : ℂ)).trans hwdist
  simpa [w] using hnorm

private theorem gridAngle_cos_sub {d L : ℕ} [NeZero L]
    (hT : TorusFourierStatement) (hL : 4 ≤ L) (k ζ : Torus d L) (j : Fin d) :
    Real.cos (gridAngle (ζ - k) j) = Real.cos (gridAngle k j - gridAngle ζ j) := by
  rcases hT d L hL with ⟨_, _, _, _, hadd, hneg⟩
  obtain ⟨n, hn⟩ := hadd ζ (-k) j
  obtain ⟨m, hm⟩ := hneg k j
  have hangle : gridAngle (ζ - k) j =
      gridAngle ζ j - gridAngle k j + (n + m : ℤ) * (2 * Real.pi) := by
    rw [sub_eq_add_neg, hn, hm]
    push_cast
    ring
  rw [hangle, Real.cos_add_int_mul_two_pi]
  have hflip : gridAngle ζ j - gridAngle k j = -(gridAngle k j - gridAngle ζ j) := by ring
  rw [hflip, Real.cos_neg]

private def interpolationAmplitude {d L : ℕ} [NeZero L]
    (u : ℝ) (ζ : Torus d L) : Frequency d :=
  fun j => ‖interpolationWeight u (gridAngle ζ j)‖

private def interpolationPhase {d L : ℕ} [NeZero L]
    (u : ℝ) (ζ : Torus d L) : Frequency d :=
  fun j => (interpolationWeight u (gridAngle ζ j)).arg

private theorem interpolated_dispersion {d L : ℕ} [NeZero L]
    (hT : TorusFourierStatement) (hL : 4 ≤ L) (u : ℝ)
    (k ζ : Torus d L) :
    (1 - u) * dispersion (gridAngle k) + u * dispersion (gridAngle (ζ - k)) =
      perturbedDispersion (interpolationAmplitude u ζ) (interpolationPhase u ζ) (gridAngle k) := by
  let a := interpolationAmplitude u ζ
  let φ := interpolationPhase u ζ
  have hcos := gridAngle_cos_sub hT hL k ζ
  unfold dispersion perturbedDispersion
  simp_rw [hcos]
  calc
    (1 - u) * (-2 * ∑ j, Real.cos (gridAngle k j)) +
        u * (-2 * ∑ j, Real.cos (gridAngle k j - gridAngle ζ j)) =
      -2 * ((1 - u) * ∑ j, Real.cos (gridAngle k j) +
        u * ∑ j, Real.cos (gridAngle k j - gridAngle ζ j)) := by ring
    _ = -2 * ∑ j, ((1 - u) * Real.cos (gridAngle k j) +
          u * Real.cos (gridAngle k j - gridAngle ζ j)) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = -2 * ∑ j, a j * Real.cos (gridAngle k j + φ j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [a, φ, interpolationAmplitude, interpolationPhase]
      exact interpolation_cos_identity u (gridAngle ζ j) (gridAngle k j)

private theorem interpolation_segment_eq {d L : ℕ} [NeZero L]
    (hT : TorusFourierStatement) (hL : 4 ≤ L) (u : ℝ)
    (k ζ : Torus d L) (E t : ℝ) (r : ℂ) :
    ((1 - u : ℝ) : ℂ) *
        ((dispersion (gridAngle k) : ℂ) - E - t * r) +
      (u : ℂ) * ((dispersion (gridAngle (ζ - k)) : ℂ) - E - t * r) =
    ((perturbedDispersion (interpolationAmplitude u ζ) (interpolationPhase u ζ)
        (gridAngle k) + 2 * (d : ℝ) -
        (E + 2 * (d : ℝ) + t * r.re) : ℝ) : ℂ) - (t * r.im) * Complex.I := by
  have hdisp := interpolated_dispersion hT hL u k ζ
  have hr : (t : ℂ) * r = ((t * r.re : ℝ) : ℂ) + (t * r.im : ℂ) * Complex.I := by
    calc
      (t : ℂ) * r = (t : ℂ) * ((r.re : ℂ) + (r.im : ℂ) * Complex.I) :=
        congrArg (fun z : ℂ => (t : ℂ) * z) (Complex.re_add_im r).symm
      _ = ((t * r.re : ℝ) : ℂ) + (t * r.im : ℂ) * Complex.I := by
        push_cast
        ring
  apply Complex.ext
  · simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, hr]
    linear_combination hdisp
  · simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, hr]
    ring

set_option maxHeartbeats 0 in
theorem smallSymbolW_of_helpers (hT : TorusFourierStatement)
    (hQ : PeriodicGridQuadratureStatement) (hB : BottomResolventStatement) :
    SmallSymbolWStatement := by
  intro d hd w hw a₀ B ha₀ haB
  have hBpos : 0 < B := lt_of_lt_of_le ha₀ haB
  let β₁ := min (w / 2) (1 / 800 : ℝ)
  have hβ₁pos : 0 < β₁ := by
    dsimp [β₁]
    exact lt_min (by positivity) (by norm_num)
  have hβ₁le : β₁ ≤ 3 / 200 := by
    dsimp [β₁]
    exact (min_le_right _ _).trans (by norm_num)
  obtain ⟨ε, Cb, cb, hε, hCb, hcb, hBottom⟩ :=
    hB d hd β₁ (3 / 200) hβ₁pos hβ₁le (by norm_num)
  obtain ⟨Cq, hCq, hQuad⟩ := grid_quadrature_apply hQ d
  let η := min (ε / 2) (1 / 2 : ℝ)
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε := by
    dsimp [η]
    exact (min_le_left _ _).trans (by linarith)
  have hηhalf : η ≤ 1 / 2 := by
    dsimp [η]
    exact min_le_right _ _
  have h800B : 0 < 800 * B := mul_pos (by norm_num) hBpos
  have h2B : 0 < 2 * B := mul_pos (by norm_num) hBpos
  let t₁ := min (min (min 1 (1 / (800 * B))) (w / (2 * B))) a₀
  have ht₁pos : 0 < t₁ := by
    dsimp [t₁]
    exact lt_min (lt_min (lt_min one_pos (one_div_pos.mpr h800B))
      (div_pos hw h2B)) ha₀
  have ht₁one : t₁ ≤ 1 := by
    dsimp [t₁]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht₁small : t₁ ≤ 1 / (800 * B) := by
    dsimp [t₁]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht₁window : t₁ ≤ w / (2 * B) := by
    dsimp [t₁]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have ht₁a₀ : t₁ ≤ a₀ := by
    dsimp [t₁]
    exact min_le_right _ _
  let α : ℝ := ((2 * Real.pi) ^ d)⁻¹
  let Kq : ℝ := Cq * (8 * (d : ℝ))
  let Kc : ℝ := 2 * α * Cb
  let Cbase : ℝ := Kc + Kq / Real.log 2
  let C : ℝ := Cbase + 1
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCbasepos : 0 < Cbase := by dsimp [Cbase, Kc, Kq]; positivity
  have hCpos : 0 < C := by dsimp [C]; linarith
  refine ⟨η, C, t₁, hηpos, hCpos, ht₁pos, ?_⟩
  intro t ht ht₁ L instL hL hEven hFine E hElo hEhi r hr ζ hζ
  have htone : t ≤ 1 := ht₁.trans ht₁one
  have httiny : t ≤ 1 / (800 * B) := ht₁.trans ht₁small
  have htwindow : t ≤ w / (2 * B) := ht₁.trans ht₁window
  have hta₀ : t ≤ a₀ := ht₁.trans ht₁a₀
  have htBsmall : t * B ≤ 1 / 800 := by
    calc
      t * B ≤ (1 / (800 * B)) * B := mul_le_mul_of_nonneg_right httiny hBpos.le
      _ = 1 / 800 := by field_simp [ne_of_gt hBpos]
  have htBwindow : t * B ≤ w / 2 := by
    calc
      t * B ≤ (w / (2 * B)) * B := mul_le_mul_of_nonneg_right htwindow hBpos.le
      _ = w / 2 := by field_simp [ne_of_gt hBpos]
  let β := E + 2 * (d : ℝ) + t * r.re
  let v := t * r.im
  have htrAbs : |t * r.re| ≤ 1 / 800 := by
    rw [abs_mul, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hr.1 ht.le).trans htBsmall
  have htrAbsWindow : |t * r.re| ≤ w / 2 := by
    rw [abs_mul, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hr.1 ht.le).trans htBwindow
  have htrLowerWindow : -(w / 2) ≤ t * r.re := (abs_le.mp htrAbsWindow).1
  have htrUpperSmall : t * r.re ≤ 1 / 800 := (abs_le.mp htrAbs).2
  have hβlo : β₁ ≤ β := by
    dsimp [β]
    have hwβ : w / 2 ≤ E + 2 * (d : ℝ) + t * r.re := by linarith
    exact (min_le_left _ _).trans hwβ
  have hβhi : β ≤ 3 / 200 := by
    dsimp [β]
    linarith
  have hβmem : β ∈ Set.Icc β₁ (3 / 200) := ⟨hβlo, hβhi⟩
  have hvpos : 0 < v := by dsimp [v]; exact mul_pos ht (lt_of_lt_of_le ha₀ hr.2.1)
  have hvle : v ≤ 1 := by
    dsimp [v]
    calc
      t * r.im ≤ t * B := mul_le_mul_of_nonneg_left hr.2.2 ht.le
      _ ≤ 1 / 800 := htBsmall
      _ ≤ 1 := by norm_num
  have ht2v : t ^ 2 ≤ v := by
    dsimp [v]
    calc
      t ^ 2 = t * t := by ring
      _ ≤ t * a₀ := mul_le_mul_of_nonneg_left hta₀ ht.le
      _ ≤ t * r.im := mul_le_mul_of_nonneg_left hr.2.1 ht.le
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) hL)
  have hLlower : (t ^ 8)⁻¹ ≤ (L : ℝ) := by
    simpa [inv_pow] using hFine
  have hLinv : (L : ℝ)⁻¹ ≤ t ^ 8 := by
    calc
      (L : ℝ)⁻¹ ≤ ((t ^ 8)⁻¹)⁻¹ := inv_anti₀ (by positivity) hLlower
      _ = t ^ 8 := by simp
  have hpow : t ^ 6 ≤ v ^ 3 := by
    calc
      t ^ 6 = (t ^ 2) ^ 3 := by ring
      _ ≤ v ^ 3 := by gcongr
  have hvinv : (v ^ 3)⁻¹ ≤ (t ^ 6)⁻¹ := inv_anti₀ (by positivity) hpow
  have herror : (8 * (d : ℝ) / v ^ 3) / (L : ℝ) ≤ 8 * (d : ℝ) := by
    calc
      (8 * (d : ℝ) / v ^ 3) / (L : ℝ) =
          (8 * (d : ℝ)) * ((v ^ 3)⁻¹ * (L : ℝ)⁻¹) := by ring
      _ ≤ (8 * (d : ℝ)) * ((t ^ 6)⁻¹ * t ^ 8) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hvinv hLinv (by positivity) (by positivity)) (by positivity)
      _ = 8 * (d : ℝ) * t ^ 2 := by field_simp [ne_of_gt ht]
      _ ≤ 8 * (d : ℝ) := by nlinarith [htone]
  have hInvV : v⁻¹ ≤ (t ^ 2)⁻¹ := inv_anti₀ (by positivity) ht2v
  have hlogRatio : 2 / v ≤ (2 / t) ^ 2 := by
    calc
      2 / v = 2 * v⁻¹ := by ring
      _ ≤ 2 * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hInvV (by norm_num)
      _ = 2 / t ^ 2 := by ring
      _ ≤ (2 / t) ^ 2 := by field_simp [ne_of_gt ht]; norm_num
  have hlog : Real.log (2 / v) ≤ 2 * Real.log (2 / t) := by
    calc
      Real.log (2 / v) ≤ Real.log ((2 / t) ^ 2) :=
        Real.log_le_log (by positivity) hlogRatio
      _ = 2 * Real.log (2 / t) := by rw [Real.log_pow]; norm_num
  have hlogLower : Real.log 2 ≤ Real.log (2 / t) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ ht]
    nlinarith [htone]
  let q : ℝ → Frequency d → ℂ := fun u x =>
    ((((perturbedDispersion (interpolationAmplitude u ζ) (interpolationPhase u ζ) x +
      2 * (d : ℝ) - β : ℝ) : ℂ) - v * Complex.I)⁻¹) ^ 2
  let denA : Torus d L → ℂ := fun k =>
    ((dispersion (gridAngle k) : ℝ) : ℂ) - (E : ℂ) - (t : ℂ) * r
  let denB : Torus d L → ℂ := fun k =>
    ((dispersion (gridAngle (ζ - k)) : ℝ) : ℂ) - (E : ℂ) - (t : ℂ) * r
  let seg : Torus d L → ℝ → ℂ := fun k u =>
    ((1 - u : ℝ) : ℂ) * denA k + (u : ℂ) * denB k
  have hImA : ∀ k, (denA k).im = -v := by
    intro k
    simp [denA, v, Complex.sub_im, Complex.mul_im]
  have hImB : ∀ k, (denB k).im = -v := by
    intro k
    simp [denB, v, Complex.sub_im, Complex.mul_im]
  have hImSeg : ∀ k u, (seg k u).im = -v := by
    intro k u
    simp [seg, Complex.add_im, Complex.mul_im, hImA, hImB]
    ring
  have hSegNe : ∀ k u, seg k u ≠ 0 := by
    intro k u hz
    have hi : (seg k u).im = 0 := by rw [hz]; simp
    rw [hImSeg k u] at hi
    linarith
  have hSegCont : ∀ k, Continuous (fun u : ℝ => seg k u) := by
    intro k
    dsimp [seg]
    fun_prop
  have hSegInt : ∀ k, IntervalIntegrable (fun u : ℝ => (seg k u)⁻¹ ^ 2) volume 0 1 := by
    intro k
    have hc : Continuous (fun u : ℝ => (seg k u)⁻¹ ^ 2) :=
      ((hSegCont k).inv₀ (hSegNe k)).pow 2
    exact hc.intervalIntegrable 0 1
  have hFeynman : ∀ k,
      (denA k)⁻¹ * (denB k)⁻¹ = ∫ u : ℝ in (0 : ℝ)..1, (seg k u)⁻¹ ^ 2 := by
    intro k
    have hAne : denA k ≠ 0 := by
      intro hz
      have hi : (denA k).im = 0 := by rw [hz]; simp
      rw [hImA k] at hi
      linarith
    have hBne : denB k ≠ 0 := by
      intro hz
      have hi : (denB k).im = 0 := by rw [hz]; simp
      rw [hImB k] at hi
      linarith
    have hAneg : (denA k).im < 0 := by rw [hImA k]; exact neg_lt_zero.mpr hvpos
    have hSame : (denB k).im = (denA k).im := by rw [hImB k, hImA k]
    have hrec := reciprocal_product_identity_proof (denA k) (denB k) hAneg hSame
    have halg : (denA k)⁻¹ * (denB k)⁻¹ = (denA k * denB k)⁻¹ := by
      field_simp [hAne, hBne]
    calc
      (denA k)⁻¹ * (denB k)⁻¹ = (denA k * denB k)⁻¹ := halg
      _ = ∫ u : ℝ in (0 : ℝ)..1, (seg k u)⁻¹ ^ 2 := hrec
  have hGridFeynman :
      gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k)) =
        ∫ u : ℝ in (0 : ℝ)..1, gridAvg (fun k : Torus d L => (seg k u)⁻¹ ^ 2) := by
    unfold gridAvg
    calc
      (Fintype.card (Torus d L) : ℂ)⁻¹ *
          ∑ k, gridResolvent E t r k * gridResolvent E t r (ζ - k) =
        (Fintype.card (Torus d L) : ℂ)⁻¹ * ∑ k, (denA k)⁻¹ * (denB k)⁻¹ := by
          congr 1
      _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
          ∑ k, ∫ u : ℝ in (0 : ℝ)..1, (seg k u)⁻¹ ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          exact hFeynman k
      _ = ∫ u : ℝ in (0 : ℝ)..1,
          (Fintype.card (Torus d L) : ℂ)⁻¹ * ∑ k, (seg k u)⁻¹ ^ 2 := by
          symm
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_finsetSum (fun k hk => hSegInt k)]
  have hSegQ : ∀ u k,
      seg k u = (((perturbedDispersion (interpolationAmplitude u ζ)
        (interpolationPhase u ζ) (gridAngle k) + 2 * (d : ℝ) - β : ℝ) : ℂ) -
        v * Complex.I) := by
    intro u k
    simpa [seg, denA, denB, β, v] using interpolation_segment_eq hT hL u k ζ E t r
  have hGridQ :
      gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k)) =
        ∫ u : ℝ in (0 : ℝ)..1, gridAvg (fun k : Torus d L => q u (gridAngle k)) := by
    rw [hGridFeynman]
    apply intervalIntegral.integral_congr
    intro u hu
    unfold gridAvg
    apply congrArg (fun z : ℂ => (Fintype.card (Torus d L) : ℂ)⁻¹ * z)
    apply Finset.sum_congr rfl
    intro k hk
    change (seg k u)⁻¹ ^ 2 = q u (gridAngle k)
    rw [hSegQ u k]
  have hAmpEta : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ j, |interpolationAmplitude u ζ j - 1| ≤ η := by
    intro u hu j
    dsimp [interpolationAmplitude]
    exact (interpolation_amplitude_close u (gridAngle ζ j) hu).trans (hζ j)
  have hPerU : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖gridAvg (fun k : Torus d L => q u (gridAngle k))‖ ≤ Cbase * Real.log (2 / t) := by
    intro u hu
    let a := interpolationAmplitude u ζ
    let φ := interpolationPhase u ζ
    have haE : ∀ j, |a j - 1| ≤ ε := by
      intro j
      dsimp [a]
      exact (hAmpEta u hu j).trans hηε
    have hsumA : ∑ j : Fin d, |a j| ≤ 2 * (d : ℝ) := by
      calc
        ∑ j : Fin d, |a j| ≤ ∑ _j : Fin d, (2 : ℝ) :=
          Finset.sum_le_sum fun j hj => by
            have hjθ := hAmpEta u hu j
            have habs : |a j| ≤ |a j - 1| + 1 := by
              calc
                |a j| = |(a j - 1) + 1| := by congr 1 <;> ring
                _ ≤ |a j - 1| + |(1 : ℝ)| := abs_add_le _ _
                _ = |a j - 1| + 1 := by simp
            linarith [habs, hjθ, hηhalf]
        _ = 2 * (d : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    let g : Frequency d → ℝ := fun x => perturbedDispersion a φ x + 2 * (d : ℝ) - β
    have hDispLip : ∀ x y, |g x - g y| ≤ 4 * (d : ℝ) * dist x y := by
      intro x y
      have hp := abs_perturbedDispersion_sub_le a φ x y
      have hCoeff : 2 * (∑ j : Fin d, |a j|) ≤ 4 * (d : ℝ) := by nlinarith [hsumA]
      calc
        |g x - g y| = |perturbedDispersion a φ x - perturbedDispersion a φ y| := by
          congr 1
          dsimp [g]
          ring
        _ ≤ 2 * (∑ j : Fin d, |a j|) * dist x y := hp
        _ ≤ 4 * (d : ℝ) * dist x y :=
          mul_le_mul_of_nonneg_right hCoeff (dist_nonneg)
    let cGrid : ℝ := 2 * (4 * (d : ℝ)) / v ^ 3
    have hcGrid : 0 ≤ cGrid := by dsimp [cGrid]; positivity
    have hSqLip : ∀ x y,
        dist (q u x) (q u y) ≤ cGrid * dist x y := by
      intro x y
      have hz : 0 < ((v : ℂ) * Complex.I).im := by simp [hvpos]
      have hs := resolvent_sq_dist_le g (4 * (d : ℝ)) hDispLip hz x y
      simpa [q, g, a, φ, cGrid] using hs
    have hQuadU := hQuad L hL hEven (fun x => q u x) cGrid hcGrid hSqLip
    have haBottom : ∀ j, |a j - 1| ≤ ε := haE
    rcases hBottom β hβmem v hvpos hvle with ⟨_, _, _, hPert⟩
    have hContU : ‖∫ k in torusCube d, q u k‖ ≤ Cb * Real.log (2 / v) := by
      simpa [q, a, φ, g] using hPert a φ haBottom
    have hQuadErr : Cq * cGrid / (L : ℝ) ≤ Kq := by
      dsimp [cGrid, Kq]
      calc
        Cq * (2 * (4 * (d : ℝ)) / v ^ 3) / (L : ℝ) =
            Cq * ((8 * (d : ℝ) / v ^ 3) / (L : ℝ)) := by ring
        _ ≤ Cq * (8 * (d : ℝ)) := mul_le_mul_of_nonneg_left herror hCq.le
    have hQuadU' :
        ‖gridAvg (fun k : Torus d L => q u (gridAngle k)) - (α : ℂ) *
          (∫ k in torusCube d, q u k)‖ ≤ Cq * cGrid / (L : ℝ) := by
      simpa [α] using hQuadU
    have hαnorm : ∀ z : ℂ, ‖(α : ℂ) * z‖ = α * ‖z‖ := by
      intro z
      rw [norm_mul]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hαpos]
    have hJbound : ‖(α : ℂ) * (∫ k in torusCube d, q u k)‖ ≤
        α * (Cb * Real.log (2 / v)) := by
      rw [hαnorm]
      exact mul_le_mul_of_nonneg_left hContU hαpos.le
    have hContLog : α * (Cb * Real.log (2 / v)) ≤ Kc * Real.log (2 / t) := by
      calc
        α * (Cb * Real.log (2 / v)) = (α * Cb) * Real.log (2 / v) := by ring
        _ ≤ (α * Cb) * (2 * Real.log (2 / t)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = Kc * Real.log (2 / t) := by dsimp [Kc]; ring
    have hKqLog : Kq ≤ (Kq / Real.log 2) * Real.log (2 / t) := by
      calc
        Kq = (Kq / Real.log 2) * Real.log 2 := by field_simp [ne_of_gt hlog2pos]
        _ ≤ (Kq / Real.log 2) * Real.log (2 / t) :=
          mul_le_mul_of_nonneg_left hlogLower (by positivity)
    calc
      ‖gridAvg (fun k : Torus d L => q u (gridAngle k))‖ =
          ‖(gridAvg (fun k : Torus d L => q u (gridAngle k)) -
            (α : ℂ) * (∫ k in torusCube d, q u k)) +
            (α : ℂ) * (∫ k in torusCube d, q u k)‖ := by congr 1 <;> abel
      _ ≤ ‖gridAvg (fun k : Torus d L => q u (gridAngle k)) -
            (α : ℂ) * (∫ k in torusCube d, q u k)‖ +
            ‖(α : ℂ) * (∫ k in torusCube d, q u k)‖ := norm_add_le _ _
      _ ≤ Kq + Kc * Real.log (2 / t) := by
        calc
          ‖gridAvg (fun k : Torus d L => q u (gridAngle k)) -
              (α : ℂ) * (∫ k in torusCube d, q u k)‖ +
              ‖(α : ℂ) * (∫ k in torusCube d, q u k)‖ ≤
              Cq * cGrid / (L : ℝ) + α * (Cb * Real.log (2 / v)) :=
            add_le_add hQuadU' hJbound
          _ = α * (Cb * Real.log (2 / v)) + Cq * cGrid / (L : ℝ) := by ring
          _ ≤ Kc * Real.log (2 / t) + Cq * cGrid / (L : ℝ) :=
            add_le_add_left hContLog _
          _ = Cq * cGrid / (L : ℝ) + Kc * Real.log (2 / t) := by ring
          _ ≤ Kq + Kc * Real.log (2 / t) := by
            calc
              Cq * cGrid / (L : ℝ) + Kc * Real.log (2 / t) =
                  Kc * Real.log (2 / t) + Cq * cGrid / (L : ℝ) := by ring
              _ ≤ Kc * Real.log (2 / t) + Kq := add_le_add_right hQuadErr _
              _ = Kq + Kc * Real.log (2 / t) := by ring
      _ ≤ Cbase * Real.log (2 / t) := by
        dsimp [Cbase]
        nlinarith [hKqLog]
  have hlognonneg : 0 ≤ Real.log (2 / t) := by
    exact le_trans (le_of_lt hlog2pos) hlogLower
  calc
    ‖gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k))‖ =
        ‖∫ u : ℝ in (0 : ℝ)..1, gridAvg (fun k : Torus d L => q u (gridAngle k))‖ :=
      congrArg norm hGridQ
    _ ≤ Cbase * Real.log (2 / t) := by
      calc
        ‖∫ u : ℝ in (0 : ℝ)..1, gridAvg (fun k : Torus d L => q u (gridAngle k))‖ ≤
            (Cbase * Real.log (2 / t)) * |1 - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
            have h01 : (0 : ℝ) ≤ 1 := by norm_num
            have hu0 : 0 < u := by simpa [min_eq_left h01] using hu.1
            have hu1 : u ≤ 1 := by simpa [max_eq_right h01] using hu.2
            have hu' : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu0.le, hu1⟩
            exact hPerU u hu')
        _ = Cbase * Real.log (2 / t) := by norm_num
    _ ≤ C * Real.log (2 / t) := by
      dsimp [C]
      nlinarith [hlognonneg]

theorem smallSymbol_of_helpers (hT : TorusFourierStatement)
    (hQ : PeriodicGridQuadratureStatement) (hB : BottomResolventStatement) :
    SmallSymbolStatement :=
  smallSymbol_of_W (smallSymbolW_of_helpers hT hQ hB)

end AndersonAC.S3
