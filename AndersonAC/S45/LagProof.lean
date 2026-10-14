import AndersonAC.S45.LagSupport
import AndersonAC.S45.JFourthProof

set_option maxHeartbeats 4000000

/-!
Proof of the transformed lag increment bound (Lemma 4.6,
`refs/tex/04-sweep.tex:791-1092`).

The finite-array estimates are in `LagSupport`; this module joins them into
the pathwise square-array bound and the signed conditional-mean bound. No
section statement module is imported here.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

namespace LagFinal

/-- Constant of the scaled forcing array bound. -/
def forcingConst (G A : ℝ) : ℝ :=
  2 * (G + A * 2) ^ 2 +
    2 * (4 * (2 * G) ^ 2 * (2 * A ^ 2) + 2 * (G ^ 2 + 2) ^ 2 * A ^ 2)

/-- Constant of the square-array contraction of the `J` correction. -/
def contractConst (G A : ℝ) : ℝ :=
  2 * (2 * G) ^ 2 * A ^ 2 + 2 * (G ^ 2 + 2) ^ 2 * A ^ 2

/-- Constant of the absolute-sum bound of the `J` correction. -/
def sumConst (G A : ℝ) : ℝ :=
  2 * (2 * G) ^ 2 * A ^ 3 + 2 * (G ^ 2 + 2) ^ 2 * A ^ 4

lemma sqrt_sqrt_sq {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t :=
  Real.sq_sqrt (Real.sqrt_nonneg t)

/-- Exponent bookkeeping for the scaled forcing. -/
lemma forcing_exponents {t A G : ℝ} (ht : 0 < t) (htle : t ≤ 1) (hA : 0 ≤ A)
    (hG : 0 ≤ G) :
    2 * ((G + A * 2) ^ 2 / t * rowCap t) +
        2 * (4 * (2 * G) ^ 2 *
            (A * power t (delta / 2) * A * power t beta ^ 2 +
              A ^ 2 * power t beta ^ 2 * rowCap t) +
          2 * (G ^ 2 + 2) ^ 2 * A ^ 2 * power t beta ^ 2 * rowCap t) ≤
      forcingConst G A * power t delta := by
  have hU2 : power t beta ^ 2 = power t (2 * beta) := LagSupport.lag_power_sq_eq ht
  have hHdiv : rowCap t / t = power t delta := by
    change t ^ (1 + delta) / t = t ^ delta
    rw [show (1 + delta) = delta + 1 by ring, Real.rpow_add ht, Real.rpow_one]
    field_simp
  have hpd : 0 ≤ power t delta := Real.rpow_nonneg ht.le _
  have h1 : power t (delta / 2) * power t (2 * beta) ≤ power t delta := by
    rw [LagSupport.lag_power_mul_eq ht]
    exact Real.rpow_le_rpow_of_exponent_ge ht htle (by norm_num [delta, beta])
  have h2 : power t (2 * beta) * rowCap t ≤ power t delta := by
    unfold rowCap
    rw [LagSupport.lag_power_mul_eq ht]
    exact Real.rpow_le_rpow_of_exponent_ge ht htle (by norm_num [delta, beta])
  have hterm1 : A * power t (delta / 2) * A * power t beta ^ 2 ≤ A ^ 2 * power t delta := by
    rw [hU2]
    calc A * power t (delta / 2) * A * power t (2 * beta)
        = A ^ 2 * (power t (delta / 2) * power t (2 * beta)) := by ring
      _ ≤ A ^ 2 * power t delta := mul_le_mul_of_nonneg_left h1 (sq_nonneg A)
  have hterm2 : A ^ 2 * power t beta ^ 2 * rowCap t ≤ A ^ 2 * power t delta := by
    rw [hU2]
    calc A ^ 2 * power t (2 * beta) * rowCap t
        = A ^ 2 * (power t (2 * beta) * rowCap t) := by ring
      _ ≤ A ^ 2 * power t delta := mul_le_mul_of_nonneg_left h2 (sq_nonneg A)
  have hdirect : (G + A * 2) ^ 2 / t * rowCap t = (G + A * 2) ^ 2 * power t delta := by
    rw [← hHdiv]; ring
  rw [hdirect]
  have hc1 : 0 ≤ 4 * (2 * G) ^ 2 := by positivity
  have hc2 : 0 ≤ 2 * (G ^ 2 + 2) ^ 2 := by positivity
  have hterm3 : 2 * (G ^ 2 + 2) ^ 2 * A ^ 2 * power t beta ^ 2 * rowCap t ≤
      2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * power t delta) := by
    calc 2 * (G ^ 2 + 2) ^ 2 * A ^ 2 * power t beta ^ 2 * rowCap t
        = 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * power t beta ^ 2 * rowCap t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm2 hc2
  have hsum := add_le_add hterm1 hterm2
  have hmid := mul_le_mul_of_nonneg_left hsum hc1
  unfold forcingConst
  nlinarith [hmid, hterm3, hpd]


lemma rowCap_le_sqrt {t : ℝ} (ht : 0 < t) (htle : t ≤ 1) : rowCap t ≤ Real.sqrt t := by
  have h1 : rowCap t ≤ t := by
    change t ^ (1 + delta) ≤ t
    calc t ^ (1 + delta) ≤ t ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge ht htle (by norm_num [delta])
      _ = t := Real.rpow_one t
  refine h1.trans ?_
  calc t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht.le).symm
    _ ≤ Real.sqrt t * 1 :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr htle) (Real.sqrt_nonneg _)
    _ = Real.sqrt t := mul_one _

/-- Deterministic core of Lemma 4.6: forcing array, square-array bound for
the increment, and the absolute-sum bound of the nonlinear remainder. -/
theorem lag_core {P : Type*} [Fintype P] [DecidableEq P]
    (C A G L t : ℝ) (s : State P) (Λplus Wstar : Form P) (S : Finset P) (z : P → ℝ)
    (hC : 1 ≤ C) (hA : 0 < A) (hG : 0 ≤ G) (hL : 0 ≤ L) (ht : 0 < t) (htle : t ≤ 1)
    (hpre : Prestate t C Λplus Wstar s)
    (hProw : rowNorm (s.P t) ≤ L)
    (hcaps :
      (∀ i, ‖s.rawLag i‖ ≤ A * power t beta ∧
        |s.q i - s.p i| ≤ A * power t beta ∧
        (∑ j, s.F t i j) ≤ A ∧ ‖s.h t i i‖ ≤ A * Real.sqrt t) ∧
      (∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤ A * power t (delta / 2)))
    (hγ : ∀ x (ζ : ℝ), |ζ| ≤ C * Real.sqrt t →
      ‖gamma t s x ζ‖ ≤ G ∧ 1 + ((ζ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hz : ∀ x ∈ S, |z x| ≤ C * Real.sqrt t)
    (hpert : L * (2 * G * Real.sqrt (Real.sqrt t) * A + (G ^ 2 + 2) * Real.sqrt t * A) < 1)
    (hsmall : 2 * L ^ 2 * (contractConst G A * Real.sqrt t) ≤ 1 / 2) :
    (∀ j, ∑ x ∈ S, ‖LagSupport.lagRawForcingScaled t s z j x‖ ^ 2 ≤
        forcingConst G A * power t delta) ∧
    arrayA2sq S (fun i x => lagInc t s x (z x) i) ≤
        4 * L ^ 2 * (forcingConst G A * power t delta) ∧
    (∀ i, (∑ x ∈ S, ‖lagInc t s x (z x) i -
        (pad (survivors x) (restrict (s.P t) (survivors x)) *ᵥ
          fun j => LagSupport.lagRawForcingScaled t s z j x) i‖) ^ 2 ≤
        L ^ 2 * (sumConst G A * (4 * L ^ 2 * (forcingConst G A * power t delta)))) := by
  classical
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr htle
  let zp : P → ℝ := fun x => if x ∈ S then z x else 0
  have hzp : ∀ x, |zp x| ≤ C * Real.sqrt t := by
    intro x
    by_cases hx : x ∈ S
    · simpa [zp, hx] using hz x hx
    · simp only [zp, hx, if_false, abs_zero]
      positivity
  have hzpS : ∀ x ∈ S, zp x = z x := fun x hx => by simp [zp, hx]
  have hgammaP : ∀ x, ‖gamma t s x (zp x)‖ ≤ G := fun x => (hγ x _ (hzp x)).1
  have hgammaS : ∀ x ∈ S, ‖gamma t s x (z x)‖ ≤ G := fun x hx => (hγ x _ (hz x hx)).1
  have hdenS : ∀ x ∈ S, 1 + ((z x : ℂ) + t * s.r x) * s.g x x ≠ 0 :=
    fun x hx => (hγ x _ (hz x hx)).2
  have hpivot := LagSupport.lag_pivot_inverse_bound s t hpre.K_cap
  have hrow : ∀ i, (∑ j, ‖s.h t i j‖ ^ 2) ≤ A := fun i => by
    simpa [State.F, entryAbsSquare] using (hcaps.1 i).2.2.1
  have hfour : ∀ i, (∑ j, ‖s.h t i j‖ ^ 4) ≤ rowCap t := fun i => by
    simpa [State.fourthRow] using hpre.row_cap i
  have hH : rowCap t ≤ Real.sqrt t := rowCap_le_sqrt ht htle
  have hmax2 : ∀ i j, ‖s.h t i j‖ ^ 2 ≤ Real.sqrt t := by
    intro i j
    have hsq : (‖s.h t i j‖ ^ 2) ^ 2 ≤ t := by
      calc (‖s.h t i j‖ ^ 2) ^ 2 = ‖s.h t i j‖ ^ 4 := by ring
        _ ≤ ∑ k, ‖s.h t i k‖ ^ 4 :=
          Finset.single_le_sum (f := fun k => ‖s.h t i k‖ ^ 4)
            (fun k _ => by positivity) (Finset.mem_univ j)
        _ ≤ rowCap t := hfour i
        _ ≤ t := by
          change t ^ (1 + delta) ≤ t
          calc t ^ (1 + delta) ≤ t ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_ge ht htle (by norm_num [delta])
            _ = t := Real.rpow_one t
    exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  have hmax : ∀ i j, ‖s.h t i j‖ ≤ Real.sqrt (Real.sqrt t) := by
    intro i j
    exact (le_abs_self _).trans (Real.abs_le_sqrt (hmax2 i j))
  have hdiag : ∀ i, ‖s.h t i i‖ ≤ A := fun i =>
    ((hcaps.1 i).2.2.2).trans (mul_le_of_le_one_right hA.le hsqrt1)
  have hβ1 : power t beta ≤ 1 := Real.rpow_le_one ht.le htle (by norm_num [beta, delta])
  have hZ : ∀ x, ‖s.z t x‖ ≤ A * Real.sqrt t := by
    intro x
    have hnorm : ‖s.z t x‖ = Real.sqrt t * ‖s.rawLag x‖ := by
      simp [State.z, Complex.norm_real, abs_of_nonneg hsqrt0]
    rw [hnorm]
    calc Real.sqrt t * ‖s.rawLag x‖ ≤ Real.sqrt t * (A * power t beta) :=
          mul_le_mul_of_nonneg_left (hcaps.1 x).1 hsqrt0
      _ ≤ Real.sqrt t * A :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hA.le hβ1) hsqrt0
      _ = A * Real.sqrt t := by ring
  have hFabs := LagSupport.lagForcingScaled_array_sq_le S t s zp A (rowCap t)
    (A * power t (delta / 2)) A (power t beta) G 2 A
    ht htle hA.le (Real.rpow_nonneg ht.le _) (mul_nonneg hA.le (Real.rpow_nonneg ht.le _)) hA.le
    (Real.rpow_nonneg ht.le _) hG (by norm_num) hA.le
    hrow hfour hcaps.2 hdiag hpre.lag_cap hgammaP (fun x => (hpivot x).2) hZ
  have hF : ∀ j, ∑ x ∈ S, ‖LagSupport.lagRawForcingScaled t s z j x‖ ^ 2 ≤
      forcingConst G A * power t delta := by
    intro j
    have hsame : ∑ x ∈ S, ‖LagSupport.lagRawForcingScaled t s z j x‖ ^ 2 =
        ∑ x ∈ S, ‖LagSupport.lagForcingScaled t s zp j x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← LagSupport.lagRawForcingScaled_eq]
      simp only [LagSupport.lagRawForcingScaled, LagSupport.lagDirectScaled, hzpS x hx]
    rw [hsame]
    exact (hFabs j).trans (forcing_exponents ht htle hA.le hG)
  have hpert' : L * (2 * G * Real.sqrt (Real.sqrt t) * A +
      (G ^ 2 + 2) * Real.sqrt (Real.sqrt t) ^ 2 * A) < 1 := by
    rw [sqrt_sqrt_sq ht.le]; exact hpert
  have hlocalCaps := LagSupport.lag_poststate_caps_of_prestate C t s Λplus Wstar S z A
    (Real.sqrt (Real.sqrt t)) G L hC ht hpre hrow hA.le hmax (Real.sqrt_nonneg _)
    hgammaS hdenS hG hProw hL hpert'
  have hlocal : ∀ x ∈ S, (1 - s.K t x x ≠ 0) ∧
      (1 + ((z x : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧
      IsUnit (1 - (deleteState t s x (z x)).K t) := by
    intro x hx
    obtain ⟨ha, _, hnew⟩ := hlocalCaps x hx
    exact ⟨ha, hdenS x hx, hnew⟩
  have hrec0 := LagSupport.lag_exact_recurrence_full S t s z ht hpre.symmetric
    hpre.invertible hlocal
  set Y : P → P → ℂ := fun i x => lagInc t s x (z x) i with hYdef
  set Mx : P → CMat P := fun x => pad (survivors x) (restrict (s.P t) (survivors x))
    with hMxdef
  set F : P → P → ℂ := fun j x => LagSupport.lagRawForcingScaled t s z j x with hFdef
  set V : P → P → ℂ := fun j x => (Jinc t s x (z x) *ᵥ fun k => Y k x) j with hVdef
  have hrec : ∀ i x, x ∈ S → Y i x =
      (Mx x *ᵥ (fun j => F j x + (Jinc t s x (z x) *ᵥ fun k => Y k x) j)) i := by
    intro i x hx
    exact hrec0 x hx i
  have hMentry : ∀ x i j, ‖Mx x i j‖ ≤ ‖s.P t i j‖ := by
    intro x i j
    by_cases hi : i ∈ survivors x <;> by_cases hj : j ∈ survivors x <;>
      simp [Mx, pad, restrict, hi, hj]
  have hMrow : ∀ i, ∑ j, ‖s.P t i j‖ ≤ L := fun i =>
    (LagSupport.rowSum_le_rowNorm (s.P t) i).trans hProw
  let c : P → ℂ := fun x => -2 * gamma t s x (zp x)
  let d : P → ℂ := fun x => gamma t s x (zp x) ^ 2 - (1 - s.K t x x)⁻¹
  have hc : ∀ x, ‖c x‖ ≤ 2 * G := by
    intro x
    have h := hgammaP x
    simp only [c, norm_mul, norm_neg]
    norm_num
    exact h
  have hd : ∀ x, ‖d x‖ ≤ G ^ 2 + 2 := by
    intro x
    calc ‖d x‖ ≤ ‖gamma t s x (zp x) ^ 2‖ + ‖(1 - s.K t x x)⁻¹‖ := norm_sub_le _ _
      _ ≤ G ^ 2 + 2 := by
        rw [norm_pow]
        exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hgammaP x) 2) (hpivot x).2
  have hJeq : ∀ x ∈ S, ∀ i (W : P → P → ℂ),
      (Jinc t s x (z x) *ᵥ fun j => W j x) i = LagSupport.lagJApply (s.h t) c d W i x := by
    intro x hx i W
    rw [LagSupport.lagJApply_eq_Jinc]
    simp only [LagSupport.lagJApply, LagSupport.lagJLinear, LagSupport.lagJQuadratic, c, d,
      hzpS x hx]
  have hYrow : ∀ j, ∑ x ∈ S, ‖Y j x‖ ^ 2 ≤ arrayA2sq S Y := fun j =>
    LagSupport.arrayA2sq_row_le S Y _ (norm_nonneg _) le_rfl j
  have hJsq : ∀ i, ∑ x ∈ S, ‖(Jinc t s x (z x) *ᵥ fun k => Y k x) i‖ ^ 2 ≤
      contractConst G A * Real.sqrt t * arrayA2sq S Y := by
    intro i
    have h := LagSupport.lagJApply_array_sq_le S (s.h t) c d Y A (rowCap t) (Real.sqrt t)
      (arrayA2sq S Y) (2 * G) (G ^ 2 + 2)
      hA.le hsqrt0 (norm_nonneg _) (by positivity) (by positivity) hrow hfour hmax2 hc hd
      hYrow i
    have hHc : 2 * (G ^ 2 + 2) ^ 2 * A ^ 2 * rowCap t ≤
        2 * (G ^ 2 + 2) ^ 2 * A ^ 2 * Real.sqrt t :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    calc ∑ x ∈ S, ‖(Jinc t s x (z x) *ᵥ fun k => Y k x) i‖ ^ 2
        = ∑ x ∈ S, ‖LagSupport.lagJApply (s.h t) c d Y i x‖ ^ 2 :=
          Finset.sum_congr rfl (fun x hx => by rw [hJeq x hx i Y])
      _ ≤ (2 * (2 * G) ^ 2 * Real.sqrt t * A ^ 2 +
            2 * (G ^ 2 + 2) ^ 2 * A ^ 2 * rowCap t) * arrayA2sq S Y := h
      _ ≤ contractConst G A * Real.sqrt t * arrayA2sq S Y := by
        rw [show contractConst G A * Real.sqrt t * arrayA2sq S Y =
          (2 * (2 * G) ^ 2 * Real.sqrt t * A ^ 2 +
            2 * (G ^ 2 + 2) ^ 2 * A ^ 2 * Real.sqrt t) * arrayA2sq S Y by
              unfold contractConst; ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hA2 : arrayA2sq S Y ≤ 4 * L ^ 2 * (forcingConst G A * power t delta) :=
    LagSupport.lag_recurrence_array_absorb S Mx (s.P t) (fun x => Jinc t s x (z x)) F Y L
      (contractConst G A * Real.sqrt t) (forcingConst G A * power t delta)
      hL (by unfold contractConst; positivity)
      (mul_nonneg (by unfold forcingConst; positivity) (Real.rpow_nonneg ht.le _))
      hsmall hrec hMentry hMrow hF hJsq
  have hB0 : 0 ≤ sumConst G A * (4 * L ^ 2 * (forcingConst G A * power t delta)) :=
    mul_nonneg (by unfold sumConst; positivity)
      (mul_nonneg (by positivity)
        (mul_nonneg (by unfold forcingConst; positivity) (Real.rpow_nonneg ht.le _)))
  have hJsum : ∀ j, (∑ x ∈ S, ‖V j x‖) ^ 2 ≤
      sumConst G A * (4 * L ^ 2 * (forcingConst G A * power t delta)) := by
    intro j
    have h := LagSupport.lagJApply_array_sum_sq_le S (s.h t) c d Y A (arrayA2sq S Y)
      (2 * G) (G ^ 2 + 2) hA.le (norm_nonneg _) (by positivity) (by positivity) hrow hc hd
      hYrow j
    have heq : ∑ x ∈ S, ‖V j x‖ = ∑ x ∈ S, ‖LagSupport.lagJApply (s.h t) c d Y j x‖ :=
      Finset.sum_congr rfl (fun x hx => by rw [hVdef]; exact congrArg norm (hJeq x hx j Y))
    rw [heq]
    calc _ ≤ (2 * (2 * G) ^ 2 * A ^ 3 + 2 * (G ^ 2 + 2) ^ 2 * A ^ 4) * arrayA2sq S Y := h
      _ ≤ sumConst G A * (4 * L ^ 2 * (forcingConst G A * power t delta)) :=
        mul_le_mul_of_nonneg_left hA2 (by positivity)
  refine ⟨hF, hA2, ?_⟩
  intro i
  set B := sumConst G A * (4 * L ^ 2 * (forcingConst G A * power t delta)) with hBdef
  have hpt : ∀ x ∈ S, ‖Y i x - (Mx x *ᵥ fun j => F j x) i‖ ≤
      ∑ j, ‖s.P t i j‖ * ‖V j x‖ := by
    intro x hx
    have hsplit : (Mx x *ᵥ (fun j => F j x + (Jinc t s x (z x) *ᵥ fun k => Y k x) j)) i =
        (Mx x *ᵥ fun j => F j x) i + ∑ j, Mx x i j * V j x := by
      simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, hVdef]
    rw [hrec i x hx, hsplit, add_sub_cancel_left]
    calc ‖∑ j, Mx x i j * V j x‖ ≤ ∑ j, ‖Mx x i j * V j x‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖s.P t i j‖ * ‖V j x‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hMentry x i j) (norm_nonneg _)
  have hsumle : ∑ x ∈ S, ‖Y i x - (Mx x *ᵥ fun j => F j x) i‖ ≤
      ∑ j, ‖s.P t i j‖ * ∑ x ∈ S, ‖V j x‖ := by
    calc _ ≤ ∑ x ∈ S, ∑ j, ‖s.P t i j‖ * ‖V j x‖ := Finset.sum_le_sum hpt
      _ = ∑ j, ∑ x ∈ S, ‖s.P t i j‖ * ‖V j x‖ := Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum]
  have hlhs0 : 0 ≤ ∑ x ∈ S, ‖Y i x - (Mx x *ᵥ fun j => F j x) i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcs := LagSupport.weighted_sum_sq_le Finset.univ (fun j => ‖s.P t i j‖)
    (fun j => ∑ x ∈ S, ‖V j x‖) (fun _ _ => norm_nonneg _)
  have hw0 : 0 ≤ ∑ j, ‖s.P t i j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc (∑ x ∈ S, ‖Y i x - (Mx x *ᵥ fun j => F j x) i‖) ^ 2
      ≤ (∑ j, ‖s.P t i j‖ * ∑ x ∈ S, ‖V j x‖) ^ 2 := pow_le_pow_left₀ hlhs0 hsumle 2
    _ ≤ (∑ j, ‖s.P t i j‖) * ∑ j, ‖s.P t i j‖ * (∑ x ∈ S, ‖V j x‖) ^ 2 := hcs
    _ ≤ L * (L * B) := by
      apply mul_le_mul (hMrow i) _
        (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) hL
      calc ∑ j, ‖s.P t i j‖ * (∑ x ∈ S, ‖V j x‖) ^ 2 ≤ ∑ j, ‖s.P t i j‖ * B :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hJsum j) (norm_nonneg _)
        _ = (∑ j, ‖s.P t i j‖) * B := by rw [Finset.sum_mul]
        _ ≤ L * B := mul_le_mul_of_nonneg_right (hMrow i) hB0
    _ = L ^ 2 * B := by ring

/-- Linear correction sum of the forcing, with the deleted index omitted. -/
def sL {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P) (j x : P) : ℂ :=
  ∑ k, if k = x then 0 else s.h t j k * s.h t x k * s.lag t k

/-- Quadratic correction sum of the forcing, with the deleted index omitted. -/
def sQ {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P) (x : P) : ℂ :=
  ∑ k, if k = x then 0 else s.h t x k ^ 2 * s.lag t k

/-- Coefficient of `γ` in the scaled forcing. -/
def E1 {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P) (j x : P) : ℂ :=
  if j = x then 0 else
    -(s.K t j x / (Real.sqrt t : ℂ)) + (-2) * s.h t j x * sL t s j x

/-- Coefficient of `γ² - (1 - K_xx)⁻¹` in the scaled forcing. -/
def E2 {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P) (j x : P) : ℂ :=
  if j = x then 0 else s.h t j x ^ 2 * sQ t s x

/-- Deterministic part of the scaled forcing. -/
def E0 {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P) (j x : P) : ℂ :=
  if j = x then 0 else
    -(s.z t x * (1 - s.K t x x)⁻¹ / (Real.sqrt t : ℂ)) * s.K t j x

/-- The scaled forcing is affine in `γ` and `γ² - (1 - K_xx)⁻¹`. -/
lemma forcing_affine {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (z : P → ℝ) (j x : P) :
    LagSupport.lagRawForcingScaled t s z j x =
      gamma t s x (z x) * E1 t s j x +
        (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹) * E2 t s j x + E0 t s j x := by
  rw [LagSupport.lagRawForcingScaled_eq]
  unfold LagSupport.lagForcingScaled LagSupport.lagDirectScaled LagSupport.lagJApply
    LagSupport.lagJLinear LagSupport.lagJQuadratic E1 E2 E0 sL sQ
  by_cases hjx : j = x
  · simp [hjx]
  · simp only [hjx, if_false]
    ring

lemma norm_K_eq_F {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P) (a b : P) :
    ‖s.K t a b‖ = s.F t a b := by
  simp [State.K, State.F, entrywiseSquare, AndersonAC.Blueprint.entrywiseSquare,
    entryAbsSquare, norm_pow]

lemma F_eq_sq {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P) (a b : P) :
    s.F t a b = ‖s.h t a b‖ ^ 2 := rfl

/-- The signed sum of the conditional forcing means (`M_0` in the manuscript). -/
lemma mean_forcing_bound {P : Type*} [Fintype P] [DecidableEq P]
    (C A M Kz Kν t : ℝ) (s : State P) (T : Finset P) (μ ν : P → ℂ)
    (ht : 0 < t) (htle : t ≤ 1) (hC : 0 < C) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hKz : 0 ≤ Kz) (hKν : 0 ≤ Kν)
    (hsym : s.g.IsSymm) (hward : s.ward t) (hp : ∀ j, 1 / C ≤ s.p j)
    (hrowF : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hdiag : ∀ i, ‖s.h t i i‖ ≤ A * Real.sqrt t)
    (hlag : ∀ i, ‖s.lag t i‖ ≤ power t beta)
    (hμz : ∀ x ∈ T, ‖μ x + s.z t x * (1 - s.K t x x)⁻¹‖ ≤ Kz * t)
    (hμ : ∀ x ∈ T, ‖μ x‖ ≤ M * Real.sqrt t * power t beta)
    (hν : ∀ x ∈ T, ‖ν x‖ ≤ Kν * Real.sqrt t) (j : P) :
    ‖∑ x ∈ T, (μ x * E1 t s j x + ν x * E2 t s j x + E0 t s j x)‖ ≤
      (Kz * A + Kν * A ^ 2) * Real.sqrt t +
        2 * (A * C * M + M * A ^ 2) * power t (2 * beta) := by
  classical
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hβ0 : 0 ≤ power t beta := Real.rpow_nonneg ht.le _
  have hβ1 : power t beta ≤ 1 := Real.rpow_le_one ht.le htle (by norm_num [beta, delta])
  have hF0 : ∀ a b, 0 ≤ s.F t a b := fun a b => by rw [F_eq_sq]; positivity
  have hnormRoot : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
  let term1 : P → ℂ := fun x => if j = x then 0 else
    -((μ x + s.z t x * (1 - s.K t x x)⁻¹) / (Real.sqrt t : ℂ)) * s.K t j x
  let term2 : P → ℂ := fun x => if j = x then 0 else μ x * s.h t j x * sL t s j x
  let term3 : P → ℂ := fun x => if j = x then 0 else ν x * s.h t j x ^ 2 * sQ t s x
  have hsplit : ∑ x ∈ T, (μ x * E1 t s j x + ν x * E2 t s j x + E0 t s j x) =
      (∑ x ∈ T, term1 x) + (-2) * (∑ x ∈ T, term2 x) + ∑ x ∈ T, term3 x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hjx : j = x
    · simp [term1, term2, term3, E1, E2, E0, hjx]
    · simp only [term1, term2, term3, E1, E2, E0, hjx, if_false]
      ring
  -- first term: the direct forcing
  have h1 : ‖∑ x ∈ T, term1 x‖ ≤ Kz * A * Real.sqrt t := by
    have hpt : ∀ x ∈ T, ‖term1 x‖ ≤ Kz * Real.sqrt t * s.F t j x := by
      intro x hx
      by_cases hjx : j = x
      · simp only [term1, hjx, if_true, norm_zero]
        exact mul_nonneg (mul_nonneg hKz hsqrt.le) (hF0 _ _)
      · simp only [term1, hjx, if_false]
        rw [norm_mul, norm_neg, norm_div, hnormRoot, norm_K_eq_F]
        apply mul_le_mul_of_nonneg_right _ (hF0 _ _)
        rw [div_le_iff₀ hsqrt]
        calc ‖μ x + s.z t x * (1 - s.K t x x)⁻¹‖ ≤ Kz * t := hμz x hx
          _ = Kz * Real.sqrt t * Real.sqrt t := by
            rw [mul_assoc, Real.mul_self_sqrt ht.le]
    calc ‖∑ x ∈ T, term1 x‖ ≤ ∑ x ∈ T, ‖term1 x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ T, Kz * Real.sqrt t * s.F t j x := Finset.sum_le_sum hpt
      _ = Kz * Real.sqrt t * ∑ x ∈ T, s.F t j x := by rw [Finset.mul_sum]
      _ ≤ Kz * Real.sqrt t * A := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hKz hsqrt.le)
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun x _ _ => hF0 _ _)).trans (hrowF j)
      _ = Kz * A * Real.sqrt t := by ring
  -- third term: the quadratic correction
  have hsQ : ∀ x, ‖sQ t s x‖ ≤ A := by
    intro x
    unfold sQ
    calc ‖∑ k, (if k = x then (0 : ℂ) else s.h t x k ^ 2 * s.lag t k)‖
        ≤ ∑ k, ‖(if k = x then (0 : ℂ) else s.h t x k ^ 2 * s.lag t k)‖ := norm_sum_le _ _
      _ ≤ ∑ k, s.F t x k := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hkx : k = x
        · simp only [hkx, if_true, norm_zero]; exact hF0 _ _
        · simp only [hkx, if_false]
          rw [norm_mul, norm_pow, ← F_eq_sq]
          calc s.F t x k * ‖s.lag t k‖ ≤ s.F t x k * 1 :=
                mul_le_mul_of_nonneg_left ((hlag k).trans hβ1) (hF0 _ _)
            _ = s.F t x k := mul_one _
      _ ≤ A := hrowF x
  have h3 : ‖∑ x ∈ T, term3 x‖ ≤ Kν * A ^ 2 * Real.sqrt t := by
    have hpt : ∀ x ∈ T, ‖term3 x‖ ≤ Kν * Real.sqrt t * A * s.F t j x := by
      intro x hx
      by_cases hjx : j = x
      · simp only [term3, hjx, if_true, norm_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg hKν hsqrt.le) hA) (hF0 _ _)
      · simp only [term3, hjx, if_false]
        rw [norm_mul, norm_mul, norm_pow, ← F_eq_sq]
        calc ‖ν x‖ * s.F t j x * ‖sQ t s x‖ ≤ (Kν * Real.sqrt t) * s.F t j x * A := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right (hν x hx) (hF0 _ _)) (hsQ x)
                (norm_nonneg _) (mul_nonneg (mul_nonneg hKν hsqrt.le) (hF0 _ _))
          _ = Kν * Real.sqrt t * A * s.F t j x := by ring
    calc ‖∑ x ∈ T, term3 x‖ ≤ ∑ x ∈ T, ‖term3 x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ T, Kν * Real.sqrt t * A * s.F t j x := Finset.sum_le_sum hpt
      _ = Kν * Real.sqrt t * A * ∑ x ∈ T, s.F t j x := by rw [Finset.mul_sum]
      _ ≤ Kν * Real.sqrt t * A * A := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun x _ _ => hF0 _ _)).trans (hrowF j)
      _ = Kν * A ^ 2 * Real.sqrt t := by ring
  -- second term: the linear correction
  let m : ℝ := M * Real.sqrt t * power t beta
  have hm : 0 ≤ m := by positivity
  let μt : P → ℂ := fun x => if x ∈ T then (if j = x then 0 else μ x) else 0
  have hμt : ∀ x, ‖μt x‖ ≤ m := by
    intro x
    by_cases hx : x ∈ T
    · by_cases hjx : j = x
      · simp [μt, hx, hjx, hm]
      · simpa [μt, hx, hjx] using hμ x hx
    · simp [μt, hx, hm]
  have hterm2 : ∑ x ∈ T, term2 x = ∑ x, μt x * s.h t j x * sL t s j x := by
    have : ∀ x, μt x * s.h t j x * sL t s j x = if x ∈ T then term2 x else 0 := by
      intro x
      by_cases hx : x ∈ T <;> by_cases hjx : j = x <;> simp [μt, term2, hx, hjx]
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_ite_mem, Finset.univ_inter]
  have hsLsplit : ∀ x, sL t s j x =
      (∑ k, s.h t j k * s.h t x k * s.lag t k) - s.h t j x * s.h t x x * s.lag t x := by
    intro x
    unfold sL
    exact LagSupport.sum_ite_eq_sum_sub x (fun k => s.h t j k * s.h t x k * s.lag t k)
  let B : P → ℂ := fun k => ∑ x, μt x * s.h t j x * s.h t x k
  have hmain : ∑ x, μt x * s.h t j x * sL t s j x =
      (∑ k, s.h t j k * s.lag t k * B k) -
        ∑ x, μt x * s.h t j x * (s.h t j x * s.h t x x * s.lag t x) := by
    simp only [hsLsplit, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [B, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro x _
    ring
  obtain ⟨_, hl2⟩ := AgentS45.mean_contraction_row_bounds s t μt j A m hsym hA hm hrowF hμt
  have hop := AgentS45.ward_h_operator_bound s t C ht hC hsym hward hp
  have hop2 : ‖s.h t‖ ^ 2 ≤ C ^ 2 / t := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C / Real.sqrt t)).2 hop
    simpa [div_pow, Real.sq_sqrt ht.le] using hs
  have hBl2 : (∑ k, ‖B k‖ ^ 2) ≤ A * (C * M * power t beta) ^ 2 := by
    have h := hl2
    change (∑ k, ‖B k‖ ^ 2) ≤ ‖s.h t‖ ^ 2 * m ^ 2 * A at h
    calc (∑ k, ‖B k‖ ^ 2) ≤ ‖s.h t‖ ^ 2 * m ^ 2 * A := h
      _ ≤ C ^ 2 / t * m ^ 2 * A := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hop2 (sq_nonneg _)) hA
      _ = A * (C * M * power t beta) ^ 2 := by
          dsimp [m]
          rw [mul_pow, mul_pow, Real.sq_sqrt ht.le]
          field_simp
  have hrowj : (∑ k, ‖s.h t j k‖ ^ 2) ≤ A := by simpa [F_eq_sq] using hrowF j
  have hcs : (∑ k, ‖s.h t j k‖ * ‖B k‖) ^ 2 ≤ (A * C * M * power t beta) ^ 2 := by
    calc (∑ k, ‖s.h t j k‖ * ‖B k‖) ^ 2
        ≤ (∑ k, ‖s.h t j k‖ ^ 2) * (∑ k, ‖B k‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ A * (A * (C * M * power t beta) ^ 2) :=
          mul_le_mul hrowj hBl2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) hA
      _ = (A * C * M * power t beta) ^ 2 := by ring
  have hcs' : (∑ k, ‖s.h t j k‖ * ‖B k‖) ≤ A * C * M * power t beta :=
    (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)).1 hcs
  have hfirst : ‖∑ k, s.h t j k * s.lag t k * B k‖ ≤ A * C * M * power t (2 * beta) := by
    calc ‖∑ k, s.h t j k * s.lag t k * B k‖ ≤ ∑ k, ‖s.h t j k * s.lag t k * B k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k, power t beta * (‖s.h t j k‖ * ‖B k‖) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul, norm_mul]
          calc ‖s.h t j k‖ * ‖s.lag t k‖ * ‖B k‖ ≤ ‖s.h t j k‖ * power t beta * ‖B k‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left (hlag k) (norm_nonneg _)
            _ = power t beta * (‖s.h t j k‖ * ‖B k‖) := by ring
      _ = power t beta * ∑ k, ‖s.h t j k‖ * ‖B k‖ := by rw [Finset.mul_sum]
      _ ≤ power t beta * (A * C * M * power t beta) := mul_le_mul_of_nonneg_left hcs' hβ0
      _ = A * C * M * power t (2 * beta) := by
          rw [← LagSupport.lag_power_sq_eq ht]; ring
  have hsecond : ‖∑ x, μt x * s.h t j x * (s.h t j x * s.h t x x * s.lag t x)‖ ≤
      M * A ^ 2 * power t (2 * beta) := by
    calc ‖∑ x, μt x * s.h t j x * (s.h t j x * s.h t x x * s.lag t x)‖
        ≤ ∑ x, ‖μt x * s.h t j x * (s.h t j x * s.h t x x * s.lag t x)‖ := norm_sum_le _ _
      _ ≤ ∑ x, m * (A * Real.sqrt t) * power t beta * s.F t j x := by
          apply Finset.sum_le_sum
          intro x _
          have e : ‖μt x * s.h t j x * (s.h t j x * s.h t x x * s.lag t x)‖ =
              ‖μt x‖ * ‖s.h t x x‖ * ‖s.lag t x‖ * s.F t j x := by
            rw [F_eq_sq]; simp only [norm_mul]; ring
          rw [e]
          apply mul_le_mul_of_nonneg_right _ (hF0 _ _)
          exact mul_le_mul (mul_le_mul (hμt x) (hdiag x) (norm_nonneg _) hm) (hlag x)
            (norm_nonneg _) (by positivity)
      _ = m * (A * Real.sqrt t) * power t beta * ∑ x, s.F t j x := by rw [Finset.mul_sum]
      _ ≤ m * (A * Real.sqrt t) * power t beta * A :=
          mul_le_mul_of_nonneg_left (hrowF j) (by positivity)
      _ = M * A ^ 2 * (Real.sqrt t ^ 2 * power t beta ^ 2) := by dsimp [m]; ring
      _ = M * A ^ 2 * (t * power t (2 * beta)) := by
          rw [Real.sq_sqrt ht.le, LagSupport.lag_power_sq_eq ht]
      _ ≤ M * A ^ 2 * power t (2 * beta) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc t * power t (2 * beta) ≤ 1 * power t (2 * beta) :=
                mul_le_mul_of_nonneg_right htle (Real.rpow_nonneg ht.le _)
            _ = power t (2 * beta) := one_mul _
  have h2 : ‖∑ x ∈ T, term2 x‖ ≤ (A * C * M + M * A ^ 2) * power t (2 * beta) := by
    rw [hterm2, hmain]
    calc _ ≤ ‖∑ k, s.h t j k * s.lag t k * B k‖ +
          ‖∑ x, μt x * s.h t j x * (s.h t j x * s.h t x x * s.lag t x)‖ := norm_sub_le _ _
      _ ≤ A * C * M * power t (2 * beta) + M * A ^ 2 * power t (2 * beta) :=
          add_le_add hfirst hsecond
      _ = (A * C * M + M * A ^ 2) * power t (2 * beta) := by ring
  rw [hsplit]
  have hneg2 : ‖(-2 : ℂ) * ∑ x ∈ T, term2 x‖ = 2 * ‖∑ x ∈ T, term2 x‖ := by
    rw [norm_mul]; norm_num
  calc ‖(∑ x ∈ T, term1 x) + (-2) * (∑ x ∈ T, term2 x) + ∑ x ∈ T, term3 x‖
      ≤ ‖(∑ x ∈ T, term1 x) + (-2) * (∑ x ∈ T, term2 x)‖ + ‖∑ x ∈ T, term3 x‖ :=
        norm_add_le _ _
    _ ≤ ‖∑ x ∈ T, term1 x‖ + ‖(-2 : ℂ) * ∑ x ∈ T, term2 x‖ + ‖∑ x ∈ T, term3 x‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ Kz * A * Real.sqrt t + 2 * ((A * C * M + M * A ^ 2) * power t (2 * beta)) +
          Kν * A ^ 2 * Real.sqrt t := by
        rw [hneg2]; gcongr
    _ = (Kz * A + Kν * A ^ 2) * Real.sqrt t +
          2 * (A * C * M + M * A ^ 2) * power t (2 * beta) := by ring

lemma integral_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (γ : Ω → ℂ) (hγ : Integrable γ μ) (hγ2 : Integrable (fun ω => γ ω ^ 2) μ)
    (a c1 c2 c0 : ℂ) :
    Integrable (fun ω => γ ω * c1 + (γ ω ^ 2 - a) * c2 + c0) μ ∧
    ∫ ω, (γ ω * c1 + (γ ω ^ 2 - a) * c2 + c0) ∂μ =
      (∫ ω, γ ω ∂μ) * c1 + ((∫ ω, γ ω ^ 2 ∂μ) - a) * c2 + c0 := by
  have i1 : Integrable (fun ω => γ ω * c1) μ := hγ.mul_const c1
  have i2' : Integrable (fun ω => γ ω ^ 2 - a) μ := hγ2.sub (integrable_const a)
  have i2 : Integrable (fun ω => (γ ω ^ 2 - a) * c2) μ := i2'.mul_const c2
  refine ⟨(i1.add i2).add (integrable_const c0), ?_⟩
  have e1 : ∫ ω, (γ ω * c1 + (γ ω ^ 2 - a) * c2 + c0) ∂μ =
      (∫ ω, (γ ω * c1 + (γ ω ^ 2 - a) * c2) ∂μ) + ∫ _ω, c0 ∂μ :=
    integral_add (i1.add i2) (integrable_const c0)
  have e2 : ∫ ω, (γ ω * c1 + (γ ω ^ 2 - a) * c2) ∂μ =
      (∫ ω, γ ω * c1 ∂μ) + ∫ ω, (γ ω ^ 2 - a) * c2 ∂μ := integral_add i1 i2
  have e3 : ∫ ω, (γ ω ^ 2 - a) ∂μ = (∫ ω, γ ω ^ 2 ∂μ) - ∫ _ω, a ∂μ :=
    integral_sub hγ2 (integrable_const a)
  rw [e1, e2, integral_mul_const, integral_mul_const, e3]
  simp

lemma inv_one_sub_sub_one (k : ℂ) (hk : 1 - k ≠ 0) :
    (1 - k)⁻¹ - 1 = (1 - k)⁻¹ * k := by
  field_simp
  ring

/-- The signed conditional mean of the lag increment, for one output coordinate. -/
theorem lag_mean_core {P Ω : Type*} [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C A G L t Kz Kν M R : ℝ) (s : State P) (Λplus Wstar : Form P) (S : Finset P)
    (ξ : P → Ω → ℝ)
    (hC : 1 ≤ C) (hA : 0 < A) (hG : 0 ≤ G) (hL : 0 ≤ L) (ht : 0 < t) (htle : t ≤ 1)
    (hM : 0 ≤ M) (hKz : 0 ≤ Kz) (hKν : 0 ≤ Kν) (hR : 0 ≤ R)
    (hpre : Prestate t C Λplus Wstar s)
    (hProw : rowNorm (s.P t) ≤ L)
    (hcaps :
      (∀ i, ‖s.rawLag i‖ ≤ A * power t beta ∧
        |s.q i - s.p i| ≤ A * power t beta ∧
        (∑ j, s.F t i j) ≤ A ∧ ‖s.h t i i‖ ≤ A * Real.sqrt t) ∧
      (∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤ A * power t (delta / 2)))
    (hγ : ∀ x (ζ : ℝ), |ζ| ≤ C * Real.sqrt t →
      ‖gamma t s x ζ‖ ≤ G ∧ 1 + ((ζ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hpert : L * (2 * G * Real.sqrt (Real.sqrt t) * A + (G ^ 2 + 2) * Real.sqrt t * A) < 1)
    (hsmall : 2 * L ^ 2 * (contractConst G A * Real.sqrt t) ≤ 1 / 2)
    (hRsq : L ^ 2 * (sumConst G A * (4 * L ^ 2 * (forcingConst G A * power t delta))) ≤ R ^ 2)
    (hmeas : ∀ x ∈ S, Measurable (ξ x))
    (hbdd : ∀ x ∈ S, ∀ᵐ ω ∂μ, |ξ x ω| ≤ C * Real.sqrt t)
    (hμz : ∀ x ∈ S, ‖(∫ ω, gamma t s x (ξ x ω) ∂μ) + s.z t x * (1 - s.K t x x)⁻¹‖ ≤ Kz * t)
    (hμ : ∀ x ∈ S, ‖∫ ω, gamma t s x (ξ x ω) ∂μ‖ ≤ M * Real.sqrt t * power t beta)
    (hν : ∀ x ∈ S, ‖(∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹‖ ≤ Kν * Real.sqrt t)
    (i : P) :
    ‖∑ x ∈ S, ∫ ω, lagInc t s x (ξ x ω) i ∂μ‖ ≤
      L * ((Kz * A + Kν * A ^ 2) * Real.sqrt t +
        2 * (A * C * M + M * A ^ 2) * power t (2 * beta)) + R := by
  classical
  -- the coordinates with an integrable increment
  set S' := S.filter (fun x => Integrable (fun ω => lagInc t s x (ξ x ω) i) μ) with hS'
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  have hsum1 : ∑ x ∈ S, ∫ ω, lagInc t s x (ξ x ω) i ∂μ =
      ∑ x ∈ S', ∫ ω, lagInc t s x (ξ x ω) i ∂μ := by
    rw [hS']
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x _ hne
    by_contra hni
    exact hne (integral_undef hni)
  -- gamma along each coordinate
  have hγm : ∀ x ∈ S, Measurable (fun ω => gamma t s x (ξ x ω)) := by
    intro x hx
    have := hmeas x hx
    unfold gamma
    fun_prop
  have hγae : ∀ x ∈ S, ∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω)‖ ≤ G := by
    intro x hx
    filter_upwards [hbdd x hx] with ω hω
    exact (hγ x _ hω).1
  have hγI : ∀ x ∈ S, Integrable (fun ω => gamma t s x (ξ x ω)) μ := fun x hx =>
    Integrable.of_bound (hγm x hx).aestronglyMeasurable G (hγae x hx)
  have hγ2I : ∀ x ∈ S, Integrable (fun ω => gamma t s x (ξ x ω) ^ 2) μ := by
    intro x hx
    refine Integrable.of_bound ((hγm x hx).pow_const 2).aestronglyMeasurable (G ^ 2) ?_
    filter_upwards [hγae x hx] with ω hω
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  -- the leading (forcing) part
  let Mx : P → CMat P := fun x => pad (survivors x) (restrict (s.P t) (survivors x))
  let c1 : P → ℂ := fun x => ∑ j, Mx x i j * E1 t s j x
  let c2 : P → ℂ := fun x => ∑ j, Mx x i j * E2 t s j x
  let c0 : P → ℂ := fun x => ∑ j, Mx x i j * E0 t s j x
  let lead : P → Ω → ℂ := fun x ω =>
    (Mx x *ᵥ fun j => LagSupport.lagRawForcingScaled t s (fun y => ξ y ω) j x) i
  have hlead : ∀ x ω, lead x ω = gamma t s x (ξ x ω) * c1 x +
      (gamma t s x (ξ x ω) ^ 2 - (1 - s.K t x x)⁻¹) * c2 x + c0 x := by
    intro x ω
    simp only [lead, c1, c2, c0, Matrix.mulVec, dotProduct, forcing_affine,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hleadI : ∀ x ∈ S, Integrable (lead x) μ ∧
      ∫ ω, lead x ω ∂μ = (∫ ω, gamma t s x (ξ x ω) ∂μ) * c1 x +
        ((∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹) * c2 x + c0 x := by
    intro x hx
    have h := integral_affine μ (fun ω => gamma t s x (ξ x ω)) (hγI x hx) (hγ2I x hx)
      ((1 - s.K t x x)⁻¹) (c1 x) (c2 x) (c0 x)
    have hfun : lead x = fun ω => gamma t s x (ξ x ω) * c1 x +
        (gamma t s x (ξ x ω) ^ 2 - (1 - s.K t x x)⁻¹) * c2 x + c0 x := funext (hlead x)
    rw [hfun]
    exact h
  -- split the integrable increments
  have hdiffI : ∀ x ∈ S', Integrable (fun ω => lagInc t s x (ξ x ω) i - lead x ω) μ := by
    intro x hx
    exact (Finset.mem_filter.1 hx).2.sub (hleadI x (hS'S hx)).1
  have hsplit : ∑ x ∈ S', ∫ ω, lagInc t s x (ξ x ω) i ∂μ =
      (∑ x ∈ S', ∫ ω, lead x ω ∂μ) +
        ∑ x ∈ S', ∫ ω, (lagInc t s x (ξ x ω) i - lead x ω) ∂μ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [integral_sub (Finset.mem_filter.1 hx).2 (hleadI x (hS'S hx)).1]
    ring
  -- the leading part: the signed forcing mean
  let ybar : P → P → ℂ := fun j x => (∫ ω, gamma t s x (ξ x ω) ∂μ) * E1 t s j x +
      ((∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹) * E2 t s j x + E0 t s j x
  have hleadInt : ∀ x ∈ S, ∫ ω, lead x ω ∂μ = ∑ j, Mx x i j * ybar j x := by
    intro x hx
    rw [(hleadI x hx).2]
    simp only [c1, c2, c0, ybar, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hybar_diag : ∀ x, ybar x x = 0 := by
    intro x
    simp [ybar, E1, E2, E0]
  have hMx_entry : ∀ x j, x ≠ i → Mx x i j * ybar j x = s.P t i j * ybar j x := by
    intro x j hxi
    by_cases hjx : j = x
    · subst hjx
      simp [hybar_diag]
    · have hi : i ∈ survivors x := by simp [survivors, Ne.symm hxi]
      have hj : j ∈ survivors x := by simp [survivors, hjx]
      simp [Mx, pad, restrict, hi, hj]
  have hMx_self : ∀ j, Mx i i j = 0 := by
    intro j
    simp [Mx, pad, survivors]
  have hleadSum : ∑ x ∈ S', ∫ ω, lead x ω ∂μ =
      ∑ j, s.P t i j * ∑ x ∈ S'.erase i, ybar j x := by
    rw [Finset.sum_congr rfl (fun x hx => hleadInt x (hS'S hx))]
    have herase : ∑ x ∈ S', ∑ j, Mx x i j * ybar j x =
        ∑ x ∈ S'.erase i, ∑ j, Mx x i j * ybar j x := by
      by_cases hiS : i ∈ S'
      · exact (Finset.sum_erase S' (by simp [hMx_self])).symm
      · rw [Finset.erase_eq_of_notMem hiS]
    rw [herase, Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl
      (fun j _ => hMx_entry x j (Finset.ne_of_mem_erase hx))), Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hT : S'.erase i ⊆ S := (Finset.erase_subset i S').trans hS'S
  have hbndj := fun j => mean_forcing_bound C A M Kz Kν t s (S'.erase i)
    (fun x => ∫ ω, gamma t s x (ξ x ω) ∂μ)
    (fun x => (∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹)
    ht htle (by linarith) hA.le hM hKz hKν hpre.symmetric hpre.ward
    (fun j => (hpre.broad j).2.1) (fun r => (hcaps.1 r).2.2.1) (fun r => (hcaps.1 r).2.2.2)
    hpre.lag_cap (fun x hx => hμz x (hT hx)) (fun x hx => hμ x (hT hx))
    (fun x hx => hν x (hT hx)) j
  have hbnd0 : 0 ≤ (Kz * A + Kν * A ^ 2) * Real.sqrt t +
      2 * (A * C * M + M * A ^ 2) * power t (2 * beta) := by
    have := Real.rpow_nonneg ht.le (2 * beta)
    have := Real.sqrt_nonneg t
    unfold power
    positivity
  have hleadBound : ‖∑ x ∈ S', ∫ ω, lead x ω ∂μ‖ ≤
      L * ((Kz * A + Kν * A ^ 2) * Real.sqrt t +
        2 * (A * C * M + M * A ^ 2) * power t (2 * beta)) := by
    rw [hleadSum]
    calc _ ≤ ∑ j, ‖s.P t i j * ∑ x ∈ S'.erase i, ybar j x‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖s.P t i j‖ * ((Kz * A + Kν * A ^ 2) * Real.sqrt t +
            2 * (A * C * M + M * A ^ 2) * power t (2 * beta)) :=
          Finset.sum_le_sum fun j _ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hbndj j) (norm_nonneg _)
      _ = (∑ j, ‖s.P t i j‖) * ((Kz * A + Kν * A ^ 2) * Real.sqrt t +
            2 * (A * C * M + M * A ^ 2) * power t (2 * beta)) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
          ((LagSupport.rowSum_le_rowNorm _ i).trans hProw) hbnd0
  -- the remainder: pathwise absolute-sum bound, then averaged
  have hpath : ∀ᵐ ω ∂μ, ∑ x ∈ S', ‖lagInc t s x (ξ x ω) i - lead x ω‖ ≤ R := by
    have hall : ∀ᵐ ω ∂μ, ∀ x ∈ S, |ξ x ω| ≤ C * Real.sqrt t :=
      (Filter.eventually_all_finset S).2 hbdd
    filter_upwards [hall] with ω hω
    have hcore := lag_core C A G L t s Λplus Wstar S' (fun y => ξ y ω) hC hA hG hL ht htle
      hpre hProw hcaps hγ (fun x hx => hω x (hS'S hx)) hpert hsmall
    have h3' : (∑ x ∈ S', ‖lagInc t s x (ξ x ω) i - lead x ω‖) ^ 2 ≤ R ^ 2 :=
      (hcore.2.2 i).trans hRsq
    exact (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hR).1 h3'
  have hremBound : ‖∑ x ∈ S', ∫ ω, (lagInc t s x (ξ x ω) i - lead x ω) ∂μ‖ ≤ R := by
    calc _ ≤ ∑ x ∈ S', ‖∫ ω, (lagInc t s x (ξ x ω) i - lead x ω) ∂μ‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ S', ∫ ω, ‖lagInc t s x (ξ x ω) i - lead x ω‖ ∂μ :=
          Finset.sum_le_sum fun x _ => norm_integral_le_integral_norm _
      _ = ∫ ω, ∑ x ∈ S', ‖lagInc t s x (ξ x ω) i - lead x ω‖ ∂μ :=
          (integral_finset_sum S' (fun x hx => (hdiffI x hx).norm)).symm
      _ ≤ ∫ _ω, R ∂μ := integral_mono_ae
          (integrable_finset_sum S' (fun x hx => (hdiffI x hx).norm)) (integrable_const R) hpath
      _ = R := by simp
  rw [hsum1, hsplit]
  calc _ ≤ ‖∑ x ∈ S', ∫ ω, lead x ω ∂μ‖ +
        ‖∑ x ∈ S', ∫ ω, (lagInc t s x (ξ x ω) i - lead x ω) ∂μ‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hleadBound hremBound

/-- Conditional moments of `γ` in the form used by the mean estimate. -/
lemma gamma_mean_inputs {P : Type*} [Fintype P] [DecidableEq P]
    (t A G1 : ℝ) (s : State P) (x : P) (m1 m2 : ℂ)
    (ht : 0 < t) (htle : t ≤ 1) (hA : 0 ≤ A) (hG1 : 0 ≤ G1)
    (hraw : ‖s.rawLag x‖ ≤ A * power t beta) (hdiag : ‖s.h t x x‖ ≤ A * Real.sqrt t)
    (hK : ‖s.K t‖ ≤ 1 / 2)
    (h1 : ‖m1 + s.z t x‖ ≤ G1 * t) (h2 : ‖m2 - 1‖ ≤ G1 * Real.sqrt t) :
    ‖m1 + s.z t x * (1 - s.K t x x)⁻¹‖ ≤ (G1 + 2 * A ^ 3) * t ∧
    ‖m1‖ ≤ (G1 + A) * Real.sqrt t * power t beta ∧
    ‖m2 - (1 - s.K t x x)⁻¹‖ ≤ (G1 + 2 * A ^ 2) * Real.sqrt t := by
  have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr htle
  have hβ0 : 0 ≤ power t beta := Real.rpow_nonneg ht.le _
  have hβ1 : power t beta ≤ 1 := Real.rpow_le_one ht.le htle (by norm_num [beta, delta])
  obtain ⟨ha, hainv⟩ := LagSupport.lag_pivot_inverse_bound s t hK x
  have hz : ‖s.z t x‖ ≤ Real.sqrt t * (A * power t beta) := by
    have hnorm : ‖s.z t x‖ = Real.sqrt t * ‖s.rawLag x‖ := by
      simp [State.z, Complex.norm_real, abs_of_nonneg hsqrt0]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hraw hsqrt0
  have hzA : ‖s.z t x‖ ≤ A := by
    calc ‖s.z t x‖ ≤ Real.sqrt t * (A * power t beta) := hz
      _ ≤ 1 * (A * 1) := mul_le_mul hsqrt1 (mul_le_mul_of_nonneg_left hβ1 hA)
          (by positivity) zero_le_one
      _ = A := by ring
  have hKxx : ‖s.K t x x‖ ≤ A ^ 2 * t := by
    rw [norm_K_eq_F, F_eq_sq]
    calc ‖s.h t x x‖ ^ 2 ≤ (A * Real.sqrt t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdiag 2
      _ = A ^ 2 * t := by rw [mul_pow, Real.sq_sqrt ht.le]
  have hdiff : ‖(1 - s.K t x x)⁻¹ - 1‖ ≤ 2 * (A ^ 2 * t) := by
    rw [inv_one_sub_sub_one _ ha, norm_mul]
    exact mul_le_mul hainv hKxx (norm_nonneg _) (by norm_num)
  have htle' : t ≤ Real.sqrt t := by
    calc t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht.le).symm
      _ ≤ Real.sqrt t * 1 := mul_le_mul_of_nonneg_left hsqrt1 hsqrt0
      _ = Real.sqrt t := mul_one _
  have hsqrtβ : Real.sqrt t ≤ power t beta := by
    unfold power
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge ht htle (by norm_num [beta, delta])
  have htβ : t ≤ Real.sqrt t * power t beta := by
    calc t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht.le).symm
      _ ≤ Real.sqrt t * power t beta := mul_le_mul_of_nonneg_left hsqrtβ hsqrt0
  refine ⟨?_, ?_, ?_⟩
  · have heq : m1 + s.z t x * (1 - s.K t x x)⁻¹ =
        (m1 + s.z t x) + s.z t x * ((1 - s.K t x x)⁻¹ - 1) := by ring
    rw [heq]
    calc ‖(m1 + s.z t x) + s.z t x * ((1 - s.K t x x)⁻¹ - 1)‖
        ≤ ‖m1 + s.z t x‖ + ‖s.z t x‖ * ‖(1 - s.K t x x)⁻¹ - 1‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ G1 * t + A * (2 * (A ^ 2 * t)) :=
          add_le_add h1 (mul_le_mul hzA hdiff (norm_nonneg _) hA)
      _ = (G1 + 2 * A ^ 3) * t := by ring
  · have heq : m1 = (m1 + s.z t x) - s.z t x := by ring
    rw [heq]
    calc ‖(m1 + s.z t x) - s.z t x‖ ≤ ‖m1 + s.z t x‖ + ‖s.z t x‖ := norm_sub_le _ _
      _ ≤ G1 * t + Real.sqrt t * (A * power t beta) := add_le_add h1 hz
      _ ≤ G1 * (Real.sqrt t * power t beta) + Real.sqrt t * (A * power t beta) := by
          gcongr
      _ = (G1 + A) * Real.sqrt t * power t beta := by ring
  · have heq : m2 - (1 - s.K t x x)⁻¹ = (m2 - 1) - ((1 - s.K t x x)⁻¹ - 1) := by ring
    rw [heq]
    calc ‖(m2 - 1) - ((1 - s.K t x x)⁻¹ - 1)‖
        ≤ ‖m2 - 1‖ + ‖(1 - s.K t x x)⁻¹ - 1‖ := norm_sub_le _ _
      _ ≤ G1 * Real.sqrt t + 2 * (A ^ 2 * t) := add_le_add h2 hdiff
      _ ≤ G1 * Real.sqrt t + 2 * (A ^ 2 * Real.sqrt t) := by gcongr
      _ = (G1 + 2 * A ^ 2) * Real.sqrt t := by ring

end LagFinal

open LagFinal in
/-- Lemma 4.6 (`refs/tex/04-sweep.tex:791-1092`), with the exact type of the
`AndersonAC.S45.lag_bounds`. -/
theorem lag_bounds_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → rowNorm (s.P t) ≤ C * logFactor t →
    (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) →
      arrayA2sq S (fun i x => lagInc t s x (z x) i) ≤
        C' * logFactor t ^ 2 * power t delta) ∧
    (∀ i, ‖∑ x ∈ S, ∫ ω, lagInc t s x (ξ x ω) i ∂μ‖ ≤
      C' * (logFactor t * (power t (2 * beta) + Real.sqrt t) +
        logFactor t ^ 2 * power t (delta / 2))) := by
  intro C hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨A, hA, tA, htA, hFacts⟩ := analyticPrestate_any C hC
  set C₁ : ℝ := 2 * C + A with hC₁def
  have hC₁ : 1 ≤ C₁ := by rw [hC₁def]; linarith
  have hC_le : C ≤ C₁ := by rw [hC₁def]; linarith
  obtain ⟨G1, hG1, tG, htG, hMom⟩ := gamma_moments_proof C₁ hC₁
  set G : ℝ := LagSupport.lagGammaBound C with hGdef
  have hG : 0 ≤ G := by rw [hGdef]; unfold LagSupport.lagGammaBound; positivity
  set fc := forcingConst G A with hfcdef
  set cc := contractConst G A with hccdef
  set sc := sumConst G A with hscdef
  have hfc : 0 ≤ fc := by rw [hfcdef]; unfold forcingConst; positivity
  have hcc : 0 ≤ cc := by rw [hccdef]; unfold contractConst; positivity
  have hsc : 0 ≤ sc := by rw [hscdef]; unfold sumConst; positivity
  set Kp : ℝ := 2 * G * A + (G ^ 2 + 2) * A with hKpdef
  have hKp : 0 ≤ Kp := by rw [hKpdef]; positivity
  set Kz : ℝ := G1 + 2 * A ^ 3 with hKzdef
  set Kν : ℝ := G1 + 2 * A ^ 2 with hKνdef
  set M : ℝ := G1 + A with hMdef
  have hKz : 0 ≤ Kz := by rw [hKzdef]; positivity
  have hKν : 0 ≤ Kν := by rw [hKνdef]; positivity
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  set K1 : ℝ := Kz * A + Kν * A ^ 2 + 2 * (A * C * M + M * A ^ 2) with hK1def
  have hK1 : 0 ≤ K1 := by rw [hK1def]; positivity
  set Cfin : ℝ := C * K1 + 2 * C ^ 2 * (1 + sc * fc) + 4 * C ^ 2 * fc + 1 with hCfindef
  have hCfin1 : C * K1 ≤ Cfin := by
    rw [hCfindef]; have : 0 ≤ 2 * C ^ 2 * (1 + sc * fc) := by positivity
    nlinarith [sq_nonneg C]
  have hCfin2 : 2 * C ^ 2 * (1 + sc * fc) ≤ Cfin := by
    rw [hCfindef]; have : 0 ≤ C * K1 := by positivity
    nlinarith [sq_nonneg C]
  have hCfin3 : 4 * C ^ 2 * fc ≤ Cfin := by
    rw [hCfindef]
    have : 0 ≤ C * K1 := by positivity
    have : 0 ≤ 2 * C ^ 2 * (1 + sc * fc) := by positivity
    linarith
  have hCfinpos : 0 < Cfin := by
    rw [hCfindef]
    have : 0 ≤ C * K1 := by positivity
    have : 0 ≤ 2 * C ^ 2 * (1 + sc * fc) := by positivity
    have : 0 ≤ 4 * C ^ 2 * fc := by positivity
    linarith
  -- small-scale thresholds
  obtain ⟨t1, ht1, hpow1⟩ := power_small (e := beta) (a := 1 / (2 * C))
    (by norm_num [beta, delta]) (by positivity)
  obtain ⟨t2, ht2, hpow2⟩ := power_small (e := 1 / 2)
    (a := (4 * (2 * C + 2 * (1 + C ^ 2)) ^ 2)⁻¹) (by norm_num) (by positivity)
  set a3 : ℝ := min (1 / (4 * C ^ 2 * cc + 1)) ((1 / (C * Kp + 1)) ^ 2) with ha3def
  have ha3 : 0 < a3 := by rw [ha3def]; apply lt_min <;> positivity
  obtain ⟨t3, ht3, hlog3⟩ := LagSupport.lag_logFactor_sq_power_small (e := 1 / 2) (a := a3)
    (by norm_num) ha3
  refine ⟨Cfin, hCfinpos, min (min tA tG) (min t1 (min t2 t3)),
    lt_min (lt_min htA htG) (lt_min ht1 (lt_min ht2 ht3)), ?_⟩
  intro P Ω _ _ _ μ _ t s Λplus Wstar S ξ htt hpre hProw hLaw
  have ht : 0 < t := hpre.scale.1
  have htle : t ≤ 1 := hpre.scale.2.le
  have httA : t < tA := lt_of_lt_of_le htt ((min_le_left _ _).trans (min_le_left _ _))
  have httG : t < tG := lt_of_lt_of_le htt ((min_le_left _ _).trans (min_le_right _ _))
  have htt1 : t < t1 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt2 : t < t2 := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htt3 : t < t3 := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcapsAll := hFacts P t s Λplus Wstar httA hpre
  have hcaps := And.intro hcapsAll.1 hcapsAll.2.1
  have hsqrt_eq : Real.sqrt t = power t (1 / 2) := by
    rw [Real.sqrt_eq_rpow]; rfl
  have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr htle
  have hlogF1 : 1 ≤ logFactor t := by
    unfold logFactor
    have : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    linarith
  set L : ℝ := C * logFactor t with hLdef
  have hL : 0 ≤ L := by rw [hLdef]; positivity
  -- pointwise gamma bounds
  have hbetaSmall : C * power t beta ≤ 1 / 2 := by
    have h := hpow1 t ht htt1
    have h' : C * power t beta < C * (1 / (2 * C)) := mul_lt_mul_of_pos_left h hCpos
    have e : C * (1 / (2 * C)) = 1 / 2 := by field_simp
    linarith
  have hepsSmall : Real.sqrt t < (4 * (2 * C + 2 * (1 + C ^ 2)) ^ 2)⁻¹ := by
    rw [hsqrt_eq]; exact hpow2 t ht htt2
  have hγ : ∀ x (ζ : ℝ), |ζ| ≤ C * Real.sqrt t →
      ‖gamma t s x ζ‖ ≤ G ∧ 1 + ((ζ : ℂ) + t * s.r x) * s.g x x ≠ 0 := by
    intro x ζ hζ
    have h := LagSupport.lag_gamma_bounds_of_prestate C t s Λplus Wstar {x} (fun _ => ζ)
      hC ht htle hpre hbetaSmall hepsSmall (fun _ _ => hζ) x (Finset.mem_singleton_self x)
    exact ⟨h.2, h.1⟩
  -- logarithmic smallness
  have hl3 : logFactor t ^ 2 * Real.sqrt t < a3 := by
    rw [hsqrt_eq]; exact hlog3 t ht htt3
  have hsmall : 2 * L ^ 2 * (cc * Real.sqrt t) ≤ 1 / 2 := by
    have h := lt_of_lt_of_le hl3 (min_le_left _ _)
    have hx0 : 0 ≤ logFactor t ^ 2 * Real.sqrt t := by positivity
    have hden : 0 < 4 * C ^ 2 * cc + 1 := by positivity
    rw [lt_div_iff₀ hden] at h
    have heq : 2 * L ^ 2 * (cc * Real.sqrt t) =
        2 * C ^ 2 * cc * (logFactor t ^ 2 * Real.sqrt t) := by rw [hLdef]; ring
    rw [heq]
    nlinarith
  have hpert : L * (2 * G * Real.sqrt (Real.sqrt t) * A + (G ^ 2 + 2) * Real.sqrt t * A) < 1 := by
    have h := lt_of_lt_of_le hl3 (min_le_right _ _)
    have hy0 : 0 ≤ logFactor t * Real.sqrt (Real.sqrt t) := by positivity
    have hd : 0 < C * Kp + 1 := by positivity
    have hy : logFactor t * Real.sqrt (Real.sqrt t) < 1 / (C * Kp + 1) := by
      have hsq : (logFactor t * Real.sqrt (Real.sqrt t)) ^ 2 < (1 / (C * Kp + 1)) ^ 2 := by
        rw [mul_pow, sqrt_sqrt_sq ht.le]; exact h
      exact (pow_lt_pow_iff_left₀ hy0 (by positivity) (by norm_num)).1 hsq
    have htle' : t ≤ Real.sqrt t := by
      calc t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht.le).symm
        _ ≤ Real.sqrt t * 1 := mul_le_mul_of_nonneg_left hsqrt1 hsqrt0
        _ = Real.sqrt t := mul_one _
    have hsq_le : Real.sqrt t ≤ Real.sqrt (Real.sqrt t) := Real.sqrt_le_sqrt htle'
    have hbound : 2 * G * Real.sqrt (Real.sqrt t) * A + (G ^ 2 + 2) * Real.sqrt t * A ≤
        Kp * Real.sqrt (Real.sqrt t) := by
      rw [hKpdef]
      have : (G ^ 2 + 2) * Real.sqrt t * A ≤ (G ^ 2 + 2) * Real.sqrt (Real.sqrt t) * A := by
        gcongr
      nlinarith
    rw [lt_div_iff₀ hd] at hy
    calc L * (2 * G * Real.sqrt (Real.sqrt t) * A + (G ^ 2 + 2) * Real.sqrt t * A)
        ≤ L * (Kp * Real.sqrt (Real.sqrt t)) := mul_le_mul_of_nonneg_left hbound hL
      _ = C * Kp * (logFactor t * Real.sqrt (Real.sqrt t)) := by rw [hLdef]; ring
      _ < 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · -- pathwise square-array bound
    intro z hz
    have hcore := lag_core C A G L t s Λplus Wstar S z hC hA hG hL ht htle hpre hProw hcaps hγ
      hz hpert hsmall
    calc arrayA2sq S (fun i x => lagInc t s x (z x) i) ≤ 4 * L ^ 2 * (fc * power t delta) :=
          hcore.2.1
      _ = (4 * C ^ 2 * fc) * logFactor t ^ 2 * power t delta := by rw [hLdef]; ring
      _ ≤ Cfin * logFactor t ^ 2 * power t delta := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
          exact mul_le_mul_of_nonneg_right hCfin3 (sq_nonneg _)
  · -- signed conditional mean
    intro i
    have hstate : ∀ x, ‖s.g x x‖ + ‖s.r x‖ ≤ C₁ := by
      intro x
      have hβ1 : power t beta ≤ 1 := Real.rpow_le_one ht.le htle (by norm_num [beta, delta])
      have hraw : ‖s.rawLag x‖ ≤ A := (hcaps.1 x).1.trans (mul_le_of_le_one_right hA.le hβ1)
      have hr : ‖s.r x‖ ≤ C := (hpre.broad x).1
      have hg : ‖s.g x x‖ ≤ ‖s.r x‖ + ‖s.rawLag x‖ := by
        calc ‖s.g x x‖ = ‖s.r x + s.rawLag x‖ := by
              congr 1; simp [State.rawLag]
          _ ≤ ‖s.r x‖ + ‖s.rawLag x‖ := norm_add_le _ _
      rw [hC₁def]
      linarith
    have hinputs : ∀ x ∈ S,
        ‖(∫ ω, gamma t s x (ξ x ω) ∂μ) + s.z t x * (1 - s.K t x x)⁻¹‖ ≤ Kz * t ∧
        ‖∫ ω, gamma t s x (ξ x ω) ∂μ‖ ≤ M * Real.sqrt t * power t beta ∧
        ‖(∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹‖ ≤ Kν * Real.sqrt t := by
      intro x hx
      let law₁ : MomentLaw μ t C₁ (ξ x) :=
        { measurable := (hLaw x hx).measurable
          mean := (hLaw x hx).mean
          variance := (hLaw x hx).variance
          bounded := (hLaw x hx).bounded.mono fun ω hω =>
            hω.trans (mul_le_mul_of_nonneg_right hC_le (Real.sqrt_nonneg t)) }
      have hm := hMom P Ω μ t s x (ξ x) ht httG (hstate x) law₁
      exact gamma_mean_inputs t A G1 s x _ _ ht htle hA.le hG1.le (hcaps.1 x).1
        (hcaps.1 x).2.2.2 hpre.K_cap hm.2.1 hm.2.2.1
    set R : ℝ := 2 * L ^ 2 * (1 + sc * fc) * power t (delta / 2) with hRdef
    have hpd0 : 0 ≤ power t (delta / 2) := Real.rpow_nonneg ht.le _
    have hR : 0 ≤ R := by rw [hRdef]; positivity
    have hpd : power t (delta / 2) ^ 2 = power t delta := by
      rw [LagSupport.lag_power_sq_eq ht]; ring_nf
    have hRsq : L ^ 2 * (sc * (4 * L ^ 2 * (fc * power t delta))) ≤ R ^ 2 := by
      have hx : sc * fc ≤ (1 + sc * fc) ^ 2 := by nlinarith [mul_nonneg hsc hfc]
      have hpd' : 0 ≤ power t delta := Real.rpow_nonneg ht.le _
      calc L ^ 2 * (sc * (4 * L ^ 2 * (fc * power t delta)))
          = (4 * L ^ 4 * power t delta) * (sc * fc) := by ring
        _ ≤ (4 * L ^ 4 * power t delta) * (1 + sc * fc) ^ 2 :=
            mul_le_mul_of_nonneg_left hx (by positivity)
        _ = R ^ 2 := by rw [hRdef, ← hpd]; ring
    have hmean := lag_mean_core μ C A G L t Kz Kν M R s Λplus Wstar S ξ hC hA hG hL ht htle
      hM hKz hKν hR hpre hProw hcaps hγ hpert hsmall hRsq
      (fun x hx => (hLaw x hx).measurable) (fun x hx => (hLaw x hx).bounded)
      (fun x hx => (hinputs x hx).1) (fun x hx => (hinputs x hx).2.1)
      (fun x hx => (hinputs x hx).2.2) i
    refine hmean.trans ?_
    have hb0 : 0 ≤ power t (2 * beta) := Real.rpow_nonneg ht.le _
    have hX0 : 0 ≤ logFactor t * (power t (2 * beta) + Real.sqrt t) := by positivity
    have hY0 : 0 ≤ logFactor t ^ 2 * power t (delta / 2) := by positivity
    have hlead : L * ((Kz * A + Kν * A ^ 2) * Real.sqrt t +
        2 * (A * C * M + M * A ^ 2) * power t (2 * beta)) ≤
        (C * K1) * (logFactor t * (power t (2 * beta) + Real.sqrt t)) := by
      have ha : 0 ≤ Kz * A + Kν * A ^ 2 := by positivity
      have hb : 0 ≤ 2 * (A * C * M + M * A ^ 2) := by positivity
      have hin : (Kz * A + Kν * A ^ 2) * Real.sqrt t +
          2 * (A * C * M + M * A ^ 2) * power t (2 * beta) ≤
          K1 * (power t (2 * beta) + Real.sqrt t) := by
        rw [hK1def]
        nlinarith [mul_nonneg ha hb0, mul_nonneg hb hsqrt0]
      calc L * ((Kz * A + Kν * A ^ 2) * Real.sqrt t +
            2 * (A * C * M + M * A ^ 2) * power t (2 * beta))
          ≤ L * (K1 * (power t (2 * beta) + Real.sqrt t)) := mul_le_mul_of_nonneg_left hin hL
        _ = (C * K1) * (logFactor t * (power t (2 * beta) + Real.sqrt t)) := by
            rw [hLdef]; ring
    have hRe : R = (2 * C ^ 2 * (1 + sc * fc)) * (logFactor t ^ 2 * power t (delta / 2)) := by
      rw [hRdef, hLdef]; ring
    rw [hRe]
    calc L * ((Kz * A + Kν * A ^ 2) * Real.sqrt t +
          2 * (A * C * M + M * A ^ 2) * power t (2 * beta)) +
          (2 * C ^ 2 * (1 + sc * fc)) * (logFactor t ^ 2 * power t (delta / 2))
        ≤ (C * K1) * (logFactor t * (power t (2 * beta) + Real.sqrt t)) +
          (2 * C ^ 2 * (1 + sc * fc)) * (logFactor t ^ 2 * power t (delta / 2)) :=
          add_le_add hlead le_rfl
      _ ≤ Cfin * (logFactor t * (power t (2 * beta) + Real.sqrt t)) +
          Cfin * (logFactor t ^ 2 * power t (delta / 2)) :=
          add_le_add (mul_le_mul_of_nonneg_right hCfin1 hX0)
            (mul_le_mul_of_nonneg_right hCfin2 hY0)
      _ = Cfin * (logFactor t * (power t (2 * beta) + Real.sqrt t) +
          logFactor t ^ 2 * power t (delta / 2)) := by ring


end AndersonAC.AgentS45
