import Mathlib
import AndersonAC.S3.HelperStatements2

/-!
The dyadic layer-cake estimate for a product of two truncated reciprocals.
This module depends only on the §3 helper statements and Mathlib.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace AndersonAC.S3H

def dyadicScale (v : ℝ) (i : ℕ) : ℝ := v * (2 : ℝ) ^ i

theorem dyadicScale_pos {v : ℝ} (hv : 0 < v) (i : ℕ) : 0 < dyadicScale v i :=
  mul_pos hv (pow_pos (by norm_num) _)

theorem dyadic_upper_cover {S v : ℝ} (hv : 0 < v) (hvs : v ≤ S) :
    S ≤ dyadicScale v (Nat.ceil (Real.log (S / v) / Real.log 2)) := by
  have hratio : 1 ≤ S / v := (le_div_iff₀ hv).2 (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (S / v) := Real.log_nonneg hratio
  let q : ℝ := Real.log (S / v) / Real.log 2
  have hq : 0 ≤ q := div_nonneg hlog hlog2.le
  have hceil : q ≤ (Nat.ceil q : ℝ) := by exact_mod_cast Nat.le_ceil q
  have hpowlog : Real.log ((2 : ℝ) ^ Nat.ceil q) =
      (Nat.ceil q : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlogle : Real.log (S / v) ≤ Real.log ((2 : ℝ) ^ Nat.ceil q) := by
    calc
      Real.log (S / v) = q * Real.log 2 := by
        dsimp [q]
        exact (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ (Nat.ceil q : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hceil hlog2.le
      _ = Real.log ((2 : ℝ) ^ Nat.ceil q) := hpowlog.symm
  have hquot : S / v ≤ (2 : ℝ) ^ Nat.ceil q :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlogle
  have hmul : S ≤ (2 : ℝ) ^ Nat.ceil q * v := (div_le_iff₀ hv).mp hquot
  simpa [dyadicScale, q, mul_comm] using hmul

theorem dyadic_count_bound {S v : ℝ} (hv : 0 < v) (hvs : v ≤ S) :
    ((Nat.ceil (Real.log (S / v) / Real.log 2) + 1 : ℕ) : ℝ) ≤
      Real.log (S / v) / Real.log 2 + 2 := by
  have hratio : 1 ≤ S / v := (le_div_iff₀ hv).2 (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (S / v) := Real.log_nonneg hratio
  have hq : 0 ≤ Real.log (S / v) / Real.log 2 := div_nonneg hlog hlog2.le
  have hceil := Nat.ceil_lt_add_one hq
  push_cast
  linarith

theorem reciprocal_le_dyadicSum {a v : ℝ} {N : ℕ} (hv : 0 < v)
    (ha : 0 ≤ a) (hcover : a ≤ dyadicScale v N) :
    (max a v)⁻¹ ≤
      ∑ i ∈ Finset.range (N + 1),
        (2 / dyadicScale v i) * (if a ≤ dyadicScale v i then 1 else 0) := by
  classical
  let P : ℕ → Prop := fun n => a ≤ dyadicScale v n
  have hP : ∃ n, P n := ⟨N, hcover⟩
  let k := Nat.find hP
  have hk : P k := Nat.find_spec hP
  have hmin : ∀ m < k, ¬ P m := by
    intro m hmk hPm
    have hkm : k ≤ m := Nat.find_min' hP hPm
    omega
  have hkN : k ≤ N := by
    by_contra h
    have hNk : N < k := Nat.lt_of_not_ge h
    exact (hmin N hNk) hcover
  have hkmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkN)
  have hterm_nonneg : ∀ i ∈ Finset.range (N + 1),
      0 ≤ (2 / dyadicScale v i) * (if a ≤ dyadicScale v i then 1 else 0) := by
    intro i hi
    apply mul_nonneg (div_nonneg (by norm_num) (dyadicScale_pos hv i).le)
    split_ifs <;> norm_num
  have hsum : (2 / dyadicScale v k) ≤
      ∑ i ∈ Finset.range (N + 1),
        (2 / dyadicScale v i) * (if a ≤ dyadicScale v i then 1 else 0) := by
    have hk' : a ≤ dyadicScale v k := hk
    calc
      2 / dyadicScale v k =
          (2 / dyadicScale v k) * (if a ≤ dyadicScale v k then 1 else 0) := by
            simp only [if_pos hk', mul_one]
      _ ≤ _ := Finset.single_le_sum hterm_nonneg hkmem
  by_cases hk0 : k = 0
  · subst k
    have hkZero : P 0 := by simpa [hk0] using hk
    have hav : a ≤ v := by simpa [P, dyadicScale] using hkZero
    rw [max_eq_right hav]
    have hcoeff : v⁻¹ ≤ 2 / v := by
      rw [← one_div]
      exact (div_le_div_iff₀ hv hv).2 (by nlinarith)
    have hsumZero : 2 / v ≤
        ∑ i ∈ Finset.range (N + 1),
          (2 / dyadicScale v i) * (if a ≤ dyadicScale v i then 1 else 0) := by
      simpa [hk0, dyadicScale] using hsum
    exact hcoeff.trans hsumZero
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hprevnot : ¬ a ≤ dyadicScale v (k - 1) := hmin (k - 1) (Nat.sub_lt hkpos (by norm_num))
    have hprev : dyadicScale v (k - 1) < a := lt_of_not_ge hprevnot
    have hpred : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)
    have hscale : dyadicScale v k = 2 * dyadicScale v (k - 1) := by
      calc
        dyadicScale v k = v * 2 ^ k := rfl
        _ = v * 2 ^ (k - 1 + 1) := by congr 2 <;> omega
        _ = v * (2 ^ (k - 1) * 2) := by rw [pow_succ]
        _ = 2 * dyadicScale v (k - 1) := by simp [dyadicScale]; ring
    have hpow : 1 ≤ (2 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
    have hvprev : v ≤ dyadicScale v (k - 1) := by
      unfold dyadicScale
      calc
        v = v * 1 := by ring
        _ ≤ v * 2 ^ (k - 1) := mul_le_mul_of_nonneg_left hpow hv.le
    have hva : v ≤ a := hvprev.trans hprev.le
    have ha_pos : 0 < a := hv.trans_le hva
    have hscale_pos := dyadicScale_pos hv k
    have hscale_lt : dyadicScale v k < 2 * a := by rw [hscale]; nlinarith
    have hcoeff : a⁻¹ ≤ 2 / dyadicScale v k := by
      rw [← one_div]
      exact (div_le_div_iff₀ ha_pos hscale_pos).2 (by nlinarith)
    rw [max_eq_left hva]
    exact hcoeff.trans hsum

def layerTerm (v a : ℝ) (i : ℕ) : ℝ :=
  (2 / dyadicScale v i) * (if a ≤ dyadicScale v i then 1 else 0)

def layerSum (v a : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), layerTerm v a i

def layerCoefficient (v : ℝ) (i j : ℕ) : ℝ :=
  (2 / dyadicScale v i) * (2 / dyadicScale v j)

def jointEvent {X : Type} [MeasurableSpace X] (Ω : Set X) (φ₁ φ₂ : X → ℝ)
    (s₁ s₂ : ℝ) : Set X :=
  {x | x ∈ Ω ∧ |φ₁ x| ≤ s₁ ∧ |φ₂ x| ≤ s₂}

def layerProductMajorant {X : Type} [MeasurableSpace X] (Ω : Set X)
    (φ₁ φ₂ : X → ℝ) (v : ℝ) (N : ℕ) (x : X) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
    (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator
      (fun _ => ENNReal.ofReal (layerCoefficient v i j)) x

theorem layerSum_mul_eq_joint_sum {X : Type} [MeasurableSpace X] (Ω : Set X)
    (φ₁ φ₂ : X → ℝ) (v : ℝ) (N : ℕ) (x : X) (hx : x ∈ Ω) :
    layerSum v |φ₁ x| N * layerSum v |φ₂ x| N =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        layerTerm v |φ₁ x| i * layerTerm v |φ₂ x| j *
          (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator (fun _ => 1) x := by
  classical
  calc
    layerSum v |φ₁ x| N * layerSum v |φ₂ x| N =
        ∑ i ∈ Finset.range (N + 1), layerTerm v |φ₁ x| i * layerSum v |φ₂ x| N := by
          simp only [layerSum, Finset.sum_mul]
    _ = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        layerTerm v |φ₁ x| i * layerTerm v |φ₂ x| j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [layerSum, Finset.mul_sum]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h₁ : |φ₁ x| ≤ dyadicScale v i
          · by_cases h₂ : |φ₂ x| ≤ dyadicScale v j
            · simp [layerTerm, jointEvent, hx, h₁, h₂]
            · simp [layerTerm, jointEvent, hx, h₁, h₂]
          · by_cases h₂ : |φ₂ x| ≤ dyadicScale v j
            · simp [layerTerm, jointEvent, hx, h₁, h₂]
            · simp [layerTerm, jointEvent, hx, h₁, h₂]

end AndersonAC.S3H

namespace AndersonAC.S3

open AndersonAC.S3H

theorem layerCake_proof : LayerCakeStatement := by
  intro X _ μ Ω φ₁ φ₂ V S v hΩ hφ₁ hφ₂ hV hv hvs hbounded hsub
  classical
  let N : ℕ := Nat.ceil (Real.log (S / v) / Real.log 2)
  let I : Finset ℕ := Finset.range (N + 1)
  let ν : Measure X := μ.restrict Ω
  have hcover : S ≤ dyadicScale v N := by
    simpa [N] using dyadic_upper_cover hv hvs
  have hcount : ((N + 1 : ℕ) : ℝ) ≤ Real.log (S / v) / Real.log 2 + 2 := by
    simpa [N] using dyadic_count_bound hv hvs
  have hEventMeas : ∀ i j, MeasurableSet (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) := by
    intro i j
    exact hΩ.inter ((measurableSet_le hφ₁.abs measurable_const).inter
      (measurableSet_le hφ₂.abs measurable_const))
  have hmajorantMeas : Measurable (layerProductMajorant Ω φ₁ φ₂ v N) := by
    unfold layerProductMajorant
    apply Finset.measurable_fun_sum
    intro i hi
    apply Finset.measurable_fun_sum
    intro j hj
    exact measurable_const.indicator (hEventMeas i j)
  have hpointwise : ∀ x ∈ Ω,
      ENNReal.ofReal ((max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹) ≤
        layerProductMajorant Ω φ₁ φ₂ v N x := by
    intro x hxΩ
    have hxBound := hbounded x hxΩ
    have hrec₁ : (max |φ₁ x| v)⁻¹ ≤ layerSum v |φ₁ x| N := by
      have h := reciprocal_le_dyadicSum hv (abs_nonneg _) (hxBound.1.trans hcover)
      simpa [layerSum, layerTerm] using h
    have hrec₂ : (max |φ₂ x| v)⁻¹ ≤ layerSum v |φ₂ x| N := by
      have h := reciprocal_le_dyadicSum hv (abs_nonneg _) (hxBound.2.trans hcover)
      simpa [layerSum, layerTerm] using h
    have hrec₁_nonneg : 0 ≤ (max |φ₁ x| v)⁻¹ :=
      inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hv (le_max_right _ _)))
    have hrec₂_nonneg : 0 ≤ (max |φ₂ x| v)⁻¹ :=
      inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hv (le_max_right _ _)))
    have hsum₁_nonneg : 0 ≤ layerSum v |φ₁ x| N := by
      unfold layerSum
      apply Finset.sum_nonneg
      intro i hi
      unfold layerTerm
      apply mul_nonneg (div_nonneg (by norm_num) (dyadicScale_pos hv i).le)
      split_ifs <;> norm_num
    have hmul := mul_le_mul hrec₁ hrec₂ hrec₂_nonneg hsum₁_nonneg
    have hconvert : ENNReal.ofReal (layerSum v |φ₁ x| N * layerSum v |φ₂ x| N) =
        layerProductMajorant Ω φ₁ φ₂ v N x := by
      have hterm_nonneg : ∀ i ∈ I, ∀ j ∈ I,
          0 ≤ layerTerm v |φ₁ x| i * layerTerm v |φ₂ x| j *
            (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator (fun _ => 1) x := by
        intro i hi j hj
        by_cases hA : x ∈ jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)
        · rcases hA with ⟨hxΩ', ⟨h₁, h₂⟩⟩
          have hI : (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator
              (fun _ => (1 : ℝ)) x = 1 := by
            simp [Set.indicator, jointEvent, hxΩ', h₁, h₂]
          rw [hI]
          unfold layerTerm
          simp only [if_pos h₁, if_pos h₂, mul_one]
          exact mul_nonneg
            (div_nonneg (by norm_num) (dyadicScale_pos hv i).le)
            (div_nonneg (by norm_num) (dyadicScale_pos hv j).le)
        · simp [Set.indicator, hA]
      have hterm_eq : ∀ i ∈ I, ∀ j ∈ I,
          ENNReal.ofReal (layerTerm v |φ₁ x| i * layerTerm v |φ₂ x| j *
            (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator (fun _ => 1) x) =
          (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator
            (fun _ => ENNReal.ofReal (layerCoefficient v i j)) x := by
        intro i hi j hj
        by_cases hA : x ∈ jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)
        · rcases hA with ⟨hxΩ', ⟨h₁, h₂⟩⟩
          simp [Set.indicator, jointEvent, hxΩ', layerTerm, layerCoefficient, h₁, h₂]
        · simp [Set.indicator, hA]
      calc
        ENNReal.ofReal (layerSum v |φ₁ x| N * layerSum v |φ₂ x| N) =
            ENNReal.ofReal
              (∑ i ∈ I, ∑ j ∈ I,
                layerTerm v |φ₁ x| i * layerTerm v |φ₂ x| j *
                  (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator (fun _ => 1) x) := by
                    congr 1
                    exact layerSum_mul_eq_joint_sum Ω φ₁ φ₂ v N x hxΩ
        _ = ∑ i ∈ I, ∑ j ∈ I,
              ENNReal.ofReal (layerTerm v |φ₁ x| i * layerTerm v |φ₂ x| j *
                (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)).indicator (fun _ => 1) x) := by
              rw [ENNReal.ofReal_sum_of_nonneg (fun i hi =>
                Finset.sum_nonneg (fun j hj => hterm_nonneg i hi j hj))]
              apply Finset.sum_congr rfl
              intro i hi
              rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => hterm_nonneg i hi j hj)]
        _ = layerProductMajorant Ω φ₁ φ₂ v N x := by
              unfold layerProductMajorant
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              exact hterm_eq i hi j hj
    calc
      ENNReal.ofReal ((max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹) ≤
          ENNReal.ofReal (layerSum v |φ₁ x| N * layerSum v |φ₂ x| N) :=
            ENNReal.ofReal_le_ofReal hmul
      _ = layerProductMajorant Ω φ₁ φ₂ v N x := hconvert
  have htermBound : ∀ i ∈ I, ∀ j ∈ I,
      ENNReal.ofReal (layerCoefficient v i j) * ν
        (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) ≤ ENNReal.ofReal (4 * V) := by
    intro i hi j hj
    have hsi := dyadicScale_pos hv i
    have hsj := dyadicScale_pos hv j
    have hμA : ν (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) ≤
        ENNReal.ofReal (V * dyadicScale v i * dyadicScale v j) := by
      calc
        ν (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) ≤
            μ (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) :=
              Measure.restrict_apply_le Ω _
        _ ≤ _ := by
          simpa [jointEvent] using hsub (dyadicScale v i) (dyadicScale v j) hsi hsj
    have hc : 0 ≤ layerCoefficient v i j := by
      exact mul_nonneg (div_nonneg (by norm_num) hsi.le) (div_nonneg (by norm_num) hsj.le)
    calc
      ENNReal.ofReal (layerCoefficient v i j) * ν
          (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) ≤
        ENNReal.ofReal (layerCoefficient v i j) * ENNReal.ofReal
          (V * dyadicScale v i * dyadicScale v j) := by gcongr
      _ = ENNReal.ofReal (4 * V) := by
        rw [← ENNReal.ofReal_mul hc]
        congr 1
        dsimp [layerCoefficient]
        field_simp [ne_of_gt hsi, ne_of_gt hsj]
        <;> ring
  have hsumIntegral :
      (∫⁻ x, layerProductMajorant Ω φ₁ φ₂ v N x ∂ν) =
        ∑ i ∈ I, ∑ j ∈ I,
          ENNReal.ofReal (layerCoefficient v i j) *
            ν (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) := by
    unfold layerProductMajorant
    rw [lintegral_finsetSum I (fun i hi => Finset.measurable_fun_sum I (fun j hj =>
      measurable_const.indicator (hEventMeas i j)))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_finsetSum I (fun j hj => measurable_const.indicator (hEventMeas i j))]
    apply Finset.sum_congr rfl
    intro j hj
    exact lintegral_indicator_const (hEventMeas i j) _
  have hsumBound :
      ∑ i ∈ I, ∑ j ∈ I,
          ENNReal.ofReal (layerCoefficient v i j) *
            ν (jointEvent Ω φ₁ φ₂ (dyadicScale v i) (dyadicScale v j)) ≤
        ∑ i ∈ I, ∑ j ∈ I, ENNReal.ofReal (4 * V) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact htermBound i hi j hj
  have hsumConst :
      ∑ i ∈ I, ∑ j ∈ I, ENNReal.ofReal (4 * V) =
        ENNReal.ofReal (4 * V * ((N + 1 : ℝ) ^ 2)) := by
    calc
      ∑ i ∈ I, ∑ j ∈ I, ENNReal.ofReal (4 * V) =
          ((N + 1 : ℕ) : ℝ≥0∞) * (((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (4 * V)) := by
            simp [I, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal (4 * V * ((N + 1 : ℝ) ^ 2)) := by
            rw [← ENNReal.ofReal_natCast (N + 1)]
            rw [← ENNReal.ofReal_mul (by positivity)]
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            push_cast
            ring
  have hreal : 4 * V * ((N + 1 : ℝ) ^ 2) ≤
      16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 := by
    have hcount' : (N : ℝ) + 1 ≤ Real.log (S / v) / Real.log 2 + 2 := by
      simpa using hcount
    have hcount_nonneg : 0 ≤ (N + 1 : ℝ) := by positivity
    have hlog_nonneg : 0 ≤ Real.log (S / v) / Real.log 2 + 2 := by
      have hratio : 1 ≤ S / v := (le_div_iff₀ hv).2 (by linarith)
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact add_nonneg (div_nonneg (Real.log_nonneg hratio) hlog2.le) (by norm_num)
    have hsquare : ((N + 1 : ℝ) ^ 2) ≤ (Real.log (S / v) / Real.log 2 + 2) ^ 2 :=
      (sq_le_sq₀ hcount_nonneg hlog_nonneg).2 (by simpa using hcount')
    calc
      4 * V * ((N + 1 : ℝ) ^ 2) ≤ 4 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ ≤ 16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2 := by
        have hsq_nonneg : 0 ≤ (Real.log (S / v) / Real.log 2 + 2) ^ 2 := sq_nonneg _
        nlinarith [mul_nonneg hV hsq_nonneg]
  calc
    ∫⁻ x in Ω, ENNReal.ofReal ((max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹) ∂μ =
        ∫⁻ x, ENNReal.ofReal ((max |φ₁ x| v)⁻¹ * (max |φ₂ x| v)⁻¹) ∂ν := rfl
    _ ≤ ∫⁻ x, layerProductMajorant Ω φ₁ φ₂ v N x ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hΩ] with x hxΩ
      exact hpointwise x hxΩ
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, ENNReal.ofReal (4 * V) := by
      rw [hsumIntegral]
      exact hsumBound
    _ = ENNReal.ofReal (4 * V * ((N + 1 : ℝ) ^ 2)) := hsumConst
    _ ≤ ENNReal.ofReal (16 * V * (Real.log (S / v) / Real.log 2 + 2) ^ 2) :=
      ENNReal.ofReal_le_ofReal hreal

end AndersonAC.S3

