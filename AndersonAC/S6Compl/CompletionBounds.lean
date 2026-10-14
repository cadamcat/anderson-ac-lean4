import AndersonAC.S6.CompletionBoundsStatement
import AndersonAC.S6.Supported

/-! Transport the supported-change estimates through the damping relation. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

private theorem completion_ds_entry {R : Type*} [Fintype R] [DecidableEq R]
    (p : R → ℝ) (dg ds : Matrix R R ℂ) (t : ℝ)
    (hrel : ds = (2 * Complex.I * (t : ℂ)) •
      (AndersonAC.S6.sqrtDamping p * dg * AndersonAC.S6.sqrtDamping p))
    (i j : R) :
    ds i j = (2 * Complex.I * (t : ℂ)) *
      ((Real.sqrt (p i) : ℂ) * dg i j * (Real.sqrt (p j) : ℂ)) := by
  rw [hrel]
  simp [AndersonAC.S6.sqrtDamping, Matrix.smul_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]

private theorem completion_ds_norm_entry {R : Type*} [Fintype R] [DecidableEq R]
    (p : R → ℝ) (dg ds : Matrix R R ℂ) (t : ℝ) (ht : 0 < t)
    (hrel : ds = (2 * Complex.I * (t : ℂ)) •
      (AndersonAC.S6.sqrtDamping p * dg * AndersonAC.S6.sqrtDamping p))
    (i j : R) :
    ‖ds i j‖ = 2 * t * Real.sqrt (p i) * Real.sqrt (p j) * ‖dg i j‖ := by
  rw [completion_ds_entry p dg ds t hrel i j]
  simp [Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), abs_of_pos ht]
  ring

private theorem completion_scaled_norm_entry {R : Type*}
    (t : ℝ) (dg : Matrix R R ℂ) (i j : R) :
    ‖AndersonAC.S6.scaledInverse t dg i j‖ =
      Real.sqrt t * ‖dg i j‖ := by
  simp [AndersonAC.S6.scaledInverse, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg t)]

theorem completionBounds_proof : AndersonAC.SolS6.CompletionBoundsStatement := by
  intro B R _ _ _ _ t c l p C dg ds ht hc hl hp hds hleft hsym hrel hproj
  let A := AndersonAC.S6.scaledInverse t dg
  have hsqrt_t : Real.sqrt t * Real.sqrt t = t := by
    nlinarith [Real.sq_sqrt ht.le]
  have hsupported := AndersonAC.S6.supported_change_bounds C ds hds hleft hsym
  rcases hsupported with ⟨_, hentry, hrow, hhs⟩

  have hrootprod (i j : R) :
      c ≤ Real.sqrt (p i) * Real.sqrt (p j) := by
    have hri : Real.sqrt c ≤ Real.sqrt (p i) := Real.sqrt_le_sqrt (hp i)
    have hrj : Real.sqrt c ≤ Real.sqrt (p j) := Real.sqrt_le_sqrt (hp j)
    calc c = Real.sqrt c * Real.sqrt c := by
          nlinarith [Real.sq_sqrt hc.le]
      _ ≤ Real.sqrt (p i) * Real.sqrt (p j) :=
        mul_le_mul hri hrj (Real.sqrt_nonneg c) (Real.sqrt_nonneg (p i))

  have hweight_nonneg (i : R) : 0 ≤ AndersonAC.S6.projectionWeight C i :=
    (AndersonAC.S6.projection_coordinate C i).1
  have hds_small (i j : R) : ‖ds i j‖ ≤ 4 * l := by
    have hprod : AndersonAC.S6.projectionWeight C i *
        AndersonAC.S6.projectionWeight C j ≤ (2 * l) ^ 2 := by
      calc AndersonAC.S6.projectionWeight C i * AndersonAC.S6.projectionWeight C j
          ≤ (2 * l) * (2 * l) :=
            mul_le_mul (hproj i) (hproj j) (hweight_nonneg j) (by positivity)
        _ = (2 * l) ^ 2 := by ring
    have hsqrt : Real.sqrt (AndersonAC.S6.projectionWeight C i *
        AndersonAC.S6.projectionWeight C j) ≤ 2 * l := by
      calc Real.sqrt (AndersonAC.S6.projectionWeight C i *
            AndersonAC.S6.projectionWeight C j)
          ≤ Real.sqrt ((2 * l) ^ 2) := Real.sqrt_le_sqrt hprod
        _ = 2 * l := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖ds i j‖ ≤ 2 * Real.sqrt
          (AndersonAC.S6.projectionWeight C i * AndersonAC.S6.projectionWeight C j) :=
            hentry i j
      _ ≤ 2 * (2 * l) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = 4 * l := by ring

  have hdg_bound (i j : R) : ‖dg i j‖ ≤ 2 * l / (t * c) := by
    have hnorm := completion_ds_norm_entry p dg ds t ht hrel i j
    have hcoeff : 2 * t * c ≤ 2 * t * Real.sqrt (p i) * Real.sqrt (p j) := by
      calc 2 * t * c = (2 * t) * c := by ring
        _ ≤ (2 * t) * (Real.sqrt (p i) * Real.sqrt (p j)) :=
          mul_le_mul_of_nonneg_left (hrootprod i j) (by positivity)
        _ = 2 * t * Real.sqrt (p i) * Real.sqrt (p j) := by ring
    have hmul := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (dg i j))
    have hmain : ‖dg i j‖ * (t * c) ≤ 2 * l := by
      nlinarith [hnorm, hmul, hds_small i j]
    exact (le_div_iff₀ (mul_pos ht hc)).2 hmain

  have hAnorm (i j : R) : ‖A i j‖ = Real.sqrt t * ‖dg i j‖ := by
    exact completion_scaled_norm_entry t dg i j

  have hden_entry_sq (i j : R) :
      (4 * t * c ^ 2) * ‖A i j‖ ^ 2 ≤ ‖ds i j‖ ^ 2 := by
    have hnormA : ‖ds i j‖ =
        (2 * Real.sqrt t * Real.sqrt (p i) * Real.sqrt (p j)) * ‖A i j‖ := by
      calc ‖ds i j‖ =
            2 * t * Real.sqrt (p i) * Real.sqrt (p j) * ‖dg i j‖ :=
              completion_ds_norm_entry p dg ds t ht hrel i j
        _ = (2 * Real.sqrt t * Real.sqrt (p i) * Real.sqrt (p j)) *
              (Real.sqrt t * ‖dg i j‖) := by
            calc 2 * t * Real.sqrt (p i) * Real.sqrt (p j) * ‖dg i j‖ =
                  2 * (Real.sqrt t * Real.sqrt t) * Real.sqrt (p i) *
                    Real.sqrt (p j) * ‖dg i j‖ := by rw [hsqrt_t]
              _ = (2 * Real.sqrt t * Real.sqrt (p i) * Real.sqrt (p j)) *
                    (Real.sqrt t * ‖dg i j‖) := by ring
        _ = _ := by rw [hAnorm]
    have hcoeff : 2 * Real.sqrt t * c ≤
        2 * Real.sqrt t * Real.sqrt (p i) * Real.sqrt (p j) := by
      calc 2 * Real.sqrt t * c = (2 * Real.sqrt t) * c := by ring
        _ ≤ (2 * Real.sqrt t) * (Real.sqrt (p i) * Real.sqrt (p j)) :=
          mul_le_mul_of_nonneg_left (hrootprod i j) (by positivity)
        _ = 2 * Real.sqrt t * Real.sqrt (p i) * Real.sqrt (p j) := by ring
    have hfactor : 2 * Real.sqrt t * c * ‖A i j‖ ≤ ‖ds i j‖ := by
      calc 2 * Real.sqrt t * c * ‖A i j‖ ≤
            (2 * Real.sqrt t * Real.sqrt (p i) * Real.sqrt (p j)) * ‖A i j‖ :=
          mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ = ‖ds i j‖ := hnormA.symm
    have hprod := mul_nonneg (sub_nonneg.mpr hfactor)
      (by positivity : 0 ≤ ‖ds i j‖ + 2 * Real.sqrt t * c * ‖A i j‖)
    have hsq : (2 * Real.sqrt t * c * ‖A i j‖) ^ 2 ≤ ‖ds i j‖ ^ 2 := by
      nlinarith [hprod]
    calc (4 * t * c ^ 2) * ‖A i j‖ ^ 2 =
          (2 * Real.sqrt t * c * ‖A i j‖) ^ 2 := by
            calc (4 * t * c ^ 2) * ‖A i j‖ ^ 2 =
                  4 * (Real.sqrt t * Real.sqrt t) * c ^ 2 * ‖A i j‖ ^ 2 := by
                    rw [hsqrt_t]
              _ = (2 * Real.sqrt t * c * ‖A i j‖) ^ 2 := by ring
      _ ≤ ‖ds i j‖ ^ 2 := hsq

  have hrow_scaled_den (i : R) :
      (4 * t * c ^ 2) * AndersonAC.S6.sqRow A i ≤
        AndersonAC.S6.sqRow ds i := by
    change (4 * t * c ^ 2) * (∑ j, ‖A i j‖ ^ 2) ≤ ∑ j, ‖ds i j‖ ^ 2
    calc (4 * t * c ^ 2) * (∑ j, ‖A i j‖ ^ 2) =
          ∑ j, (4 * t * c ^ 2) * ‖A i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ j, ‖ds i j‖ ^ 2 := Finset.sum_le_sum fun j _ => hden_entry_sq i j

  have hrow_scaled (i : R) :
      AndersonAC.S6.sqRow A i ≤ 2 * l / (t * c ^ 2) := by
    have hraw : (t * c ^ 2) * AndersonAC.S6.sqRow A i ≤ 2 * l := by
      have hupper : (4 * t * c ^ 2) * AndersonAC.S6.sqRow A i ≤ 8 * l := by
        calc (4 * t * c ^ 2) * AndersonAC.S6.sqRow A i
            ≤ AndersonAC.S6.sqRow ds i := hrow_scaled_den i
          _ ≤ 4 * AndersonAC.S6.projectionWeight C i := hrow i
          _ ≤ 8 * l := by nlinarith [hproj i]
      nlinarith [hupper]
    exact (le_div_iff₀ (mul_pos ht (sq_pos_of_pos hc))).2 (by
      simpa [mul_comm] using hraw)

  have hentry_scaled_sq (i j : R) :
      ‖A i j‖ ^ 2 ≤ 4 * l ^ 2 / (t * c ^ 2) := by
    have hbound_nonneg : 0 ≤ 2 * l / (t * c) :=
      div_nonneg (by positivity) (le_of_lt (mul_pos ht hc))
    have hpow : ‖dg i j‖ ^ 2 ≤ (2 * l / (t * c)) ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr (hdg_bound i j))
        (by positivity : 0 ≤ 2 * l / (t * c) + ‖dg i j‖)
      nlinarith [hprod]
    have hscale : ‖A i j‖ ^ 2 = t * ‖dg i j‖ ^ 2 := by
      calc ‖A i j‖ ^ 2 = (Real.sqrt t * ‖dg i j‖) ^ 2 := by rw [hAnorm]
        _ = Real.sqrt t ^ 2 * ‖dg i j‖ ^ 2 := by ring
        _ = t * ‖dg i j‖ ^ 2 := by rw [Real.sq_sqrt ht.le]
    have halg : t * (2 * l / (t * c)) ^ 2 = 4 * l ^ 2 / (t * c ^ 2) := by
      field_simp [ne_of_gt ht, ne_of_gt hc]
      <;> ring
    calc ‖A i j‖ ^ 2 = t * ‖dg i j‖ ^ 2 := hscale
      _ ≤ t * (2 * l / (t * c)) ^ 2 :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt ht)
      _ = 4 * l ^ 2 / (t * c ^ 2) := halg

  have hfourth_scaled (i : R) :
      AndersonAC.S6.fourthRow A i ≤
        (4 * l ^ 2 / (t * c ^ 2)) * AndersonAC.S6.sqRow A i := by
    change (∑ j, ‖A i j‖ ^ 4) ≤
      (4 * l ^ 2 / (t * c ^ 2)) * (∑ j, ‖A i j‖ ^ 2)
    calc ∑ j, ‖A i j‖ ^ 4 ≤
          ∑ j, (4 * l ^ 2 / (t * c ^ 2)) * ‖A i j‖ ^ 2 :=
            Finset.sum_le_sum fun j _ => by
              calc ‖A i j‖ ^ 4 = ‖A i j‖ ^ 2 * ‖A i j‖ ^ 2 := by ring
                _ ≤ (4 * l ^ 2 / (t * c ^ 2)) * ‖A i j‖ ^ 2 :=
                  mul_le_mul_of_nonneg_right (hentry_scaled_sq i j) (sq_nonneg _)
      _ = (4 * l ^ 2 / (t * c ^ 2)) * (∑ j, ‖A i j‖ ^ 2) := by
        rw [Finset.mul_sum]

  have hfourth_scaled_target (i : R) :
      AndersonAC.S6.fourthRow A i ≤ 8 * l ^ 3 / (t ^ 2 * c ^ 4) := by
    have hK : 0 ≤ 4 * l ^ 2 / (t * c ^ 2) :=
      div_nonneg (by positivity) (le_of_lt (mul_pos ht (sq_pos_of_pos hc)))
    have halg : (4 * l ^ 2 / (t * c ^ 2)) * (2 * l / (t * c ^ 2)) =
        8 * l ^ 3 / (t ^ 2 * c ^ 4) := by
      field_simp [ne_of_gt ht, ne_of_gt hc]
      <;> ring
    calc AndersonAC.S6.fourthRow A i ≤
          (4 * l ^ 2 / (t * c ^ 2)) * AndersonAC.S6.sqRow A i :=
            hfourth_scaled i
      _ ≤ (4 * l ^ 2 / (t * c ^ 2)) * (2 * l / (t * c ^ 2)) :=
        mul_le_mul_of_nonneg_left (hrow_scaled i) hK
      _ = 8 * l ^ 3 / (t ^ 2 * c ^ 4) := halg

  have hhs_scaled_den :
      (4 * t * c ^ 2) * AndersonAC.S6.hsSq A ≤ AndersonAC.S6.hsSq ds := by
    change (4 * t * c ^ 2) * (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤
      ∑ i, ∑ j, ‖ds i j‖ ^ 2
    calc (4 * t * c ^ 2) * (∑ i, ∑ j, ‖A i j‖ ^ 2) =
          ∑ i, ∑ j, (4 * t * c ^ 2) * ‖A i j‖ ^ 2 := by
            simp only [Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, ‖ds i j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hden_entry_sq i j
      _ = AndersonAC.S6.hsSq ds := rfl

  have hhs_target :
      AndersonAC.S6.hsSq A ≤ (Fintype.card B : ℝ) / (t * c ^ 2) := by
    have hraw : (t * c ^ 2) * AndersonAC.S6.hsSq A ≤ (Fintype.card B : ℝ) := by
      have hupper : (4 * t * c ^ 2) * AndersonAC.S6.hsSq A ≤
          4 * (Fintype.card B : ℝ) := by
        calc (4 * t * c ^ 2) * AndersonAC.S6.hsSq A ≤
              AndersonAC.S6.hsSq ds := hhs_scaled_den
          _ ≤ 4 * (Fintype.card B : ℝ) := hhs
      nlinarith [hupper]
    exact (le_div_iff₀ (mul_pos ht (sq_pos_of_pos hc))).2 (by
      simpa [mul_comm] using hraw)

  refine ⟨hdg_bound, hrow_scaled, hfourth_scaled_target, hhs_target⟩

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.completionBounds_proof
