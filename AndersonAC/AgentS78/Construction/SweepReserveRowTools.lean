import AndersonAC.S45.LocalTransferProof

/-!
# Sweep reserve rows: generic tools

Generic sequence lemmas for `AndersonAC.AgentS78.sweepReserveRow_proof`
(`SweepReserveRow.lean`). The row-step tail (`row_step_bound`) uses `poly_row_step_bound`
and the ambient-port update identities. The supplementary fact `gamma_le_of_entry`
(the deletion coefficient is bounded by the row cap
alone, without the cumulative Schur identity) and `row_telescope` (the row half of
`scalar_records`, without its lag hypothesis).
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace AndersonAC.AgentS78resrow

open AndersonAC.S45

/-! ## Powers -/

theorem power_mul' {t : ℝ} (ht : 0 < t) (e f : ℝ) :
    power t e * power t f = power t (e + f) := (Real.rpow_add ht e f).symm

theorem power_mono' {t e f : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hef : e ≤ f) : power t (-e) ≤ power t (-f) :=
  Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)

theorem sqrt_inv_le {t B : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hB : 0 ≤ B) : B / Real.sqrt t ≤ B * power t (-1) := by
  have hsqrt_le_one : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht1
  have htsqrt : t ≤ Real.sqrt t := by
    have hmul := Real.mul_self_sqrt ht.le
    have hle : Real.sqrt t * Real.sqrt t ≤ Real.sqrt t * 1 :=
      mul_le_mul_of_nonneg_left hsqrt_le_one (Real.sqrt_nonneg _)
    rw [hmul] at hle
    simpa using hle
  have hdiv : 1 / Real.sqrt t ≤ 1 / t := one_div_le_one_div_of_le ht htsqrt
  have hdiv' : (Real.sqrt t)⁻¹ ≤ t⁻¹ := by simpa [one_div] using hdiv
  have hpow_inv : power t (-1) = t⁻¹ := by
    dsimp [power]
    rw [Real.rpow_neg ht.le, Real.rpow_one]
  rw [hpow_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hdiv' hB

/-! ## Entries -/

/-- Every entry of a state with capped fourth rows is at most `t^{1/4}`. -/
theorem entry_small {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : State ι) (ht : 0 < t) (ht1 : t ≤ 1)
    (hrow : ∀ i, s.fourthRow t Finset.univ i ≤ rowCap t) :
    ∀ i j, ‖s.h t i j‖ ≤ power t (1 / 4) := by
  intro i j
  have hfour : ‖s.h t i j‖ ^ 4 ≤ rowCap t :=
    (Finset.single_le_sum (fun k _ => pow_nonneg (norm_nonneg _) 4)
      (Finset.mem_univ j)).trans (hrow i)
  have hcap : rowCap t ≤ t := by
    calc
      rowCap t = power t (1 + delta) := rfl
      _ ≤ power t 1 := Real.rpow_le_rpow_of_exponent_ge ht ht1
        (by norm_num [delta])
      _ = t := Real.rpow_one _
  have hv : 0 ≤ power t (1 / 4) := Real.rpow_nonneg ht.le _
  have hpow : (power t (1 / 4)) ^ 4 = t := by
    dsimp [power]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hle : ‖s.h t i j‖ ^ 4 ≤ (power t (1 / 4)) ^ 4 := by rw [hpow]; exact hfour.trans hcap
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hv (by norm_num : (4 : ℕ) ≠ 0)).mp hle

theorem h_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) (ht : 0 < t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    ∀ i j : survivors x, (deleteState t s x ξ).h t i j =
      s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val := by
  intro i j
  have hsqrt : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  change (Real.sqrt t : ℂ) *
    (s.g i.val j.val - ((ξ : ℂ) + t * s.r x) * s.g i.val x * s.g x j.val /
      (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)) =
    (Real.sqrt t : ℂ) * s.g i.val j.val -
      (((ξ : ℂ) + t * s.r x) /
        ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + t * s.r x) * s.g x x))) *
        ((Real.sqrt t : ℂ) * s.g i.val x) * ((Real.sqrt t : ℂ) * s.g x j.val)
  field_simp [hden, hsqrt]

theorem quartic_difference (a b : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ‖a‖ ≤ M) (hab : ‖a - b‖ ≤ M) :
    |‖a - b‖ ^ 4 - ‖a‖ ^ 4| ≤ 4 * M ^ 3 * ‖b‖ := by
  have hdiff : |‖a - b‖ - ‖a‖| ≤ ‖b‖ := by
    simpa using abs_norm_sub_norm_le (a - b) a
  have heq : ‖a - b‖ ^ 4 - ‖a‖ ^ 4 =
      (‖a - b‖ - ‖a‖) * (‖a - b‖ + ‖a‖) * (‖a - b‖ ^ 2 + ‖a‖ ^ 2) := by ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a - b‖ + ‖a‖),
    abs_of_nonneg (by positivity : 0 ≤ ‖a - b‖ ^ 2 + ‖a‖ ^ 2)]
  have hsum : ‖a - b‖ + ‖a‖ ≤ 2 * M := by linarith
  have hsq : ‖a - b‖ ^ 2 + ‖a‖ ^ 2 ≤ 2 * M ^ 2 := by
    nlinarith [(sq_le_sq₀ (norm_nonneg _) hM).2 ha, (sq_le_sq₀ (norm_nonneg _) hM).2 hab]
  calc
    _ ≤ ‖b‖ * (2 * M) * (2 * M ^ 2) :=
      mul_le_mul (mul_le_mul hdiff hsum (by positivity) (norm_nonneg _)) hsq
        (by positivity) (by positivity)
    _ = 4 * M ^ 3 * ‖b‖ := by ring

theorem shell_poly {ι : Type*} [Fintype ι] {d : ℕ}
    {C : ℝ} {dist : ι → ι → ℝ} (hs : ShellBounds d C dist)
    {t c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1) (i : ι) :
    ∑ j, Real.exp (-c * t ^ 3 * dist i j) ≤
      (C * power c (-(d : ℝ))) * power t (-3 * (d : ℝ)) := by
  have hu : 0 < c * t ^ 3 := by positivity
  have hu1 : c * t ^ 3 ≤ 1 := by
    have ht3 : t ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ ht.le ht1 3
    nlinarith
  have hpower : power (c * t ^ 3) (-(d : ℝ)) =
      power c (-(d : ℝ)) * power t (-3 * (d : ℝ)) := by
    dsimp [power]
    rw [Real.mul_rpow hc.le (by positivity : 0 ≤ t ^ 3), ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le]
    congr 2
    ring
  have hh := hs.count (c * t ^ 3) hu hu1 i
  have hsum : (∑ j, Real.exp (-(c * t ^ 3) * dist i j)) =
      ∑ j, Real.exp (-c * t ^ 3 * dist i j) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  rw [hsum, hpower] at hh
  simpa [mul_assoc] using hh

/-! ## Ambient entries -/

section Ambient
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem amb_h_apply (a : LiveState P) (r : P → ℂ) (t : ℝ) (i j : P) :
    (a.ambient r).h t i j =
      if hi : i ∈ a.live then if hj : j ∈ a.live then
        (a.state r).h t ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := by
  by_cases hi : i ∈ a.live <;> by_cases hj : j ∈ a.live <;>
    simp [LiveState.ambient, LiveState.state, State.h, mask, pad,
      restrict, hi, hj]

theorem amb_h_norm_le (a : LiveState P) (r : P → ℂ) (t : ℝ) (M : P → P → ℝ)
    (hM0 : ∀ i j, 0 ≤ M i j)
    (hsk : ∀ i j : a.live, ‖(a.state r).h t i j‖ ≤ M i.val j.val) (i j : P) :
    ‖(a.ambient r).h t i j‖ ≤ M i j := by
  rw [amb_h_apply]
  by_cases hi : i ∈ a.live
  · by_cases hj : j ∈ a.live
    · simp only [hi, hj, ↓reduceDIte]
      exact hsk ⟨i, hi⟩ ⟨j, hj⟩
    · simp only [hi, hj, ↓reduceDIte, norm_zero]
      exact hM0 i j
  · simp only [hi, ↓reduceDIte, norm_zero]
    exact hM0 i j

theorem stepRel_amb_h_update
    {t : ℝ} {r : P → ℂ} {a b : LiveState P} {x : P} {ξ : ℝ}
    (ht : 0 < t) (ha_wf : a.g = mask a.live a.g) (hrel : StepRel t r a b x ξ)
    {i j : P} (hi : i ∈ b.live) (hj : j ∈ b.live) :
    (b.ambient r).h t i j =
      (a.ambient r).h t i j -
        gamma t (a.ambient r) x ξ * (a.ambient r).h t i x * (a.ambient r).h t x j := by
  have hi_s : i ∈ survivors x := by
    have hi' : i ∈ a.live.erase x := hrel.survivors ▸ hi
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hi', Finset.mem_univ i⟩
  have hj_s : j ∈ survivors x := by
    have hj' : j ∈ a.live.erase x := hrel.survivors ▸ hj
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hj', Finset.mem_univ j⟩
  have hamb_g : (a.ambient r).g = a.g := ha_wf.symm
  have hden_amb : 1 + ((ξ : ℂ) + t * (a.ambient r).r x) * (a.ambient r).g x x ≠ 0 := by
    rw [hamb_g]; exact hrel.denominator
  have hg_eq : (b.ambient r).g i j = (deleteState t (a.ambient r) x ξ).g ⟨i, hi_s⟩ ⟨j, hj_s⟩ := by
    have h1 : (b.ambient r).g i j = b.g i j := by
      simp [LiveState.ambient, mask, pad, restrict, Matrix.submatrix_apply, hi, hj]
    have h2 := congrFun (congrFun hrel.update i) j
    have h3 : mask b.live (fun u v => a.g u v -
        ((ξ : ℂ) + t * r x) * a.g u x * a.g x v /
          (1 + ((ξ : ℂ) + t * r x) * a.g x x)) i j =
        a.g i j - ((ξ : ℂ) + t * r x) * a.g i x * a.g x j /
          (1 + ((ξ : ℂ) + t * r x) * a.g x x) := by
      simp [mask, pad, restrict, hi, hj]; rfl
    rw [h1, h2, h3]
    dsimp [deleteState, LiveState.ambient]
    rw [← ha_wf]
  have hh_eq : (b.ambient r).h t i j =
      (deleteState t (a.ambient r) x ξ).h t ⟨i, hi_s⟩ ⟨j, hj_s⟩ := by
    change (Real.sqrt t : ℂ) * (b.ambient r).g i j =
      (Real.sqrt t : ℂ) * (deleteState t (a.ambient r) x ξ).g ⟨i, hi_s⟩ ⟨j, hj_s⟩
    rw [hg_eq]
  rw [hh_eq]
  exact h_update t (a.ambient r) x ξ ht hden_amb ⟨i, hi_s⟩ ⟨j, hj_s⟩

/-! ## The deletion coefficient from the row cap -/

/-- **`γ` from the row cap alone.** If the pivot's diagonal entry of `h` is at most `t^{1/4}`
(as the row cap gives), `|ξ| ≤ 2√t`, `‖r_x‖ ≤ Cr` and `(2 + Cr) t^{1/4} ≤ 1/2`, then the
deletion coefficient `γ = (ξ + t r_x) / (√t (1 + (ξ + t r_x) g_xx))` is at most `2 (2 + Cr)`. -/
theorem gamma_le_of_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (t Cr : ℝ) (s : State ι)
    (x : ι) (ξ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hCr : 0 ≤ Cr)
    (hhxx : ‖s.h t x x‖ ≤ power t (1 / 4)) (hr : ‖s.r x‖ ≤ Cr)
    (hξ : |ξ| ≤ 2 * Real.sqrt t) (hsmall : (2 + Cr) * power t (1 / 4) ≤ 1 / 2) :
    ‖gamma t s x ξ‖ ≤ 2 * (2 + Cr) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hts : t ≤ Real.sqrt t := by
    have h1 : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht1
    have hmul := Real.mul_self_sqrt ht.le
    nlinarith
  set a : ℂ := (ξ : ℂ) + t * s.r x with ha
  have hna : ‖a‖ ≤ Real.sqrt t * (2 + Cr) := by
    have h1 : ‖a‖ ≤ |ξ| + t * ‖s.r x‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht]
    have h2 : t * ‖s.r x‖ ≤ Real.sqrt t * Cr :=
      mul_le_mul hts hr (norm_nonneg _) hs.le
    nlinarith
  have hhg : ‖s.h t x x‖ = Real.sqrt t * ‖s.g x x‖ := by
    simp only [State.h, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have hag : ‖a * s.g x x‖ ≤ 1 / 2 := by
    rw [norm_mul]
    have h3 : ‖a‖ * ‖s.g x x‖ ≤ (2 + Cr) * ‖s.h t x x‖ := by
      rw [hhg]
      calc ‖a‖ * ‖s.g x x‖ ≤ (Real.sqrt t * (2 + Cr)) * ‖s.g x x‖ :=
            mul_le_mul_of_nonneg_right hna (norm_nonneg _)
        _ = (2 + Cr) * (Real.sqrt t * ‖s.g x x‖) := by ring
    have h4 : (2 + Cr) * ‖s.h t x x‖ ≤ (2 + Cr) * power t (1 / 4) :=
      mul_le_mul_of_nonneg_left hhxx (by linarith)
    linarith
  have hden : 1 / 2 ≤ ‖1 + a * s.g x x‖ := by
    have h1 : (1 : ℝ) ≤ ‖1 + a * s.g x x‖ + ‖a * s.g x x‖ := by
      have := norm_sub_le (1 + a * s.g x x) (a * s.g x x)
      simp only [add_sub_cancel_right, norm_one] at this
      linarith
    linarith
  have hden_pos : 0 < ‖1 + a * s.g x x‖ := by linarith
  have hg : gamma t s x ξ = a / ((Real.sqrt t : ℂ) * (1 + a * s.g x x)) := rfl
  rw [hg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    div_le_iff₀ (mul_pos hs hden_pos)]
  calc ‖a‖ ≤ Real.sqrt t * (2 + Cr) := hna
    _ = 2 * (2 + Cr) * (Real.sqrt t * (1 / 2)) := by ring
    _ ≤ 2 * (2 + Cr) * (Real.sqrt t * ‖1 + a * s.g x x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden hs.le) (by linarith)

/-! ## The row-step tail (sweep transfer `poly_row_step_bound`) -/

theorem row_step_bound {d : ℕ}
    {q : Sequence P} {t B G c : ℝ} {r : P → ℂ} {dist : P → P → ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hB : 0 < B) (hG : 0 ≤ G)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcB : c ≤ 1 / B)
    (hshell : ShellBounds d B dist)
    {k : ℕ} {x : P}
    (ha_wf : (q.state k).g = mask (q.state k).live (q.state k).g)
    (hrel : StepRel t r (q.state k) (q.state (k + 1)) x (q.scalar k))
    (hsmall : ∀ u v, ‖((q.state k).ambient r).h t u v‖ ≤ 1)
    (hdec : ∀ u v, ‖((q.state k).ambient r).h t u v‖ ≤
      B / Real.sqrt t * Real.exp (-t ^ 3 * dist u v / B))
    (hγ : ‖gamma t ((q.state k).ambient r) x (q.scalar k)‖ ≤ G)
    (cols : Finset P) (i : P) :
    |q.stepRow t r cols k i| ≤
      (4 * (1 + G) ^ 3 * G * B ^ 3 * power c (-(d : ℝ))) *
        power t (-(4 + 3 * (d : ℝ))) * Real.exp (-c * t ^ 3 * dist i x) := by
  classical
  let a := q.state k
  let b := q.state (k + 1)
  let ξ := q.scalar k
  let amb := a.ambient r
  let amb1 := b.ambient r
  have hBsimp : B / Real.sqrt t ≤ B * power t (-1) := sqrt_inv_le ht ht1 hB.le
  have hhdec (u v : P) : ‖amb.h t u v‖ ≤
      (B * power t (-1)) * Real.exp (-c * t ^ 3 * dist u v) := by
    have hexp_uv : Real.exp (-t ^ 3 * dist u v / B) ≤ Real.exp (-c * t ^ 3 * dist u v) := by
      apply Real.exp_le_exp.mpr
      have h1 : c * (t ^ 3 * dist u v) ≤ (1 / B) * (t ^ 3 * dist u v) :=
        mul_le_mul_of_nonneg_right hcB (mul_nonneg (by positivity : 0 ≤ t ^ 3) (hshell.nonneg u v))
      have h2 : -t ^ 3 * dist u v / B = -((1 / B) * (t ^ 3 * dist u v)) := by ring
      have h3 : -c * t ^ 3 * dist u v = -(c * (t ^ 3 * dist u v)) := by ring
      linarith
    exact (hdec u v).trans (mul_le_mul hBsimp hexp_uv (Real.exp_nonneg _)
      (mul_nonneg hB.le (Real.rpow_nonneg ht.le _)))
  by_cases hi : i ∈ b.live
  · have hstep_eq : q.stepRow t r cols k i =
        (∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)) / rowCap t := by
      simp [Sequence.stepRow, b, amb, amb1, a, hi]
    have hcap_pos : 0 < rowCap t := Real.rpow_pos_of_pos ht _
    rw [hstep_eq, abs_div, abs_of_pos hcap_pos]
    have hterm (j : P) (hj_mem : j ∈ cols ∩ b.live) :
        |‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4| ≤
          4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ := by
      have hj : j ∈ b.live := (Finset.mem_inter.mp hj_mem).2
      have hupd := stepRel_amb_h_update ht ha_wf hrel hi hj
      change amb1.h t i j = amb.h t i j - gamma t amb x ξ * amb.h t i x * amb.h t x j at hupd
      let d_ij := gamma t amb x ξ * amb.h t i x * amb.h t x j
      have hd_norm : ‖d_ij‖ ≤ G * (‖amb.h t i x‖ * ‖amb.h t x j‖) := by
        dsimp [d_ij]
        rw [norm_mul, norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right hγ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have hd_le_G : ‖d_ij‖ ≤ G := by
        have hprod1 : ‖amb.h t i x‖ * ‖amb.h t x j‖ ≤ 1 := by
          have := mul_le_mul (hsmall i x) (hsmall x j) (norm_nonneg _) zero_le_one
          linarith
        nlinarith
      have ha_le : ‖amb.h t i j‖ ≤ 1 + G := by linarith [hsmall i j]
      have hab_le : ‖amb.h t i j - d_ij‖ ≤ 1 + G :=
        (norm_sub_le _ _).trans (by linarith [hsmall i j, hd_le_G])
      have hq := quartic_difference (amb.h t i j) d_ij (1 + G) (by positivity) ha_le hab_le
      rw [← hupd] at hq
      exact hq.trans (by
        calc 4 * (1 + G) ^ 3 * ‖d_ij‖
            ≤ 4 * (1 + G) ^ 3 * (G * (‖amb.h t i x‖ * ‖amb.h t x j‖)) :=
              mul_le_mul_of_nonneg_left hd_norm (by positivity)
          _ = 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ := by ring)
    have hsum_le : |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)| ≤
        4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * (∑ j : P, ‖amb.h t x j‖) := by
      calc |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)|
          ≤ ∑ j ∈ cols ∩ b.live, |‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ cols ∩ b.live, 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ j : P, 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * (∑ j : P, ‖amb.h t x j‖) := by
            rw [← Finset.mul_sum]
    have hsum_xj : (∑ j : P, ‖amb.h t x j‖) ≤
        (B * power t (-1)) * ((B * power c (-(d : ℝ))) * power t (-3 * (d : ℝ))) := by
      calc (∑ j : P, ‖amb.h t x j‖)
          ≤ ∑ j : P, (B * power t (-1)) * Real.exp (-c * t ^ 3 * dist x j) :=
            Finset.sum_le_sum fun j _ => hhdec x j
        _ = (B * power t (-1)) * (∑ j : P, Real.exp (-c * t ^ 3 * dist x j)) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (shell_poly hshell ht ht1 hc hc1 x)
            (mul_nonneg hB.le (Real.rpow_nonneg ht.le _))
    have hcap_inv : 1 / rowCap t ≤ power t (-2) := by
      have h1 : 1 / rowCap t = power t (-(1 + delta)) := by
        dsimp [rowCap, power]
        rw [one_div, ← Real.rpow_neg ht.le]
      rw [h1]
      exact power_mono' ht ht1 (by norm_num [delta])
    have hpow_comb : power t (-1) * power t (-1) * power t (-3 * (d : ℝ)) *
        power t (-2) = power t (-(4 + 3 * (d : ℝ))) := by
      rw [power_mul' ht, power_mul' ht, power_mul' ht]
      congr 1; ring
    have hnum : |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)| ≤
        (4 * (1 + G) ^ 3 * G * B ^ 3 * power c (-(d : ℝ))) *
          (power t (-1) * power t (-1) * power t (-3 * (d : ℝ))) *
          Real.exp (-c * t ^ 3 * dist i x) := by
      calc |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)|
          ≤ 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * (∑ j : P, ‖amb.h t x j‖) := hsum_le
        _ ≤ (4 * (1 + G) ^ 3 * G * ((B * power t (-1)) * Real.exp (-c * t ^ 3 * dist i x))) *
            ((B * power t (-1)) * ((B * power c (-(d : ℝ))) * power t (-3 * (d : ℝ)))) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (hhdec i x) (by positivity))
            hsum_xj
            (Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (by dsimp [power]; positivity)
        _ = _ := by ring
    rw [div_eq_mul_one_div]
    calc |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)| * (1 / rowCap t)
        ≤ ((4 * (1 + G) ^ 3 * G * B ^ 3 * power c (-(d : ℝ))) *
            (power t (-1) * power t (-1) * power t (-3 * (d : ℝ))) *
            Real.exp (-c * t ^ 3 * dist i x)) * power t (-2) :=
          mul_le_mul hnum hcap_inv (by dsimp [rowCap, power]; positivity)
            (by dsimp [power]; positivity)
      _ = (4 * (1 + G) ^ 3 * G * B ^ 3 * power c (-(d : ℝ))) *
          (power t (-1) * power t (-1) * power t (-3 * (d : ℝ)) * power t (-2)) *
          Real.exp (-c * t ^ 3 * dist i x) := by ring
      _ = _ := by rw [hpow_comb]
  · simp [Sequence.stepRow, b, hi]
    dsimp [power]; positivity

/-! ## The row telescope (row half of `scalar_records`, no lag hypothesis) -/

theorem live_succ_sub {q : Sequence P} {t : ℝ} {r : P → ℂ} (hq : q.wellFormed t r) {k : ℕ}
    (hk : k < q.length) : (q.state (k + 1)).live ⊆ (q.state k).live := by
  have h := hq.2 k hk
  rcases hp : q.pivot k with _ | x
  · simp only [hp] at h; rw [h]
  · simp only [hp] at h; rw [h.survivors]; exact Finset.erase_subset _ _

theorem live_sub_of_le {q : Sequence P} {t : ℝ} {r : P → ℂ} (hq : q.wellFormed t r) :
    ∀ {k l : ℕ}, k ≤ l → l ≤ q.length → (q.state l).live ⊆ (q.state k).live := by
  intro k l hkl hl
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hkl ih => exact (live_succ_sub hq (by omega)).trans (ih (by omega))

theorem row_telescope (q : Sequence P) (t : ℝ) (r : P → ℂ) (cols : Finset P) (ht : 0 < t)
    (hq : q.wellFormed t r) (i : P) (hi : i ∈ (q.state q.length).live) :
    (∑ j ∈ cols ∩ (q.state q.length).live, ‖((q.state q.length).ambient r).h t i j‖ ^ 4) ≤
      (∑ j ∈ cols ∩ (q.state 0).live, ‖((q.state 0).ambient r).h t i j‖ ^ 4) +
        rowCap t * q.rowRecord t r cols (Finset.range q.length) i := by
  let E : ℕ → ℝ := fun k =>
    ∑ j ∈ cols ∩ (q.state k).live, ‖((q.state k).ambient r).h t i j‖ ^ 4
  have hcap : rowCap t ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hstep : ∀ k < q.length, E (k + 1) - E k ≤ rowCap t * q.stepRow t r cols k i := by
    intro k hk
    have hik : i ∈ (q.state (k + 1)).live := live_sub_of_le hq (by omega) le_rfl hi
    have hsub : cols ∩ (q.state (k + 1)).live ⊆ cols ∩ (q.state k).live :=
      Finset.inter_subset_inter le_rfl (live_succ_sub hq hk)
    have hle : (∑ j ∈ cols ∩ (q.state (k + 1)).live, ‖((q.state k).ambient r).h t i j‖ ^ 4) ≤
        E k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hrow : rowCap t * q.stepRow t r cols k i =
        (∑ j ∈ cols ∩ (q.state (k + 1)).live, ‖((q.state (k + 1)).ambient r).h t i j‖ ^ 4) -
          ∑ j ∈ cols ∩ (q.state (k + 1)).live, ‖((q.state k).ambient r).h t i j‖ ^ 4 := by
      simp only [Sequence.stepRow, hik, if_true, Finset.sum_sub_distrib]
      field_simp
    rw [hrow]
    show E (k + 1) - E k ≤ _
    simp only [E]
    linarith
  have key : ∀ k ≤ q.length, E k ≤ E 0 + rowCap t * q.rowRecord t r cols (Finset.range k) i := by
    intro k
    induction k with
    | zero => intro _; simp [Sequence.rowRecord]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hstep k (by omega)
      have e : q.rowRecord t r cols (Finset.range (k + 1)) i =
          q.rowRecord t r cols (Finset.range k) i + q.stepRow t r cols k i := by
        simp [Sequence.rowRecord, Finset.sum_range_succ, Finset.sum_apply]
      rw [e]
      linarith
  exact key q.length le_rfl

end Ambient

end AndersonAC.AgentS78resrow
