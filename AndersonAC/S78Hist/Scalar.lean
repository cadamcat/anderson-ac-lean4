import AndersonAC.S78Hist.Definitions

open Filter Asymptotics
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78hist

theorem parameters (d : ℕ) (hd : 3 ≤ d) (c : ℝ) (hc : 0 < c) :
    0 < historyAlpha d ∧ historyAlpha d < 1 ∧
    0 < historyExponent d c ∧ historyExponent d c ≤ c * historyAlpha d / 4 ∧
    historyExponent d c < historyBeta d := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hn : 0 < nu d := by unfold nu delta; positivity
  have hn1 : nu d < 1 := by
    unfold nu delta
    rw [div_lt_one (by positivity)]
    norm_num
    linarith
  have ha : 0 < historyAlpha d := by unfold historyAlpha; positivity
  have ha1 : historyAlpha d < 1 := by
    unfold historyAlpha
    rw [div_lt_one (by positivity)]
    linarith
  refine ⟨ha, ha1, lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
  have hq := min_le_right (c * historyAlpha d / 4) (nu d / 20)
  unfold historyExponent historyBeta
  linarith

theorem radius_exp (d j : ℕ) :
    witnessRadius j ^ d = Real.exp ((10 * (d : ℝ) * Real.log 4) * (j : ℝ)) := by
  rw [witnessRadius, ← pow_mul, ← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  congr 1
  push_cast
  ring

/-- A fixed linear function and a slower exponential are negligible relative
to a faster exponential. The threshold is independent of subsequent indices. -/
theorem eventually_linear_exp (a b A B K ε : ℝ) (hb : 0 < b)
    (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      A * x + B + K * Real.exp (a * x) ≤ ε * Real.exp (b * x) := by
  have hlin : (fun x : ℝ => x) =o[atTop] (fun x => Real.exp (b * x)) := by
    simpa using isLittleO_pow_exp_pos_mul_atTop 1 hb
  have hconst : (fun _ : ℝ => (1 : ℝ)) =o[atTop]
      (fun x => Real.exp (b * x)) := by
    simpa using isLittleO_pow_exp_pos_mul_atTop 0 hb
  have hexp : (fun x : ℝ => Real.exp (a * x)) =o[atTop]
      (fun x => Real.exp (b * x)) := by
    simpa using isLittleO_exp_mul_rpow_of_lt 0 hab
  have h := ((hlin.const_mul_left A).add (hconst.const_mul_left B)).add
    (hexp.const_mul_left K)
  filter_upwards [h.def hε] with x hx
  simp only [mul_one, Real.norm_eq_abs, Real.abs_exp] at hx
  exact (le_abs_self _).trans hx

theorem eventually_linear_rpow (a b A B K ε : ℝ) (hb : 0 < b)
    (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      A * x + B + K * (4 : ℝ) ^ (a * x) ≤ ε * (4 : ℝ) ^ (b * x) := by
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h := eventually_linear_exp (Real.log 4 * a) (Real.log 4 * b) A B K ε
    (mul_pos hl hb) (mul_lt_mul_of_pos_left hab hl) hε
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), mul_assoc] using h

theorem earlier_lt (d j : ℕ) (ha : historyAlpha d < 1) (hj : 0 < j) :
    historyEarlier d j < j := by
  apply (Nat.floor_lt' (Nat.ne_of_gt hj)).mpr
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  nlinarith

theorem parent_scale (d j u : ℕ) (hu : historyEarlier d j ≤ u) :
    historyAlpha d * (j : ℝ) < (u : ℝ) + 1 := by
  have h := Nat.lt_floor_add_one (historyAlpha d * (j : ℝ))
  have hu' : (historyEarlier d j : ℝ) ≤ u := by exact_mod_cast hu
  exact h.trans_le (by simpa [historyEarlier] using add_le_add_right hu' 1)

/-- Both contributions to the recursion obey a half-bound above one cutoff.
The leaf estimate uses the maximum of the cutoff and the parent index. -/
theorem scalar_bounds (d : ℕ) (hd : 3 ≤ d) (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ n₀ j, N ≤ n₀ → n₀ < j →
        C * (j : ℝ) * witnessRadius j ^ d *
          birthBound c (max n₀ (historyEarlier d j)) ≤
            birthBound (historyExponent d c) j / 2) ∧
      (∀ n₀ j z, N ≤ n₀ → n₀ < j → n₀ ≤ historyEarlier d j →
        0 ≤ z → z ≤ birthBound (historyExponent d c) (historyEarlier d j) →
        (C * witnessRadius j ^ d * z) ^ historyChildren d j ≤
          birthBound (historyExponent d c) j / 2) := by
  obtain ⟨ha, ha1, hq, hqc, hqb⟩ := parameters d hd c hc
  let α := historyAlpha d
  let q := historyExponent d c
  let β := historyBeta d
  let D := 10 * (d : ℝ) * Real.log 4
  let L := (C + D) / α
  have hC0 : 0 ≤ C := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCD : 0 ≤ C + D := add_nonneg hC0 hD
  have hleaf := eventually_linear_rpow (c / 4) c L (L + Real.log 2)
    ((4 : ℝ) ^ (c / 4)) 1 hc (by linarith) (by norm_num)
  have hentropy := eventually_linear_rpow 0 q (2 * L) (2 * L) 0 1
    hq hq (by norm_num)
  have hgain := eventually_linear_rpow q β 0 (Real.log 2) 1 (1 / 4)
    (lt_trans hq hqb) hqb (by norm_num)
  have hev : ∀ᶠ u : ℕ in atTop,
      (L * (u : ℝ) + (L + Real.log 2) +
        (4 : ℝ) ^ (c / 4) * (4 : ℝ) ^ ((c / 4) * (u : ℝ)) ≤
          (4 : ℝ) ^ (c * (u : ℝ))) ∧
      (2 * L * (u : ℝ) + 2 * L ≤ (4 : ℝ) ^ (q * (u : ℝ))) ∧
      (Real.log 2 + (4 : ℝ) ^ (q * (u : ℝ)) ≤
        (4 : ℝ) ^ (β * (u : ℝ)) / 4) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hleaf,
      tendsto_natCast_atTop_atTop.eventually hentropy,
      tendsto_natCast_atTop_atTop.eventually hgain] with u h₁ h₂ h₃
    simpa only [zero_mul, zero_add, zero_mul, add_zero, one_mul, div_eq_mul_inv,
      mul_comm (4 : ℝ)⁻¹] using And.intro h₁ (And.intro h₂ h₃)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hscale (j u : ℕ) (hu : historyEarlier d j ≤ u) :
      (C + D) * (j : ℝ) ≤ L * ((u : ℝ) + 1) := by
    have hs : (j : ℝ) ≤ ((u : ℝ) + 1) / α :=
      (le_div_iff₀ ha).mpr (by simpa [α, mul_comm] using (parent_scale d j u hu).le)
    calc
      (C + D) * (j : ℝ) ≤ (C + D) * (((u : ℝ) + 1) / α) :=
        mul_le_mul_of_nonneg_left hs hCD
      _ = L * ((u : ℝ) + 1) := by dsimp [L]; ring
  have hfac (j : ℕ) : C * (j : ℝ) * witnessRadius j ^ d ≤
      Real.exp ((C + D) * (j : ℝ)) := by
    rw [radius_exp]
    calc
      C * (j : ℝ) * Real.exp (D * (j : ℝ)) ≤
          Real.exp (C * (j : ℝ)) * Real.exp (D * (j : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      _ = Real.exp ((C + D) * (j : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  have hhalf (x : ℝ) : Real.exp (-x - Real.log 2) = Real.exp (-x) / 2 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine ⟨max 1 N, le_max_left _ _, ?_, ?_⟩
  · intro n₀ j hn₀ hj
    let u := max n₀ (historyEarlier d j)
    have huN : N ≤ u := (le_max_right 1 N).trans (hn₀.trans (le_max_left _ _))
    have hu := (hN u huN).1
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hqu : q * (j : ℝ) ≤ c * ((u : ℝ) + 1) / 4 := by
      have hs := parent_scale d j u (le_max_right _ _)
      have hqcj := mul_le_mul_of_nonneg_right hqc hj0
      dsimp [q] at *
      nlinarith
    have hpow : (4 : ℝ) ^ (c * ((u : ℝ) + 1) / 4) =
        (4 : ℝ) ^ (c / 4) * (4 : ℝ) ^ ((c / 4) * (u : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      congr 1
      ring
    have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hqu
    have hs := hscale j u (le_max_right _ _)
    have hex : (C + D) * (j : ℝ) - (4 : ℝ) ^ (c * (u : ℝ)) ≤
        -(4 : ℝ) ^ (q * (j : ℝ)) - Real.log 2 := by
      rw [hpow] at ht
      nlinarith
    calc
      C * (j : ℝ) * witnessRadius j ^ d * birthBound c u ≤
          Real.exp ((C + D) * (j : ℝ)) * birthBound c u :=
        mul_le_mul_of_nonneg_right (hfac j) (Real.exp_nonneg _)
      _ = Real.exp ((C + D) * (j : ℝ) - (4 : ℝ) ^ (c * (u : ℝ))) := by
        simp only [birthBound, sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp (-(4 : ℝ) ^ (q * (j : ℝ)) - Real.log 2) := Real.exp_le_exp.mpr hex
      _ = birthBound q j / 2 := hhalf _
  · intro n₀ j z hn₀ hj hr hz hzb
    let r := historyEarlier d j
    have hrN : N ≤ r := (le_max_right 1 N).trans (hn₀.trans hr)
    have hjN : N ≤ j := (le_max_right 1 N).trans (hn₀.trans hj.le)
    have he := (hN r hrN).2.1
    have hg := (hN j hjN).2.2
    have hs := hscale j r le_rfl
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (le_max_left 1 N).trans (hn₀.trans hj.le)
    have hf : C * witnessRadius j ^ d ≤ Real.exp ((C + D) * (j : ℝ)) := by
      apply le_trans _ (hfac j)
      apply mul_le_mul_of_nonneg_right _ (by unfold witnessRadius; positivity)
      nlinarith
    have hex : (C + D) * (j : ℝ) - (4 : ℝ) ^ (q * (r : ℝ)) ≤
        -(4 : ℝ) ^ (q * (r : ℝ)) / 2 := by nlinarith
    have hqr : 1 ≤ (4 : ℝ) ^ (q * (r : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (show 0 ≤ q * (r : ℝ) by positivity)
    have hroot : C * witnessRadius j ^ d * z ≤ Real.exp (-(1 / 2 : ℝ)) := by
      calc
        C * witnessRadius j ^ d * z ≤
            Real.exp ((C + D) * (j : ℝ)) * birthBound q r :=
          mul_le_mul hf hzb hz (Real.exp_nonneg _)
        _ = Real.exp ((C + D) * (j : ℝ) - (4 : ℝ) ^ (q * (r : ℝ))) := by
          simp only [birthBound, sub_eq_add_neg, Real.exp_add]
        _ ≤ Real.exp (-(1 / 2 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    have hqj : 1 ≤ (4 : ℝ) ^ (q * (j : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (show 0 ≤ q * (j : ℝ) by positivity)
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hk := Nat.sub_one_lt_floor ((4 : ℝ) ^ (β * (j : ℝ)))
    have hchildren : (4 : ℝ) ^ (β * (j : ℝ)) / 2 ≤ (historyChildren d j : ℝ) := by
      dsimp [historyChildren, β] at *
      linarith
    calc
      (C * witnessRadius j ^ d * z) ^ historyChildren d j ≤
          Real.exp (-(1 / 2 : ℝ)) ^ historyChildren d j :=
        pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hC0 (by unfold witnessRadius; positivity)) hz) hroot _
      _ = Real.exp (-(historyChildren d j : ℝ) / 2) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-(4 : ℝ) ^ (β * (j : ℝ)) / 4) :=
        Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(4 : ℝ) ^ (q * (j : ℝ)) - Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = birthBound q j / 2 := hhalf _

end AndersonAC.SolS78hist
