import Mathlib

noncomputable section

open scoped BigOperators

namespace AndersonAC.S6

private theorem one_add_pow_mul_exp_neg_le (m : ℕ) {a x : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) ^ m * Real.exp (-a * x) ≤
      (1 + ((m : ℝ) + 1) / a) ^ m := by
  let b : ℝ := a / ((m : ℝ) + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hmb : (m : ℝ) * b ≤ a := by
    calc
      (m : ℝ) * b ≤ ((m : ℝ) + 1) * b := by
        exact mul_le_mul_of_nonneg_right (by linarith) hb.le
      _ = a := by dsimp [b]; field_simp
  have hexp_le : Real.exp (-b * x) ≤ 1 := by
    calc
      Real.exp (-b * x) ≤ Real.exp 0 := Real.exp_monotone (by nlinarith)
      _ = 1 := Real.exp_zero
  have hlin : x * Real.exp (-b * x) ≤ b⁻¹ := by
    have h := Real.mul_exp_neg_le_exp_neg_one (b * x)
    have h' : (b * x) * Real.exp (-(b * x)) ≤ 1 := by
      calc
        (b * x) * Real.exp (-(b * x)) ≤ Real.exp (-1) := h
        _ ≤ Real.exp 0 := Real.exp_monotone (by norm_num)
        _ = 1 := Real.exp_zero
    have hm := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hb.le)
    calc
      x * Real.exp (-b * x) = b⁻¹ * ((b * x) * Real.exp (-(b * x))) := by
        field_simp [ne_of_gt hb]
        <;> ring
      _ ≤ b⁻¹ := by simpa using hm
  have hbase : (1 + x) * Real.exp (-b * x) ≤ 1 + b⁻¹ := by
    rw [add_mul, one_mul]
    exact add_le_add hexp_le hlin
  have hrem : Real.exp (-(a - (m : ℝ) * b) * x) ≤ 1 := by
    calc
      Real.exp (-(a - (m : ℝ) * b) * x) ≤ Real.exp 0 :=
        Real.exp_monotone (by nlinarith [hmb, hx])
      _ = 1 := Real.exp_zero
  have hExpProd : Real.exp (-b * x) ^ m * Real.exp (-(a - (m : ℝ) * b) * x) =
      Real.exp (-a * x) := by
    calc
      _ = Real.exp ((m : ℝ) * (-b * x) + (-(a - (m : ℝ) * b) * x)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ = Real.exp (-a * x) := by congr 1 <;> ring
  calc
    (1 + x) ^ m * Real.exp (-a * x) =
        ((1 + x) * Real.exp (-b * x)) ^ m *
          Real.exp (-(a - (m : ℝ) * b) * x) := by
            rw [← hExpProd, mul_pow]
            ring
    _ ≤ (1 + b⁻¹) ^ m * 1 := by
          exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase m) hrem
            (by positivity) (by positivity)
    _ = (1 + ((m : ℝ) + 1) / a) ^ m := by
          dsimp [b]
          congr 1
          field_simp [ne_of_gt ha]
          <;> ring

theorem exponential_shell_tail (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ K c' t0 : ℝ, 0 < K ∧ 0 < c' ∧ 0 < t0 ∧ ∀ t : ℝ, 0 < t → t < t0 →
      (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
        then (1 + (n : ℝ)) ^ (d - 1) * Real.exp (-c * t * n) else 0) ≤
          K * t ^ (-(d : ℝ)) * Real.exp (-c' * t ^ (-4 : ℤ)) := by
  let p : ℕ := d - 1
  let C : ℝ := (1 + ((p : ℝ) + 1) / (c / 4)) ^ p
  let K : ℝ := (8 / c) * C * (1 + 4 / c)
  let t0 : ℝ := min 1 (4 / c)
  refine ⟨K, c / 4, t0, ?_, ?_, ?_, ?_⟩
  · dsimp [K]
    positivity
  · positivity
  · dsimp [t0]
    positivity
  · intro t ht htt
    have ht1 : t < 1 := lt_of_lt_of_le htt (min_le_left _ _)
    have httsmall' : t < 4 / c :=
      lt_of_lt_of_le htt (min_le_right _ _)
    have hprod' : c * t / 4 < 1 := by
      have hx := (lt_div_iff₀ hc).mp httsmall'
      nlinarith
    have hx : 0 < c * t / 4 := by positivity
    have hxle : c * t / 4 ≤ 1 := hprod'.le
    let x : ℝ := c * t / 4
    have hxpos : 0 < x := by dsimp [x]; positivity
    have hxle' : x ≤ 1 := by simpa [x] using hxle
    have hbaseexp : 1 + x ≤ Real.exp x := by
      simpa [add_comm] using Real.add_one_le_exp x
    have hinvexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
      have h := (inv_le_inv₀ (by positivity : 0 < Real.exp x) (by positivity : 0 < 1 + x)).2 hbaseexp
      simpa [Real.exp_neg] using h
    have hfrac : x / 2 ≤ 1 - (1 + x)⁻¹ := by
      have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by
        field_simp
        <;> ring
      rw [heq]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : 0 < 1 + x)]
      have hsmall : 1 + x ≤ 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsmall hxpos.le
      nlinarith
    have hgap : x / 2 ≤ 1 - Real.exp (-x) := by linarith
    have hgap_pos : 0 < 1 - Real.exp (-x) := by
      have : 0 < x / 2 := by positivity
      linarith
    have hgeomBound : (1 - Real.exp (-x))⁻¹ ≤ 8 / (c * t) := by
      have hInv := (inv_le_inv₀ hgap_pos (by positivity : 0 < x / 2)).2 hgap
      have hsimple : (x / 2)⁻¹ = 8 / (c * t) := by
        dsimp [x]
        field_simp [ne_of_gt hc, ne_of_gt ht]
        <;> ring
      rw [hsimple] at hInv
      exact hInv
    have hcut_mul (n : ℕ) (hn : t ^ (-5 : ℤ) ≤ (n : ℝ)) :
        t ^ (-4 : ℤ) ≤ t * (n : ℝ) := by
      have hpow5 : t ^ (-5 : ℤ) = (t ^ 5)⁻¹ := by
        norm_num [zpow_neg, zpow_natCast]
      have hpow4 : t ^ (-4 : ℤ) = (t ^ 4)⁻¹ := by
        norm_num [zpow_neg, zpow_natCast]
      have hmul : t * t ^ (-5 : ℤ) = t ^ (-4 : ℤ) := by
        rw [hpow5, hpow4]
        field_simp [ne_of_gt ht]
        <;> ring
      have h := mul_le_mul_of_nonneg_left hn ht.le
      rw [hmul] at h
      exact h
    have hpoly (n : ℕ) :
        (1 + (n : ℝ)) ^ p * Real.exp (-(c * t * n) / 2) ≤
          (t⁻¹) ^ p * C * Real.exp (-(c * t * n) / 4) := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have htbase : 1 + (n : ℝ) ≤ t⁻¹ * (1 + t * n) := by
        have hmul : t * (1 + (n : ℝ)) ≤ 1 + t * n := by nlinarith
        calc
          1 + (n : ℝ) = (t * (1 + (n : ℝ))) * t⁻¹ := by
            field_simp [ne_of_gt ht]
          _ ≤ (1 + t * n) * t⁻¹ := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr ht.le)
          _ = t⁻¹ * (1 + t * n) := by ring
      have hscale : (1 + (n : ℝ)) ^ p ≤ (t⁻¹) ^ p * (1 + t * n) ^ p := by
        calc
          (1 + (n : ℝ)) ^ p ≤ (t⁻¹ * (1 + t * n)) ^ p := by gcongr
          _ = (t⁻¹) ^ p * (1 + t * n) ^ p := by rw [mul_pow]
      have habsorb := one_add_pow_mul_exp_neg_le p (by positivity : 0 < c / 4)
        (mul_nonneg ht.le hn)
      have habsorb' : (1 + t * n) ^ p * Real.exp (-(c * t * n) / 4) ≤ C := by
        dsimp [C]
        convert habsorb using 1 <;> congr 1 <;> ring
      have hsplit : Real.exp (-(c * t * n) / 2) =
          Real.exp (-(c * t * n) / 4) * Real.exp (-(c * t * n) / 4) := by
        rw [← Real.exp_add]
        congr 1
        <;> ring
      calc
        (1 + (n : ℝ)) ^ p * Real.exp (-(c * t * n) / 2)
            ≤ ((t⁻¹) ^ p * (1 + t * n) ^ p) * Real.exp (-(c * t * n) / 2) :=
                mul_le_mul_of_nonneg_right hscale (by positivity)
        _ = (t⁻¹) ^ p * ((1 + t * n) ^ p * Real.exp (-(c * t * n) / 4)) *
              Real.exp (-(c * t * n) / 4) := by rw [hsplit]; ring
        _ ≤ (t⁻¹) ^ p * C * Real.exp (-(c * t * n) / 4) := by
              have h := mul_le_mul_of_nonneg_left habsorb' (by positivity : 0 ≤ (t⁻¹) ^ p)
              calc
                _ ≤ ((t⁻¹) ^ p * C) * Real.exp (-(c * t * n) / 4) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact h
                _ = _ := by ring
    let outer : ℝ := Real.exp (-(c / 2) * t ^ (-4 : ℤ))
    have hcutExp (n : ℕ) (hn : t ^ (-5 : ℤ) ≤ (n : ℝ)) :
        Real.exp (-(c * t * n) / 2) ≤ outer := by
      dsimp [outer]
      apply Real.exp_monotone
      have h := mul_le_mul_of_nonneg_left (hcut_mul n hn) (by positivity : 0 ≤ c / 2)
      nlinarith
    let geo : ℕ → ℝ := fun n => Real.exp (-(c * t / 4) * (n : ℝ))
    have hqpos : 0 ≤ Real.exp (-(c * t / 4)) := Real.exp_nonneg _
    have hqlt : Real.exp (-(c * t / 4)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_lt_zero.mpr (by positivity)
    have hgeo : Summable geo := by
      apply (summable_geometric_of_lt_one hqpos hqlt).congr
      intro n
      dsimp [geo]
      calc
        (Real.exp (-(c * t / 4))) ^ n =
            Real.exp ((n : ℝ) * (-(c * t / 4)) : ℝ) := by rw [Real.exp_nat_mul]
        _ = Real.exp (-(c * t / 4) * (n : ℝ)) := by congr 1 <;> ring
    have hqsum : (∑' n : ℕ, geo n) = (1 - Real.exp (-(c * t / 4)))⁻¹ := by
      dsimp [geo]
      calc
        (∑' n : ℕ, Real.exp (-(c * t / 4) * (n : ℝ))) =
            ∑' n : ℕ, (Real.exp (-(c * t / 4))) ^ n := by
              apply tsum_congr
              intro n
              calc
                Real.exp (-(c * t / 4) * (n : ℝ)) = Real.exp ((n : ℝ) * (-(c * t / 4))) := by
                  congr 1
                  ring
                _ = (Real.exp (-(c * t / 4))) ^ n := by rw [Real.exp_nat_mul]
        _ = (1 - Real.exp (-(c * t / 4)))⁻¹ := tsum_geometric_of_lt_one hqpos hqlt
    have hsum_dom :
        (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
          then (1 + (n : ℝ)) ^ p * Real.exp (-c * t * n) else 0) ≤
          ((t⁻¹) ^ p * C * outer) * (8 / (c * t)) := by
      let f : ℕ → ℝ := fun n => if t ^ (-5 : ℤ) ≤ (n : ℝ)
        then (1 + (n : ℝ)) ^ p * Real.exp (-c * t * n) else 0
      let g : ℕ → ℝ := fun n => ((t⁻¹) ^ p * C * outer) * geo n
      have hfg : ∀ n, f n ≤ g n := by
        intro n
        by_cases hn : t ^ (-5 : ℤ) ≤ (n : ℝ)
        · dsimp [f, g, geo]
          rw [if_pos hn]
          have hsplit : Real.exp (-c * t * n) =
              Real.exp (-(c * t * n) / 2) * Real.exp (-(c * t * n) / 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hsplit]
          calc
            (1 + (n : ℝ)) ^ p *
                (Real.exp (-(c * t * n) / 2) * Real.exp (-(c * t * n) / 2))
                = ((1 + (n : ℝ)) ^ p * Real.exp (-(c * t * n) / 2)) *
                    Real.exp (-(c * t * n) / 2) := by ring
            _ ≤ ((t⁻¹) ^ p * C * Real.exp (-(c * t * n) / 4)) * outer :=
                  mul_le_mul (hpoly n) (hcutExp n hn) (by positivity) (by positivity)
            _ = ((t⁻¹) ^ p * C * outer) * Real.exp (-(c * t / 4) * (n : ℝ)) := by
                  have heq : -(c * t * (n : ℝ)) / 4 = -(c * t / 4) * (n : ℝ) := by ring
                  rw [heq]
                  ring
        · dsimp [f, g]
          rw [if_neg hn]
          positivity
      have hgsummable : Summable g := by
        dsimp [g]
        exact hgeo.mul_left ((t⁻¹) ^ p * C * outer)
      have hfsummable : Summable f :=
        Summable.of_nonneg_of_le (fun n => by
          dsimp [f]
          split_ifs <;> positivity) hfg hgsummable
      have hle := hfsummable.tsum_le_tsum hfg hgsummable
      dsimp [f, g] at hle ⊢
      calc
        (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
          then (1 + (n : ℝ)) ^ p * Real.exp (-c * t * n) else 0)
            = ∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
                then (1 + (n : ℝ)) ^ p * Real.exp (-c * t * n) else 0 := rfl
        _ ≤ ∑' n : ℕ, ((t⁻¹) ^ p * C * outer) * geo n := hle
        _ = ((t⁻¹) ^ p * C * outer) * (∑' n : ℕ, geo n) := tsum_mul_left
        _ = ((t⁻¹) ^ p * C * outer) * (1 - Real.exp (-(c * t / 4)))⁻¹ := by rw [hqsum]
        _ ≤ ((t⁻¹) ^ p * C * outer) * (8 / (c * t)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hh := hgeomBound
              dsimp [x] at hh
              exact hh
    have hsum_main :
        (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
          then (1 + (n : ℝ)) ^ (d - 1) * Real.exp (-c * t * n) else 0) ≤
          (8 / c) * C * (t⁻¹) ^ (p + 1) * outer := by
      have hmain :
          (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
            then (1 + (n : ℝ)) ^ p * Real.exp (-c * t * n) else 0) ≤
            ((t⁻¹) ^ p * C * outer) * (8 / (c * t)) := hsum_dom
      calc
        _ = ∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
              then (1 + (n : ℝ)) ^ p * Real.exp (-c * t * n) else 0 := rfl
        _ ≤ ((t⁻¹) ^ p * C * outer) * (8 / (c * t)) := hmain
        _ = (8 / c) * C * (t⁻¹) ^ (p + 1) * outer := by
              have hdiv : 8 / (c * t) = (8 / c) * t⁻¹ := by
                field_simp [ne_of_gt hc, ne_of_gt ht]
              rw [hdiv]
              calc
                ((t⁻¹) ^ p * C * outer) * ((8 / c) * t⁻¹) =
                    (8 / c) * C * ((t⁻¹) ^ p * t⁻¹) * outer := by ring
                _ = (8 / c) * C * (t⁻¹) ^ (p + 1) * outer := by
                      rw [← pow_succ]
    by_cases hd : 0 < d
    · have hp1 : p + 1 = d := by dsimp [p]; omega
      have hrpow : t ^ (-(d : ℝ)) = (t⁻¹) ^ d := by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_pow]
      have hK : (8 / c) * C ≤ K := by
        change (8 / c) * C ≤ (8 / c) * C * (1 + 4 / c)
        have hfactor : 1 ≤ 1 + 4 / c := by
          have hp : 0 < 4 / c := by positivity
          linarith
        calc
          (8 / c) * C = (8 / c) * C * 1 := by ring
          _ ≤ (8 / c) * C * (1 + 4 / c) := by gcongr
      have hOuter : outer ≤ Real.exp (-(c / 4) * t ^ (-4 : ℤ)) := by
        dsimp [outer]
        apply Real.exp_monotone
        have hy : 0 ≤ t ^ (-4 : ℤ) := by positivity
        nlinarith
      rw [hp1] at hsum_main
      rw [hrpow]
      calc
        _ ≤ (8 / c) * C * (t⁻¹) ^ d * outer := hsum_main
        _ ≤ K * (t⁻¹) ^ d * outer := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
              exact mul_le_mul_of_nonneg_right hK (by positivity)
        _ ≤ K * (t⁻¹) ^ d * Real.exp (-(c / 4) * t ^ (-4 : ℤ)) :=
              mul_le_mul_of_nonneg_left hOuter (by positivity)
    · have hd0 : d = 0 := by omega
      have hp0 : p = 0 := by simp [p, hd0]
      have hC0 : C = 1 := by simp [C, hp0]
      have hpow4 : t ^ (-4 : ℤ) = (t ^ 4)⁻¹ := by
        norm_num [zpow_neg, zpow_natCast]
      have ht3 : t ^ 3 ≤ 1 := by
        calc
          t ^ 3 ≤ (1 : ℝ) ^ 3 := by gcongr
          _ = 1 := by norm_num
      have ht4 : t ^ 4 ≤ t := by
        calc
          t ^ 4 = t ^ 3 * t := by ring
          _ ≤ 1 * t := mul_le_mul_of_nonneg_right ht3 ht.le
          _ = t := by ring
      have hinv4 : t⁻¹ ≤ t ^ (-4 : ℤ) := by
        rw [hpow4]
        exact (inv_le_inv₀ ht (pow_pos ht 4)).2 ht4
      have hypos : 0 < t ^ (-4 : ℤ) := by positivity
      have hyexp : t ^ (-4 : ℤ) ≤ (4 / c) *
          Real.exp ((c / 4) * t ^ (-4 : ℤ)) := by
        have harg := Real.add_one_le_exp ((c / 4) * t ^ (-4 : ℤ))
        have harg' : (c / 4) * t ^ (-4 : ℤ) ≤
            Real.exp ((c / 4) * t ^ (-4 : ℤ)) := by linarith
        have hmul := mul_le_mul_of_nonneg_left harg' (by positivity : 0 ≤ 4 / c)
        have hcancel : (4 / c) * ((c / 4) * t ^ (-4 : ℤ)) = t ^ (-4 : ℤ) := by
          field_simp [ne_of_gt hc]
          <;> ring
        calc
          t ^ (-4 : ℤ) = (4 / c) * ((c / 4) * t ^ (-4 : ℤ)) := hcancel.symm
          _ ≤ (4 / c) * Real.exp ((c / 4) * t ^ (-4 : ℤ)) := hmul
      have hAbsorb : t⁻¹ * Real.exp (-(c / 2) * t ^ (-4 : ℤ)) ≤
          (4 / c) * Real.exp (-(c / 4) * t ^ (-4 : ℤ)) := by
        calc
          t⁻¹ * Real.exp (-(c / 2) * t ^ (-4 : ℤ)) ≤
              ((4 / c) * Real.exp ((c / 4) * t ^ (-4 : ℤ))) *
                Real.exp (-(c / 2) * t ^ (-4 : ℤ)) :=
                  mul_le_mul_of_nonneg_right (hinv4.trans hyexp) (by positivity)
          _ = (4 / c) * (Real.exp ((c / 4) * t ^ (-4 : ℤ)) *
                Real.exp (-(c / 2) * t ^ (-4 : ℤ))) := by ring
          _ = (4 / c) * Real.exp (-(c / 4) * t ^ (-4 : ℤ)) := by
                rw [← Real.exp_add]
                congr 1
                <;> ring
      have hK : (8 / c) * (4 / c) ≤ K := by
        change (8 / c) * (4 / c) ≤ (8 / c) * C * (1 + 4 / c)
        rw [hC0]
        have hfactor : 4 / c ≤ 1 + 4 / c := by linarith
        calc
          (8 / c) * (4 / c) ≤ (8 / c) * (1 + 4 / c) :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = (8 / c) * 1 * (1 + 4 / c) := by ring
      have hrpow0 : t ^ (-(d : ℝ)) = 1 := by simp [hd0]
      have hfinal0 :
          (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
            then (1 + (n : ℝ)) ^ 0 * Real.exp (-c * t * n) else 0) ≤
            K * t ^ (-(0 : ℝ)) * Real.exp (-(c / 4) * t ^ (-4 : ℤ)) := by
        have hsum0 :
            (∑' n : ℕ, if t ^ (-5 : ℤ) ≤ (n : ℝ)
              then (1 + (n : ℝ)) ^ 0 * Real.exp (-c * t * n) else 0) ≤
              (8 / c) * t⁻¹ * outer := by
          simpa [hd0, p, C, pow_one] using hsum_main
        calc
          _ ≤ (8 / c) * t⁻¹ * outer := hsum0
          _ ≤ (8 / c) * (4 / c) * Real.exp (-(c / 4) * t ^ (-4 : ℤ)) := by
                have hmul := mul_le_mul_of_nonneg_left hAbsorb
                  (by positivity : 0 ≤ 8 / c)
                simpa only [mul_assoc] using hmul
          _ ≤ K * 1 * Real.exp (-(c / 4) * t ^ (-4 : ℤ)) := by
                have hK' : (8 / c) * (4 / c) ≤ K * 1 := by simpa using hK
                simpa [mul_assoc] using
                  mul_le_mul_of_nonneg_right hK' (Real.exp_nonneg _)
          _ = K * t ^ (-(0 : ℝ)) * Real.exp (-(c / 4) * t ^ (-4 : ℤ)) := by simp
      simpa [hd0, Nat.zero_sub] using hfinal0

end AndersonAC.S6

#print axioms AndersonAC.S6.exponential_shell_tail
