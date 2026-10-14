import AndersonAC.AgentS78.Construction.TorusMetric

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78

open AndersonAC.S78

private lemma expRangeSum_le (N : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (∑ k ∈ Finset.range N, Real.exp (-u * (k : ℝ))) ≤ 2 / u := by
  let q : ℝ := Real.exp (-u)
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by
    dsimp [q]
    exact (Real.exp_lt_one_iff).2 (by linarith)
  have hgeom :
      (∑ k ∈ Finset.range N, q ^ k) * (1 - q) = 1 - q ^ N :=
    geom_sum_mul_neg q N
  have hsum : (∑ k ∈ Finset.range N, q ^ k) ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hqlt)).2
    rw [hgeom]
    nlinarith [pow_nonneg hqpos.le N]
  have hexp : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hqle : q ≤ 1 / (1 + u) := by
    dsimp [q]
    calc
      Real.exp (-u) = (Real.exp u)⁻¹ := Real.exp_neg u
      _ ≤ (1 + u)⁻¹ := inv_anti₀ (by linarith : 0 < 1 + u) hexp
      _ = 1 / (1 + u) := (one_div _).symm
  have hfrac : 1 / (1 + u) ≤ 1 - u / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + u)).2
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
  have hden : u / 2 ≤ 1 - q := by linarith [hqle.trans hfrac]
  have hrecip : 1 / (1 - q) ≤ 2 / u := by
    calc
      1 / (1 - q) ≤ 1 / (u / 2) :=
        one_div_le_one_div_of_le (by positivity : 0 < u / 2) hden
      _ = 2 / u := by field_simp
  have hqpow :
      (∑ k ∈ Finset.range N, q ^ k) =
        ∑ k ∈ Finset.range N, Real.exp (-u * (k : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    (∑ k ∈ Finset.range N, Real.exp (-u * (k : ℝ))) =
        ∑ k ∈ Finset.range N, q ^ k := hqpow.symm
    _ ≤ 1 / (1 - q) := hsum
    _ ≤ 2 / u := hrecip

private lemma finExpSum_le (N : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (∑ k : Fin N, Real.exp (-u * (k.val : ℝ))) ≤ 2 / u := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => Real.exp (-u * (k : ℝ)))]
  exact expRangeSum_le N hu hu1

private lemma circExpSum_le (m : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (x₀ : ZMod (OAI.Anderson.sideLength m)) :
    (∑ a : ZMod (OAI.Anderson.sideLength m),
      Real.exp (-u * (circDist m (a - x₀) : ℝ))) ≤ 4 / u := by
  let N := OAI.Anderson.sideLength m
  let e : Fin N ≃ ZMod N :=
    { toFun := fun k => (k.val : ZMod N)
      invFun := fun a => ⟨a.val, ZMod.val_lt a⟩
      left_inv := fun k => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt])
      right_inv := fun a => ZMod.natCast_zmod_val a }
  let f : ZMod N → ℝ := fun a => Real.exp (-u * (circDist m a : ℝ))
  have hsum : (∑ a : ZMod N, f a) = ∑ k : Fin N, f (e k) :=
    (Equiv.sum_comp e f).symm
  have hN : N ≠ 0 := by dsimp [N]; exact (OAI.Anderson.sideLength_neZero m).out
  have heval (k : Fin N) : (e k).val = k.val := by
    show ((k.val : ℕ) : ZMod N).val = k.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
  have hfirst : (∑ k : Fin N, Real.exp (-u * (k.val : ℝ))) ≤ 2 / u :=
    finExpSum_le N hu hu1
  have hsecondEq :
      (∑ k : Fin N, Real.exp (-u * ((N - k.val : ℕ) : ℝ))) =
        ∑ k : Fin N, Real.exp (-u * ((k.val : ℝ) + 1)) := by
    let g : Fin N → ℝ := fun k => Real.exp (-u * ((N - k.val : ℕ) : ℝ))
    calc
      (∑ k : Fin N, g k) = ∑ k : Fin N, g (Fin.revPerm k) :=
        (Equiv.sum_comp Fin.revPerm g).symm
      _ = ∑ k : Fin N, Real.exp (-u * ((k.val : ℝ) + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk := k.isLt
        have hrev : (Fin.revPerm k).val = N - 1 - k.val := by
          simp [Fin.revPerm]
          omega
        have hn : N - (N - 1 - k.val) = k.val + 1 := by omega
        simp [g, hrev, hn]
  have hsecond :
      (∑ k : Fin N, Real.exp (-u * ((N - k.val : ℕ) : ℝ))) ≤ 2 / u := by
    rw [hsecondEq]
    calc
      (∑ k : Fin N, Real.exp (-u * ((k.val : ℝ) + 1))) ≤
          ∑ k : Fin N, Real.exp (-u * (k.val : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Real.exp_le_exp.mpr
        nlinarith [hu]
      _ ≤ 2 / u := hfirst
  have hterm (k : Fin N) :
      f (e k) ≤ Real.exp (-u * (k.val : ℝ)) +
        Real.exp (-u * ((N - k.val : ℕ) : ℝ)) := by
    by_cases h : k.val ≤ N - k.val
    · simp only [f, circDist, heval, N, min_eq_left h]
      nlinarith [Real.exp_pos (-u * ((N - k.val : ℕ) : ℝ))]
    · have h' : N - k.val ≤ k.val := le_of_not_ge h
      simp only [f, circDist, heval, N, min_eq_right h']
      nlinarith [Real.exp_pos (-u * (k.val : ℝ))]
  calc
    (∑ a : ZMod N, f (a - x₀)) = ∑ a : ZMod N, f a := by
      let e' : ZMod N ≃ ZMod N := Equiv.addRight (-x₀)
      calc
        (∑ a : ZMod N, f (a - x₀)) = ∑ a : ZMod N, f (e' a) := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [e', sub_eq_add_neg]
        _ = ∑ a : ZMod N, f a := Equiv.sum_comp e' f
    _ = ∑ k : Fin N, f (e k) := hsum
    _ ≤ ∑ k : Fin N,
        (Real.exp (-u * (k.val : ℝ)) +
          Real.exp (-u * ((N - k.val : ℕ) : ℝ))) :=
      Finset.sum_le_sum fun k hk => hterm k
    _ = (∑ k : Fin N, Real.exp (-u * (k.val : ℝ))) +
        ∑ k : Fin N, Real.exp (-u * ((N - k.val : ℕ) : ℝ)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ 4 / u := by
      calc
        _ ≤ 2 / u + 2 / u := add_le_add hfirst hsecond
        _ = 4 / u := by ring

private lemma rpow_negNat (u : ℝ) (hu : 0 < u) (n : ℕ) :
    S45.power u (-(n : ℝ)) = 1 / u ^ n := by
  show u ^ (-(n : ℝ)) = 1 / u ^ n
  rw [Real.rpow_neg hu.le (n : ℝ), Real.rpow_natCast]
  simp [one_div]

private lemma shell_exp_sum_le (d m : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (x : Torus d m) :
    (∑ y : Torus d m, Real.exp (-u * physicalDistance d m x y)) ≤ (4 / u) ^ d := by
  have hterm (y : Torus d m) :
      Real.exp (-u * physicalDistance d m x y) =
        ∏ i : Fin d, Real.exp (-u * (circDist m (y i - x i) : ℝ)) := by
    rw [torusMetric_proof]
    have harg : -u * (l1Dist x y : ℝ) =
        ∑ i : Fin d, (-u * (circDist m (y i - x i) : ℝ)) := by
      simp [l1Dist, Finset.mul_sum]
    rw [harg, Real.exp_sum]
  have hfactor :
      (∑ y : Torus d m,
          ∏ i : Fin d, Real.exp (-u * (circDist m (y i - x i) : ℝ))) =
        ∏ i : Fin d, ∑ a : ZMod (OAI.Anderson.sideLength m),
          Real.exp (-u * (circDist m (a - x i) : ℝ)) := by
    exact (Fintype.prod_sum (fun i (a : ZMod (OAI.Anderson.sideLength m)) =>
      Real.exp (-u * (circDist m (a - x i) : ℝ)))).symm
  calc
    (∑ y : Torus d m, Real.exp (-u * physicalDistance d m x y)) =
        ∑ y : Torus d m,
          ∏ i : Fin d, Real.exp (-u * (circDist m (y i - x i) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm y
    _ = ∏ i : Fin d, ∑ a : ZMod (OAI.Anderson.sideLength m),
          Real.exp (-u * (circDist m (a - x i) : ℝ)) := hfactor
    _ ≤ ∏ i : Fin d, (4 / u) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg fun a ha => (Real.exp_pos _).le
      · intro i hi
        exact circExpSum_le m hu hu1 (x i)
    _ = (4 / u) ^ d := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (div_pow (4 : ℝ) u d).symm

private lemma polyExp_half_bound (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t) ≤ 16 * Real.exp (-t / 2) := by
  let a := (t / 4) * Real.exp (-(t / 4))
  have ha : a ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (t / 4)).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have ha0 : 0 ≤ a := mul_nonneg (by positivity) (Real.exp_pos _).le
  have hsq : a * a ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left ha ha0]
  have he2 : Real.exp (-t / 2) = Real.exp (-(t / 4)) * Real.exp (-(t / 4)) := by
    rw [← Real.exp_add]; ring_nf
  have hform : t ^ 2 * Real.exp (-t / 2) = 16 * (a * a) := by
    rw [he2]; simp only [a]; ring
  have hpoly : t ^ 2 * Real.exp (-t / 2) ≤ 16 := by rw [hform]; nlinarith
  have he1 : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
    rw [← Real.exp_add]; ring_nf
  calc
    t ^ 2 * Real.exp (-t) = (t ^ 2 * Real.exp (-t / 2)) * Real.exp (-t / 2) := by
          rw [he1]; ring
    _ ≤ 16 * Real.exp (-t / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le

private lemma weighted_by_half {D u : ℝ} (hD : 0 ≤ D) (hu : 0 < u) :
    D ^ 2 * Real.exp (-u * D) ≤ 16 / u ^ 2 * Real.exp (-(u / 2) * D) := by
  let t := u * D
  have ht : 0 ≤ t := mul_nonneg hu.le hD
  have hpoly := polyExp_half_bound t ht
  have hD' : D = t / u := by
    dsimp [t]
    field_simp
  have hscaled :
      (t ^ 2 * Real.exp (-t)) / u ^ 2 ≤
        (16 * Real.exp (-t / 2)) / u ^ 2 :=
    div_le_div_of_nonneg_right hpoly (sq_nonneg u)
  rw [hD']
  dsimp [t] at hscaled ⊢
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu.ne'
  field_simp [hu.ne'] at hscaled ⊢
  nlinarith [hscaled]

private lemma shell_second_sum_le (d m : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (x : Torus d m) :
    (∑ y : Torus d m,
      physicalDistance d m x y ^ 2 * Real.exp (-u * physicalDistance d m x y)) ≤
        (16 / u ^ 2) * (8 / u) ^ d := by
  have hterm (y : Torus d m) :
      physicalDistance d m x y ^ 2 * Real.exp (-u * physicalDistance d m x y) ≤
        (16 / u ^ 2) * Real.exp (-(u / 2) * physicalDistance d m x y) := by
    exact weighted_by_half (by unfold physicalDistance; exact Nat.cast_nonneg _) hu
  have hcount := shell_exp_sum_le d m (u := u / 2) (by linarith) (by linarith [hu1]) x
  have hcount' : (∑ y : Torus d m,
      Real.exp (-(u / 2) * physicalDistance d m x y)) ≤ (8 / u) ^ d := by
    have h := hcount
    have hfactor : 4 / (u / 2) = 8 / u := by field_simp; ring
    rw [hfactor] at h
    exact h
  calc
    (∑ y : Torus d m,
        physicalDistance d m x y ^ 2 * Real.exp (-u * physicalDistance d m x y)) ≤
      ∑ y : Torus d m,
        (16 / u ^ 2) * Real.exp (-(u / 2) * physicalDistance d m x y) :=
      Finset.sum_le_sum fun y hy => hterm y
    _ = (16 / u ^ 2) *
        ∑ y : Torus d m, Real.exp (-(u / 2) * physicalDistance d m x y) := by
      rw [Finset.mul_sum]
    _ ≤ (16 / u ^ 2) * (8 / u) ^ d := by
      exact mul_le_mul_of_nonneg_left hcount' (by positivity)

theorem torusShell_proof : ∀ d, TorusShellStatement d := by
  intro d
  let C : ℝ := 16 * 8 ^ d
  refine ⟨C, by positivity, ?_⟩
  intro m u hu hu1 x
  constructor
  · have hcount := shell_exp_sum_le d m hu hu1 x
    have hcountId : (4 / u) ^ d = (4 ^ d) * S45.power u (-(d : ℝ)) := by
      rw [rpow_negNat u hu d, div_pow]
      ring
    rw [hcountId] at hcount
    calc
      (∑ y : Torus d m, Real.exp (-u * physicalDistance d m x y)) ≤
          (4 ^ d) * S45.power u (-(d : ℝ)) := hcount
      _ ≤ C * S45.power u (-(d : ℝ)) := by
        apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _)
        dsimp [C]
        have h48 : (4 : ℝ) ^ d ≤ 8 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
        have h8 : (0 : ℝ) ≤ 8 ^ d := by positivity
        linarith
  · have hsecond := shell_second_sum_le d m hu hu1 x
    have hsecondId : (16 / u ^ 2) * (8 / u) ^ d =
        C * S45.power u (-(d : ℝ) - 2) := by
      have hp : S45.power u (-(d : ℝ) - 2) = 1 / u ^ (d + 2) := by
        convert rpow_negNat u hu (d + 2) using 1 <;> push_cast <;> ring
      rw [hp, div_pow]
      dsimp [C]
      field_simp [hu.ne']
      ring
    rw [hsecondId] at hsecond
    exact hsecond

end AndersonAC.AgentS78
