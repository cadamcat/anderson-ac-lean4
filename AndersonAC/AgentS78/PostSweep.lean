import AndersonAC.AgentS78.Comparators

/-!
certificate construction: assembly initial data for the post-sweep state (07-assembly.tex:970–1000): the `W*`
comparison at the halved low scale `θ b` from the stage-start comparators and the sweep's
affine mixture, and the constant kernel of the post-sweep energy from a positive dual
lower bound.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- A positive lower bound on the dual on two-point dipoles forces the constant kernel. -/
theorem constantKernel_of_dual_lower {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (p : ι → ℝ)
    (h : Matrix ι ι ℂ) (W : (ι → ℝ) → ℝ) (c : ℝ) (hc : 0 < c)
    (hW : ∀ y, neutral A y → (∑ i ∈ A, y i ^ 2) ≤ W y)
    (hlow : ∀ y, neutral A y → c * W y ≤ inverseEnergy A (wardEnergy A p h) y) :
    constantKernel A (wardEnergy A p h) := by
  intro f
  constructor
  · intro hf
    by_contra hnc
    push_neg at hnc
    obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ A, ∃ j ∈ A, f i ≠ f j := by
      by_contra hall
      push_neg at hall
      by_cases hA : A.Nonempty
      · obtain ⟨k, hk⟩ := hA
        obtain ⟨l, hl, hne⟩ := hnc (f k)
        exact hne (hall l hl k hk)
      · obtain ⟨l, hl, -⟩ := hnc 0
        exact hA ⟨l, hl⟩
    have hij' : i ≠ j := fun e => hij (by rw [e])
    let y : ι → ℝ := fun x => (if x = i then 1 else 0) - (if x = j then 1 else 0)
    have hy : neutral A y := by
      refine ⟨fun x hx => ?_, ?_⟩
      · have h1 : x ≠ i := fun e => hx (e ▸ hi)
        have h2 : x ≠ j := fun e => hx (e ▸ hj)
        simp [y, h1, h2]
      · simp only [y, Finset.sum_sub_distrib, Finset.sum_ite_eq', hi, hj, if_true]; ring
    have hpair : ∑ x ∈ A, y x * f x = f i - f j := by
      simp only [y, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        hi, hj, if_true]
    have hzero : ∀ s : ℝ, wardEnergy A p h (fun x => s * f x) = 0 := by
      intro s
      unfold wardEnergy at hf ⊢
      have : ∀ x ∈ A, ∀ z ∈ A, p x * p z * ‖h x z‖ ^ 2 * (s * f x - s * f z) ^ 2 =
          s ^ 2 * (p x * p z * ‖h x z‖ ^ 2 * (f x - f z) ^ 2) := by intros; ring
      rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun z hz => this x hx z hz]
      simp only [← Finset.mul_sum]
      rw [show (1 / 2 : ℝ) * (s ^ 2 * ∑ x ∈ A, ∑ z ∈ A, p x * p z * ‖h x z‖ ^ 2 * (f x - f z) ^ 2) =
        s ^ 2 * ((1 / 2) * ∑ x ∈ A, ∑ z ∈ A, p x * p z * ‖h x z‖ ^ 2 * (f x - f z) ^ 2) by ring, hf,
        mul_zero]
    have hnb : ¬ BddAbove (Set.range fun g : ι → ℝ => 2 * (∑ x ∈ A, y x * g x) - wardEnergy A p h g) := by
      rintro ⟨B, hB⟩
      have hd : f i - f j ≠ 0 := sub_ne_zero.mpr hij
      let s : ℝ := (|B| + 1) / (2 * (f i - f j))
      have hmem := hB ⟨fun x => s * f x, rfl⟩
      simp only at hmem
      rw [hzero, sub_zero] at hmem
      have : ∑ x ∈ A, y x * (s * f x) = s * (f i - f j) := by
        rw [← hpair, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      rw [this] at hmem
      have : 2 * (s * (f i - f j)) = |B| + 1 := by
        simp only [s]; field_simp
      rw [this] at hmem
      linarith [le_abs_self B]
    have hX := hlow y hy
    unfold inverseEnergy at hX
    rw [Real.sSup_of_not_bddAbove hnb] at hX
    have hWp := hW y hy
    have hpos : 0 < ∑ x ∈ A, y x ^ 2 := by
      have : y i ^ 2 ≤ ∑ x ∈ A, y x ^ 2 :=
        Finset.single_le_sum (f := fun x => y x ^ 2) (fun x _ => sq_nonneg _) hi
      have hyi : y i = 1 := by simp [y, hij']
      rw [hyi] at this; linarith
    nlinarith
  · rintro ⟨c0, hc0⟩
    unfold wardEnergy
    rw [Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun z hz => by rw [hc0 x hx, hc0 z hz]; ring,
      mul_zero]

/-- The `W*` comparison after the sweep, at low scale `θ b`. -/
theorem post_sweep_wstar {ι : Type} [Fintype ι] (A : Finset ι) (Xold Xsw Λ : (ι → ℝ) → ℝ) (p : ι → ℝ)
    (y : ι → ℝ) (θ ε b cP CP cL CL C₀ : ℝ) (hθ : 1 / 4 ≤ θ) (hθ' : θ ≤ 5 / 8) (hε : 0 ≤ ε)
    (hε' : ε ≤ 1 / 2) (hb : 0 ≤ b) (hΛ : 0 ≤ Λ y) (hcP : 0 < cP) (hcL : 0 < cL) (hCL : 0 ≤ CL)
    (hC₀ : 0 ≤ C₀)
    (hp : ∀ i ∈ A, cP ≤ p i ∧ p i ≤ CP)
    (hlow : cL * b * Λ y ≤ Xold y) (hup : Xold y ≤ C₀ * (∑ i ∈ A, y i ^ 2) + CL * b * Λ y)
    (haff : (1 - ε) * (θ * Xold y + (1 - θ) * ∑ i ∈ A, y i ^ 2 / p i ^ 2) ≤ Xsw y ∧
      Xsw y ≤ (1 + ε) * (θ * Xold y + (1 - θ) * ∑ i ∈ A, y i ^ 2 / p i ^ 2)) :
    (min cL (3 / (8 * CP ^ 2)) / 2) * ((∑ i ∈ A, y i ^ 2) + (θ * b) * Λ y) ≤ Xsw y ∧
      Xsw y ≤ (3 / 2 * max (C₀ + 1 / cP ^ 2) CL) * ((∑ i ∈ A, y i ^ 2) + (θ * b) * Λ y) := by
  have hS : 0 ≤ ∑ i ∈ A, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSlo : (∑ i ∈ A, y i ^ 2) * (1 / CP ^ 2) ≤ ∑ i ∈ A, y i ^ 2 / p i ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 := (hp i hi).1; have h2 := (hp i hi).2
    have hpi : 0 < p i := hcP.trans_le h1
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ hpi.le h2 2)
  have hShi : ∑ i ∈ A, y i ^ 2 / p i ^ 2 ≤ (∑ i ∈ A, y i ^ 2) * (1 / cP ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 := (hp i hi).1
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ hcP.le h1 2)
  have hbΛ : 0 ≤ b * Λ y := mul_nonneg hb hΛ
  have hXo : 0 ≤ Xold y := le_trans (by positivity) hlow
  have hS' : 0 ≤ ∑ i ∈ A, y i ^ 2 / p i ^ 2 := le_trans (by positivity) hSlo
  obtain ⟨a1, a2⟩ := haff
  have m1 := min_le_left cL (3 / (8 * CP ^ 2))
  have m2 := min_le_right cL (3 / (8 * CP ^ 2))
  have hm0 : 0 ≤ min cL (3 / (8 * CP ^ 2)) := le_min hcL.le (by positivity)
  have M1 := le_max_left (C₀ + 1 / cP ^ 2) CL
  have M2 := le_max_right (C₀ + 1 / cP ^ 2) CL
  have hinv : 0 ≤ 1 / cP ^ 2 := by positivity
  constructor
  · -- lower
    have L1 : (1 / 2) * (θ * (cL * b * Λ y) + (3 / 8) * ((∑ i ∈ A, y i ^ 2) * (1 / CP ^ 2))) ≤ Xsw y := by
      refine le_trans ?_ a1
      have e1 : θ * (cL * b * Λ y) ≤ θ * Xold y := mul_le_mul_of_nonneg_left hlow (by linarith)
      have e2 : (3 / 8) * ((∑ i ∈ A, y i ^ 2) * (1 / CP ^ 2)) ≤ (1 - θ) * ∑ i ∈ A, y i ^ 2 / p i ^ 2 :=
        mul_le_mul (by linarith) hSlo (by positivity) (by linarith)
      have e3 : 0 ≤ θ * Xold y + (1 - θ) * ∑ i ∈ A, y i ^ 2 / p i ^ 2 := by
        have : 0 ≤ 1 - θ := by linarith
        positivity
      nlinarith
    refine le_trans ?_ L1
    have k1 : min cL (3 / (8 * CP ^ 2)) * (θ * b * Λ y) ≤ cL * (θ * b * Λ y) :=
      mul_le_mul_of_nonneg_right m1 (by positivity)
    have k2 : min cL (3 / (8 * CP ^ 2)) * (∑ i ∈ A, y i ^ 2) ≤
        (3 / 8) * ((∑ i ∈ A, y i ^ 2) * (1 / CP ^ 2)) := by
      calc min cL (3 / (8 * CP ^ 2)) * (∑ i ∈ A, y i ^ 2) ≤ (3 / (8 * CP ^ 2)) * (∑ i ∈ A, y i ^ 2) :=
            mul_le_mul_of_nonneg_right m2 hS
        _ = (3 / 8) * ((∑ i ∈ A, y i ^ 2) * (1 / CP ^ 2)) := by
            by_cases hc : CP = 0
            · simp [hc]
            · field_simp
    nlinarith
  · -- upper
    have U1 : Xsw y ≤ (3 / 2) * (θ * (C₀ * (∑ i ∈ A, y i ^ 2) + CL * b * Λ y) +
        (∑ i ∈ A, y i ^ 2) * (1 / cP ^ 2)) := by
      refine a2.trans ?_
      have e1 : θ * Xold y ≤ θ * (C₀ * (∑ i ∈ A, y i ^ 2) + CL * b * Λ y) :=
        mul_le_mul_of_nonneg_left hup (by linarith)
      have e2 : (1 - θ) * ∑ i ∈ A, y i ^ 2 / p i ^ 2 ≤ (∑ i ∈ A, y i ^ 2) * (1 / cP ^ 2) := by
        have : (1 - θ) * ∑ i ∈ A, y i ^ 2 / p i ^ 2 ≤ 1 * ∑ i ∈ A, y i ^ 2 / p i ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hS'
        linarith
      have e3 : 0 ≤ θ * Xold y + (1 - θ) * ∑ i ∈ A, y i ^ 2 / p i ^ 2 := by
        have : 0 ≤ 1 - θ := by linarith
        positivity
      nlinarith
    refine U1.trans ?_
    have k1 : θ * (C₀ * (∑ i ∈ A, y i ^ 2)) + (∑ i ∈ A, y i ^ 2) * (1 / cP ^ 2) ≤
        max (C₀ + 1 / cP ^ 2) CL * (∑ i ∈ A, y i ^ 2) := by
      have : θ * (C₀ * (∑ i ∈ A, y i ^ 2)) ≤ C₀ * (∑ i ∈ A, y i ^ 2) := by
        have := mul_nonneg hC₀ hS; nlinarith
      nlinarith [mul_le_mul_of_nonneg_right M1 hS]
    have k2 : θ * (CL * b * Λ y) ≤ max (C₀ + 1 / cP ^ 2) CL * (θ * b * Λ y) := by
      have := mul_le_mul_of_nonneg_right M2 (by positivity : 0 ≤ θ * b * Λ y)
      nlinarith
    nlinarith

end AndersonAC.AgentS78
