import AndersonAC.AgentS6Shell.ExponentialShell

/-! Deterministic far-field tail for finite monitoring (06-clearing.tex:1066–1087): a vector
with exponential decay `‖h_j‖ ≤ K' t^{-1/2} e^{-ctρ_j}`, `ρ_j ≥ dist_j/4` beyond `t^{-5}`, and
shell counts `K(1+n)^{d-1}`, has square mass beyond `t^{-5}+1` at most
`C K K'² t^{-1} t^{-d} e^{-c' t^{-4}}`, independently of the torus volume. -/

noncomputable section
open scoped BigOperators

namespace AndersonAC.AgentS6

theorem one_add_pow_le (m n : ℕ) : (1 + (n : ℝ)) ^ m ≤ 2 ^ m * ((n : ℝ) ^ m + 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    · simp only [Nat.cast_zero, add_zero, one_pow, zero_pow (Nat.pos_iff_ne_zero.mp hm), zero_add,
        mul_one]
      exact h2
  · have h1 : 1 + (n : ℝ) ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc (1 + (n : ℝ)) ^ m ≤ (2 * n) ^ m := pow_le_pow_left₀ (by positivity) h1 m
      _ = 2 ^ m * (n : ℝ) ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * ((n : ℝ) ^ m + 1) := by gcongr; linarith

theorem shell_summable (m : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Summable (fun n : ℕ => if s ≤ (n : ℝ) then (1 + (n : ℝ)) ^ m * Real.exp (-a * n) else 0) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul m ha
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 0 ha
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) ((h1.add h2).mul_left (2 ^ m))
  · split_ifs <;> positivity
  · split_ifs
    · simp only [pow_zero, one_mul]
      calc (1 + (n : ℝ)) ^ m * Real.exp (-a * n) ≤ 2 ^ m * ((n : ℝ) ^ m + 1) * Real.exp (-a * n) :=
            mul_le_mul_of_nonneg_right (one_add_pow_le m n) (Real.exp_pos _).le
        _ = 2 ^ m * ((n : ℝ) ^ m * Real.exp (-a * n) + Real.exp (-a * n)) := by ring
    · positivity

theorem far_tail (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C c' t0 : ℝ, 0 < C ∧ 0 < c' ∧ 0 < t0 ∧ ∀ t : ℝ, 0 < t → t < t0 →
      ∀ {ι : Type*} [Fintype ι] (dist ρ : ι → ℝ) (h : ι → ℂ) (K K' : ℝ), 0 ≤ K →
      (∀ n : ℕ, ((Finset.univ.filter (fun j => (n : ℝ) ≤ dist j ∧ dist j < n + 1)).card : ℝ) ≤
        K * (1 + (n : ℝ)) ^ (d - 1)) →
      (∀ j, ‖h j‖ ≤ K' / Real.sqrt t * Real.exp (-c * t * ρ j)) →
      (∀ j, t ^ (-5 : ℤ) ≤ dist j → dist j / 4 ≤ ρ j) →
      ∑ j ∈ Finset.univ.filter (fun j => t ^ (-5 : ℤ) + 1 ≤ dist j), ‖h j‖ ^ 2 ≤
        C * K * K' ^ 2 / t * t ^ (-(d : ℝ)) * Real.exp (-c' * t ^ (-4 : ℤ)) := by
  obtain ⟨C, c', t0, hC, hc', ht0, htail⟩ := AndersonAC.S6.exponential_shell_tail d (c / 2)
    (by positivity)
  refine ⟨C, c', t0, hC, hc', ht0, ?_⟩
  intro t ht htt ι _ dist ρ h K K' hK hshell hh hρ
  set a := c / 2 * t with ha
  have ha0 : 0 < a := by positivity
  set F := Finset.univ.filter (fun j => t ^ (-5 : ℤ) + 1 ≤ dist j) with hF
  have h5 : 0 < t ^ (-5 : ℤ) := zpow_pos ht _
  set f : ℕ → ℝ := fun n => if t ^ (-5 : ℤ) ≤ (n : ℝ) then
    (1 + (n : ℝ)) ^ (d - 1) * Real.exp (-(c / 2) * t * n) else 0 with hf
  have hfsum : Summable f := by
    have := shell_summable (d - 1) ha0 (t ^ (-5 : ℤ))
    refine this.congr fun n => ?_
    simp only [hf, ha]; ring_nf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; split_ifs <;> positivity
  -- termwise bound by the floor shell
  have hterm : ∀ j ∈ F, ‖h j‖ ^ 2 ≤ K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j⌋₊ : ℝ)) := by
    intro j hj
    have hdj : t ^ (-5 : ℤ) + 1 ≤ dist j := (Finset.mem_filter.mp hj).2
    have hd0 : 0 ≤ dist j := by linarith
    have hρj := hρ j (by linarith)
    have hfl : (⌊dist j⌋₊ : ℝ) ≤ dist j := Nat.floor_le hd0
    have hb := hh j
    have hn : 0 ≤ ‖h j‖ := norm_nonneg _
    have hsq : ‖h j‖ ^ 2 ≤ (K' / Real.sqrt t * Real.exp (-c * t * ρ j)) ^ 2 :=
      pow_le_pow_left₀ hn hb 2
    have e1 : (K' / Real.sqrt t * Real.exp (-c * t * ρ j)) ^ 2 =
        K' ^ 2 / t * Real.exp (-(2 * c) * t * ρ j) := by
      rw [mul_pow, div_pow, Real.sq_sqrt ht.le, ← Real.exp_nat_mul]; ring_nf
    have e2 : Real.exp (-(2 * c) * t * ρ j) ≤ Real.exp (-(c / 2) * t * (⌊dist j⌋₊ : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (c / 2) * t * (⌊dist j⌋₊ : ℝ) ≤ (2 * c) * t * ρ j := by
        have : (⌊dist j⌋₊ : ℝ) ≤ 4 * ρ j := by linarith
        have hct : 0 ≤ c / 2 * t := by positivity
        nlinarith
      linarith
    calc ‖h j‖ ^ 2 ≤ K' ^ 2 / t * Real.exp (-(2 * c) * t * ρ j) := e1 ▸ hsq
      _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
  have hmaps : ∀ j ∈ F, ⌊dist j⌋₊ ∈ F.image (fun j => ⌊dist j⌋₊) :=
    fun j hj => Finset.mem_image_of_mem _ hj
  calc ∑ j ∈ F, ‖h j‖ ^ 2
      ≤ ∑ j ∈ F, K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j⌋₊ : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ∑ n ∈ F.image (fun j => ⌊dist j⌋₊),
          ∑ j ∈ F.filter (fun j => ⌊dist j⌋₊ = n),
            K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j⌋₊ : ℝ)) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ F.image (fun j => ⌊dist j⌋₊), K * K' ^ 2 / t * f n := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.mp hn
        have hd0 : t ^ (-5 : ℤ) + 1 ≤ dist j0 := (Finset.mem_filter.mp hj0).2
        have hn5 : t ^ (-5 : ℤ) ≤ (⌊dist j0⌋₊ : ℝ) := by
          have := Nat.lt_floor_add_one (dist j0); linarith
        have hfn : f ⌊dist j0⌋₊ = (1 + (⌊dist j0⌋₊ : ℝ)) ^ (d - 1) *
            Real.exp (-(c / 2) * t * (⌊dist j0⌋₊ : ℝ)) := by simp only [hf, if_pos hn5]
        rw [hfn]
        have hcongr : ∑ j ∈ F.filter (fun j => ⌊dist j⌋₊ = ⌊dist j0⌋₊),
            K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j⌋₊ : ℝ)) =
            ((F.filter (fun j => ⌊dist j⌋₊ = ⌊dist j0⌋₊)).card : ℝ) *
              (K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j0⌋₊ : ℝ))) := by
          rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
            Finset.sum_const, nsmul_eq_mul]
        rw [hcongr]
        have hsub : F.filter (fun j => ⌊dist j⌋₊ = ⌊dist j0⌋₊) ⊆
            Finset.univ.filter (fun j => ((⌊dist j0⌋₊ : ℕ) : ℝ) ≤ dist j ∧
              dist j < (⌊dist j0⌋₊ : ℕ) + 1) := by
          intro j hj
          obtain ⟨hjF, hjn⟩ := Finset.mem_filter.mp hj
          have hdj : 0 ≤ dist j := by linarith [(Finset.mem_filter.mp hjF).2]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · rw [← hjn]; exact Nat.floor_le hdj
          · rw [← hjn]; exact Nat.lt_floor_add_one _
        have hcard : ((F.filter (fun j => ⌊dist j⌋₊ = ⌊dist j0⌋₊)).card : ℝ) ≤
            K * (1 + (⌊dist j0⌋₊ : ℝ)) ^ (d - 1) :=
          le_trans (by exact_mod_cast Finset.card_le_card hsub) (hshell _)
        have hpos : 0 ≤ K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j0⌋₊ : ℝ)) := by positivity
        calc ((F.filter (fun j => ⌊dist j⌋₊ = ⌊dist j0⌋₊)).card : ℝ) *
              (K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j0⌋₊ : ℝ)))
            ≤ K * (1 + (⌊dist j0⌋₊ : ℝ)) ^ (d - 1) *
              (K' ^ 2 / t * Real.exp (-(c / 2) * t * (⌊dist j0⌋₊ : ℝ))) :=
              mul_le_mul_of_nonneg_right hcard hpos
          _ = _ := by ring
    _ = K * K' ^ 2 / t * ∑ n ∈ F.image (fun j => ⌊dist j⌋₊), f n := by rw [Finset.mul_sum]
    _ ≤ K * K' ^ 2 / t * ∑' n, f n := by
        gcongr
        exact hfsum.sum_le_tsum _ (fun n _ => hf0 n)
    _ ≤ K * K' ^ 2 / t * (C * t ^ (-(d : ℝ)) * Real.exp (-c' * t ^ (-4 : ℤ))) := by
        gcongr
        have := htail t ht htt
        refine le_trans (le_of_eq ?_) this
        refine tsum_congr fun n => ?_
        simp only [hf]
    _ = C * K * K' ^ 2 / t * t ^ (-(d : ℝ)) * Real.exp (-c' * t ^ (-4 : ℤ)) := by ring

/-- Collapsed-distance comparison beyond `t^{-5}` (06-clearing.tex:1078–1080):
`d_T ≥ dist/2 - t^{-1.03}` gives `d_T ≥ dist/4` once `dist ≥ t^{-5}`, for `0 < t ≤ 1/4`. -/
theorem collapsed_quarter {t D Dc : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4)
    (hD : t ^ (-5 : ℤ) ≤ D) (hmetric : D / 2 - t ^ (-(103 / 100 : ℝ)) ≤ Dc) : D / 4 ≤ Dc := by
  have h1 : t ^ (-(103 / 100 : ℝ)) ≤ t ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht (by linarith) (by norm_num)
  have h2 : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht.le]; norm_cast
  have h3 : t ^ (-5 : ℤ) = (t ^ 5)⁻¹ := by rw [zpow_neg]; norm_cast
  have h4 : 4 * (t ^ 2)⁻¹ ≤ (t ^ 5)⁻¹ := by
    rw [show (t ^ 5)⁻¹ = (t ^ 2)⁻¹ * (t ^ 3)⁻¹ by rw [← mul_inv, ← pow_add]]
    have : 4 ≤ (t ^ 3)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      have : t ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ ht.le ht4 3
      linarith
    have hp : 0 ≤ (t ^ 2)⁻¹ := by positivity
    nlinarith
  linarith

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.far_tail
#print axioms AndersonAC.AgentS6.collapsed_quarter
