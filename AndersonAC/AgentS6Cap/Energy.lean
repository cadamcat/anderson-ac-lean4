import AndersonAC.AgentS6Cap.TrialControl

/-! Fourth-power control along the distinct pivots that still see a fixed row. -/

noncomputable section
open scoped BigOperators

namespace AndersonAC.AgentS6

open AndersonAC.S6

/-- The row of `heatV` has a small predictable squared-energy budget. We first
restrict to heats before the row is removed, then use distinct pivots and the
fourth-power row slack at initialization. -/
theorem heatV_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t c K : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) (i : Fin n)
    (hc : 0 < c) (hK : 1 ≤ K)
    (hbroad : ∀ ω, BroadBounds c K (r ω))
    :
    ∑ k ∈ (Finset.range (q.stop ω)).filter (fun k => i ∈ (q.state k ω).active),
      ‖heatV q k ω i‖ ^ 2 ≤
        (K / c) * Real.sqrt
          ((q.stop ω : ℝ) *
            (8 * fourthRow (scaledInverse t (g0 ω)) i +
              8 * (q.stop ω : ℝ) * (Real.sqrt t * entryBudget t) ^ 4)) := by
  let S : Finset ℕ := (Finset.range (q.stop ω)).filter
    (fun k => i ∈ (q.state k ω).active)
  let m : ℕ := S.card
  have hSsubset : S ⊆ Finset.range m := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkstop, hactive⟩
    have hkstop' : k < q.stop ω := Finset.mem_range.mp hkstop
    have hprefix : Finset.range (k + 1) ⊆ S := by
      intro j hj
      have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hjstop : j < q.stop ω := lt_of_le_of_lt hjle hkstop'
      have hactivej := active_antitone q ω hjle (Nat.le_of_lt hkstop') hactive
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjstop, hactivej⟩
    have hcard : k + 1 ≤ S.card := by
      calc
        k + 1 = (Finset.range (k + 1)).card := by simp
        _ ≤ S.card := Finset.card_le_card hprefix
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have hcard_le : (Finset.range m).card ≤ S.card := by simp [m]
  have hSeq : S = Finset.range m := Finset.eq_of_subset_of_card_le hSsubset hcard_le
  have hmstop : m ≤ q.stop ω := by
    simpa [m, S] using Finset.card_le_card (Finset.filter_subset
      (fun k => i ∈ (q.state k ω).active) (Finset.range (q.stop ω)))
  let piv : Fin m → Fin n := fun a => q.pivot a.val ω
  have hpiv_inj : Function.Injective piv := by
    intro a b hab
    have haS : a.val ∈ S := by rw [hSeq]; exact Finset.mem_range.mpr a.isLt
    have hbS : b.val ∈ S := by rw [hSeq]; exact Finset.mem_range.mpr b.isLt
    have harun : a.val < q.stop ω := Finset.mem_range.mp (Finset.mem_filter.mp haS).1
    have hbrun : b.val < q.stop ω := Finset.mem_range.mp (Finset.mem_filter.mp hbS).1
    change q.pivot a.val ω = q.pivot b.val ω at hab
    have hval := pivot_injective_running q ω harun hbrun hab
    exact Fin.ext hval
  let g : Fin m → Matrix (Fin n) (Fin n) ℂ := fun a x y =>
    if hx : x ∈ (q.state a.val ω).active then
      if hy : y ∈ (q.state a.val ω).active then
        trialInverse t (r ω) (q.state a.val ω) ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0
  have haS (a : Fin m) : a.val ∈ S := by
    rw [hSeq]
    exact Finset.mem_range.mpr a.isLt
  have harun (a : Fin m) : a.val < q.stop ω :=
    Finset.mem_range.mp (Finset.mem_filter.mp (haS a)).1
  have haactive (a : Fin m) : i ∈ (q.state a.val ω).active :=
    (Finset.mem_filter.mp (haS a)).2
  have hapivot (a : Fin m) : piv a ∈ (q.state a.val ω).active := by
    obtain ⟨hx, -, -, -, -⟩ := q.heat a.val ω (harun a)
    exact hx
  have hstored (a : Fin m) : (q.state a.val ω).hatG i (piv a) =
      trialInverse t (r ω) (q.state a.val ω) ⟨i, haactive a⟩ ⟨piv a, hapivot a⟩ :=
    by
      simpa using AndersonAC.AgentS6.hatG_eq_trialInverse q a.val ω
        (Nat.le_of_lt (harun a)) ⟨i, haactive a⟩ ⟨piv a, hapivot a⟩
  have hentry (a : Fin m) :
      ‖g a i (piv a) - g0 ω i (piv a)‖ ≤ entryBudget t := by
    have hbud := (q.running_budgets a.val ω (harun a)).1 i (piv a)
    have hg : g a i (piv a) =
        trialInverse t (r ω) (q.state a.val ω) ⟨i, haactive a⟩ ⟨piv a, hapivot a⟩ := by
      simp [g, haactive a, hapivot a]
    calc
      _ = ‖(q.state a.val ω).hatG i (piv a) - g0 ω i (piv a)‖ := by
        rw [hg, ← hstored a]
      _ ≤ entryBudget t := hbud
  have hfour := AndersonAC.S6.pivot_fourth t m piv (g0 ω) g i hpiv_inj hentry
  let F : Fin m → ℝ := fun a =>
    ‖scaledInverse t (g a) i (piv a)‖ ^ 2
  have hFnonneg : ∀ a, 0 ≤ F a := fun _ => sq_nonneg _
  have hFsum : ∑ a : Fin m, F a ≤
      Real.sqrt ((m : ℝ) *
        (8 * fourthRow (scaledInverse t (g0 ω)) i +
          8 * (m : ℝ) * (Real.sqrt t * entryBudget t) ^ 4)) := by
    have hmass := AndersonAC.S6.pivot_mass m F hFnonneg
    have hFfour : ∑ a : Fin m, F a ^ 2 ≤
        8 * fourthRow (scaledInverse t (g0 ω)) i +
          8 * (m : ℝ) * (Real.sqrt t * entryBudget t) ^ 4 := by
      calc
        ∑ a : Fin m, F a ^ 2 =
            ∑ a : Fin m, ‖scaledInverse t (g a) i (piv a)‖ ^ 4 := by
              apply Finset.sum_congr rfl
              intro a ha
              dsimp [F]
              ring
        _ ≤ _ := hfour
    calc
      ∑ a : Fin m, F a ≤ Real.sqrt ((m : ℝ) * ∑ a : Fin m, F a ^ 2) := hmass
      _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hFfour (Nat.cast_nonneg _))
  have hsumV : ∑ a : Fin m, ‖heatV q a.val ω i‖ ^ 2 ≤ (K / c) * ∑ a : Fin m, F a := by
    calc
      ∑ a : Fin m, ‖heatV q a.val ω i‖ ^ 2 ≤
          ∑ a : Fin m, (K / c) * F a := by
            apply Finset.sum_le_sum
            intro a ha
            have hv := heatV_norm_sq_le q ω a.val i (hbroad ω) (haactive a) (hapivot a)
            have hg : g a i (piv a) =
                trialInverse t (r ω) (q.state a.val ω) ⟨i, haactive a⟩
                  ⟨piv a, hapivot a⟩ := by simp [g, haactive a, hapivot a]
            have hentryEq := hg.symm
            have hnormEq :
                ‖scaledInverse t (trialInverse t (r ω) (q.state a.val ω))
                  ⟨i, haactive a⟩ ⟨piv a, hapivot a⟩‖ ^ 2 =
                ‖scaledInverse t (g a) i (piv a)‖ ^ 2 := by
              simp [scaledInverse, Matrix.smul_apply, hentryEq]
            rw [hnormEq] at hv
            simpa [F] using hv
      _ = (K / c) * ∑ a : Fin m, F a := by rw [Finset.mul_sum]
  calc
    _ = ∑ k ∈ S, ‖heatV q k ω i‖ ^ 2 := rfl
    _ = ∑ k ∈ Finset.range m, ‖heatV q k ω i‖ ^ 2 := by rw [hSeq]
    _ = ∑ a : Fin m, ‖heatV q a.val ω i‖ ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range]
    _ ≤ (K / c) * Real.sqrt ((m : ℝ) *
          (8 * fourthRow (scaledInverse t (g0 ω)) i +
            8 * (m : ℝ) * (Real.sqrt t * entryBudget t) ^ 4)) := by
        calc
          _ ≤ (K / c) * ∑ a : Fin m, F a := hsumV
          _ ≤ _ := mul_le_mul_of_nonneg_left hFsum (by positivity)
    _ ≤ (K / c) * Real.sqrt
          ((q.stop ω : ℝ) *
            (8 * fourthRow (scaledInverse t (g0 ω)) i +
              8 * (q.stop ω : ℝ) * (Real.sqrt t * entryBudget t) ^ 4)) := by
        have hR0 : 0 ≤ 8 * fourthRow (scaledInverse t (g0 ω)) i := by
          unfold fourthRow
          positivity
        have hE0 : 0 ≤ 8 * (Real.sqrt t * entryBudget t) ^ 4 := by positivity
        have hm' : (m : ℝ) ≤ q.stop ω := by exact_mod_cast hmstop
        let A : ℝ := 8 * fourthRow (scaledInverse t (g0 ω)) i
        let B : ℝ := 8 * (Real.sqrt t * entryBudget t) ^ 4
        have hA : 0 ≤ A := by dsimp [A]; exact hR0
        have hB : 0 ≤ B := by dsimp [B]; exact hE0
        have hs0 : 0 ≤ (q.stop ω : ℝ) := Nat.cast_nonneg _
        have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
        have hmul1 : (m : ℝ) * A ≤ (q.stop ω : ℝ) * A :=
          mul_le_mul_of_nonneg_right hm' hA
        have hsq : (m : ℝ) ^ 2 ≤ (q.stop ω : ℝ) ^ 2 :=
          pow_le_pow_left₀ hm0 hm' 2
        have hmul2 : (m : ℝ) ^ 2 * B ≤ (q.stop ω : ℝ) ^ 2 * B :=
          mul_le_mul_of_nonneg_right hsq hB
        have hmul : (m : ℝ) *
            (8 * fourthRow (scaledInverse t (g0 ω)) i + 8 * (m : ℝ) *
              (Real.sqrt t * entryBudget t) ^ 4) ≤
            (q.stop ω : ℝ) *
              (8 * fourthRow (scaledInverse t (g0 ω)) i + 8 * (q.stop ω : ℝ) *
                (Real.sqrt t * entryBudget t) ^ 4) := by
          dsimp [A, B] at hmul1 hmul2
          nlinarith
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmul) (by positivity)

/-- Initial inverse entries at distinct running pivots have square mass controlled
by the fourth-power row norm. -/
theorem initial_pivot_row_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) (i : Fin n) :
    ∑ k ∈ Finset.range (q.stop ω),
        ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 ≤
      Real.sqrt ((q.stop ω : ℝ) * fourthRow (scaledInverse t (g0 ω)) i) := by
  let piv : Fin (q.stop ω) → Fin n := fun k => q.pivot k.val ω
  have hpiv : Function.Injective piv := by
    intro k l h
    have hk : k.val < q.stop ω := k.isLt
    have hl : l.val < q.stop ω := l.isLt
    change q.pivot k.val ω = q.pivot l.val ω at h
    exact Fin.ext (pivot_injective_running q ω hk hl h)
  let F : Fin (q.stop ω) → ℝ := fun k =>
    ‖scaledInverse t (g0 ω) i (piv k)‖ ^ 2
  have hFnonneg : ∀ k, 0 ≤ F k := fun _ => sq_nonneg _
  have hFfour : ∑ k : Fin (q.stop ω), F k ^ 2 ≤
      fourthRow (scaledInverse t (g0 ω)) i := by
    have hImage : ∑ k : Fin (q.stop ω), F k ^ 2 =
        ∑ j ∈ (Finset.univ : Finset (Fin (q.stop ω))).image piv,
          ‖scaledInverse t (g0 ω) i j‖ ^ 4 := by
      unfold F
      symm
      rw [Finset.sum_image hpiv.injOn]
      simp [pow_two]
      ring
    calc
      ∑ k : Fin (q.stop ω), F k ^ 2
          = ∑ j ∈ (Finset.univ : Finset (Fin (q.stop ω))).image piv,
              ‖scaledInverse t (g0 ω) i j‖ ^ 4 := hImage
      _ ≤ ∑ j, ‖scaledInverse t (g0 ω) i j‖ ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by positivity)
      _ = fourthRow (scaledInverse t (g0 ω)) i := rfl
  have hmass := AndersonAC.S6.pivot_mass (q.stop ω) F hFnonneg
  have hmass' : ∑ k : Fin (q.stop ω), F k ≤
      Real.sqrt ((q.stop ω : ℝ) * fourthRow (scaledInverse t (g0 ω)) i) := by
    calc
      ∑ k : Fin (q.stop ω), F k ≤
          Real.sqrt ((q.stop ω : ℝ) * ∑ k : Fin (q.stop ω), F k ^ 2) := hmass
      _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hFfour (Nat.cast_nonneg _))
  calc
    ∑ k ∈ Finset.range (q.stop ω),
        ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 =
      ∑ k : Fin (q.stop ω), F k := by
        rw [← Fin.sum_univ_eq_sum_range]
    _ ≤ _ := hmass'

/-- A running heat-vector is controlled by the initial row entry and the
entry-budget error, in a form measurable before the residual is queried. -/
theorem heatV_sq_le_initial_entry
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t c K : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) (k : ℕ) (i : Fin n)
    (hrun : k < q.stop ω) (hi : i ∈ (q.state k ω).active)
    (hbroad : BroadBounds c K (r ω)) :
    ‖heatV q k ω i‖ ^ 2 ≤ (K / c) * 2 *
      (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
        (Real.sqrt t * entryBudget t) ^ 2) := by
  obtain ⟨hx, -, -, -, -⟩ := q.heat k ω hrun
  have hstored := AndersonAC.AgentS6.hatG_eq_trialInverse q k ω
    (Nat.le_of_lt hrun) ⟨i, hi⟩ ⟨q.pivot k ω, hx⟩
  have hbudget := (q.running_budgets k ω hrun).1 i (q.pivot k ω)
  rw [hstored] at hbudget
  have hdiff :
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
          ⟨q.pivot k ω, hx⟩ - scaledInverse t (g0 ω) i (q.pivot k ω)‖ ≤
        Real.sqrt t * entryBudget t := by
    simp only [scaledInverse, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg t)]
    exact mul_le_mul_of_nonneg_left hbudget (Real.sqrt_nonneg t)
  have hnorm :
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
          ⟨q.pivot k ω, hx⟩‖ ≤
        ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ + Real.sqrt t * entryBudget t := by
    calc
      _ = ‖(scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
            ⟨q.pivot k ω, hx⟩ - scaledInverse t (g0 ω) i (q.pivot k ω)) +
            scaledInverse t (g0 ω) i (q.pivot k ω)‖ := by congr 1 <;> abel
      _ ≤ _ := by
        calc
          _ ≤ ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
                ⟨q.pivot k ω, hx⟩ - scaledInverse t (g0 ω) i (q.pivot k ω)‖ +
                ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ := norm_add_le _ _
          _ = ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ +
                ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
                  ⟨q.pivot k ω, hx⟩ - scaledInverse t (g0 ω) i (q.pivot k ω)‖ :=
                    add_comm _ _
          _ ≤ _ := by linarith [hdiff]
  have hnormSq :
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
          ⟨q.pivot k ω, hx⟩‖ ^ 2 ≤ 2 *
        (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
          (Real.sqrt t * entryBudget t) ^ 2) := by
    have hsum := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ -
      (Real.sqrt t * entryBudget t))]
  calc
    ‖heatV q k ω i‖ ^ 2 ≤ (K / c) *
        ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
          ⟨q.pivot k ω, hx⟩‖ ^ 2 := heatV_norm_sq_le q ω k i hbroad hi hx
    _ ≤ (K / c) * 2 *
        (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2 +
          (Real.sqrt t * entryBudget t) ^ 2) := by
        have hKc : 0 ≤ K / c := by
          rcases hbroad with ⟨hc, hb⟩
          rcases hb i with ⟨-, hlow, hup⟩
          exact div_nonneg (le_of_lt (hc.trans_le (hlow.trans hup))) hc.le
        nlinarith [hKc, hnormSq]

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.heatV_energy_bound
#print axioms AndersonAC.AgentS6.initial_pivot_row_energy_bound
#print axioms AndersonAC.AgentS6.heatV_sq_le_initial_entry
