import AndersonAC.AgentS6.Increments
import AndersonAC.AgentS6.Margins

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

theorem active_antitone (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ q.stop ω) :
    (q.state b ω).active ⊆ (q.state a ω).active := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    exact Finset.Subset.refl _
  | succ b ih =>
    by_cases ha : a = b + 1
    · subst a; exact Finset.Subset.refl _
    · obtain ⟨-, -, hact, -⟩ := q.heat b ω (by omega)
      rw [hact]
      exact (Finset.erase_subset _ _).trans (ih (by omega) (by omega))

theorem pivot_not_active_later (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω)
    {a b : ℕ} (hab : a < b) (hb : b ≤ q.stop ω) :
    q.pivot a ω ∉ (q.state b ω).active := by
  obtain ⟨-, -, hact, -⟩ := q.heat a ω (by omega)
  intro h
  have h' := active_antitone q ω (Nat.succ_le_of_lt hab) hb h
  rw [hact] at h'
  exact (Finset.mem_erase.mp h').1 rfl

theorem pivots_injective (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω)
    (m : ℕ) (hm : m ≤ q.stop ω) :
    Function.Injective (fun k : Fin m => q.pivot k ω) := by
  intro a b h
  apply Fin.ext
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hab
  · have hbactive := (q.heat b ω (by omega)).choose
    apply pivot_not_active_later q ω hab (by omega)
    simpa only [h] using hbactive
  · have haactive := (q.heat a ω (by omega)).choose
    apply pivot_not_active_later q ω hab (by omega)
    simpa only [h] using haactive

/-- The sum includes the last running prestate, hence the possible breaking heat. -/
theorem pivot_fourth_sum_le (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hstart : ∀ i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t)
    (m : ℕ) (hm : m ≤ q.stop ω) (i : Fin n) :
    ∑ k : Fin m, ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 4 ≤
      16 * fourthCap t := by
  have hfour := AndersonAC.S6.pivot_fourth t m (fun k => q.pivot k ω) (g0 ω)
    (fun k => (q.state k ω).hatG) i (pivots_injective q ω m hm)
    (fun k => (q.running_budgets k ω (by omega)).1 i (q.pivot k ω))
  have hmnat : (m : ℝ) ≤ (heatLimit t : ℝ) := by
    exact_mod_cast hm.trans (q.finite_stop ω)
  have hmheat : (m : ℝ) ≤ t ^ (-1 - eh) :=
    hmnat.trans (Nat.floor_le (Real.rpow_nonneg ht.le _))
  have herror : (m : ℝ) * (Real.sqrt t * entryBudget t) ^ 4 ≤ fourthCap t := by
    calc
      (m : ℝ) * (Real.sqrt t * entryBudget t) ^ 4
          ≤ t ^ (-1 - eh) * (Real.sqrt t * entryBudget t) ^ 4 := by gcongr
      _ = t ^ (1 + (122 / 100) * delta) := by
        unfold entryBudget
        rw [mul_pow, show (Real.sqrt t) ^ 4 = t ^ 2 by
          rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt ht.le],
          ← Real.rpow_natCast (t ^ ((42 / 100) * delta)) 4,
          ← Real.rpow_mul ht.le, ← Real.rpow_natCast t 2,
          ← Real.rpow_add ht, ← Real.rpow_add ht]
        congr 1
        unfold eh
        push_cast
        ring
      _ ≤ fourthCap t := rpow_anti ht ht1 (by unfold delta; norm_num)
  unfold Planned.pivot_fourth at hfour
  dsimp only at hfour
  ring_nf at hfour herror
  have hH0 : 0 ≤ fourthCap t := Real.rpow_nonneg ht.le _
  nlinarith [hstart i]

theorem pivot_square_sum_le (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hstart : ∀ i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t)
    (m : ℕ) (hm : m ≤ q.stop ω) (i : Fin n) :
    ∑ k : Fin m, ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 2 ≤
      4 * t ^ ((27 / 100) * delta) := by
  have hmass := AndersonAC.S6.pivot_mass m
    (fun k => ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 2)
    (fun k => sq_nonneg _)
  have hfour := pivot_fourth_sum_le q ω ht ht1 hstart m hm i
  have hmnat : (m : ℝ) ≤ (heatLimit t : ℝ) := by
    exact_mod_cast hm.trans (q.finite_stop ω)
  have hmheat : (m : ℝ) ≤ t ^ (-1 - eh) :=
    hmnat.trans (Nat.floor_le (Real.rpow_nonneg ht.le _))
  have hprod : (m : ℝ) *
      (∑ k : Fin m, (‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 2) ^ 2) ≤
      (4 * t ^ ((27 / 100) * delta)) ^ 2 := by
    calc
      _ ≤ t ^ (-1 - eh) * (16 * fourthCap t) := by
        apply mul_le_mul hmheat _ (by positivity) (by positivity)
        simpa only [← pow_mul] using hfour
      _ = _ := by
        unfold fourthCap
        have hexp : (-1 - eh) + (1 + delta) = ((27 / 100) * delta) * 2 := by
          unfold eh
          ring
        calc
          t ^ (-1 - eh) * (16 * t ^ (1 + delta))
              = 16 * (t ^ (-1 - eh) * t ^ (1 + delta)) := by ring
          _ = 16 * t ^ ((-1 - eh) + (1 + delta)) := by rw [← Real.rpow_add ht]
          _ = 16 * t ^ (((27 / 100) * delta) * 2) := by rw [hexp]
          _ = (4 * t ^ ((27 / 100) * delta)) ^ 2 := by
            rw [mul_pow, ← Real.rpow_natCast (t ^ ((27 / 100) * delta)) 2,
              ← Real.rpow_mul ht.le]
            norm_num
  exact hmass.trans (Real.sqrt_le_iff.mpr ⟨by positivity, hprod⟩)

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.pivots_injective
#print axioms AndersonAC.AgentS6Budget.pivot_fourth_sum_le
#print axioms AndersonAC.AgentS6Budget.pivot_square_sum_le
