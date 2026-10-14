import AndersonAC.AgentS6.CapTelescope
import AndersonAC.AgentS6.RunningPrestate

/-! One-step estimates for the predictable row stream. -/

noncomputable section
open scoped BigOperators

namespace AndersonAC.AgentS6

open AndersonAC.S6

/-! A site is never selected twice before the stopping time. -/
theorem pivot_injective_running
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) :
    Set.InjOn (fun k => q.pivot k ω) {k : ℕ | k < q.stop ω} := by
  intro k hk l hl heq
  change q.pivot k ω = q.pivot l ω at heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · obtain ⟨hxk, hxkc, hactivek, -, -⟩ := q.heat k ω hk
    obtain ⟨hxl, -, -, -, -⟩ := q.heat l ω hl
    have hnot : q.pivot k ω ∉ (q.state (k + 1) ω).active := by
      rw [hactivek]
      simp
    have hsub := active_antitone q ω (Nat.succ_le_of_lt hkl) (Nat.le_of_lt hl)
    have hmem : q.pivot k ω ∈ (q.state l ω).active := by
      rw [heq]
      exact hxl
    exact hnot (hsub hmem)
  · obtain ⟨hxl, hxlc, hactivel, -, -⟩ := q.heat l ω hl
    obtain ⟨hxk, -, -, -, -⟩ := q.heat k ω hk
    have hnot : q.pivot l ω ∉ (q.state (l + 1) ω).active := by
      rw [hactivel]
      simp
    have hsub := active_antitone q ω (Nat.succ_le_of_lt hlk) (Nat.le_of_lt hk)
    have hmem : q.pivot l ω ∈ (q.state k ω).active := by
      rw [← heq]
      exact hxk
    exact hnot (hsub hmem)

/-- The damping factor in `heatV` costs at most `K/c` in squared norm. -/
theorem heatV_norm_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t c K : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) (k : ℕ) (i : Fin n)
    (hbroad : BroadBounds c K (r ω)) (hi : i ∈ (q.state k ω).active)
    (hx : q.pivot k ω ∈ (q.state k ω).active) :
    ‖heatV q k ω i‖ ^ 2 ≤ (K / c) *
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω))
        ⟨i, hi⟩ ⟨q.pivot k ω, hx⟩‖ ^ 2 := by
  rcases hbroad with ⟨hc, hsite⟩
  rcases hsite i with ⟨-, hpiLow, hpiUp⟩
  rcases hsite (q.pivot k ω) with ⟨-, hpxLow, -⟩
  have hpi : 0 < (r ω i).im := hc.trans_le hpiLow
  have hpx : 0 < (r ω (q.pivot k ω)).im := hc.trans_le hpxLow
  have hK0 : 0 ≤ K := le_trans hc.le (hpiLow.trans hpiUp)
  have hratio0 : 0 ≤ (r ω i).im / (r ω (q.pivot k ω)).im :=
    div_nonneg hpi.le hpx.le
  have hratio : (r ω i).im / (r ω (q.pivot k ω)).im ≤ K / c := by
    calc
      (r ω i).im / (r ω (q.pivot k ω)).im ≤ K / (r ω (q.pivot k ω)).im :=
        div_le_div_of_nonneg_right hpiUp hpx.le
      _ ≤ K / c := (div_le_div_iff₀ hpx hc).2
        (mul_le_mul_of_nonneg_left hpxLow hK0)
  rw [heatV, dif_pos hi, dif_pos hx]
  calc
    ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
        ⟨q.pivot k ω, hx⟩ *
          (Real.sqrt ((r ω i).im / (r ω (q.pivot k ω)).im) : ℂ)‖ ^ 2
        = ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
            ⟨q.pivot k ω, hx⟩‖ ^ 2 * ((r ω i).im / (r ω (q.pivot k ω)).im) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt hratio0]
    _ = ((r ω i).im / (r ω (q.pivot k ω)).im) *
          ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hi⟩
            ⟨q.pivot k ω, hx⟩‖ ^ 2 := by ring
    _ ≤ (K / c) * ‖scaledInverse t (trialInverse t (r ω) (q.state k ω))
          ⟨i, hi⟩ ⟨q.pivot k ω, hx⟩‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _)

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.pivot_injective_running
#print axioms AndersonAC.AgentS6.heatV_norm_sq_le
