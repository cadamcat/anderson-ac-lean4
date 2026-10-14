import AndersonAC.AgentS6Row.ScalarData
import AndersonAC.AgentS6Row.GramBounds
import AndersonAC.AgentS6Row.Scales

noncomputable section
open Matrix Finset ComplexConjugate MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

def jumpConstant (K c : ℝ) : ℝ :=
  8 * (4 * K) + 4 * (4 * K) ^ 2 * (K / c) +
    16 * (1 + (4 * K) ^ 2 * (K / c)) * (4 * Real.sqrt (KPhi K c))

lemma jumpConstant_nonneg {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c) : 0 ≤ jumpConstant K c := by
  unfold jumpConstant
  positivity

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

/-- The Ward estimate puts the normalized heat vector within distance one of unit mass. -/
lemma ambientHeat_vn_le_two {d : ℕ} {K c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hK : 0 ≤ K) (hc : 0 < c) (r0 : Fin n → ℂ)
    (hr : ∀ i, c ≤ (r0 i).im ∧ (r0 i).im ≤ K)
    (s : TrialState core) (x : Fin n) (hx : x ∈ s.active) (hxc : x ∉ core)
    (L : Matrix core core ℂ) (hpre : HeatPrestate t K (fun i : s.active => r0 i) (trialInverse t r0 s))
    (hcard : (core.card : ℝ) ≤ coreCap d t)
    (hsmall : K / c * (t ^ betaW + 2 * coreCap d t * Real.sqrt (fourthCap t)) ≤ 1) :
    (nheat (ambientScattering t r0 s) L x (ambientV t r0 s x hx)).vn ≤ 2 := by
  have hdev := ambientHeat_vn_bound ht hc r0 hr s x hx hxc L hpre
  have hcap := coreCap_ge_one d t ht ht1
  have hcount : (core.card : ℝ) + 1 ≤ 2 * coreCap d t := by linarith
  have hnon : 0 ≤ K / c * Real.sqrt (fourthCap t) := by positivity
  have hh := mul_le_mul_of_nonneg_right hcount hnon
  have he : K * t ^ betaW / c + 2 * coreCap d t * (K / c * Real.sqrt (fourthCap t)) =
      K / c * (t ^ betaW + 2 * coreCap d t * Real.sqrt (fourthCap t)) := by ring
  have hdev1 : |(nheat (ambientScattering t r0 s) L x (ambientV t r0 s x hx)).vn - 1| ≤ 1 := by
    calc
      _ ≤ _ := hdev
      _ ≤ K * t ^ betaW / c + 2 * coreCap d t * (K / c * Real.sqrt (fourthCap t)) := by linarith
      _ ≤ 1 := by rw [he]; exact hsmall
  exact le_trans (by linarith [(abs_le.mp hdev1).2]) le_rfl

set_option maxHeartbeats 800000 in
/-- Pathwise bound for a recorded row increment, with constants independent of the ridge and n. -/
theorem recorded_jump_bound (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (d : ℕ) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hs : Small t K)
    (hvl : leverageScale t / Real.sqrt t ≤ 1)
    (hfourth : Real.sqrt (fourthCap t) ≤ leverageScale t / Real.sqrt t)
    (hvnsmall : K / c * (t ^ betaW + 2 * coreCap d t * Real.sqrt (fourthCap t)) ≤ 1)
    (hfrosmall : 16 * KPhi K c * (leverageScale t) ^ 2 / t ≤ 1 / 4)
    (hcard : (core.card : ℝ) ≤ coreCap d t) (k : ℕ) (ω : Ω) (i : Fin n)
    (hk : k < q.stop ω) (hr : BroadBounds c K (r ω))
    (hpre : HeatPrestate t K (fun j : (q.state k ω).active => r ω j)
      (trialInverse t (r ω) (q.state k ω)))
    (hξ : |q.residual k ω| ≤ K * Real.sqrt t) :
    |recordedLeverageIncrement q k ω i| ≤ oneRowJump t (jumpConstant K c) ‖heatV q k ω i‖ := by
  classical
  have ht := hs.pos
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hp : ∀ j, 0 < (r ω j).im := fun j => hc.trans_le (hr.2 j).2.1
  have hup := q.heat k ω hk
  have hcopy := hup
  obtain ⟨hx, hxc, hact, _, _, _⟩ := hcopy
  have hτ := q.running_ridge k ω hk
  by_cases hrec : k < q.stop ω ∧ i ∈ (q.state (k + 1) ω).active ∧ i ∉ core
  · obtain ⟨_, hi', hic⟩ := hrec
    have hierase : i ∈ (q.state k ω).active.erase (q.pivot k ω) := by rw [← hact]; exact hi'
    have hi := Finset.mem_of_mem_erase hierase
    have hix := Finset.ne_of_mem_erase hierase
    have hiS : i ∈ coreᶜ.erase (q.pivot k ω) := Finset.mem_erase.mpr ⟨hix, Finset.mem_compl.mpr hic⟩
    obtain ⟨L, hL⟩ := exists_normalizer (ambientScattering t (r ω) (q.state k ω))
      core (q.ridge k ω) coreᶜ hτ
    let H := nheat (ambientScattering t (r ω) (q.state k ω)) L (q.pivot k ω)
      (ambientV t (r ω) (q.state k ω) (q.pivot k ω) hx)
    have hHm : H.m = trialWeights t (r ω) (q.state k ω) (q.ridge k ω) (q.pivot k ω) := by
      rw [nheat_m _ hτ hL, ambientLeverage_eq t (r ω) (q.state k ω) (q.ridge k ω) _ hxc]
    have hHlev : H.lev i = trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i := by
      rw [nheat_lev _ hτ hL, ambientLeverage_eq t (r ω) (q.state k ω) (q.ridge k ω) i hic]
    have hm : H.m ≤ 4 * leverageScale t := by
      rw [hHm, q.pivot_max k ω hk]
      exact (q.running_cap k ω hk).2
    have hmi : H.lev i ≤ H.m := by
      rw [hHlev, hHm, q.pivot_max k ω hk]
      exact AndersonAC.AgentS6.le_maxWeight _ _
    have hvn : H.vn ≤ 2 := ambientHeat_vn_le_two ht hs.le_one hK hc (r ω)
      (fun j => (hr.2 j).2) (q.state k ω) (q.pivot k ω) hx hxc L hpre hcard hvnsmall
    have hb : nsq H.b ≤ H.m / (t * c ^ 2) := ambientHeat_b_bound ht hc (r ω)
      (fun j => (hr.2 j).2.1) (q.state k ω) (q.pivot k ω) hx hxc (q.ridge k ω) hτ L hL
    let z := heatCoefficient t (r ω (q.pivot k ω))
      (trialInverse t (r ω) (q.state k ω) ⟨_, hx⟩ ⟨_, hx⟩) (q.residual k ω)
    have hρ : ‖r ω (q.pivot k ω)‖ ≤ K := (hr.2 _).1
    have hγ : ‖trialInverse t (r ω) (q.state k ω) ⟨_, hx⟩ ⟨_, hx⟩‖ ≤ K := by
      have hh := hpre.1 ⟨_, hx⟩
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans hh
    have hz : ‖z‖ ≤ 4 * K := norm_hc_le hs hρ hγ hξ
    have hF : fro (H.D z) ≤ 1 / 4 :=
      (fro_D_scale H ht hs.le_one hc hl.le hK hm hvn hb z hz).trans hfrosmall
    have hD : Real.sqrt (fro (H.D z)) ≤ (4 * Real.sqrt (KPhi K c)) * leverageScale t / Real.sqrt t :=
      sqrt_fro_D_scale H ht hs.le_one hc hl.le hK hm hvn hb z hz
    have hvi : ‖H.v i‖ ^ 2 ≤ (K / c) * leverageScale t / Real.sqrt t := by
      calc
        _ ≤ K / c * Real.sqrt (fourthCap t) := ambientV_sq_le ht hc (r ω)
          (fun j => (hr.2 j).2) (q.state k ω) (q.pivot k ω) hx hpre i
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hfourth (div_nonneg hK hc.le)
          simpa only [mul_div_assoc] using hh
    have hjump := row_jump_bound H z i ht hl (by positivity : 0 ≤ 4 * K)
      (div_nonneg hK hc.le) (by positivity : 0 ≤ 4 * Real.sqrt (KPhi K c))
      hvl hm hmi hz hvi hF hD
    have hV : heatV q k ω i = ambientV t (r ω) (q.state k ω) (q.pivot k ω) hx i := by
      simp [heatV, ambientV, hi, hx]
    rw [recordedLeverageIncrement, if_pos ⟨hk, hi', hic⟩]
    rw [← normalized_trial_row_update ht (r ω) hp hup hx (q.ridge k ω) hτ L hL i hiS]
    simpa only [H, z, nheat, jumpConstant, oneRowJump, hV] using hjump
  · rw [recordedLeverageIncrement, if_neg hrec, abs_zero]
    unfold oneRowJump
    have hJ := jumpConstant_nonneg hK hc
    positivity

end AndersonAC.AgentS6Row

#print axioms AndersonAC.AgentS6Row.recorded_jump_bound
