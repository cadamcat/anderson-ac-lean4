import AndersonAC.AgentS78.Construction.FinalSweep
import AndersonAC.AgentS78.Construction.SweepReserveRowTools

/-!
# Row tails of the committed sweep

`AndersonAC.AgentS78.sweepRowTail_proof : SweepRowTailStatement d` uses the statement
in `SweepEndReserve.lean:150` and is consumed by `sweepReserveRow_of_tails`.
Paper: 05-local-sweeps.tex:155–239 (Lemma `local-prospective`, the
scalar row tails), used in 05:568–577.

**Proof.** The row-step bound (`poly_row_step_bound`, copied as
`row_step_bound` in SweepReserveRowTools.lean, generic port type) at every committed step of
`x.sweep` on the ambient ports `Port d m`. Its inputs at step `k`:

* the step relation and mask from `TileSweepCore.wellFormed`;
* `|h| ≤ 1` from the row cap of `TileSweepCore.valid k` (`entry_small`);
* the decay `|h_ab| ≤ C/√t · exp(−t³ dist/C)` from `TileSweepCore.start.prefix_decay` at the
  valid prefix `k` (live entries; dead ambient entries vanish);
* the deletion coefficient `|γ| ≤ 2(2 + C)` (`gamma_le_of_entry`): from the row cap
  (`|h_yy| ≤ t^{1/4}`), `|ξ| ≤ 2√t` (`scalar_bound`) and `‖r_y‖ ≤ C` (the broad bound of the v3
  start prestate on `startV3`, entrywise equal to `portR`). No `‖K‖ ≤ 3/4` / rawLag bound, hence
  no cumulative Schur identity, is needed for the rows: the denominator `1 + (ξ + t r_y) g_yy`
  is `≥ 1/2` because `|(ξ + t r_y) g_yy| ≤ (2 + C) t^{1/4}`.

The constants: `Ct = 5 + 3d`, `ct = min 1 (1/C)`; `StageBounds` is not used.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78resrow

open AndersonAC.S78
open AndersonAC.AgentS78
open AndersonAC.S45 (power rowCap delta reserves)

variable {d m : ℕ}

theorem sweepScale_pos'' {u : ℝ} (hu : 0 < u) (m j : ℕ) : 0 < sweepScale u m j := by
  unfold sweepScale stageScale
  split_ifs <;> positivity

section Tail

variable {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}
  {done : Finset (Fin (P.cover j).cover.count)} {x : RunRecord d m}

/-- **Per-step row tail of the committed sweep** (05:155–239 through sweep transfer's row-step bound):
`|stepRow cols k i| ≤ A t^{-(4+3d)} exp(−c t³ dist(i, x_k))` with `A` depending on `d, C, c`. -/
theorem step_row_tail (hx : TileSweepCore C P j n₀ u E ρ Cb done x) (hC : 1 ≤ C)
    (ht : 0 < sweepScale P.u m j) (ht1 : sweepScale P.u m j ≤ 1)
    (hsmall : (2 + C) * power (sweepScale P.u m j) (1 / 4) ≤ 1 / 2)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcC : c ≤ 1 / C)
    {k : ℕ} (hk : k < x.sweep.length) {y : Port d m} (hy : x.sweep.pivot k = some y)
    (cols : Finset (Port d m)) (i : Port d m) :
    |x.sweep.stepRow (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) cols k i| ≤
      (4 * (1 + 2 * (2 + C)) ^ 3 * (2 * (2 + C)) * C ^ 3 * power c (-(d : ℝ))) *
        power (sweepScale P.u m j) (-(4 + 3 * (d : ℝ))) *
        Real.exp (-c * (sweepScale P.u m j) ^ 3 * (P.cover j).dist i y) := by
  classical
  set t := sweepScale P.u m j with htdef
  set r := portR (sweepTheta P.u m j) x.r with hrdef
  have hC0 : 0 < C := by linarith
  have hwf := hx.wellFormed
  have ha_wf := hwf.1 k hk.le
  have hrel : S45.StepRel t r (x.sweep.state k) (x.sweep.state (k + 1)) y (x.sweep.scalar k) := by
    have h := hwf.2 k hk
    rw [hy] at h
    exact h
  have hval := hx.valid k hk.le
  have hent := entry_small t _ ht ht1 hval.2.2.1
  have hv1 : power t (1 / 4) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hsm : ∀ a b, ‖((x.sweep.state k).ambient r).h t a b‖ ≤ 1 :=
    amb_h_norm_le _ r t (fun _ _ => 1) (fun _ _ => zero_le_one)
      (fun a b => (hent a b).trans hv1)
  have hdecay := (hx.start.prefix_decay x.sweep hwf rfl hx.bit_pivots k hk.le hval).1
  have hdec : ∀ a b, ‖((x.sweep.state k).ambient r).h t a b‖ ≤
      C / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist a b / C) :=
    amb_h_norm_le _ r t (fun a b => C / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist a b / C))
      (fun _ _ => by positivity) (fun a b => hdecay a b)
  -- the deletion coefficient
  have hylive : y ∈ (x.sweep.state k).live := hrel.pivot_live
  have hy0 : y ∈ (x.sweep.state 0).live := live_sub_of_le hwf (Nat.zero_le k) hk.le hylive
  have hyact : y.1 ∈ x.endpoint.active := by
    rw [hx.start_live] at hy0
    exact (Finset.mem_filter.1 hy0).2
  have hyy : ‖((x.sweep.state k).ambient r).h t y y‖ ≤ power t (1 / 4) :=
    amb_h_norm_le _ r t (fun _ _ => power t (1 / 4)) (fun _ _ => Real.rpow_nonneg ht.le _)
      (fun a b => hent a b) y y
  obtain ⟨Λplus, Wstar, hpre, -⟩ := hx.start.start_prestate
  have hry : ‖((x.sweep.state k).ambient r).r y‖ ≤ C := by
    have h := (hpre.broad ((⟨y.1, hyact⟩, y.2) :
      S45.initialPorts {i // i ∈ x.endpoint.active})).1
    exact h
  have hξ : |x.sweep.scalar k| ≤ 2 * Real.sqrt t := hx.scalar_bound k hk
  have hγ := gamma_le_of_entry t C ((x.sweep.state k).ambient r) y (x.sweep.scalar k) ht ht1
    hC0.le hyy hry hξ hsmall
  exact row_step_bound ht ht1 hC0 (by positivity) hc hc1 hcC hx.plan.shell ha_wf hrel hsm hdec
    hγ cols i

end Tail

end AndersonAC.AgentS78resrow

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78resrow
open AndersonAC.S45 (power rowCap delta reserves)

/-- **Row tails of the committed sweep** (05:155–239), for every sweep including the final
residual one (`j ≤ m + 1`; the bound `j ≤ m` is never used: the clauses of `TileSweepCore` used
here — wellFormed, valid, prefix_decay, scalar_bound `|ξ| ≤ 2√t`, start_prestate — have the same
form for the final sweep, `θ = 1/2`, `t = sweepScale u m (m+1)`). -/
theorem sweepRowTailFull_proof (d : ℕ) : SweepRowTailFullStatement d := by
  classical
  intro cP CP cL CL C₀ _ _ _ _ _ C hC
  have hC0 : 0 < C := by linarith
  set c : ℝ := min 1 (1 / C) with hcdef
  have hc : 0 < c := lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcC : c ≤ 1 / C := min_le_right _ _
  have hpc : 0 < power c (-(d : ℝ)) := Real.rpow_pos_of_pos hc _
  set A : ℝ := 4 * (1 + 2 * (2 + C)) ^ 3 * (2 * (2 + C)) * C ^ 3 * power c (-(d : ℝ)) with hAdef
  have hA : 0 < A := by positivity
  obtain ⟨t2, ht2, hs2⟩ := AgentS45.power_small (e := 1 / 4) (by norm_num)
    (a := 1 / (2 * (2 + C))) (by positivity)
  refine ⟨5 + 3 * (d : ℝ), by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); linarith, c, hc, min t2 (min 1 (1 / A)), by positivity, ?_⟩
  intro m n₀ u E ρ P j Cb x _ hu huI _ _ htt _ hx k hk y hy i
  subst hu
  set t := sweepScale P.u m j with htdef
  have hu0 : 0 < P.u := lt_trans (by norm_num) huI.1
  have ht : 0 < t := sweepScale_pos'' hu0 m j
  have htt2 : t < t2 := lt_of_lt_of_le htt (min_le_left _ _)
  have ht1 : t ≤ 1 := (lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))).le
  have htA : t ≤ 1 / A := (lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))).le
  have hsmall : (2 + C) * power t (1 / 4) ≤ 1 / 2 := by
    have h := hs2 t ht htt2
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith
  have hAt : A ≤ power t (-1) := by
    have hpt : power t (-1) = t⁻¹ := by
      show t ^ (-1 : ℝ) = t⁻¹
      rw [Real.rpow_neg ht.le, Real.rpow_one]
    rw [hpt, ← one_div, le_div_iff₀ ht]
    rw [le_div_iff₀ hA] at htA
    linarith
  have h := step_row_tail hx hC ht ht1 hsmall hc hc1 hcC hk hy reserves i
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  calc A * power t (-(4 + 3 * (d : ℝ))) ≤ power t (-1) * power t (-(4 + 3 * (d : ℝ))) :=
        mul_le_mul_of_nonneg_right hAt (Real.rpow_nonneg ht.le _)
    _ = power t (-(5 + 3 * (d : ℝ))) := by rw [power_mul' ht]; ring_nf

/-- The digit form. -/
theorem sweepRowTail_proof (d : ℕ) : SweepRowTailStatement d :=
  (sweepRowTailFull_proof d).digit

end AndersonAC.AgentS78
