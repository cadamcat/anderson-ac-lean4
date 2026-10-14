import AndersonAC.AgentS78.Construction.TileTransfer
import AndersonAC.AgentS78.Construction.TileTrialFirst
import AndersonAC.AgentS78.Construction.TileCoreA3
import AndersonAC.S2.Binary
import AndersonAC.S45.LocalTransferProof
import AndersonAC.S45.LocalTransferLProof
import AndersonAC.S45.StepLProof
import AndersonAC.S45.CumulativeSchurProof
import AndersonAC.S45.PrestateProof
import AndersonAC.S45.GammaProof
import AndersonAC.S45.LocalityProof
import AndersonAC.S45.RestrictLive

/-!
# WP10 construction, C4a core, piece A3b: tile transfer (`TileTransferStatement`)

Proves `AndersonAC.AgentS78.tileTransfer_proof` (05-local-sweeps.tex:844–860, Lemma
`local-transfer` 05:538–564, Lemma `local-prospective` 05:155–239).
-/

open MeasureTheory Matrix
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw signValue binarySuffix
  abs_signValue binarySuffix_bound)

/-! ## Section 1: Scale, weight, and normalized scalar bounds -/

/-- For `0 < u`, `0 < j ≤ m + 1`, the sweep ratio `θ = sweepTheta u m j` lies in `[1/4, 5/8]`. -/
theorem sweepTheta_bounds_a3b {u : ℝ} (hu : 0 < u) {m j : ℕ} (hj0 : 0 < j) (hjm : j ≤ m + 1) :
    1 / 4 ≤ sweepTheta u m j ∧ sweepTheta u m j ≤ 5 / 8 := by
  unfold sweepTheta
  split_ifs with hf
  · constructor <;> norm_num
  · have hle : j ≤ m := by unfold IsFinalSweep at hf; omega
    unfold stageScale
    set a : ℝ := u / (4 : ℝ) ^ j with ha_def
    set b : ℝ := u / (4 : ℝ) ^ m with hb_def
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hj1 : u / (4 : ℝ) ^ (j - 1) = 4 * a := by
      rw [ha_def]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    have hba : b ≤ a := by
      rw [ha_def, hb_def]
      exact div_le_div_of_nonneg_left hu.le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hle)
    rw [hj1]
    have hden : 0 < 4 * a + b := by positivity
    constructor
    · rw [le_div_iff₀ hden]
      linarith
    · rw [div_le_iff₀ hden]
      linarith

/-- For `0 < u`, `0 < j ≤ m + 1`, the bit-port weight `w = 1 - θ` lies in `[3/8, 3/4]`. -/
theorem sweepW_bounds {u : ℝ} (hu : 0 < u) {m j : ℕ} (hj0 : 0 < j) (hjm : j ≤ m + 1) :
    3 / 8 ≤ sweepW u m j ∧ sweepW u m j ≤ 3 / 4 := by
  obtain ⟨h1, h2⟩ := sweepTheta_bounds_a3b hu hj0 hjm
  unfold sweepW
  constructor <;> linarith

theorem sweepW_pos_a3b {u : ℝ} (hu : 0 < u) {m j : ℕ} (hj0 : 0 < j) (hjm : j ≤ m + 1) :
    0 < sweepW u m j :=
  lt_of_lt_of_le (by norm_num) (sweepW_bounds hu hj0 hjm).1

/-- At an ordinary digit sweep (`¬ IsFinalSweep m j`), `digitAmp u (j - 1) = √(w t)`. -/
theorem digitAmp_eq_sqrt_sweepW_scale {u : ℝ} (hu : 0 < u) {m j : ℕ} (hj0 : 0 < j)
    (hf : ¬ IsFinalSweep m j) :
    digitAmp u (j - 1) = Real.sqrt (sweepW u m j * sweepScale u m j) := by
  unfold digitAmp sweepW sweepTheta sweepScale
  simp only [hf, ↓reduceIte]
  congr 1
  unfold stageScale
  set a : ℝ := u / (4 : ℝ) ^ (j - 1) with ha_def
  set b : ℝ := u / (4 : ℝ) ^ m with hb_def
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hj1 : u / (4 : ℝ) ^ j = a / 4 := by
    rw [ha_def]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  rw [hj1]
  have hden : a + b ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- At the final sweep (`IsFinalSweep m j`), `couplingOf u n₀ / 2 ^ (m - n₀) = √(3 w t)` when
`n₀ ≤ m` and `j ≤ m + 1`. -/
theorem final_suffix_amp_eq {u : ℝ} (hu : 0 < u) {n₀ m j : ℕ} (hnm : n₀ ≤ m)
    (hf : IsFinalSweep m j) :
    couplingOf u n₀ / (2 : ℝ) ^ (m - n₀) =
      Real.sqrt (3 * (sweepW u m j * sweepScale u m j)) := by
  unfold couplingOf sweepW sweepTheta sweepScale stageScale
  simp only [hf, ↓reduceIte]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (m - n₀) := by positivity
  rw [← Real.sqrt_sq h2pos.le, ← Real.sqrt_div (by positivity)]
  congr 1
  have hpow : ((2 : ℝ) ^ (m - n₀)) ^ 2 = (4 : ℝ) ^ (m - n₀) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h4 : (4 : ℝ) ^ n₀ * (4 : ℝ) ^ (m - n₀) = (4 : ℝ) ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hnm]
  rw [hpow, div_div, h4]
  ring

/-- Every slot's physical increment satisfies `|tileZeta| ≤ √3 · √(w t)`. -/
theorem abs_tileZeta_le {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : 0 < P.u) (hj : P.n₀ < j) (hjm : j ≤ m + 1) (hx : TileGoodCore C P j T x)
    (i : Torus d m) (ω : RandomSources (Torus d m) M) :
    |tileZeta P j T M x i ω| ≤
      Real.sqrt 3 * Real.sqrt (sweepW P.u m j * sweepScale P.u m j) := by
  have hj0 : 0 < j := by omega
  have hwpos : 0 < sweepW P.u m j := sweepW_pos_a3b hu hj0 hjm
  have htpos : 0 < sweepScale P.u m j := sweepScale_pos_first hu m j
  have h1le3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  by_cases hact : activeIn P j T x i
  · by_cases hpend : i ∈ x.pending
    · by_cases hfin : IsFinalSweep m j
      · exfalso
        exact hx.final_no_pending hfin i hact.1 hact.2.1 hpend
      · simp only [tileZeta, hact, hpend, not_true_eq_false, ↓reduceIte]
        rw [abs_mul, abs_signValue, mul_one, digitAmp_eq_sqrt_sweepW_scale hu hj0 hfin,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        nlinarith [Real.sqrt_nonneg (sweepW P.u m j * sweepScale P.u m j)]
    · by_cases hfin : IsFinalSweep m j
      · simp only [tileZeta, hact, hpend, not_false_eq_true, hfin, ↓reduceIte]
        have hnm : P.n₀ ≤ m := by unfold IsFinalSweep at hfin; omega
        have hpref : x.prefixLength i = m - P.n₀ :=
          hx.final_prefix hfin i hact.1 hact.2.1
        rw [hpref]
        have hb := binarySuffix_bound (couplingOf P.u P.n₀) (m - P.n₀)
          (fun k => ω.1 (Sum.inl (i, k)))
        have hcpos : 0 ≤ couplingOf P.u P.n₀ := by unfold couplingOf; positivity
        rw [abs_of_nonneg hcpos, final_suffix_amp_eq hu hnm hfin,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)] at hb
        exact hb
      · simp only [tileZeta, hact, hpend, not_false_eq_true, hfin, ↓reduceIte]
        rw [abs_mul, abs_signValue, mul_one, digitAmp_eq_sqrt_sweepW_scale hu hj0 hfin,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        nlinarith [Real.sqrt_nonneg (sweepW P.u m j * sweepScale P.u m j)]
  · simp only [tileZeta, hact, ↓reduceIte]
    rw [abs_mul, abs_signValue, mul_one, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sqrt_nonneg (sweepW P.u m j * sweepScale P.u m j)]

/-- Every slot's normalized scalar satisfies `|tileXi| ≤ 2 √t`. -/
theorem abs_tileXi_le {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : 0 < P.u) (hj : P.n₀ < j) (hjm : j ≤ m + 1) (hx : TileGoodCore C P j T x)
    (k : ℕ) (ω : RandomSources (Torus d m) M) :
    |tileXi P j T M x k ω| ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
  have hj0 : 0 < j := by omega
  have hwpos : 0 < sweepW P.u m j := sweepW_pos_a3b hu hj0 hjm
  have htpos : 0 < sweepScale P.u m j := sweepScale_pos_first hu m j
  unfold tileXi
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hwpos)]
  have hz := abs_tileZeta_le P j T M x hu hj hjm hx (tileSlot P j T M k ω) ω
  have hdiv : Real.sqrt 3 * Real.sqrt (sweepW P.u m j * sweepScale P.u m j) /
      Real.sqrt (sweepW P.u m j) = Real.sqrt 3 * Real.sqrt (sweepScale P.u m j) := by
    have hwne : Real.sqrt (sweepW P.u m j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hwpos)
    rw [Real.sqrt_mul hwpos.le]
    field_simp [hwne]
  have h3le2 : Real.sqrt 3 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc |tileZeta P j T M x (tileSlot P j T M k ω) ω| / Real.sqrt (sweepW P.u m j)
      ≤ Real.sqrt 3 * Real.sqrt (sweepW P.u m j * sweepScale P.u m j) /
          Real.sqrt (sweepW P.u m j) :=
        div_le_div_of_nonneg_right hz (Real.sqrt_nonneg _)
    _ = Real.sqrt 3 * Real.sqrt (sweepScale P.u m j) := hdiv
    _ ≤ 2 * Real.sqrt (sweepScale P.u m j) :=
        mul_le_mul_of_nonneg_right h3le2 (Real.sqrt_nonneg _)

/-! ## Section 2: `extendSeq`, `candidate`, and `slotSeq` invariants -/

section SeqLemmas
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

theorem extendSeq_length_a3b (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ : ℝ) : (extendSeq q b p ξ).length = q.length + 1 := rfl

theorem extendSeq_state_of_le (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ : ℝ) {s : ℕ} (hs : s ≤ q.length) :
    (extendSeq q b p ξ).state s = q.state s := by
  simp [extendSeq, show s ≠ q.length + 1 by omega]

theorem extendSeq_state_last_a3b (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ : ℝ) :
    (extendSeq q b p ξ).state (q.length + 1) = b := by
  simp [extendSeq]

theorem extendSeq_pivot_of_lt (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ : ℝ) {s : ℕ} (hs : s < q.length) :
    (extendSeq q b p ξ).pivot s = q.pivot s := by
  simp [extendSeq, show s ≠ q.length by omega]

theorem extendSeq_pivot_last_a3b (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ : ℝ) :
    (extendSeq q b p ξ).pivot q.length = some p := by
  simp [extendSeq]

theorem extendSeq_scalar_of_lt (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ : ℝ) {s : ℕ} (hs : s < q.length) :
    (extendSeq q b p ξ).scalar s = q.scalar s := by
  simp [extendSeq, show s ≠ q.length by omega]

theorem extendSeq_scalar_last_a3b (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ : ℝ) :
    (extendSeq q b p ξ).scalar q.length = ξ := by
  simp [extendSeq]

theorem extendSeq_stepJ_of_lt (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ t : ℝ) (r : Port d m → ℂ) {s : ℕ} (hs : s < q.length) :
    (extendSeq q b p ξ).stepJ t r s = q.stepJ t r s := by
  unfold S45.Sequence.stepJ
  rw [extendSeq_pivot_of_lt q b p ξ hs, extendSeq_state_of_le q b p ξ hs.le,
    extendSeq_state_of_le q b p ξ (by omega : s + 1 ≤ q.length),
    extendSeq_scalar_of_lt q b p ξ hs]

theorem extendSeq_stepL_of_lt (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ t : ℝ) (r : Port d m → ℂ) {s : ℕ} (hs : s < q.length) :
    (extendSeq q b p ξ).stepL t r s = q.stepL t r s := by
  unfold S45.Sequence.stepL
  rw [extendSeq_pivot_of_lt q b p ξ hs, extendSeq_state_of_le q b p ξ hs.le,
    extendSeq_state_of_le q b p ξ (by omega : s + 1 ≤ q.length),
    extendSeq_scalar_of_lt q b p ξ hs]

theorem extendSeq_stepLag_of_lt (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ t : ℝ) (r : Port d m → ℂ) {s : ℕ} (hs : s < q.length) :
    (extendSeq q b p ξ).stepLag t r s = q.stepLag t r s := by
  funext i
  unfold S45.Sequence.stepLag
  rw [extendSeq_state_of_le q b p ξ hs.le,
    extendSeq_state_of_le q b p ξ (by omega : s + 1 ≤ q.length)]

theorem extendSeq_stepRow_of_lt (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ t : ℝ) (r : Port d m → ℂ) (cols : Finset (Port d m))
    {s : ℕ} (hs : s < q.length) :
    (extendSeq q b p ξ).stepRow t r cols s = q.stepRow t r cols s := by
  funext i
  unfold S45.Sequence.stepRow
  rw [extendSeq_state_of_le q b p ξ hs.le,
    extendSeq_state_of_le q b p ξ (by omega : s + 1 ≤ q.length)]

theorem extendSeq_records_of_subset (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ t : ℝ) (r : Port d m → ℂ) {K : Finset ℕ}
    (hK : K ⊆ Finset.range q.length) :
    (extendSeq q b p ξ).Jrecord t r K = q.Jrecord t r K ∧
    (extendSeq q b p ξ).Lrecord t r K = q.Lrecord t r K ∧
    (extendSeq q b p ξ).lagRecord t r K = q.lagRecord t r K ∧
    (∀ cols, (extendSeq q b p ξ).rowRecord t r cols K = q.rowRecord t r cols K) := by
  refine ⟨Finset.sum_congr rfl fun s hs =>
      extendSeq_stepJ_of_lt q b p ξ t r (Finset.mem_range.mp (hK hs)),
    Finset.sum_congr rfl fun s hs =>
      extendSeq_stepL_of_lt q b p ξ t r (Finset.mem_range.mp (hK hs)),
    Finset.sum_congr rfl fun s hs =>
      extendSeq_stepLag_of_lt q b p ξ t r (Finset.mem_range.mp (hK hs)),
    fun cols => Finset.sum_congr rfl fun s hs =>
      extendSeq_stepRow_of_lt q b p ξ t r cols (Finset.mem_range.mp (hK hs))⟩

theorem extendSeq_valid_of_le (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (p : Port d m) (ξ t : ℝ) (r : Port d m → ℂ) (D0 : S45.RMat (Port d m))
    {s : ℕ} (hs : s ≤ q.length) (hv : q.valid t r D0 s) :
    (extendSeq q b p ξ).valid t r D0 s := by
  have hsub : Finset.range s ⊆ Finset.range q.length := Finset.range_mono hs
  obtain ⟨hJ, hL, _, _⟩ := extendSeq_records_of_subset q b p ξ t r hsub
  unfold S45.Sequence.valid at hv ⊢
  rw [hJ, hL, extendSeq_state_of_le q b p ξ hs]
  exact hv

/-- Structural invariant of a prefix `q` produced by `slotSeq P j T M x k ω = some q`. -/
structure SlotSeqInv (x : RunRecord d m) (ω : RandomSources (Torus d m) M)
    (q : S45.Sequence (Port d m)) : Prop where
  len_ge : x.sweep.length ≤ q.length
  wellFormed : q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
  state_prefix : ∀ s ≤ x.sweep.length, q.state s = x.sweep.state s
  pivot_prefix : ∀ s < x.sweep.length, q.pivot s = x.sweep.pivot s
  scalar_prefix : ∀ s < x.sweep.length, q.scalar s = x.sweep.scalar s
  trial_step : ∀ s, x.sweep.length ≤ s → s < q.length →
    ∃ l < slotCount P j T,
      activeIn P j T x (tileSlot P j T M l ω) ∧
      q.pivot s = some (tileSlot P j T M l ω, false) ∧
      q.scalar s = tileXi P j T M x l ω
  valid : ∀ s ≤ q.length,
    q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (stageD0 P j x) s

theorem slotSeq_inv {C : ℝ} (x : RunRecord d m) (hx : TileGoodCore C P j T x)
    (ω : RandomSources (Torus d m) M) :
    ∀ k q, slotSeq P j T M x k ω = some q → SlotSeqInv P j T M x ω q := by
  intro k
  induction k with
  | zero =>
    intro q hq
    simp only [slotSeq, Option.some.injEq] at hq
    subst hq
    exact {
      len_ge := le_rfl
      wellFormed := hx.wellFormed
      state_prefix := fun _ _ => rfl
      pivot_prefix := fun _ _ => rfl
      scalar_prefix := fun _ _ => rfl
      trial_step := fun s h1 h2 => by omega
      valid := hx.valid
    }
  | succ k ih =>
    intro q hq
    simp only [slotSeq] at hq
    split_ifs at hq with hk
    · obtain ⟨q0, hq0, hstep⟩ := Option.bind_eq_some_iff.mp hq
      have inv0 := ih q0 hq0
      unfold slotStep at hstep
      split_ifs at hstep with hal hok
      · simp only [Option.some.injEq] at hstep
        subst hstep
        set y := tileSlot P j T M k ω
        set ξ := tileXi P j T M x k ω
        set t := sweepScale P.u m j
        set r := portR (sweepTheta P.u m j) x.r
        set b := stepLive t r (q0.state q0.length) (y, false) ξ
        have hlen0 := inv0.len_ge
        refine {
          len_ge := by simp [candidate, extendSeq]; omega
          wellFormed := extendSeq_wellFormed t r q0 inv0.wellFormed (y, false) ξ hal.2 hok.1
          state_prefix := fun s hs =>
            (extendSeq_state_of_le q0 b (y, false) ξ (hs.trans hlen0)).trans (inv0.state_prefix s hs)
          pivot_prefix := fun s hs =>
            (extendSeq_pivot_of_lt q0 b (y, false) ξ (lt_of_lt_of_le hs hlen0)).trans
              (inv0.pivot_prefix s hs)
          scalar_prefix := fun s hs =>
            (extendSeq_scalar_of_lt q0 b (y, false) ξ (lt_of_lt_of_le hs hlen0)).trans
              (inv0.scalar_prefix s hs)
          trial_step := fun s hs1 hs2 => by
            change s < q0.length + 1 at hs2
            rcases Nat.lt_succ_iff_lt_or_eq.mp hs2 with hlt | rfl
            · obtain ⟨l, hl, ha, hp, hsc⟩ := inv0.trial_step s hs1 hlt
              exact ⟨l, hl, ha,
                (extendSeq_pivot_of_lt q0 b (y, false) ξ hlt).trans hp,
                (extendSeq_scalar_of_lt q0 b (y, false) ξ hlt).trans hsc⟩
            · exact ⟨k, hk, hal.1,
                extendSeq_pivot_last_a3b q0 b (y, false) ξ,
                extendSeq_scalar_last_a3b q0 b (y, false) ξ⟩
          valid := fun s hs => by
            change s ≤ q0.length + 1 at hs
            by_cases heq : s = q0.length + 1
            · subst heq; exact hok.2.1
            · have hs0 : s ≤ q0.length := by omega
              exact extendSeq_valid_of_le q0 b (y, false) ξ t r (stageD0 P j x) hs0
                (inv0.valid s hs0)
        }
      · simp only [Option.some.injEq] at hstep
        subst hstep
        exact inv0
    · exact ih q hq

end SeqLemmas

/-! ## Section 3: Live-set monotonicity, distinct pivots, blocks, and Ward preservation -/

section WellFormedProps
variable {P_port : Type*} [Fintype P_port] [DecidableEq P_port]

theorem wellFormed_live_succ {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (hq : q.wellFormed t r) {s : ℕ} (hs : s < q.length) :
    (q.state (s + 1)).live ⊆ (q.state s).live := by
  have hwf := hq.2 s hs
  cases hp : q.pivot s with
  | none =>
    rw [hp] at hwf
    rw [hwf]
  | some x =>
    rw [hp] at hwf
    rw [hwf.survivors]
    exact Finset.erase_subset x _

theorem wellFormed_live_antitone {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (hq : q.wellFormed t r) {s1 s2 : ℕ} (h12 : s1 ≤ s2) (h2 : s2 ≤ q.length) :
    (q.state s2).live ⊆ (q.state s1).live := by
  induction s2 with
  | zero =>
    have : s1 = 0 := by omega
    subst this
    exact Finset.Subset.refl _
  | succ s2 ih =>
    by_cases heq : s1 = s2 + 1
    · subst heq; exact Finset.Subset.refl _
    · exact (wellFormed_live_succ hq (by omega)).trans (ih (by omega) (by omega))

theorem wellFormed_pivot_mem_live {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (hq : q.wellFormed t r) {s : ℕ} (hs : s < q.length) {x : P_port}
    (hp : q.pivot s = some x) :
    x ∈ (q.state s).live ∧ x ∉ (q.state (s + 1)).live := by
  have hwf := hq.2 s hs
  rw [hp] at hwf
  exact ⟨hwf.pivot_live, by rw [hwf.survivors]; exact Finset.notMem_erase x _⟩

theorem wellFormed_pivot_injective {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (hq : q.wellFormed t r) {s1 s2 : ℕ} (hs1 : s1 < q.length) (hs2 : s2 < q.length)
    {x : P_port} (hp1 : q.pivot s1 = some x) (hp2 : q.pivot s2 = some x) :
    s1 = s2 := by
  rcases lt_trichotomy s1 s2 with hlt | rfl | hgt
  · exfalso
    have h1 := (wellFormed_pivot_mem_live hq hs1 hp1).2
    have h2 := (wellFormed_pivot_mem_live hq hs2 hp2).1
    exact h1 (wellFormed_live_antitone hq (by omega : s1 + 1 ≤ s2) hs2.le h2)
  · rfl
  · exfalso
    have h1 := (wellFormed_pivot_mem_live hq hs2 hp2).2
    have h2 := (wellFormed_pivot_mem_live hq hs1 hp1).1
    exact h1 (wellFormed_live_antitone hq (by omega : s2 + 1 ≤ s1) hs1.le h2)

@[ext]
theorem state_ext {ι : Type*} {s1 s2 : S45.State ι} (hg : s1.g = s2.g) (hr : s1.r = s2.r) :
    s1 = s2 := by
  cases s1; cases s2; congr

/-- Equivalence between `b.live` and `S45.survivors ⟨x, hx⟩` when `b.live = a.live.erase x`. -/
def stepLiveEquiv {a b : S45.LiveState P_port} {x : P_port}
    (hx : x ∈ a.live) (hsurv : b.live = a.live.erase x) :
    b.live ≃ S45.survivors (⟨x, hx⟩ : a.live) where
  toFun i :=
    have hi : i.1 ∈ a.live.erase x := hsurv ▸ i.2
    ⟨⟨i.1, Finset.mem_of_mem_erase hi⟩,
      Finset.mem_erase.mpr ⟨fun h => (Finset.ne_of_mem_erase hi)
        (congrArg Subtype.val h), Finset.mem_univ _⟩⟩
  invFun j := ⟨j.1.1, by
    rw [hsurv]
    exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp j.2).1 (Subtype.ext h), j.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stepRel_state_eq_reindex {t : ℝ} {r : P_port → ℂ} {a b : S45.LiveState P_port}
    {x : P_port} {ξ : ℝ} (hrel : S45.StepRel t r a b x ξ) :
    b.state r = AgentS45.State.reindex (stepLiveEquiv hrel.pivot_live hrel.survivors)
      (S45.deleteState t (a.state r) ⟨x, hrel.pivot_live⟩ ξ) := by
  apply state_ext
  · ext i j
    have hg := congrFun (congrFun hrel.update i.1) j.1
    change b.g i.1 j.1 = _
    rw [hg]
    simp [AgentS45.State.reindex, stepLiveEquiv, S45.deleteState, S45.LiveState.state,
      S45.restrict, S45.mask, S45.pad, Matrix.submatrix_apply, i.2, j.2]
    rfl
  · ext i
    rfl

lemma ward_polar_identity (gij a zi zj : ℂ) :
    (gij.im : ℂ) - a * zi * (zj.im : ℂ) - star a * star zj * (zi.im : ℂ) +
      ((-a.im : ℝ) : ℂ) * zi * star zj = ((gij - a * zi * zj).im : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem deleteState_isSymm (t : ℝ) (s : S45.State P_port) (x : P_port) (ξ : ℝ)
    (hsym : s.g.IsSymm) : (S45.deleteState t s x ξ).g.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change s.g j.1 i.1 - ((ξ : ℂ) + t * s.r x) * s.g j.1 x * s.g x i.1 /
      (1 + ((ξ : ℂ) + t * s.r x) * s.g x x) =
    s.g i.1 j.1 - ((ξ : ℂ) + t * s.r x) * s.g i.1 x * s.g x j.1 /
      (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)
  rw [hsym.apply j.1 i.1, hsym.apply j.1 x, hsym.apply x i.1]
  ring

theorem deleteState_ward (t : ℝ) (s : S45.State P_port) (x : P_port) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hw : s.ward t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    (S45.deleteState t s x ξ).ward t := by
  classical
  let s' := S45.deleteState t s x ξ
  let c : ℂ := (ξ : ℂ) + t * s.r x
  let d : ℂ := 1 + c * s.g x x
  let a : ℂ := c / d
  have hsqrt_pos : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hdne : d ≠ 0 := hden
  have hcim : c.im = t * s.p x := by
    simp [c, S45.State.p, Complex.add_im, Complex.mul_im]
  have hscalar := AgentS45.scalar_ward_coeff t (s.p x) (s.q x) c d (s.g x x)
    hcim (by simp [S45.State.q]) rfl hdne
  have halphaNorm : Complex.normSq a = Complex.normSq c / Complex.normSq d := by
    simp [a]
  have hcoeffBase : Complex.normSq a * s.q x - t * s.p x / Complex.normSq d = -a.im := by
    rw [halphaNorm]; linarith [hscalar]
  have hfactor : 1 - a * s.g x x = d⁻¹ := by
    dsimp [a]; field_simp [hdne]; dsimp [d]; ring
  have hupdate : ∀ i j : S45.survivors x,
      s'.h t i j = s.h t i.1 j.1 - S45.gamma t s x ξ * s.h t i.1 x * s.h t x j.1 := by
    intro i j
    change (Real.sqrt t : ℂ) *
        (s.g i.1 j.1 - ((ξ : ℂ) + t * s.r x) * s.g i.1 x * s.g x j.1 /
          (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)) =
      (Real.sqrt t : ℂ) * s.g i.1 j.1 -
        (((ξ : ℂ) + t * s.r x) /
          ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + t * s.r x) * s.g x x))) *
          ((Real.sqrt t : ℂ) * s.g i.1 x) * ((Real.sqrt t : ℂ) * s.g x j.1)
    field_simp [hden, hsqrt_pos]
  ext i j
  change ((s'.h t * Matrix.diagonal (fun k => (s'.p k : ℂ))) * (s'.h t)ᴴ) i j =
    S45.matrixIm s'.g i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, S45.matrixIm]
  let zi : ℂ := s.g i.1 x
  let zj : ℂ := s.g j.1 x
  let bi : ℂ := a * zi
  let bj : ℂ := a * zj
  let Hi : P_port → ℂ := fun k => s.h t i.1 k - bi * s.h t x k
  let Hj : P_port → ℂ := fun k => s.h t j.1 k - bj * s.h t x k
  have hsymxj : s.g x j.1 = zj := hsym.apply j.1 x
  have hcoeff_i : S45.gamma t s x ξ * s.h t i.1 x = bi := by
    dsimp [S45.gamma, a, bi, c, d, zi, S45.State.h]
    field_simp [hden, hsqrt_pos]
  have hcoeff_j : S45.gamma t s x ξ * s.h t j.1 x = bj := by
    dsimp [S45.gamma, a, bj, c, d, zj, S45.State.h]
    field_simp [hden, hsqrt_pos]
  have hHi (k : S45.survivors x) : s'.h t i k = Hi k.1 := by
    dsimp [Hi]; rw [hupdate i k, hcoeff_i]
  have hHj (k : S45.survivors x) : s'.h t j k = Hj k.1 := by
    dsimp [Hj]; rw [hupdate j k, hcoeff_j]
  have hHx (z : ℂ) : (Real.sqrt t : ℂ) * z - (a * z) * ((Real.sqrt t : ℂ) * s.g x x) =
      (Real.sqrt t : ℂ) * z / d := by
    calc (Real.sqrt t : ℂ) * z - (a * z) * ((Real.sqrt t : ℂ) * s.g x x)
        = (Real.sqrt t : ℂ) * z * (1 - a * s.g x x) := by ring
      _ = (Real.sqrt t : ℂ) * z * d⁻¹ := by rw [hfactor]
      _ = (Real.sqrt t : ℂ) * z / d := by simp [div_eq_mul_inv]
  have hHix : Hi x = (Real.sqrt t : ℂ) * zi / d := hHx zi
  have hHjx : Hj x = (Real.sqrt t : ℂ) * zj / d := hHx zj
  have hsplit : (∑ k : S45.survivors x, s'.h t i k * (s'.p k : ℂ) * star (s'.h t j k)) =
      (∑ k : P_port, Hi k * (s.p k : ℂ) * star (Hj k)) - Hi x * (s.p x : ℂ) * star (Hj x) := by
    rw [show (∑ k : S45.survivors x, s'.h t i k * (s'.p k : ℂ) * star (s'.h t j k)) =
      ∑ k : S45.survivors x, Hi k.1 * (s.p k.1 : ℂ) * star (Hj k.1) from
      Finset.sum_congr rfl fun k _ => by rw [hHi k, hHj k]; rfl]
    exact AgentS45.sum_survivors_sub x (fun k => Hi k * (s.p k : ℂ) * star (Hj k))
  have hfull : (∑ k : P_port, Hi k * (s.p k : ℂ) * star (Hj k)) =
      (s.g i.1 j.1).im - bi * (s.g x j.1).im - star bj * (s.g i.1 x).im +
        bi * star bj * (s.q x : ℂ) := by
    have hterm (k : P_port) : Hi k * (s.p k : ℂ) * star (Hj k) =
        s.h t i.1 k * (s.p k : ℂ) * star (s.h t j.1 k) -
          bi * (s.h t x k * (s.p k : ℂ) * star (s.h t j.1 k)) -
          star bj * (s.h t i.1 k * (s.p k : ℂ) * star (s.h t x k)) +
          bi * star bj * (s.h t x k * (s.p k : ℂ) * star (s.h t x k)) := by
      simp only [Hi, Hj, star_sub, star_mul]; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      AgentS45.ward_entry_h t s hw i.1 j.1, AgentS45.ward_entry_h t s hw x j.1,
      AgentS45.ward_entry_h t s hw i.1 x, AgentS45.ward_entry_h t s hw x x]
    rfl
  have hdel : Hi x * (s.p x : ℂ) * star (Hj x) =
      ((t * s.p x / Complex.normSq d : ℝ) : ℂ) * zi * star zj := by
    rw [hHix, hHjx, star_div₀, star_mul, Complex.star_def, Complex.conj_ofReal]
    have hsqt : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt ht.le
    have hdd : d * (starRingEnd ℂ) d = (Complex.normSq d : ℂ) := Complex.mul_conj d
    calc ((Real.sqrt t : ℂ) * zi / d) * (s.p x : ℂ) * ((starRingEnd ℂ) zj * (Real.sqrt t : ℂ) / (starRingEnd ℂ) d)
        = ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) * (s.p x : ℂ) / (d * (starRingEnd ℂ) d) * zi * (starRingEnd ℂ) zj := by ring
      _ = (t : ℂ) * (s.p x : ℂ) / (Complex.normSq d : ℂ) * zi * star zj := by
          rw [hsqt, hdd, Complex.star_def]
      _ = ((t * s.p x / Complex.normSq d : ℝ) : ℂ) * zi * star zj := by push_cast; ring
  have hbibj : bi * star bj * (s.q x : ℂ) =
      ((Complex.normSq a * s.q x : ℝ) : ℂ) * zi * star zj := by
    dsimp [bi, bj]
    have haa : a * star a = (Complex.normSq a : ℂ) := by
      simpa [Complex.star_def] using Complex.mul_conj a
    calc (a * zi) * star (a * zj) * (s.q x : ℂ)
        = (a * star a) * (s.q x : ℂ) * zi * star zj := by rw [star_mul]; ring
      _ = ((Complex.normSq a * s.q x : ℝ) : ℂ) * zi * star zj := by
          rw [haa]; push_cast; ring
  have hgij : s'.g i j = s.g i.1 j.1 - a * zi * zj := by
    dsimp [s', S45.deleteState, a, c, d, zi, zj]
    rw [hsymxj]
    field_simp [hdne]
    ring
  rw [hsplit, hfull, hbibj, hdel, hsymxj, hgij]
  have hcomb : (s.g i.1 j.1).im - bi * (zj.im : ℂ) - star bj * (zi.im : ℂ) +
      ((Complex.normSq a * s.q x : ℝ) : ℂ) * zi * star zj -
      ((t * s.p x / Complex.normSq d : ℝ) : ℂ) * zi * star zj =
      (s.g i.1 j.1).im - a * zi * (zj.im : ℂ) - star a * star zj * (zi.im : ℂ) +
      ((-a.im : ℝ) : ℂ) * zi * star zj := by
    have hbj : star bj = star zj * star a := star_mul a zj
    rw [hbj, ← hcoeffBase]
    dsimp [bi]
    push_cast
    ring
  rw [hcomb]
  exact ward_polar_identity (s.g i.1 j.1) a zi zj

theorem reindex_isSymm {ι κ : Type*} (e : κ ≃ ι) (s : S45.State ι) (hs : s.g.IsSymm) :
    (AgentS45.State.reindex e s).g.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hs.apply (e i) (e j)

theorem reindex_ward {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : S45.State ι) (t : ℝ) (hw : s.ward t) :
    (AgentS45.State.reindex e s).ward t := by
  ext i j
  have h := congrFun (congrFun hw (e i)) (e j)
  change (((AgentS45.State.reindex e s).h t *
      Matrix.diagonal (fun k => ((AgentS45.State.reindex e s).p k : ℂ))) *
    ((AgentS45.State.reindex e s).h t)ᴴ) i j = _
  change ((s.h t * Matrix.diagonal (fun k => (s.p k : ℂ))) * (s.h t)ᴴ) (e i) (e j) = _ at h
  rw [Matrix.mul_apply] at h ⊢
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    S45.matrixIm, AgentS45.State.reindex, S45.State.h, S45.State.p, Matrix.smul_apply] at h ⊢
  rw [← h]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem wellFormed_symm_ward {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (ht : 0 < t) (hq : q.wellFormed t r)
    (hsym0 : ((q.state 0).state r).g.IsSymm) (hward0 : ((q.state 0).state r).ward t) :
    ∀ s ≤ q.length, ((q.state s).state r).g.IsSymm ∧ ((q.state s).state r).ward t := by
  intro s
  induction s with
  | zero => intro _; exact ⟨hsym0, hward0⟩
  | succ s ih =>
    intro hs1
    have hs : s < q.length := hs1
    obtain ⟨hsym, hward⟩ := ih hs.le
    have hwf := hq.2 s hs
    cases hp : q.pivot s with
    | none =>
      rw [hp] at hwf
      rw [hwf]
      exact ⟨hsym, hward⟩
    | some x =>
      rw [hp] at hwf
      have hrel : S45.StepRel t r (q.state s) (q.state (s + 1)) x (q.scalar s) := hwf
      have hden : 1 + ((q.scalar s : ℂ) + t * ((q.state s).state r).r ⟨x, hrel.pivot_live⟩) *
          ((q.state s).state r).g ⟨x, hrel.pivot_live⟩ ⟨x, hrel.pivot_live⟩ ≠ 0 :=
        hrel.denominator
      rw [stepRel_state_eq_reindex hrel]
      exact ⟨reindex_isSymm _ _ (deleteState_isSymm t _ _ _ hsym),
        reindex_ward _ _ t (deleteState_ward t _ _ _ ht hsym hward hden)⟩

/-- Entries of `D` (05:327): `D = diag(p q) − diag(p) F diag(p)`. -/
theorem state_D_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (s : S45.State ι) (t : ℝ)
    (i j : ι) :
    s.D t i j = (if i = j then s.p i * s.q i else 0) - s.p i * s.F t i j * s.p j := by
  simp only [S45.State.D, Matrix.sub_apply, S45.diagonal_sandwich_apply, Matrix.diagonal_apply]

/-- A quadratic form only sees the support of its matrix. -/
theorem qform_congr_of_support {ι : Type*} [Fintype ι] (M : S45.RMat ι) (L0 : Finset ι)
    (hM : ∀ i j, i ∉ L0 ∨ j ∉ L0 → M i j = 0) (f g : ι → ℝ)
    (hfg : ∀ x ∈ L0, f x = g x) : S45.qform M f = S45.qform M g := by
  simp only [S45.qform, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hi : i ∈ L0
  · by_cases hk : k ∈ L0
    · rw [hfg i hi, hfg k hk]
    · rw [hM i k (Or.inr hk)]; ring
  · rw [hM i k (Or.inl hi)]; ring

/-- `L` records of a well-formed sequence vanish off the start live set. -/
theorem Lrecord_supported {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (hq : q.wellFormed t r) (K : Finset ℕ) (hK : K ⊆ Finset.range q.length) (i j : P_port)
    (hij : i ∉ (q.state 0).live ∨ j ∉ (q.state 0).live) : q.Lrecord t r K i j = 0 := by
  simp only [S45.Sequence.Lrecord, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k < q.length := Finset.mem_range.mp (hK hk)
  have hsub : (q.state (k + 1)).live ⊆ (q.state 0).live :=
    wellFormed_live_antitone hq (Nat.zero_le _) hk'
  have hij' : i ∉ (q.state (k + 1)).live ∨ j ∉ (q.state (k + 1)).live := by
    rcases hij with hi | hj
    · exact Or.inl fun h => hi (hsub h)
    · exact Or.inr fun h => hj (hsub h)
  unfold S45.Sequence.stepL
  rcases q.pivot k with _ | x
  · rfl
  · rcases hij' with hi | hj
    · simp [S45.mask, S45.pad, hi]
    · simp [S45.mask, S45.pad, hj]

lemma submatrix_isUnit_and_inv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (M : Matrix β β ℂ) (hM : IsUnit M) :
    IsUnit (M.submatrix e e) ∧ (M.submatrix e e)⁻¹ = M⁻¹.submatrix e e := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hmul1 : (M.submatrix e e) * (M⁻¹.submatrix e e) = 1 := by
    rw [Matrix.submatrix_mul_equiv M M⁻¹ e e e, Matrix.mul_nonsing_inv M hdet,
      Matrix.submatrix_one_equiv]
  have hmul2 : (M⁻¹.submatrix e e) * (M.submatrix e e) = 1 := by
    rw [Matrix.submatrix_mul_equiv M⁻¹ M e e e, Matrix.nonsing_inv_mul M hdet,
      Matrix.submatrix_one_equiv]
  have hu : IsUnit (M.submatrix e e) :=
    ⟨⟨M.submatrix e e, M⁻¹.submatrix e e, hmul1, hmul2⟩, rfl⟩
  have hdetA : IsUnit (M.submatrix e e).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  refine ⟨hu, ?_⟩
  calc (M.submatrix e e)⁻¹
      = (M.submatrix e e)⁻¹ * ((M.submatrix e e) * (M⁻¹.submatrix e e)) := by rw [hmul1, mul_one]
    _ = ((M.submatrix e e)⁻¹ * (M.submatrix e e)) * (M⁻¹.submatrix e e) := by rw [Matrix.mul_assoc]
    _ = M⁻¹.submatrix e e := by rw [Matrix.nonsing_inv_mul _ hdetA, one_mul]

lemma reindex_one_sub_K {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : S45.State ι) (t : ℝ) :
    1 - (AgentS45.State.reindex e s).K t = (1 - s.K t).submatrix e e := by
  ext i j
  simp [AgentS45.State.reindex_K, Matrix.sub_apply, Matrix.one_apply]

lemma reindex_P {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : S45.State ι) (t : ℝ) (hunit : IsUnit (1 - s.K t)) :
    IsUnit (1 - (AgentS45.State.reindex e s).K t) ∧
      (AgentS45.State.reindex e s).P t = (s.P t).submatrix e e := by
  have hsub := submatrix_isUnit_and_inv e (1 - s.K t) hunit
  rw [← reindex_one_sub_K e s t] at hsub
  exact hsub

lemma reindex_lag {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : S45.State ι) (t : ℝ) (hunit : IsUnit (1 - s.K t)) (i : κ) :
    (AgentS45.State.reindex e s).lag t i = s.lag t (e i) := by
  obtain ⟨_, hP⟩ := reindex_P e s t hunit
  change ((AgentS45.State.reindex e s).P t *ᵥ (AgentS45.State.reindex e s).rawLag) i =
    (s.P t *ᵥ s.rawLag) (e i)
  rw [hP]
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, S45.State.rawLag,
    AgentS45.State.reindex]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem ambient_D_live (a : S45.LiveState P_port) (r : P_port → ℂ) (t : ℝ) {i j : P_port}
    (hi : i ∈ a.live) (hj : j ∈ a.live) :
    (a.ambient r).D t i j = (a.state r).D t ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [state_D_apply, state_D_apply]
  have hF : (a.ambient r).F t i j = (a.state r).F t ⟨i, hi⟩ ⟨j, hj⟩ := by
    simp only [S45.State.F, S45.entryAbsSquare, AgentS45.ambient_h_live a r t hi hj]
  have hq : (a.ambient r).q i = (a.state r).q ⟨i, hi⟩ := by
    simp only [S45.State.q, S45.LiveState.ambient, S45.LiveState.state, S45.mask,
      AgentS45.pad_apply_mem a.live _ hi hi]
  rw [hF, hq]
  by_cases h : i = j
  · subst h; simp; rfl
  · simp [h]; rfl

theorem ambient_D_dead (a : S45.LiveState P_port) (r : P_port → ℂ) (t : ℝ) {i j : P_port}
    (h : i ∉ a.live ∨ j ∉ a.live) : (a.ambient r).D t i j = 0 := by
  rw [state_D_apply]
  have hF : (a.ambient r).F t i j = 0 := by
    rcases h with hi | hj
    · simp [S45.State.F, S45.entryAbsSquare, S45.State.h, S45.LiveState.ambient, S45.mask,
        S45.pad, hi]
    · simp [S45.State.F, S45.entryAbsSquare, AgentS45.ambient_h_dead a r t i hj]
  rw [hF]
  by_cases hij : i = j
  · subst hij
    have hi : i ∉ a.live := by rcases h with h | h <;> exact h
    simp [S45.State.q, S45.LiveState.ambient, S45.mask, S45.pad, hi]
  · simp [hij]

theorem reindex_D {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : S45.State ι) (t : ℝ) (a b : κ) :
    (AgentS45.State.reindex e s).D t a b = s.D t (e a) (e b) := by
  rw [state_D_apply, state_D_apply]
  by_cases hab : a = b
  · subst hab; simp; rfl
  · have hne : e a ≠ e b := e.injective.ne hab
    simp only [hab, hne, if_false]
    rfl

/-- A form supported on `L` is the reindexed form on any type equivalent to `L`. -/
theorem qform_of_support_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (L : Finset ι)
    (e : L ≃ κ) (M : S45.RMat ι) (N : S45.RMat κ)
    (hM : ∀ i j (hi : i ∈ L) (hj : j ∈ L), M i j = N (e ⟨i, hi⟩) (e ⟨j, hj⟩))
    (hM0 : ∀ i j, i ∉ L ∨ j ∉ L → M i j = 0) (f : ι → ℝ) :
    S45.qform M f = S45.qform N (fun a => f (e.symm a).1) := by
  have hsum : ∀ g : ι → ℝ, (∀ i, i ∉ L → g i = 0) → ∑ i, g i = ∑ a : κ, g (e.symm a).1 := by
    intro g hg
    rw [← Finset.sum_subset (Finset.subset_univ L) (fun i _ hi => hg i hi),
      ← Finset.sum_coe_sort L g]
    exact (Equiv.sum_comp e.symm (fun i : L => g i.1)).symm
  simp only [S45.qform, Matrix.mulVec, dotProduct]
  rw [hsum (fun i => f i * ∑ j, M i j * f j) (fun i hi => by
    simp [fun k => hM0 i k (Or.inl hi)])]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [hsum (fun j => M (e.symm a).1 j * f j) (fun j hj => by
    simp [fun k => hM0 k j (Or.inr hj)])]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hM _ _ (e.symm a).2 (e.symm b).2]
  simp

end WellFormedProps

/-! ## Section 3b: the v3.1 stage start on the active-site ports

Under TileGoodCore v3.1 the sweep starts on the ports of the active sites (`start_live`) and
the start clauses are stated on `stageStartV3`. The live start state is `stageStartV3`
reindexed along `activeLiveEquiv` (05:320–333, 04:67–80). -/

section StartV3
variable {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
  (x : RunRecord d m)

/-- A finset of torus ports whose members are the ports of the active sites is equivalent to
the active-site port space. -/
def activeLiveEquiv (L : Finset (Port d m))
    (hL : ∀ p : Port d m, p ∈ L ↔ p.1 ∈ x.endpoint.active) :
    L ≃ S45.initialPorts {i // i ∈ x.endpoint.active} where
  toFun p := (⟨p.1.1, (hL p.1).1 p.2⟩, p.1.2)
  invFun a := ⟨(a.1.1, a.2), (hL (a.1.1, a.2)).2 a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mem_sweepStartLiveState (θ : ℝ) (p : Port d m) :
    p ∈ (sweepStartLiveState θ x).live ↔ p.1 ∈ x.endpoint.active := by
  simp [sweepStartLiveState]

theorem start_live_mem (hx : TileGoodCore C P j T x) (p : Port d m) :
    p ∈ (x.sweep.state 0).live ↔ p.1 ∈ x.endpoint.active := by
  rw [hx.start_live]; exact mem_sweepStartLiveState x _ p

/-- The start live set as the active-site ports. -/
abbrev startEquiv (hx : TileGoodCore C P j T x) :
    (x.sweep.state 0).live ≃ S45.initialPorts {i // i ∈ x.endpoint.active} :=
  activeLiveEquiv x (x.sweep.state 0).live (start_live_mem P j T x hx)

/-- **The v3.1 start identification.** The live start state of the sweep is `stageStartV3`
reindexed to the start live set. -/
theorem start_state_eq_reindex (hx : TileGoodCore C P j T x) :
    (x.sweep.state 0).state (portR (sweepTheta P.u m j) x.r) =
      AgentS45.State.reindex (startEquiv P j T x hx) (stageStartV3 P j x) := by
  have hg : (x.sweep.state 0).g = (sweepStartLiveState (sweepTheta P.u m j) x).g := by
    rw [hx.start_live]
  apply state_ext
  · ext a b
    change (x.sweep.state 0).g a.1 b.1 = _
    rw [hg]
    rfl
  · ext a
    rfl

/-- The broad bounds of the frozen damping at every start-live port. -/
theorem start_broad (hx : TileGoodCore C P j T x) {p : Port d m}
    (hp : p ∈ (x.sweep.state 0).live) :
    ‖portR (sweepTheta P.u m j) x.r p‖ ≤ C ∧
      1 / C ≤ (portR (sweepTheta P.u m j) x.r p).im ∧
      (portR (sweepTheta P.u m j) x.r p).im ≤ C := by
  obtain ⟨Λplus, Wstar, hpre, _⟩ := hx.start_prestate
  exact hpre.broad (startEquiv P j T x hx ⟨p, hp⟩)

/-- Live ports of a well-formed sequence from the sweep start are start-live. -/
theorem live_mem_start {q : S45.Sequence (Port d m)} {t : ℝ} {r : Port d m → ℂ}
    (hq : q.wellFormed t r) (hq0 : q.state 0 = x.sweep.state 0) {s : ℕ} (hs : s ≤ q.length)
    {p : Port d m} (hp : p ∈ (q.state s).live) : p ∈ (x.sweep.state 0).live := by
  rw [← hq0]; exact wellFormed_live_antitone hq (Nat.zero_le s) hs hp

end StartV3

/-! ## Section 4: Cumulative Schur induction and `stepDen ≠ 0` at valid prefixes -/

section PrefixBounds
variable {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
  (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)

theorem seq_truncate_wellFormed {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (hq : q.wellFormed t r) {s : ℕ} (hs : s ≤ q.length) :
    ({ q with length := s } : S45.Sequence P_port).wellFormed t r :=
  ⟨fun k hk => hq.1 k (hk.trans hs), fun k hk => hq.2 k (lt_of_lt_of_le hk hs)⟩

/-- Equivalence between `L` and `(Lᶜᶜ : Finset P)`. -/
def complComplEquiv {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (L : Finset P_port) : L ≃ (↑(Lᶜᶜ) : Type _) where
  toFun i := ⟨i.1, Finset.mem_compl.mpr (fun h => (Finset.mem_compl.mp h) i.2)⟩
  invFun j := ⟨j.1, by
    by_contra h
    exact (Finset.mem_compl.mp j.2) (Finset.mem_compl.mpr h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem K_submatrix_of_pad_schur {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (L : Finset P_port) (K : Matrix L L ℂ) (A : S45.CMat P_port)
    (hpad : S45.pad L (1 - K) = S45.pad Lᶜᶜ (S45.schur A Lᶜ)) :
    K = (1 - S45.schur A Lᶜ).submatrix (complComplEquiv L) (complComplEquiv L) := by
  ext i j
  have h1 := congrFun (congrFun hpad i.1) j.1
  have hicc : i.1 ∈ Lᶜᶜ := (complComplEquiv L i).2
  have hjcc : j.1 ∈ Lᶜᶜ := (complComplEquiv L j).2
  rw [AgentS45.pad_apply_mem L (1 - K) i.2 j.2,
    AgentS45.pad_apply_mem Lᶜᶜ (S45.schur A Lᶜ) hicc hjcc] at h1
  simp only [Matrix.sub_apply, Matrix.one_apply, submatrix_apply, complComplEquiv,
    Equiv.coe_fn_mk, Subtype.mk.injEq] at h1 ⊢
  linear_combination -h1

theorem norm_K_le_of_pad_schur {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (L : Finset P_port) (K : Matrix L L ℂ) (B : S45.CMat P_port) (ρ : ℝ)
    (hρ : 0 ≤ ρ ∧ ρ < 1) (hB : ‖B‖ ≤ ρ)
    (hpad : S45.pad L (1 - K) = S45.pad Lᶜᶜ (S45.schur (1 - B) Lᶜ)) :
    ‖K‖ ≤ ρ := by
  have hcon := (AgentS45.schur_contraction_proof B Lᶜ ρ hρ hB).2
  have hsub := K_submatrix_of_pad_schur L K (1 - B) hpad
  rw [hsub, AgentS45.norm_submatrix_equiv]
  exact hcon

theorem start_state_isSymm_ward {q : S45.Sequence (Port d m)}
    (hq0 : q.state 0 = x.sweep.state 0) (hx : TileGoodCore C P j T x) :
    (((q.state 0).state (portR (sweepTheta P.u m j) x.r)).g).IsSymm ∧
    ((q.state 0).state (portR (sweepTheta P.u m j) x.r)).ward (sweepScale P.u m j) := by
  obtain ⟨Λplus, Wstar, hpre, _⟩ := hx.start_prestate
  rw [hq0, start_state_eq_reindex P j T x hx]
  exact ⟨reindex_isSymm _ _ hpre.symmetric, reindex_ward _ _ _ hpre.ward⟩

theorem F_diag_le_sqrt_of_row_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (s : S45.State ι) (i : ι)
    (hrow : s.fourthRow t Finset.univ i ≤ S45.rowCap t) :
    s.F t i i ≤ Real.sqrt t := by
  have hfour : ‖s.h t i i‖ ^ 4 ≤ S45.rowCap t :=
    (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 4)
      (Finset.mem_univ i)).trans hrow
  have hcap : S45.rowCap t ≤ t := by
    calc S45.rowCap t = S45.power t (1 + S45.delta) := rfl
      _ ≤ S45.power t 1 :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num [S45.delta])
      _ = t := Real.rpow_one t
  have hsq : (s.F t i i) ^ 2 ≤ (Real.sqrt t) ^ 2 := by
    rw [Real.sq_sqrt ht.le]
    have hF : (s.F t i i) ^ 2 = ‖s.h t i i‖ ^ 4 := by
      simp only [S45.State.F, S45.entryAbsSquare]
      ring
    rw [hF]
    exact hfour.trans hcap
  have hF0 : 0 ≤ s.F t i i := by simp [S45.State.F, S45.entryAbsSquare]
  exact (sq_le_sq₀ hF0 (Real.sqrt_nonneg t)).mp hsq

/-- Small-scale threshold for cumulative Schur and `stepDen ≠ 0`. -/
theorem exists_schur_den_scale (C : ℝ) (hC : 1 ≤ C) :
    ∃ t0 > 0, t0 ≤ 1 ∧ ∀ t, 0 < t → t < t0 →
      S45.power t (S45.delta / 10) ≤ 1 / 4 ∧
      S45.power t S45.beta / (1 / C) ≤ 1 / 2 ∧
      2 * (1 + C ^ 2) * S45.power t S45.beta ≤ 1 / (2 * C) ∧
      C * Real.sqrt t < 1 / (2 * C) ∧
      Real.sqrt t < (4 * (3 * C) ^ 2)⁻¹ := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨t1, ht1, h1⟩ := AgentS45.power_small (e := S45.delta / 10)
    (by norm_num [S45.delta]) (a := 1 / 4) (by norm_num)
  obtain ⟨t2, ht2, h2⟩ := AgentS45.power_small (e := S45.beta)
    (by norm_num [S45.beta, S45.delta]) (a := 1 / (4 * C * (1 + C ^ 2))) (by positivity)
  obtain ⟨t3, ht3, h3⟩ := AgentS45.power_small (e := 1 / 2)
    (by norm_num) (a := 1 / (36 * C ^ 2)) (by positivity)
  let t0 := min 1 (min t1 (min t2 t3))
  have ht0pos : 0 < t0 := lt_min one_pos (lt_min ht1 (lt_min ht2 ht3))
  have ht0le : t0 ≤ 1 := min_le_left _ _
  refine ⟨t0, ht0pos, ht0le, fun t ht htt => ?_⟩
  have htt1 : t < t1 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt2 : t < t2 := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htt3 : t < t3 := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hp1 : S45.power t (S45.delta / 10) ≤ 1 / 4 := (h1 t ht htt1).le
  have hp2 := h2 t ht htt2
  have hp3 := h3 t ht htt3
  have hsqrt : Real.sqrt t = S45.power t (1 / 2) := Real.sqrt_eq_rpow t
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  refine ⟨hp1, ?_, ?_, ?_, ?_⟩
  · rw [div_div_eq_mul_div, div_one]
    have hle : C * S45.power t S45.beta ≤ C * (1 / (4 * C * (1 + C ^ 2))) :=
      mul_le_mul_of_nonneg_left hp2.le hCpos.le
    have heq : C * (1 / (4 * C * (1 + C ^ 2))) = 1 / (4 * (1 + C ^ 2)) := by
      field_simp
    have h4 : 1 / (4 * (1 + C ^ 2)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · have hle : 2 * (1 + C ^ 2) * S45.power t S45.beta ≤
        2 * (1 + C ^ 2) * (1 / (4 * C * (1 + C ^ 2))) :=
      mul_le_mul_of_nonneg_left hp2.le (by positivity)
    have heq : 2 * (1 + C ^ 2) * (1 / (4 * C * (1 + C ^ 2))) = 1 / (2 * C) := by
      field_simp; ring
    linarith
  · rw [hsqrt]
    have hlt : C * S45.power t (1 / 2) < C * (1 / (36 * C ^ 2)) :=
      mul_lt_mul_of_pos_left hp3 hCpos
    have heq : C * (1 / (36 * C ^ 2)) = 1 / (36 * C) := by field_simp
    have h36 : 1 / (36 * C) ≤ 1 / (2 * C) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
    linarith
  · rw [hsqrt]
    have heq : (4 * (3 * C) ^ 2)⁻¹ = 1 / (36 * C ^ 2) := by ring
    rw [heq]
    exact hp3

/-- Along any well-formed prefix `q` starting from `x.sweep.state 0` with valid prefixes,
every step state `s_k = (q.state k).state r` has `‖s_k.K t‖ ≤ 3 / 4`,
`‖s_k.rawLag p‖ ≤ 2 * (1 + C ^ 2) * t^β`, `1 - s_k.K t p p ≠ 0`, and
`0 < s_k.q p - s_k.p p * s_k.F t p p`, and the cumulative Schur identity holds at `s`. -/
theorem prefix_schur_and_bounds (hx : TileGoodCore C P j T x)
    {q : S45.Sequence (Port d m)}
    (hq_wf : q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r))
    (hq0 : q.state 0 = x.sweep.state 0)
    (hq_val : ∀ s ≤ q.length,
      q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (stageD0 P j x) s)
    {t0 : ℝ} (ht0le : t0 ≤ 1)
    (hsmall : ∀ t, 0 < t → t < t0 →
      S45.power t (S45.delta / 10) ≤ 1 / 4 ∧
      S45.power t S45.beta / (1 / C) ≤ 1 / 2 ∧
      2 * (1 + C ^ 2) * S45.power t S45.beta ≤ 1 / (2 * C) ∧
      C * Real.sqrt t < 1 / (2 * C) ∧
      Real.sqrt t < (4 * (3 * C) ^ 2)⁻¹)
    (htpos : 0 < sweepScale P.u m j) (htlt : sweepScale P.u m j < t0) :
    ∀ s ≤ q.length,
      let t := sweepScale P.u m j
      let r := portR (sweepTheta P.u m j) x.r
      let sk := (q.state s).state r
      ‖sk.K t‖ ≤ 3 / 4 ∧
      (∀ p : (q.state s).live,
        ‖sk.rawLag p‖ ≤ 2 * (1 + C ^ 2) * S45.power t S45.beta ∧
        1 - sk.K t p p ≠ 0 ∧
        0 < sk.q p - sk.p p * sk.F t p p) := by
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  have hC1 : 1 ≤ C := hx.one_le
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have ht1 : t ≤ 1 := htlt.le.trans ht0le
  obtain ⟨hp1, hp2, hp3, hp4, _⟩ := hsmall t htpos htlt
  obtain ⟨Λplus, Wstar, hpre0, _⟩ := hx.start_prestate
  have hsw0 := start_state_isSymm_ward P j T x hq0 hx
  have hsw := wellFormed_symm_ward htpos hq_wf hsw0.1 hsw0.2
  have hstartK : ‖((q.state 0).state r).K t‖ ≤ 1 / 2 := by
    rw [hq0, start_state_eq_reindex P j T x hx, AgentS45.State.reindex_K,
      AgentS45.norm_submatrix_equiv]
    exact hpre0.K_cap
  have hbroad : ∀ p ∈ (q.state 0).live, ‖r p‖ ≤ C ∧ 1 / C ≤ (r p).im ∧ (r p).im ≤ C :=
    fun p hp => start_broad P j T x hx (by rw [← hq0]; exact hp)
  set S := (q.state 0).live with hSdef
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs
    let qs : S45.Sequence (Port d m) := { q with length := s }
    have hqs_wf : qs.wellFormed t r := seq_truncate_wellFormed hq_wf hs
    have hstep : ∀ k < qs.length,
        ((qs.state k).state r).g.IsSymm ∧ ((qs.state k).state r).ward t ∧
        ∀ p : (qs.state k).live, 1 - ((qs.state k).state r).K t p p ≠ 0 ∧
          0 < ((qs.state k).state r).q p -
            ((qs.state k).state r).p p * ((qs.state k).state r).F t p p := by
      intro k hk
      change k < s at hk
      have hk_le : k ≤ q.length := hk.le.trans hs
      obtain ⟨_, hpiv⟩ := ih k hk hk_le
      exact ⟨(hsw k hk_le).1, (hsw k hk_le).2, fun p => ⟨(hpiv p).2.1, (hpiv p).2.2⟩⟩
    -- restrict the prefix to the start live set `S` (luna-s78live `restrictLive`)
    have hsub : ∀ k ≤ s, (q.state k).live ⊆ S := fun k hk =>
      wellFormed_live_antitone hq_wf (Nat.zero_le k) (hk.trans hs)
    have hpivS : ∀ k < qs.length, ∀ p, qs.pivot k = some p → p ∈ S := by
      intro k hk p hp
      change k < s at hk
      exact hsub k hk.le (wellFormed_pivot_mem_live hq_wf (lt_of_lt_of_le hk hs) hp).1
    let r' : {p // p ∈ S} → ℂ := S45.restrictDamping S r
    let q' := qs.restrictLive S
    have hq'wf : q'.wellFormed t r' := S45.Sequence.wellFormed_restrictLive qs S hqs_wf hpivS
    have hq's : (q'.state 0).live = Finset.univ := S45.Sequence.restrictLive_start qs S rfl
    have hp' : ∀ i : {p // p ∈ S}, 0 < (r' i).im := fun i =>
      lt_of_lt_of_le (by positivity) (hbroad i.1 i.2).2.1
    have hstep' : ∀ k < q'.length, ((q'.state k).state r').g.IsSymm ∧
        ((q'.state k).state r').ward t ∧
        ∀ y : (q'.state k).live, 1 - ((q'.state k).state r').K t y y ≠ 0 ∧
          0 < ((q'.state k).state r').q y -
            ((q'.state k).state r').p y * ((q'.state k).state r').F t y y := by
      intro k hk
      obtain ⟨hsymm, hward, hK⟩ := hstep k hk
      have hsk : (qs.state k).live ⊆ S := hsub k (le_of_lt hk)
      exact ⟨S45.LiveState.restrictLive_state_symm S (qs.state k) r hsymm,
        S45.LiveState.restrictLive_state_ward S (qs.state k) r t hsk hward,
        S45.Sequence.hstep_restrictLive qs S t r k hsk hK⟩
    obtain ⟨hpadK, -⟩ := AgentS45.cumulative_schur_proof q' t r' htpos hp' hq'wf hq's hstep'
    replace hpadK : S45.pad (q'.state s).live (1 - ((q'.state s).state r').K t) =
      S45.pad (q'.state s).liveᶜᶜ (S45.schur (1 - ((q'.state 0).ambient r').K t -
        q'.Jrecord t r' (Finset.range s)) (q'.state s).liveᶜ) := hpadK
    have hamb0 : ((q'.state 0).ambient r').K t = ((q.state 0).state r).K t := by
      have hg : ((q'.state 0).ambient r').g = ((q.state 0).state r).g := by
        ext a b
        have ha : a ∈ (q'.state 0).live := hq's ▸ Finset.mem_univ a
        have hb : b ∈ (q'.state 0).live := hq's ▸ Finset.mem_univ b
        change S45.mask (q'.state 0).live (q'.state 0).g a b = _
        simp only [S45.mask, S45.pad, ha, hb, ↓reduceDIte]
        rfl
      simp only [S45.State.K, S45.State.h, hg]
    have hJ' : ‖q'.Jrecord t r' (Finset.range s)‖ = ‖q.Jrecord t r (Finset.range s)‖ := by
      show ‖(qs.restrictLive S).Jrecord t (S45.restrictDamping S r) (Finset.range s)‖ = _
      rw [← S45.Sequence.Jrecord_restrictLive qs S t r hpivS (Finset.range s) subset_rfl]
      refine norm_submatrix_of_support (fun a : {p // p ∈ S} => a.1) Subtype.val_injective _ ?_
      intro i j hij
      refine S45.Sequence.Jrecord_supported qs S t r hqs_wf rfl (Finset.range s) subset_rfl i j ?_
      rcases hij with hi | hj
      · exact Or.inl fun h => hi ⟨i, h⟩ rfl
      · exact Or.inr fun h => hj ⟨j, h⟩ rfl
    have hvs := hq_val s hs
    let B := ((q.state 0).state r).K t + q'.Jrecord t r' (Finset.range s)
    have hB : ‖B‖ ≤ 3 / 4 := by
      calc ‖B‖ ≤ ‖((q.state 0).state r).K t‖ + ‖q'.Jrecord t r' (Finset.range s)‖ :=
            norm_add_le _ _
        _ ≤ 1 / 2 + S45.power t (S45.delta / 10) := by
            rw [hJ']; exact add_le_add hstartK hvs.1
        _ ≤ 3 / 4 := by linarith
    have hpadK' : S45.pad (q'.state s).live (1 - ((q'.state s).state r').K t) =
        S45.pad (q'.state s).liveᶜᶜ (S45.schur (1 - B) (q'.state s).liveᶜ) := by
      rw [hpadK, hamb0, show 1 - ((q.state 0).state r).K t - q'.Jrecord t r' (Finset.range s) =
        1 - B by simp [B]; abel]
    have hKnorm' : ‖((q'.state s).state r').K t‖ ≤ 3 / 4 :=
      norm_K_le_of_pad_schur (q'.state s).live _ B (3 / 4) ⟨by norm_num, by norm_num⟩
        hB hpadK'
    have hsubs : (q.state s).live ⊆ S := hsub s le_rfl
    have hKmat : ((q'.state s).state r').K t = (((q.state s).state r).K t).submatrix
        (S45.LiveState.subLiveEquiv S (q.state s) hsubs)
        (S45.LiveState.subLiveEquiv S (q.state s) hsubs) := by
      ext a b; rfl
    have hKnorm0 : ‖((q.state s).state r).K t‖ ≤ 3 / 4 := by
      have h := AgentS45.norm_submatrix_equiv (S45.LiveState.subLiveEquiv S (q.state s) hsubs)
        (((q.state s).state r).K t)
      rw [hKmat] at hKnorm'
      calc ‖((q.state s).state r).K t‖ = _ := h.symm
        _ ≤ 3 / 4 := by
          convert hKnorm' using 2
          first
            | (congr 1; exact Subsingleton.elim _ _)
            | (congr; exact Subsingleton.elim _ _)
            | congr
    let sk := (q.state s).state r
    have hKnorm : ‖sk.K t‖ ≤ 3 / 4 := hKnorm0
    have hunit : IsUnit (1 - sk.K t) :=
      (Units.oneSub (sk.K t) (by linarith : ‖sk.K t‖ < 1)).isUnit
    have hsk_p : ∀ p : (q.state s).live, 1 / C ≤ sk.p p := fun p => (hbroad p.1 (hsubs p.2)).2.1
    have hsk_r : ∀ p : (q.state s).live, ‖sk.r p‖ ≤ C := fun p => (hbroad p.1 (hsubs p.2)).1
    have hβ0 : 0 ≤ S45.power t S45.beta := (Real.rpow_pos_of_pos htpos _).le
    have hdiag := AgentS45.diag_from_lag sk t (S45.power t S45.beta) (1 / C) C
      (hsw s hs).2 hunit hvs.2.2.2 (by positivity) hsk_p hsk_r hβ0 hp2
    refine ⟨hKnorm, fun p => ?_⟩
    have hraw : ‖sk.rawLag p‖ ≤ 2 * (1 + C ^ 2) * S45.power t S45.beta := by
      have hd := hdiag p
      have heq : 2 * S45.power t S45.beta * (1 + C / (1 / C)) =
          2 * (1 + C ^ 2) * S45.power t S45.beta := by field_simp
      linarith
    have hKpp : 1 - sk.K t p p ≠ 0 := by
      intro h0
      have h1 : sk.K t p p = 1 := by linear_combination -h0
      have h2 : ‖sk.K t p p‖ ≤ 3 / 4 := (entry_le_l2 (sk.K t) p p).trans hKnorm
      rw [h1, norm_one] at h2
      linarith
    have hqp : |sk.q p - sk.p p| ≤ 2 * (1 + C ^ 2) * S45.power t S45.beta := by
      have him : sk.q p - sk.p p = (sk.rawLag p).im := by
        simp [S45.State.q, S45.State.p, S45.State.rawLag]
      rw [him]
      exact (Complex.abs_im_le_norm _).trans hraw
    have hq_lo : 1 / (2 * C) ≤ sk.q p := by
      have hp_lo : 1 / C ≤ sk.p p := hsk_p p
      have hqp_lo := (abs_le.mp hqp).1
      have hdiv2 : 1 / C - 1 / (2 * C) = 1 / (2 * C) := by ring
      linarith
    have hFpp : sk.F t p p ≤ Real.sqrt t :=
      F_diag_le_sqrt_of_row_cap htpos ht1 sk p (hvs.2.2.1 p)
    have hpF : sk.p p * sk.F t p p ≤ C * Real.sqrt t :=
      mul_le_mul (hbroad p.1 (hsubs p.2)).2.2 hFpp (by simp [S45.State.F, S45.entryAbsSquare])
        hCpos.le
    refine ⟨hraw, hKpp, by linarith⟩

/-- At any valid prefix `q` reached by `slotSeq`, the candidate update denominator is nonzero. -/
theorem stepDen_ne_zero_of_slotSeq (hx : TileGoodCore C P j T x)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    {k : ℕ} {ω : RandomSources (Torus d m) M} {q : S45.Sequence (Port d m)}
    (hq : slotSeq P j T M x k ω = some q)
    (hal2 : ((tileSlot P j T M k ω, false) : Port d m) ∈ (q.state q.length).live)
    {t0 : ℝ} (ht0le : t0 ≤ 1)
    (hsmall : ∀ t, 0 < t → t < t0 →
      S45.power t (S45.delta / 10) ≤ 1 / 4 ∧
      S45.power t S45.beta / (1 / C) ≤ 1 / 2 ∧
      2 * (1 + C ^ 2) * S45.power t S45.beta ≤ 1 / (2 * C) ∧
      C * Real.sqrt t < 1 / (2 * C) ∧
      Real.sqrt t < (4 * (3 * C) ^ 2)⁻¹)
    (htlt : sweepScale P.u m j < t0) :
    stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
      (q.state q.length) (tileSlot P j T M k ω, false) (tileXi P j T M x k ω) ≠ 0 := by
  have hu_pos : 0 < P.u := lt_trans (by norm_num) hu.1
  have htpos : 0 < sweepScale P.u m j := sweepScale_pos_first hu_pos m j
  have ht1 : sweepScale P.u m j ≤ 1 := htlt.le.trans ht0le
  have hC1 : 1 ≤ C := hx.one_le
  have inv := slotSeq_inv P j T M x hx ω k q hq
  obtain ⟨_, hbounds⟩ := prefix_schur_and_bounds P j T x hx inv.wellFormed
    (inv.state_prefix 0 (Nat.zero_le _)) inv.valid ht0le hsmall htpos htlt q.length le_rfl
  obtain ⟨_, _, hp3, _, hp5⟩ := hsmall (sweepScale P.u m j) htpos htlt
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set p : (q.state q.length).live := ⟨(tileSlot P j T M k ω, false), hal2⟩
  set ξ := tileXi P j T M x k ω
  set sq := (q.state q.length).state r
  have hraw : ‖sq.rawLag p‖ ≤ C := by
    have h1 := (hbounds p).1
    have h2 : 1 / (2 * C) ≤ C := by
      have : 1 ≤ 2 * C ^ 2 := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hrp : ‖sq.r p‖ ≤ C := (start_broad P j T x hx (live_mem_start x inv.wellFormed
    (inv.state_prefix 0 (Nat.zero_le _)) le_rfl hal2)).1
  have hg_plus_r : ‖sq.g p p‖ + ‖sq.r p‖ ≤ 3 * C := by
    have htri : ‖sq.g p p‖ ≤ ‖sq.r p‖ + ‖sq.rawLag p‖ := by
      have : sq.g p p = sq.r p + sq.rawLag p := by simp [S45.State.rawLag]
      rw [this]; exact norm_add_le _ _
    linarith
  have hξ : |ξ| ≤ (3 * C) * Real.sqrt t := by
    have h1 := abs_tileXi_le P j T M x hu_pos hj hjm hx k ω
    exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg t))
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
  have hsqrt_le : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hη : |ξ / Real.sqrt t| ≤ 3 * C := by
    rw [abs_div, abs_of_pos hsqrt_pos, div_le_iff₀ hsqrt_pos]
    exact hξ
  have hηeq : Real.sqrt t * (ξ / Real.sqrt t) = ξ := by field_simp
  have hgamma := AgentS45.gamma_pointwise_bounds (3 * C) t (Real.sqrt t) (ξ / Real.sqrt t) ξ
    sq p (by linarith) htpos hsqrt_pos hsqrt_le hp5 (Real.sq_sqrt htpos.le) hηeq hη hg_plus_r
  exact hgamma.1

end PrefixBounds


/-! ## Section 5: Local transfer (`c.valid` from `TraceTails` and `localBudget`) -/

section LocalTransferValid

theorem ShellBounds_mono {P : Type*} [Fintype P] {d : ℕ} {C C1 : ℝ} {dist : P → P → ℝ}
    (hs : S45.ShellBounds d C dist) (hCC : C ≤ C1) : S45.ShellBounds d C1 dist where
  nonneg := hs.nonneg
  symmetric := hs.symmetric
  triangle := hs.triangle
  self := hs.self
  count u hu hu1 i := (hs.count u hu hu1 i).trans
    (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hu.le _))
  second u hu hu1 i := (hs.second u hu hu1 i).trans
    (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hu.le _))

theorem TileCover_C_pos {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    [Nonempty P] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cov : S45.TileCover (P := P) (I := I) d t b C dist) : 0 < C := by
  obtain ⟨x⟩ := ‹Nonempty P›
  obtain ⟨T, hT, -⟩ := cov.cover x
  have hx : x ∈ cov.inner T := (cov.inside T).1 hT
  have hmem : T ∈ Finset.univ.filter (fun S => x ∈ cov.inner S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ T, hx⟩
  have hcard : (1 : ℝ) ≤ ((Finset.univ.filter (fun S => x ∈ cov.inner S)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨T, hmem⟩
  exact lt_of_lt_of_le zero_lt_one (hcard.trans (cov.overlap x))

def TileCover_mono {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    [Nonempty P] {d : ℕ} {t b C C1 : ℝ} {dist : P → P → ℝ}
    (ht : 0 < t) (hb : 0 < b) (hCC : C ≤ C1)
    (cov : S45.TileCover (P := P) (I := I) d t b C dist) :
    S45.TileCover (P := P) (I := I) d t b C1 dist where
  site := cov.site
  energy := cov.energy
  count := cov.count
  tile := cov.tile
  inner := cov.inner
  cube := cov.cube
  dim := cov.dim
  coords := cov.coords
  edge_symm := cov.edge_symm
  cutoff_one := cov.cutoff_one
  same_site := cov.same_site
  cover := cov.cover
  inside := cov.inside
  buffer := cov.buffer
  overlap i := (cov.overlap i).trans hCC
  dimension T := (cov.dimension T).trans
    (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg ht.le _))
  local_split T w := by
    obtain ⟨α, v, h1, h2⟩ := cov.local_split T w
    exact ⟨α, v, h1, h2.trans
      (mul_le_mul_of_nonneg_right hCC (Finset.sum_nonneg fun _ _ => sq_nonneg _))⟩
  kernel_energy u hu hu1 α v := by
    have hC0 : 0 < C := TileCover_C_pos cov
    have hE : 0 ≤ cov.energy v := AgentS45.cover_energy_nonneg cov hC0 hb v
    have hα : 0 ≤ S45.l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hrhs : 0 ≤ S45.power u (-(d : ℝ)) * S45.l2sq α +
        S45.power u (-(d : ℝ) - 2) * cov.energy v :=
      add_nonneg (mul_nonneg (Real.rpow_nonneg hu.le _) hα)
        (mul_nonneg (Real.rpow_nonneg hu.le _) hE)
    exact (cov.kernel_energy u hu hu1 α v).trans (mul_le_mul_of_nonneg_right hCC hrhs)
  local_sum α v := by
    have hC0 : 0 < C := TileCover_C_pos cov
    have hE : 0 ≤ cov.energy v := AgentS45.cover_energy_nonneg cov hC0 hb v
    have hα : 0 ≤ S45.l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact (cov.local_sum α v).trans
      (mul_le_mul_of_nonneg_right hCC (add_nonneg hα (div_nonneg hE hb.le)))

set_option maxHeartbeats 1000000 in
/-- Energy-form decomposition bound for `Lrecord` using port-level pivot injectivity `hinj`
(which holds automatically for every well-formed sequence via `wellFormed_pivot_injective`). -/
theorem local_transfer_decomposition_bound_hinj {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {d : ℕ} {C c t b : ℝ} {dist : P → P → ℝ}
    (cover : S45.TileCover (P := P) (I := I) d t b C dist)
    (q : S45.Sequence P) (blocks : Fin cover.count → Finset ℕ)
    (r : P → ℂ) (res : Finset P)
    (hC : 1 ≤ C) (_hc : 0 < c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hb : 0 < b) (hbt : b ≤ t)
    (shell : S45.ShellBounds d C dist)
    (hblocks : ∀ k < q.length, ∃! T, k ∈ blocks T)
    (hblockSub : ∀ T, blocks T ⊆ Finset.range q.length)
    (htile : ∀ k < q.length, ∀ x, q.pivot k = some x → ∀ T, k ∈ blocks T → x ∈ cover.tile T)
    (hinj : ∀ k l, k < q.length → l < q.length → ∀ x,
      q.pivot k = some x → q.pivot l = some x → k = l)
    (tails : S45.TraceTails q t C c r res dist)
    (hstep : ∀ k < q.length,
      (q.stepL t r k).IsSymm ∧ q.stepL t r k *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hbudget : ∀ T, S45.localBudget cover T (q.Jrecord t r (blocks T))
      (q.Lrecord t r (blocks T)) (q.lagRecord t r (blocks T))
      (q.rowRecord t r Finset.univ (blocks T)) (q.rowRecord t r res (blocks T)))
    (u : ℝ) (huDef : u = c * t ^ 3 / 2) (hu : 0 < u) (hu1 : u ≤ 1)
    (α : P → ℝ) (v : I → ℝ) :
    |S45.qform (q.Lrecord t r (Finset.range q.length))
        (fun x => α x + v (cover.site x))| ≤
      (C * S45.power t (S45.delta / 8) +
        2 * C ^ 4 * S45.power t (-C) * Real.exp (-u * S45.power t (-6)) *
          S45.power (u / 2) (-(d : ℝ)) * S45.power (u / 2) (-(d : ℝ) - 2)) *
        (S45.l2sq α + cover.energy v / b) := by
  classical
  let F : P → ℝ := fun x => α x + v (cover.site x)
  let G : Fin cover.count → P → ℝ := fun T =>
    (cover.cube T).extend (fun p => α p.1)
      (AgentS45.localCubeCentered (cover.cube T) v)
  let z := u / 2
  let A := S45.power t (-C)
  let R := S45.power t (-6)
  let S := C * S45.power z (-(d : ℝ))
  let far := A * Real.exp (-u * R)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hA : 0 ≤ A := (Real.rpow_pos_of_pos ht _).le
  have hfar : 0 ≤ far := by dsimp [far]; positivity
  have hS : 0 ≤ S := mul_nonneg hC0.le (Real.rpow_pos_of_pos hz _).le
  have hcost : 0 ≤ S45.l2sq α + cover.energy v / b := by
    have hE := AgentS45.cover_energy_nonneg cover hC0 hb v
    have hα : 0 ≤ S45.l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact add_nonneg hα (div_nonneg hE hb.le)
  have hdecay : -c * t ^ 3 = -(2 * u) := by rw [huDef]; ring
  have hstepTail (T : Fin cover.count) (k : ℕ) (hkT : k ∈ blocks T) :
      |S45.qform (q.stepL t r k) F - S45.qform (q.stepL t r k) (G T)| ≤
        far * ((q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F) +
          (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T))) := by
    have hk : k < q.length := Finset.mem_range.1 (hblockSub T hkT)
    cases hpv : q.pivot k with
    | none => simp [S45.Sequence.stepL, hpv, F, G, S45.qform]
    | some x =>
      have hxT := htile k hk x hpv T hkT
      have hagree : ∀ i ∈ cover.inner T, ∀ j ∈ cover.inner T,
          F i - F j = G T i - G T j := by
        intro i hi j hj
        have ei := AgentS45.local_extended_is_global_split cover T α v i hi
        have ej := AgentS45.local_extended_is_global_split cover T α v j hj
        have ei' : G T i + AgentS45.localCubeMean (cover.cube T) v = F i := by simpa [F] using ei
        have ej' : G T j + AgentS45.localCubeMean (cover.cube T) v = F j := by simpa [F] using ej
        linarith
      have hbuf : ∀ i j, (i ∉ cover.inner T ∨ j ∉ cover.inner T) →
          R ≤ dist i x + dist j x := by
        intro i j hout
        rcases hout with hi | hj
        · linarith [cover.buffer T x hxT i hi, shell.nonneg j x]
        · linarith [cover.buffer T x hxT j hj, shell.nonneg i x]
      have hrow : ∀ i, ∑ j, q.stepL t r k i j = 0 := by
        intro i
        have hi := congrFun (hstep k hk).2 i
        simpa [Matrix.mulVec, dotProduct] using hi
      have htail : ∀ i j, i ≠ j → |q.stepL t r k i j| ≤
          A * Real.exp (-(2 * u) * (dist i x + dist j x)) := by
        intro i j hij
        have h := tails.L k hk x hpv i j hij
        rw [hdecay] at h
        simpa [A] using h
      have h := AgentS45.step_tail_weighted dist shell (q.stepL t r k) (hstep k hk).1 hrow
        F (G T) (cover.inner T) hagree A u R hA hu x hbuf htail
      rw [← AgentS45.weightedGraphEnergy_add] at h
      simpa [far] using h
  have hlocalT (T : Fin cover.count) :
      |S45.qform (q.Lrecord t r (blocks T)) (G T)| ≤
        S45.power t (S45.delta / 8) *
          (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) :=
    AgentS45.local_block_form_bound (cover.cube T) b (cover.dim T) (cover.coords T)
      (cover.edge_symm T) (q.Lrecord t r (blocks T)) (fun p => α p.1) v
      (S45.power t (S45.delta / 8)) ((hbudget T).2.2.2)
  have hlocalSum :
      (∑ T, |S45.qform (q.Lrecord t r (blocks T)) (G T)|) ≤
        S45.power t (S45.delta / 8) * C * (S45.l2sq α + cover.energy v / b) := by
    calc (∑ T, |S45.qform (q.Lrecord t r (blocks T)) (G T)|)
        ≤ ∑ T, S45.power t (S45.delta / 8) *
            (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) :=
          Finset.sum_le_sum fun T _ => hlocalT T
      _ = S45.power t (S45.delta / 8) *
            ∑ T, (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
          rw [Finset.mul_sum]
      _ ≤ S45.power t (S45.delta / 8) * (C * (S45.l2sq α + cover.energy v / b)) :=
          mul_le_mul_of_nonneg_left (cover.local_sum α v) (Real.rpow_pos_of_pos ht _).le
      _ = _ := by ring
  have hFpartition :
      (∑ T, ∑ k ∈ blocks T,
        (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F)) =
      ∑ k ∈ Finset.range q.length,
        (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F) :=
    AgentS45.partition_sum q.length blocks hblocks hblockSub _
  have hFpivot :
      (∑ k ∈ Finset.range q.length,
        (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F)) ≤
      S * AgentS45.graphEnergy dist z F := by
    simpa [S, z] using AgentS45.pivot_weighted_graph_sum_le dist shell q.length q.pivot
      hinj z hz hz1 F
  have hGpivot :
      (∑ T, ∑ k ∈ blocks T,
        (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T))) ≤
      S * ∑ T, AgentS45.graphEnergy dist z (G T) := by
    calc (∑ T, ∑ k ∈ blocks T,
          (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T)))
        ≤ ∑ T, S * AgentS45.graphEnergy dist z (G T) := by
          refine Finset.sum_le_sum fun T _ => ?_
          let pvT : ℕ → Option P := fun k => if k ∈ blocks T then q.pivot k else none
          have hsumTle :
              (∑ k ∈ blocks T,
                (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T))) ≤
              ∑ k ∈ Finset.range q.length,
                (pvT k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T)) := by
            calc _ = ∑ k ∈ blocks T,
                  (pvT k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T)) :=
                Finset.sum_congr rfl fun k hk => by simp [pvT, hk]
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (hblockSub T) fun k _ hknot => by
                simp [pvT, hknot]
          have hinjT : ∀ k l, k < q.length → l < q.length → ∀ x,
              pvT k = some x → pvT l = some x → k = l := by
            intro k l hk hl x hx hy
            have hx' : k ∈ blocks T ∧ q.pivot k = some x := by simpa [pvT] using hx
            have hy' : l ∈ blocks T ∧ q.pivot l = some x := by simpa [pvT] using hy
            exact hinj k l hk hl x hx'.2 hy'.2
          exact hsumTle.trans (by
            simpa [S, z] using AgentS45.pivot_weighted_graph_sum_le dist shell q.length pvT
              hinjT z hz hz1 (G T))
      _ = S * ∑ T, AgentS45.graphEnergy dist z (G T) := by rw [Finset.mul_sum]
  have hFkernel' : AgentS45.graphEnergy dist z F ≤
      C * S45.power z (-(d : ℝ) - 2) * (S45.l2sq α + cover.energy v / b) :=
    AgentS45.kernel_graph_bound_split cover hC0 hb (hbt.trans ht1) z hz hz1 α v
  have hGkernel' :
      (∑ T, AgentS45.graphEnergy dist z (G T)) ≤
        C ^ 3 * S45.power z (-(d : ℝ) - 2) * (S45.l2sq α + cover.energy v / b) := by
    calc (∑ T, AgentS45.graphEnergy dist z (G T))
        ≤ ∑ T, C ^ 2 * S45.power z (-(d : ℝ) - 2) *
            (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) :=
          Finset.sum_le_sum fun T _ => AgentS45.local_extension_graph_bound cover T hC0 hb
            (hbt.trans ht1) z hz hz1 α v
      _ = C ^ 2 * S45.power z (-(d : ℝ) - 2) *
            ∑ T, (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
          rw [Finset.mul_sum]
      _ ≤ C ^ 2 * S45.power z (-(d : ℝ) - 2) *
            (C * (S45.l2sq α + cover.energy v / b)) :=
          mul_le_mul_of_nonneg_left (cover.local_sum α v)
            (mul_nonneg (sq_nonneg C) (Real.rpow_pos_of_pos hz _).le)
      _ = _ := by ring
  have htailSum :
      (∑ T, |S45.qform (q.Lrecord t r (blocks T)) F -
          S45.qform (q.Lrecord t r (blocks T)) (G T)|) ≤
        2 * C ^ 4 * far * S45.power z (-(d : ℝ)) * S45.power z (-(d : ℝ) - 2) *
          (S45.l2sq α + cover.energy v / b) := by
    have hblock (T : Fin cover.count) :
        |S45.qform (q.Lrecord t r (blocks T)) F -
          S45.qform (q.Lrecord t r (blocks T)) (G T)| ≤
        far * ((∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F)) +
          ∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T))) := by
      have hformula :
          S45.qform (q.Lrecord t r (blocks T)) F -
              S45.qform (q.Lrecord t r (blocks T)) (G T) =
            ∑ k ∈ blocks T,
              (S45.qform (q.stepL t r k) F - S45.qform (q.stepL t r k) (G T)) := by
        change S45.qform (∑ k ∈ blocks T, q.stepL t r k) F -
          S45.qform (∑ k ∈ blocks T, q.stepL t r k) (G T) = _
        rw [AgentS45.qform_finset_sum, AgentS45.qform_finset_sum, ← Finset.sum_sub_distrib]
      calc |S45.qform (q.Lrecord t r (blocks T)) F -
            S45.qform (q.Lrecord t r (blocks T)) (G T)|
          = ‖∑ k ∈ blocks T, (S45.qform (q.stepL t r k) F - S45.qform (q.stepL t r k) (G T))‖ := by
            rw [hformula, Real.norm_eq_abs]
        _ ≤ ∑ k ∈ blocks T, ‖S45.qform (q.stepL t r k) F - S45.qform (q.stepL t r k) (G T)‖ :=
            norm_sum_le _ _
        _ = ∑ k ∈ blocks T, |S45.qform (q.stepL t r k) F - S45.qform (q.stepL t r k) (G T)| := by
            simp [Real.norm_eq_abs]
        _ ≤ ∑ k ∈ blocks T,
              far * ((q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F) +
                (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T))) :=
            Finset.sum_le_sum fun k hk => hstepTail T k hk
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hC2 : 1 ≤ C ^ 2 := by nlinarith
    have hCpower : C ^ 2 + C ^ 4 ≤ 2 * C ^ 4 := by nlinarith [mul_le_mul_of_nonneg_right hC2 (sq_nonneg C)]
    have hpz1 : 0 ≤ S45.power z (-(d : ℝ)) := (Real.rpow_pos_of_pos hz _).le
    have hpz2 : 0 ≤ S45.power z (-(d : ℝ) - 2) := (Real.rpow_pos_of_pos hz _).le
    calc (∑ T, |S45.qform (q.Lrecord t r (blocks T)) F -
          S45.qform (q.Lrecord t r (blocks T)) (G T)|)
        ≤ ∑ T, far * ((∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F)) +
          ∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T))) :=
          Finset.sum_le_sum fun T _ => hblock T
      _ = far * ((∑ T, ∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x F)) +
          ∑ T, ∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => AgentS45.weightedGraphEnergy dist z x (G T))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ far * (S * AgentS45.graphEnergy dist z F +
          S * (C ^ 3 * S45.power z (-(d : ℝ) - 2) * (S45.l2sq α + cover.energy v / b))) := by
          rw [hFpartition]
          exact mul_le_mul_of_nonneg_left
            (add_le_add hFpivot (hGpivot.trans (mul_le_mul_of_nonneg_left hGkernel' hS))) hfar
      _ ≤ far * (S * (C * S45.power z (-(d : ℝ) - 2) * (S45.l2sq α + cover.energy v / b)) +
          S * (C ^ 3 * S45.power z (-(d : ℝ) - 2) * (S45.l2sq α + cover.energy v / b))) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hFkernel' hS) le_rfl) hfar
      _ = far * ((C ^ 2 + C ^ 4) * (S45.power z (-(d : ℝ)) * S45.power z (-(d : ℝ) - 2) *
            (S45.l2sq α + cover.energy v / b))) := by
          dsimp [S]; ring
      _ ≤ far * ((2 * C ^ 4) * (S45.power z (-(d : ℝ)) * S45.power z (-(d : ℝ) - 2) *
            (S45.l2sq α + cover.energy v / b))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hCpower (mul_nonneg (mul_nonneg hpz1 hpz2) hcost)) hfar
      _ = _ := by ring
  have hpartition :
      q.Lrecord t r (Finset.range q.length) = ∑ T, q.Lrecord t r (blocks T) := by
    ext i j
    simp only [S45.Sequence.Lrecord, Matrix.sum_apply]
    exact (AgentS45.partition_sum q.length blocks hblocks hblockSub
      (fun k => q.stepL t r k i j)).symm
  have hformPartition :
      S45.qform (q.Lrecord t r (Finset.range q.length)) F =
        ∑ T, S45.qform (q.Lrecord t r (blocks T)) F := by
    rw [hpartition, AgentS45.qform_sum]
  have htriangle (T : Fin cover.count) :
      |S45.qform (q.Lrecord t r (blocks T)) F| ≤
        |S45.qform (q.Lrecord t r (blocks T)) (G T)| +
          |S45.qform (q.Lrecord t r (blocks T)) F -
            S45.qform (q.Lrecord t r (blocks T)) (G T)| := by
    have h1 := abs_sub_le
      (S45.qform (q.Lrecord t r (blocks T)) F)
      (S45.qform (q.Lrecord t r (blocks T)) (G T)) 0
    simp only [sub_zero] at h1
    linarith
  calc |S45.qform (q.Lrecord t r (Finset.range q.length)) F|
      = ‖∑ T, S45.qform (q.Lrecord t r (blocks T)) F‖ := by rw [hformPartition, Real.norm_eq_abs]
    _ ≤ ∑ T, ‖S45.qform (q.Lrecord t r (blocks T)) F‖ := norm_sum_le _ _
    _ = ∑ T, |S45.qform (q.Lrecord t r (blocks T)) F| := by simp [Real.norm_eq_abs]
    _ ≤ ∑ T, (|S45.qform (q.Lrecord t r (blocks T)) (G T)| +
          |S45.qform (q.Lrecord t r (blocks T)) F -
            S45.qform (q.Lrecord t r (blocks T)) (G T)|) :=
        Finset.sum_le_sum fun T _ => htriangle T
    _ = (∑ T, |S45.qform (q.Lrecord t r (blocks T)) (G T)|) +
          ∑ T, |S45.qform (q.Lrecord t r (blocks T)) F -
            S45.qform (q.Lrecord t r (blocks T)) (G T)| := Finset.sum_add_distrib
    _ ≤ S45.power t (S45.delta / 8) * C * (S45.l2sq α + cover.energy v / b) +
          2 * C ^ 4 * far * S45.power z (-(d : ℝ)) * S45.power z (-(d : ℝ) - 2) *
            (S45.l2sq α + cover.energy v / b) := add_le_add hlocalSum htailSum
    _ = _ := by dsimp [far, A, R, z]; ring

/-- The spatial energy of `f` seen only on the ports of `L` (05:240–256 on the live ports):
decompositions `α + v ∘ site` agreeing with `f` on `L`, with `α` supported in `L`. -/
def liveSpatialEnergy {P I : Type*} [Fintype P] (L : Finset P) (site : P → I) (b : ℝ)
    (Λ : S45.Form I) : S45.Form P :=
  fun f => sInf {a : ℝ | ∃ α : P → ℝ, ∃ v : I → ℝ, (∀ x ∈ L, f x = α x + v (site x)) ∧
    (∀ x, x ∉ L → α x = 0) ∧ a = S45.l2sq α + Λ v / b}

set_option maxHeartbeats 1000000 in
/-- Polymorphic local transfer validity lemma: for any finite port/site types `P, I`,
if `q` is well-formed, starts from `live = univ` with symmetric/Ward initial state, zero initial
lag, initial fourth-moment rows `≤ 3/4 * rowCap t`, has a block partition satisfying `localBudget`,
and satisfies `TraceTails q t C c r res dist`, then `q.valid t r D0 q.length` holds for `t < t0`. -/
theorem local_transfer_valid_poly (d : ℕ) (C c : ℝ) (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ t0 > 0, ∀ (P I : Type) [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (t b : ℝ) (dist : P → P → ℝ) (r : P → ℂ) (res : Finset P)
    (cover : S45.TileCover (P := P) (I := I) d t b C dist)
    (q : S45.Sequence P) (blocks : Fin cover.count → Finset ℕ) (D0 : S45.RMat P),
    0 < t → t < t0 → 0 < b → b ≤ t →
    S45.ShellBounds d C dist → q.wellFormed t r →
    (∀ k ≤ q.length, ((q.state k).state r).g.IsSymm) →
    (∀ k < q.length, ∃! T, k ∈ blocks T) → (∀ T, blocks T ⊆ Finset.range q.length) →
    (∀ k < q.length, ∀ x, q.pivot k = some x → ∀ T, k ∈ blocks T → x ∈ cover.tile T) →
    S45.TraceTails q t C c r res dist →
    (∀ f, liveSpatialEnergy (q.state 0).live cover.site b cover.energy f ≤ C * S45.qform D0 f) →
    (∀ i ∈ (q.state 0).live, (q.state 0).ambientLag t r i = 0) →
    (∀ i ∈ (q.state 0).live,
      ((q.state 0).ambient r).fourthRow t Finset.univ i ≤ 3 / 4 * S45.rowCap t) →
    (∀ T, S45.localBudget cover T (q.Jrecord t r (blocks T)) (q.Lrecord t r (blocks T))
      (q.lagRecord t r (blocks T)) (q.rowRecord t r Finset.univ (blocks T))
      (q.rowRecord t r res (blocks T))) →
    q.valid t r D0 q.length := by
  have hC0 : 0 < C := by linarith
  obtain ⟨tTail, htTail, htailSmall⟩ := AgentS45.tail_transfer_coefficient_small (d := d) hC hc
  obtain ⟨t1, ht1, htail⟩ := AgentS45.tail_small C C c d hc
  let CL := C * (C + 1)
  let C' : ℝ := max (C + 1) CL
  have hC'pos : 0 < C' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hC1 : C + 1 ≤ C' := le_max_left _ _
  have hCLle : CL ≤ C' := le_max_right _ _
  obtain ⟨t2, ht2, hs2⟩ := AgentS45.power_small (e := S45.delta / 40)
    (by norm_num [S45.delta]) (a := 1 / C') (by positivity)
  obtain ⟨t3, ht3, hs3⟩ := AgentS45.power_small (e := S45.delta / 2000)
    (by norm_num [S45.delta]) (a := 1 / (4 * C')) (by positivity)
  obtain ⟨t4, ht4, hs4⟩ := AgentS45.power_small (e := S45.delta / 50)
    (by norm_num [S45.delta]) (a := 1 / C') (by positivity)
  obtain ⟨t5, ht5, hs5⟩ := AgentS45.power_small (e := 3) (by norm_num) (a := 2 / c) (by positivity)
  refine ⟨min (min (min tTail t1) (min t2 t3)) (min (min t4 t5) 1), by positivity, ?_⟩
  intro P I _ _ _ _ t b dist r res cover q blocks D0 ht htt hb hbt hshell hwf
    hsym_all hblk hbsub htile htails hcomp hu0 hrow0 hbud
  have httTail : t < tTail := lt_of_lt_of_le htt (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _)))
  have htt1 : t < t1 := lt_of_lt_of_le htt (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have htt2 : t < t2 := lt_of_lt_of_le htt (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htt3 : t < t3 := lt_of_lt_of_le htt (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))
  have htt4 : t < t4 := lt_of_lt_of_le htt (le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _)))
  have htt5 : t < t5 := lt_of_lt_of_le htt (le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have ht1' : t ≤ 1 := (lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_right _ _))).le
  have hinj : ∀ k l, k < q.length → l < q.length → ∀ x,
      q.pivot k = some x → q.pivot l = some x → k = l :=
    fun k l hk hl x hx hy => wellFormed_pivot_injective hwf hk hl hx hy
  have hstepL : ∀ k < q.length, (q.stepL t r k).IsSymm ∧ q.stepL t r k *ᵥ (fun _ => 1) = 0 :=
    AgentS45.stepLLaplacian_proof P q t r hwf hsym_all
  set u : ℝ := c * t ^ 3 / 2 with hudef
  have hu0' : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    have h := hs5 t ht htt5
    have : S45.power t 3 = t ^ 3 := by
      show t ^ (3 : ℝ) = t ^ 3; exact_mod_cast Real.rpow_natCast t 3
    rw [this] at h
    rw [hudef]
    have := mul_lt_mul_of_pos_left h hc
    rw [mul_div_cancel₀ _ (ne_of_gt hc)] at this
    linarith
  have hLpart : S45.formAbsLe (S45.qform (q.Lrecord t r (Finset.range q.length)))
      (S45.qform D0) (CL * S45.power t (S45.delta / 8)) := by
    have htEps : t ≤ S45.power t (S45.delta / 8) :=
      AgentS45.le_power_of_le_one ht ht1' (by norm_num [S45.delta])
    have htailT :
        2 * C ^ 4 * S45.power t (-C) * Real.exp (-u * S45.power t (-6)) *
          S45.power (u / 2) (-(d : ℝ)) * S45.power (u / 2) (-(d : ℝ) - 2) ≤
        S45.power t (S45.delta / 8) := by
      have h := htailSmall t ht httTail
      have huHalf : u / 2 = c * t ^ 3 / 4 := by dsimp [u]; ring
      calc _ ≤ t := by rw [hudef, huHalf]; exact h
        _ ≤ S45.power t (S45.delta / 8) := htEps
    have hsplitBound (α : P → ℝ) (v : I → ℝ) :
        |S45.qform (q.Lrecord t r (Finset.range q.length))
            (fun x => α x + v (cover.site x))| ≤
          (C + 1) * S45.power t (S45.delta / 8) *
            (S45.l2sq α + cover.energy v / b) := by
      have hraw := local_transfer_decomposition_bound_hinj cover q blocks r res hC hc ht ht1'
        hb hbt hshell hblk hbsub htile hinj htails hstepL hbud u hudef hu0' hu1 α v
      have hcost : 0 ≤ S45.l2sq α + cover.energy v / b := by
        have hE := AgentS45.cover_energy_nonneg cover hC0 hb v
        have hα : 0 ≤ S45.l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
        exact add_nonneg hα (div_nonneg hE hb.le)
      have hcoef : C * S45.power t (S45.delta / 8) +
          2 * C ^ 4 * S45.power t (-C) * Real.exp (-u * S45.power t (-6)) *
            S45.power (u / 2) (-(d : ℝ)) * S45.power (u / 2) (-(d : ℝ) - 2) ≤
          (C + 1) * S45.power t (S45.delta / 8) := by nlinarith [htailT]
      exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hcost)
    have hB : 0 < (C + 1) * S45.power t (S45.delta / 8) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos ht _)
    intro f
    let S0 := (q.state 0).live
    let Costs : Set ℝ := {a | ∃ α : P → ℝ, ∃ v : I → ℝ,
      (∀ x ∈ S0, f x = α x + v (cover.site x)) ∧ (∀ x, x ∉ S0 → α x = 0) ∧
        a = S45.l2sq α + cover.energy v / b}
    have hCostsNonempty : Costs.Nonempty :=
      ⟨S45.l2sq (fun x => if x ∈ S0 then f x else 0) + cover.energy (fun _ => 0) / b,
        fun x => if x ∈ S0 then f x else 0, (fun _ => 0),
        ⟨fun x hx => by simp [hx], fun x hx => by simp [hx], rfl⟩⟩
    have hLsupp : ∀ i j, i ∉ S0 ∨ j ∉ S0 →
        q.Lrecord t r (Finset.range q.length) i j = 0 :=
      Lrecord_supported hwf (Finset.range q.length) subset_rfl
    have hCostsLower : |S45.qform (q.Lrecord t r (Finset.range q.length)) f| /
        ((C + 1) * S45.power t (S45.delta / 8)) ≤ sInf Costs := by
      apply le_csInf hCostsNonempty
      rintro a ⟨α, v, hsplit, -, rfl⟩
      have hdecomp := hsplitBound α v
      have hfun : S45.qform (q.Lrecord t r (Finset.range q.length)) f =
          S45.qform (q.Lrecord t r (Finset.range q.length)) (fun x => α x + v (cover.site x)) :=
        qform_congr_of_support _ S0 hLsupp f _ hsplit
      rw [← hfun] at hdecomp
      exact (div_le_iff₀ hB).2 (by simpa [mul_comm] using hdecomp)
    have hspatialCompare : sInf Costs ≤ C * S45.qform D0 f := hcomp f
    have hglobal : |S45.qform (q.Lrecord t r (Finset.range q.length)) f| ≤
        (C + 1) * S45.power t (S45.delta / 8) * sInf Costs := by
      have h := (div_le_iff₀ hB).1 hCostsLower
      simpa [mul_comm] using h
    calc |S45.qform (q.Lrecord t r (Finset.range q.length)) f|
        ≤ (C + 1) * S45.power t (S45.delta / 8) * (C * S45.qform D0 f) :=
          hglobal.trans (mul_le_mul_of_nonneg_left hspatialCompare hB.le)
      _ = CL * S45.power t (S45.delta / 8) * S45.qform D0 f := by dsimp [CL]; ring
  set A : ℝ := S45.power t (-C)
  have hA0 : 0 ≤ A := (Real.rpow_pos_of_pos ht _).le
  set R : ℝ := S45.power t (-6)
  set S : ℝ := C * S45.power u (-(d : ℝ))
  have hS1' : 1 ≤ S45.power u (-(d : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0' hu1 (by simp)
  have hS0 : 0 ≤ S := by positivity
  have hSge : 1 ≤ S := by nlinarith
  have hcount1 : ∀ x, (∑ j, Real.exp (-u * dist j x)) ≤ S := by
    intro x
    calc (∑ j, Real.exp (-u * dist j x)) = ∑ j, Real.exp (-u * dist x j) :=
          Finset.sum_congr rfl fun j _ => by rw [hshell.symmetric]
      _ ≤ S := hshell.count u hu0' hu1 x
  have hcount2 : ∀ i, (∑ x, Real.exp (-u * dist i x)) ≤ S := fun i => hshell.count u hu0' hu1 i
  have htailt : A * Real.exp (-u * R) * S ^ 2 ≤ t := htail t ht htt1
  have hTAIL : ∀ e, e ≤ 1 → A * Real.exp (-u * R) * S ^ 2 ≤ S45.power t e := fun e he =>
    htailt.trans (AgentS45.le_power_of_le_one ht ht1' he)
  have hTAIL1 : ∀ i, A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist i x) ≤
      A * Real.exp (-u * R) * S ^ 2 := by
    intro i
    refine mul_le_mul_of_nonneg_left ((hcount2 i).trans ?_) (by positivity)
    nlinarith
  have hov : ∀ i, ((Finset.univ.filter fun T => i ∈ cover.inner T).card : ℝ) ≤ C := cover.overlap
  have hbuf : ∀ T, ∀ x ∈ cover.tile T, ∀ i, i ∉ cover.inner T → R ≤ dist i x := cover.buffer
  have hexpu : ∀ z : ℝ, Real.exp (-c * t ^ 3 * z) = Real.exp (-(2 * u) * z) := fun z => by
    rw [hudef]; congr 1; ring
  have hJ : ‖q.Jrecord t r (Finset.range q.length)‖ ≤ (C + 1) * S45.power t (S45.delta / 8) := by
    have h := AgentS45.matrix_transfer q.length q.pivot hinj blocks hblk hbsub cover.inner
      cover.tile dist hshell.nonneg C (S45.power t (S45.delta / 8)) A u R S hu0'.le hA0
      (Real.rpow_pos_of_pos ht _).le hC0.le hS0 hov htile hbuf hcount1 hcount2
      (fun k => q.stepJ t r k) (fun k hk hpv => (AgentS45.step_none hwf hk hpv).1)
      (fun k hk x hpv i j => by rw [← hexpu]; exact htails.J k hk x hpv i j)
      (fun T => (hbud T).2.2.1)
    have h2 := hTAIL (S45.delta / 8) (by norm_num [S45.delta])
    change ‖∑ k ∈ Finset.range q.length, q.stepJ t r k‖ ≤ _
    linarith
  have hlag : ∀ i, ‖q.lagRecord t r (Finset.range q.length) i‖ ≤
      (C + 1) * S45.power t (11 * S45.delta / 25) := by
    intro i
    have h := AgentS45.scalar_transfer q.length q.pivot hinj blocks hblk hbsub cover.inner
      cover.tile dist C (S45.power t (11 * S45.delta / 25)) A u R hu0'.le hA0
      (Real.rpow_pos_of_pos ht _).le hov htile hbuf
      (fun k => q.stepLag t r k) (fun k hk hpv => (AgentS45.step_none hwf hk hpv).2.1)
      (fun k hk x hpv i => by rw [← hexpu]; exact htails.lag k hk x hpv i)
      (fun T i hi => by simpa [S45.Sequence.lagRecord, Finset.sum_apply] using (hbud T).1 i hi) i
    have h2 := (hTAIL1 i).trans (hTAIL (11 * S45.delta / 25) (by norm_num [S45.delta]))
    have e : q.lagRecord t r (Finset.range q.length) i =
        ∑ k ∈ Finset.range q.length, q.stepLag t r k i := by
      simp [S45.Sequence.lagRecord, Finset.sum_apply]
    rw [e]; linarith
  have hrowb : ∀ i, |q.rowRecord t r Finset.univ (Finset.range q.length) i| ≤
      (C + 1) * S45.power t (S45.delta / 2000) := by
    intro i
    have h := AgentS45.scalar_transfer q.length q.pivot hinj blocks hblk hbsub cover.inner
      cover.tile dist C (S45.power t (S45.delta / 2000)) A u R hu0'.le hA0
      (Real.rpow_pos_of_pos ht _).le hov htile hbuf
      (fun k => q.stepRow t r Finset.univ k)
      (fun k hk hpv => (AgentS45.step_none hwf hk hpv).2.2 Finset.univ)
      (fun k hk x hpv i => by
        rw [← hexpu, Real.norm_eq_abs]
        linarith [htails.rows k hk x hpv i, abs_nonneg (q.stepRow t r res k i)])
      (fun T i hi => by
        rw [Real.norm_eq_abs]
        simpa [S45.Sequence.rowRecord, Finset.sum_apply] using ((hbud T).2.1 i hi).1) i
    have h2 := (hTAIL1 i).trans (hTAIL (S45.delta / 2000) (by norm_num [S45.delta]))
    have e : q.rowRecord t r Finset.univ (Finset.range q.length) i =
        ∑ k ∈ Finset.range q.length, q.stepRow t r Finset.univ k i := by
      simp [S45.Sequence.rowRecord, Finset.sum_apply]
    rw [e, ← Real.norm_eq_abs]; linarith
  have hp40 : C' * S45.power t (S45.delta / 40) ≤ 1 := by
    have := hs2 t ht htt2; rw [lt_div_iff₀ hC'pos] at this; linarith
  have hp2000 : C' * S45.power t (S45.delta / 2000) ≤ 1 / 4 := by
    have := hs3 t ht htt3; rw [lt_div_iff₀ (by positivity)] at this; linarith
  have hp50 : C' * S45.power t (S45.delta / 50) ≤ 1 := by
    have := hs4 t ht htt4; rw [lt_div_iff₀ hC'pos] at this; linarith
  have hpw : ∀ e, 0 ≤ S45.power t e := fun e => (Real.rpow_pos_of_pos ht _).le
  have hrc : 0 ≤ S45.rowCap t := hpw _
  have e8 : S45.power t (S45.delta / 8) =
      S45.power t (S45.delta / 40) * S45.power t (S45.delta / 10) := by
    rw [← AgentS45.power_split ht]; norm_num [S45.delta]
  have e44 : S45.power t (11 * S45.delta / 25) =
      S45.power t (S45.delta / 50) * S45.power t S45.beta := by
    rw [← AgentS45.power_split ht]; norm_num [S45.delta, S45.beta]
  have hLmono : ∀ a', CL * S45.power t (S45.delta / 8) ≤ a' →
      S45.formAbsLe (S45.qform (q.Lrecord t r (Finset.range q.length))) (S45.qform D0) a' := by
    intro a' ha' f
    have h := hLpart f
    have hpos : 0 < CL * S45.power t (S45.delta / 8) := by
      have := Real.rpow_pos_of_pos ht (S45.delta / 8); dsimp [CL]; positivity
    have hR0 : 0 ≤ S45.qform D0 f := by
      by_contra hneg
      have hneg' : S45.qform D0 f < 0 := not_le.mp hneg
      have : CL * S45.power t (S45.delta / 8) * S45.qform D0 f < 0 := mul_neg_of_pos_of_neg hpos hneg'
      linarith [abs_nonneg (S45.qform (q.Lrecord t r (Finset.range q.length)) f)]
    exact h.trans (mul_le_mul_of_nonneg_right ha' hR0)
  have hlag0 : ∀ i ∈ (q.state 0).live, (q.state 0).ambientLag t r i = 0 := hu0
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hJ.trans ?_
    rw [e8]
    have : (C + 1) * S45.power t (S45.delta / 40) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hC1 (hpw _)) hp40
    nlinarith [hpw (S45.delta / 10), hpw (S45.delta / 40)]
  · refine hLmono _ ?_
    rw [e8]
    have : CL * S45.power t (S45.delta / 40) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hCLle (hpw _)) hp40
    nlinarith [hpw (S45.delta / 10), hpw (S45.delta / 40)]
  · intro i
    have hsr' := (AgentS45.scalar_records_proof q t r Finset.univ ht hwf hlag0 i.1 i.2).2
    rw [Finset.univ_inter, Finset.univ_inter] at hsr'
    have e1 : ((q.state q.length).state r).fourthRow t Finset.univ i =
        ∑ j ∈ (q.state q.length).live, ‖((q.state q.length).ambient r).h t i j‖ ^ 4 := by
      simp only [S45.State.fourthRow]
      rw [← Finset.sum_coe_sort (q.state q.length).live]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [AgentS45.ambient_h_live _ r t i.2 j.2]
    have hi0 : i.1 ∈ (q.state 0).live :=
      wellFormed_live_antitone hwf (Nat.zero_le _) le_rfl i.2
    have h0' := hrow0 i.1 hi0
    simp only [S45.State.fourthRow] at h0'
    have h0 : ∑ j ∈ (q.state 0).live, ‖((q.state 0).ambient r).h t i j‖ ^ 4 ≤
        3 / 4 * S45.rowCap t :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by positivity)).trans h0'
    have hrr' : q.rowRecord t r Finset.univ (Finset.range q.length) i ≤
        (C + 1) * S45.power t (S45.delta / 2000) := (le_abs_self _).trans (hrowb i.1)
    have hc1 : (C + 1) * S45.power t (S45.delta / 2000) ≤ 1 / 4 :=
      le_trans (mul_le_mul_of_nonneg_right hC1 (hpw _)) hp2000
    rw [e1]
    calc _ ≤ _ := hsr'
      _ ≤ 3 / 4 * S45.rowCap t + S45.rowCap t * ((C + 1) * S45.power t (S45.delta / 2000)) :=
          add_le_add h0 (mul_le_mul_of_nonneg_left hrr' hrc)
      _ ≤ 3 / 4 * S45.rowCap t + S45.rowCap t * (1 / 4) := by
          nlinarith [mul_le_mul_of_nonneg_left hc1 hrc]
      _ = S45.rowCap t := by ring
  · intro i
    have hsr' := (AgentS45.scalar_records_proof q t r Finset.univ ht hwf hlag0 i.1 i.2).1
    have e1 : (q.state q.length).ambientLag t r i.1 = ((q.state q.length).state r).lag t i := by
      simp [S45.LiveState.ambientLag, i.2]
    rw [← e1, ← hsr']
    refine (hlag i.1).trans ?_
    rw [e44]
    have : (C + 1) * S45.power t (S45.delta / 50) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hC1 (hpw _)) hp50
    nlinarith [hpw S45.beta, hpw (S45.delta / 50)]

theorem spatialEnergy_nonneg {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    [Nonempty P] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cov : S45.TileCover (P := P) (I := I) d t b C dist) (hb : 0 < b) (f : P → ℝ) :
    0 ≤ S45.spatialEnergy cov.site b cov.energy f := by
  have hC0 : 0 < C := TileCover_C_pos cov
  apply Real.sInf_nonneg
  intro a ⟨α, v, _, ha⟩
  rw [ha]
  have hE : 0 ≤ cov.energy v := AgentS45.cover_energy_nonneg cov hC0 hb v
  have hα : 0 ≤ S45.l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact add_nonneg hα (div_nonneg hE hb.le)

theorem formComparable_mono_a3b {P : Type*} {F G : S45.Form P} {C C1 : ℝ}
    (hC : 0 < C) (hCC : C ≤ C1) (hG : ∀ f, 0 ≤ G f)
    (hcomp : S45.formComparable F G C) : S45.formComparable F G C1 := by
  intro f
  refine ⟨?_, ?_⟩
  · exact (div_le_div_of_nonneg_left (hG f) hC hCC).trans (hcomp f).1
  · exact (hcomp f).2.trans (mul_le_mul_of_nonneg_right hCC (hG f))

theorem slotSeq_records_of_subset {d m : ℕ} {P : TilePlan d m} {j : ℕ}
    {T : Fin (P.cover j).cover.count} {M : ℕ → ℕ} {x : RunRecord d m}
    {ω : RandomSources (Torus d m) M} {q : S45.Sequence (Port d m)}
    (inv : SlotSeqInv P j T M x ω q) (t : ℝ) (r : Port d m → ℂ) {K : Finset ℕ}
    (hK : K ⊆ Finset.range x.sweep.length) :
    q.Jrecord t r K = x.sweep.Jrecord t r K ∧
    q.Lrecord t r K = x.sweep.Lrecord t r K ∧
    q.lagRecord t r K = x.sweep.lagRecord t r K ∧
    (∀ cols, q.rowRecord t r cols K = x.sweep.rowRecord t r cols K) := by
  refine ⟨Finset.sum_congr rfl fun s hs => ?_,
    Finset.sum_congr rfl fun s hs => ?_,
    Finset.sum_congr rfl fun s hs => ?_,
    fun cols => Finset.sum_congr rfl fun s hs => ?_⟩
  · have hs0 : s < x.sweep.length := Finset.mem_range.mp (hK hs)
    unfold S45.Sequence.stepJ
    rw [inv.pivot_prefix s hs0, inv.state_prefix s hs0.le,
      inv.state_prefix (s + 1) (Nat.succ_le_of_lt hs0), inv.scalar_prefix s hs0]
  · have hs0 : s < x.sweep.length := Finset.mem_range.mp (hK hs)
    unfold S45.Sequence.stepL
    rw [inv.pivot_prefix s hs0, inv.state_prefix s hs0.le,
      inv.state_prefix (s + 1) (Nat.succ_le_of_lt hs0), inv.scalar_prefix s hs0]
  · have hs0 : s < x.sweep.length := Finset.mem_range.mp (hK hs)
    funext i
    unfold S45.Sequence.stepLag
    rw [inv.state_prefix s hs0.le, inv.state_prefix (s + 1) (Nat.succ_le_of_lt hs0)]
  · have hs0 : s < x.sweep.length := Finset.mem_range.mp (hK hs)
    funext i
    unfold S45.Sequence.stepRow
    rw [inv.state_prefix s hs0.le, inv.state_prefix (s + 1) (Nat.succ_le_of_lt hs0)]

/-- **v3.1 start comparison** (05:328 on the active-site ports): the live spatial energy of
the start live set is controlled by the stage-start form `D₀`. -/
theorem start_live_comparison {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (hx : TileGoodCore C P j T x)
    (f : Port d m → ℝ) :
    0 ≤ S45.qform (stageD0 P j x) f ∧
      liveSpatialEnergy (x.sweep.state 0).live (P.cover j).cover.site (P.cover j).b
        (P.cover j).cover.energy f ≤ C * S45.qform (stageD0 P j x) f := by
  classical
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set L := (x.sweep.state 0).live with hLdef
  set e := startEquiv P j T x hx
  set s3 := stageStartV3 P j x
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hx.one_le
  have hb : 0 < (P.cover j).b := hx.cover_b.1
  have : Nonempty (Port d m) := ⟨(site₀ d m, false)⟩
  have hE : ∀ v, 0 ≤ (P.cover j).cover.energy v := fun v =>
    AgentS45.cover_energy_nonneg (P.cover j).cover (TileCover_C_pos (P.cover j).cover) hb v
  let y : S45.initialPorts {i // i ∈ x.endpoint.active} → ℝ := fun a => f (e.symm a).1
  -- the form identity `q_{D₀}(f) = q_{D₀^{v3}}(f ∘ activePort)`
  have hQ : S45.qform (stageD0 P j x) f = S45.qform (s3.D t) y := by
    apply qform_of_support_equiv L e
    · intro i k hi hk
      change ((x.sweep.state 0).ambient r).D t i k = _
      rw [ambient_D_live _ r t hi hk, start_state_eq_reindex P j T x hx, reindex_D]
    · intro i k hik
      exact ambient_D_dead _ r t hik
  -- the frozen comparison on the active-site ports
  set site' := fun p => (P.cover j).cover.site (activePort x p)
  have hcomp := hx.start_comparison y
  have hR0 : 0 ≤ S45.spatialEnergy site' (P.cover j).b (P.cover j).cover.energy y := by
    apply Real.sInf_nonneg
    rintro a ⟨α, v, -, rfl⟩
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (div_nonneg (hE v) hb.le)
  have hRC : S45.spatialEnergy site' (P.cover j).b (P.cover j).cover.energy y ≤
      C * S45.qform (s3.D t) y := by
    have h := (div_le_iff₀ hCpos).1 hcomp.1
    linarith
  have hQ0 : 0 ≤ S45.qform (s3.D t) y :=
    le_trans (div_nonneg hR0 hCpos.le) hcomp.1
  refine ⟨hQ ▸ hQ0, ?_⟩
  rw [hQ]
  refine le_trans ?_ hRC
  -- every decomposition on the active-site ports extends to the start live set
  unfold liveSpatialEnergy S45.spatialEnergy
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    rintro a ⟨α, v, -, -, rfl⟩
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (div_nonneg (hE v) hb.le)
  · exact ⟨_, y, fun _ => 0, fun p => by simp, rfl⟩
  · rintro a ⟨α', v, hsplit, rfl⟩
    refine ⟨fun z => if hz : z ∈ L then α' (e ⟨z, hz⟩) else 0, v, ?_, ?_, ?_⟩
    · intro z hz
      simp only [dif_pos hz]
      exact hsplit (e ⟨z, hz⟩)
    · intro z hz
      simp [hz]
    · congr 1
      have hsum : ∀ g : Port d m → ℝ, (∀ i, i ∉ L → g i = 0) →
          ∑ i, g i = ∑ a, g (e.symm a).1 := by
        intro g hg
        rw [← Finset.sum_subset (Finset.subset_univ L) (fun i _ hi => hg i hi),
          ← Finset.sum_coe_sort L g]
        exact (Equiv.sum_comp e.symm (fun i : L => g i.1)).symm
      unfold S45.l2sq
      rw [hsum _ (fun i hi => by simp [hi])]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [dif_pos (e.symm a).2]
      simp

/-- Applying `local_transfer_valid_poly` to the candidate extension `c` in `TileTransferStatement`. -/
theorem valid_of_traceTails {d m : ℕ} {C C_tail c_tail t0_valid : ℝ}
    (hCC : C ≤ C_tail)
    (hvalid : ∀ (P I : Type) [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
      (t b : ℝ) (dist : P → P → ℝ) (r : P → ℂ) (res : Finset P)
      (cover : S45.TileCover (P := P) (I := I) d t b C_tail dist)
      (q : S45.Sequence P) (blocks : Fin cover.count → Finset ℕ) (D0 : S45.RMat P),
      0 < t → t < t0_valid → 0 < b → b ≤ t →
      S45.ShellBounds d C_tail dist → q.wellFormed t r →
      (∀ k ≤ q.length, ((q.state k).state r).g.IsSymm) →
      (∀ k < q.length, ∃! T, k ∈ blocks T) → (∀ T, blocks T ⊆ Finset.range q.length) →
      (∀ k < q.length, ∀ x, q.pivot k = some x → ∀ T, k ∈ blocks T → x ∈ cover.tile T) →
      S45.TraceTails q t C_tail c_tail r res dist →
      (∀ f, liveSpatialEnergy (q.state 0).live cover.site b cover.energy f ≤
        C_tail * S45.qform D0 f) →
      (∀ i ∈ (q.state 0).live, (q.state 0).ambientLag t r i = 0) →
      (∀ i ∈ (q.state 0).live,
        ((q.state 0).ambient r).fourthRow t Finset.univ i ≤ 3 / 4 * S45.rowCap t) →
      (∀ T, S45.localBudget cover T (q.Jrecord t r (blocks T)) (q.Lrecord t r (blocks T))
        (q.lagRecord t r (blocks T)) (q.rowRecord t r Finset.univ (blocks T))
        (q.rowRecord t r res (blocks T))) →
      q.valid t r D0 q.length)
    (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m) (hu_pos : 0 < P.u)
    (hx : TileGoodCore C P j T x)
    (k : ℕ) (ω : RandomSources (Torus d m) M) (q : S45.Sequence (Port d m))
    (hq : slotSeq P j T M x k ω = some q)
    (hact : activeIn P j T x (tileSlot P j T M k ω))
    (hal2 : ((tileSlot P j T M k ω, false) : Port d m) ∈ (q.state q.length).live)
    (hden : stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
      (q.state q.length) (tileSlot P j T M k ω, false) (tileXi P j T M x k ω) ≠ 0)
    (htlt : sweepScale P.u m j < t0_valid)
    (hbud : let c := candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω)
      let t := sweepScale P.u m j
      let r := portR (sweepTheta P.u m j) x.r
      let K := Finset.Ico x.sweep.length c.length
      S45.localBudget (P.cover j).cover T
        (c.Jrecord t r K) (c.Lrecord t r K) (c.lagRecord t r K)
        (c.rowRecord t r Finset.univ K) (c.rowRecord t r S45.reserves K))
    (htails : S45.TraceTails
      (candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
      (sweepScale P.u m j) C_tail c_tail (portR (sweepTheta P.u m j) x.r)
      S45.reserves (P.cover j).dist) :
    (candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω)).valid
      (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (stageD0 P j x)
      (candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω)).length := by
  classical
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set y := tileSlot P j T M k ω
  set p : Port d m := (y, false)
  set ξ := tileXi P j T M x k ω
  set b := stepLive t r (q.state q.length) p ξ
  set c := candidate P j x q y ξ
  have hc_def : c = extendSeq q b p ξ := rfl
  have htpos : 0 < t := sweepScale_pos_first hu_pos m j
  have hC1 : 1 ≤ C := hx.one_le
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have inv := slotSeq_inv P j T M x hx ω k q hq
  have hc_wf : c.wellFormed t r := extendSeq_wellFormed t r q inv.wellFormed p ξ hal2 hden
  have hc_state0 : c.state 0 = x.sweep.state 0 := by
    rw [hc_def, extendSeq_state_of_le q b p ξ (Nat.zero_le _), inv.state_prefix 0 (Nat.zero_le _)]
  obtain ⟨hsym0_c, hward0_c⟩ := start_state_isSymm_ward P j T x hc_state0 hx
  have hsym_all : ∀ s ≤ c.length, ((c.state s).state r).g.IsSymm :=
    fun s hs => (wellFormed_symm_ward htpos hc_wf hsym0_c hward0_c s hs).1
  have : Nonempty (Port d m) := ⟨(site₀ d m, false)⟩
  let cov' := TileCover_mono htpos hx.cover_b.1 (hx.cover_C.trans hCC) (P.cover j).cover
  have hshell' : S45.ShellBounds d C_tail (P.cover j).dist := ShellBounds_mono hx.shell hCC
  have hcomp' : ∀ f, liveSpatialEnergy (c.state 0).live cov'.site (P.cover j).b cov'.energy f ≤
      C_tail * S45.qform (stageD0 P j x) f := by
    intro f
    rw [hc_state0]
    obtain ⟨hQ0, hle⟩ := start_live_comparison P j T x hx f
    exact hle.trans (mul_le_mul_of_nonneg_right hCC hQ0)
  obtain ⟨blocks, hblk0, hbsub0, htile0, hTempty, hbud0⟩ := hx.accepted
  let cBlocks : Fin (P.cover j).cover.count → Finset ℕ :=
    fun S => if S = T then Finset.Ico x.sweep.length c.length else blocks S
  have hq_le_c : x.sweep.length ≤ c.length := by
    rw [hc_def, extendSeq_length_a3b]
    exact le_trans inv.len_ge (Nat.le_succ _)
  have hc_blk : ∀ s < c.length, ∃! S, s ∈ cBlocks S := by
    intro s hs
    by_cases hs0 : s < x.sweep.length
    · obtain ⟨S, hS, hSuniq⟩ := hblk0 s hs0
      have hST : S ≠ T := by
        intro hEq; subst hEq; rw [hTempty] at hS; exact Finset.notMem_empty s hS
      refine ⟨S, by simp [cBlocks, hST, hS], fun S' hS' => ?_⟩
      by_cases hS'T : S' = T
      · subst hS'T
        simp only [cBlocks, ↓reduceIte, Finset.mem_Ico] at hS'
        omega
      · simp only [cBlocks, hS'T, ↓reduceIte] at hS'
        exact hSuniq S' hS'
    · refine ⟨T, ?_, fun S' hS' => ?_⟩
      · simp only [cBlocks, ↓reduceIte, Finset.mem_Ico]
        exact ⟨Nat.le_of_not_lt hs0, hs⟩
      · by_contra hne
        simp only [cBlocks, hne, ↓reduceIte] at hS'
        have := Finset.mem_range.mp (hbsub0 S' hS')
        omega
  have hc_bsub : ∀ S, cBlocks S ⊆ Finset.range c.length := by
    intro S s hs
    simp only [Finset.mem_range]
    by_cases hST : S = T
    · subst hST
      simp only [cBlocks, ↓reduceIte, Finset.mem_Ico] at hs
      exact hs.2
    · simp only [cBlocks, hST, ↓reduceIte] at hs
      exact lt_of_lt_of_le (Finset.mem_range.mp (hbsub0 S hs)) hq_le_c
  have hc_tile : ∀ s < c.length, ∀ z, c.pivot s = some z → ∀ S, s ∈ cBlocks S → z ∈ cov'.tile S := by
    intro s hs z hpiv S hsS
    by_cases hST : S = T
    · subst hST
      simp only [cBlocks, ↓reduceIte, Finset.mem_Ico] at hsS
      rw [hc_def, extendSeq_length_a3b] at hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hslt | rfl
      · rw [hc_def, extendSeq_pivot_of_lt q b p ξ hslt] at hpiv
        obtain ⟨l, _, hact_l, hpiv_l, _⟩ := inv.trial_step s hsS.1 hslt
        rw [hpiv] at hpiv_l
        injection hpiv_l with hz
        subst hz
        have hmem := hact_l.1
        unfold TS tileSites at hmem
        exact (Finset.mem_filter.mp hmem).2
      · rw [hc_def, extendSeq_pivot_last_a3b q b p ξ] at hpiv
        injection hpiv with hpiv_eq
        subst hpiv_eq
        have hmem := hact.1
        unfold TS tileSites at hmem
        exact (Finset.mem_filter.mp hmem).2
    · simp only [cBlocks, hST, ↓reduceIte] at hsS
      have hs0 : s < x.sweep.length := Finset.mem_range.mp (hbsub0 S hsS)
      have hslt : s < q.length := lt_of_lt_of_le hs0 inv.len_ge
      rw [hc_def, extendSeq_pivot_of_lt q b p ξ hslt, inv.pivot_prefix s hs0] at hpiv
      exact htile0 s hs0 z hpiv S hsS
  have hc_bud : ∀ S : Fin (P.cover j).cover.count, S45.localBudget cov' S (c.Jrecord t r (cBlocks S))
      (c.Lrecord t r (cBlocks S)) (c.lagRecord t r (cBlocks S))
      (c.rowRecord t r Finset.univ (cBlocks S)) (c.rowRecord t r S45.reserves (cBlocks S)) := by
    intro S
    by_cases hST : S = T
    · subst hST
      simp only [cBlocks, ↓reduceIte]
      exact hbud
    · simp only [cBlocks, hST, ↓reduceIte]
      have hsub_q : blocks S ⊆ Finset.range q.length := fun s hs =>
        Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp (hbsub0 S hs)) inv.len_ge)
      obtain ⟨hJ, hL, hlag, hrow⟩ := extendSeq_records_of_subset q b p ξ t r hsub_q
      obtain ⟨hJq, hLq, hlagq, hrowq⟩ := slotSeq_records_of_subset inv t r (hbsub0 S)
      rw [hc_def, hJ, hL, hlag, hrow Finset.univ, hrow S45.reserves,
        hJq, hLq, hlagq, hrowq Finset.univ, hrowq S45.reserves]
      exact hbud0 S
  obtain ⟨Λplus0, Wstar0, hpre0, _⟩ := hx.start_prestate
  have hc_lag0 : ∀ i ∈ (c.state 0).live, (c.state 0).ambientLag t r i = 0 := by
    intro i hi
    rw [hc_state0] at hi ⊢
    simp only [S45.LiveState.ambientLag, dif_pos hi]
    rw [start_state_eq_reindex P j T x hx, reindex_lag _ _ _ hpre0.invertible]
    exact hx.start_lag _
  have hc_row0 : ∀ i ∈ (c.state 0).live,
      ((c.state 0).ambient r).fourthRow t Finset.univ i ≤ 3 / 4 * S45.rowCap t := by
    intro i hi
    rw [hc_state0] at hi ⊢
    have h1 : ((x.sweep.state 0).ambient r).fourthRow t Finset.univ i =
        ((x.sweep.state 0).state r).fourthRow t Finset.univ ⟨i, hi⟩ := by
      simp only [S45.State.fourthRow]
      rw [← Finset.sum_subset (Finset.subset_univ (x.sweep.state 0).live)
        (fun k _ hk => by rw [AgentS45.ambient_h_dead _ r t i hk]; simp),
        ← Finset.sum_coe_sort]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [AgentS45.ambient_h_live _ r t hi k.2]
    rw [h1, start_state_eq_reindex P j T x hx, AgentS45.State.reindex_fourthRow]
    exact hx.start_rows _
  exact hvalid (Port d m) (Torus d m) t (P.cover j).b (P.cover j).dist r S45.reserves
    cov' c cBlocks (stageD0 P j x) htpos htlt hx.cover_b.1 hx.cover_b.2 hshell' hc_wf
    hsym_all hc_blk hc_bsub hc_tile htails hcomp' hc_lag0 hc_row0 hc_bud

end LocalTransferValid

/-! ## Section 6: Prospective trace tails and `tileTransfer_proof` -/

section TraceTailsAndTransfer

open scoped Matrix.Norms.L2Operator BigOperators

lemma ShellBounds_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ} {C : ℝ}
    {dist : ι → ι → ℝ} (e : κ ≃ ι) (hs : S45.ShellBounds d C dist) :
    S45.ShellBounds d C (fun i j => dist (e i) (e j)) := by
  refine ⟨fun i j => hs.nonneg _ _, fun i j => hs.symmetric _ _,
    fun i j k => hs.triangle _ _ _, fun i => hs.self _, ?_, ?_⟩
  · intro u hu hu1 i
    have hsum : (∑ j : κ, Real.exp (-u * dist (e i) (e j))) =
        ∑ j : ι, Real.exp (-u * dist (e i) j) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [hsum]
    exact hs.count u hu hu1 (e i)
  · intro u hu hu1 i
    have hsum : (∑ j : κ, dist (e i) (e j) ^ 2 * Real.exp (-u * dist (e i) (e j))) =
        ∑ j : ι, dist (e i) j ^ 2 * Real.exp (-u * dist (e i) j) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [hsum]
    exact hs.second u hu hu1 (e i)

theorem inverse_row_fintype (d : ℕ) (C ρ β : ℝ) (hC : 1 ≤ C) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hβ : 0 < β) :
    ∃ C' > 0, ∃ c > 0, ∃ t0 > 0, ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (t : ℝ)
      (s : S45.State ι) (dist : ι → ι → ℝ),
      0 < t → t < t0 → S45.ShellBounds d C dist → ‖s.K t‖ ≤ ρ → s.g.IsSymm →
      (∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C) → s.F t *ᵥ s.p = s.q →
      (∀ i, |s.q i - s.p i| ≤ C * S45.power t β) →
      (∀ i j, ‖s.h t i j‖ ≤ C / Real.sqrt t) →
      (∀ i j, C * S45.power t (-2) < dist i j →
        ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C)) →
      IsUnit (1 - s.K t) ∧ (∀ i j, ‖s.P t i j‖ ≤ C' * Real.exp (-c * t ^ 3 * dist i j)) := by
  obtain ⟨C', hC', c, hc, t0, ht0, hfin⟩ := AgentS45.inverse_row_proof d C ρ β hC hρ0 hρ1 hβ
  refine ⟨C', hC', c, hc, t0, ht0, ?_⟩
  intro ι _ _ t s dist ht htt hshell hK hsym hp hward hqp hcrude hfar
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let s' : S45.State (Fin n) := AgentS45.State.reindex e s
  let dist' : Fin n → Fin n → ℝ := fun i j => dist (e i) (e j)
  have hshell' : S45.ShellBounds d C dist' := ShellBounds_reindex e hshell
  have hK' : ‖s'.K t‖ ≤ ρ := by
    change ‖(AgentS45.State.reindex e s).K t‖ ≤ ρ
    rw [AgentS45.State.reindex_K, AgentS45.norm_submatrix_equiv]
    exact hK
  have hsym' : s'.g.IsSymm := reindex_isSymm e s hsym
  have hp' : ∀ i : Fin n, 1 / C ≤ s'.p i ∧ s'.p i ≤ C := fun i => hp (e i)
  have hward' : s'.F t *ᵥ s'.p = s'.q := by
    ext i
    have hi := congrFun hward (e i)
    simp only [Matrix.mulVec, dotProduct, S45.State.F, S45.entryAbsSquare, S45.State.h,
      S45.State.p, S45.State.q, s', AgentS45.State.reindex, Matrix.smul_apply] at hi ⊢
    rw [← hi]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hqp' : ∀ i : Fin n, |s'.q i - s'.p i| ≤ C * S45.power t β := fun i => hqp (e i)
  have hcrude' : ∀ i j : Fin n, ‖s'.h t i j‖ ≤ C / Real.sqrt t := fun i j => hcrude (e i) (e j)
  have hfar' : ∀ i j : Fin n, C * S45.power t (-2) < dist' i j →
      ‖s'.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist' i j / C) :=
    fun i j hij => hfar (e i) (e j) hij
  obtain ⟨hunit', _, hP'⟩ := hfin n t s' dist' ht htt hshell' hK' hsym' hp' hward' hqp' hcrude' hfar'
  have hs_eq : 1 - s.K t = (1 - s'.K t).submatrix e.symm e.symm := by
    ext i j
    simp [s', AgentS45.State.reindex_K, Matrix.sub_apply, Matrix.one_apply]
  have hsub := submatrix_isUnit_and_inv e.symm (1 - s'.K t) hunit'
  rw [← hs_eq] at hsub
  refine ⟨hsub.1, fun i j => ?_⟩
  change ‖(1 - s.K t)⁻¹ i j‖ ≤ _
  rw [hsub.2]
  change ‖s'.P t (e.symm i) (e.symm j)‖ ≤ _
  have hPij := hP' (e.symm i) (e.symm j)
  simpa [dist'] using hPij

private lemma poly_small_power (e ε : ℝ) (he : 0 < e) (hε : 0 < ε) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 → S45.power t e < ε := by
  refine ⟨S45.power ε (1 / e), Real.rpow_pos_of_pos hε _, ?_⟩
  intro t ht hlt
  have hpow : S45.power (S45.power ε (1 / e)) e = ε := by
    dsimp [S45.power]
    rw [← Real.rpow_mul hε.le]
    have hexp : (1 / e) * e = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  exact (Real.rpow_lt_rpow ht.le hlt he).trans_eq hpow

private lemma poly_sum_subtype_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i : S, f i.val) ≤ ∑ i, f i := by
  rw [← Finset.sum_subtype S (by intro i; rfl) f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hf i)

private lemma poly_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : S45.CMat ι) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R) (i x : ι) :
    ∑ j, ‖h i j‖ * ‖h x j‖ ≤ R := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖h i j‖) (fun j => ‖h x j‖)
  have hi := hrow i
  have hx := hrow x
  have hprod : (∑ j, ‖h i j‖ ^ 2) * (∑ j, ‖h x j‖ ^ 2) ≤ R ^ 2 := by
    simpa [pow_two] using mul_le_mul hi hx (Finset.sum_nonneg fun j _ => sq_nonneg _) hR
  exact (sq_le_sq₀ (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hR).mp
    (hcs.trans hprod)

private lemma poly_h_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : S45.State ι) (x : ι) (ξ : ℝ) (ht : 0 < t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    ∀ i j : S45.survivors x, (S45.deleteState t s x ξ).h t i j =
      s.h t i.val j.val - S45.gamma t s x ξ * s.h t i.val x * s.h t x j.val := by
  intro i j
  have hsqrt : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  change (Real.sqrt t : ℂ) *
    (s.g i.val j.val - ((ξ : ℂ) + t * s.r x) * s.g i.val x * s.g x j.val /
      (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)) =
    (Real.sqrt t : ℂ) * s.g i.val j.val -
      (((ξ : ℂ) + t * s.r x) /
        ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + t * s.r x) * s.g x x))) *
        ((Real.sqrt t : ℂ) * s.g i.val x) * ((Real.sqrt t : ℂ) * s.g x j.val)
  field_simp [hden, hsqrt]

private lemma poly_gamma {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t G : ℝ) (s : S45.State ι) (x : ι) (ξ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hG : 1 ≤ G) (hsmall : Real.sqrt t < (4 * G ^ 2)⁻¹)
    (hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ G) (hξ : |ξ| ≤ G * Real.sqrt t) :
    (1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧ ‖S45.gamma t s x ξ‖ ≤ 4 * G := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrt1 : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht1
  have hη : |ξ / Real.sqrt t| ≤ G := by
    rw [abs_div, abs_of_pos hsqrt, div_le_iff₀ hsqrt]
    exact hξ
  have hηeq : Real.sqrt t * (ξ / Real.sqrt t) = ξ := by field_simp
  have hb := AgentS45.gamma_pointwise_bounds G t (Real.sqrt t) (ξ / Real.sqrt t) ξ s x hG ht
    hsqrt hsqrt1 hsmall (Real.sq_sqrt ht.le) hηeq hη hstate
  exact ⟨hb.1, hb.2.1⟩

private lemma poly_entry_small {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : S45.State ι) (ht : 0 < t) (ht1 : t ≤ 1)
    (hrow : ∀ i, s.fourthRow t Finset.univ i ≤ S45.rowCap t) :
    ∀ i j, ‖s.h t i j‖ ≤ S45.power t (1 / 4) := by
  intro i j
  have hfour : ‖s.h t i j‖ ^ 4 ≤ S45.rowCap t :=
    (Finset.single_le_sum (fun k _ => pow_nonneg (norm_nonneg _) 4)
      (Finset.mem_univ j)).trans (hrow i)
  have hcap : S45.rowCap t ≤ t := by
    calc
      S45.rowCap t = S45.power t (1 + S45.delta) := rfl
      _ ≤ S45.power t 1 := Real.rpow_le_rpow_of_exponent_ge ht ht1
        (by norm_num [S45.delta])
      _ = t := Real.rpow_one _
  have hv : 0 ≤ S45.power t (1 / 4) := Real.rpow_nonneg ht.le _
  have hpow : (S45.power t (1 / 4)) ^ 4 = t := by
    dsimp [S45.power]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hle : ‖s.h t i j‖ ^ 4 ≤ (S45.power t (1 / 4)) ^ 4 := by rw [hpow]; exact hfour.trans hcap
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hv (by norm_num : (4 : ℕ) ≠ 0)).mp hle

private lemma poly_sqrt_cap {t : ℝ} (ht : 0 < t) :
    Real.sqrt (S45.rowCap t) / Real.sqrt t = S45.power t (S45.delta / 2) := by
  have hrowpos : 0 < S45.rowCap t := Real.rpow_pos_of_pos ht _
  have hrowExp : t ^ (1 + S45.delta) / t = t ^ S45.delta := by
    calc
      t ^ (1 + S45.delta) / t = t ^ (1 + S45.delta) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((1 + S45.delta) - 1) := (Real.rpow_sub ht (1 + S45.delta) 1).symm
      _ = t ^ S45.delta := by congr 1; ring
  have hleftsq : (Real.sqrt (S45.rowCap t) / Real.sqrt t) ^ 2 = S45.power t S45.delta := by
    rw [div_pow, Real.sq_sqrt hrowpos.le, Real.sq_sqrt ht.le, S45.rowCap, S45.power]
    exact hrowExp
  have hrightsq : S45.power t (S45.delta / 2) ^ 2 = S45.power t S45.delta := by
    dsimp [S45.power]
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hleftpos : 0 < Real.sqrt (S45.rowCap t) / Real.sqrt t := by positivity
  have hrightpos : 0 < S45.power t (S45.delta / 2) := Real.rpow_pos_of_pos ht _
  nlinarith

private lemma poly_K_delta_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : S45.State ι) (x : ι) (ξ G : ℝ) (_hG : 0 ≤ G)
    (hγ : ‖S45.gamma t s x ξ‖ ≤ G)
    (hupdate : ∀ i j : S45.survivors x, (S45.deleteState t s x ξ).h t i j =
      s.h t i.val j.val - S45.gamma t s x ξ * s.h t i.val x * s.h t x j.val) :
    ∀ i j : S45.survivors x,
      ‖(S45.deleteState t s x ξ).K t i j - s.K t i.val j.val‖ ≤
        2 * G * ‖s.h t i.val x‖ * ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖ +
          G ^ 2 * ‖s.h t i.val x‖ ^ 2 * ‖s.h t x j.val‖ ^ 2 := by
  intro i j
  change ‖((S45.deleteState t s x ξ).h t i j) ^ 2 - (s.h t i.val j.val) ^ 2‖ ≤ _
  rw [hupdate]
  have heq : (s.h t i.val j.val - S45.gamma t s x ξ * s.h t i.val x * s.h t x j.val) ^ 2 -
      (s.h t i.val j.val) ^ 2 =
      -2 * S45.gamma t s x ξ * s.h t i.val x * s.h t i.val j.val * s.h t x j.val +
        (S45.gamma t s x ξ) ^ 2 * (s.h t i.val x) ^ 2 * (s.h t x j.val) ^ 2 := by ring
  rw [heq]
  calc
    ‖_ + _‖ ≤ ‖-2 * S45.gamma t s x ξ * s.h t i.val x * s.h t i.val j.val * s.h t x j.val‖ +
        ‖(S45.gamma t s x ξ) ^ 2 * (s.h t i.val x) ^ 2 * (s.h t x j.val) ^ 2‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul, norm_pow, norm_neg]
      norm_num
      gcongr

private lemma poly_K_delta_sums {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : S45.State ι) (x : ι) (ξ G R v : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hγ : ‖S45.gamma t s x ξ‖ ≤ G) (hsymm : s.g.IsSymm)
    (hrow : ∀ i, ∑ j, ‖s.h t i j‖ ^ 2 ≤ R) (hentry : ∀ i j, ‖s.h t i j‖ ≤ v)
    (hupdate : ∀ i j : S45.survivors x, (S45.deleteState t s x ξ).h t i j =
      s.h t i.val j.val - S45.gamma t s x ξ * s.h t i.val x * s.h t x j.val) :
    (∀ i : S45.survivors x, ∑ j : S45.survivors x,
      ‖(S45.deleteState t s x ξ).K t i j - s.K t i.val j.val‖ ≤ (2 * G + G ^ 2) * R * v) ∧
    (∀ j : S45.survivors x, ∑ i : S45.survivors x,
      ‖(S45.deleteState t s x ξ).K t i j - s.K t i.val j.val‖ ≤ (2 * G + G ^ 2) * R * v) := by
  classical
  have hprod (i : S45.survivors x) : (∑ j : S45.survivors x,
      ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖) ≤ R :=
    (poly_sum_subtype_le (S45.survivors x) _ (fun j => by positivity)).trans
      (poly_row_product (s.h t) R hR hrow i.val x)
  have hxsum : (∑ j : S45.survivors x, ‖s.h t x j.val‖ ^ 2) ≤ R :=
    (poly_sum_subtype_le (S45.survivors x) _ (fun j => sq_nonneg _)).trans (hrow x)
  have hrowDelta (i : S45.survivors x) : (∑ j : S45.survivors x,
      ‖(S45.deleteState t s x ξ).K t i j - s.K t i.val j.val‖) ≤ (2 * G + G ^ 2) * R * v := by
    have hi := hentry i.val x
    have hi2 : ‖s.h t i.val x‖ ^ 2 ≤ v := by
      have hiSq : ‖s.h t i.val x‖ ^ 2 ≤ v ^ 2 := (sq_le_sq₀ (norm_nonneg _) hv).2 hi
      nlinarith [mul_nonneg hv (sub_nonneg.mpr hv1)]
    calc
      (∑ j : S45.survivors x, ‖(S45.deleteState t s x ξ).K t i j - s.K t i.val j.val‖) ≤
          ∑ j : S45.survivors x, (2 * G * ‖s.h t i.val x‖ * ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖ +
            G ^ 2 * ‖s.h t i.val x‖ ^ 2 * ‖s.h t x j.val‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => poly_K_delta_entry t s x ξ G hG hγ hupdate i j
      _ = 2 * G * ‖s.h t i.val x‖ *
          (∑ j : S45.survivors x, ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖) +
          G ^ 2 * ‖s.h t i.val x‖ ^ 2 * (∑ j : S45.survivors x, ‖s.h t x j.val‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ 2 * G * v * R + G ^ 2 * v * R := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hi (by positivity)) (hprod i)
            (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hi2 (sq_nonneg G)) hxsum
            (Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
      _ = (2 * G + G ^ 2) * R * v := by ring
  have hnewSym := deleteState_isSymm t s x ξ hsymm
  have hdeltaSym (i j : S45.survivors x) :
      (S45.deleteState t s x ξ).K t i j - s.K t i.val j.val =
        (S45.deleteState t s x ξ).K t j i - s.K t j.val i.val := by
    simp only [S45.State.K, S45.entrywiseSquare, AndersonAC.Blueprint.entrywiseSquare,
      S45.State.h, Matrix.smul_apply, smul_eq_mul]
    rw [hnewSym.apply i j, hsymm.apply i.val j.val]
  refine ⟨hrowDelta, ?_⟩
  intro j
  calc
    (∑ i : S45.survivors x, ‖(S45.deleteState t s x ξ).K t i j - s.K t i.val j.val‖) =
        ∑ i : S45.survivors x, ‖(S45.deleteState t s x ξ).K t j i - s.K t j.val i.val‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdeltaSym]
    _ ≤ _ := hrowDelta j

private lemma poly_restrict_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : S45.CMat ι) (S : Finset ι) : ‖S45.restrict A S‖ ≤ ‖A‖ := by
  classical
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro y
  let v : ι → ℂ := fun i => if hi : i ∈ S then y.ofLp ⟨i, hi⟩ else 0
  let z : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hz : ‖z‖ = ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖v i‖ ^ 2) = ∑ i : S, ‖y.ofLp i‖ ^ 2
    have hout : (∑ i ∈ S, ‖v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp [v, hi]
    calc
      (∑ i, ‖v i‖ ^ 2) = ∑ i ∈ S, ‖v i‖ ^ 2 := hout.symm
      _ = ∑ i : S, ‖v i.val‖ ^ 2 := Finset.sum_subtype S (by intro i; rfl) _
      _ = ∑ i : S, ‖y.ofLp i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [v, i.property]
  have hrestrict (i : S) :
      (Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) (S45.restrict A S) y).ofLp i =
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A z).ofLp i.val := by
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
    change (∑ j : S, A i.val j.val * y.ofLp j) = ∑ j, A i.val j * v j
    have hout : (∑ j ∈ S, A i.val j * v j) = ∑ j, A i.val j * v j := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      simp [v, hj]
    calc
      (∑ j : S, A i.val j.val * y.ofLp j) = ∑ j : S, A i.val j.val * v j.val := by
        apply Finset.sum_congr rfl
        intro j _
        simp [v, j.property]
      _ = ∑ j ∈ S, A i.val j * v j :=
        (Finset.sum_subtype S (by intro j; rfl) (fun j => A i.val j * v j)).symm
      _ = ∑ j, A i.val j * v j := hout
  have hproj : ‖Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) (S45.restrict A S) y‖ ≤
      ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hh : (∑ i : S, ‖(Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) (S45.restrict A S) y).ofLp i‖ ^ 2) =
        ∑ i : S, ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A z).ofLp i.val‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrestrict]
    rw [hh]
    exact poly_sum_subtype_le S (fun i => ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A z).ofLp i‖ ^ 2)
      (fun i => sq_nonneg _)
  calc
    ‖Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) (S45.restrict A S) y‖ ≤
        ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A z‖ := hproj
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖ * ‖z‖ :=
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm z
    _ = ‖A‖ * ‖y‖ := by
      have hnorm : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖ = ‖A‖ :=
        (Matrix.l2_opNorm_toEuclideanCLM A).symm
      rw [hz, hnorm]

private lemma poly_diag_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : S45.State ι) (ht : 0 < t) (ht1 : t ≤ 1)
    (hsym : s.g.IsSymm) (hrow : ∀ i, s.fourthRow t Finset.univ i ≤ S45.rowCap t)
    (x : ι) (ξ G : ℝ) (hγ : ‖S45.gamma t s x ξ‖ ≤ G) (hG : 0 ≤ G)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    ∀ i : S45.survivors x, ‖(S45.deleteState t s x ξ).g i i - s.g i.val i.val‖ ≤ G * S45.power t S45.beta := by
  intro i
  have hroot := Real.sqrt_pos.2 ht
  have hupdate := poly_h_update t s x ξ ht hden i i
  have hscale : (Real.sqrt t : ℂ) *
      ((S45.deleteState t s x ξ).g i i - s.g i.val i.val) =
      -S45.gamma t s x ξ * s.h t i.val x * s.h t x i.val := by
    change (Real.sqrt t : ℂ) * (S45.deleteState t s x ξ).g i i =
      (Real.sqrt t : ℂ) * s.g i.val i.val -
        S45.gamma t s x ξ * s.h t i.val x * s.h t x i.val at hupdate
    linear_combination hupdate
  have hsmall : ‖s.h t i.val x‖ ^ 2 ≤ Real.sqrt (S45.rowCap t) := by
    have hfour : ‖s.h t i.val x‖ ^ 4 ≤ S45.rowCap t :=
      (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 4)
        (Finset.mem_univ x)).trans (hrow i.val)
    have hrootSq : Real.sqrt (S45.rowCap t) ^ 2 = S45.rowCap t :=
      Real.sq_sqrt (Real.rpow_nonneg ht.le _)
    nlinarith [Real.sqrt_nonneg (S45.rowCap t), sq_nonneg ‖s.h t i.val x‖]
  have hnorm : Real.sqrt t * ‖(S45.deleteState t s x ξ).g i i - s.g i.val i.val‖ ≤
      G * Real.sqrt (S45.rowCap t) := by
    have heq := congrArg norm hscale
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hroot] at heq
    have hsymm_h : s.h t x i.val = s.h t i.val x := by simp [S45.State.h, hsym.apply]
    rw [hsymm_h] at heq
    rw [heq]
    calc
      ‖S45.gamma t s x ξ‖ * ‖s.h t i.val x‖ * ‖s.h t i.val x‖ =
          ‖S45.gamma t s x ξ‖ * ‖s.h t i.val x‖ ^ 2 := by ring
      _ ≤ G * Real.sqrt (S45.rowCap t) := mul_le_mul hγ hsmall (sq_nonneg _) hG
  calc
    ‖(S45.deleteState t s x ξ).g i i - s.g i.val i.val‖ ≤ G * Real.sqrt (S45.rowCap t) / Real.sqrt t :=
      (le_div_iff₀ hroot).2 (by simpa [mul_comm] using hnorm)
    _ = G * S45.power t (S45.delta / 2) := by rw [mul_div_assoc, poly_sqrt_cap ht]
    _ ≤ G * S45.power t S45.beta := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num [S45.beta, S45.delta])) hG

private lemma poly_power_mul {t : ℝ} (ht : 0 < t) (e f : ℝ) :
    S45.power t e * S45.power t f = S45.power t (e + f) := (Real.rpow_add ht e f).symm

private lemma poly_power_pow {t : ℝ} (ht : 0 < t) (e : ℝ) (k : ℕ) :
    S45.power t e ^ k = S45.power t (e * (k : ℝ)) := by
  dsimp [S45.power]
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]

private lemma poly_mono {t e f : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hef : e ≤ f) : S45.power t (-e) ≤ S45.power t (-f) :=
  Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)

private lemma poly_exp_mono {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) :
    Real.exp (-b * r) ≤ Real.exp (-a * r) := Real.exp_le_exp.mpr (by nlinarith)

private lemma poly_shell_subtype {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    {C : ℝ} {dist : ι → ι → ℝ} (hs : S45.ShellBounds d C dist) (S : Finset ι) :
    S45.ShellBounds d C (fun i j : S => dist i.val j.val) := by
  refine ⟨fun i j => hs.nonneg _ _, fun i j => hs.symmetric _ _,
    fun i j k => hs.triangle _ _ _, fun i => hs.self _, ?_, ?_⟩
  · intro u hu hu1 i
    exact (poly_sum_subtype_le S _ (fun j => Real.exp_nonneg _)).trans (hs.count u hu hu1 i.val)
  · intro u hu hu1 i
    exact (poly_sum_subtype_le S _ (fun j => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))).trans
      (hs.second u hu hu1 i.val)

private lemma poly_shell_poly {ι : Type*} [Fintype ι] {d : ℕ}
    {C : ℝ} {dist : ι → ι → ℝ} (hs : S45.ShellBounds d C dist)
    {t c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1) (i : ι) :
    ∑ j, Real.exp (-c * t ^ 3 * dist i j) ≤
      (C * S45.power c (-(d : ℝ))) * S45.power t (-3 * (d : ℝ)) := by
  have hu : 0 < c * t ^ 3 := by positivity
  have hu1 : c * t ^ 3 ≤ 1 := by
    have ht3 : t ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ ht.le ht1 3
    nlinarith
  have hpower : S45.power (c * t ^ 3) (-(d : ℝ)) =
      S45.power c (-(d : ℝ)) * S45.power t (-3 * (d : ℝ)) := by
    dsimp [S45.power]
    rw [Real.mul_rpow hc.le (by positivity : 0 ≤ t ^ 3), ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le]
    congr 2
    ring
  have hh := hs.count (c * t ^ 3) hu hu1 i
  have hsum : (∑ j, Real.exp (-(c * t ^ 3) * dist i j)) =
      ∑ j, Real.exp (-c * t ^ 3 * dist i j) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  rw [hsum, hpower] at hh
  simpa [mul_assoc] using hh

private lemma poly_convolution_sum {ι : Type*} [Fintype ι] {d : ℕ}
    {C : ℝ} {dist : ι → ι → ℝ} (hs : S45.ShellBounds d C dist)
    {t c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1) (i x : ι) :
    ∑ j, Real.exp (-(2 * c) * t ^ 3 * dist i j) *
      Real.exp (-(2 * c) * t ^ 3 * dist j x) ≤
      Real.exp (-c * t ^ 3 * dist i x) *
        ((C * S45.power c (-(d : ℝ))) * S45.power t (-3 * (d : ℝ))) := by
  have hcu : 0 ≤ c * t ^ 3 := by positivity
  have hterm (j : ι) : Real.exp (-(2 * c) * t ^ 3 * dist i j) *
      Real.exp (-(2 * c) * t ^ 3 * dist j x) ≤
        Real.exp (-c * t ^ 3 * dist i x) * Real.exp (-c * t ^ 3 * dist i j) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htri := hs.triangle i j x
    have hn := hs.nonneg j x
    nlinarith
  calc
    _ ≤ ∑ j, Real.exp (-c * t ^ 3 * dist i x) * Real.exp (-c * t ^ 3 * dist i j) :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = Real.exp (-c * t ^ 3 * dist i x) * (∑ j, Real.exp (-c * t ^ 3 * dist i j)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (poly_shell_poly hs ht ht1 hc hc1 i) (Real.exp_nonneg _)

private lemma poly_quartic_difference (a b : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ‖a‖ ≤ M) (hab : ‖a - b‖ ≤ M) :
    |‖a - b‖ ^ 4 - ‖a‖ ^ 4| ≤ 4 * M ^ 3 * ‖b‖ := by
  have hdiff : |‖a - b‖ - ‖a‖| ≤ ‖b‖ := by
    simpa using abs_norm_sub_norm_le (a - b) a
  have heq : ‖a - b‖ ^ 4 - ‖a‖ ^ 4 =
      (‖a - b‖ - ‖a‖) * (‖a - b‖ + ‖a‖) * (‖a - b‖ ^ 2 + ‖a‖ ^ 2) := by ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a - b‖ + ‖a‖),
    abs_of_nonneg (by positivity : 0 ≤ ‖a - b‖ ^ 2 + ‖a‖ ^ 2)]
  have hsum : ‖a - b‖ + ‖a‖ ≤ 2 * M := by linarith
  have hsq : ‖a - b‖ ^ 2 + ‖a‖ ^ 2 ≤ 2 * M ^ 2 := by
    nlinarith [(sq_le_sq₀ (norm_nonneg _) hM).2 ha, (sq_le_sq₀ (norm_nonneg _) hM).2 hab]
  calc
    _ ≤ ‖b‖ * (2 * M) * (2 * M ^ 2) :=
      mul_le_mul (mul_le_mul hdiff hsum (by positivity) (norm_nonneg _)) hsq
        (by positivity) (by positivity)
    _ = 4 * M ^ 3 * ‖b‖ := by ring

private lemma poly_decay_constant {C B t u r : ℝ} (hC : 0 < C) (hCB : C ≤ B)
    (_ht : 0 < t) (hu : 0 ≤ u) (hr : 0 ≤ r) :
    C / Real.sqrt t * Real.exp (-u * r / C) ≤
      B / Real.sqrt t * Real.exp (-u * r / B) := by
  have hB : 0 < B := hC.trans_le hCB
  have hcoeff : C / Real.sqrt t ≤ B / Real.sqrt t := div_le_div_of_nonneg_right hCB (Real.sqrt_nonneg _)
  have hdiv : u * r / B ≤ u * r / C := div_le_div_of_nonneg_left (mul_nonneg hu hr) hC hCB
  exact mul_le_mul hcoeff (Real.exp_le_exp.mpr (by
    simpa only [neg_mul, neg_div] using neg_le_neg hdiv)) (Real.exp_nonneg _)
    (div_nonneg hB.le (Real.sqrt_nonneg _))

private lemma poly_two_leg_decay {ι : Type*} [Fintype ι] {d : ℕ}
    (h : S45.CMat ι) (dist : ι → ι → ℝ) {C : ℝ} (hs : S45.ShellBounds d C dist)
    (A a L : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hsmall : ∀ i j, ‖h i j‖ ≤ 1)
    (hdec : ∀ i j, L < dist i j → ‖h i j‖ ≤ A * Real.exp (-a * dist i j))
    (i x j : ι) (hij : 2 * L < dist i j) :
    ‖h i x‖ * ‖h x j‖ ≤ A * Real.exp (-(a / 2) * dist i j) := by
  by_cases hix : dist i j / 2 ≤ dist i x
  · have hfar : L < dist i x := by linarith
    have hnorm := hdec i x hfar
    calc
      ‖h i x‖ * ‖h x j‖ ≤ ‖h i x‖ := by simpa using
        (mul_le_mul_of_nonneg_left (hsmall x j) (norm_nonneg (h i x)))
      _ ≤ A * Real.exp (-a * dist i x) := hnorm
      _ ≤ A * Real.exp (-(a / 2) * dist i j) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hA
  · have hxj : dist i j / 2 ≤ dist x j := by
      have hh := hs.triangle i x j
      linarith
    have hfar : L < dist x j := by linarith
    calc
      ‖h i x‖ * ‖h x j‖ ≤ ‖h x j‖ := by simpa using
        (mul_le_mul_of_nonneg_right (hsmall i x) (norm_nonneg (h x j)))
      _ ≤ A * Real.exp (-a * dist x j) := hdec x j hfar
      _ ≤ A * Real.exp (-(a / 2) * dist i j) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hA

private lemma poly_updated_decay {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (t B : ℝ) (s : S45.State ι) (dist : ι → ι → ℝ) (hshell : S45.ShellBounds d B dist)
    (x : ι) (ξ a L G : ℝ) (ht : 0 < t) (hB : 0 < B) (ha : 0 ≤ a) (hG : 0 ≤ G)
    (hγ : ‖S45.gamma t s x ξ‖ ≤ G) (hsmall : ∀ i j, ‖s.h t i j‖ ≤ 1)
    (hdec : ∀ i j, L < dist i j → ‖s.h t i j‖ ≤ B / Real.sqrt t * Real.exp (-a * dist i j))
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (i j : S45.survivors x) (hij : 2 * L < dist i.val j.val) (hdir : L < dist i.val j.val) :
    ‖(S45.deleteState t s x ξ).h t i j‖ ≤
      (1 + G) * (B / Real.sqrt t) * Real.exp (-(a / 2) * dist i.val j.val) := by
  have hprod := poly_two_leg_decay (s.h t) dist hshell (B / Real.sqrt t) a L
    (by positivity) ha hsmall hdec i.val x j.val hij
  have hnorm : ‖s.h t i.val j.val‖ ≤ B / Real.sqrt t * Real.exp (-(a / 2) * dist i.val j.val) :=
    (hdec i.val j.val hdir).trans (mul_le_mul_of_nonneg_left
      (poly_exp_mono (by nlinarith : a / 2 ≤ a) (hshell.nonneg _ _)) (by positivity))
  rw [poly_h_update t s x ξ ht hden]
  calc
    ‖s.h t i.val j.val - S45.gamma t s x ξ * s.h t i.val x * s.h t x j.val‖ ≤
        ‖s.h t i.val j.val‖ + ‖S45.gamma t s x ξ * s.h t i.val x * s.h t x j.val‖ := norm_sub_le _ _
    _ ≤ B / Real.sqrt t * Real.exp (-(a / 2) * dist i.val j.val) +
        G * (B / Real.sqrt t * Real.exp (-(a / 2) * dist i.val j.val)) := by
      apply add_le_add hnorm
      simp only [norm_mul]
      calc
        ‖S45.gamma t s x ξ‖ * ‖s.h t i.val x‖ * ‖s.h t x j.val‖ =
            ‖S45.gamma t s x ξ‖ * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) := by ring
        _ ≤ _ := mul_le_mul hγ hprod (by positivity) hG
    _ = _ := by ring

private lemma poly_sqrt_inv_le {t B : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hB : 0 ≤ B) : B / Real.sqrt t ≤ B * S45.power t (-1) := by
  have hsqrt_le_one : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht1
  have htsqrt : t ≤ Real.sqrt t := by
    have hmul := Real.mul_self_sqrt ht.le
    have hle : Real.sqrt t * Real.sqrt t ≤ Real.sqrt t * 1 :=
      mul_le_mul_of_nonneg_left hsqrt_le_one (Real.sqrt_nonneg _)
    rw [hmul] at hle
    simpa using hle
  have hdiv : 1 / Real.sqrt t ≤ 1 / t := one_div_le_one_div_of_le ht htsqrt
  have hdiv' : (Real.sqrt t)⁻¹ ≤ t⁻¹ := by simpa [one_div] using hdiv
  have hpow_inv : S45.power t (-1) = t⁻¹ := by
    dsimp [S45.power]
    rw [Real.rpow_neg ht.le, Real.rpow_one]
  rw [hpow_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hdiv' hB

private lemma poly_K_le_h {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℝ} {s : S45.State ι}
    (hsmall : ∀ a b, ‖s.h t a b‖ ≤ 1) (a b : ι) :
    ‖s.K t a b‖ ≤ ‖s.h t a b‖ ∧ s.F t a b ≤ ‖s.h t a b‖ := by
  have h1 : ‖s.h t a b‖ ≤ 1 := hsmall a b
  have hnn : 0 ≤ ‖s.h t a b‖ := norm_nonneg _
  have hsq : ‖s.h t a b‖ ^ 2 ≤ ‖s.h t a b‖ := by nlinarith
  have hK : ‖s.K t a b‖ = ‖s.h t a b‖ ^ 2 := by
    change ‖(s.h t a b) ^ 2‖ = ‖s.h t a b‖ ^ 2
    exact norm_pow _ 2
  have hF : s.F t a b = ‖s.h t a b‖ ^ 2 := rfl
  exact ⟨hK.trans_le hsq, hF.trans_le hsq⟩

private lemma poly_Jinc_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {t G : ℝ}
    {s : S45.State ι} {x : ι} {ξ : ℝ} (hG : 0 ≤ G)
    (hsmall : ∀ a b, ‖s.h t a b‖ ≤ 1)
    (hγ : ‖S45.gamma t s x ξ‖ ≤ G)
    (hKinv : ‖(1 - s.K t x x)⁻¹‖ ≤ 4) (i j : ι) :
    ‖S45.Jinc t s x ξ i j‖ ≤
      (2 * G + G ^ 2 + 4) * (‖s.h t i x‖ * ‖s.h t x j‖) := by
  classical
  by_cases hi : i ∈ S45.survivors x
  · by_cases hj : j ∈ S45.survivors x
    · have hJeq : S45.Jinc t s x ξ i j =
          -2 * S45.gamma t s x ξ * s.h t i x * s.h t i j * s.h t x j +
            ((S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) * s.K t i x * s.K t x j := by
        simp [S45.Jinc, S45.pad, hi, hj]
      rw [hJeq]
      have hKix := (poly_K_le_h hsmall i x).1
      have hKxj := (poly_K_le_h hsmall x j).1
      have hhij := hsmall i j
      have hfirst : ‖-2 * S45.gamma t s x ξ * s.h t i x * s.h t i j * s.h t x j‖ ≤
          2 * G * (‖s.h t i x‖ * ‖s.h t x j‖) := by
        simp only [norm_mul, norm_neg, Complex.norm_ofNat]
        have h1 : ‖S45.gamma t s x ξ‖ * ‖s.h t i x‖ * ‖s.h t i j‖ * ‖s.h t x j‖ ≤
            G * ‖s.h t i x‖ * 1 * ‖s.h t x j‖ := by
          gcongr
        nlinarith
      have hsecond : ‖((S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) * s.K t i x * s.K t x j‖ ≤
          (G ^ 2 + 4) * (‖s.h t i x‖ * ‖s.h t x j‖) := by
        simp only [norm_mul]
        have hcoeff : ‖(S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹‖ ≤ G ^ 2 + 4 := by
          calc
            ‖(S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹‖ ≤
                ‖(S45.gamma t s x ξ) ^ 2‖ + ‖(1 - s.K t x x)⁻¹‖ := norm_sub_le _ _
            _ ≤ G ^ 2 + 4 := by
              rw [norm_pow]
              exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hγ 2) hKinv
        have hprod : ‖s.K t i x‖ * ‖s.K t x j‖ ≤ ‖s.h t i x‖ * ‖s.h t x j‖ :=
          mul_le_mul hKix hKxj (norm_nonneg _) (norm_nonneg _)
        calc
          ‖(S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹‖ * ‖s.K t i x‖ * ‖s.K t x j‖ =
              ‖(S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹‖ * (‖s.K t i x‖ * ‖s.K t x j‖) := by ring
          _ ≤ (G ^ 2 + 4) * (‖s.h t i x‖ * ‖s.h t x j‖) :=
            mul_le_mul hcoeff hprod (by positivity) (by positivity)
      calc
        ‖-2 * S45.gamma t s x ξ * s.h t i x * s.h t i j * s.h t x j +
            ((S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) * s.K t i x * s.K t x j‖ ≤
            ‖-2 * S45.gamma t s x ξ * s.h t i x * s.h t i j * s.h t x j‖ +
              ‖((S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) * s.K t i x * s.K t x j‖ :=
          norm_add_le _ _
        _ ≤ 2 * G * (‖s.h t i x‖ * ‖s.h t x j‖) +
            (G ^ 2 + 4) * (‖s.h t i x‖ * ‖s.h t x j‖) := add_le_add hfirst hsecond
        _ = (2 * G + G ^ 2 + 4) * (‖s.h t i x‖ * ‖s.h t x j‖) := by ring
    · have hJeq : S45.Jinc t s x ξ i j = 0 := by simp [S45.Jinc, S45.pad, hi, hj]
      rw [hJeq, norm_zero]
      positivity
  · have hJeq : S45.Jinc t s x ξ i j = 0 := by simp [S45.Jinc, S45.pad, hi]
    rw [hJeq, norm_zero]
    positivity

private lemma poly_Ledge_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {t B G P0 : ℝ}
    {s : S45.State ι} {x : ι} {ξ : ℝ} (hB : 0 ≤ B) (hG : 0 ≤ G) (hP0 : 0 ≤ P0)
    (hsmall : ∀ a b, ‖s.h t a b‖ ≤ 1)
    (hγ : ‖S45.gamma t s x ξ‖ ≤ G)
    (hpivot : |s.p x / (s.q x - s.p x * s.F t x x)| ≤ P0)
    (i j : S45.survivors x) (hpi : |s.p i.val| ≤ B) (hpj : |s.p j.val| ≤ B) :
    |S45.Ledge t s x ξ i j| ≤
      B ^ 2 * (2 * G + G ^ 2 + P0) * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) := by
  have hFix := (poly_K_le_h hsmall i.val x).2
  have hFxj := (poly_K_le_h hsmall x j.val).2
  have hhij := hsmall i.val j.val
  have hFnn (a b : ι) : 0 ≤ s.F t a b := by simp [S45.State.F, S45.entryAbsSquare]
  have hLdef : S45.Ledge t s x ξ i j = (s.p i.val * s.p j.val) *
      ((-2 * (S45.gamma t s x ξ * star (s.h t i.val j.val) * s.h t i.val x *
        s.h t x j.val).re) +
        ((‖S45.gamma t s x ξ‖ ^ 2 - s.p x / (s.q x - s.p x * s.F t x x)) *
          (s.F t i.val x * s.F t x j.val))) := by
    dsimp [S45.Ledge]
    ring_nf
  rw [hLdef, abs_mul]
  have hpij : |s.p i.val * s.p j.val| ≤ B ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hpi hpj (abs_nonneg _) hB).trans_eq (by ring)
  have hfirst : |-2 * (S45.gamma t s x ξ * star (s.h t i.val j.val) * s.h t i.val x *
      s.h t x j.val).re| ≤ 2 * G * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hre : |(S45.gamma t s x ξ * star (s.h t i.val j.val) * s.h t i.val x *
        s.h t x j.val).re| ≤ G * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) := by
      calc
        |(S45.gamma t s x ξ * star (s.h t i.val j.val) * s.h t i.val x *
            s.h t x j.val).re| ≤
            ‖S45.gamma t s x ξ * star (s.h t i.val j.val) * s.h t i.val x * s.h t x j.val‖ :=
          Complex.abs_re_le_norm _
        _ = ‖S45.gamma t s x ξ‖ * ‖s.h t i.val j.val‖ * ‖s.h t i.val x‖ * ‖s.h t x j.val‖ := by
          simp only [norm_mul, norm_star]
        _ ≤ G * 1 * ‖s.h t i.val x‖ * ‖s.h t x j.val‖ := by gcongr
        _ = G * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) := by ring
    nlinarith
  have hsecond : |(‖S45.gamma t s x ξ‖ ^ 2 - s.p x / (s.q x - s.p x * s.F t x x)) *
      (s.F t i.val x * s.F t x j.val)| ≤
      (G ^ 2 + P0) * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hFnn _ _) (hFnn _ _))]
    have hcoeff : |‖S45.gamma t s x ξ‖ ^ 2 - s.p x / (s.q x - s.p x * s.F t x x)| ≤ G ^ 2 + P0 := by
      have h1 : ‖S45.gamma t s x ξ‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hγ 2
      have h2 := abs_le.mp hpivot
      rw [abs_le]
      constructor <;> linarith [sq_nonneg ‖S45.gamma t s x ξ‖]
    have hFprod : s.F t i.val x * s.F t x j.val ≤ ‖s.h t i.val x‖ * ‖s.h t x j.val‖ :=
      mul_le_mul hFix hFxj (hFnn _ _) (norm_nonneg _)
    exact mul_le_mul hcoeff hFprod (mul_nonneg (hFnn _ _) (hFnn _ _)) (by positivity)
  have hsum := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  calc
    |s.p i.val * s.p j.val| *
        |(-2 * (S45.gamma t s x ξ * star (s.h t i.val j.val) * s.h t i.val x *
          s.h t x j.val).re) +
          ((‖S45.gamma t s x ξ‖ ^ 2 - s.p x / (s.q x - s.p x * s.F t x x)) *
            (s.F t i.val x * s.F t x j.val))| ≤
        B ^ 2 * (2 * G * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) +
          (G ^ 2 + P0) * (‖s.h t i.val x‖ * ‖s.h t x j.val‖)) :=
      mul_le_mul hpij hsum (abs_nonneg _) (sq_nonneg _)
    _ = B ^ 2 * (2 * G + G ^ 2 + P0) * (‖s.h t i.val x‖ * ‖s.h t x j.val‖) := by ring

private lemma poly_two_factor_exp {ι : Type*} [Fintype ι] [DecidableEq ι] {t B : ℝ}
    {s : S45.State ι} {dist : ι → ι → ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hB : 0 < B)
    (hsym : ∀ a b, dist a b = dist b a)
    (hdec : ∀ i j, ‖s.h t i j‖ ≤ B / Real.sqrt t * Real.exp (-t ^ 3 * dist i j / B))
    (i x j : ι) :
    ‖s.h t i x‖ * ‖s.h t x j‖ ≤
      B ^ 2 * S45.power t (-2) * Real.exp (-t ^ 3 * (dist i x + dist j x) / B) := by
  have hBsimp : B / Real.sqrt t ≤ B * S45.power t (-1) := poly_sqrt_inv_le ht ht1 hB.le
  have hBpow : 0 ≤ B * S45.power t (-1) := mul_nonneg hB.le (Real.rpow_nonneg ht.le _)
  have hhdec (a b : ι) : ‖s.h t a b‖ ≤
      (B * S45.power t (-1)) * Real.exp (-t ^ 3 * dist a b / B) :=
    (hdec a b).trans (mul_le_mul_of_nonneg_right hBsimp (Real.exp_nonneg _))
  have h1 := hhdec i x
  have h2 : ‖s.h t x j‖ ≤ (B * S45.power t (-1)) * Real.exp (-t ^ 3 * dist j x / B) := by
    have hh := hhdec x j; rwa [hsym x j] at hh
  have hexp : Real.exp (-t ^ 3 * dist i x / B) * Real.exp (-t ^ 3 * dist j x / B) =
      Real.exp (-t ^ 3 * (dist i x + dist j x) / B) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpow12 : S45.power t (-1 : ℝ) * S45.power t (-1 : ℝ) = S45.power t (-2 : ℝ) := by
    rw [poly_power_mul ht]; congr 1; ring
  calc
    ‖s.h t i x‖ * ‖s.h t x j‖ ≤
        ((B * S45.power t (-1)) * Real.exp (-t ^ 3 * dist i x / B)) *
          ((B * S45.power t (-1)) * Real.exp (-t ^ 3 * dist j x / B)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hBpow (Real.exp_nonneg _))
    _ = B ^ 2 * (S45.power t (-1) * S45.power t (-1)) *
        (Real.exp (-t ^ 3 * dist i x / B) * Real.exp (-t ^ 3 * dist j x / B)) := by ring
    _ = B ^ 2 * S45.power t (-2) * Real.exp (-t ^ 3 * (dist i x + dist j x) / B) := by
      rw [hpow12, hexp]

private lemma absorb_const_into_power {t A E C_tail : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (_hA : 0 ≤ A) (htA : t ≤ 1 / (1 + A)) (hEC : E + 1 ≤ C_tail) :
    A * S45.power t (-E) ≤ S45.power t (-C_tail) := by
  have h1A : 0 < 1 + A := by linarith
  have hAt : A ≤ S45.power t (-1) := by
    have hpow : S45.power t (-1) = t⁻¹ := by
      dsimp [S45.power]; rw [Real.rpow_neg ht.le, Real.rpow_one]
    rw [hpow, ← one_div]
    have hle : 1 + A ≤ 1 / t := (le_div_iff₀ ht).mpr (by
      have := (le_div_iff₀ h1A).mp htA; linarith)
    linarith
  calc A * S45.power t (-E)
      ≤ S45.power t (-1) * S45.power t (-E) :=
        mul_le_mul_of_nonneg_right hAt (Real.rpow_nonneg ht.le _)
    _ = S45.power t (-(E + 1)) := by
        rw [poly_power_mul ht]; congr 1; ring
    _ ≤ S45.power t (-C_tail) := poly_mono ht ht1 hEC

set_option maxHeartbeats 1600000 in
theorem step_delete_inverse_decay (d : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    let B : ℝ := 2 * (1 + C ^ 2)
    let G : ℝ := 12 * B
    ∃ Ri > 0, ∃ c_inv > 0, ∃ t0 > 0, t0 ≤ 1 ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (t : ℝ)
        (s : S45.State ι) (dist : ι → ι → ℝ) (x : ι) (ξ : ℝ),
        0 < t → t < t0 → S45.ShellBounds d C dist →
        s.g.IsSymm → s.ward t →
        (∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C) →
        (∀ i, ‖s.r i‖ ≤ C) →
        ‖s.K t‖ ≤ 3 / 4 →
        (∀ i, ‖s.rawLag i‖ ≤ B * S45.power t S45.beta) →
        (∀ i, s.fourthRow t Finset.univ i ≤ S45.rowCap t) →
        (∀ i j, ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t ^ 3 * dist i j / C)) →
        (∀ i j, C * S45.power t (-2) < dist i j →
          ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C)) →
        |ξ| ≤ 2 * C * Real.sqrt t →
        (1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧
        ‖S45.gamma t s x ξ‖ ≤ G ∧
        IsUnit (1 - (S45.deleteState t s x ξ).K t) ∧
        (∀ i j : S45.survivors x,
          ‖(S45.deleteState t s x ξ).P t i j‖ ≤
            Ri * Real.exp (-c_inv * t ^ 3 * dist i.val j.val)) := by
  intro B G
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hCB : C ≤ B := by dsimp [B]; nlinarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hGpos : 0 < G := by dsimp [G]; positivity
  let R_row_F : ℝ := 2 * B ^ 2
  let A_schur : ℝ := (2 * G + G ^ 2) * R_row_F
  let M_dec : ℝ := (1 + G) * B
  let D0 : ℝ := 1 + M_dec + 2 * B + (G + B)
  have hMpos : 0 < M_dec := by dsimp [M_dec, G]; positivity
  have hD0 : 1 ≤ D0 := by dsimp [D0]; linarith
  have hMD0 : M_dec ≤ D0 := by dsimp [D0]; linarith
  have h2BD0 : 2 * B ≤ D0 := by dsimp [D0]; linarith
  have hBD0 : B ≤ D0 := by linarith
  have hGBD0 : G + B ≤ D0 := by dsimp [D0]; linarith
  have hM2B : 2 * B ≤ M_dec := by dsimp [M_dec, G]; nlinarith
  obtain ⟨Ri, hRi, c_inv, hc_inv, ti, hti, hinv⟩ :=
    inverse_row_fintype d D0 (7 / 8) S45.beta hD0 (by norm_num) (by norm_num)
      (by norm_num [S45.beta, S45.delta])
  obtain ⟨tg, htg, hg⟩ := poly_small_power (1 / 2) ((4 * (3 * B) ^ 2)⁻¹)
    (by norm_num) (by positivity)
  have hApos : 0 < A_schur := by dsimp [A_schur, R_row_F, G]; positivity
  obtain ⟨tk, htk, hk⟩ := poly_small_power (1 / 4) (1 / (8 * A_schur))
    (by norm_num) (by positivity)
  let t0 := min 1 (min ti (min tg tk))
  have ht0pos : 0 < t0 := lt_min one_pos (lt_min hti (lt_min htg htk))
  have ht0le : t0 ≤ 1 := min_le_left _ _
  refine ⟨Ri, hRi, c_inv, hc_inv, t0, ht0pos, ht0le, ?_⟩
  intro ι _ _ t s dist x ξ ht htt hshell hsym hward hp hr hK hraw hrow hweak hfar hξ
  have ht1 : t ≤ 1 := htt.le.trans ht0le
  have htti : t < ti := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have httg : t < tg := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have httk : t < tk := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpowβ : 0 ≤ S45.power t S45.beta := Real.rpow_nonneg ht.le _
  have hpowβ1 : S45.power t S45.beta ≤ 1 :=
    Real.rpow_le_one ht.le ht1 (by norm_num [S45.beta, S45.delta])
  have hqp (i : ι) : |s.q i - s.p i| ≤ B * S45.power t S45.beta := by
    have him : s.q i - s.p i = (s.rawLag i).im := by
      simp [S45.State.q, S45.State.p, S45.State.rawLag]
    rw [him]
    exact (Complex.abs_im_le_norm _).trans (hraw i)
  have hrows (i : ι) : ∑ j, ‖s.h t i j‖ ^ 2 ≤ R_row_F := by
    have hdiag := AgentS45.ward_diag_row t s hward i
    have hqi : s.q i ≤ 2 * B := by
      have h1 := (abs_le.mp (hqp i)).2
      have h2 : s.p i ≤ B := (hp i).2.trans hCB
      nlinarith
    calc (∑ j, ‖s.h t i j‖ ^ 2)
        ≤ ∑ j, B * (s.p j * ‖s.h t i j‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro j _
          have hpj : 1 / B ≤ s.p j :=
            (one_div_le_one_div_of_le hCpos hCB).trans (hp j).1
          have h1 : 1 ≤ s.p j * B := (div_le_iff₀ hBpos).mp hpj
          nlinarith [sq_nonneg ‖s.h t i j‖]
      _ = B * (∑ j, s.p j * ‖s.h t i j‖ ^ 2) := (Finset.mul_sum _ _ _).symm
      _ = B * s.q i := by rw [hdiag]
      _ ≤ R_row_F := by dsimp [R_row_F]; nlinarith
  have hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ 3 * B := by
    have hrx : ‖s.r x‖ ≤ B := (hr x).trans hCB
    have hrawB : ‖s.rawLag x‖ ≤ B := (hraw x).trans (by nlinarith)
    have htri : ‖s.g x x‖ ≤ ‖s.r x‖ + ‖s.rawLag x‖ := by
      have heq : s.g x x = s.r x + s.rawLag x := by simp [S45.State.rawLag]
      rw [heq]; exact norm_add_le _ _
    linarith
  have hrootSmall : Real.sqrt t < (4 * (3 * B) ^ 2)⁻¹ := by
    simpa [S45.power, Real.sqrt_eq_rpow] using hg t ht httg
  have hξB : |ξ| ≤ (3 * B) * Real.sqrt t := hξ.trans
    (mul_le_mul_of_nonneg_right (by linarith : 2 * C ≤ 3 * B) (Real.sqrt_nonneg t))
  obtain ⟨hden, hgamma⟩ := poly_gamma t (3 * B) s x ξ ht ht1 (by linarith)
    hrootSmall hstate hξB
  have hγ : ‖S45.gamma t s x ξ‖ ≤ G := by dsimp [G]; linarith
  have hupdate := poly_h_update t s x ξ ht hden
  have hentry := poly_entry_small t s ht ht1 hrow
  have hv : 0 ≤ S45.power t (1 / 4) := Real.rpow_nonneg ht.le _
  have hv1 : S45.power t (1 / 4) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hsums := poly_K_delta_sums t s x ξ G R_row_F (S45.power t (1 / 4))
    (by dsimp [G]; positivity) (by dsimp [R_row_F]; positivity) hv hv1 hγ hsym hrows hentry hupdate
  have hδ : ‖(S45.deleteState t s x ξ).K t - S45.restrict (s.K t) (S45.survivors x)‖ ≤ 1 / 8 := by
    have hscale : A_schur * S45.power t (1 / 4) ≤ 1 / 8 := by
      have hlt := (lt_div_iff₀ (by positivity : 0 < 8 * A_schur)).mp (hk t ht httk)
      nlinarith
    calc
      ‖(S45.deleteState t s x ξ).K t - S45.restrict (s.K t) (S45.survivors x)‖ ≤
          Real.sqrt ((A_schur * S45.power t (1 / 4)) * (A_schur * S45.power t (1 / 4))) :=
        AgentS45.norm_le_schur_test _ _ _ (by positivity) (by positivity) hsums.1 hsums.2
      _ = A_schur * S45.power t (1 / 4) := Real.sqrt_mul_self (by positivity)
      _ ≤ 1 / 8 := hscale
  have hcap : ‖(S45.deleteState t s x ξ).K t‖ ≤ 7 / 8 := by
    have htri : ‖(S45.deleteState t s x ξ).K t‖ ≤
        ‖S45.restrict (s.K t) (S45.survivors x)‖ +
          ‖(S45.deleteState t s x ξ).K t - S45.restrict (s.K t) (S45.survivors x)‖ := by
      simpa using norm_add_le (S45.restrict (s.K t) (S45.survivors x))
        ((S45.deleteState t s x ξ).K t - S45.restrict (s.K t) (S45.survivors x))
    calc
      ‖(S45.deleteState t s x ξ).K t‖ ≤ ‖s.K t‖ + 1 / 8 :=
        htri.trans (add_le_add (poly_restrict_norm _ _) hδ)
      _ ≤ 7 / 8 := by linarith
  have hnew_sym : (S45.deleteState t s x ξ).g.IsSymm := deleteState_isSymm t s x ξ hsym
  have hnew_ward : (S45.deleteState t s x ξ).ward t :=
    deleteState_ward t s x ξ ht hsym hward hden
  have hnew_ward_vec : (S45.deleteState t s x ξ).F t *ᵥ (S45.deleteState t s x ξ).p =
      (S45.deleteState t s x ξ).q := by
    ext i
    simpa [S45.State.F, S45.entryAbsSquare, Matrix.mulVec, dotProduct, mul_comm] using
      AgentS45.ward_diag_row t (S45.deleteState t s x ξ) hnew_ward i
  have hnew_qp (i : S45.survivors x) :
      |(S45.deleteState t s x ξ).q i - (S45.deleteState t s x ξ).p i| ≤
        D0 * S45.power t S45.beta := by
    have hchange := poly_diag_change t s ht ht1 hsym hrow x ξ G hγ (by dsimp [G]; positivity) hden i
    have htriangle : |(S45.deleteState t s x ξ).q i - (S45.deleteState t s x ξ).p i| ≤
        ‖(S45.deleteState t s x ξ).g i i - s.g i.val i.val‖ + |s.q i.val - s.p i.val| := by
      have heq : (S45.deleteState t s x ξ).q i - (S45.deleteState t s x ξ).p i =
          ((S45.deleteState t s x ξ).g i i - s.g i.val i.val).im + (s.q i.val - s.p i.val) := by
        simp [S45.State.q, S45.State.p, S45.deleteState]; ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add (Complex.abs_im_le_norm _) (le_refl _))
    calc
      |(S45.deleteState t s x ξ).q i - (S45.deleteState t s x ξ).p i| ≤
          (G + B) * S45.power t S45.beta := by
        have hsum := htriangle.trans (add_le_add hchange (hqp i.val))
        linarith
      _ ≤ D0 * S45.power t S45.beta := mul_le_mul_of_nonneg_right hGBD0 hpowβ
  have hbShell := ShellBounds_mono hshell hCB
  have hweakB (i j : ι) : ‖s.h t i j‖ ≤
      B / Real.sqrt t * Real.exp (-t ^ 3 * dist i j / B) := (hweak i j).trans
    (poly_decay_constant hCpos hCB ht (by positivity) (hshell.nonneg i j))
  have hfarB (i j : ι) (hij : B * S45.power t (-2) < dist i j) :
      ‖s.h t i j‖ ≤ B / Real.sqrt t * Real.exp (-t * dist i j / B) := by
    have hh : C * S45.power t (-2) < dist i j := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg ht.le _)) hij
    exact (hfar i j hh).trans (poly_decay_constant hCpos hCB ht ht.le (hshell.nonneg i j))
  have hsmall (i j : ι) : ‖s.h t i j‖ ≤ 1 := (hentry i j).trans hv1
  have hweakNew (i j : S45.survivors x) : ‖(S45.deleteState t s x ξ).h t i j‖ ≤
      M_dec / Real.sqrt t * Real.exp (-(1 / (2 * B)) * t ^ 3 * dist i.val j.val) := by
    have hh := poly_updated_decay t B s dist hbShell x ξ (t ^ 3 / B) (-1) G
      ht hBpos (by positivity) (by dsimp [G]; positivity) hγ hsmall
      (fun a b _ => by simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hweakB a b)
      hden i j (by linarith [hshell.nonneg i.val j.val])
      (by linarith [hshell.nonneg i.val j.val])
    have heq : (t ^ 3 / B) / 2 = (1 / (2 * B)) * t ^ 3 := by field_simp
    simpa [heq, M_dec, mul_div_assoc] using hh
  have hfarNew (i j : S45.survivors x) (hij : 2 * B * S45.power t (-2) < dist i.val j.val) :
      ‖(S45.deleteState t s x ξ).h t i j‖ ≤
        M_dec / Real.sqrt t * Real.exp (-t * dist i.val j.val / (2 * B)) := by
    have hLpos : 0 ≤ B * S45.power t (-2) := mul_nonneg hBpos.le (Real.rpow_nonneg ht.le _)
    have hdir : B * S45.power t (-2) < dist i.val j.val := by linarith
    have hh := poly_updated_decay t B s dist hbShell x ξ (t / B) (B * S45.power t (-2)) G
      ht hBpos (by positivity) (by dsimp [G]; positivity) hγ hsmall
      (fun a b hab => by simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hfarB a b hab)
      hden i j (by simpa [mul_assoc] using hij) hdir
    have hexp : (-(t / B / 2)) * dist i.val j.val = -t * dist i.val j.val / (2 * B) := by
      have hBne : B ≠ 0 := ne_of_gt hBpos; field_simp
    rw [hexp] at hh
    simpa [M_dec, mul_div_assoc] using hh
  have hfarD0 (i j : S45.survivors x) (hij : D0 * S45.power t (-2) < dist i.val j.val) :
      ‖(S45.deleteState t s x ξ).h t i j‖ ≤
        D0 / Real.sqrt t * Real.exp (-t * dist i.val j.val / D0) := by
    have hh := hfarNew i j (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right h2BD0 (Real.rpow_nonneg ht.le _)) hij)
    have hdiv : t * dist i.val j.val / M_dec ≤ t * dist i.val j.val / (2 * B) :=
      div_le_div_of_nonneg_left (mul_nonneg ht.le (hshell.nonneg _ _)) (by positivity) hM2B
    calc
      _ ≤ M_dec / Real.sqrt t * Real.exp (-t * dist i.val j.val / (2 * B)) := hh
      _ ≤ M_dec / Real.sqrt t * Real.exp (-t * dist i.val j.val / M_dec) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          simpa only [neg_mul, neg_div] using neg_le_neg hdiv)) (by positivity)
      _ ≤ D0 / Real.sqrt t * Real.exp (-t * dist i.val j.val / D0) :=
        poly_decay_constant hMpos hMD0 ht ht.le (hshell.nonneg _ _)
  have hcrude (i j : S45.survivors x) : ‖(S45.deleteState t s x ξ).h t i j‖ ≤ D0 / Real.sqrt t := by
    calc
      _ ≤ M_dec / Real.sqrt t * Real.exp (-(1 / (2 * B)) * t ^ 3 * dist i.val j.val) := hweakNew i j
      _ ≤ M_dec / Real.sqrt t := by
        have he : Real.exp (-(1 / (2 * B)) * t ^ 3 * dist i.val j.val) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have hnon := hshell.nonneg i.val j.val
          have hpos : 0 ≤ (1 / (2 * B)) * t ^ 3 * dist i.val j.val := by positivity
          linarith
        simpa using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ M_dec / Real.sqrt t)
      _ ≤ D0 / Real.sqrt t := div_le_div_of_nonneg_right hMD0 (Real.sqrt_nonneg _)
  have hpD0 (i : S45.survivors x) : 1 / D0 ≤ (S45.deleteState t s x ξ).p i ∧
      (S45.deleteState t s x ξ).p i ≤ D0 := by
    change 1 / D0 ≤ s.p i.val ∧ s.p i.val ≤ D0
    have hCD0 : C ≤ D0 := hCB.trans hBD0
    exact ⟨(one_div_le_one_div_of_le hCpos hCD0).trans (hp i.val).1,
      (hp i.val).2.trans hCD0⟩
  have hsSub := poly_shell_subtype (ShellBounds_mono hshell (hCB.trans hBD0)) (S45.survivors x)
  obtain ⟨hnew_unit, hnew_P⟩ := hinv (S45.survivors x) t (S45.deleteState t s x ξ)
    (fun i j => dist i.val j.val) ht htti hsSub hcap hnew_sym hpD0 hnew_ward_vec
    hnew_qp hcrude hfarD0
  exact ⟨hden, hγ, hnew_unit, hnew_P⟩

private lemma norm_inv_one_sub_le_four (z : ℂ) (hz : ‖z‖ ≤ 3 / 4) : ‖(1 - z)⁻¹‖ ≤ 4 := by
  have htri : (1 : ℝ) ≤ ‖1 - z‖ + ‖z‖ := by
    have h1 : (1 : ℂ) = (1 - z) + z := by ring
    have h2 := norm_add_le (1 - z) z
    rw [← h1, norm_one] at h2
    exact h2
  have hlow : 1 / 4 ≤ ‖1 - z‖ := by linarith
  rw [norm_inv, ← one_div]
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hlow
  linarith

private lemma amb_h_apply {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (a : S45.LiveState P_port) (r : P_port → ℂ) (t : ℝ) (i j : P_port) :
    (a.ambient r).h t i j =
      if hi : i ∈ a.live then if hj : j ∈ a.live then
        (a.state r).h t ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := by
  by_cases hi : i ∈ a.live <;> by_cases hj : j ∈ a.live <;>
    simp [S45.LiveState.ambient, S45.LiveState.state, S45.State.h, S45.mask, S45.pad,
      S45.restrict, hi, hj]

private lemma amb_h_norm_le {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (a : S45.LiveState P_port) (r : P_port → ℂ) (t : ℝ) (M : P_port → P_port → ℝ)
    (hM0 : ∀ i j, 0 ≤ M i j)
    (hsk : ∀ i j : a.live, ‖(a.state r).h t i j‖ ≤ M i.val j.val) (i j : P_port) :
    ‖(a.ambient r).h t i j‖ ≤ M i j := by
  rw [amb_h_apply]
  by_cases hi : i ∈ a.live
  · by_cases hj : j ∈ a.live
    · simp only [hi, hj, ↓reduceDIte]
      exact hsk ⟨i, hi⟩ ⟨j, hj⟩
    · simp only [hi, hj, ↓reduceDIte, norm_zero]
      exact hM0 i j
  · simp only [hi, ↓reduceDIte, norm_zero]
    exact hM0 i j

private lemma amb_at_pivot {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (a : S45.LiveState P_port) (r : P_port → ℂ) (t : ℝ) {x : P_port} (hx : x ∈ a.live) (ξ : ℝ) :
    let x_live : a.live := ⟨x, hx⟩
    (a.ambient r).g x x = (a.state r).g x_live x_live ∧
    (a.ambient r).r x = (a.state r).r x_live ∧
    (a.ambient r).p x = (a.state r).p x_live ∧
    (a.ambient r).q x = (a.state r).q x_live ∧
    (a.ambient r).K t x x = (a.state r).K t x_live x_live ∧
    (a.ambient r).F t x x = (a.state r).F t x_live x_live ∧
    S45.gamma t (a.ambient r) x ξ = S45.gamma t (a.state r) x_live ξ := by
  intro x_live
  have hg : (a.ambient r).g x x = (a.state r).g x_live x_live := by
    simp [S45.LiveState.ambient, S45.LiveState.state, S45.mask, S45.pad, S45.restrict, hx, x_live]
  have hr : (a.ambient r).r x = (a.state r).r x_live := rfl
  have hp : (a.ambient r).p x = (a.state r).p x_live := rfl
  have hq : (a.ambient r).q x = (a.state r).q x_live := by
    simp [S45.State.q, hg]
  have hh : (a.ambient r).h t x x = (a.state r).h t x_live x_live := by
    simp [S45.State.h, hg]
  have hK : (a.ambient r).K t x x = (a.state r).K t x_live x_live := by
    change ((a.ambient r).h t x x) ^ 2 = ((a.state r).h t x_live x_live) ^ 2
    rw [hh]
  have hF : (a.ambient r).F t x x = (a.state r).F t x_live x_live := by
    change ‖(a.ambient r).h t x x‖ ^ 2 = ‖(a.state r).h t x_live x_live‖ ^ 2
    rw [hh]
  have hγ : S45.gamma t (a.ambient r) x ξ = S45.gamma t (a.state r) x_live ξ := by
    simp [S45.gamma, hg, hr]
  exact ⟨hg, hr, hp, hq, hK, hF, hγ⟩

private lemma stepRel_amb_h_update {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    {t : ℝ} {r : P_port → ℂ} {a b : S45.LiveState P_port} {x : P_port} {ξ : ℝ}
    (ht : 0 < t) (ha_wf : a.g = S45.mask a.live a.g) (hrel : S45.StepRel t r a b x ξ)
    {i j : P_port} (hi : i ∈ b.live) (hj : j ∈ b.live) :
    (b.ambient r).h t i j =
      (a.ambient r).h t i j -
        S45.gamma t (a.ambient r) x ξ * (a.ambient r).h t i x * (a.ambient r).h t x j := by
  have hi_s : i ∈ S45.survivors x := by
    have hi' : i ∈ a.live.erase x := hrel.survivors ▸ hi
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hi', Finset.mem_univ i⟩
  have hj_s : j ∈ S45.survivors x := by
    have hj' : j ∈ a.live.erase x := hrel.survivors ▸ hj
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hj', Finset.mem_univ j⟩
  have hamb_g : (a.ambient r).g = a.g := ha_wf.symm
  have hden_amb : 1 + ((ξ : ℂ) + t * (a.ambient r).r x) * (a.ambient r).g x x ≠ 0 := by
    rw [hamb_g]; exact hrel.denominator
  have hg_eq : (b.ambient r).g i j = (S45.deleteState t (a.ambient r) x ξ).g ⟨i, hi_s⟩ ⟨j, hj_s⟩ := by
    have h1 : (b.ambient r).g i j = b.g i j := by
      simp [S45.LiveState.ambient, S45.mask, S45.pad, S45.restrict, Matrix.submatrix_apply, hi, hj]
    have h2 := congrFun (congrFun hrel.update i) j
    have h3 : S45.mask b.live (fun u v => a.g u v -
        ((ξ : ℂ) + t * r x) * a.g u x * a.g x v /
          (1 + ((ξ : ℂ) + t * r x) * a.g x x)) i j =
        a.g i j - ((ξ : ℂ) + t * r x) * a.g i x * a.g x j /
          (1 + ((ξ : ℂ) + t * r x) * a.g x x) := by
      simp [S45.mask, S45.pad, S45.restrict, hi, hj]; rfl
    rw [h1, h2, h3]
    dsimp [S45.deleteState, S45.LiveState.ambient]
    rw [← ha_wf]
  have hh_eq : (b.ambient r).h t i j =
      (S45.deleteState t (a.ambient r) x ξ).h t ⟨i, hi_s⟩ ⟨j, hj_s⟩ := by
    change (Real.sqrt t : ℂ) * (b.ambient r).g i j =
      (Real.sqrt t : ℂ) * (S45.deleteState t (a.ambient r) x ξ).g ⟨i, hi_s⟩ ⟨j, hj_s⟩
    rw [hg_eq]
  rw [hh_eq]
  exact poly_h_update t (a.ambient r) x ξ ht hden_amb ⟨i, hi_s⟩ ⟨j, hj_s⟩

private lemma poly_row_step_bound {P_port : Type*} [Fintype P_port] [DecidableEq P_port] {d : ℕ}
    {q : S45.Sequence P_port} {t B G c : ℝ} {r : P_port → ℂ} {dist : P_port → P_port → ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hB : 0 < B) (hG : 0 ≤ G)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcB : c ≤ 1 / B)
    (hshell : S45.ShellBounds d B dist)
    {k : ℕ} {x : P_port}
    (ha_wf : (q.state k).g = S45.mask (q.state k).live (q.state k).g)
    (hrel : S45.StepRel t r (q.state k) (q.state (k + 1)) x (q.scalar k))
    (hsmall : ∀ u v, ‖((q.state k).ambient r).h t u v‖ ≤ 1)
    (hdec : ∀ u v, ‖((q.state k).ambient r).h t u v‖ ≤
      B / Real.sqrt t * Real.exp (-t ^ 3 * dist u v / B))
    (hγ : ‖S45.gamma t ((q.state k).ambient r) x (q.scalar k)‖ ≤ G)
    (cols : Finset P_port) (i : P_port) :
    |q.stepRow t r cols k i| ≤
      (4 * (1 + G) ^ 3 * G * B ^ 3 * S45.power c (-(d : ℝ))) *
        S45.power t (-(4 + 3 * (d : ℝ))) * Real.exp (-c * t ^ 3 * dist i x) := by
  classical
  let a := q.state k
  let b := q.state (k + 1)
  let ξ := q.scalar k
  let amb := a.ambient r
  let amb1 := b.ambient r
  have hBsimp : B / Real.sqrt t ≤ B * S45.power t (-1) := poly_sqrt_inv_le ht ht1 hB.le
  have hhdec (u v : P_port) : ‖amb.h t u v‖ ≤
      (B * S45.power t (-1)) * Real.exp (-c * t ^ 3 * dist u v) := by
    have hexp_uv : Real.exp (-t ^ 3 * dist u v / B) ≤ Real.exp (-c * t ^ 3 * dist u v) := by
      apply Real.exp_le_exp.mpr
      have h1 : c * (t ^ 3 * dist u v) ≤ (1 / B) * (t ^ 3 * dist u v) :=
        mul_le_mul_of_nonneg_right hcB (mul_nonneg (by positivity : 0 ≤ t ^ 3) (hshell.nonneg u v))
      have h2 : -t ^ 3 * dist u v / B = -((1 / B) * (t ^ 3 * dist u v)) := by ring
      have h3 : -c * t ^ 3 * dist u v = -(c * (t ^ 3 * dist u v)) := by ring
      linarith
    exact (hdec u v).trans (mul_le_mul hBsimp hexp_uv (Real.exp_nonneg _)
      (mul_nonneg hB.le (Real.rpow_nonneg ht.le _)))
  by_cases hi : i ∈ b.live
  · have hstep_eq : q.stepRow t r cols k i =
        (∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)) / S45.rowCap t := by
      simp [S45.Sequence.stepRow, b, amb, amb1, a, hi]
    have hcap_pos : 0 < S45.rowCap t := Real.rpow_pos_of_pos ht _
    rw [hstep_eq, abs_div, abs_of_pos hcap_pos]
    have hterm (j : P_port) (hj_mem : j ∈ cols ∩ b.live) :
        |‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4| ≤
          4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ := by
      have hj : j ∈ b.live := (Finset.mem_inter.mp hj_mem).2
      have hupd := stepRel_amb_h_update ht ha_wf hrel hi hj
      change amb1.h t i j = amb.h t i j - S45.gamma t amb x ξ * amb.h t i x * amb.h t x j at hupd
      let d_ij := S45.gamma t amb x ξ * amb.h t i x * amb.h t x j
      have hd_norm : ‖d_ij‖ ≤ G * (‖amb.h t i x‖ * ‖amb.h t x j‖) := by
        dsimp [d_ij]
        rw [norm_mul, norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right hγ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have hd_le_G : ‖d_ij‖ ≤ G := by
        have hprod1 : ‖amb.h t i x‖ * ‖amb.h t x j‖ ≤ 1 := by
          have := mul_le_mul (hsmall i x) (hsmall x j) (norm_nonneg _) zero_le_one
          linarith
        nlinarith
      have ha_le : ‖amb.h t i j‖ ≤ 1 + G := by linarith [hsmall i j]
      have hab_le : ‖amb.h t i j - d_ij‖ ≤ 1 + G :=
        (norm_sub_le _ _).trans (by linarith [hsmall i j, hd_le_G])
      have hq := poly_quartic_difference (amb.h t i j) d_ij (1 + G) (by positivity) ha_le hab_le
      rw [← hupd] at hq
      exact hq.trans (by
        calc 4 * (1 + G) ^ 3 * ‖d_ij‖
            ≤ 4 * (1 + G) ^ 3 * (G * (‖amb.h t i x‖ * ‖amb.h t x j‖)) :=
              mul_le_mul_of_nonneg_left hd_norm (by positivity)
          _ = 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ := by ring)
    have hsum_le : |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)| ≤
        4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * (∑ j : P_port, ‖amb.h t x j‖) := by
      calc |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)|
          ≤ ∑ j ∈ cols ∩ b.live, |‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ cols ∩ b.live, 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ j : P_port, 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * ‖amb.h t x j‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * (∑ j : P_port, ‖amb.h t x j‖) := by
            rw [← Finset.mul_sum]
    have hsum_xj : (∑ j : P_port, ‖amb.h t x j‖) ≤
        (B * S45.power t (-1)) * ((B * S45.power c (-(d : ℝ))) * S45.power t (-3 * (d : ℝ))) := by
      calc (∑ j : P_port, ‖amb.h t x j‖)
          ≤ ∑ j : P_port, (B * S45.power t (-1)) * Real.exp (-c * t ^ 3 * dist x j) :=
            Finset.sum_le_sum fun j _ => hhdec x j
        _ = (B * S45.power t (-1)) * (∑ j : P_port, Real.exp (-c * t ^ 3 * dist x j)) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (poly_shell_poly hshell ht ht1 hc hc1 x)
            (mul_nonneg hB.le (Real.rpow_nonneg ht.le _))
    have hcap_inv : 1 / S45.rowCap t ≤ S45.power t (-2) := by
      have h1 : 1 / S45.rowCap t = S45.power t (-(1 + S45.delta)) := by
        dsimp [S45.rowCap, S45.power]
        rw [one_div, ← Real.rpow_neg ht.le]
      rw [h1]
      exact poly_mono ht ht1 (by norm_num [S45.delta])
    have hpow_comb : S45.power t (-1) * S45.power t (-1) * S45.power t (-3 * (d : ℝ)) *
        S45.power t (-2) = S45.power t (-(4 + 3 * (d : ℝ))) := by
      rw [poly_power_mul ht, poly_power_mul ht, poly_power_mul ht]
      congr 1; ring
    have hnum : |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)| ≤
        (4 * (1 + G) ^ 3 * G * B ^ 3 * S45.power c (-(d : ℝ))) *
          (S45.power t (-1) * S45.power t (-1) * S45.power t (-3 * (d : ℝ))) *
          Real.exp (-c * t ^ 3 * dist i x) := by
      calc |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)|
          ≤ 4 * (1 + G) ^ 3 * G * ‖amb.h t i x‖ * (∑ j : P_port, ‖amb.h t x j‖) := hsum_le
        _ ≤ (4 * (1 + G) ^ 3 * G * ((B * S45.power t (-1)) * Real.exp (-c * t ^ 3 * dist i x))) *
            ((B * S45.power t (-1)) * ((B * S45.power c (-(d : ℝ))) * S45.power t (-3 * (d : ℝ)))) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (hhdec i x) (by positivity))
            hsum_xj
            (Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (by dsimp [S45.power]; positivity)
        _ = _ := by ring
    rw [div_eq_mul_one_div]
    calc |∑ j ∈ cols ∩ b.live, (‖amb1.h t i j‖ ^ 4 - ‖amb.h t i j‖ ^ 4)| * (1 / S45.rowCap t)
        ≤ ((4 * (1 + G) ^ 3 * G * B ^ 3 * S45.power c (-(d : ℝ))) *
            (S45.power t (-1) * S45.power t (-1) * S45.power t (-3 * (d : ℝ))) *
            Real.exp (-c * t ^ 3 * dist i x)) * S45.power t (-2) :=
          mul_le_mul hnum hcap_inv (by dsimp [S45.rowCap, S45.power]; positivity)
            (by dsimp [S45.power]; positivity)
      _ = (4 * (1 + G) ^ 3 * G * B ^ 3 * S45.power c (-(d : ℝ))) *
          (S45.power t (-1) * S45.power t (-1) * S45.power t (-3 * (d : ℝ)) * S45.power t (-2)) *
          Real.exp (-c * t ^ 3 * dist i x) := by ring
      _ = _ := by rw [hpow_comb]
  · simp [S45.Sequence.stepRow, b, hi]
    dsimp [S45.power]; positivity

set_option maxHeartbeats 1200000 in
private lemma poly_lagInc_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    {t B G Ri c_inv c : ℝ} {s : S45.State ι} {dist : ι → ι → ℝ} {x : ι} {ξ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hB : 1 ≤ B) (hG : 0 ≤ G) (hRi : 0 < Ri)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcB : 2 * c ≤ 1 / B) (hcinv : 2 * c ≤ c_inv)
    (hshell : S45.ShellBounds d B dist)
    (hsym : s.g.IsSymm) (hA : IsUnit (1 - s.K t)) (ha : 1 - s.K t x x ≠ 0)
    (hKinv : ‖(1 - s.K t x x)⁻¹‖ ≤ 4)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hγ : ‖S45.gamma t s x ξ‖ ≤ G)
    (hraw : ‖s.rawLag x‖ ≤ B)
    (hlag : ∀ l : ι, ‖s.lag t l‖ ≤ 1)
    (hsmall : ∀ a b : ι, ‖s.h t a b‖ ≤ 1)
    (hdec : ∀ a b : ι, ‖s.h t a b‖ ≤ B / Real.sqrt t * Real.exp (-t ^ 3 * dist a b / B))
    (hnew_unit : IsUnit (1 - (S45.deleteState t s x ξ).K t))
    (hnew_P : ∀ u v : S45.survivors x,
      ‖(S45.deleteState t s x ξ).P t u v‖ ≤ Ri * Real.exp (-c_inv * t ^ 3 * dist u.val v.val))
    (i : ι) :
    ‖S45.lagInc t s x ξ i‖ ≤
      (Ri * ((G + 4 * B) * B + (2 * G + G ^ 2 + 4) * B ^ 3 * S45.power c (-(d : ℝ))) *
        (B * S45.power c (-(d : ℝ)))) *
        S45.power t (-(3 + 6 * (d : ℝ))) * Real.exp (-c * t ^ 3 * dist i x) := by
  classical
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let A_f : ℝ := (G + 4 * B) * B + (2 * G + G ^ 2 + 4) * B ^ 3 * S45.power c (-(d : ℝ))
  have hAf_nn : 0 ≤ A_f := by dsimp [A_f, S45.power]; positivity
  by_cases hi : i ∈ S45.survivors x
  · have hexact := AgentS45.lag_exact_proof t s x ξ ht hsym hA ha hden hnew_unit i hi
    have hBsimp : B / Real.sqrt t ≤ B * S45.power t (-1) := poly_sqrt_inv_le ht ht1 hBpos.le
    have hU_norm (l : ι) : ‖s.U t l‖ ≤ 1 := by
      have hUeq : s.U t l = (Real.sqrt t : ℂ) * s.lag t l := by
        have h := congrFun (show s.U t = (Real.sqrt t : ℂ) • s.lag t from by
          ext u; simp [S45.State.U, S45.State.z, S45.State.lag, S45.State.P, Matrix.mulVec_smul]) l
        simpa [Pi.smul_apply, smul_eq_mul] using h
      rw [hUeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
      exact (mul_le_mul (Real.sqrt_le_one.mpr ht1) (hlag l) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
    have hforc (j : S45.survivors x) :
        ‖S45.forcing t s x ξ j.val‖ ≤
          A_f * S45.power t (-(2 + 3 * (d : ℝ))) * Real.exp (-(2 * c) * t ^ 3 * dist j.val x) := by
      have hjx : j.val ≠ x := (Finset.mem_erase.mp j.2).1
      have hfeq : S45.forcing t s x ξ j.val =
          -(S45.gamma t s x ξ + s.z t x / (1 - s.K t x x)) * s.K t j.val x +
            (S45.Jinc t s x ξ *ᵥ s.U t) j.val := by
        simp [S45.forcing, hjx]
      rw [hfeq]
      have hz_norm : ‖s.z t x‖ ≤ B := by
        change ‖(Real.sqrt t : ℂ) * s.rawLag x‖ ≤ B
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
        exact (mul_le_mul (Real.sqrt_le_one.mpr ht1) hraw (norm_nonneg _) zero_le_one).trans_eq
          (one_mul B)
      have hcoeff1 : ‖-(S45.gamma t s x ξ + s.z t x / (1 - s.K t x x))‖ ≤ G + 4 * B := by
        rw [norm_neg]
        refine (norm_add_le _ _).trans (add_le_add hγ ?_)
        rw [div_eq_mul_inv, norm_mul]
        have := mul_le_mul hz_norm hKinv (norm_nonneg _) hBpos.le
        linarith
      have hKjx : ‖s.K t j.val x‖ ≤
          B * S45.power t (-(2 + 3 * (d : ℝ))) * Real.exp (-(2 * c) * t ^ 3 * dist j.val x) := by
        have h1 := (poly_K_le_h hsmall j.val x).1.trans (hdec j.val x)
        have hexp1 : Real.exp (-t ^ 3 * dist j.val x / B) ≤
            Real.exp (-(2 * c) * t ^ 3 * dist j.val x) := by
          apply Real.exp_le_exp.mpr
          have hle : (2 * c) * (t ^ 3 * dist j.val x) ≤ (1 / B) * (t ^ 3 * dist j.val x) :=
            mul_le_mul_of_nonneg_right hcB (mul_nonneg (by positivity : 0 ≤ t ^ 3) (hshell.nonneg j.val x))
          have heq1 : -t ^ 3 * dist j.val x / B = -((1 / B) * (t ^ 3 * dist j.val x)) := by ring
          have heq2 : -(2 * c) * t ^ 3 * dist j.val x = -((2 * c) * (t ^ 3 * dist j.val x)) := by ring
          linarith
        have hpow1 : S45.power t (-1) ≤ S45.power t (-(2 + 3 * (d : ℝ))) :=
          poly_mono ht ht1 (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
        calc ‖s.K t j.val x‖
            ≤ (B / Real.sqrt t) * Real.exp (-t ^ 3 * dist j.val x / B) := h1
          _ ≤ (B * S45.power t (-1)) * Real.exp (-(2 * c) * t ^ 3 * dist j.val x) :=
              mul_le_mul hBsimp hexp1 (Real.exp_nonneg _) (mul_nonneg hBpos.le (Real.rpow_nonneg ht.le _))
          _ ≤ (B * S45.power t (-(2 + 3 * (d : ℝ)))) * Real.exp (-(2 * c) * t ^ 3 * dist j.val x) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 hBpos.le) (Real.exp_nonneg _)
          _ = _ := by ring
      have hterm1 : ‖-(S45.gamma t s x ξ + s.z t x / (1 - s.K t x x)) * s.K t j.val x‖ ≤
          ((G + 4 * B) * B) * S45.power t (-(2 + 3 * (d : ℝ))) *
            Real.exp (-(2 * c) * t ^ 3 * dist j.val x) := by
        rw [norm_mul]
        exact (mul_le_mul hcoeff1 hKjx (norm_nonneg _) (by positivity)).trans_eq (by ring)
      have hJterm (l : ι) : ‖S45.Jinc t s x ξ j.val l * s.U t l‖ ≤
          (2 * G + G ^ 2 + 4) * B ^ 2 * S45.power t (-2) *
            Real.exp (-(2 * c) * t ^ 3 * dist j.val x) *
            Real.exp (-c * t ^ 3 * dist x l) := by
        rw [norm_mul]
        have hU1 := hU_norm l
        have hJ1 := (poly_Jinc_factor hG hsmall hγ hKinv j.val l).trans
          (mul_le_mul_of_nonneg_left
            (poly_two_factor_exp ht ht1 hBpos hshell.symmetric hdec j.val x l) (by positivity))
        have hexp_split : Real.exp (-t ^ 3 * (dist j.val x + dist l x) / B) ≤
            Real.exp (-(2 * c) * t ^ 3 * dist j.val x) * Real.exp (-c * t ^ 3 * dist x l) := by
          rw [← Real.exp_add, hshell.symmetric x l]
          apply Real.exp_le_exp.mpr
          have hle1 : (2 * c) * (t ^ 3 * dist j.val x) ≤ (1 / B) * (t ^ 3 * dist j.val x) :=
            mul_le_mul_of_nonneg_right hcB (mul_nonneg (by positivity : 0 ≤ t ^ 3) (hshell.nonneg j.val x))
          have hle2 : c * (t ^ 3 * dist l x) ≤ (1 / B) * (t ^ 3 * dist l x) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by positivity : 0 ≤ t ^ 3) (hshell.nonneg l x))
          have heq1 : -t ^ 3 * (dist j.val x + dist l x) / B =
              -((1 / B) * (t ^ 3 * dist j.val x)) + -((1 / B) * (t ^ 3 * dist l x)) := by ring
          have heq2 : -(2 * c) * t ^ 3 * dist j.val x + -c * t ^ 3 * dist l x =
              -((2 * c) * (t ^ 3 * dist j.val x)) + -(c * (t ^ 3 * dist l x)) := by ring
          linarith
        calc ‖S45.Jinc t s x ξ j.val l‖ * ‖s.U t l‖
            ≤ ‖S45.Jinc t s x ξ j.val l‖ * 1 := mul_le_mul_of_nonneg_left hU1 (norm_nonneg _)
          _ = ‖S45.Jinc t s x ξ j.val l‖ := mul_one _
          _ ≤ (2 * G + G ^ 2 + 4) * (B ^ 2 * S45.power t (-2) *
                Real.exp (-t ^ 3 * (dist j.val x + dist l x) / B)) := hJ1
          _ ≤ (2 * G + G ^ 2 + 4) * (B ^ 2 * S45.power t (-2) *
                (Real.exp (-(2 * c) * t ^ 3 * dist j.val x) * Real.exp (-c * t ^ 3 * dist x l))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hexp_split (by dsimp [S45.power]; positivity)) (by positivity)
          _ = _ := by ring
      have hterm2 : ‖(S45.Jinc t s x ξ *ᵥ s.U t) j.val‖ ≤
          ((2 * G + G ^ 2 + 4) * B ^ 3 * S45.power c (-(d : ℝ))) *
            S45.power t (-(2 + 3 * (d : ℝ))) *
            Real.exp (-(2 * c) * t ^ 3 * dist j.val x) := by
        have hpow_comb : S45.power t (-2) * S45.power t (-3 * (d : ℝ)) =
            S45.power t (-(2 + 3 * (d : ℝ))) := by
          rw [poly_power_mul ht]; congr 1; ring
        calc ‖(S45.Jinc t s x ξ *ᵥ s.U t) j.val‖
            = ‖∑ l : ι, S45.Jinc t s x ξ j.val l * s.U t l‖ := rfl
          _ ≤ ∑ l : ι, ‖S45.Jinc t s x ξ j.val l * s.U t l‖ := norm_sum_le _ _
          _ ≤ ∑ l : ι, (2 * G + G ^ 2 + 4) * B ^ 2 * S45.power t (-2) *
                Real.exp (-(2 * c) * t ^ 3 * dist j.val x) *
                Real.exp (-c * t ^ 3 * dist x l) := Finset.sum_le_sum fun l _ => hJterm l
          _ = ((2 * G + G ^ 2 + 4) * B ^ 2 * S45.power t (-2) *
                Real.exp (-(2 * c) * t ^ 3 * dist j.val x)) *
                (∑ l : ι, Real.exp (-c * t ^ 3 * dist x l)) := (Finset.mul_sum _ _ _).symm
          _ ≤ ((2 * G + G ^ 2 + 4) * B ^ 2 * S45.power t (-2) *
                Real.exp (-(2 * c) * t ^ 3 * dist j.val x)) *
                ((B * S45.power c (-(d : ℝ))) * S45.power t (-3 * (d : ℝ))) :=
              mul_le_mul_of_nonneg_left (poly_shell_poly hshell ht ht1 hc hc1 x)
                (by dsimp [S45.power]; positivity)
          _ = ((2 * G + G ^ 2 + 4) * B ^ 3 * S45.power c (-(d : ℝ))) *
                (S45.power t (-2) * S45.power t (-3 * (d : ℝ))) *
                Real.exp (-(2 * c) * t ^ 3 * dist j.val x) := by ring
          _ = _ := by rw [hpow_comb]
      calc ‖-(S45.gamma t s x ξ + s.z t x / (1 - s.K t x x)) * s.K t j.val x +
              (S45.Jinc t s x ξ *ᵥ s.U t) j.val‖
          ≤ ‖-(S45.gamma t s x ξ + s.z t x / (1 - s.K t x x)) * s.K t j.val x‖ +
              ‖(S45.Jinc t s x ξ *ᵥ s.U t) j.val‖ := norm_add_le _ _
        _ ≤ _ := (add_le_add hterm1 hterm2).trans_eq (by dsimp [A_f]; ring)
    have hP_forc (j : S45.survivors x) :
        ‖(S45.deleteState t s x ξ).P t ⟨i, hi⟩ j * S45.forcing t s x ξ j.val‖ ≤
          (Ri * A_f * S45.power t (-(2 + 3 * (d : ℝ)))) *
            (Real.exp (-(2 * c) * t ^ 3 * dist i j.val) *
              Real.exp (-(2 * c) * t ^ 3 * dist j.val x)) := by
      rw [norm_mul]
      have hPij : ‖(S45.deleteState t s x ξ).P t ⟨i, hi⟩ j‖ ≤
          Ri * Real.exp (-(2 * c) * t ^ 3 * dist i j.val) := by
        refine (hnew_P ⟨i, hi⟩ j).trans (mul_le_mul_of_nonneg_left ?_ hRi.le)
        change Real.exp (-c_inv * t ^ 3 * dist i j.val) ≤ Real.exp (-(2 * c) * t ^ 3 * dist i j.val)
        apply Real.exp_le_exp.mpr
        have hle : (2 * c) * (t ^ 3 * dist i j.val) ≤ c_inv * (t ^ 3 * dist i j.val) :=
          mul_le_mul_of_nonneg_right hcinv
            (mul_nonneg (by positivity : 0 ≤ t ^ 3) (hshell.nonneg i j.val))
        have heq1 : -c_inv * t ^ 3 * dist i j.val = -(c_inv * (t ^ 3 * dist i j.val)) := by ring
        have heq2 : -(2 * c) * t ^ 3 * dist i j.val = -((2 * c) * (t ^ 3 * dist i j.val)) := by ring
        linarith
      exact (mul_le_mul hPij (hforc j) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    have hconv_surv :
        (∑ j : S45.survivors x,
          Real.exp (-(2 * c) * t ^ 3 * dist i j.val) *
            Real.exp (-(2 * c) * t ^ 3 * dist j.val x)) ≤
          Real.exp (-c * t ^ 3 * dist i x) *
            ((B * S45.power c (-(d : ℝ))) * S45.power t (-3 * (d : ℝ))) :=
      (poly_sum_subtype_le (S45.survivors x)
        (fun u => Real.exp (-(2 * c) * t ^ 3 * dist i u) * Real.exp (-(2 * c) * t ^ 3 * dist u x))
        (fun _ => by positivity)).trans (poly_convolution_sum hshell ht ht1 hc hc1 i x)
    have hrhs_bound :
        ‖((S45.deleteState t s x ξ).P t *ᵥ (fun j => S45.forcing t s x ξ j.val)) ⟨i, hi⟩‖ ≤
          (Ri * A_f * (B * S45.power c (-(d : ℝ))) *
            (S45.power t (-(2 + 3 * (d : ℝ))) * S45.power t (-3 * (d : ℝ))) *
            Real.exp (-c * t ^ 3 * dist i x)) := by
      calc ‖((S45.deleteState t s x ξ).P t *ᵥ (fun j => S45.forcing t s x ξ j.val)) ⟨i, hi⟩‖
          = ‖∑ j : S45.survivors x, (S45.deleteState t s x ξ).P t ⟨i, hi⟩ j *
              S45.forcing t s x ξ j.val‖ := rfl
        _ ≤ ∑ j : S45.survivors x,
              ‖(S45.deleteState t s x ξ).P t ⟨i, hi⟩ j * S45.forcing t s x ξ j.val‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j : S45.survivors x,
              (Ri * A_f * S45.power t (-(2 + 3 * (d : ℝ)))) *
                (Real.exp (-(2 * c) * t ^ 3 * dist i j.val) *
                  Real.exp (-(2 * c) * t ^ 3 * dist j.val x)) :=
            Finset.sum_le_sum fun j _ => hP_forc j
        _ = (Ri * A_f * S45.power t (-(2 + 3 * (d : ℝ)))) *
              (∑ j : S45.survivors x,
                Real.exp (-(2 * c) * t ^ 3 * dist i j.val) *
                  Real.exp (-(2 * c) * t ^ 3 * dist j.val x)) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (Ri * A_f * S45.power t (-(2 + 3 * (d : ℝ)))) *
              (Real.exp (-c * t ^ 3 * dist i x) *
                ((B * S45.power c (-(d : ℝ))) * S45.power t (-3 * (d : ℝ)))) :=
            mul_le_mul_of_nonneg_left hconv_surv (by dsimp [S45.power]; positivity)
        _ = _ := by ring
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hnorm_eq : Real.sqrt t * ‖S45.lagInc t s x ξ i‖ =
        ‖((S45.deleteState t s x ξ).P t *ᵥ (fun j => S45.forcing t s x ξ j.val)) ⟨i, hi⟩‖ := by
      have h := congrArg norm hexact
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos] using h
    have hdiv_le : ‖S45.lagInc t s x ξ i‖ ≤
        (Ri * A_f * (B * S45.power c (-(d : ℝ))) *
          (S45.power t (-(2 + 3 * (d : ℝ))) * S45.power t (-3 * (d : ℝ))) *
          Real.exp (-c * t ^ 3 * dist i x)) / Real.sqrt t := by
      rw [le_div_iff₀ hsqrt_pos, mul_comm, hnorm_eq]
      exact hrhs_bound
    have hpow_comb : S45.power t (-(2 + 3 * (d : ℝ))) * S45.power t (-3 * (d : ℝ)) *
        S45.power t (-1) = S45.power t (-(3 + 6 * (d : ℝ))) := by
      rw [poly_power_mul ht, poly_power_mul ht]; congr 1; ring
    have hsqrt_inv := poly_sqrt_inv_le ht ht1 (B := Ri * A_f * (B * S45.power c (-(d : ℝ))) *
      (S45.power t (-(2 + 3 * (d : ℝ))) * S45.power t (-3 * (d : ℝ))) *
      Real.exp (-c * t ^ 3 * dist i x)) (by dsimp [S45.power]; positivity)
    calc ‖S45.lagInc t s x ξ i‖
        ≤ _ := hdiv_le.trans hsqrt_inv
      _ = (Ri * A_f * (B * S45.power c (-(d : ℝ)))) *
            (S45.power t (-(2 + 3 * (d : ℝ))) * S45.power t (-3 * (d : ℝ)) * S45.power t (-1)) *
            Real.exp (-c * t ^ 3 * dist i x) := by ring
      _ = _ := by rw [hpow_comb]
  · simp [S45.lagInc, hi]
    dsimp [S45.power]; positivity

set_option maxHeartbeats 1600000 in
/-- At any valid prefix `q` reached by `slotSeq`, the candidate extension `c` satisfies
`TraceTails` with constants `(C_tail, c_tail)` depending only on `(d, C)`. -/
theorem traceTails_of_slotSeq (d : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    let C_tail : ℝ := 5 + 6 * (d : ℝ)
    ∃ c_tail > 0, ∃ t0 > 0, t0 ≤ 1 ∧
      ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
        (M : ℕ → ℕ) (x : RunRecord d m),
        P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 →
        TileGoodCore C P j T x → sweepScale P.u m j < t0 →
        ∀ (k : ℕ) (ω : RandomSources (Torus d m) M) (q : S45.Sequence (Port d m)),
          slotSeq P j T M x k ω = some q →
          ((tileSlot P j T M k ω, false) : Port d m) ∈ (q.state q.length).live →
          S45.TraceTails
            (candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
            (sweepScale P.u m j) C_tail c_tail (portR (sweepTheta P.u m j) x.r)
            S45.reserves (P.cover j).dist := by
  intro C_tail
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let B : ℝ := 2 * (1 + C ^ 2)
  let G : ℝ := 12 * B
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hCB : C ≤ B := by dsimp [B]; nlinarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hGpos : 0 < G := by dsimp [G]; positivity
  obtain ⟨Ri, hRi, c_inv, hc_inv, t0_del, ht0_del, ht0_del_le, hdel⟩ :=
    step_delete_inverse_decay d C hC
  obtain ⟨t0_schur, ht0_schur, ht0_schur_le, hschur⟩ := exists_schur_den_scale C hC
  let c_tail : ℝ := min (1 / (2 * B)) (c_inv / 2)
  have hc_tail : 0 < c_tail := lt_min (by positivity) (by positivity)
  have hc_tail_2B : c_tail ≤ 1 / (2 * B) := min_le_left _ _
  have hc_tail_inv : c_tail ≤ c_inv / 2 := min_le_right _ _
  have hc_tail_1 : c_tail ≤ 1 := by
    have h1 : 1 / (2 * B) ≤ 1 / 2 := div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
    linarith
  have hcB2 : 2 * c_tail ≤ 1 / B := by
    have := mul_le_mul_of_nonneg_left hc_tail_2B (by norm_num : (0 : ℝ) ≤ 2)
    have heq : 2 * (1 / (2 * B)) = 1 / B := by field_simp
    linarith
  have hcB : c_tail ≤ 1 / B := by linarith
  have hcinv2 : 2 * c_tail ≤ c_inv := by linarith
  let A_J : ℝ := (2 * G + G ^ 2 + 4) * B ^ 2
  let A_L : ℝ := B ^ 2 * (2 * G + G ^ 2 + 2 * B) * B ^ 2
  let A_row : ℝ := 2 * (4 * (1 + G) ^ 3 * G * B ^ 3 * S45.power c_tail (-(d : ℝ)))
  let A_lag : ℝ := Ri * ((G + 4 * B) * B + (2 * G + G ^ 2 + 4) * B ^ 3 * S45.power c_tail (-(d : ℝ))) *
    (B * S45.power c_tail (-(d : ℝ)))
  have hpow_ct : 0 < S45.power c_tail (-(d : ℝ)) := Real.rpow_pos_of_pos hc_tail _
  have hAJ_pos : 0 ≤ A_J := by dsimp [A_J]; positivity
  have hAL_pos : 0 ≤ A_L := by dsimp [A_L]; positivity
  have hArow_pos : 0 ≤ A_row := by dsimp [A_row, S45.power]; positivity
  have hAlag_pos : 0 ≤ A_lag := by dsimp [A_lag, S45.power]; positivity
  let t0_abs : ℝ := min (1 / (1 + A_J)) (min (1 / (1 + A_L)) (min (1 / (1 + A_row)) (1 / (1 + A_lag))))
  have ht0_abs : 0 < t0_abs :=
    lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  let t0 : ℝ := min t0_del (min t0_schur t0_abs)
  have ht0 : 0 < t0 := lt_min ht0_del (lt_min ht0_schur ht0_abs)
  have ht0_le : t0 ≤ 1 := (min_le_left _ _).trans ht0_del_le
  refine ⟨c_tail, hc_tail, t0, ht0, ht0_le, ?_⟩
  intro m P j T M x hu hj hjm hx htt k ω q hq hal2
  have hu_pos : 0 < P.u := lt_trans (by norm_num) hu.1
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set y := tileSlot P j T M k ω
  set p_cand : Port d m := (y, false)
  set ξ_cand := tileXi P j T M x k ω
  set b_cand := stepLive t r (q.state q.length) p_cand ξ_cand
  set c := candidate P j x q y ξ_cand
  have hc_def : c = extendSeq q b_cand p_cand ξ_cand := rfl
  have ht : 0 < t := sweepScale_pos_first hu_pos m j
  have ht1 : t ≤ 1 := htt.le.trans ht0_le
  have htt_del : t < t0_del := lt_of_lt_of_le htt (min_le_left _ _)
  have htt_schur : t < t0_schur :=
    lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt_abs : t ≤ t0_abs :=
    htt.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht_AJ : t ≤ 1 / (1 + A_J) := htt_abs.trans (min_le_left _ _)
  have ht_AL : t ≤ 1 / (1 + A_L) :=
    htt_abs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht_Arow : t ≤ 1 / (1 + A_row) :=
    htt_abs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht_Alag : t ≤ 1 / (1 + A_lag) :=
    htt_abs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hden_cand : stepDen t r (q.state q.length) p_cand ξ_cand ≠ 0 :=
    stepDen_ne_zero_of_slotSeq P j T M x hx hu hj hjm hq hal2 ht0_schur_le hschur htt_schur
  have inv := slotSeq_inv P j T M x hx ω k q hq
  have hc_wf : c.wellFormed t r :=
    extendSeq_wellFormed t r q inv.wellFormed p_cand ξ_cand hal2 hden_cand
  have hbroad : ∀ {s : ℕ}, s ≤ q.length → ∀ {u : Port d m}, u ∈ (q.state s).live →
      ‖r u‖ ≤ C ∧ 1 / C ≤ (r u).im ∧ (r u).im ≤ C := fun hs _ hu =>
    start_broad P j T x hx (live_mem_start x inv.wellFormed
      (inv.state_prefix 0 (Nat.zero_le _)) hs hu)
  have hsw0 := start_state_isSymm_ward P j T x (inv.state_prefix 0 (Nat.zero_le _)) hx
  have hsw := wellFormed_symm_ward ht inv.wellFormed hsw0.1 hsw0.2
  have hbit_q : ∀ s < q.length, ∀ z, q.pivot s = some z → z.2 = false := by
    intro s hs z hpz
    by_cases hs0 : s < x.sweep.length
    · rw [inv.pivot_prefix s hs0] at hpz
      exact hx.bit_pivots s hs0 z hpz
    · obtain ⟨l, _, _, hpiv_l, _⟩ := inv.trial_step s (Nat.le_of_not_lt hs0) hs
      rw [hpz] at hpiv_l
      injection hpiv_l with hz
      rw [hz]
  have hshellB : S45.ShellBounds d B (P.cover j).dist := ShellBounds_mono hx.shell hCB
  have hd_nn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hEC_J : 2 + 1 ≤ C_tail := by dsimp [C_tail]; linarith
  have hEC_row : (4 + 3 * (d : ℝ)) + 1 ≤ C_tail := by dsimp [C_tail]; linarith
  have hEC_lag : (3 + 6 * (d : ℝ)) + 1 ≤ C_tail := by dsimp [C_tail]; linarith
  have hstep_all : ∀ s < c.length, ∀ z, c.pivot s = some z →
      (∀ i u, ‖c.stepJ t r s i u‖ ≤
        S45.power t (-C_tail) * Real.exp (-c_tail * t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z))) ∧
      (∀ i u, i ≠ u → |c.stepL t r s i u| ≤
        S45.power t (-C_tail) * Real.exp (-c_tail * t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z))) ∧
      (∀ i, ‖c.stepLag t r s i‖ ≤
        S45.power t (-C_tail) * Real.exp (-c_tail * t ^ 3 * (P.cover j).dist i z)) ∧
      (∀ i, |c.stepRow t r Finset.univ s i| + |c.stepRow t r S45.reserves s i| ≤
        S45.power t (-C_tail) * Real.exp (-c_tail * t ^ 3 * (P.cover j).dist i z)) := by
    intro s hs_lt z hpiv
    have hs_le : s ≤ q.length := by
      rw [hc_def, extendSeq_length_a3b] at hs_lt
      omega
    let a := q.state s
    have hstate_s : c.state s = a := by
      rw [hc_def, extendSeq_state_of_le q b_cand p_cand ξ_cand hs_le]
    let b := c.state (s + 1)
    let ξ := c.scalar s
    let amb := a.ambient r
    let sk := a.state r
    have ha_wf_c : (c.state s).g = S45.mask (c.state s).live (c.state s).g := hc_wf.1 s hs_lt.le
    have ha_wf : a.g = S45.mask a.live a.g := hstate_s ▸ ha_wf_c
    have hrel_c : S45.StepRel t r (c.state s) b z ξ := by
      have h := hc_wf.2 s hs_lt
      simpa [hpiv] using h
    have hrel : S45.StepRel t r a b z ξ := hstate_s ▸ hrel_c
    let z_live : a.live := ⟨z, hrel.pivot_live⟩
    have h2C : 2 * Real.sqrt t ≤ 2 * C * Real.sqrt t :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg t)
    have hξ_bound : |ξ| ≤ 2 * C * Real.sqrt t := by
      dsimp [ξ]
      rcases lt_or_eq_of_le hs_le with hslt | rfl
      · rw [hc_def, extendSeq_scalar_of_lt q b_cand p_cand ξ_cand hslt]
        by_cases hs0 : s < x.sweep.length
        · rw [inv.scalar_prefix s hs0]
          exact (hx.scalar_bound s hs0).trans h2C
        · obtain ⟨l, _, _, _, hsc_l⟩ := inv.trial_step s (Nat.le_of_not_lt hs0) hslt
          rw [hsc_l]
          exact (abs_tileXi_le P j T M x hu_pos hj hjm hx l ω).trans h2C
      · rw [hc_def, extendSeq_scalar_last_a3b q b_cand p_cand ξ_cand]
        exact (abs_tileXi_le P j T M x hu_pos hj hjm hx k ω).trans h2C
    have hval_s : q.valid t r (stageD0 P j x) s := inv.valid s hs_le
    obtain ⟨hK_q, hbounds_q⟩ := prefix_schur_and_bounds P j T x hx inv.wellFormed
      (inv.state_prefix 0 (Nat.zero_le _)) inv.valid ht0_schur_le hschur ht htt_schur s hs_le
    obtain ⟨hweak_q, hfar_q⟩ := hx.prefix_decay q inv.wellFormed
      (inv.state_prefix 0 (Nat.zero_le _)) hbit_q s hs_le hval_s
    have hshell_sk : S45.ShellBounds d C (fun u v : a.live => (P.cover j).dist u.val v.val) :=
      poly_shell_subtype hx.shell a.live
    have hsym_sk : sk.g.IsSymm := (hsw s hs_le).1
    have hward_sk : sk.ward t := (hsw s hs_le).2
    have hp_sk : ∀ u : a.live, 1 / C ≤ sk.p u ∧ sk.p u ≤ C :=
      fun u => ⟨(hbroad hs_le u.2).2.1, (hbroad hs_le u.2).2.2⟩
    have hr_sk : ∀ u : a.live, ‖sk.r u‖ ≤ C := fun u => (hbroad hs_le u.2).1
    have hK_sk : ‖sk.K t‖ ≤ 3 / 4 := hK_q
    have hraw_sk : ∀ u : a.live, ‖sk.rawLag u‖ ≤ B * S45.power t S45.beta :=
      fun u => (hbounds_q u).1
    have hKne_sk : 1 - sk.K t z_live z_live ≠ 0 := (hbounds_q z_live).2.1
    have hrow_sk : ∀ u : a.live, sk.fourthRow t Finset.univ u ≤ S45.rowCap t := hval_s.2.2.1
    have hlag_sk : ∀ u : a.live, ‖sk.lag t u‖ ≤ 1 := by
      intro u
      have h1 := hval_s.2.2.2 u
      have h2 : S45.power t S45.beta ≤ 1 :=
        Real.rpow_le_one ht.le ht1 (by norm_num [S45.beta, S45.delta])
      exact h1.trans h2
    have hweak_sk : ∀ u v : a.live,
        ‖sk.h t u v‖ ≤ C / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist u.val v.val / C) :=
      hweak_q
    have hfar_sk : ∀ u v : a.live, C * S45.power t (-2) < (P.cover j).dist u.val v.val →
        ‖sk.h t u v‖ ≤ C / Real.sqrt t * Real.exp (-t * (P.cover j).dist u.val v.val / C) :=
      hfar_q
    obtain ⟨hden_sk, hγ_sk, hnew_unit, hnew_P⟩ :=
      hdel a.live t sk (fun u v => (P.cover j).dist u.val v.val) z_live ξ
        ht htt_del hshell_sk hsym_sk hward_sk hp_sk hr_sk hK_sk hraw_sk hrow_sk
        hweak_sk hfar_sk hξ_bound
    have hentry_sk := poly_entry_small t sk ht ht1 hrow_sk
    have hv1 : S45.power t (1 / 4) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
    have hsmall_sk (u v : a.live) : ‖sk.h t u v‖ ≤ 1 := (hentry_sk u v).trans hv1
    have hweakB_sk (u v : a.live) :
        ‖sk.h t u v‖ ≤ B / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist u.val v.val / B) :=
      (hweak_sk u v).trans (poly_decay_constant hCpos hCB ht (by positivity)
        (hx.shell.nonneg u.val v.val))
    have hsmall_amb (u v : Port d m) : ‖amb.h t u v‖ ≤ 1 :=
      amb_h_norm_le a r t (fun _ _ => 1) (fun _ _ => zero_le_one) hsmall_sk u v
    have hdec_amb (u v : Port d m) :
        ‖amb.h t u v‖ ≤ B / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist u v / B) :=
      amb_h_norm_le a r t (fun u v => B / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist u v / B))
        (fun _ _ => by positivity) hweakB_sk u v
    obtain ⟨_, _, hp_piv, hq_piv, hK_piv, hF_piv, hγ_piv⟩ :=
      amb_at_pivot a r t hrel.pivot_live ξ
    have hγ_amb : ‖S45.gamma t amb z ξ‖ ≤ G := by rw [hγ_piv]; exact hγ_sk
    have hKxx_norm : ‖sk.K t z_live z_live‖ ≤ 3 / 4 :=
      (entry_le_l2 (sk.K t) z_live z_live).trans hK_sk
    have hKinv_sk : ‖(1 - sk.K t z_live z_live)⁻¹‖ ≤ 4 :=
      norm_inv_one_sub_le_four (sk.K t z_live z_live) hKxx_norm
    have hKinv_amb : ‖(1 - amb.K t z z)⁻¹‖ ≤ 4 := by rw [hK_piv]; exact hKinv_sk
    have hexp_bound (u v : Port d m) :
        Real.exp (-t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z) / B) ≤
          Real.exp (-c_tail * t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z)) := by
      apply Real.exp_le_exp.mpr
      have hd_uv : 0 ≤ (P.cover j).dist u z + (P.cover j).dist v z :=
        add_nonneg (hx.shell.nonneg u z) (hx.shell.nonneg v z)
      have h1 : c_tail * (t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z)) ≤
          (1 / B) * (t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z)) :=
        mul_le_mul_of_nonneg_right hcB (mul_nonneg (by positivity : 0 ≤ t ^ 3) hd_uv)
      have h2 : -t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z) / B =
          -((1 / B) * (t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z))) := by ring
      have h3 : -c_tail * t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z) =
          -(c_tail * (t ^ 3 * ((P.cover j).dist u z + (P.cover j).dist v z))) := by ring
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i u
      have hstepJ : ‖c.stepJ t r s i u‖ ≤ ‖S45.Jinc t amb z ξ i u‖ := by
        unfold S45.Sequence.stepJ
        rw [hpiv, hstate_s]
        by_cases hi : i ∈ b.live <;> by_cases hu' : u ∈ b.live <;>
          simp [S45.mask, S45.pad, S45.restrict, b, amb, a, ξ, hi, hu']
      have hJ1 := poly_Jinc_factor hGpos.le hsmall_amb hγ_amb hKinv_amb i u
      have hJ2 := poly_two_factor_exp ht ht1 hBpos hx.shell.symmetric hdec_amb i z u
      have habs := absorb_const_into_power ht ht1 hAJ_pos ht_AJ hEC_J
      calc ‖c.stepJ t r s i u‖
          ≤ ‖S45.Jinc t amb z ξ i u‖ := hstepJ
        _ ≤ (2 * G + G ^ 2 + 4) * (B ^ 2 * S45.power t (-2) *
              Real.exp (-t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z) / B)) :=
            hJ1.trans (mul_le_mul_of_nonneg_left hJ2 (by positivity))
        _ = (A_J * S45.power t (-2)) *
              Real.exp (-t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z) / B) := by
            dsimp [A_J]; ring
        _ ≤ S45.power t (-C_tail) *
              Real.exp (-c_tail * t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z)) :=
            mul_le_mul habs (hexp_bound i u) (Real.exp_nonneg _)
              (Real.rpow_nonneg ht.le _)
    · intro i u hiu
      by_cases hlive_iu : i ∈ b.live ∧ u ∈ b.live
      swap
      · have h0 : c.stepL t r s i u = 0 := by
          unfold S45.Sequence.stepL
          rw [hpiv]
          rcases not_and_or.mp hlive_iu with hi | hu'
          · have hi' : i ∉ (c.state (s + 1)).live := hi
            simp [S45.mask, S45.pad, hi']
          · have hu'' : u ∉ (c.state (s + 1)).live := hu'
            simp [S45.mask, S45.pad, hu'']
        rw [h0, abs_zero]
        dsimp [S45.power]; positivity
      have hb_sub : b.live ⊆ a.live := by
        rw [hrel.survivors]; exact Finset.erase_subset z a.live
      have hp_amb : ∀ w, w ∈ b.live → |amb.p w| ≤ B := by
        intro w hw
        have hbw := hbroad hs_le (hb_sub hw)
        have hp1 : 0 ≤ amb.p w := le_trans (by positivity) hbw.2.1
        rw [abs_of_nonneg hp1]
        exact hbw.2.2.trans hCB
      have hpivot_amb : |amb.p z / (amb.q z - amb.p z * amb.F t z z)| ≤ 2 * B := by
        rw [hp_piv, hq_piv, hF_piv]
        obtain ⟨_, _, hp3_s, _, hp5_s⟩ := hschur t ht htt_schur
        have hqp_z : |sk.q z_live - sk.p z_live| ≤ 1 / (2 * C) := by
          have him : sk.q z_live - sk.p z_live = (sk.rawLag z_live).im := by
            simp [S45.State.q, S45.State.p, S45.State.rawLag]
          rw [him]
          exact (Complex.abs_im_le_norm _).trans ((hraw_sk z_live).trans hp3_s)
        have hq_lo : 1 / (2 * C) ≤ sk.q z_live := by
          have hp_lo := (hp_sk z_live).1
          have hqp_lo := (abs_le.mp hqp_z).1
          have hdiv2 : 1 / C - 1 / (2 * C) = 1 / (2 * C) := by ring
          linarith
        have hFzz : sk.F t z_live z_live ≤ Real.sqrt t :=
          F_diag_le_sqrt_of_row_cap ht ht1 sk z_live (hrow_sk z_live)
        have hpF_z : sk.p z_live * sk.F t z_live z_live ≤ 1 / (4 * C) := by
          have h1 : sk.p z_live * sk.F t z_live z_live ≤ C * Real.sqrt t :=
            mul_le_mul (hp_sk z_live).2 hFzz (by simp [S45.State.F, S45.entryAbsSquare]) hCpos.le
          have h2 : C * Real.sqrt t ≤ C * (4 * (3 * C) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hp5_s.le hCpos.le
          have h3 : C * (4 * (3 * C) ^ 2)⁻¹ = 1 / (36 * C) := by field_simp; ring
          have h4 : 1 / (36 * C) ≤ 1 / (4 * C) :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
          linarith
        have hden_lo : 1 / (4 * C) ≤ sk.q z_live - sk.p z_live * sk.F t z_live z_live := by
          have : 1 / (2 * C) - 1 / (4 * C) = 1 / (4 * C) := by ring
          linarith
        have hden_pos : 0 < sk.q z_live - sk.p z_live * sk.F t z_live z_live :=
          lt_of_lt_of_le (by positivity) hden_lo
        have hp_pos : 0 ≤ sk.p z_live := le_trans (by positivity) (hp_sk z_live).1
        rw [abs_div, abs_of_nonneg hp_pos, abs_of_pos hden_pos]
        calc sk.p z_live / (sk.q z_live - sk.p z_live * sk.F t z_live z_live)
            ≤ C / (1 / (4 * C)) :=
              div_le_div₀ hCpos.le (hp_sk z_live).2 (by positivity) hden_lo
          _ = 4 * C ^ 2 := by field_simp
          _ ≤ 2 * B := by dsimp [B]; linarith
      have hstepL_le : |c.stepL t r s i u| ≤ |S45.Linc t amb z ξ i u| := by
        unfold S45.Sequence.stepL
        rw [hpiv, hstate_s]
        by_cases hi : i ∈ b.live <;> by_cases hu' : u ∈ b.live <;>
          simp [S45.mask, S45.pad, S45.restrict, b, amb, a, ξ, hi, hu']
      by_cases hi_s : i ∈ S45.survivors z
      · by_cases hu_s : u ∈ S45.survivors z
        · have hne_sub : (⟨i, hi_s⟩ : S45.survivors z) ≠ ⟨u, hu_s⟩ :=
            fun h => hiu (congrArg Subtype.val h)
          have hLinc_eq : |S45.Linc t amb z ξ i u| =
              |S45.Ledge t amb z ξ ⟨i, hi_s⟩ ⟨u, hu_s⟩| := by
            simp [S45.Linc, S45.pad, S45.laplacian, hi_s, hu_s, hne_sub]
          have hL1 := poly_Ledge_factor hBpos.le hGpos.le (by positivity : 0 ≤ 2 * B)
            hsmall_amb hγ_amb hpivot_amb ⟨i, hi_s⟩ ⟨u, hu_s⟩ (hp_amb i hlive_iu.1)
            (hp_amb u hlive_iu.2)
          have hL2 := poly_two_factor_exp ht ht1 hBpos hx.shell.symmetric hdec_amb i z u
          have habs := absorb_const_into_power ht ht1 hAL_pos ht_AL hEC_J
          calc |c.stepL t r s i u|
              ≤ |S45.Ledge t amb z ξ ⟨i, hi_s⟩ ⟨u, hu_s⟩| := hstepL_le.trans_eq hLinc_eq
            _ ≤ B ^ 2 * (2 * G + G ^ 2 + 2 * B) *
                  (B ^ 2 * S45.power t (-2) *
                    Real.exp (-t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z) / B)) :=
                hL1.trans (mul_le_mul_of_nonneg_left hL2 (by positivity))
            _ = (A_L * S45.power t (-2)) *
                  Real.exp (-t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z) / B) := by
                dsimp [A_L]; ring
            _ ≤ S45.power t (-C_tail) *
                  Real.exp (-c_tail * t ^ 3 * ((P.cover j).dist i z + (P.cover j).dist u z)) :=
                mul_le_mul habs (hexp_bound i u) (Real.exp_nonneg _)
                  (Real.rpow_nonneg ht.le _)
        · have h0 : S45.Linc t amb z ξ i u = 0 := by simp [S45.Linc, S45.pad, hi_s, hu_s]
          rw [h0, abs_zero] at hstepL_le
          exact hstepL_le.trans (by dsimp [S45.power]; positivity)
      · have h0 : S45.Linc t amb z ξ i u = 0 := by simp [S45.Linc, S45.pad, hi_s]
        rw [h0, abs_zero] at hstepL_le
        exact hstepL_le.trans (by dsimp [S45.power]; positivity)
    · intro i
      by_cases hi_b : i ∈ b.live
      · have hi_er : i ∈ a.live.erase z := hrel.survivors ▸ hi_b
        have hi_a : i ∈ a.live := Finset.mem_of_mem_erase hi_er
        let e_step := stepLiveEquiv hrel.pivot_live hrel.survivors
        have hi_surv : (⟨i, hi_a⟩ : a.live) ∈ S45.survivors z_live :=
          (e_step ⟨i, hi_b⟩).property
        have hlag_b : (b.state r).lag t ⟨i, hi_b⟩ =
            (S45.deleteState t sk z_live ξ).lag t ⟨⟨i, hi_a⟩, hi_surv⟩ := by
          have hre := stepRel_state_eq_reindex hrel
          rw [hre]
          exact reindex_lag e_step (S45.deleteState t sk z_live ξ) t hnew_unit ⟨i, hi_b⟩
        have hstepLag_eq : c.stepLag t r s i = S45.lagInc t sk z_live ξ ⟨i, hi_a⟩ := by
          unfold S45.Sequence.stepLag
          rw [hstate_s]
          simp only [b, a, hi_b, ↓reduceIte, S45.LiveState.ambientLag, hi_a, ↓reduceDIte]
          rw [hlag_b]
          simp [S45.lagInc, hi_surv, sk, a]
        have hunit_sk : IsUnit (1 - sk.K t) :=
          (Units.oneSub (sk.K t) (by linarith : ‖sk.K t‖ < 1)).isUnit
        have hraw_z : ‖sk.rawLag z_live‖ ≤ B := by
          have hpowβ1 : S45.power t S45.beta ≤ 1 :=
            Real.rpow_le_one ht.le ht1 (by norm_num [S45.beta, S45.delta])
          nlinarith [hraw_sk z_live]
        have hshellB_sk : S45.ShellBounds d B (fun u v : a.live => (P.cover j).dist u.val v.val) :=
          poly_shell_subtype hshellB a.live
        have hlagInc := poly_lagInc_bound ht ht1 hB hGpos.le hRi hc_tail hc_tail_1 hcB2 hcinv2
          hshellB_sk hsym_sk hunit_sk hKne_sk hKinv_sk hden_sk hγ_sk hraw_z hlag_sk
          hsmall_sk hweakB_sk hnew_unit hnew_P ⟨i, hi_a⟩
        have habs := absorb_const_into_power ht ht1 hAlag_pos ht_Alag hEC_lag
        rw [hstepLag_eq]
        calc ‖S45.lagInc t sk z_live ξ ⟨i, hi_a⟩‖
            ≤ (A_lag * S45.power t (-(3 + 6 * (d : ℝ)))) *
                Real.exp (-c_tail * t ^ 3 * (P.cover j).dist i z) := by
              simpa [A_lag, mul_assoc] using hlagInc
          _ ≤ S45.power t (-C_tail) * Real.exp (-c_tail * t ^ 3 * (P.cover j).dist i z) :=
              mul_le_mul_of_nonneg_right habs (Real.exp_nonneg _)
      · have h0 : c.stepLag t r s i = 0 := by simp [S45.Sequence.stepLag, b, hi_b]
        rw [h0, norm_zero]
        dsimp [S45.power]; positivity
    · intro i
      have hsmall_amb_c : ∀ u v, ‖((c.state s).ambient r).h t u v‖ ≤ 1 := by
        rw [hstate_s]; exact hsmall_amb
      have hdec_amb_c : ∀ u v, ‖((c.state s).ambient r).h t u v‖ ≤
          B / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist u v / B) := by
        rw [hstate_s]; exact hdec_amb
      have hγ_amb_c : ‖S45.gamma t ((c.state s).ambient r) z ξ‖ ≤ G := by
        rw [hstate_s]; exact hγ_amb
      have h1 := poly_row_step_bound ht ht1 hBpos hGpos.le hc_tail hc_tail_1 hcB
        hshellB ha_wf_c hrel_c hsmall_amb_c hdec_amb_c hγ_amb_c Finset.univ i
      have h2 := poly_row_step_bound ht ht1 hBpos hGpos.le hc_tail hc_tail_1 hcB
        hshellB ha_wf_c hrel_c hsmall_amb_c hdec_amb_c hγ_amb_c S45.reserves i
      have habs := absorb_const_into_power ht ht1 hArow_pos ht_Arow hEC_row
      calc |c.stepRow t r Finset.univ s i| + |c.stepRow t r S45.reserves s i|
          ≤ (A_row * S45.power t (-(4 + 3 * (d : ℝ)))) *
              Real.exp (-c_tail * t ^ 3 * (P.cover j).dist i z) := by
            have hsum := add_le_add h1 h2
            dsimp [A_row]
            linarith
        _ ≤ S45.power t (-C_tail) * Real.exp (-c_tail * t ^ 3 * (P.cover j).dist i z) :=
            mul_le_mul_of_nonneg_right habs (Real.exp_nonneg _)
  exact ⟨fun s hs z hpz => (hstep_all s hs z hpz).1,
    fun s hs z hpz => (hstep_all s hs z hpz).2.1,
    fun s hs z hpz => (hstep_all s hs z hpz).2.2.1,
    fun s hs z hpz => (hstep_all s hs z hpz).2.2.2⟩

/-- Unconditional proof of `TileTransferStatement` (A3b). -/
theorem tileTransfer_proof : ∀ d (C : ℝ), 1 ≤ C → TileTransferStatement d C := by
  intro d C hC
  let C_tail : ℝ := max C (5 + 6 * (d : ℝ))
  have hC_le_Ctail : C ≤ C_tail := le_max_left _ _
  have h1_Ctail : 1 ≤ C_tail := hC.trans hC_le_Ctail
  have h5_le_Ctail : 5 + 6 * (d : ℝ) ≤ C_tail := le_max_right _ _
  obtain ⟨t0_den, ht0_den, ht0_den_le, hschur⟩ := exists_schur_den_scale C hC
  obtain ⟨c_tail, hc_tail, t0_tail, ht0_tail, ht0_tail_le, htails_gen⟩ :=
    traceTails_of_slotSeq d C hC
  obtain ⟨t0_val, ht0_val, hvalid_gen⟩ :=
    local_transfer_valid_poly d C_tail c_tail h1_Ctail hc_tail
  let t0 : ℝ := min t0_den (min t0_tail t0_val)
  have ht0 : 0 < t0 := lt_min ht0_den (lt_min ht0_tail ht0_val)
  refine ⟨t0, ht0, ?_⟩
  intro m P j T M x hu hj hjm _hM _habort hx htt k ω q _hk hq hact hal2 _c _t _r _K hbud
  have hu_pos : 0 < P.u := lt_trans (by norm_num) hu.1
  have htpos : 0 < sweepScale P.u m j := sweepScale_pos_first hu_pos m j
  have htt_den : sweepScale P.u m j < t0_den := lt_of_lt_of_le htt (min_le_left _ _)
  have htt_tail : sweepScale P.u m j < t0_tail :=
    lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt_val : sweepScale P.u m j < t0_val :=
    lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
  have ht1 : sweepScale P.u m j ≤ 1 := htt_tail.le.trans ht0_tail_le
  have hden := stepDen_ne_zero_of_slotSeq P j T M x hx hu hj hjm hq hal2 ht0_den_le hschur htt_den
  have htails5 := htails_gen m P j T M x hu hj hjm hx htt_tail k ω q hq hal2
  have hpow_mono : S45.power (sweepScale P.u m j) (-(5 + 6 * (d : ℝ))) ≤
      S45.power (sweepScale P.u m j) (-C_tail) :=
    poly_mono htpos ht1 h5_le_Ctail
  have htails : S45.TraceTails
      (candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
      (sweepScale P.u m j) C_tail c_tail (portR (sweepTheta P.u m j) x.r)
      S45.reserves (P.cover j).dist := by
    refine ⟨fun s hs z hpz i u => (htails5.J s hs z hpz i u).trans
        (mul_le_mul_of_nonneg_right hpow_mono (Real.exp_nonneg _)),
      fun s hs z hpz i u hiu => (htails5.L s hs z hpz i u hiu).trans
        (mul_le_mul_of_nonneg_right hpow_mono (Real.exp_nonneg _)),
      fun s hs z hpz i => (htails5.lag s hs z hpz i).trans
        (mul_le_mul_of_nonneg_right hpow_mono (Real.exp_nonneg _)),
      fun s hs z hpz i => (htails5.rows s hs z hpz i).trans
        (mul_le_mul_of_nonneg_right hpow_mono (Real.exp_nonneg _))⟩
  have hval := valid_of_traceTails hC_le_Ctail hvalid_gen P j T M x hu_pos hx k ω q
    hq hact hal2 hden htt_val hbud htails
  exact ⟨hden, hval⟩

end TraceTailsAndTransfer

end AndersonAC.AgentS78
