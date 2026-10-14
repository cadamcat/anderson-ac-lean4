import AndersonAC.S45.LocalTransferProof
import AndersonAC.S45.EndpointAssembly

/-!
# The reserve-row transfer for an arbitrary live start (generic port type)

 . The last conclusion of `S45.local_transfer` (05:536–600: the
reserve fourth rows after a sweep are at most `(θ² + C' t^{δ/2000}) rowCap t`) uses only the
row records: the row tails of every step (`TraceTails.rows`), the row budgets of the tiles,
the scalar-record identity (`scalarRecords_holds`) and the start reserve rows. Its proof
(`AgentS45.local_transfer_of`, reserve-row part) does not need the start live set to be all
ports. This file restates that part for an arbitrary port type and an arbitrary live start,
so that it applies to the committed sweep of a record directly on `Port d m` (live start = the
ports of the active sites), without the restriction to the active ports.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace AndersonAC.AgentS78send

open AndersonAC.S45

/-- **Reserve-row transfer** (generic port type, arbitrary live start; cover and shell constants
at most `C`). -/
theorem reserveRow_transfer (d : ℕ) (C c : ℝ) (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ C' > (0 : ℝ), ∃ t0 > (0 : ℝ), ∀ (P I : Type) [Fintype P] [DecidableEq P] [Fintype I]
      [DecidableEq I] (t b θ Ccov Csh : ℝ) (dist : P → P → ℝ) (r : P → ℂ) (res : Finset P)
      (cover : TileCover (P := P) (I := I) d t b Ccov dist) (q : Sequence P)
      (blocks : Fin cover.count → Finset ℕ),
      0 < t → t < t0 → Ccov ≤ C → ShellBounds d Csh dist → Csh ≤ C → q.wellFormed t r →
      (∀ k l, k < q.length → l < q.length → ∀ x, q.pivot k = some x → q.pivot l = some x →
        k = l) →
      (∀ k < q.length, ∃! T, k ∈ blocks T) → (∀ T, blocks T ⊆ Finset.range q.length) →
      (∀ k < q.length, ∀ x, q.pivot k = some x → ∀ T, k ∈ blocks T → x ∈ cover.tile T) →
      (∀ k < q.length, ∀ x, q.pivot k = some x → ∀ i,
        |q.stepRow t r res k i| ≤ power t (-C) * Real.exp (-c * t ^ 3 * dist i x)) →
      (∀ i ∈ (q.state 0).live, (q.state 0).ambientLag t r i = 0) →
      (∀ i ∈ res, ((q.state 0).ambient r).fourthRow t res i ≤ θ ^ 2 * rowCap t) →
      (∀ T, ∀ i ∈ cover.inner T, |q.rowRecord t r res (blocks T) i| ≤ power t (delta / 2000)) →
      ∀ i ∈ res ∩ (q.state q.length).live,
        ((q.state q.length).ambient r).fourthRow t res i ≤
          (θ ^ 2 + C' * power t (delta / 2000)) * rowCap t := by
  have hC0 : 0 < C := by linarith
  obtain ⟨t1, ht1, htail⟩ := AgentS45.tail_small C C c d hc
  obtain ⟨t5, ht5, hs5⟩ := AgentS45.power_small (e := 3) (by norm_num) (a := 2 / c)
    (by positivity)
  refine ⟨C + 1, by linarith, min (min t1 t5) 1, lt_min (lt_min ht1 ht5) one_pos, ?_⟩
  intro P I _ _ _ _ t b θ Ccov Csh dist r res cover q blocks ht htt hCcov hshell hCsh hwf hinj
    hblk hbsub htile
    hrowtail hlag0 hres0 hbud
  have htt1 : t < t1 := lt_of_lt_of_le htt ((min_le_left _ _).trans (min_le_left _ _))
  have htt5 : t < t5 := lt_of_lt_of_le htt ((min_le_left _ _).trans (min_le_right _ _))
  have ht1' : t ≤ 1 := (lt_of_lt_of_le htt (min_le_right _ _)).le
  -- kernel parameters (as in `local_transfer_of`)
  set u : ℝ := c * t ^ 3 / 2 with hudef
  have hu0' : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    have h := hs5 t ht htt5
    have : power t 3 = t ^ 3 := by
      show t ^ (3 : ℝ) = t ^ 3; exact_mod_cast Real.rpow_natCast t 3
    rw [this] at h
    rw [hudef]
    have := mul_lt_mul_of_pos_left h hc
    rw [mul_div_cancel₀ _ (ne_of_gt hc)] at this
    linarith
  set A : ℝ := power t (-C) with hAdef
  have hA0 : 0 ≤ A := (Real.rpow_pos_of_pos ht _).le
  set R : ℝ := power t (-6) with hRdef
  set S : ℝ := C * power u (-(d : ℝ)) with hSdef
  have hS1' : 1 ≤ power u (-(d : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0' hu1 (by simp)
  have hS0 : 0 ≤ S := by positivity
  have hSge : 1 ≤ S := by nlinarith
  have hcount2 : ∀ i, (∑ x, Real.exp (-u * dist i x)) ≤ S := fun i =>
    (hshell.count u hu0' hu1 i).trans
      (mul_le_mul_of_nonneg_right hCsh (Real.rpow_pos_of_pos hu0' _).le)
  have htailt : A * Real.exp (-u * R) * S ^ 2 ≤ t := htail t ht htt1
  have hTAIL1 : ∀ i, A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist i x) ≤
      A * Real.exp (-u * R) * S ^ 2 := by
    intro i
    refine mul_le_mul_of_nonneg_left ((hcount2 i).trans ?_) (by positivity)
    nlinarith
  have hov : ∀ i, ((Finset.univ.filter fun T => i ∈ cover.inner T).card : ℝ) ≤ C :=
    fun i => (cover.overlap i).trans hCcov
  have hbuf : ∀ T, ∀ x ∈ cover.tile T, ∀ i, i ∉ cover.inner T → R ≤ dist i x := cover.buffer
  have hexpu : ∀ z : ℝ, Real.exp (-c * t ^ 3 * z) = Real.exp (-(2 * u) * z) := fun z => by
    rw [hudef]; ring_nf
  have hpw : ∀ e, 0 ≤ power t e := fun e => (Real.rpow_pos_of_pos ht _).le
  have hrc : 0 ≤ rowCap t := hpw _
  -- the reserve row record
  have hrowb : ∀ i, |q.rowRecord t r res (Finset.range q.length) i| ≤
      (C + 1) * power t (delta / 2000) := by
    intro i
    have h := AgentS45.scalar_transfer q.length q.pivot hinj blocks hblk hbsub cover.inner
      cover.tile dist C (power t (delta / 2000)) A u R hu0'.le hA0 (hpw _) hov htile hbuf
      (fun k => q.stepRow t r res k) (fun k hk hpv => (AgentS45.step_none hwf hk hpv).2.2 res)
      (fun k hk x hpv i => by
        rw [← hexpu, Real.norm_eq_abs]
        exact hrowtail k hk x hpv i)
      (fun T i hi => by
        have := hbud T i hi
        rw [Real.norm_eq_abs]
        simpa [Sequence.rowRecord, Finset.sum_apply] using this) i
    have h2 : A * Real.exp (-u * R) * S ^ 2 ≤ power t (delta / 2000) :=
      htailt.trans (AgentS45.le_power_of_le_one ht ht1' (by norm_num [delta]))
    have h3 := (hTAIL1 i).trans h2
    have e : q.rowRecord t r res (Finset.range q.length) i =
        ∑ k ∈ Finset.range q.length, q.stepRow t r res k i := by
      simp [Sequence.rowRecord, Finset.sum_apply]
    rw [e, ← Real.norm_eq_abs]
    linarith
  -- the final reserve rows
  intro i hi
  obtain ⟨hires, hilive⟩ := Finset.mem_inter.1 hi
  have hsr' := (AgentS45.scalarRecords_holds P q t r res ht hwf hlag0 i hilive).2
  have edead : ∀ (a : LiveState P), ∑ j ∈ res ∩ a.live, ‖(a.ambient r).h t i j‖ ^ 4 =
      (a.ambient r).fourthRow t res i := by
    intro a
    simp only [State.fourthRow]
    rw [← Finset.sum_filter_add_sum_filter_not res (· ∈ a.live)]
    rw [Finset.sum_eq_zero (s := res.filter fun j => j ∉ a.live) (fun j hj => by
      rw [AgentS45.ambient_h_dead _ r t i (Finset.mem_filter.1 hj).2]; simp), add_zero]
    rw [Finset.filter_mem_eq_inter]
  rw [edead, edead] at hsr'
  have h0 := hres0 i hires
  have hrr' : q.rowRecord t r res (Finset.range q.length) i ≤ (C + 1) * power t (delta / 2000) :=
    (le_abs_self _).trans (hrowb i)
  calc _ ≤ _ := hsr'
    _ ≤ θ ^ 2 * rowCap t + rowCap t * ((C + 1) * power t (delta / 2000)) :=
        add_le_add h0 (mul_le_mul_of_nonneg_left hrr' hrc)
    _ = (θ ^ 2 + (C + 1) * power t (delta / 2000)) * rowCap t := by ring

end AndersonAC.AgentS78send
