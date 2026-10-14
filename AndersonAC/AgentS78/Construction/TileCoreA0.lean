import AndersonAC.AgentS78.Construction.TileCoreA3
import AndersonAC.AgentS78.Construction.TileBlockMeasurable
import AndersonAC.AgentS78.Construction.MachineRunProof
import AndersonAC.AgentS78.Construction.TileTrialHalt

/-!
# the first trial is the slot recursion. `tileSlotDescription_proof : TileSlotDescriptionStatement`:
the block-local run of `tileBlock` from a non-aborted record, while in its first trial,
reveals the order `π_{j,T,0}` slot by slot and performs exactly the steps of `slotSeq`
(TileCore.lean); it fails iff `slotSeq` fails, and the exposed sites are distinct.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw querySigns)

/-! ## The site order -/

section SiteAt
variable {d m : ℕ}

theorem siteAt_some (S : Finset (Torus d m)) (v : ℕ) (hv : v < S.card) :
    ∃ i ∈ S, siteAt S v = some i := by
  unfold siteAt
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hlen : L.length = S.card := by rw [hL, Finset.length_sort, Finset.card_map]
  have hv' : v < L.length := hlen ▸ hv
  rw [List.getElem?_eq_getElem hv']
  have hmem : L[v] ∈ S.map (siteRank d m).toEmbedding :=
    (Finset.mem_sort _).mp (List.getElem_mem hv')
  obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hmem
  refine ⟨a, ha, ?_⟩
  simp only [Option.map_some, Option.some.injEq]
  rw [← hae]; simp

theorem siteAt_inj (S : Finset (Torus d m)) {v v' : ℕ} {i : Torus d m}
    (h : siteAt S v = some i) (h' : siteAt S v' = some i) : v = v' := by
  unfold siteAt at h h'
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hnd : L.Nodup := Finset.sort_nodup _ _
  rcases hv : L[v]? with _ | a
  · rw [hv] at h; cases h
  rcases hv' : L[v']? with _ | a'
  · rw [hv'] at h'; cases h'
  rw [hv] at h; rw [hv'] at h'
  simp only [Option.map_some, Option.some.injEq] at h h'
  have haa : a = a' := (siteRank d m).symm.injective (h.trans h'.symm)
  subst haa
  obtain ⟨hvl, hva⟩ := List.getElem?_eq_some_iff.mp hv
  obtain ⟨hvl', hva'⟩ := List.getElem?_eq_some_iff.mp hv'
  exact (List.Nodup.getElem_inj_iff hnd).mp (hva.trans hva'.symm)

end SiteAt

section Slots
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

theorem tileSlot_spec (hM : TileOrderSizes P j T M) (k : ℕ) (hk : k < slotCount P j T)
    (ω : RandomSources (Torus d m) M) :
    ∃ h : k < M (tileOrderIndex j T 0),
      siteAt (tileSites (P.cover j) T) (ω.2 (tileOrderIndex j T 0) ⟨k, h⟩).val =
        some (tileSlot P j T M k ω) ∧ tileSlot P j T M k ω ∈ tileSites (P.cover j) T := by
  have h : k < M (tileOrderIndex j T 0) := by rw [hM 0]; exact hk
  refine ⟨h, ?_⟩
  have hv : (ω.2 (tileOrderIndex j T 0) ⟨k, h⟩).val < (tileSites (P.cover j) T).card := by
    have h1 := (ω.2 (tileOrderIndex j T 0) ⟨k, h⟩).isLt
    have h2 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
    omega
  obtain ⟨i, hi, hs⟩ := siteAt_some _ _ hv
  have ht : tileSlot P j T M k ω = i := by simp [tileSlot, h, hs]
  rw [ht]; exact ⟨hs, hi⟩

theorem tileSlot_inj (hM : TileOrderSizes P j T M) {k k' : ℕ} (hk : k < slotCount P j T)
    (hk' : k' < slotCount P j T) (ω : RandomSources (Torus d m) M)
    (h : tileSlot P j T M k ω = tileSlot P j T M k' ω) : k = k' := by
  obtain ⟨h1, hs1, -⟩ := tileSlot_spec P j T M hM k hk ω
  obtain ⟨h2, hs2, -⟩ := tileSlot_spec P j T M hM k' hk' ω
  rw [h] at hs1
  have := siteAt_inj _ hs1 hs2
  have := (ω.2 (tileOrderIndex j T 0)).injective (Fin.ext this)
  simpa using this

theorem tileRemaining_card (hM : TileOrderSizes P j T M) (k : ℕ) (hk : k ≤ slotCount P j T)
    (ω : RandomSources (Torus d m) M) :
    (tileRemaining P j T M k ω).card = slotCount P j T - k := by
  classical
  unfold tileRemaining
  have hsub : (Finset.range k).image (fun l => tileSlotF P j T M l ω) ⊆
      (tileSites (P.cover j) T).image (siteRank d m) := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
    have hl' : l < slotCount P j T := lt_of_lt_of_le (Finset.mem_range.mp hl) hk
    exact Finset.mem_image.mpr ⟨_, (tileSlot_spec P j T M hM l hl' ω).2.2, rfl⟩
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injective _ (siteRank d m).injective,
    Finset.card_image_of_injOn, Finset.card_range]
  intro l hl l' hl' h
  have hl1 : l < slotCount P j T := lt_of_lt_of_le (Finset.mem_range.mp hl) hk
  have hl2 : l' < slotCount P j T := lt_of_lt_of_le (Finset.mem_range.mp hl') hk
  exact tileSlot_inj P j T M hM hl1 hl2 ω ((siteRank d m).injective h)

end Slots

/-! ## The block run in its first trial -/

section Run
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

/-- Order answers count the block's own order queries. -/
theorem tile_count_eq (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) (o : ℕ) :
    (machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update k ω).2.count (Query.nextOrder o) =
      (localState M (tileBlock P j T) x k ω).2.orderCount o := by
  rw [MachineRunProof.machineRun_snd, tileBlock_orderCount, List.count_eq_length_filter, List.filter_map,
    List.length_map]
  congr 1
  refine List.filter_congr fun k' _ => ?_
  show decide (((tileBlock P j T).next (localState M (tileBlock P j T) x k' ω)) =
      Query.nextOrder o) = decide (_ ∧ _)
  generalize localState M (tileBlock P j T) x k' ω = s
  by_cases hh : s.2.halted = true
  · have : (tileBlock P j T).next s = Query.decision := by
      show (if s.2.halted = true then _ else _) = _; rw [if_pos hh]
    rw [this, tileBlock_halted, hh]; simp
  · have hf : s.2.halted = false := by simpa using hh
    rw [tileBlock_halted, hf]; simp

theorem slotSeq_none_mono (x : RunRecord d m) (ω : RandomSources (Torus d m) M) {a b : ℕ}
    (ha : slotSeq P j T M x a ω = none) (hab : a ≤ b) : slotSeq P j T M x b ω = none := by
  induction b, hab using Nat.le_induction with
  | base => exact ha
  | succ b _ ih =>
    rw [slotSeq_succ, ih]; split_ifs <;> rfl

theorem activeIn_active (x : RunRecord d m) (i : Torus d m) (h : activeIn P j T x i) :
    i ∈ x.endpoint.active := by
  unfold activeIn at h; tauto

/-- The block state is running the first trial, at slot `l`. -/
def SimR (x : RunRecord d m) (s : RunRecord d m × TileScratch d m)
    (ω : RandomSources (Torus d m) M) (l : ℕ) : Prop :=
  s.1 = x ∧ s.2.attempt = 0 ∧ s.2.halted = false ∧ s.2.firstFail = false ∧
  slotSeq P j T M x l ω = some s.2.seq ∧
  (∀ a, s.2.auxUsed (tileAuxIndex j T 0 a) = true → ∃ l' < l, tileSlot P j T M l' ω = a) ∧
  ((s.2.site = none ∧ s.2.orderCount (tileOrderIndex j T 0) = l ∧ l ≤ slotCount P j T) ∨
   (s.2.site = some (tileSlot P j T M l ω) ∧ s.2.orderCount (tileOrderIndex j T 0) = l + 1 ∧
     l < slotCount P j T ∧ tileSlot P j T M l ω ∈ x.endpoint.active ∧
     ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live))

/-- The three phases of the block-local run. -/
def Phase (x : RunRecord d m) (s : RunRecord d m × TileScratch d m)
    (ω : RandomSources (Torus d m) M) : Prop :=
  (∃ l, SimR P j T M x s ω l) ∨
  (s.2.halted = true ∧ s.2.firstFail = false ∧ slotSeq P j T M x (slotCount P j T) ω ≠ none) ∨
  (s.2.firstFail = true ∧ slotSeq P j T M x (slotCount P j T) ω = none)

open Classical in
/-- Step from an unexposed slot: reveal the next order entry (or accept after all slots). -/
theorem step_none (hM : TileOrderSizes P j T M) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (ω : RandomSources (Torus d m) M) (l : ℕ)
    (L : List (Query (Torus d m))) (hS : SimR P j T M x s ω l) (hsn : s.2.site = none)
    (hcount : L.count (Query.nextOrder (tileOrderIndex j T 0)) =
      s.2.orderCount (tileOrderIndex j T 0)) :
    Phase P j T M x ((tileBlock P j T).update s
      (localAnswer (Torus d m) M L ((tileBlock P j T).next s) ω)) ω := by
  obtain ⟨h1, ha, hh, hf, hq, haux, hsite⟩ := hS
  have hoc : s.2.orderCount (tileOrderIndex j T 0) = l ∧ l ≤ slotCount P j T := by
    rcases hsite with ⟨_, h2, h3⟩ | ⟨h2, -⟩
    · exact ⟨h2, h3⟩
    · rw [hsn] at h2; cases h2
  rw [tileBlock_next_running P j T s hh, tileBlock_update_running P j T s _ hh]
  by_cases hlt : l < slotCount P j T
  · have hq0 : tileQuery P j T s = Query.nextOrder (tileOrderIndex j T 0) := by
      unfold tileQuery; rw [hsn]; simp only; rw [ha, hoc.1, if_pos hlt]
    rw [hq0]
    obtain ⟨hM0, hsa, hmem⟩ := tileSlot_spec P j T M hM l hlt ω
    have hc : L.count (Query.nextOrder (tileOrderIndex j T 0)) = l := hcount.trans hoc.1
    have hans : (localAnswer (Torus d m) M L (Query.nextOrder (tileOrderIndex j T 0)) ω).2 =
        some (ω.2 (tileOrderIndex j T 0) ⟨l, hM0⟩).val := by
      simp only [localAnswer]
      rw [dif_pos (by rw [hc]; exact hM0)]
      simp [hc]
    have hexp : exposedSite P j T (s.1, logQuery (Query.nextOrder (tileOrderIndex j T 0)) s.2)
        (some (ω.2 (tileOrderIndex j T 0) ⟨l, hM0⟩).val) =
        if tileSlot P j T M l ω ∈ x.endpoint.active ∧
          ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live
        then some (tileSlot P j T M l ω) else none := by
      simp only [exposedSite, hsa, h1, logQuery]
    simp only [tileStep, hans, hexp]
    have hoc' : (logQuery (Query.nextOrder (tileOrderIndex j T 0)) s.2).orderCount
        (tileOrderIndex j T 0) = l + 1 := by simp [logQuery, hoc.1]
    have haux' : ∀ a, (logQuery (Query.nextOrder (tileOrderIndex j T 0)) s.2).auxUsed a =
        s.2.auxUsed a := by intro a; simp [logQuery]
    by_cases hal0 : tileSlot P j T M l ω ∈ x.endpoint.active ∧
        ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live
    · rw [if_pos hal0]
      refine Or.inl ⟨l, h1, ha, hh, hf, hq, fun a ha' => haux a (by rw [← haux']; exact ha'),
        Or.inr ⟨rfl, hoc', hlt, hal0.1, hal0.2⟩⟩
    · have hal : ¬ (activeIn P j T x (tileSlot P j T M l ω) ∧
          ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live) :=
        fun h => hal0 ⟨activeIn_active P j T x _ h.1, h.2⟩
      rw [if_neg hal0]
      refine Or.inl ⟨l + 1, h1, ha, hh, hf, ?_, fun a ha' => ?_, Or.inl ⟨rfl, hoc', hlt⟩⟩
      · rw [slotSeq_succ, if_pos hlt, hq]
        simp only [Option.bind_some]
        rw [slotStep_eq, if_neg hal]
        rfl
      · obtain ⟨l', hl', hl'e⟩ := haux a (by rw [← haux']; exact ha')
        exact ⟨l', by omega, hl'e⟩
  · have hlN : l = slotCount P j T := le_antisymm hoc.2 (not_lt.mp hlt)
    have hq0 : tileQuery P j T s = Query.decision := by
      unfold tileQuery; rw [hsn]; simp only; rw [ha, hoc.1, if_neg hlt]
    rw [hq0]
    refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
    · simp [tileStep, logQuery, hsn]
    · simp [tileStep, logQuery, hsn, hf]
    · rw [← hlN, hq]; simp

theorem failTrial_firstFail (s : RunRecord d m × TileScratch d m) :
    (failTrial P j T s).2.firstFail = true := by
  unfold failTrial; split_ifs <;> rfl

open Classical in
/-- A scalar step at the exposed site of slot `l`. -/
theorem step_scalar (hM : TileOrderSizes P j T M) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (ω : RandomSources (Torus d m) M) (l : ℕ)
    (L : List (Query (Torus d m))) (h1 : s.1 = x) (ha : s.2.attempt = 0)
    (hh : s.2.halted = false) (hf : s.2.firstFail = false)
    (hq : slotSeq P j T M x l ω = some s.2.seq)
    (haux : ∀ a, s.2.auxUsed (tileAuxIndex j T 0 a) = true → ∃ l' < l, tileSlot P j T M l' ω = a)
    (hss : s.2.site = some (tileSlot P j T M l ω))
    (hoc : s.2.orderCount (tileOrderIndex j T 0) = l + 1) (hlt : l < slotCount P j T)
    (hal : activeIn P j T x (tileSlot P j T M l ω) ∧
      ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live)
    (c : Query (Torus d m)) (hc1 : ∀ o, c ≠ Query.nextOrder o) (hc2 : c ≠ Query.decision)
    (hz : tileIncrement P j c (localAnswer (Torus d m) M L c ω) =
      tileZeta P j T M x (tileSlot P j T M l ω) ω)
    (hauxc : ∀ a, (logQuery c s.2).auxUsed (tileAuxIndex j T 0 a) = true →
      a = tileSlot P j T M l ω ∨ s.2.auxUsed (tileAuxIndex j T 0 a) = true) :
    Phase P j T M x (tileStep P j T (s.1, logQuery c s.2) c (localAnswer (Torus d m) M L c ω)) ω := by
  have hts : tileStep P j T (s.1, logQuery c s.2) c (localAnswer (Torus d m) M L c ω) =
      scalarStep P j T (s.1, logQuery c s.2) (tileSlot P j T M l ω)
        (tileIncrement P j c (localAnswer (Torus d m) M L c ω)) := by
    have hsite : (logQuery c s.2).site = some (tileSlot P j T M l ω) := hss
    rcases c with ⟨i', h⟩ | k | ⟨i', h⟩ | o | _
    · simp only [tileStep]; rw [hsite]
    · simp only [tileStep]; rw [hsite]
    · simp only [tileStep]; rw [hsite]
    · exact absurd rfl (hc1 o)
    · exact absurd rfl hc2
  have hlogc : (logQuery c s.2).orderCount = s.2.orderCount := by
    funext o; simp [logQuery, hc1 o]
  rw [hts, hz]
  subst h1
  unfold scalarStep
  simp only
  set ξ := tileZeta P j T M s.1 (tileSlot P j T M l ω) ω / Real.sqrt (sweepW P.u m j) with hξ
  have hcand : extendSeq (logQuery c s.2).seq
      (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        ((logQuery c s.2).seq.state (logQuery c s.2).seq.length)
        (tileSlot P j T M l ω, false) ξ) (tileSlot P j T M l ω, false) ξ =
      candidate P j s.1 s.2.seq (tileSlot P j T M l ω) (tileXi P j T M s.1 l ω) := rfl
  have hden : stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
      ((logQuery c s.2).seq.state (logQuery c s.2).seq.length) (tileSlot P j T M l ω, false) ξ =
      stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (tileSlot P j T M l ω, false) (tileXi P j T M s.1 l ω) :=
    rfl
  rw [hcand, hden]
  have hnext : slotSeq P j T M s.1 (l + 1) ω =
      slotStep P j T s.1 s.2.seq (tileSlot P j T M l ω) (tileXi P j T M s.1 l ω) := by
    rw [slotSeq_succ, if_pos hlt, hq]; rfl
  split_ifs with hok
  · refine Or.inl ⟨l + 1, rfl, ha, hh, hf, ?_, fun a ha' => ?_, Or.inl ⟨rfl, ?_, hlt⟩⟩
    · rw [hnext, slotStep_eq, if_pos hal, if_pos hok]
    · rcases hauxc a ha' with rfl | h
      · exact ⟨l, Nat.lt_succ_self l, rfl⟩
      · obtain ⟨l', hl', he⟩ := haux a h
        exact ⟨l', by omega, he⟩
    · show (logQuery c s.2).orderCount (tileOrderIndex j T 0) = l + 1
      rw [hlogc, hoc]
  · refine Or.inr (Or.inr ⟨failTrial_firstFail P j T _, ?_⟩)
    have hnone : slotSeq P j T M s.1 (l + 1) ω = none := by
      rw [hnext, slotStep_eq, if_pos hal, if_neg hok]
    exact slotSeq_none_mono P j T M s.1 ω hnone hlt

open Classical in
/-- Step from an exposed slot. -/
theorem step_some (hM : TileOrderSizes P j T M) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (ω : RandomSources (Torus d m) M) (l : ℕ)
    (L : List (Query (Torus d m))) (hS : SimR P j T M x s ω l)
    (hss : s.2.site = some (tileSlot P j T M l ω)) :
    Phase P j T M x ((tileBlock P j T).update s
      (localAnswer (Torus d m) M L ((tileBlock P j T).next s) ω)) ω := by
  obtain ⟨h1, ha, hh, hf, hq, haux, hsite⟩ := hS
  obtain ⟨hoc, hlt, hal'⟩ : s.2.orderCount (tileOrderIndex j T 0) = l + 1 ∧
      l < slotCount P j T ∧ (tileSlot P j T M l ω ∈ x.endpoint.active ∧
        ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live) := by
    rcases hsite with ⟨h2, -⟩ | ⟨-, h2, h3, h4, h5⟩
    · rw [hss] at h2; cases h2
    · exact ⟨h2, h3, h4, h5⟩
  rw [tileBlock_next_running P j T s hh, tileBlock_update_running P j T s _ hh]
  by_cases hact0 : activeIn P j T x (tileSlot P j T M l ω)
  swap
  · -- an inactive exposed site is skipped by a decision step
    have hq0 : tileQuery P j T s = Query.decision := by
      unfold tileQuery; rw [hss]; simp only; rw [if_neg (by rw [h1]; exact hact0)]
    rw [hq0]
    have hsite' : (logQuery Query.decision s.2).site = some (tileSlot P j T M l ω) := hss
    have hstep : tileStep P j T (s.1, logQuery Query.decision s.2) Query.decision
        (localAnswer (Torus d m) M L Query.decision ω) =
        (s.1, { logQuery Query.decision s.2 with site := none }) := by
      simp only [tileStep]; rw [hsite']
    rw [hstep]
    have hnal : ¬ (activeIn P j T x (tileSlot P j T M l ω) ∧
        ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live) :=
      fun h => hact0 h.1
    refine Or.inl ⟨l + 1, h1, ha, hh, hf, ?_, fun a ha' => ?_, Or.inl ⟨?_, ?_, hlt⟩⟩
    · show slotSeq P j T M x (l + 1) ω = some s.2.seq
      rw [slotSeq_succ, if_pos hlt, hq]
      simp only [Option.bind_some]
      rw [slotStep_eq, if_neg hnal]
    · have ha'' : s.2.auxUsed (tileAuxIndex j T 0 a) = true := by
        simpa [logQuery] using ha'
      obtain ⟨l', hl', he⟩ := haux a ha''
      exact ⟨l', by omega, he⟩
    · rfl
    · simp [logQuery, hoc]
  have hal : activeIn P j T x (tileSlot P j T M l ω) ∧
      ((tileSlot P j T M l ω, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live :=
    ⟨hact0, hal'.2⟩
  set i := tileSlot P j T M l ω with hi
  have hfree : s.2.auxUsed (tileAuxIndex j T 0 i) = false := by
    by_contra hc
    obtain ⟨l', hl', he⟩ := haux i (by simpa using hc)
    have := tileSlot_inj P j T M hM (by omega) hlt ω he
    omega
  have hact : activeIn P j T s.1 i := h1 ▸ hal.1
  have hans : ∀ c : Query (Torus d m), ∀ z ∈ querySigns (Torus d m) c,
      answeredSign (localAnswer (Torus d m) M L c ω) z = ω.1 z := by
    intro c z hz; simp [answeredSign, localAnswer, hz]
  by_cases hpend : i ∈ x.pending
  · -- designated auxiliary sign
    have hq0 : tileQuery P j T s = Query.auxiliary (tileAuxIndex j T 0 i) := by
      unfold tileQuery; rw [hss]; simp only
      rw [if_pos hact, if_neg (by simp [usesTrue, h1, hpend]), ha, hfree]; rfl
    rw [hq0]
    refine step_scalar P j T M hM x s ω l L h1 ha hh hf hq haux hss hoc hlt hal _
      (fun o h => by cases h) (fun h => by cases h) ?_ ?_
    · rw [← hi, tileZeta, if_pos hal.1, if_neg (by simpa using hpend)]
      simp only [tileIncrement]
      rw [hans _ _ (by simp [querySigns])]
    · intro a hau
      simp only [logQuery, Bool.or_eq_true, decide_eq_true_eq] at hau
      rcases hau with h | h
      · exact Or.inr h
      · left
        exact ((tileAuxIndex_injective (Query.auxiliary.inj h)).2.2.2).symm
  · have hu : usesTrue s i := ⟨ha, by rw [h1]; exact hpend⟩
    by_cases hfin : IsFinalSweep m j
    · have hq0 : tileQuery P j T s = Query.trueSuffix i (x.prefixLength i) := by
        unfold tileQuery; rw [hss]; simp only
        rw [if_pos hact, if_pos hu, if_pos hfin, h1]
      rw [hq0]
      refine step_scalar P j T M hM x s ω l L h1 ha hh hf hq haux hss hoc hlt hal _
        (fun o h => by cases h) (fun h => by cases h) ?_ ?_
      · rw [← hi, tileZeta, if_pos hal.1, if_pos hpend, if_pos hfin]
        simp only [tileIncrement]
        unfold S2.binarySuffix
        congr 1; funext k
        simp only
        rw [hans (Query.trueSuffix i (x.prefixLength i)) (Sum.inl (i, x.prefixLength i + k))
          (by simp [querySigns])]
      · intro a hau
        simp only [logQuery, Bool.or_eq_true, decide_eq_true_eq] at hau
        rcases hau with h | h
        · exact Or.inr h
        · cases h
    · have hq0 : tileQuery P j T s = Query.trueDigit i (x.prefixLength i) := by
        unfold tileQuery; rw [hss]; simp only
        rw [if_pos hact, if_pos hu, if_neg hfin, h1]
      rw [hq0]
      refine step_scalar P j T M hM x s ω l L h1 ha hh hf hq haux hss hoc hlt hal _
        (fun o h => by cases h) (fun h => by cases h) ?_ ?_
      · rw [← hi, tileZeta, if_pos hal.1, if_pos hpend, if_neg hfin]
        simp only [tileIncrement]
        rw [hans _ _ (by simp [querySigns])]
      · intro a hau
        simp only [logQuery, Bool.or_eq_true, decide_eq_true_eq] at hau
        rcases hau with h | h
        · exact Or.inr h
        · cases h

/-- Every state of the block-local run from a non-aborted record is in one of the phases. -/
theorem phase_all (hM : TileOrderSizes P j T M) (x : RunRecord d m) (hab : x.aborted = false)
    (ω : RandomSources (Torus d m) M) :
    ∀ k, Phase P j T M x (localState M (tileBlock P j T) x k ω) ω := by
  intro k
  induction k with
  | zero =>
    rw [localState_zero]
    have he : (tileBlock P j T).enter x = (x, initScratch x) := by
      simp [tileBlock, hab]
    rw [he]
    refine Or.inl ⟨0, rfl, rfl, rfl, rfl, rfl, fun a ha => ?_, Or.inl ⟨rfl, rfl, Nat.zero_le _⟩⟩
    simp [initScratch] at ha
  | succ k ih =>
    rw [localState_succ]
    set s := localState M (tileBlock P j T) x k ω with hs
    rcases ih with ⟨l, hS⟩ | ⟨hh, hf, hn⟩ | ⟨hf, hn⟩
    · rcases hS.2.2.2.2.2.2 with ⟨hsn, -⟩ | ⟨hss, -⟩
      · exact step_none P j T M hM x s ω l _ hS hsn (tile_count_eq P j T M x k ω _)
      · exact step_some P j T M hM x s ω l _ hS hss
    · rw [tileBlock_update_halted P j T s _ hh]
      exact Or.inr (Or.inl ⟨hh, hf, hn⟩)
    · refine Or.inr (Or.inr ⟨?_, hn⟩)
      by_cases hh : s.2.halted = true
      · rw [tileBlock_update_halted P j T s _ hh]; exact hf
      · have hh' : s.2.halted = false := by simpa using hh
        rw [tileBlock_update_running P j T s _ hh']
        rcases (tileStep_keeps P j T (s.1, logQuery (tileQuery P j T s) s.2) (tileQuery P j T s)
          _).2 with ⟨_, _, e3, _⟩ | ⟨_, _, e3⟩ | ⟨_, e2, _⟩
        · rw [e3]; exact hf
        · exact e3 hf
        · exact e2

end Run

/-- **slot recursion.** -/
theorem tileSlotDescription_proof : TileSlotDescriptionStatement := by
  intro d m P j T M x hM hab
  refine ⟨?_, fun k hk ω => tileRemaining_card P j T M hM k hk ω⟩
  ext ω
  simp only [localFirstFail, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, -, hff⟩
    change (localState M (tileBlock P j T) x k ω).2.firstFail = true at hff
    rcases phase_all P j T M hM x hab ω k with ⟨l, hS⟩ | ⟨-, hf', -⟩ | ⟨-, hnone⟩
    · rw [hS.2.2.2.1] at hff; cases hff
    · rw [hf'] at hff; cases hff
    · exact hnone
  · intro hnone
    have hex : ∃ k, (localState M (tileBlock P j T) x k ω).2.firstFail = true := by
      by_contra hne
      push_neg at hne
      have hrun : ∀ k, (localState M (tileBlock P j T) x k ω).2.halted = false ∧
          (localState M (tileBlock P j T) x k ω).2.attempt = 0 := by
        intro k
        rcases phase_all P j T M hM x hab ω k with ⟨l, hS⟩ | ⟨-, -, hn⟩ | ⟨hf, -⟩
        · exact ⟨hS.2.2.1, hS.2.1⟩
        · exact absurd hnone hn
        · exact absurd hf (by simp [hne k])
      have h := (tile_steps_le P j T M x ω (2 * tileN P j T + 1)
        (fun k' _ => (hrun k').1)).1
      rw [(hrun _).2] at h
      omega
    classical
    refine ⟨Nat.find hex, fun k' hk' => ?_, ?_⟩
    · have hf' : (localState M (tileBlock P j T) x k' ω).2.firstFail = false := by
        have := Nat.find_min hex hk'; simpa using this
      rw [tileBlock_halted]
      rcases phase_all P j T M hM x hab ω k' with ⟨l, hS⟩ | ⟨-, -, hn⟩ | ⟨hf, -⟩
      · exact hS.2.2.1
      · exact absurd hnone hn
      · rw [hf'] at hf; cases hf
    · exact Nat.find_spec hex






end AndersonAC.AgentS78
