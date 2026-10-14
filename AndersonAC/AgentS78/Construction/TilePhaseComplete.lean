import AndersonAC.AgentS78.Construction.TilePhaseRun

/-!
# completeness of accepted trials on real answers. Proof of `TileCompleteStatement` (TilePhaseRun.lean): along real
local answers, the `v`-th order answer of trial `a` is `π_{j,T,a}(v)`, a permutation of the
`|T|` positions (`M (tileOrderIndex j T a) = |T|`), and `siteAt` is a bijection from the
positions onto the sites of `T`. A trial is accepted only after `|T|` order answers, and every
revealed active site is deleted before the next order query (05:338–344). Hence an accepted
trial has deleted the bit port of every active site of `T`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-! ## `siteAt` is a bijection from positions onto the set -/

section SiteAt

theorem siteAt_mem' (S : Finset (Torus d m)) {v : ℕ} {i : Torus d m}
    (h : siteAt S v = some i) : i ∈ S ∧ v < S.card := by
  unfold siteAt at h
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hlen : L.length = S.card := by rw [hL, Finset.length_sort, Finset.card_map]
  rcases hv : L[v]? with _ | a
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Option.map_some, Option.some.injEq] at h
  obtain ⟨hvl, hva⟩ := List.getElem?_eq_some_iff.mp hv
  refine ⟨?_, hlen ▸ hvl⟩
  have hmem : L[v] ∈ S.map (siteRank d m).toEmbedding := (Finset.mem_sort _).mp (List.getElem_mem hvl)
  rw [hva] at hmem
  obtain ⟨b, hb, hbe⟩ := Finset.mem_map.mp hmem
  rw [← h, ← hbe]; simpa using hb

theorem siteAt_inj' (S : Finset (Torus d m)) {v v' : ℕ} {i : Torus d m}
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

theorem siteAt_surj (S : Finset (Torus d m)) {i : Torus d m} (hi : i ∈ S) :
    ∃ p < S.card, siteAt S p = some i := by
  unfold siteAt
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hlen : L.length = S.card := by rw [hL, Finset.length_sort, Finset.card_map]
  have hmem : siteRank d m i ∈ L := by
    rw [hL, Finset.mem_sort]; exact Finset.mem_map_of_mem _ hi
  obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨p, hlen ▸ hp, ?_⟩
  rw [List.getElem?_eq_getElem hp, hpe]
  simp

end SiteAt

/-! ## Order counts are list counts; order answers are the permutation -/

section Answers
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

theorem tile_list_count (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) (o : ℕ) :
    ((machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
      (tileBlock P j T).update k ω).2).count (Query.nextOrder o) =
      (localState M (tileBlock P j T) x k ω).2.orderCount o := by
  induction k with
  | zero =>
    show ([] : List (Query (Torus d m))).count _ = _
    simp only [List.count_nil, localState_zero]
    simp only [tileBlock]; split_ifs <;> rfl
  | succ k ih =>
    rw [machineRun_succ, List.count_append, ih, localState_succ]
    set s := localState M (tileBlock P j T) x k ω with hs
    have hs1 : (machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update k ω).1 = s := rfl
    rw [hs1]
    by_cases hh : s.2.halted = true
    · rw [tileBlock_update_halted P j T s _ hh]
      simp [tileBlock, hh]
    · have hf : s.2.halted = false := by simpa using hh
      rw [tileBlock_update_running P j T s _ hf, (tileStep_keeps P j T _ _ _).1.orderCount,
        tileBlock_next_running P j T s hf]
      by_cases hq : tileQuery P j T s = Query.nextOrder o
      · simp [hq, logQuery]
      · simp [hq, logQuery, List.count_singleton]

/-- The `v`-th entry of the order `π_{j,T,a}` (a position of the tile). -/
def orderPos (ω : RandomSources (Torus d m) M) (a v : ℕ) : ℕ :=
  if h : v < M (tileOrderIndex j T a) then (ω.2 (tileOrderIndex j T a) ⟨v, h⟩).val else 0

theorem orderPos_lt (hM : TileOrderSizes P j T M) (ω : RandomSources (Torus d m) M) (a v : ℕ)
    (hv : v < (tileSites (P.cover j) T).card) :
    orderPos P j T M ω a v < (tileSites (P.cover j) T).card := by
  have hv' : v < M (tileOrderIndex j T a) := by rw [hM a]; exact hv
  simp only [orderPos, hv', dif_pos]
  have := (ω.2 (tileOrderIndex j T a) ⟨v, hv'⟩).isLt
  exact lt_of_lt_of_eq this (hM a)

theorem orderPos_inj (hM : TileOrderSizes P j T M) (ω : RandomSources (Torus d m) M) (a : ℕ)
    {v v' : ℕ} (hv : v < (tileSites (P.cover j) T).card)
    (hv' : v' < (tileSites (P.cover j) T).card)
    (h : orderPos P j T M ω a v = orderPos P j T M ω a v') : v = v' := by
  have h1 : v < M (tileOrderIndex j T a) := by rw [hM a]; exact hv
  have h2 : v' < M (tileOrderIndex j T a) := by rw [hM a]; exact hv'
  simp only [orderPos, h1, h2, dif_pos] at h
  have := (ω.2 (tileOrderIndex j T a)).injective (Fin.ext h)
  simpa using this

theorem orderPos_surj (hM : TileOrderSizes P j T M) (ω : RandomSources (Torus d m) M) (a : ℕ)
    {p : ℕ} (hp : p < (tileSites (P.cover j) T).card) :
    ∃ v < (tileSites (P.cover j) T).card, orderPos P j T M ω a v = p := by
  have hp' : p < M (tileOrderIndex j T a) := by rw [hM a]; exact hp
  set v := ((ω.2 (tileOrderIndex j T a)).symm ⟨p, hp'⟩) with hv
  have hvl : v.val < M (tileOrderIndex j T a) := v.isLt
  refine ⟨v.val, by rw [← hM a]; exact hvl, ?_⟩
  simp only [orderPos, hvl, dif_pos, Fin.eta]
  rw [hv, Equiv.apply_symm_apply]

/-- The answer to an order query of the running block is the next entry of the order. -/
theorem tile_order_answer (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) (a : ℕ)
    (hM : TileOrderSizes P j T M)
    (hc : (localState M (tileBlock P j T) x k ω).2.orderCount (tileOrderIndex j T a) <
      (tileSites (P.cover j) T).card) :
    (localAnswer (Torus d m) M (machineRun (Torus d m) M ((tileBlock P j T).enter x)
      (tileBlock P j T).next (tileBlock P j T).update k ω).2
      (Query.nextOrder (tileOrderIndex j T a)) ω).2 =
      some (orderPos P j T M ω a
        ((localState M (tileBlock P j T) x k ω).2.orderCount (tileOrderIndex j T a))) := by
  have hcnt := tile_list_count P j T M x k ω (tileOrderIndex j T a)
  have hlt : (localState M (tileBlock P j T) x k ω).2.orderCount (tileOrderIndex j T a) <
      M (tileOrderIndex j T a) := by rw [hM a]; exact hc
  simp only [localAnswer, hcnt, hlt, dif_pos, orderPos]

end Answers

end AndersonAC.AgentS78

/-! ## The completeness invariant of a running trial -/

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

section Inv
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
  (ω : RandomSources (Torus d m) M) (x : RunRecord d m)

theorem siteAt_some' (S : Finset (Torus d m)) (v : ℕ) (hv : v < S.card) :
    ∃ i, siteAt S v = some i := by
  unfold siteAt
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hlen : L.length = S.card := by rw [hL, Finset.length_sort, Finset.card_map]
  have hv' : v < L.length := hlen ▸ hv
  rw [List.getElem?_eq_getElem hv']
  exact ⟨_, rfl⟩

/-- The order count of the current trial. -/
abbrev curCount (s : RunRecord d m × TileScratch d m) : ℕ :=
  s.2.orderCount (tileOrderIndex j T s.2.attempt)

/-- **Completeness invariant** of a running state. -/
structure CompInv (s : RunRecord d m × TileScratch d m) : Prop where
  ep : s.1.endpoint = x.endpoint
  te : s.1.terminal = x.terminal
  le : curCount P j T s ≤ (tileSites (P.cover j) T).card
  fresh : ∀ a' > s.2.attempt, s.2.orderCount (tileOrderIndex j T a') = 0
  rev : ∀ v < curCount P j T s, ∀ i, siteAt (tileSites (P.cover j) T)
      (orderPos P j T M ω s.2.attempt v) = some i → i ∈ x.endpoint.active →
    ((i, false) : Port d m) ∉ (s.2.seq.state s.2.seq.length).live ∨
      (s.2.site = some i ∧ v + 1 = curCount P j T s)
  cur : ∀ i, s.2.site = some i → 0 < curCount P j T s ∧
    siteAt (tileSites (P.cover j) T) (orderPos P j T M ω s.2.attempt (curCount P j T s - 1)) =
      some i ∧ i ∈ x.endpoint.active ∧
    ((i, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live
  aux : ∀ a' (i : Torus d m), s.2.auxUsed (tileAuxIndex j T a' i) = true →
    a' < s.2.attempt ∨ (a' = s.2.attempt ∧ ∃ v < curCount P j T s,
      siteAt (tileSites (P.cover j) T) (orderPos P j T M ω s.2.attempt v) = some i ∧
      ¬ (s.2.site = some i ∧ v + 1 = curCount P j T s))

theorem compInv_enter (hab : x.aborted = false) :
    CompInv P j T M ω x ((tileBlock P j T).enter x) := by
  have he : (tileBlock P j T).enter x = (x, initScratch x) := by simp [tileBlock, hab]
  rw [he]
  refine ⟨rfl, rfl, by simp [initScratch, curCount], fun _ _ => rfl,
    fun v hv => by simp [initScratch, curCount] at hv,
    fun i hi => by simp [initScratch] at hi, fun a' i hi => by simp [initScratch] at hi⟩

/-- Two revealed positions of one trial with the same site are equal. -/
theorem revealed_inj (hM : TileOrderSizes P j T M) (a : ℕ) {v v' : ℕ} {i : Torus d m}
    (hv : v < (tileSites (P.cover j) T).card) (hv' : v' < (tileSites (P.cover j) T).card)
    (h : siteAt (tileSites (P.cover j) T) (orderPos P j T M ω a v) = some i)
    (h' : siteAt (tileSites (P.cover j) T) (orderPos P j T M ω a v') = some i) : v = v' :=
  orderPos_inj P j T M hM ω a hv hv' (siteAt_inj' _ h h')

end Inv

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

section LogQuery
variable (q : Query (Torus d m)) (sc : TileScratch d m)
@[simp] theorem logQuery_orderCount (o : ℕ) :
    (logQuery q sc).orderCount o = sc.orderCount o + if q = Query.nextOrder o then 1 else 0 := rfl
@[simp] theorem logQuery_auxUsed (k : ℕ) :
    (logQuery q sc).auxUsed k = (sc.auxUsed k || decide (q = Query.auxiliary k)) := rfl
@[simp] theorem logQuery_seq : (logQuery q sc).seq = sc.seq := rfl
@[simp] theorem logQuery_attempt : (logQuery q sc).attempt = sc.attempt := rfl
@[simp] theorem logQuery_site : (logQuery q sc).site = sc.site := rfl
@[simp] theorem logQuery_halted : (logQuery q sc).halted = sc.halted := rfl
end LogQuery

section Step
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
  (ω : RandomSources (Torus d m) M) (x : RunRecord d m)

/-- The conclusion at a halt. -/
def HaltComplete (y : RunRecord d m) : Prop :=
  y.aborted = false → ∀ i ∈ tileSites (P.cover j) T, i ∈ x.endpoint.active →
    ((i, false) : Port d m) ∉ (y.sweep.state y.sweep.length).live

/-- After a scalar slot at the current site `i` the invariant holds again (or the trial
halts aborted). -/
theorem compInv_scalar (hM : TileOrderSizes P j T M) (s : RunRecord d m × TileScratch d m)
    (hrun : s.2.halted = false) (hI : CompInv P j T M ω x s) (i : Torus d m)
    (hsite : s.2.site = some i) (q : Query (Torus d m))
    (hqa : ∀ a' i', q = Query.auxiliary (tileAuxIndex j T a' i') →
      a' = s.2.attempt ∧ i' = i)
    (hqo : ∀ o, q ≠ Query.nextOrder o) (ζ : ℝ) :
    let s' := scalarStep P j T (s.1, logQuery q s.2) i ζ
    (s'.2.halted = false → CompInv P j T M ω x s') ∧
      (s'.2.halted = true → HaltComplete P j T x s'.1) := by
  intro s'
  have hcur := hI.cur i hsite
  have hlog : logQuery q s.2 =
      { s.2 with auxUsed := fun k => s.2.auxUsed k || decide (q = Query.auxiliary k) } := by
    simp only [logQuery]; congr; funext o; simp [hqo o]
  unfold s' scalarStep
  rw [hlog]
  dsimp only
  split_ifs with hok
  · -- success: the bit port of `i` is deleted
    refine ⟨fun _ => ?_, fun hh => by simp [hrun] at hh⟩
    refine ⟨hI.ep, hI.te, hI.le, hI.fresh, ?_, ?_, ?_⟩
    · intro v hv i' hi' hia'
      left
      intro hl
      have hl2 : ((i', false) : Port d m) ∈
          (s.2.seq.state s.2.seq.length).live.erase ((i, false) : Port d m) := by
        simpa [extendSeq, stepLive] using hl
      have hl' := Finset.mem_erase.mp hl2
      rcases hI.rev v hv i' hi' hia' with h | ⟨h1, -⟩
      · exact h hl'.2
      · rw [hsite] at h1; cases h1; exact hl'.1 rfl
    · intro i' hi'; simp at hi'
    · intro a' i' hau
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hau
      rcases hau with hau | hau
      · rcases hI.aux a' i' hau with h | ⟨h1, v, hv, h2, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, v, hv, h2, fun h' => by simp at h'⟩
      · obtain ⟨rfl, rfl⟩ := hqa a' i' hau
        exact Or.inr ⟨rfl, curCount P j T s - 1,
          (by have := hcur.1; show curCount P j T s - 1 < curCount P j T s; omega), hcur.2.1,
          fun h' => by simp at h'⟩
  · -- failure
    unfold failTrial
    dsimp only
    by_cases hlate : m / 2 < j
    · simp only [hlate, if_true]
      refine ⟨fun hh => by simp at hh, fun _ hab => by simp at hab⟩
    · simp only [hlate, if_false]
      refine ⟨fun _ => ?_, fun hh => by simp [trialScratch, hrun] at hh⟩
      have hep : (if s.2.attempt = 0 then
          markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1 else s.1).endpoint =
          x.endpoint := by
        split_ifs <;> simp [markTile, hI.ep]
      have h0 := hI.fresh (s.2.attempt + 1) (Nat.lt_succ_self _)
      have hte : (if s.2.attempt = 0 then
          markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1 else s.1).terminal =
          x.terminal := by
        split_ifs <;> simp [markTile, hI.te]
      refine ⟨hep, hte, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [curCount, trialScratch]; rw [h0]; exact Nat.zero_le _
      · intro a' ha'
        simp only [trialScratch] at ha' ⊢
        exact hI.fresh a' (by omega)
      · intro v hv
        simp only [curCount, trialScratch] at hv
        rw [h0] at hv
        exact absurd hv (Nat.not_lt_zero v)
      · intro i' hi'; simp [trialScratch] at hi'
      · intro a' i' hau
        simp only [trialScratch, Bool.or_eq_true, decide_eq_true_eq] at hau ⊢
        left
        rcases hau with hau | hau
        · rcases hI.aux a' i' hau with h | ⟨h1, -⟩
          · omega
          · omega
        · obtain ⟨h1, -⟩ := hqa a' i' hau; omega

end Step

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

section Step2
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
  (ω : RandomSources (Torus d m) M) (x : RunRecord d m)

/-- **One step of the running block keeps the completeness invariant.** -/
theorem compInv_step (hM : TileOrderSizes P j T M)
    (hxt : ∀ i ∈ tileSites (P.cover j) T, i ∈ x.endpoint.active → i ∉ x.terminal)
    (s : RunRecord d m × TileScratch d m)
    (hrun : s.2.halted = false) (hI : CompInv P j T M ω x s) (a : Answer (Torus d m))
    (ha : ∀ o, tileQuery P j T s = Query.nextOrder o →
      a.2 = some (orderPos P j T M ω s.2.attempt (s.2.orderCount o))) :
    let s' := (tileBlock P j T).update s a
    (s'.2.halted = false → CompInv P j T M ω x s') ∧
      (s'.2.halted = true → HaltComplete P j T x s'.1) := by
  classical
  intro s'
  have hs' : s' = tileStep P j T (s.1, logQuery (tileQuery P j T s) s.2)
      (tileQuery P j T s) a := tileBlock_update_running P j T s a hrun
  clear_value s'
  subst hs'
  rcases hsite : s.2.site with _ | i
  · have hq : tileQuery P j T s =
        if s.2.orderCount (tileOrderIndex j T s.2.attempt) < (TS P j T).card then
          Query.nextOrder (tileOrderIndex j T s.2.attempt) else Query.decision := by
      unfold tileQuery; rw [hsite]
    by_cases hlt : s.2.orderCount (tileOrderIndex j T s.2.attempt) < (TS P j T).card
    · rw [if_pos hlt] at hq
      have ha' := ha _ hq
      obtain ⟨i₀, hi₀⟩ := siteAt_some' (TS P j T)
        (orderPos P j T M ω s.2.attempt (s.2.orderCount (tileOrderIndex j T s.2.attempt)))
        (orderPos_lt P j T M hM ω _ _ hlt)
      rw [hq]
      set o := tileOrderIndex j T s.2.attempt with ho
      set c := s.2.orderCount o with hc
      have hex1 : ∀ i', exposedSite P j T (s.1, logQuery (Query.nextOrder o) s.2) a.2 = some i' →
          i' = i₀ ∧ i₀ ∈ s.1.endpoint.active ∧
            ((i₀, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live := by
        intro i' h
        unfold exposedSite at h
        rw [ha'] at h
        simp only at h
        rw [hi₀] at h
        simp only at h
        split_ifs at h with hcd
        cases h; exact ⟨rfl, hcd.1, hcd.2⟩
      have hex2 : i₀ ∈ s.1.endpoint.active →
          ((i₀, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live →
          exposedSite P j T (s.1, logQuery (Query.nextOrder o) s.2) a.2 = some i₀ := by
        intro h1 h2
        unfold exposedSite
        rw [ha']
        simp only
        rw [hi₀]
        simp only
        split_ifs with hcd
        · rfl
        · exact absurd ⟨h1, h2⟩ hcd
      have hcnt : ∀ o', (logQuery (Query.nextOrder o) s.2).orderCount o' =
          s.2.orderCount o' + if o' = o then 1 else 0 := by
        intro o'; simp [eq_comm]
      have haux : ∀ k, (logQuery (Query.nextOrder o) s.2).auxUsed k = s.2.auxUsed k := by
        intro k; simp
      refine ⟨fun _ => ?_, fun hh => by simp [tileStep, hrun] at hh⟩
      simp only [tileStep]
      have hcur' : curCount P j T (s.1, { logQuery (Query.nextOrder o) s.2 with
          site := exposedSite P j T (s.1, logQuery (Query.nextOrder o) s.2) a.2 }) = c + 1 := by
        show (logQuery (Query.nextOrder o) s.2).orderCount o = c + 1
        rw [hcnt]; simp [hc]
      refine ⟨hI.ep, hI.te, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcur']; exact hlt
      · intro a' ha'
        show (logQuery (Query.nextOrder o) s.2).orderCount (tileOrderIndex j T a') = 0
        rw [hcnt]
        have hne : tileOrderIndex j T a' ≠ o := by
          intro he; have := (tileOrderIndex_injective he).2.2
          change a' > s.2.attempt at ha'; omega
        simp only [hne, if_false, add_zero]; exact hI.fresh a' ha'
      · intro v hv i' hi' hia'
        rw [hcur'] at hv ⊢
        change siteAt _ (orderPos P j T M ω s.2.attempt v) = some i' at hi'
        show ((i', false) : Port d m) ∉ (s.2.seq.state s.2.seq.length).live ∨
          (exposedSite P j T (s.1, logQuery (Query.nextOrder o) s.2) a.2 = some i' ∧ v + 1 = c + 1)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · rcases hI.rev v hv i' hi' hia' with h | ⟨h1, -⟩
          · exact Or.inl h
          · rw [hsite] at h1; cases h1
        · have : i' = i₀ := by rw [hi₀] at hi'; exact (Option.some.inj hi').symm
          subst this
          by_cases hl : ((i', false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live
          · right; exact ⟨hex2 (by rw [hI.ep]; exact hia') hl, rfl⟩
          · exact Or.inl hl
      · intro i' hi'
        change exposedSite P j T (s.1, logQuery (Query.nextOrder o) s.2) a.2 = some i' at hi'
        obtain ⟨rfl, hcond⟩ := hex1 i' hi'
        rw [hcur']
        refine ⟨Nat.succ_pos _, by simpa using hi₀, by rw [← hI.ep]; exact hcond.1, hcond.2⟩
      · intro a' i' hau
        change (logQuery (Query.nextOrder o) s.2).auxUsed _ = true at hau
        rw [haux] at hau
        rw [hcur']
        rcases hI.aux a' i' hau with h | ⟨h1, v, hv, h2, -⟩
        · exact Or.inl h
        · have hv' : v < c := hv
          refine Or.inr ⟨h1, v, Nat.lt_succ_of_lt hv', h2, fun h' => ?_⟩
          have := h'.2; omega
    · rw [if_neg hlt] at hq
      rw [hq]
      refine ⟨fun hh => by simp [tileStep, hsite] at hh, fun _ hab' => ?_⟩
      intro i hi hia hl
      have hsw : (tileStep P j T (s.1, logQuery Query.decision s.2) Query.decision a).1.sweep =
          s.2.seq := by simp [tileStep, logQuery, hsite, commitTrial]
      rw [hsw] at hl
      have hceq : curCount P j T s = (TS P j T).card := le_antisymm hI.le (not_lt.mp hlt)
      obtain ⟨p, hp, hsp⟩ := siteAt_surj (TS P j T) hi
      obtain ⟨v, hv, hvp⟩ := orderPos_surj P j T M hM ω s.2.attempt hp
      rw [← hvp] at hsp
      rcases hI.rev v (hceq ▸ hv) i hsp hia with h | ⟨h1, -⟩
      · exact h hl
      · rw [hsite] at h1; cases h1
  · have hcur := hI.cur i hsite
    have hiT : i ∈ TS P j T := (siteAt_mem' _ hcur.2.1).1
    have hia' : i ∈ s.1.endpoint.active := by rw [hI.ep]; exact hcur.2.2.1
    have hnt : i ∉ s.1.terminal := by rw [hI.te]; exact hxt i hiT hcur.2.2.1
    have hact : activeIn P j T s.1 i := by
      unfold activeIn
      first
        | exact ⟨hiT, hia'⟩
        | exact ⟨hiT, hia', hnt⟩
    have hq : tileQuery P j T s =
        if usesTrue s i then
          (if IsFinalSweep m j then Query.trueSuffix i (s.1.prefixLength i)
            else Query.trueDigit i (s.1.prefixLength i))
        else
          (if s.2.auxUsed (tileAuxIndex j T s.2.attempt i) then Query.decision
            else Query.auxiliary (tileAuxIndex j T s.2.attempt i)) := by
      unfold tileQuery; rw [hsite]; simp only [hact, if_true]
    have hscal : ∀ q : Query (Torus d m), (q ≠ Query.decision) → (∀ o, q ≠ Query.nextOrder o) →
        (∀ a' i', q = Query.auxiliary (tileAuxIndex j T a' i') → a' = s.2.attempt ∧ i' = i) →
        let s' := tileStep P j T (s.1, logQuery q s.2) q a
        (s'.2.halted = false → CompInv P j T M ω x s') ∧
          (s'.2.halted = true → HaltComplete P j T x s'.1) := by
      intro q hdec hord hqa
      have hstep : tileStep P j T (s.1, logQuery q s.2) q a =
          scalarStep P j T (s.1, logQuery q s.2) i (tileIncrement P j q a) := by
        rcases q with ⟨i₀, h₀⟩ | k | ⟨i₀, h₀⟩ | o | _
        · simp [tileStep, hsite]
        · simp [tileStep, hsite]
        · simp [tileStep, hsite]
        · exact absurd rfl (hord o)
        · exact absurd rfl hdec
      simp only
      rw [hstep]
      exact compInv_scalar P j T M ω x hM s hrun hI i hsite q hqa hord _
    rw [hq]
    split_ifs with hu hf hau
    · exact hscal _ (by simp) (by simp) (by simp)
    · exact hscal _ (by simp) (by simp) (by simp)
    · exfalso
      rcases hI.aux s.2.attempt i hau with h | ⟨-, v, hv, h2, h3⟩
      · exact lt_irrefl _ h
      · have hc1 := hcur.1
        have := revealed_inj P j T M ω hM s.2.attempt (lt_of_lt_of_le hv hI.le)
          (by have := hI.le; omega) h2 hcur.2.1
        exact h3 ⟨hsite, by omega⟩
    · refine hscal _ (by simp) (by simp) ?_
      intro a' i' he
      simp only [Query.auxiliary.injEq] at he
      obtain ⟨-, -, h1, h2⟩ := tileAuxIndex_injective he
      exact ⟨h1.symm, h2.symm⟩

end Step2

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

/-- **Completeness of accepted trials on real answers.** -/
theorem tileComplete_proof : TileCompleteStatement := by
  intro d m P j T M x k ω hM hab hT hrun hh
  have key : ∀ k', k' ≤ k →
      ((localState M (tileBlock P j T) x k' ω).2.halted = false →
        CompInv P j T M ω x (localState M (tileBlock P j T) x k' ω)) ∧
      ((localState M (tileBlock P j T) x k' ω).2.halted = true →
        HaltComplete P j T x (localState M (tileBlock P j T) x k' ω).1) := by
    intro k'
    induction k' with
    | zero =>
      intro _
      refine ⟨fun _ => compInv_enter P j T M ω x hab, fun h0 => ?_⟩
      rw [localState_zero] at h0
      simp [tileBlock, hab, initScratch] at h0
    | succ k' ih =>
      intro hk
      have hr : (localState M (tileBlock P j T) x k' ω).2.halted = false := hrun k' hk
      have hI := (ih (Nat.le_of_succ_le hk)).1 hr
      rw [localState_succ]
      refine compInv_step P j T M ω x hM (fun i hi ha => (hT i hi ha).1) _ hr hI _ ?_
      intro o ho
      rw [tileBlock_next_running P j T _ hr, ho]
      obtain ⟨rfl, hlt⟩ := tileQuery_nextOrder P j T _ o ho
      exact tile_order_answer P j T M x k' ω _ hM hlt
  exact (key k le_rfl).2 hh

example : TileCompleteStatement := tileComplete_proof

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

/-- **Operation `(j, 0, y)` keeps the tile-phase invariant** (unconditional form of
`tileOp_keeps`; the `hInv` shape of `blockRun_of_runOps` for tile operations). -/
theorem tileOp_keeps' {d m : ℕ} {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ}
    {Cb : ℝ} {ClSc : Type} [MeasurableSpace ClSc] (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (hu : 0 < P.u) (hj : P.n₀ < j) (hjm : j ≤ m + 1) (y : Torus d m)
    (x : RunRecord d m)
    (hx : x ∈ TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j (siteRank d m y)))
    (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hrun : ∀ k' < k, (runOp P ts₀ cl₀ clr j 0 y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ clr j 0 y) x k' ω) = false)
    (hh : (runOp P ts₀ cl₀ clr j 0 y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ clr j 0 y) x k ω) = true) :
    (runOp P ts₀ cl₀ clr j 0 y).exit
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ clr j 0 y) x k ω) ∈
      TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j (siteRank d m y + 1)) :=
  tileOp_keeps tileComplete_proof ts₀ cl₀ clr hu hj hjm y x hx k ω hrun hh

end AndersonAC.AgentS78
