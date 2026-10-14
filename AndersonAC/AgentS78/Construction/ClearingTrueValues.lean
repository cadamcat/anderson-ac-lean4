import AndersonAC.AgentS78.Construction.BoxPhasesTrue
import AndersonAC.AgentS78.Construction.StagePhaseClr

/-!
# WP10 construction: clearing blocks keep the true installed values

agent-s78runinv (2026-10-14), DISPATCH-REQUESTS 04:27:17 (agent-s78box):
`clearingTrueValues_proof : ClearingTrueValuesStatement` (BoxPhasesTrue.lean).

Along the block-local run on the answers of `ω` the record is unchanged (`CTV.fst`); every heat
pivot `p` gets `resids p = binarySuffix λ (prefixLength p)` of its true digits and every queried
core site `y` gets `resids y = λ V_y − installed y` (`residOfAnswer_true`, correction (9)); with
`binaryPrefix + binarySuffix = binaryValue λ = λ V` and the coupled clause of `TrueValues` at the
(guarded, coupled, non-terminal) pivots, DONE commits `installed + resids = λ V` on
`core ∪ inspected`; FAIL only adds `core ∪ inspected` to `pending`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer binaryValue binaryPrefix binarySuffix signValue)

variable {d m : ℕ}

/-! ## Binary values -/

theorem binaryValue_coupling_ctv (c : ℝ) (a : ℕ → Bool) : binaryValue c a = c * binaryValue 1 a := by
  unfold binaryValue
  rw [← tsum_mul_left]
  congr 1; funext k; ring

/-- `λ V(ω)` at a site as a binary value with coupling `λ`. -/
theorem lamV_eq_ctv {M : ℕ → ℕ} (n₀ : ℕ) (u : ℝ) (ω : RandomSources (Torus d m) M) (i : Torus d m) :
    OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ) =
      binaryValue (OAI.Anderson.scaleCoupling n₀ u) (trueDigits ω i) := by
  rw [binaryValue_coupling_ctv]; rfl

/-- Heat and core residuals are true suffixes on the actual answer to `trueSuffix y h`
(`residOfAnswer` after correction (9)). -/
theorem residOfAnswer_true (M : ℕ → ℕ) (L : List (Query (Torus d m)))
    (ω : RandomSources (Torus d m) M) (lam : ℝ) (y : Torus d m) (h : ℕ) :
    residOfAnswer lam y h (localAnswer (Torus d m) M L (Query.trueSuffix y h) ω) =
      binarySuffix lam h (trueDigits ω y) := by
  classical
  unfold residOfAnswer binarySuffix localAnswer
  congr 1; funext k
  have hmem : (Sum.inl (y, h + k) : AndersonAC.S2.SignIndex (Torus d m)) ∈
      AndersonAC.S2.querySigns (Torus d m) (Query.trueSuffix y h) := ⟨h + k, by omega, rfl⟩
  simp only [if_pos hmem, Option.getD_some, trueDigits]

/-! ## Clearing actions: shapes of one update -/

section ClearShape
variable (n₀ j : ℕ) (u : ℝ)

/-- Shape of an update (not halted). -/
structure ClrUpdShape (s r : RunRecord d m × ClearScratch d m) (ans : Answer (Torus d m)) : Prop where
  fst : r.1 = s.1
  core : r.2.core = s.2.core
  /-- every update is one of the five actions -/
  cases :
    (r.2.failed = true ∧ r.2.active = s.2.active ∧ r.2.coreLeft = s.2.coreLeft ∧
      s.2.inspected ⊆ r.2.inspected) ∨
    (r.2.failed = s.2.failed ∧ r.2.done = s.2.done ∧ r.2.active = s.2.active ∧
      r.2.inspected = s.2.inspected ∧ r.2.resids = s.2.resids ∧ r.2.coreLeft = s.2.coreLeft) ∨
    (∃ p hg, actionOf (d := d) (m := m) j u s.1 s.2 = .heat p hg ∧
      r.2.active = s.2.active.erase p ∧ r.2.inspected = insert p s.2.inspected ∧
      r.2.resids = Function.update s.2.resids p
        (residOfAnswer (clearingLam n₀ u) p (s.1.prefixLength p) ans) ∧
      r.2.done = s.2.done ∧ r.2.coreLeft = s.2.coreLeft) ∨
    (∃ y hc, actionOf (d := d) (m := m) j u s.1 s.2 = .coreQuery y hc ∧
      r.2.failed = s.2.failed ∧
      r.2.active = s.2.active.erase y ∧ r.2.inspected = s.2.inspected ∧
      r.2.resids = Function.update s.2.resids y
        (residOfAnswer (clearingLam n₀ u) y 0 ans - s.1.installed y) ∧
      r.2.coreLeft = s.2.coreLeft.erase y ∧ (r.2.done = true → r.2.coreLeft = ∅)) ∨
    (actionOf (d := d) (m := m) j u s.1 s.2 = .finish ∧ r.2.failed = s.2.failed ∧
      r.2.active = s.2.active ∧ r.2.inspected = s.2.inspected ∧ r.2.resids = s.2.resids ∧
      r.2.coreLeft = s.2.coreLeft)

theorem clearingUpdate_shape_ctv (s : RunRecord d m × ClearScratch d m) (ans : Answer (Torus d m))
    (hfd : ¬ (s.2.failed = true ∨ s.2.done = true)) :
    ClrUpdShape n₀ j u s (clearingUpdate (d := d) (m := m) n₀ j u s ans) ans := by
  classical
  unfold clearingUpdate
  dsimp only
  rw [if_neg hfd]
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po =>
    refine ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl, ?_⟩⟩
    cases po <;> simp [Finset.subset_insert]
  | coreReady =>
    exact ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩
  | heat p hg =>
    dsimp only
    split_ifs <;> exact ⟨rfl, rfl, Or.inr (Or.inr (Or.inl ⟨p, hg, hact, rfl, rfl, rfl, rfl, rfl⟩))⟩
  | coreQuery y hc =>
    refine ⟨rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hc, hact, rfl, rfl, rfl, rfl, rfl, ?_⟩)))⟩
    intro h; simpa using h
  | finish =>
    exact ⟨rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨hact, rfl, rfl, rfl, rfl, rfl⟩)))⟩

end ClearShape

/-! ## Clearing blocks keep `TrueValues` (correction (9)) -/

section ClearTV
variable (n₀ j : ℕ) (u : ℝ) (yy : Torus d m) {M : ℕ → ℕ} (ω : RandomSources (Torus d m) M)
  (x : RunRecord d m)

/-- Invariant of the states of a clearing block entered with `x`, along the answers of `ω`. -/
structure CTV (s : RunRecord d m × ClearScratch d m) : Prop where
  fst : s.1 = x
  core : s.2.core = theCore (d := d) (m := m) j u yy x
  left : s.2.coreLeft ⊆ s.2.core
  act : s.2.active ⊆ x.endpoint.active
  gone : ∀ i ∈ x.endpoint.active, i ∉ s.2.active → i ∈ s.2.core ∪ s.2.inspected
  insp : s.2.failed = false → ∀ i ∈ s.2.inspected,
    x.installed i + s.2.resids i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)
  coreV : s.2.failed = false → ∀ i ∈ s.2.core, i ∉ s.2.coreLeft →
    x.installed i + s.2.resids i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)
  inspA : s.2.failed = false → ∀ i ∈ s.2.inspected, i ∉ s.2.active
  done : s.2.failed = false → s.2.done = true → s.2.core = ∅ ∨ s.2.coreLeft = ∅ ∨
    x.aborted = true ∨ ¬ clearingScheduled j m

theorem ctv_enter : CTV n₀ j u yy ω x ((clearingBlock (d := d) (m := m) n₀ j u yy).enter x) := by
  classical
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [clearingBlock, clearInitScratch]
  · exact le_rfl
  · exact le_rfl
  · intro i _ h; exact absurd ‹_› h
  · intro _ i hi; simp at hi
  · intro _ i hi h; exact absurd h (by simp at h ⊢; exact hi)
  · intro _ i hi; simp at hi
  · intro _ h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem ctv_step (hx : x ∈ TrueValues n₀ u ω)
    (hab : x.aborted = false) (L : List (Query (Torus d m)))
    (s : RunRecord d m × ClearScratch d m) (hs : CTV n₀ j u yy ω x s) :
    CTV n₀ j u yy ω x (clearingUpdate (d := d) (m := m) n₀ j u s
      (localAnswer (Torus d m) M L (clearingNext (d := d) (m := m) n₀ j u s) ω)) := by
  classical
  by_cases hfd : s.2.failed = true ∨ s.2.done = true
  · rw [update_halted_fixed _ _ hfd]; exact hs
  have hf : s.2.failed = false := by simpa using (not_or.mp hfd).1
  have hsh := clearingUpdate_shape_ctv n₀ j u s
    (localAnswer (Torus d m) M L (clearingNext (d := d) (m := m) n₀ j u s) ω) hfd
  set r := clearingUpdate (d := d) (m := m) n₀ j u s
    (localAnswer (Torus d m) M L (clearingNext (d := d) (m := m) n₀ j u s) ω) with hr
  have hfst : r.1 = x := hsh.fst.trans hs.fst
  have hcore : r.2.core = s.2.core := hsh.core
  obtain ⟨htv, hcv⟩ := hx hab
  have hpL : ∀ p : Torus d m, p ∉ x.pending → p ∉ x.terminal →
      x.installed p + residOfAnswer (clearingLam n₀ u) p (x.prefixLength p)
        (localAnswer (Torus d m) M L (Query.trueSuffix p (x.prefixLength p)) ω) =
        OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω p : ℝ) := by
    intro p hp ht
    rw [residOfAnswer_true, hcv p hp ht, lamV_eq_ctv, AndersonAC.S2.binary_prefix_suffix _ (x.prefixLength p)]
    rfl
  have hfull : ∀ y : Torus d m, x.installed y + (residOfAnswer (clearingLam n₀ u) y 0
      (localAnswer (Torus d m) M L (Query.trueSuffix y 0) ω) - x.installed y) =
      OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω y : ℝ) := by
    intro y
    rw [residOfAnswer_true, lamV_eq_ctv, AndersonAC.S2.binary_prefix_suffix _ 0]
    simp [binaryPrefix]; rfl
  have hs1 : s.1 = x := hs.fst
  rcases hsh.cases with ⟨hf', ha, hl, hi⟩ | ⟨hf', hd, ha, hi, hrs, hl⟩ |
      ⟨p, hg, hact, ha, hi, hrs, hd, hl⟩ | ⟨y, hc, hact, hf', ha, hi, hrs, hl, hdl⟩ |
      ⟨hact, hf', ha, hi, hrs, hl⟩
  · refine ⟨hfst, hcore.trans hs.core, (by rw [hl, hcore]; exact hs.left), (by rw [ha]; exact hs.act),
      ?_, (fun h => by rw [hf'] at h; cases h), (fun h => by rw [hf'] at h; cases h),
      (fun h => by rw [hf'] at h; cases h), (fun h => by rw [hf'] at h; cases h)⟩
    intro i hi' hn
    rw [ha] at hn
    rcases Finset.mem_union.mp (hs.gone i hi' hn) with h | h
    · exact Finset.mem_union_left _ (hcore ▸ h)
    · exact Finset.mem_union_right _ (hi h)
  · refine ⟨hfst, hcore.trans hs.core, (by rw [hl, hcore]; exact hs.left), (by rw [ha]; exact hs.act),
      (by rw [ha, hi, hcore]; exact hs.gone), (fun _ => by rw [hi, hrs]; exact hs.insp hf),
      (fun _ => by rw [hcore, hl, hrs]; exact hs.coreV hf),
      (fun _ => by rw [hi, ha]; exact hs.inspA hf), (fun _ h => by rw [hd] at h; simp_all)⟩
  · have hn : clearingNext (d := d) (m := m) n₀ j u s =
        Query.trueSuffix p (s.1.prefixLength p) := by unfold clearingNext; rw [hact]
    rw [hn, hs1] at hrs
    have hgx : p ∉ x.pending ∧ p ∉ x.terminal := by
      have h1 := hg.1; have h2 := hg.2.1
      rw [hs1] at h1 h2
      exact ⟨coupledActive_not_pending x h1, h2⟩
    have hval := hpL p hgx.1 hgx.2
    refine ⟨hfst, hcore.trans hs.core, (by rw [hl, hcore]; exact hs.left),
      (by rw [ha]; exact (Finset.erase_subset _ _).trans hs.act), ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi' hn'
      rw [ha] at hn'
      by_cases hip : i = p
      · subst hip; rw [hi]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · have : i ∉ s.2.active := fun h' => hn' (Finset.mem_erase.mpr ⟨hip, h'⟩)
        rcases Finset.mem_union.mp (hs.gone i hi' this) with h | h
        · exact Finset.mem_union_left _ (hcore ▸ h)
        · rw [hi]; exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
    · intro _ i hi'
      rw [hrs]
      by_cases hip : i = p
      · subst hip; rw [Function.update_self]; exact hval
      · rw [Function.update_of_ne hip]
        rw [hi] at hi'
        exact hs.insp hf i ((Finset.mem_insert.mp hi').resolve_left hip)
    · intro _ i hic hil
      rw [hrs]
      by_cases hip : i = p
      · subst hip; rw [Function.update_self]; exact hval
      · rw [Function.update_of_ne hip]
        rw [hcore] at hic; rw [hl] at hil
        exact hs.coreV hf i hic hil
    · intro _ i hi'
      rw [hi] at hi'; rw [ha]
      rcases Finset.mem_insert.mp hi' with rfl | h
      · exact Finset.notMem_erase _ _
      · exact fun h' => hs.inspA hf i h (Finset.mem_of_mem_erase h')
    · intro _ h
      have : s.2.done = false := by simpa using (not_or.mp hfd).2
      rw [hd, this] at h; cases h
  · have hn : clearingNext (d := d) (m := m) n₀ j u s = Query.trueSuffix y 0 := by
      unfold clearingNext; rw [hact]
    rw [hn, hs1] at hrs
    have hval := hfull y
    have hyl := actionOf_coreQuery_mem j u s.1 s.2 y hc hact
    refine ⟨hfst, hcore.trans hs.core, ?_, (by rw [ha]; exact (Finset.erase_subset _ _).trans hs.act),
      ?_, ?_, ?_, ?_, fun _ h => Or.inr (Or.inl (hdl h))⟩
    · rw [hl, hcore]; exact (Finset.erase_subset _ _).trans hs.left
    · intro i hi' hn'
      rw [ha] at hn'
      by_cases hiy : i = y
      · subst hiy; exact Finset.mem_union_left _ (hcore ▸ hs.left hyl)
      · have : i ∉ s.2.active := fun h' => hn' (Finset.mem_erase.mpr ⟨hiy, h'⟩)
        rw [hi, hcore]; exact hs.gone i hi' this
    · intro _ i hi'
      rw [hrs]
      by_cases hiy : i = y
      · subst hiy; rw [Function.update_self]; exact hval
      · rw [Function.update_of_ne hiy]; rw [hi] at hi'; exact hs.insp hf i hi'
    · intro _ i hic hil
      rw [hrs]
      by_cases hiy : i = y
      · subst hiy; rw [Function.update_self]; exact hval
      · rw [Function.update_of_ne hiy]
        rw [hcore] at hic
        rw [hl] at hil
        exact hs.coreV hf i hic (fun h' => hil (Finset.mem_erase.mpr ⟨hiy, h'⟩))
    · intro _ i hi'
      rw [hi] at hi'; rw [ha]
      exact fun h' => hs.inspA hf i hi' (Finset.mem_of_mem_erase h')
  · have hdf : s.2.done = false := by simpa using (not_or.mp hfd).2
    have hfin : s.2.core = ∅ ∨ s.2.coreLeft = ∅ := by
      by_cases hne : s.2.core = ∅
      · exact Or.inl hne
      · exact Or.inr (actionOf_finish_facts j u s.1 s.2 hf hdf hne hact).2
    refine ⟨hfst, hcore.trans hs.core, (by rw [hl, hcore]; exact hs.left), (by rw [ha]; exact hs.act),
      (by rw [ha, hi, hcore]; exact hs.gone), (fun _ => by rw [hi, hrs]; exact hs.insp hf),
      (fun _ => by rw [hcore, hl, hrs]; exact hs.coreV hf),
      (fun _ => by rw [hi, ha]; exact hs.inspA hf), fun _ _ => ?_⟩
    rw [hcore, hl]
    rcases hfin with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem ctv_all (hx : x ∈ TrueValues n₀ u ω)
    (hab : x.aborted = false) (k : ℕ) :
    CTV n₀ j u yy ω x (localState M (clearingBlock (d := d) (m := m) n₀ j u yy) x k ω) := by
  induction k with
  | zero => exact ctv_enter n₀ j u yy ω x
  | succ k ih =>
    rw [localState_succ]
    exact ctv_step n₀ j u yy ω x hx hab _ _ ih

/-- Terminal bookkeeping of a block exit: active sites only leave by becoming terminal. -/
def ClrKeepT (x z : RunRecord d m) : Prop :=
  z.endpoint.active ⊆ x.endpoint.active ∧ x.terminal ⊆ z.terminal ∧
    ∀ i ∈ x.endpoint.active, i ∉ z.endpoint.active → i ∈ z.terminal

theorem clrKeepT_refl (x : RunRecord d m) : ClrKeepT x x :=
  ⟨le_rfl, le_rfl, fun _ hi hn => absurd hi hn⟩

/-- **Clearing blocks, true values** (along the answers of `ω`). -/
theorem clear_tv_exit (hx : x ∈ TrueValues n₀ u ω) (k : ℕ) :
    let z := (clearingBlock (d := d) (m := m) n₀ j u yy).exit
      (localState M (clearingBlock (d := d) (m := m) n₀ j u yy) x k ω)
    z ∈ TrueValues n₀ u ω ∧ (z.aborted = false → x.aborted = false) ∧ ClrKeepT x z := by
  classical
  intro z
  have hz : z = clearingExit (d := d) (m := m) j yy
    (localState M (clearingBlock (d := d) (m := m) n₀ j u yy) x k ω) := rfl
  by_cases hab : x.aborted = true
  · have h1 : (localState M (clearingBlock (d := d) (m := m) n₀ j u yy) x k ω).1 = x :=
      state_fst x k ω
    have : z = x := by rw [hz]; unfold clearingExit; rw [h1, if_pos hab]
    rw [this]
    exact ⟨(fun h => by rw [hab] at h; cases h), id, clrKeepT_refl x⟩
  have hab' : x.aborted = false := by simpa using hab
  have hs := ctv_all n₀ j u yy ω x hx hab' k
  set s := localState M (clearingBlock (d := d) (m := m) n₀ j u yy) x k ω with hsdef
  obtain ⟨htv, hcv⟩ := hx hab'
  have hs1 := hs.fst
  rw [hz]
  unfold clearingExit
  rw [hs1, if_neg hab]
  split_ifs with hsch hcore hfail hdone
  · exact ⟨fun _ => ⟨htv, hcv⟩, id, clrKeepT_refl x⟩
  · exact ⟨fun _ => ⟨htv, hcv⟩, id, clrKeepT_refl x⟩
  · refine ⟨fun _ => ⟨htv, fun i hp ht => ?_⟩, id, clrKeepT_refl x⟩
    · simp only [clearingFailExit, Finset.mem_union, not_or] at hp
      exact hcv i hp.1.1 ht
  · have hf : s.2.failed = false := by simpa using hfail
    have hleft : s.2.coreLeft = ∅ := by
      rcases hs.done hf hdone with h | h | h | h
      · exact absurd h hcore
      · exact h
      · rw [hab'] at h; cases h
      · exact absurd h (by simpa using hsch)
    refine ⟨fun _ => ⟨fun i hi => ?_, fun i hp ht => ?_⟩, id, ?_, ?_, ?_⟩
    · simp only [clearingDoneExit, Finset.mem_union] at hi ⊢
      by_cases hc : i ∈ s.2.core ∨ i ∈ s.2.inspected
      · rw [if_pos hc]
        rcases hc with hc | hc
        · exact hs.coreV hf i hc (by rw [hleft]; exact Finset.notMem_empty i)
        · exact hs.insp hf i hc
      · rw [if_neg hc]
        rcases hi with (hi | hi) | hi
        · exact htv i hi
        · exact absurd (Or.inl hi) hc
        · exact absurd (Or.inr hi) hc
    · simp only [clearingDoneExit, Finset.mem_union, Finset.mem_sdiff, not_or, not_and,
        not_not] at hp ht ⊢
      have hc : ¬ (i ∈ s.2.core ∨ i ∈ s.2.inspected) := fun h' => h'.elim ht.1.2 ht.2
      rw [if_neg hc]
      have hpx : i ∉ x.pending := by
        intro h'
        by_cases hcc : i ∈ s.2.core
        · exact hc (Or.inl hcc)
        · exact hc (Or.inr (hp h' hcc))
      exact hcv i hpx ht.1.1
    · intro i hi
      simp only [clearingDoneExit, Finset.mem_sdiff] at hi
      exact hs.act hi.1
    · intro i hi
      simp only [clearingDoneExit, Finset.mem_union]
      exact Or.inl (Or.inl hi)
    · intro i hi hn
      simp only [clearingDoneExit, Finset.mem_sdiff, not_and, not_not] at hn ⊢
      simp only [Finset.mem_union]
      by_cases ha : i ∈ s.2.active
      · exact Or.inl (Or.inr (hn ha))
      · rcases Finset.mem_union.mp (hs.gone i hi ha) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  · exact ⟨fun _ => ⟨htv, hcv⟩, id, clrKeepT_refl x⟩

end ClearTV

/-- **Clearing blocks keep the true installed values** along the answers of `ω`. -/
theorem clearingTrueValues_proof : ClearingTrueValuesStatement := by
  intro d m n₀ j u y M ω x k hx _ _
  exact (clear_tv_exit n₀ j u y ω x hx k).1

example : ClearingTrueValuesStatement := clearingTrueValues_proof

end AndersonAC.AgentS78
