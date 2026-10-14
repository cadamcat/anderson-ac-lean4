import AndersonAC.AgentS78.Construction.TileCore
import AndersonAC.AgentS78.Construction.TileBlockMeasurable
import AndersonAC.S2.Scales
import AndersonAC.S2.SignResampling
import AndersonAC.S2.OrderResampling
import AndersonAC.S2.OrderCompletion

/-!
# uniform slot law of the first tile trial.

Proves `AndersonAC.AgentS78.tileSlotLaw_proof : TileSlotLawStatement`.
-/

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw signValue binarySuffix)

/-! ## Scale facts -/

theorem sweepScale_pos' {u : ℝ} (hu : 0 < u) (m j : ℕ) : 0 < sweepScale u m j := by
  unfold sweepScale stageScale
  split_ifs <;> positivity

theorem sweepW_pos_of_digit {u : ℝ} {m j : ℕ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (hj0 : 0 < j) (hjm : j ≤ m) : 0 < sweepW u m j := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have htpos : 0 < sweepScale u m j := sweepScale_pos' hu0 m j
  unfold sweepW sweepTheta
  have hfin : ¬ IsFinalSweep m j := by unfold IsFinalSweep; omega
  rw [if_neg hfin]
  have hjm' : j - 1 ≤ m := by omega
  have hlt : stageScale u j m < stageScale u (j - 1) m := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    unfold stageScale
    have h4 : (4 : ℝ) ^ k < (4 : ℝ) ^ (k + 1) := by
      apply pow_lt_pow_right₀ (by norm_num) (by omega)
    have h1 : u / (4 : ℝ) ^ (k + 1) < u / (4 : ℝ) ^ k := by gcongr
    linarith
  have hpos2 : 0 < stageScale u (j - 1) m := by
    unfold stageScale; positivity
  have hθ : stageScale u j m / stageScale u (j - 1) m < 1 :=
    (div_lt_one hpos2).mpr hlt
  linarith

theorem digitAmp_sq (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (digitAmp u n) ^ 2 = 3 * (u / (4 : ℝ) ^ n) / 4 := by
  unfold digitAmp
  rw [Real.sq_sqrt (by positivity)]

theorem digitAmp_sq_eq_wt {u : ℝ} {m j : ℕ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (hj0 : 0 < j) (hjm : j ≤ m) :
    (digitAmp u (j - 1)) ^ 2 = sweepW u m j * sweepScale u m j := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have hfin : ¬ IsFinalSweep m j := by unfold IsFinalSweep; omega
  have ht : sweepScale u m j = stageScale u (j - 1) m := by
    unfold sweepScale; rw [if_neg hfin]
  have hθ : sweepTheta u m j = stageScale u j m / stageScale u (j - 1) m := by
    unfold sweepTheta; rw [if_neg hfin]
  have hw : sweepW u m j = 1 - stageScale u j m / stageScale u (j - 1) m := by
    unfold sweepW; rw [hθ]
  rw [digitAmp_sq u hu0.le, ht, hw]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hpos : 0 < stageScale u k m := by unfold stageScale; positivity
  field_simp
  unfold stageScale
  have h4k : (4 : ℝ) ^ k ≠ 0 := by positivity
  have h4k1 : (4 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have h4m : (4 : ℝ) ^ m ≠ 0 := by positivity
  field_simp
  ring

theorem sweep_final_eq {u : ℝ} (m : ℕ) :
    sweepScale u m (m + 1) = stageScale u m m := by
  unfold sweepScale
  have hfin : IsFinalSweep m (m + 1) := by unfold IsFinalSweep; omega
  rw [if_pos hfin]

theorem sweepW_final (u : ℝ) (m : ℕ) : sweepW u m (m + 1) = 1 / 2 := by
  unfold sweepW sweepTheta
  have hfin : IsFinalSweep m (m + 1) := by unfold IsFinalSweep; omega
  rw [if_pos hfin]; ring

theorem sweepScale_final_eq (u : ℝ) (m : ℕ) :
    sweepScale u m (m + 1) = 2 * u / (4 : ℝ) ^ m := by
  rw [sweep_final_eq]
  unfold stageScale
  ring

theorem wt_final_eq (u : ℝ) (m : ℕ) :
    sweepW u m (m + 1) * sweepScale u m (m + 1) = u / (4 : ℝ) ^ m := by
  rw [sweepW_final, sweepScale_final_eq]
  ring

theorem couplingOf_sq (u : ℝ) (hu : 0 ≤ u) (n₀ : ℕ) :
    (couplingOf u n₀) ^ 2 = 3 * u / (4 : ℝ) ^ n₀ := by
  unfold couplingOf
  rw [Real.sq_sqrt (by positivity)]

/-! ## Measurability -/

theorem tileOrderEval_measurable {d m : ℕ} (M : ℕ → ℕ) (o : ℕ) (j : Fin (M o)) :
    Measurable (fun ω : RandomSources (Torus d m) M => ω.2 o j) := by
  have h1 : Measurable (fun ω : RandomSources (Torus d m) M => ω.2 o) :=
    (measurable_pi_apply o).comp measurable_snd
  have h2 : Measurable (fun p : AndersonAC.S2.Order (M o) => p j) :=
    measurable_of_finite _
  exact h2.comp h1

theorem tileSlot_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ) :
    Measurable (tileSlot P j T M k) := by
  unfold tileSlot
  by_cases h : k < M (tileOrderIndex j T 0)
  · simp only [dif_pos h]
    have hord : Measurable
        (fun ω : RandomSources (Torus d m) M =>
          ω.2 (tileOrderIndex j T 0) ⟨k, h⟩) :=
      tileOrderEval_measurable M _ _
    have hF : Measurable (fun v : Fin (M (tileOrderIndex j T 0)) =>
        ((siteAt (tileSites (P.cover j) T) v.val).getD (site₀ d m))) :=
      measurable_of_finite _
    exact hF.comp hord
  · simp only [dif_neg h]
    exact measurable_const

theorem tileSlotF_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ) :
    Measurable (tileSlotF P j T M k) := by
  unfold tileSlotF
  have hRank : Measurable (fun i : Torus d m => siteRank d m i) :=
    measurable_of_finite _
  exact hRank.comp (tileSlot_measurable P j T M k)

theorem signEval_measurable {d m : ℕ} (M : ℕ → ℕ)
    (z : AndersonAC.S2.SignIndex (Torus d m)) :
    Measurable (fun ω : RandomSources (Torus d m) M => ω.1 z) :=
  (measurable_pi_apply z).comp measurable_fst

theorem tileZeta_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (i : Torus d m) : Measurable (fun ω : RandomSources (Torus d m) M => tileZeta P j T M x i ω) := by
  unfold tileZeta
  by_cases hact : activeIn P j T x i
  · simp only [if_pos hact]
    by_cases hpend : i ∉ x.pending
    · simp only [if_pos hpend]
      by_cases hfin : IsFinalSweep m j
      · simp only [if_pos hfin]
        have hinner : Measurable
            (fun ω : RandomSources (Torus d m) M => fun k : ℕ => ω.1 (Sum.inl (i, k))) :=
          Measurable.of_eval fun k => signEval_measurable M (Sum.inl (i, k))
        exact (AndersonAC.S2.binarySuffix_measurable _ _).comp hinner
      · simp only [if_neg hfin]
        exact measurable_const.mul
          ((measurable_of_finite signValue).comp (signEval_measurable M _))
    · simp only [if_neg hpend]
      exact measurable_const.mul
        ((measurable_of_finite signValue).comp (signEval_measurable M _))
  · simp only [if_neg hact]
    exact measurable_const.mul
      ((measurable_of_finite signValue).comp (signEval_measurable M _))

theorem tileXi_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ) :
    Measurable (tileXi P j T M x k) := by
  unfold tileXi
  have hslot := tileSlot_measurable P j T M k
  have hzeta : ∀ i : Torus d m,
      Measurable (fun ω : RandomSources (Torus d m) M => tileZeta P j T M x i ω) :=
    fun i => tileZeta_measurable P j T M x i
  have hsel : Measurable (fun ω : RandomSources (Torus d m) M =>
      tileZeta P j T M x (tileSlot P j T M k ω) ω) :=
    measurable_select hslot (fun i => hzeta i)
  exact hsel.div_const _

theorem tileHist_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ) :
    Measurable (tileHist P j T M x k) := by
  unfold tileHist
  apply Measurable.of_eval
  intro l
  apply Measurable.prodMk
  · -- first component: (slotF as ℕ), discrete
    have hslot : Measurable (tileSlotF P j T M l.val) :=
      tileSlotF_measurable P j T M l.val
    have hnat : Measurable (fun n : Fin (siteCount d m) => (n.val : ℕ)) :=
      measurable_of_finite _
    exact hnat.comp hslot
  · exact tileXi_measurable P j T M x l.val

/-! ## Deterministic slot combinatorics -/

theorem siteAt_mem {d m : ℕ} (S : Finset (Torus d m)) (v : ℕ) (hv : v < S.card)
    : ∃ i ∈ S, siteAt S v = some i := by
  classical
  unfold siteAt
  set s := S.map (siteRank d m).toEmbedding with hs
  have hcard : s.card = S.card := by simp [hs]
  have hlen : (s.sort (· ≤ ·)).length = S.card := by
    rw [← hcard, Finset.length_sort]
  have hvlen : v < (s.sort (· ≤ ·)).length := by omega
  set l := s.sort (· ≤ ·) with hl
  have ha_some : l[v]? = some (l[v]'hvlen) :=
    (List.getElem_eq_iff hvlen).mp rfl
  have ha_mem : (l[v]'hvlen) ∈ l := List.getElem_mem hvlen
  have ha_fin : (l[v]'hvlen) ∈ s := (Finset.mem_sort (· ≤ ·)).mp ha_mem
  obtain ⟨i, hi, ha_eq⟩ := Finset.mem_map.mp ha_fin
  have hrank : (siteRank d m) i = (l[v]'hvlen) := ha_eq
  refine ⟨i, hi, ?_⟩
  simp [ha_some, ← hrank]

theorem siteAt_injOn {d m : ℕ} (S : Finset (Torus d m)) :
    Set.InjOn (fun v : ℕ => siteAt S v) {v | v < S.card} := by
  classical
  intro v₁ hv₁ v₂ hv₂ heq
  simp only [Set.mem_setOf_eq] at hv₁ hv₂
  have heq' : siteAt S v₁ = siteAt S v₂ := heq
  obtain ⟨i₁, hi₁, heq₁⟩ := siteAt_mem S v₁ hv₁
  obtain ⟨i₂, hi₂, heq₂⟩ := siteAt_mem S v₂ hv₂
  have hi_eq : i₁ = i₂ := Option.some_inj.mp (heq₁.symm.trans (heq'.trans heq₂))
  -- sorted list and its Nodup
  set s := S.map (siteRank d m).toEmbedding with hs
  have hcard : s.card = S.card := by simp [hs]
  have hlen : (s.sort (· ≤ ·)).length = S.card := by
    rw [← hcard, Finset.length_sort]
  have hv₁len : v₁ < (s.sort (· ≤ ·)).length := by omega
  have hv₂len : v₂ < (s.sort (· ≤ ·)).length := by omega
  set l := s.sort (· ≤ ·) with hl
  have hnodup : l.Nodup := Finset.sort_nodup _ _
  have ha₁ : l[v₁]? = some (l[v₁]'hv₁len) := (List.getElem_eq_iff hv₁len).mp rfl
  have ha₂ : l[v₂]? = some (l[v₂]'hv₂len) := (List.getElem_eq_iff hv₂len).mp rfl
  -- siteAt unfolds to map symm over get?
  have hsite₁ : siteAt S v₁ = some ((siteRank d m).symm (l[v₁]'hv₁len)) := by
    unfold siteAt
    simp only [hs, hl] at *
    rw [ha₁]; rfl
  have hsite₂ : siteAt S v₂ = some ((siteRank d m).symm (l[v₂]'hv₂len)) := by
    unfold siteAt
    simp only [hs, hl] at *
    rw [ha₂]; rfl
  rw [hsite₁, hsite₂] at heq'
  have hsymm_eq := Option.some_inj.mp heq'
  have hl_eq : (l[v₁]'hv₁len) = (l[v₂]'hv₂len) := by
    have := congrArg (siteRank d m) hsymm_eq
    simpa using this
  have hfin_eq : (⟨v₁, hv₁len⟩ : Fin l.length) = ⟨v₂, hv₂len⟩ :=
    hnodup.injective_get (by simpa [List.get_eq_getElem] using hl_eq)
  exact congrArg Fin.val hfin_eq

theorem siteAt_getD_mem {d m : ℕ} (S : Finset (Torus d m)) (v : ℕ) (hv : v < S.card) :
    (siteAt S v).getD (site₀ d m) ∈ S := by
  obtain ⟨i, hi, heq⟩ := siteAt_mem S v hv
  rw [heq]; simpa using hi

theorem tileSlot_eq_siteAt {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM : TileOrderSizes P j T M) (k : ℕ) (hk : k < slotCount P j T)
    (ω : RandomSources (Torus d m) M) :
    tileSlot P j T M k ω =
      ((siteAt (tileSites (P.cover j) T)
        ((ω.2 (tileOrderIndex j T 0) ⟨k, by have hM0 := hM 0; unfold slotCount at hk; omega⟩).val)).getD (site₀ d m)) := by
  unfold tileSlot slotCount at *
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hkM : k < M (tileOrderIndex j T 0) := by omega
  simp only [dif_pos hkM]

theorem tileSlot_mem_tile {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM : TileOrderSizes P j T M) (k : ℕ) (hk : k < slotCount P j T)
    (ω : RandomSources (Torus d m) M) :
    tileSlot P j T M k ω ∈ tileSites (P.cover j) T := by
  rw [tileSlot_eq_siteAt P j T M hM k hk ω]
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hval : ((ω.2 (tileOrderIndex j T 0)
      ⟨k, by unfold slotCount at hk; omega⟩).val) < (tileSites (P.cover j) T).card := by
    have hlt := (ω.2 (tileOrderIndex j T 0)
      ⟨k, by unfold slotCount at hk; omega⟩).isLt
    omega
  exact siteAt_getD_mem _ _ hval

theorem tileSlotF_mem_image {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM : TileOrderSizes P j T M) (k : ℕ) (hk : k < slotCount P j T)
    (ω : RandomSources (Torus d m) M) :
    tileSlotF P j T M k ω ∈
      (tileSites (P.cover j) T).image (siteRank d m) := by
  unfold tileSlotF
  exact Finset.mem_image.mpr
    ⟨tileSlot P j T M k ω, tileSlot_mem_tile P j T M hM k hk ω, rfl⟩

theorem tileSlotF_injOnRange {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM : TileOrderSizes P j T M) (k : ℕ) (hk : k ≤ slotCount P j T)
    (ω : RandomSources (Torus d m) M) :
    Set.InjOn (fun l : ℕ => tileSlotF P j T M l ω) {l | l < k} := by
  classical
  intro l₁ hl₁ l₂ hl₂ heq
  simp only [Set.mem_setOf_eq] at hl₁ hl₂
  by_contra hne
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  have hl₁N : l₁ < slotCount P j T := by omega
  have hl₂N : l₂ < slotCount P j T := by omega
  have hl₁M : l₁ < M (tileOrderIndex j T 0) := by omega
  have hl₂M : l₂ < M (tileOrderIndex j T 0) := by omega
  -- permutation inputs distinct
  have hfin_ne : (⟨l₁, hl₁M⟩ : Fin (M (tileOrderIndex j T 0))) ≠ ⟨l₂, hl₂M⟩ := by
    intro hcon
    apply hne
    have := congrArg Fin.val hcon
    simpa using this
  have hperm_ne : ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩ ≠
      ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩ :=
    fun hcon => hfin_ne ((Equiv.injective _ ) hcon)
  have hval_ne : ((ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩).val) ≠
      ((ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩).val) := by
    intro hcon
    apply hperm_ne
    exact Fin.ext hcon
  have hcard_lt₁ : ((ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩).val) <
      (tileSites (P.cover j) T).card := by
    have hlt := (ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩).isLt
    omega
  have hcard_lt₂ : ((ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩).val) <
      (tileSites (P.cover j) T).card := by
    have hlt := (ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩).isLt
    omega
  have hsite_ne : siteAt (tileSites (P.cover j) T)
      ((ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩).val) ≠
      siteAt (tileSites (P.cover j) T)
      ((ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩).val) := by
    intro hcon
    apply hval_ne
    have hinj := siteAt_injOn (d := d) (m := m) (tileSites (P.cover j) T)
    have h1 : ((ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩).val) ∈
        {v | v < (tileSites (P.cover j) T).card} := hcard_lt₁
    have h2 : ((ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩).val) ∈
        {v | v < (tileSites (P.cover j) T).card} := hcard_lt₂
    exact hinj h1 h2 hcon
  -- transfer to tileSlot via eq_siteAt (needs hk for l₁,l₂)
  have heq_slot : tileSlot P j T M l₁ ω ≠ tileSlot P j T M l₂ ω := by
    rw [tileSlot_eq_siteAt P j T M hM l₁ hl₁N ω,
      tileSlot_eq_siteAt P j T M hM l₂ hl₂N ω]
    -- getD of distinct somes are distinct (both are some via mem)
    obtain ⟨i₁, _, heq₁⟩ := siteAt_mem (tileSites (P.cover j) T)
      ((ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩).val) hcard_lt₁
    obtain ⟨i₂, _, heq₂⟩ := siteAt_mem (tileSites (P.cover j) T)
      ((ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩).val) hcard_lt₂
    -- rewrite siteAt to some form using injOn? Actually hsite_ne says Options distinct,
    -- so getDs distinct
    have hget₁ : ((siteAt (tileSites (P.cover j) T)
        ((ω.2 (tileOrderIndex j T 0) ⟨l₁, hl₁M⟩).val)).getD (site₀ d m)) = i₁ := by
      rw [heq₁]; rfl
    have hget₂ : ((siteAt (tileSites (P.cover j) T)
        ((ω.2 (tileOrderIndex j T 0) ⟨l₂, hl₂M⟩).val)).getD (site₀ d m)) = i₂ := by
      rw [heq₂]; rfl
    rw [hget₁, hget₂]
    intro hcon
    apply hsite_ne
    rw [heq₁, heq₂, hcon]
  have heqF : tileSlotF P j T M l₁ ω = tileSlotF P j T M l₂ ω := heq
  unfold tileSlotF at heqF
  exact heq_slot ((siteRank d m).injective heqF)

theorem tileRemaining_card_a1 {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM : TileOrderSizes P j T M) (k : ℕ) (hk : k ≤ slotCount P j T)
    (ω : RandomSources (Torus d m) M) :
    (tileRemaining P j T M k ω).card = slotCount P j T - k := by
  classical
  unfold tileRemaining slotCount at *
  set S := tileSites (P.cover j) T with hS
  set img := S.image (siteRank d m) with himg
  have himg_card : img.card = S.card :=
    Finset.card_image_of_injective _ (siteRank d m).injective
  set slots := ((Finset.range k).image fun l => tileSlotF P j T M l ω) with hslots
  have hslots_card : slots.card = k := by
    have hset : (↑(Finset.range k) : Set ℕ) = {l | l < k} := by
      ext x; simp
    have hinj : Set.InjOn (fun l : ℕ => tileSlotF P j T M l ω) ↑(Finset.range k) := by
      rw [hset]
      exact tileSlotF_injOnRange P j T M hM k hk ω
    have hcard := Finset.card_image_of_injOn hinj
    rw [Finset.card_range] at hcard
    simpa [hslots] using hcard
  have hsub : slots ⊆ img := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range] at hl
    have hlN : l < S.card := by omega
    exact tileSlotF_mem_image P j T M hM l (by omega) ω
  have hcard := Finset.card_sdiff_of_subset hsub
  rw [himg_card, hslots_card] at hcard
  -- tileRemaining is img \ slots by definition
  simpa [himg, hslots, hS] using hcard

theorem tileFiltration_eq_comap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ) :
    (tileFiltration P j T M x k) =
      MeasurableSpace.comap (tileHist P j T M x k)
        (inferInstance : MeasurableSpace (Fin k → ℕ × ℝ)) := by
  have hmeas := tileHist_measurable P j T M x k
  have hle : MeasurableSpace.comap (tileHist P j T M x k)
      (inferInstance : MeasurableSpace (Fin k → ℕ × ℝ)) ≤
      (inferInstance : MeasurableSpace (RandomSources (Torus d m) M)) :=
    hmeas.comap_le
  have hseq : (tileFiltration P j T M x).seq k =
      MeasurableSpace.comap (tileHist P j T M x k)
        (inferInstance : MeasurableSpace (Fin k → ℕ × ℝ)) ⊓
      (inferInstance : MeasurableSpace (RandomSources (Torus d m) M)) := rfl
  have heq : (tileFiltration P j T M x).seq k =
      MeasurableSpace.comap (tileHist P j T M x k)
        (inferInstance : MeasurableSpace (Fin k → ℕ × ℝ)) := by
    rw [hseq, inf_eq_left.mpr hle]
  exact heq

/-- Every set of finsets over a finite type is measurable (finite union of singletons). -/
theorem measurableSet_finset_all {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] (S : Set (Finset α)) : MeasurableSet S := by
  have hfin : S.Finite := Set.toFinite S
  rw [← Set.biUnion_of_singleton S]
  refine hfin.measurableSet_biUnion fun s _ => ?_
  have heq : ({s} : Set (Finset α)) =
      (⋂ a ∈ (s : Finset α), {t : Finset α | a ∈ t}) ∩
      (⋂ a ∈ (Finset.univ \ s), {t : Finset α | a ∉ t}) := by
    ext t
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro ht
      subst ht
      refine ⟨?_, ?_⟩ <;> intro a ha <;> simpa using ha
    · rintro ⟨h1, h2⟩
      rw [Finset.ext_iff]
      intro a
      constructor
      · intro hat
        by_contra has
        have h2x : a ∉ t := by simpa using h2 a (by simpa using has)
        exact h2x hat
      · intro has
        have h1x : a ∈ t := by simpa using h1 a (by simpa using has)
        exact h1x
  rw [heq]
  apply MeasurableSet.inter
  · apply Set.Finite.measurableSet_biInter (Finset.finite_toSet s)
    intro a _
    exact measurableSet_mem_finset a
  · apply Set.Finite.measurableSet_biInter ((Finset.univ \ s).finite_toSet)
    intro a _
    exact measurableSet_notMem_finset a

/-- Convert measurability into `Finset.instMeasurableSpace` to measurability into `⊤`. -/
theorem measurable_to_top_finset {α : Type*} {β : Type*} (mα : MeasurableSpace α)
    [Fintype β] [DecidableEq β] [MeasurableSpace β] {f : α → Finset β}
    (h : @Measurable α (Finset β) mα inferInstance f) :
    @Measurable α (Finset β) mα ⊤ f :=
  fun _ _ => h (measurableSet_finset_all _)

theorem tileRemaining_measurable_comap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ)
    (hM : TileOrderSizes P j T M) :
    @Measurable _ _ (MeasurableSpace.comap (tileHist P j T M x k)
      (inferInstance : MeasurableSpace (Fin k → ℕ × ℝ)))
      inferInstance (tileRemaining P j T M k) := by
  classical
  have hpos : 0 < siteCount d m := siteCount_pos d m
  -- inner vector Fin k → Fin via % (measurable)
  have hmod : Measurable (fun a : ℕ =>
      (⟨a % siteCount d m, Nat.mod_lt _ hpos⟩ : Fin (siteCount d m))) := by
    exact measurable_of_countable _
  have hinner : Measurable (fun f : Fin k → ℕ × ℝ => fun l : Fin k =>
      (⟨((f l).1) % siteCount d m, Nat.mod_lt _ hpos⟩ : Fin (siteCount d m))) := by
    apply measurable_pi_lambda
    intro l
    exact hmod.comp (measurable_fst.comp (measurable_pi_apply l))
  -- H' on finite domain Fin k → Fin (any function measurable via finite)
  have hH' : Measurable (fun g : (Fin k → Fin (siteCount d m)) =>
      ((tileSites (P.cover j) T).image (siteRank d m) \
        ((Finset.univ : Finset (Fin k)).image g))) := by
    exact measurable_of_finite _
  have hG : Measurable (fun f : Fin k → ℕ × ℝ =>
      ((tileSites (P.cover j) T).image (siteRank d m) \
        ((Finset.univ : Finset (Fin k)).image
          fun l => (⟨((f l).1) % siteCount d m, Nat.mod_lt _ hpos⟩ :
            Fin (siteCount d m))))) := by
    have heqG : (fun f : Fin k → ℕ × ℝ =>
        ((tileSites (P.cover j) T).image (siteRank d m) \
          ((Finset.univ : Finset (Fin k)).image
            fun l => (⟨((f l).1) % siteCount d m, Nat.mod_lt _ hpos⟩ :
              Fin (siteCount d m))))) =
        (fun g : (Fin k → Fin (siteCount d m)) =>
          ((tileSites (P.cover j) T).image (siteRank d m) \
            ((Finset.univ : Finset (Fin k)).image g))) ∘
        (fun f : Fin k → ℕ × ℝ => fun l : Fin k =>
          (⟨((f l).1) % siteCount d m, Nat.mod_lt _ hpos⟩ :
            Fin (siteCount d m))) := rfl
    rw [heqG]
    exact hH'.comp hinner
  have heq : tileRemaining P j T M k =
      (fun f : Fin k → ℕ × ℝ =>
        ((tileSites (P.cover j) T).image (siteRank d m) \
          ((Finset.univ : Finset (Fin k)).image
            fun l => (⟨((f l).1) % siteCount d m, Nat.mod_lt _ hpos⟩ :
              Fin (siteCount d m))))) ∘
      tileHist P j T M x k := by
    funext ω
    unfold tileRemaining tileHist
    simp only [Function.comp]
    congr 1
    ext y
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l, hl⟩, Fin.ext ?_⟩
      simp only [Fin.val_mk]
      exact Nat.mod_eq_of_lt (tileSlotF P j T M l ω).isLt
    · rintro ⟨lf, rfl⟩
      -- lf : Fin k, need l = lf.val < k with slotF = ofNat
      refine ⟨lf.val, lf.isLt, Fin.ext ?_⟩
      simp only [Fin.val_mk]
      exact (Nat.mod_eq_of_lt (tileSlotF P j T M lf.val ω).isLt).symm
  rw [heq]
  exact hG.comp (comap_measurable _)

theorem tileSlotF_measurable_comap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ) :
    @Measurable _ _ (MeasurableSpace.comap (tileHist P j T M x (k + 1))
      (inferInstance : MeasurableSpace (Fin (k + 1) → ℕ × ℝ)))
      ⊤ (tileSlotF P j T M k) := by
  classical
  have hpos : 0 < siteCount d m := siteCount_pos d m
  have hkk : k < k + 1 := Nat.lt_succ_self k
  let lk : Fin (k + 1) := ⟨k, hkk⟩
  have hmod : Measurable (fun a : ℕ =>
      (⟨a % siteCount d m, Nat.mod_lt _ hpos⟩ : Fin (siteCount d m))) := by
    exact measurable_of_countable _
  have hH : Measurable (fun f : Fin (k + 1) → ℕ × ℝ =>
      (⟨((f lk).1) % siteCount d m, Nat.mod_lt _ hpos⟩ : Fin (siteCount d m))) := by
    exact hmod.comp (measurable_fst.comp (measurable_pi_apply lk))
  have heq : tileSlotF P j T M k =
      (fun f : Fin (k + 1) → ℕ × ℝ =>
        (⟨((f lk).1) % siteCount d m, Nat.mod_lt _ hpos⟩ :
          Fin (siteCount d m))) ∘ tileHist P j T M x (k + 1) := by
    funext ω
    unfold tileHist tileSlotF
    simp only [Function.comp]
    -- (tileHist... lk).1 = (slotF k).val, then % recovers
    have h1 : (((fun l : Fin (k + 1) => ((tileSlotF P j T M l.val ω : ℕ),
        tileXi P j T M x l.val ω)) lk).1) = (tileSlotF P j T M k ω).val := rfl
    have h2 : (tileSlotF P j T M k ω).val % siteCount d m =
        (tileSlotF P j T M k ω).val :=
      Nat.mod_eq_of_lt (tileSlotF P j T M k ω).isLt
    have hval_eq : (((fun l : Fin (k + 1) => ((tileSlotF P j T M l.val ω : ℕ),
        tileXi P j T M x l.val ω)) lk).1 % siteCount d m) =
        (tileSlotF P j T M k ω).val := by rw [h1, h2]
    have h3 : (⟨((((fun l : Fin (k + 1) => ((tileSlotF P j T M l.val ω : ℕ),
        tileXi P j T M x l.val ω)) lk).1) % siteCount d m),
        Nat.mod_lt _ hpos⟩ : Fin (siteCount d m)) =
        tileSlotF P j T M k ω := Fin.ext hval_eq
    -- need to show lk.val = k? Since lk = ⟨k, ...⟩, val = k rfl, but fun uses l.val?
    -- Actually (fun...) lk uses lk.val = k? Since lk = ⟨k, ...⟩, val = k rfl, good.
    -- Above h1 already uses that? h1 is rfl? Since lf.val = k? Good.
    exact h3.symm
  rw [heq]
  exact hH.comp (comap_measurable _)

theorem tileXi_measurable_comap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ) :
    @Measurable _ _ (MeasurableSpace.comap (tileHist P j T M x (k + 1))
      (inferInstance : MeasurableSpace (Fin (k + 1) → ℕ × ℝ)))
      inferInstance (tileXi P j T M x k) := by
  classical
  have hkk : k < k + 1 := Nat.lt_succ_self k
  let lk : Fin (k + 1) := ⟨k, hkk⟩
  have hH : Measurable (fun f : Fin (k + 1) → ℕ × ℝ => (f lk).2) :=
    measurable_snd.comp (measurable_pi_apply lk)
  have heq : tileXi P j T M x k =
      (fun f : Fin (k + 1) → ℕ × ℝ => (f lk).2) ∘ tileHist P j T M x (k + 1) := by
    funext ω
    unfold tileHist
    simp only [Function.comp]
    rfl
  rw [heq]
  exact hH.comp (comap_measurable _)

theorem tileXi_bound_pointwise {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (hM : TileOrderSizes P j T M) (hGood : TileGoodCore C P j T x)
    (k : ℕ) (hk : k < slotCount P j T) (ω : RandomSources (Torus d m) M) :
    |tileXi P j T M x k ω| ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
  classical
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  have htpos : 0 < sweepScale P.u m j := sweepScale_pos' hu0 m j
  have hsqrt_t_nonneg : 0 ≤ Real.sqrt (sweepScale P.u m j) := Real.sqrt_nonneg _
  -- site of slot
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  have hmem : tileSlot P j T M k ω ∈ tileSites (P.cover j) T :=
    tileSlot_mem_tile P j T M hM k hk ω
  -- unfold xi as zeta / sqrt w
  unfold tileXi
  by_cases hfin : IsFinalSweep m j
  · -- final sweep: w = 1/2, t = 2u/4^m
    have hw : sweepW P.u m j = 1 / 2 := by
      have hj_eq : j = m + 1 := by simp only [IsFinalSweep] at hfin; omega
      subst hj_eq
      exact sweepW_final P.u m
    have hwt : sweepW P.u m j * sweepScale P.u m j = P.u / (4 : ℝ) ^ m := by
      have hj_eq : j = m + 1 := by simp only [IsFinalSweep] at hfin; omega
      subst hj_eq
      exact wt_final_eq P.u m
    have hsqrt_w_pos : 0 < Real.sqrt (sweepW P.u m j) := by
      rw [hw]; positivity
    have hsqrt_w_ne : Real.sqrt (sweepW P.u m j) ≠ 0 := ne_of_gt hsqrt_w_pos
    -- active vs inactive
    by_cases hact : activeIn P j T x (tileSlot P j T M k ω)
    · -- active at final: no pending (Good), suffix with h = m - n₀
      have hno_pend : (tileSlot P j T M k ω) ∉ x.pending := by
        have hmem' : tileSlot P j T M k ω ∈ tileSites (P.cover j) T := hmem
        have hact' : tileSlot P j T M k ω ∈ x.endpoint.active := hact.2.1
        exact hGood.final_no_pending hfin _ hmem' hact'
      have hpre : x.prefixLength (tileSlot P j T M k ω) = m - P.n₀ := by
        have hmem' : tileSlot P j T M k ω ∈ tileSites (P.cover j) T := hmem
        have hact' : tileSlot P j T M k ω ∈ x.endpoint.active := hact.2.1
        exact hGood.final_prefix hfin _ hmem' hact'
      -- zeta is suffix
      have hzeta_eq : tileZeta P j T M x (tileSlot P j T M k ω) ω =
          AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
            (fun kk => ω.1 (Sum.inl (tileSlot P j T M k ω, kk))) := by
        unfold tileZeta
        simp only [if_pos hact, if_pos hno_pend, if_pos hfin, hpre]
      rw [hzeta_eq]
      -- bound suffix via binarySuffix_bound
      have hbound := AndersonAC.S2.binarySuffix_bound (couplingOf P.u P.n₀) (m - P.n₀)
        (fun kk => ω.1 (Sum.inl (tileSlot P j T M k ω, kk)))
      -- |suffix| ≤ |λ| / 2^h
      have hlam_nonneg : 0 ≤ couplingOf P.u P.n₀ := by
        unfold couplingOf; positivity
      have hlam_abs : |couplingOf P.u P.n₀| = couplingOf P.u P.n₀ := abs_of_nonneg hlam_nonneg
      rw [hlam_abs] at hbound
      -- need |suffix|/√w ≤ 2√t
      have hsqrt_w : Real.sqrt (sweepW P.u m j) = Real.sqrt (1 / 2 : ℝ) := by rw [hw]
      -- suffices λ/2^h/√w ≤ 2√t since |suffix| ≤ λ/2^h
      have hle_suf : |AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
          (fun kk => ω.1 (Sum.inl (tileSlot P j T M k ω, kk)))| /
          Real.sqrt (sweepW P.u m j) ≤
          (couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
          Real.sqrt (sweepW P.u m j) := by
        apply div_le_div_of_nonneg_right hbound (le_of_lt hsqrt_w_pos)
      have hle_main : (couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
          Real.sqrt (sweepW P.u m j) ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
        -- square both sides (both ≥0)
        have hleft_nonneg : 0 ≤ (couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
            Real.sqrt (sweepW P.u m j) := by
          apply div_nonneg _ (le_of_lt hsqrt_w_pos)
          apply div_nonneg hlam_nonneg (by positivity)
        have hright_nonneg : 0 ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
          positivity
        -- squares: left² = 6u/4^m, right² = 8u/4^m
        have hsq_le : ((couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
            Real.sqrt (sweepW P.u m j)) ^ 2 ≤
            (2 * Real.sqrt (sweepScale P.u m j)) ^ 2 := by
          have hlam_sq : (couplingOf P.u P.n₀) ^ 2 = 3 * P.u / (4 : ℝ) ^ P.n₀ :=
            couplingOf_sq P.u hu0.le P.n₀
          have hsqrt_w_sq : (Real.sqrt (sweepW P.u m j)) ^ 2 = sweepW P.u m j :=
            Real.sq_sqrt (by rw [hw]; positivity : (0:ℝ) ≤ sweepW P.u m j)
          have hsqrt_t_sq : (Real.sqrt (sweepScale P.u m j)) ^ 2 = sweepScale P.u m j :=
            Real.sq_sqrt htpos.le
          have h2pow_sq : ((2 : ℝ) ^ (m - P.n₀)) ^ 2 = (4 : ℝ) ^ (m - P.n₀) := by
            rw [← AndersonAC.SolS2.four_pow_eq_two_pow_sq]
          have hn0_le : P.n₀ ≤ m := by
            have hj_eq : j = m + 1 := by simp only [IsFinalSweep] at hfin; omega
            omega
          have hm_eq : P.n₀ + (m - P.n₀) = m := Nat.add_sub_cancel' hn0_le
          have h4m : (4 : ℝ) ^ m = (4 : ℝ) ^ P.n₀ * (4 : ℝ) ^ (m - P.n₀) := by
            rw [← pow_add, hm_eq]
          have ht_eq : sweepScale P.u m j = 2 * P.u / (4 : ℝ) ^ m := by
            have hj_eq : j = m + 1 := by simp only [IsFinalSweep] at hfin; omega
            subst hj_eq
            exact sweepScale_final_eq P.u m
          calc ((couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
              Real.sqrt (sweepW P.u m j)) ^ 2
              = ((couplingOf P.u P.n₀) ^ 2 / ((2 : ℝ) ^ (m - P.n₀)) ^ 2) /
                (Real.sqrt (sweepW P.u m j)) ^ 2 := by
                rw [div_pow, div_pow]
            _ = ((3 * P.u / (4 : ℝ) ^ P.n₀) / (4 : ℝ) ^ (m - P.n₀)) / (1 / 2 : ℝ) := by
                rw [hlam_sq, h2pow_sq, hsqrt_w_sq, hw]
            _ = 6 * P.u / (4 : ℝ) ^ m := by
                rw [h4m]; field_simp; ring
            _ ≤ 8 * P.u / (4 : ℝ) ^ m := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                nlinarith [hu0]
            _ = (2 * Real.sqrt (sweepScale P.u m j)) ^ 2 := by
                rw [mul_pow, hsqrt_t_sq, ht_eq]
                field_simp; ring
        -- from squares to original via sqrt monotonicity (both ≥0)
        have hle_sq : ((couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
            Real.sqrt (sweepW P.u m j)) ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
          have ha_eq : (couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
              Real.sqrt (sweepW P.u m j) =
              Real.sqrt (((couplingOf P.u P.n₀ / (2 : ℝ) ^ (m - P.n₀)) /
                Real.sqrt (sweepW P.u m j)) ^ 2) := by
            rw [Real.sqrt_sq hleft_nonneg]
          have hb_eq : 2 * Real.sqrt (sweepScale P.u m j) =
              Real.sqrt ((2 * Real.sqrt (sweepScale P.u m j)) ^ 2) := by
            rw [Real.sqrt_sq hright_nonneg]
          rw [ha_eq, hb_eq]
          exact Real.sqrt_le_sqrt hsq_le
        exact hle_sq
      have h_eq : |(AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
          (fun kk => ω.1 (Sum.inl (tileSlot P j T M k ω, kk))) /
          Real.sqrt (sweepW P.u m j))| =
          |AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
            (fun kk => ω.1 (Sum.inl (tileSlot P j T M k ω, kk)))| /
          Real.sqrt (sweepW P.u m j) := by
        rw [abs_div, abs_of_pos hsqrt_w_pos]
      rw [h_eq]
      exact le_trans hle_suf hle_main
    · -- inactive dummy: zeta = √(w t) * ±1
      have hzeta_eq : tileZeta P j T M x (tileSlot P j T M k ω) ω =
          Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
            signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω)))) := by
        unfold tileZeta
        simp only [if_neg hact]
      have hsign_outer : |signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω))))| = 1 := by
        unfold signValue
        split_ifs <;> simp
      have hwt_nonneg : 0 ≤ sweepW P.u m j * sweepScale P.u m j :=
        mul_nonneg (le_of_lt (by rw [hw]; positivity)) (le_of_lt htpos)
      have hzeta_abs : |Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
          signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω))))| =
          Real.sqrt (sweepW P.u m j * sweepScale P.u m j) := by
        have hsign : |signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω))))| = 1 := by
          unfold signValue
          split_ifs <;> simp
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), hsign, mul_one]
      -- |xi| = √(w t)/√w = √t ≤ 2√t
      have hxi_eq : |tileZeta P j T M x (tileSlot P j T M k ω) ω /
          Real.sqrt (sweepW P.u m j)| =
          Real.sqrt (sweepScale P.u m j) := by
        rw [hzeta_eq, abs_div, abs_of_pos hsqrt_w_pos, hzeta_abs,
          Real.sqrt_mul (by rw [hw]; positivity : (0:ℝ) ≤ sweepW P.u m j)]
        field_simp
      rw [hxi_eq]
      have : Real.sqrt (sweepScale P.u m j) ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
        linarith [Real.sqrt_nonneg (sweepScale P.u m j)]
      exact this
  · -- digit sweep: j ≤ m
    have hjm' : j ≤ m := by simp only [IsFinalSweep] at hfin; omega
    have hj0 : 0 < j := by omega
    have hw_pos : 0 < sweepW P.u m j := sweepW_pos_of_digit hu hj0 hjm'
    have htpos' : 0 < sweepScale P.u m j := sweepScale_pos' hu0 m j
    have hsqrt_w_pos : 0 < Real.sqrt (sweepW P.u m j) :=
      Real.sqrt_pos.mpr hw_pos
    have hsqrt_w_ne : Real.sqrt (sweepW P.u m j) ≠ 0 := ne_of_gt hsqrt_w_pos
    have hdigit_sq : (digitAmp P.u (j - 1)) ^ 2 = sweepW P.u m j * sweepScale P.u m j :=
      digitAmp_sq_eq_wt hu hj0 hjm'
    have hdigit_nonneg : 0 ≤ digitAmp P.u (j - 1) := by
      unfold digitAmp; positivity
    have hwt_nonneg : 0 ≤ sweepW P.u m j * sweepScale P.u m j :=
      mul_nonneg hw_pos.le htpos'.le
    have hdigit_eq : digitAmp P.u (j - 1) =
        Real.sqrt (sweepW P.u m j * sweepScale P.u m j) := by
      rw [← Real.sqrt_sq hdigit_nonneg, hdigit_sq]
    -- In all three subcases |zeta| = √(w t), hence |xi| = √t
    have hzeta_abs : |tileZeta P j T M x (tileSlot P j T M k ω) ω| =
        Real.sqrt (sweepW P.u m j * sweepScale P.u m j) := by
      by_cases hact : activeIn P j T x (tileSlot P j T M k ω)
      · by_cases hpend : (tileSlot P j T M k ω) ∉ x.pending
        · -- coupled digit
          have heq : tileZeta P j T M x (tileSlot P j T M k ω) ω =
              digitAmp P.u (j - 1) *
                signValue (ω.1 (Sum.inl (tileSlot P j T M k ω,
                  x.prefixLength (tileSlot P j T M k ω)))) := by
            unfold tileZeta
            simp only [if_pos hact, if_pos hpend, if_neg hfin]
          rw [heq, abs_mul, abs_of_nonneg hdigit_nonneg, hdigit_eq]
          have hsign : |signValue (ω.1 (Sum.inl (tileSlot P j T M k ω,
              x.prefixLength (tileSlot P j T M k ω))))| = 1 := by
            unfold signValue; split_ifs <;> simp
          rw [hsign, mul_one]
        · -- pending aux
          have heq : tileZeta P j T M x (tileSlot P j T M k ω) ω =
              digitAmp P.u (j - 1) *
                signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω)))) := by
            unfold tileZeta
            simp only [if_pos hact, if_neg hpend]
          rw [heq, abs_mul, abs_of_nonneg hdigit_nonneg, hdigit_eq]
          have hsign : |signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω))))| = 1 := by
            unfold signValue; split_ifs <;> simp
          rw [hsign, mul_one]
      · -- dummy
        have heq : tileZeta P j T M x (tileSlot P j T M k ω) ω =
            Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
              signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω)))) := by
          unfold tileZeta
          simp only [if_neg hact]
        rw [heq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        have hsign : |signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 (tileSlot P j T M k ω))))| = 1 := by
          unfold signValue; split_ifs <;> simp
        rw [hsign, mul_one]
    have hxi_eq : |tileZeta P j T M x (tileSlot P j T M k ω) ω /
        Real.sqrt (sweepW P.u m j)| =
        Real.sqrt (sweepScale P.u m j) := by
      rw [abs_div, abs_of_pos hsqrt_w_pos, hzeta_abs,
        Real.sqrt_mul hw_pos.le]
      field_simp
    rw [hxi_eq]
    have : Real.sqrt (sweepScale P.u m j) ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
      linarith [Real.sqrt_nonneg (sweepScale P.u m j)]
    exact this

/-! ## CondExp infrastructure: comap sets, coordinate blocks, flips -/

/-- Every ℱk-measurable set is a tileHist preimage (comap characterization). -/
theorem obtain_hist_preimage {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ)
    (E : Set (RandomSources (Torus d m) M))
    (hE : MeasurableSet[(tileFiltration P j T M x k)] E) :
    ∃ B : Set (Fin k → ℕ × ℝ), MeasurableSet B ∧ tileHist P j T M x k ⁻¹' B = E := by
  rw [tileFiltration_eq_comap] at hE
  exact MeasurableSpace.measurableSet_comap.mp hE

theorem tileAuxIndex_injective_same {d m : ℕ} (j T a : ℕ) :
    Function.Injective (fun i : Torus d m => tileAuxIndex j T a i) := by
  intro i i' h
  exact (tileAuxIndex_injective h).2.2.2

open Classical in
/-- Sign coordinates read by `tileZeta` at site `s` (superset per case, mirroring
`tileZeta`'s splits: suffix uses all `inl (s, ·)` coords). -/
def siteCoords {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (s : Torus d m) :
    Set (AndersonAC.S2.SignIndex (Torus d m)) :=
  if activeIn P j T x s then
    (if s ∉ x.pending then
      (if IsFinalSweep m j then {z | ∃ kk, z = Sum.inl (s, kk)}
       else {Sum.inl (s, x.prefixLength s)})
    else {Sum.inr (tileAuxIndex j T 0 s)})
  else {Sum.inr (tileAuxIndex j T 0 s)}

/-- Classification of `siteCoords` into the three explicit shapes. -/
theorem siteCoords_cases {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (s : Torus d m) :
    (siteCoords P j T x s = {Sum.inl (s, x.prefixLength s)} ∧
      activeIn P j T x s ∧ s ∉ x.pending ∧ ¬ IsFinalSweep m j)
    ∨ (siteCoords P j T x s = {z | ∃ kk, z = Sum.inl (s, kk)} ∧
      activeIn P j T x s ∧ s ∉ x.pending ∧ IsFinalSweep m j)
    ∨ (siteCoords P j T x s = {Sum.inr (tileAuxIndex j T 0 s)} ∧
      ¬ (activeIn P j T x s ∧ s ∉ x.pending)) := by
  unfold siteCoords
  by_cases ha : activeIn P j T x s
  · by_cases hp : s ∉ x.pending
    · by_cases hf : IsFinalSweep m j
      · simp only [if_pos ha, if_pos hp, if_pos hf]
        exact Or.inr (Or.inl ⟨trivial, ha, hp, hf⟩)
      · simp only [if_pos ha, if_pos hp, if_neg hf]
        exact Or.inl ⟨trivial, ha, hp, hf⟩
    · simp only [if_pos ha, if_neg hp]
      exact Or.inr (Or.inr ⟨trivial, fun h => hp h.2⟩)
  · simp only [if_neg ha]
    exact Or.inr (Or.inr ⟨trivial, fun h => ha h.1⟩)

/-- Every `siteCoords` set lies in the site fiber (all `inl` coords plus the aux `inr`). -/
theorem siteCoords_subset_fiber {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (s : Torus d m) :
    siteCoords P j T x s ⊆
      ({z : AndersonAC.S2.SignIndex (Torus d m) | ∃ k, z = Sum.inl (s, k)} ∪
        {Sum.inr (tileAuxIndex j T 0 s)}) := by
  rcases siteCoords_cases P j T x s with ⟨hs, -, -, -⟩ | ⟨hs, -, -, -⟩ | ⟨hs, -⟩ <;>
    rw [hs]
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨_, rfl⟩
  · intro z hz
    obtain ⟨kk, rfl⟩ := hz
    exact Or.inl ⟨_, rfl⟩
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr rfl

/-- Distinct sites have disjoint fibers. -/
theorem fiber_disjoint {d m : ℕ} (j T : ℕ) {s s' : Torus d m} (hne : s ≠ s') :
    Disjoint ({z : AndersonAC.S2.SignIndex (Torus d m) | ∃ k, z = Sum.inl (s, k)} ∪
        {Sum.inr (tileAuxIndex j T 0 s)})
      ({z : AndersonAC.S2.SignIndex (Torus d m) | ∃ k, z = Sum.inl (s', k)} ∪
        {Sum.inr (tileAuxIndex j T 0 s')}) := by
  rw [Set.disjoint_left]
  rintro z (⟨k, rfl⟩ | hz) (⟨k', hk'⟩ | hz')
  · simp only [Sum.inl.injEq, Prod.mk.injEq] at hk'
    exact hne hk'.1
  · simp at hz'
  · subst hz
    simp at hk'
  · rw [Set.mem_singleton_iff] at hz hz'
    subst hz
    simp only [Sum.inr.injEq] at hz'
    exact hne (tileAuxIndex_injective_same j _ 0 hz')

/-- Sites use pairwise disjoint sign coordinates. -/
theorem siteCoords_disjoint {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) {s s' : Torus d m}
    (hne : s ≠ s') : Disjoint (siteCoords P j T x s) (siteCoords P j T x s') :=
  Disjoint.mono (siteCoords_subset_fiber P j T x s)
    (siteCoords_subset_fiber P j T x s') (fiber_disjoint j T hne)

/-- Flip acts as identity outside the mask. -/
theorem flipSigns_outside {d m : ℕ} (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (ε : AndersonAC.S2.SignIndex (Torus d m) → Bool) (x) (hx : x ∉ mask) :
    AndersonAC.SolS2.flipSigns (Torus d m) mask ε x = ε x := by
  simp only [AndersonAC.SolS2.flipSigns, hx, ite_false]

/-- Flip negates inside the mask. -/
theorem flipSigns_inside {d m : ℕ} (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (ε : AndersonAC.S2.SignIndex (Torus d m) → Bool) (x) (hx : x ∈ mask) :
    AndersonAC.SolS2.flipSigns (Torus d m) mask ε x = !(ε x) := by
  simp only [AndersonAC.SolS2.flipSigns, hx, ite_true]

theorem signFlip_fst_outside {d m : ℕ} {M : ℕ → ℕ}
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (ω : RandomSources (Torus d m) M) (x) (hx : x ∉ mask) :
    (AndersonAC.SolS2.signFlip (Torus d m) mask ω).1 x = ω.1 x :=
  flipSigns_outside mask ω.1 x hx

theorem signFlip_fst_inside {d m : ℕ} {M : ℕ → ℕ}
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (ω : RandomSources (Torus d m) M) (x) (hx : x ∈ mask) :
    (AndersonAC.SolS2.signFlip (Torus d m) mask ω).1 x = !(ω.1 x) := by
  show AndersonAC.SolS2.flipSigns (Torus d m) mask ω.1 x = _
  exact flipSigns_inside mask ω.1 x hx

theorem signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> simp [signValue]

theorem signValue_sq_one (b : Bool) : (signValue b) ^ 2 = 1 := by
  cases b <;> simp [signValue]

/-- `tileZeta` at a coupled-digit site is unchanged by flips avoiding its coordinate. -/
theorem tileZeta_flip_irrelevant_digit {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s' : Torus d m) (hact : activeIn P j T x s') (hpend : s' ∉ x.pending)
    (hfin : ¬ IsFinalSweep m j) (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hdisj : Disjoint mask {Sum.inl (s', x.prefixLength s')}) (ω) :
    tileZeta P j T M x s' (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      tileZeta P j T M x s' ω := by
  have e1 : tileZeta P j T M x s' (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      digitAmp P.u (j - 1) * signValue ((AndersonAC.SolS2.signFlip (Torus d m) mask ω).1
        (Sum.inl (s', x.prefixLength s'))) := by
    unfold tileZeta
    simp only [if_pos hact, if_pos hpend, if_neg hfin]
  have e2 : tileZeta P j T M x s' ω =
      digitAmp P.u (j - 1) * signValue (ω.1 (Sum.inl (s', x.prefixLength s'))) := by
    unfold tileZeta
    simp only [if_pos hact, if_pos hpend, if_neg hfin]
  rw [e1, e2]
  have hout : (Sum.inl (s', x.prefixLength s') : AndersonAC.S2.SignIndex (Torus d m)) ∉ mask := by
    have hmem : Sum.inl (s', x.prefixLength s') ∈
        ({Sum.inl (s', x.prefixLength s')} : Set (AndersonAC.S2.SignIndex (Torus d m))) := rfl
    exact Set.disjoint_right.mp hdisj hmem
  rw [signFlip_fst_outside _ _ _ hout]

/-- `tileZeta` at a suffix site is unchanged by flips avoiding its whole tail. -/
theorem tileZeta_flip_irrelevant_suffix {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s' : Torus d m) (hact : activeIn P j T x s') (hpend : s' ∉ x.pending)
    (hfin : IsFinalSweep m j) (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hdisj : Disjoint mask {z : AndersonAC.S2.SignIndex (Torus d m) | ∃ kk, z = Sum.inl (s', kk)})
    (ω) :
    tileZeta P j T M x s' (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      tileZeta P j T M x s' ω := by
  have e1 : tileZeta P j T M x s' (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      binarySuffix (couplingOf P.u P.n₀) (x.prefixLength s')
        (fun kk => (AndersonAC.SolS2.signFlip (Torus d m) mask ω).1 (Sum.inl (s', kk))) := by
    unfold tileZeta
    simp only [if_pos hact, if_pos hpend, if_pos hfin]
  have e2 : tileZeta P j T M x s' ω =
      binarySuffix (couplingOf P.u P.n₀) (x.prefixLength s')
        (fun kk => ω.1 (Sum.inl (s', kk))) := by
    unfold tileZeta
    simp only [if_pos hact, if_pos hpend, if_pos hfin]
  rw [e1, e2]
  congr 1
  funext kk
  have hout : (Sum.inl (s', kk) : AndersonAC.S2.SignIndex (Torus d m)) ∉ mask := by
    have hmem : (Sum.inl (s', kk) : AndersonAC.S2.SignIndex (Torus d m)) ∈
        {z : AndersonAC.S2.SignIndex (Torus d m) | ∃ kk, z = Sum.inl (s', kk)} :=
      ⟨kk, rfl⟩
    exact Set.disjoint_right.mp hdisj hmem
  rw [signFlip_fst_outside _ _ _ hout]

/-- `tileZeta` at an aux/dummy site is unchanged by flips avoiding its coordinate. -/
theorem tileZeta_flip_irrelevant_aux {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s' : Torus d m) (C : ℝ)
    (hform : ∀ ω, tileZeta P j T M x s' ω = C * signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 s'))))
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hdisj : Disjoint mask {Sum.inr (tileAuxIndex j T 0 s')}) (ω) :
    tileZeta P j T M x s' (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      tileZeta P j T M x s' ω := by
  rw [hform, hform]
  have hout : (Sum.inr (tileAuxIndex j T 0 s') : AndersonAC.S2.SignIndex (Torus d m)) ∉ mask := by
    have hmem : Sum.inr (tileAuxIndex j T 0 s') ∈
        ({Sum.inr (tileAuxIndex j T 0 s')} : Set (AndersonAC.S2.SignIndex (Torus d m))) := rfl
    exact Set.disjoint_right.mp hdisj hmem
  rw [signFlip_fst_outside _ _ _ hout]

/-- Single-sign `tileZeta` negates when its coordinate is flipped. -/
theorem tileZeta_flip_single_neg {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (C : ℝ) (z : AndersonAC.S2.SignIndex (Torus d m))
    (hform : ∀ ω, tileZeta P j T M x s ω = C * signValue (ω.1 z))
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m))) (hz : z ∈ mask) (ω) :
    tileZeta P j T M x s (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      - tileZeta P j T M x s ω := by
  rw [hform, hform, signFlip_fst_inside _ _ _ hz, signValue_not, mul_neg]

/-- Pointwise `Z² = t` for digit/aux/dummy sites (non-suffix cases). -/
theorem Zsq_single {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (A : ℝ) (z : AndersonAC.S2.SignIndex (Torus d m))
    (hform : ∀ ω, tileZeta P j T M x s ω = A * signValue (ω.1 z))
    (hA : A ^ 2 = sweepW P.u m j * sweepScale P.u m j)
    (hw : 0 < sweepW P.u m j) (ω) :
    (tileZeta P j T M x s ω / Real.sqrt (sweepW P.u m j)) ^ 2 =
      sweepScale P.u m j := by
  rw [hform, div_pow, mul_pow, signValue_sq_one, mul_one,
    Real.sq_sqrt hw.le, hA]
  have hwne : sweepW P.u m j ≠ 0 := ne_of_gt hw
  field_simp

/-- Slot values as a function of permutation entries (globally injective). -/
def slotVal {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card)
    (w : Fin (M (tileOrderIndex j T 0))) : Fin (siteCount d m) :=
  siteRank d m ((siteAt (tileSites (P.cover j) T) w.val).getD (site₀ d m))

theorem slotVal_injective {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card) :
    Function.Injective (slotVal P j T M hM0) := by
  intro a b hab
  unfold slotVal at hab
  have hva : a.val < (tileSites (P.cover j) T).card := by
    have h1 : a.val < M (tileOrderIndex j T 0) := a.isLt
    omega
  have hvb : b.val < (tileSites (P.cover j) T).card := by
    have h1 : b.val < M (tileOrderIndex j T 0) := b.isLt
    omega
  obtain ⟨ia, _, ha_mem⟩ := siteAt_mem _ _ hva
  obtain ⟨ib, _, hb_mem⟩ := siteAt_mem _ _ hvb
  have hga : ((siteAt (tileSites (P.cover j) T) a.val).getD (site₀ d m)) = ia := by
    rw [ha_mem]; rfl
  have hgb : ((siteAt (tileSites (P.cover j) T) b.val).getD (site₀ d m)) = ib := by
    rw [hb_mem]; rfl
  have hsite : ia = ib := by
    rw [← hga, ← hgb]
    exact (siteRank d m).injective hab
  -- lift getD equality back to Options, then injectivity of siteAt
  have hopt : siteAt (tileSites (P.cover j) T) a.val =
      siteAt (tileSites (P.cover j) T) b.val := by
    rw [ha_mem, hb_mem, hsite]
  have hval : a.val = b.val := by
    have hinj := siteAt_injOn (d := d) (m := m) (tileSites (P.cover j) T)
    have h1 : a.val ∈ {v : ℕ | v < (tileSites (P.cover j) T).card} := hva
    have h2 : b.val ∈ {v : ℕ | v < (tileSites (P.cover j) T).card} := hvb
    exact hinj h1 h2 hopt
  exact Fin.ext hval

theorem slotVal_image {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card) :
    Finset.image (slotVal P j T M hM0) Finset.univ =
      (tileSites (P.cover j) T).image (siteRank d m) := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
    have hmem : ((siteAt (tileSites (P.cover j) T) w.val).getD (site₀ d m)) ∈
        tileSites (P.cover j) T := by
      have hv : w.val < (tileSites (P.cover j) T).card := by
        have h1 : w.val < M (tileOrderIndex j T 0) := w.isLt
        omega
      exact siteAt_getD_mem _ _ hv
    exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  · have hcard : (Finset.image (slotVal P j T M hM0) Finset.univ).card =
        M (tileOrderIndex j T 0) := by
      rw [Finset.card_image_of_injective _ (slotVal_injective P j T M hM0),
        Finset.card_univ, Fintype.card_fin]
    have himg : (((tileSites (P.cover j) T).image (siteRank d m))).card =
        M (tileOrderIndex j T 0) := by
      rw [Finset.card_image_of_injective _ (siteRank d m).injective, hM0]
    omega

/-! ## CondExp infrastructure II: order-swap symmetry -/

/-- The swap family: right-multiply order `o₀` by `τ`, identity elsewhere. -/
def swapFam (M : ℕ → ℕ) (o₀ k : ℕ)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) :
    (o : ℕ) → AndersonAC.S2.Order (M o) :=
  Function.update (fun _ => 1) o₀ τ.val

theorem swapFam_o₀ (M : ℕ → ℕ) (o₀ k : ℕ)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) :
    swapFam M o₀ k τ o₀ = τ.val := by
  simp [swapFam]

/-- Swap future order positions by `τ ∈ StabN`: right-multiply `π₀` by `τ`, fixing entries
`< k` pointwise. Signs untouched. -/
def orderSwap (d m : ℕ) (M : ℕ → ℕ) (o₀ k : ℕ)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k)
    (ω : RandomSources (Torus d m) M) : RandomSources (Torus d m) M :=
  AndersonAC.SolS2.orderAction (Torus d m) (swapFam M o₀ k τ) ω

theorem orderSwap_measurable (d m : ℕ) (M : ℕ → ℕ) (o₀ k : ℕ)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) :
    Measurable (orderSwap d m M o₀ k τ) :=
  AndersonAC.SolS2.orderAction_measurable _ _

/-- The swap preserves `sourcesLaw`. -/
theorem orderSwap_law (d m : ℕ) (M : ℕ → ℕ) (o₀ k : ℕ)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) :
    (sourcesLaw (Torus d m) M).map (orderSwap d m M o₀ k τ) =
      sourcesLaw (Torus d m) M :=
  AndersonAC.SolS2.orderAction_law _ _

/-- The swapped order at `o₀` is right-multiplication by `τ`. -/
theorem orderSwap_snd (d m : ℕ) (M : ℕ → ℕ) (o₀ k : ℕ)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k)
    (ω : RandomSources (Torus d m) M) :
    (orderSwap d m M o₀ k τ ω).2 o₀ = (ω.2 o₀) * τ.val := by
  show AndersonAC.SolS2.permuteOrders (swapFam M o₀ k τ) ω.2 o₀ = _
  show ω.2 o₀ * swapFam M o₀ k τ o₀ = _
  rw [swapFam_o₀]

/-- Slots `< k` are fixed by the swap (it fixes the first `k` order entries). -/
theorem tileSlot_orderSwap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ) (hkM : k < M (tileOrderIndex j T 0))
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k)
    (l : ℕ) (hl : l < k) (ω : RandomSources (Torus d m) M) :
    tileSlot P j T M l (orderSwap d m M (tileOrderIndex j T 0) k τ ω) =
      tileSlot P j T M l ω := by
  have hlM : l < M (tileOrderIndex j T 0) := lt_trans hl hkM
  have hfix : τ.val ⟨l, hlM⟩ = ⟨l, hlM⟩ :=
    τ.property _ (not_le.mpr hl)
  have hval : (((orderSwap d m M (tileOrderIndex j T 0) k τ ω).2
      (tileOrderIndex j T 0) ⟨l, hlM⟩).val) =
      (((ω.2 (tileOrderIndex j T 0)) ⟨l, hlM⟩).val) := by
    rw [orderSwap_snd d m M _ k τ ω, Equiv.Perm.mul_apply, hfix]
  unfold tileSlot
  rw [dif_pos hlM, dif_pos hlM, hval]

theorem tileSlotF_orderSwap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ) (hkM : k < M (tileOrderIndex j T 0))
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k)
    (l : ℕ) (hl : l < k) (ω : RandomSources (Torus d m) M) :
    tileSlotF P j T M l (orderSwap d m M (tileOrderIndex j T 0) k τ ω) =
      tileSlotF P j T M l ω := by
  unfold tileSlotF
  rw [tileSlot_orderSwap P j T M k hkM τ l hl ω]

/-- `tileZeta` reads only signs, so it is fixed by the order swap. -/
theorem tileZeta_orderSwap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (o₀ k : ℕ)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k)
    (ω : RandomSources (Torus d m) M) :
    tileZeta P j T M x s (orderSwap d m M o₀ k τ ω) =
      tileZeta P j T M x s ω :=
  rfl

/-- The revealed history before slot `k` is fixed by the swap. -/
theorem tileHist_orderSwap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (k : ℕ) (hkM : k < M (tileOrderIndex j T 0))
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k)
    (ω : RandomSources (Torus d m) M) :
    tileHist P j T M x k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) =
      tileHist P j T M x k ω := by
  funext lf
  have hl : (↑lf : ℕ) < k := lf.isLt
  have hslot := tileSlot_orderSwap P j T M k hkM τ (↑lf) hl ω
  have hslotF := tileSlotF_orderSwap P j T M k hkM τ (↑lf) hl ω
  simp only [tileHist]
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact congrArg Fin.val hslotF
  · unfold tileXi
    rw [hslot, tileZeta_orderSwap P j T M x _ _ _ _ ω]

/-- The remaining set before slot `k` is fixed by the swap. -/
theorem tileRemaining_orderSwap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ) (hkM : k < M (tileOrderIndex j T 0))
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k)
    (ω : RandomSources (Torus d m) M) :
    tileRemaining P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) =
      tileRemaining P j T M k ω := by
  unfold tileRemaining
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, (tileSlotF_orderSwap P j T M k hkM τ l hl ω).symm⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, tileSlotF_orderSwap P j T M k hkM τ l hl ω⟩

/-- History preimages are invariant under the swap. -/
theorem histPreimage_swap_invariant {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (k : ℕ) (hkM : k < M (tileOrderIndex j T 0))
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k)
    (B : Set (Fin k → ℕ × ℝ)) :
    (orderSwap d m M (tileOrderIndex j T 0) k τ) ⁻¹' (tileHist P j T M x k ⁻¹' B) =
      tileHist P j T M x k ⁻¹' B := by
  ext ω
  simp only [Set.mem_preimage]
  rw [tileHist_orderSwap P j T M x k hkM τ ω]

/-- Orbit averaging over the swap group preserves integrals over invariant sets. -/
theorem orbit_avg_integral {d m : ℕ} (M : ℕ → ℕ) (o₀ k : ℕ)
    (E : Set (RandomSources (Torus d m) M))
    (hEmeas : MeasurableSet E)
    (hE : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
      (orderSwap d m M o₀ k τ) ⁻¹' E = E)
    (F : RandomSources (Torus d m) M → ℝ)
    (hF : Integrable F (sourcesLaw (Torus d m) M)) :
    ∫ ω in E, F ω ∂(sourcesLaw (Torus d m) M) =
      ∫ ω in E, ((Fintype.card
        (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) : ℝ)⁻¹ *
        ∑ τ, F (orderSwap d m M o₀ k τ ω)) ∂(sourcesLaw (Torus d m) M) := by
  classical
  have hmp : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
      MeasurePreserving (orderSwap d m M o₀ k τ)
        (sourcesLaw (Torus d m) M) (sourcesLaw (Torus d m) M) :=
    fun τ => ⟨orderSwap_measurable d m M o₀ k τ, orderSwap_law d m M o₀ k τ⟩
  have hFc : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
      Integrable (fun ω => F (orderSwap d m M o₀ k τ ω))
        (sourcesLaw (Torus d m) M) :=
    fun τ => (hmp τ).integrable_comp_of_integrable hF
  have key : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
      ∫ ω in E, F (orderSwap d m M o₀ k τ ω) ∂(sourcesLaw (Torus d m) M) =
        ∫ ω in E, F ω ∂(sourcesLaw (Torus d m) M) := by
    intro τ
    have hmem : ∀ ω, ω ∈ E ↔
        orderSwap d m M o₀ k τ ω ∈ E := by
      intro ω
      have h := hE τ
      constructor
      · intro hω
        have hmem2 : ω ∈ (orderSwap d m M o₀ k τ) ⁻¹' E := by
          rw [h]; exact hω
        exact hmem2
      · intro hφ
        have hmem2 : ω ∈ (orderSwap d m M o₀ k τ) ⁻¹' E := hφ
        rw [h] at hmem2
        exact hmem2
    have hfun : E.indicator (fun ω => F (orderSwap d m M o₀ k τ ω)) =
        (fun ω => E.indicator F (orderSwap d m M o₀ k τ ω)) := by
      funext ω
      by_cases hω : ω ∈ E
      · have hφ : orderSwap d m M o₀ k τ ω ∈ E := (hmem ω).mp hω
        rw [Set.indicator_of_mem hω, Set.indicator_of_mem hφ]
      · have hφ : orderSwap d m M o₀ k τ ω ∉ E :=
          fun hcon => hω ((hmem ω).mpr hcon)
        rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hφ]
    have h1EF : Integrable (E.indicator F) (sourcesLaw (Torus d m) M) :=
      hF.indicator hEmeas
    calc ∫ ω in E, F (orderSwap d m M o₀ k τ ω) ∂(sourcesLaw (Torus d m) M)
        = ∫ ω, E.indicator (fun ω => F (orderSwap d m M o₀ k τ ω)) ω
            ∂(sourcesLaw (Torus d m) M) := by
          rw [integral_indicator hEmeas]
      _ = ∫ ω, E.indicator F (orderSwap d m M o₀ k τ ω)
            ∂(sourcesLaw (Torus d m) M) := by
          rw [hfun]
      _ = ∫ ω, E.indicator F ω ∂(sourcesLaw (Torus d m) M) := by
          have hae : AEStronglyMeasurable (E.indicator F)
              ((sourcesLaw (Torus d m) M).map (orderSwap d m M o₀ k τ)) := by
            rw [orderSwap_law d m M o₀ k τ]
            exact h1EF.aestronglyMeasurable
          have hmap := integral_map (orderSwap_measurable d m M o₀ k τ).aemeasurable hae
          rw [orderSwap_law d m M o₀ k τ] at hmap
          exact hmap.symm
      _ = ∫ ω in E, F ω ∂(sourcesLaw (Torus d m) M) := by
          rw [integral_indicator hEmeas]
  have hsum : IntegrableOn
      (fun ω => ∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
        F (orderSwap d m M o₀ k τ ω)) E (sourcesLaw (Torus d m) M) :=
    (integrable_finsetSum Finset.univ (fun τ _ => hFc τ)).integrableOn
  have hcard : (Fintype.card
      (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc ∫ ω in E, F ω ∂(sourcesLaw (Torus d m) M)
      = (Fintype.card
          (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) : ℝ)⁻¹ *
        (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
          ∫ ω in E, F ω ∂(sourcesLaw (Torus d m) M)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hcard, one_mul]
    _ = (Fintype.card
          (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) : ℝ)⁻¹ *
        (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
          ∫ ω in E, F (orderSwap d m M o₀ k τ ω)
            ∂(sourcesLaw (Torus d m) M)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro τ _
        exact (key τ).symm
    _ = ∫ ω in E, ((Fintype.card
          (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) : ℝ)⁻¹ *
          ∑ τ, F (orderSwap d m M o₀ k τ ω)) ∂(sourcesLaw (Torus d m) M) := by
        have hsum_eq : (∫ ω in E, (∑ τ :
            AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
            F (orderSwap d m M o₀ k τ ω)) ∂(sourcesLaw (Torus d m) M)) =
            ∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
              (∫ ω in E, F (orderSwap d m M o₀ k τ ω)
                ∂(sourcesLaw (Torus d m) M)) := by
          have h1 : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k,
              Integrable (fun ω => F (orderSwap d m M o₀ k τ ω))
                ((sourcesLaw (Torus d m) M).restrict E) :=
            fun τ => (hFc τ).integrableOn
          exact integral_finsetSum Finset.univ (fun τ _ => h1 τ)
        rw [integral_const_mul, hsum_eq]

/-! ## Fiber counting for the swap action -/

/-- Fibers of evaluation at `k'` under `StabN`. -/
def swapFiber (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀) (v : Fin (M o₀)) :
    Finset (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) :=
  Finset.univ.filter (fun τ => τ.val ⟨k, hkM⟩ = v)

/-- Future positions (values `≥ k`). -/
def swapPos (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀) : Finset (Fin (M o₀)) :=
  Finset.univ.filter (fun v => k ≤ v.val)

theorem swapFiber_empty_of_lt (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀)
    (v : Fin (M o₀)) (hv : v.val < k) : swapFiber M o₀ k hkM v = ∅ := by
  rw [swapFiber]
  apply Finset.filter_eq_empty_iff.mpr
  intro τ _
  intro hcon
  -- τ(k') = v with v.val < k forces k' = v, contradiction
  have hinv : τ.val.symm v = v := by
    have hfix : τ.val v = v := τ.property v (not_le.mpr hv)
    calc τ.val.symm v = τ.val.symm (τ.val v) := by rw [hfix]
      _ = v := τ.val.symm_apply_apply v
  have hkk : (⟨k, hkM⟩ : Fin (M o₀)) = τ.val.symm v := by
    have h := τ.val.symm_apply_apply ⟨k, hkM⟩
    rw [hcon] at h
    exact h.symm
  have hkv : (⟨k, hkM⟩ : Fin (M o₀)) = v := hkk.trans hinv
  have hcontra : k = v.val := congrArg Fin.val hkv
  omega

theorem swapFiber_maps_to (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀) :
    (↑(Finset.univ : Finset
      (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k)) :
      Set (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k)).MapsTo
      (fun τ => τ.val ⟨k, hkM⟩) ↑(swapPos M o₀ k hkM) := by
  intro τ _
  simp only [swapPos, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
  by_contra hlt
  push_neg at hlt
  have hempty := swapFiber_empty_of_lt M o₀ k hkM (τ.val ⟨k, hkM⟩) hlt
  have hmem : τ ∈ swapFiber M o₀ k hkM (τ.val ⟨k, hkM⟩) := by
    simp [swapFiber]
  rw [hempty] at hmem
  exact Finset.notMem_empty τ hmem

/-- All fibers over future positions have equal card (transport by a transposition). -/
theorem swapFiber_card_eq (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀)
    (v v' : Fin (M o₀)) (hv : k ≤ v.val) (hv' : k ≤ v'.val) :
    (swapFiber M o₀ k hkM v).card = (swapFiber M o₀ k hkM v').card := by
  classical
  -- the transposition swapping v v' lies in StabN
  have hswap_mem : ∀ j : Fin (M o₀), ¬ k ≤ j.val →
      Equiv.swap v v' j = j := by
    intro j hj
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hcon
      subst hcon
      exact hj hv
    · intro hcon
      subst hcon
      exact hj hv'
  let s : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k :=
    ⟨Equiv.swap v v', hswap_mem⟩
  have hss1 : s.val * s.val = 1 := Equiv.swap_mul_self v v'
  -- forward and backward maps (same transposition both ways)
  let F : {τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k //
      τ.val ⟨k, hkM⟩ = v} → {τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k //
      τ.val ⟨k, hkM⟩ = v'} := fun τ =>
    ⟨⟨s.val * τ.val.val,
      fun j hj => by
        show s.val (τ.val.val j) = j
        rw [τ.val.property j hj]
        exact hswap_mem j hj⟩,
      by
        show s.val (τ.val.val ⟨k, hkM⟩) = v'
        rw [τ.property]
        exact Equiv.swap_apply_left v v'⟩
  let G : {τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k //
      τ.val ⟨k, hkM⟩ = v'} → {τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k //
      τ.val ⟨k, hkM⟩ = v} := fun τ =>
    ⟨⟨s.val * τ.val.val,
      fun j hj => by
        show s.val (τ.val.val j) = j
        rw [τ.val.property j hj]
        exact hswap_mem j hj⟩,
      by
        show s.val (τ.val.val ⟨k, hkM⟩) = v
        rw [τ.property]
        exact Equiv.swap_apply_right v v'⟩
  have hFG : ∀ τ, G (F τ) = τ := by
    intro τ
    apply Subtype.ext
    apply Subtype.ext
    show s.val * (s.val * τ.val.val) = τ.val.val
    rw [← mul_assoc, hss1, one_mul]
  have hGF : ∀ τ, F (G τ) = τ := by
    intro τ
    apply Subtype.ext
    apply Subtype.ext
    show s.val * (s.val * τ.val.val) = τ.val.val
    rw [← mul_assoc, hss1, one_mul]
  have hEquiv : {τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k //
      τ.val ⟨k, hkM⟩ = v} ≃
      {τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k //
      τ.val ⟨k, hkM⟩ = v'} :=
    { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  have hcard := Fintype.card_congr hEquiv
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  simpa [swapFiber] using hcard

theorem swapPos_card (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀) :
    (swapPos M o₀ k hkM).card = M o₀ - k := by
  rw [swapPos, ← Fintype.card_subtype]
  exact AndersonAC.SolS2.OrderCompletionCore.remaining_card_aux
    (M o₀) k (le_of_lt hkM)

theorem swapFiber_sum (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀) :
    ∑ v ∈ swapPos M o₀ k hkM, (swapFiber M o₀ k hkM v).card =
      Fintype.card (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ :
    Finset (AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k)))
    (t := swapPos M o₀ k hkM)
    (f := fun τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M o₀) k =>
      τ.val ⟨k, hkM⟩) (fun τ hτ =>
      swapFiber_maps_to M o₀ k hkM hτ)
  rw [Finset.card_univ] at h
  simpa [swapFiber] using h.symm

theorem swapFiber_card (M : ℕ → ℕ) (o₀ k : ℕ) (hkM : k < M o₀)
    (v : Fin (M o₀)) (hv : k ≤ v.val) :
    (swapFiber M o₀ k hkM v).card = (M o₀ - k - 1).factorial := by
  have hpos : 0 < M o₀ - k := by omega
  have hS := swapPos_card M o₀ k hkM
  have hsum := swapFiber_sum M o₀ k hkM
  have hvS : v ∈ swapPos M o₀ k hkM := by
    simp [swapPos, hv]
  have hall : ∀ v' ∈ swapPos M o₀ k hkM,
      (swapFiber M o₀ k hkM v').card = (swapFiber M o₀ k hkM v).card := by
    intro v' hv'
    simp only [swapPos, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    exact swapFiber_card_eq M o₀ k hkM v' v hv' hv
  have hsum2 : (∑ v' ∈ swapPos M o₀ k hkM, (swapFiber M o₀ k hkM v').card) =
      ∑ _v' ∈ swapPos M o₀ k hkM, (swapFiber M o₀ k hkM v).card :=
    Finset.sum_congr rfl (fun v' hv' => hall v' hv')
  rw [hsum2, Finset.sum_const, nsmul_eq_mul, hS,
    AndersonAC.SolS2.OrderCompletionCore.StabN.card_eq _ _ (le_of_lt hkM)] at hsum
  simp only [Nat.cast_id] at hsum
  have hfact : (M o₀ - k).factorial = (M o₀ - k) * (M o₀ - k - 1).factorial := by
    conv_lhs => rw [show M o₀ - k = M o₀ - k - 1 + 1 by omega]
    rw [Nat.factorial_succ, show M o₀ - k - 1 + 1 = M o₀ - k by omega]
  rw [hfact] at hsum
  exact mul_left_cancel₀ (by omega : M o₀ - k ≠ 0) hsum

/-- The swapped slot at `k` is `slotVal` of the permuted entry. -/
theorem slotF_swap_eq {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ) (hkM : k < M (tileOrderIndex j T 0))
    (hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card)
    (τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k)
    (ω : RandomSources (Torus d m) M) :
    tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) =
      slotVal P j T M hM0 (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) := by
  unfold tileSlotF tileSlot slotVal
  rw [dif_pos hkM, orderSwap_snd d m M _ k τ ω]

/-- Slots before `N` are `slotVal` of the order entries. -/
theorem slotF_eq_slotVal {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (l : ℕ) (hlM : l < M (tileOrderIndex j T 0))
    (hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card)
    (ω : RandomSources (Torus d m) M) :
    tileSlotF P j T M l ω =
      slotVal P j T M hM0 ((ω.2 (tileOrderIndex j T 0)) ⟨l, hlM⟩) := by
  unfold tileSlotF tileSlot slotVal
  rw [dif_pos hlM]

/-- The orbit sum for `uniform`: each swap moves slot `k` across the remaining sites. -/
theorem orbit_sum_uniform {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (k : ℕ) (hk : k < slotCount P j T)
    (hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card)
    (i : Fin (siteCount d m)) (ω : RandomSources (Torus d m) M) :
    (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k,
      (if tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
        then (1 : ℝ) else 0))
    = (if i ∈ tileRemaining P j T M k ω
        then ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) else 0) := by
  classical
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  have hterm : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
      (M (tileOrderIndex j T 0)) k,
      (if tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
        then (1 : ℝ) else 0)
      = (if slotVal P j T M hM0
          (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) = i then 1 else 0) := by
    intro τ
    rw [slotF_swap_eq P j T M k hkM hM0 τ ω]
  rw [Finset.sum_congr rfl (fun τ _ => hterm τ)]
  by_cases hi : i ∈ (tileSites (P.cover j) T).image (siteRank d m)
  · -- target is a tile site: reduce to the fiber over its preimage
    have hi' : i ∈ Finset.image (slotVal P j T M hM0) Finset.univ := by
      rw [slotVal_image P j T M hM0]; exact hi
    obtain ⟨wᵢ, _, hwᵢ⟩ := Finset.mem_image.mp hi'
    set jstar : Fin (M (tileOrderIndex j T 0)) :=
      (ω.2 (tileOrderIndex j T 0)).symm wᵢ with hjstar
    have hcond : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
        (M (tileOrderIndex j T 0)) k,
        (slotVal P j T M hM0 (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) = i)
          ↔ (τ.val ⟨k, hkM⟩ = jstar) := by
      intro τ
      constructor
      · intro h
        have hX : (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) = wᵢ :=
          slotVal_injective P j T M hM0 (h.trans hwᵢ.symm)
        have h2 : (ω.2 (tileOrderIndex j T 0)) (τ.val ⟨k, hkM⟩) = wᵢ := by
          have hmul : (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) =
              (ω.2 (tileOrderIndex j T 0)) (τ.val ⟨k, hkM⟩) :=
            Equiv.Perm.mul_apply _ _ _
          rw [hmul] at hX
          exact hX
        have h3 : τ.val ⟨k, hkM⟩ = (ω.2 (tileOrderIndex j T 0)).symm wᵢ := by
          have hcon := congrArg (ω.2 (tileOrderIndex j T 0)).symm h2
          rwa [Equiv.symm_apply_apply] at hcon
        rw [hjstar]
        exact h3
      · intro h
        have h2 : (ω.2 (tileOrderIndex j T 0)) (τ.val ⟨k, hkM⟩) = wᵢ := by
          rw [h, hjstar]
          exact Equiv.apply_symm_apply _ _
        have hmul : (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) =
            (ω.2 (tileOrderIndex j T 0)) (τ.val ⟨k, hkM⟩) :=
          Equiv.Perm.mul_apply _ _ _
        rw [hmul, h2, hwᵢ]
    have hsum_rw : (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
        (M (tileOrderIndex j T 0)) k,
        (if slotVal P j T M hM0 (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) = i
          then (1 : ℝ) else 0))
        = (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
          (M (tileOrderIndex j T 0)) k,
          (if τ.val ⟨k, hkM⟩ = jstar then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hτ : τ.val ⟨k, hkM⟩ = jstar
      · rw [if_pos ((hcond τ).mpr hτ), if_pos hτ]
      · rw [if_neg (fun h => hτ ((hcond τ).mp h)), if_neg hτ]
    rw [hsum_rw]
    have hfib : (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
        (M (tileOrderIndex j T 0)) k,
        (if τ.val ⟨k, hkM⟩ = jstar then (1 : ℝ) else 0))
        = ((swapFiber M (tileOrderIndex j T 0) k hkM jstar).card : ℝ) := by
      rw [Finset.sum_boole]
      rfl
    -- remaining-membership iff future-position
    have hslots : i ∈ (Finset.range k).image (fun l => tileSlotF P j T M l ω) ↔
        jstar.val < k := by
      constructor
      · intro hmem
        obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_range] at hl
        have hlM : l < M (tileOrderIndex j T 0) := lt_trans hl hkM
        have heq2 : slotVal P j T M hM0
            ((ω.2 (tileOrderIndex j T 0)) ⟨l, hlM⟩) = i := by
          rw [← slotF_eq_slotVal P j T M l hlM hM0 ω]; exact heq
        have hX : ((ω.2 (tileOrderIndex j T 0)) ⟨l, hlM⟩) = wᵢ :=
          slotVal_injective P j T M hM0 (heq2.trans hwᵢ.symm)
        have hlj : (⟨l, hlM⟩ : Fin (M (tileOrderIndex j T 0))) = jstar := by
          have h2 : (⟨l, hlM⟩ : Fin (M (tileOrderIndex j T 0))) =
              (ω.2 (tileOrderIndex j T 0)).symm wᵢ := by
            have hcon := congrArg (ω.2 (tileOrderIndex j T 0)).symm hX
            rwa [Equiv.symm_apply_apply] at hcon
          rw [hjstar]
          exact h2
        have hleq : l = jstar.val := congrArg Fin.val hlj
        omega
      · intro hjk
        apply Finset.mem_image.mpr
        refine ⟨jstar.val, Finset.mem_range.mpr hjk, ?_⟩
        have hlM : jstar.val < M (tileOrderIndex j T 0) := lt_trans hjk hkM
        rw [slotF_eq_slotVal P j T M _ hlM hM0 ω]
        have heta : (⟨jstar.val, hlM⟩ : Fin (M (tileOrderIndex j T 0))) = jstar :=
          Fin.ext rfl
        rw [heta, hjstar, Equiv.apply_symm_apply, hwᵢ]
    have hrem_iff : i ∈ tileRemaining P j T M k ω ↔
        jstar ∈ swapPos M (tileOrderIndex j T 0) k hkM := by
      unfold tileRemaining
      simp only [Finset.mem_sdiff]
      constructor
      · intro ⟨_, hnot⟩
        simp only [swapPos, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hcon
        push_neg at hcon
        exact hnot (hslots.mpr hcon)
      · intro hjS
        simp only [swapPos, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
        refine ⟨hi, ?_⟩
        intro hcon
        have := (hslots.mp hcon)
        omega
    by_cases hrem : i ∈ tileRemaining P j T M k ω
    · have hjS : jstar ∈ swapPos M (tileOrderIndex j T 0) k hkM :=
        hrem_iff.mp hrem
      simp only [swapPos, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
      rw [if_pos hrem, hfib,
        swapFiber_card M (tileOrderIndex j T 0) k hkM jstar hjS]
    · have hjS : jstar ∉ swapPos M (tileOrderIndex j T 0) k hkM :=
        fun hcon => hrem (hrem_iff.mpr hcon)
      simp only [swapPos, Finset.mem_filter, Finset.mem_univ, true_and,
        not_and] at hjS
      have hjlt : jstar.val < k := by
        by_contra hcon
        push_neg at hcon
        exact hjS hcon
      have hempty := swapFiber_empty_of_lt M (tileOrderIndex j T 0) k hkM jstar hjlt
      rw [if_neg hrem, hfib, hempty, Finset.card_empty, Nat.cast_zero]
  · -- target outside the tile: no slot hits it, and it is never remaining
    have hzero : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
        (M (tileOrderIndex j T 0)) k,
        (if slotVal P j T M hM0 (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) = i
          then (1 : ℝ) else 0) = 0 := by
      intro τ
      rw [if_neg]
      intro hcon
      apply hi
      have hmem : slotVal P j T M hM0
          (((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩) ∈
          Finset.image (slotVal P j T M hM0) Finset.univ :=
        Finset.mem_image.mpr
          ⟨(((ω.2 (tileOrderIndex j T 0)) * τ.val) ⟨k, hkM⟩), Finset.mem_univ _, rfl⟩
      rw [slotVal_image P j T M hM0] at hmem
      rw [hcon] at hmem
      exact hmem
    rw [Finset.sum_congr rfl (fun τ _ => hzero τ)]
    simp only [Finset.sum_const_zero]
    have hrem_empty : i ∉ tileRemaining P j T M k ω := by
      unfold tileRemaining
      intro hcon
      exact hi (Finset.mem_sdiff.mp hcon).1
    rw [if_neg hrem_empty]

/-- The run set is a history preimage. -/
theorem run_preimage {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (k : ℕ) (run : ℕ → RandomSources (Torus d m) M → Bool)
    (hrun : @Measurable _ Bool (tileFiltration P j T M x k) ⊤ (run k)) :
    ∃ B : Set (Fin k → ℕ × ℝ), MeasurableSet B ∧
      tileHist P j T M x k ⁻¹' B = (run k) ⁻¹' {true} := by
  have hE : MeasurableSet[tileFiltration P j T M x k] ((run k) ⁻¹' {true}) :=
    hrun (by trivial)
  exact obtain_hist_preimage P j T M x k _ hE

/-- `if`-indicators over measurable sets are measurable (any σ-algebra). -/
theorem measurable_if_one {α : Type*} (m : MeasurableSpace α) (S : Set α)
    [DecidablePred (· ∈ S)]
    (hS : @MeasurableSet α m S) :
    @Measurable α ℝ m _ (fun ω => if ω ∈ S then (1 : ℝ) else 0) := by
  classical
  have heq : (fun ω => if ω ∈ S then (1 : ℝ) else 0) = S.indicator 1 := by
    funext ω
    by_cases hω : ω ∈ S
    · rw [if_pos hω, Set.indicator_of_mem hω, Pi.one_apply]
    · rw [if_neg hω, Set.indicator_of_notMem hω]
  rw [heq]
  exact measurable_const.indicator hS

/-- Comap-measurable functions along the history are ambient-measurable. -/
theorem of_hist_comap {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ)
    {β : Type*} [MeasurableSpace β]
    {f : RandomSources (Torus d m) M → β}
    (hf : @Measurable _ _ (MeasurableSpace.comap (tileHist P j T M x k)
      inferInstance) _ f) :
    Measurable f := by
  intro t ht
  obtain ⟨B, hB, hBeq⟩ := MeasurableSpace.measurableSet_comap.mp (hf ht)
  rw [← hBeq]
  exact (tileHist_measurable P j T M x k) hB

/-- Conditional uniformity of the exposed slot. -/
theorem uniform_condExp {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hM : TileOrderSizes P j T M)
    (run : ℕ → RandomSources (Torus d m) M → Bool)
    (hrun : ∀ k < slotCount P j T,
      @Measurable _ Bool (tileFiltration P j T M x k) ⊤ (run k))
    (k : ℕ) (hk : k < slotCount P j T) (i : Fin (siteCount d m)) :
    (sourcesLaw (Torus d m) M)[(fun ω =>
      if run k ω = true ∧ tileSlotF P j T M k ω = i then (1 : ℝ) else 0) |
      tileFiltration P j T M x k] =ᵐ[sourcesLaw (Torus d m) M]
      (fun ω => if run k ω = true ∧ i ∈ tileRemaining P j T M k ω
        then 1 / ((tileRemaining P j T M k ω).card : ℝ) else 0) := by
  classical
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  -- run-free integrands in membership form
  set S_F : Set (RandomSources (Torus d m) M) :=
    (tileSlotF P j T M k) ⁻¹' {i} with hS_F
  set S_G : Set (RandomSources (Torus d m) M) :=
    (tileRemaining P j T M k) ⁻¹' {s | i ∈ s} with hS_G
  set F₀ : RandomSources (Torus d m) M → ℝ :=
    (fun ω => if ω ∈ S_F then (1 : ℝ) else 0) with hF₀
  set G₀ : RandomSources (Torus d m) M → ℝ :=
    (fun ω => if ω ∈ S_G then 1 / ((tileRemaining P j T M k ω).card : ℝ)
      else 0) with hG₀
  set E_run : Set (RandomSources (Torus d m) M) := (run k) ⁻¹' {true} with hE_run
  have hS_Fmeas : MeasurableSet S_F :=
    (tileSlotF_measurable P j T M k) (measurableSet_singleton i)
  have hS_Gmeas : MeasurableSet S_G :=
    (of_hist_comap P j T M x k
      (tileRemaining_measurable_comap P j T M x k hM))
      (measurableSet_finset_all _)
  have hF₀meas : Measurable F₀ := measurable_if_one _ _ hS_Fmeas
  have hG₀meas : Measurable G₀ := by
    have hval : Measurable (fun ω =>
        (1 : ℝ) / ((tileRemaining P j T M k ω).card : ℝ)) :=
      measurable_const.div
        ((measurable_of_countable
          (fun s : Finset (Fin (siteCount d m)) => (s.card : ℝ))).comp
          (of_hist_comap P j T M x k
            (tileRemaining_measurable_comap P j T M x k hM)))
    have heq : G₀ = fun ω => if ω ∈ S_G
        then (1 : ℝ) / ((tileRemaining P j T M k ω).card : ℝ) else 0 := rfl
    rw [heq]
    exact Measurable.ite hS_Gmeas hval measurable_const
  have hF₀int : Integrable F₀ (sourcesLaw (Torus d m) M) := by
    apply Integrable.of_bound hF₀meas.aestronglyMeasurable 1
    filter_upwards with ω
    simp only [hF₀]
    by_cases h : ω ∈ S_F <;> simp [h]
  have hG₀bound : ∀ ω, ‖G₀ ω‖ ≤ 1 := by
    intro ω
    simp only [hG₀]
    by_cases h : ω ∈ S_G
    · simp only [h, if_true]
      have hmem : i ∈ tileRemaining P j T M k ω := h
      have hcard : 1 ≤ (tileRemaining P j T M k ω).card := by
        have h0 := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
      have hcardR : (1 : ℝ) ≤ ((tileRemaining P j T M k ω).card : ℝ) := by
        exact_mod_cast hcard
      have hposR : (0 : ℝ) < ((tileRemaining P j T M k ω).card : ℝ) := by
        exact_mod_cast (by omega : 0 < (tileRemaining P j T M k ω).card)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one hposR]
      exact hcardR
    · simp [h]
  have hG₀int : Integrable G₀ (sourcesLaw (Torus d m) M) :=
    Integrable.of_bound hG₀meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hG₀bound)
  -- the two sides as indicators over the run set
  have hf_eq : (fun ω => if run k ω = true ∧ tileSlotF P j T M k ω = i
      then (1 : ℝ) else 0) = E_run.indicator F₀ := by
    funext ω
    simp only [hF₀, hE_run, hS_F]
    by_cases hω : run k ω = true
    · have hm : ω ∈ (run k) ⁻¹' {true} := hω
      by_cases hs : tileSlotF P j T M k ω = i
      · have hms : ω ∈ (tileSlotF P j T M k) ⁻¹' {i} := hs
        simp [hm, hms, hs, hω]
      · have hms : ω ∉ (tileSlotF P j T M k) ⁻¹' {i} := hs
        simp [hm, hms, hs, hω]
    · have hm : ω ∉ (run k) ⁻¹' {true} := hω
      simp [hm, hω]
  have hg_eq : (fun ω => if run k ω = true ∧ i ∈ tileRemaining P j T M k ω
      then 1 / ((tileRemaining P j T M k ω).card : ℝ) else 0) =
      E_run.indicator G₀ := by
    funext ω
    simp only [hG₀, hE_run, hS_G]
    by_cases hω : run k ω = true
    · have hm : ω ∈ (run k) ⁻¹' {true} := hω
      by_cases hs : i ∈ tileRemaining P j T M k ω
      · have hms : ω ∈ (tileRemaining P j T M k) ⁻¹' {s | i ∈ s} := hs
        simp [hm, hms, hs, hω]
      · have hms : ω ∉ (tileRemaining P j T M k) ⁻¹' {s | i ∈ s} := hs
        simp [hm, hms, hs, hω]
    · have hm : ω ∉ (run k) ⁻¹' {true} := hω
      simp [hm, hω]
  rw [hf_eq, hg_eq]
  -- run-free core identity on history preimages
  have hcore : ∀ B₁ : Set (Fin k → ℕ × ℝ), MeasurableSet B₁ →
      ∫ ω in tileHist P j T M x k ⁻¹' B₁, F₀ ω ∂(sourcesLaw (Torus d m) M) =
        ∫ ω in tileHist P j T M x k ⁻¹' B₁, G₀ ω ∂(sourcesLaw (Torus d m) M) := by
    intro B₁ hB₁
    have hE₁ : MeasurableSet (tileHist P j T M x k ⁻¹' B₁) :=
      (tileHist_measurable P j T M x k) hB₁
    have havg := orbit_avg_integral M (tileOrderIndex j T 0) k
      (E := tileHist P j T M x k ⁻¹' B₁) hE₁
      (fun τ => histPreimage_swap_invariant P j T M x k hkM τ B₁) F₀ hF₀int
    -- the orbit average equals G₀ pointwise
    have hpt : ∀ ω, ((Fintype.card
        (AndersonAC.SolS2.OrderCompletionCore.StabN
          (M (tileOrderIndex j T 0)) k) : ℝ)⁻¹ *
        ∑ τ, F₀ (orderSwap d m M (tileOrderIndex j T 0) k τ ω)) = G₀ ω := by
      intro ω
      have hsum := orbit_sum_uniform P j T M x k hk hM0 i ω
      have hcardG : (Fintype.card
          (AndersonAC.SolS2.OrderCompletionCore.StabN
            (M (tileOrderIndex j T 0)) k) : ℝ) =
          ((M (tileOrderIndex j T 0) - k).factorial : ℝ) := by
        rw [AndersonAC.SolS2.OrderCompletionCore.StabN.card_eq _ _ (le_of_lt hkM)]
      have hrem : (tileRemaining P j T M k ω).card = M (tileOrderIndex j T 0) - k := by
        have hc := tileRemaining_card_a1 P j T M hM k (le_of_lt hk) ω
        omega
      have hfact : ((M (tileOrderIndex j T 0) - k).factorial : ℝ) =
          (((M (tileOrderIndex j T 0) - k : ℕ)) : ℝ) *
            ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) := by
        have hfactN : (M (tileOrderIndex j T 0) - k).factorial =
            (M (tileOrderIndex j T 0) - k) * (M (tileOrderIndex j T 0) - k - 1).factorial := by
          conv_lhs => rw [show M (tileOrderIndex j T 0) - k =
            M (tileOrderIndex j T 0) - k - 1 + 1 by omega]
          rw [Nat.factorial_succ, show M (tileOrderIndex j T 0) - k - 1 + 1 =
            M (tileOrderIndex j T 0) - k by omega]
        rw [hfactN, Nat.cast_mul]
      have hfact0 : ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      simp only [hF₀, hS_F, Set.mem_preimage, Set.mem_singleton_iff]
      rw [hsum]
      by_cases hri : i ∈ tileRemaining P j T M k ω
      · have hriS : ω ∈ S_G := hri
        rw [if_pos hri]
        simp only [hG₀, if_pos hriS]
        rw [hcardG, hfact, hrem, mul_inv, mul_assoc,
          inv_mul_cancel₀ hfact0, mul_one, inv_eq_one_div]
      · have hriS : ω ∉ S_G := hri
        rw [if_neg hri]
        simp only [hG₀, if_neg hriS]
        simp
    rw [havg]
    apply setIntegral_congr_ae hE₁
    filter_upwards with ω _
    exact hpt ω
  -- assemble via the integral characterization
  have hm : tileFiltration P j T M x k ≤
      (inferInstance : MeasurableSpace (RandomSources (Torus d m) M)) :=
    (tileFiltration P j T M x).le' k
  have hG₀fmeas : StronglyMeasurable[tileFiltration P j T M x k] G₀ := by
    have heq := tileFiltration_eq_comap P j T M x k
    have hrem : @Measurable _ _ (tileFiltration P j T M x k)
        inferInstance (tileRemaining P j T M k) := by
      rw [heq]
      exact tileRemaining_measurable_comap P j T M x k hM
    have hS_Gf : MeasurableSet[tileFiltration P j T M x k] S_G :=
      hrem (measurableSet_finset_all _)
    have hval : @Measurable _ ℝ (tileFiltration P j T M x k) _ (fun ω =>
        (1 : ℝ) / ((tileRemaining P j T M k ω).card : ℝ)) :=
      (measurable_const.div
        ((measurable_of_countable
          (fun s : Finset (Fin (siteCount d m)) => (s.card : ℝ))).comp hrem))
    have hmeas : @Measurable _ ℝ (tileFiltration P j T M x k) _ G₀ := by
      simp only [hG₀]
      exact Measurable.ite hS_Gf hval measurable_const
    exact hmeas.stronglyMeasurable
  obtain ⟨Br, hBr, hBrE⟩ := run_preimage P j T M x k run (hrun k hk)
  have hEr : MeasurableSet E_run := by
    rw [hE_run, ← hBrE]
    exact (tileHist_measurable P j T M x k) hBr
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm (hF₀int.indicator hEr) _ _ _).symm
  · -- E_run-indicator of G₀ is globally integrable, hence on every set
    intro s hs _
    exact (hG₀int.indicator hEr).integrableOn
  · intro s hs _
    obtain ⟨B, hB, hBE⟩ := obtain_hist_preimage P j T M x k s hs
    have hinter : s ∩ E_run = tileHist P j T M x k ⁻¹' (B ∩ Br) := by
      rw [← hBE, hE_run, ← hBrE, Set.preimage_inter]
    calc ∫ ω in s, E_run.indicator G₀ ω ∂(sourcesLaw (Torus d m) M)
        = ∫ ω in s ∩ E_run, G₀ ω ∂(sourcesLaw (Torus d m) M) := by
          rw [setIntegral_indicator hEr]
      _ = ∫ ω in tileHist P j T M x k ⁻¹' (B ∩ Br), G₀ ω
            ∂(sourcesLaw (Torus d m) M) := by
          rw [hinter]
      _ = ∫ ω in tileHist P j T M x k ⁻¹' (B ∩ Br), F₀ ω
            ∂(sourcesLaw (Torus d m) M) := by
          rw [hcore (B ∩ Br) (hB.inter hBr)]
      _ = ∫ ω in s, E_run.indicator F₀ ω ∂(sourcesLaw (Torus d m) M) := by
          rw [setIntegral_indicator hEr, hinter]
  · have hErF : MeasurableSet[tileFiltration P j T M x k] E_run :=
      (hrun k hk) (by trivial)
    exact (hG₀fmeas.indicator hErF).aestronglyMeasurable
/-! ## Mean field: zeta forms and flip negation -/

/-- Digit form of `tileZeta` at a coupled site. -/
theorem zeta_form_digit {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (hact : activeIn P j T x s) (hpend : s ∉ x.pending)
    (hfin : ¬ IsFinalSweep m j) :
    ∀ ω, tileZeta P j T M x s ω =
      digitAmp P.u (j - 1) * signValue (ω.1 (Sum.inl (s, x.prefixLength s))) := by
  intro ω
  unfold tileZeta
  simp only [if_pos hact, if_pos hpend, if_neg hfin]

/-- Aux form of `tileZeta` at a pending active site. -/
theorem zeta_form_aux {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (hact : activeIn P j T x s) (hpend : s ∈ x.pending) :
    ∀ ω, tileZeta P j T M x s ω =
      digitAmp P.u (j - 1) * signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 s))) := by
  intro ω
  unfold tileZeta
  simp only [if_pos hact, if_neg (fun h : s ∉ x.pending => h hpend)]

/-- Suffix form of `tileZeta` at a final active coupled site. -/
theorem zeta_form_suffix {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (hact : activeIn P j T x s) (hpend : s ∉ x.pending)
    (hfin : IsFinalSweep m j) :
    ∀ ω, tileZeta P j T M x s ω =
      AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (x.prefixLength s)
        (fun kk => ω.1 (Sum.inl (s, kk))) := by
  intro ω
  unfold tileZeta
  simp only [if_pos hact, if_pos hpend, if_pos hfin]

/-- Dummy form of `tileZeta` at an inactive site. -/
theorem zeta_form_dummy {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (hact : ¬ activeIn P j T x s) :
    ∀ ω, tileZeta P j T M x s ω =
      Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
        signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 s))) := by
  intro ω
  unfold tileZeta
  simp only [if_neg hact]

/-- The suffix series is summable (transport of `binary_summable` along the shift). -/
theorem suffix_summable (c : ℝ) (h : ℕ) (b : ℕ → Bool) :
    Summable (fun kk : ℕ => c / (2 : ℝ) ^ (h + kk + 1) * signValue (b kk)) := by
  classical
  have hbase := AndersonAC.S2.binary_summable c
    (fun n => if h ≤ n then b (n - h) else true)
  have hinj : Function.Injective (fun kk : ℕ => h + kk) :=
    fun a b hab => Nat.add_left_cancel hab
  have hcomp := hbase.comp_injective hinj
  have heq : (fun kk : ℕ => c / (2 : ℝ) ^ ((h + kk) + 1) *
      signValue ((fun n => if h ≤ n then b (n - h) else true) (h + kk)))
      = (fun kk : ℕ => c / (2 : ℝ) ^ (h + kk + 1) * signValue (b kk)) := by
    funext kk
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
  rw [← heq]
  exact hcomp

/-- Flipping every tail bit negates the suffix. -/
theorem binarySuffix_flip_neg {d m : ℕ} (c : ℝ) (h : ℕ) (s : Torus d m)
    (ε : AndersonAC.S2.SignIndex (Torus d m) → Bool)
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hmask : ∀ kk, (Sum.inl (s, kk) :
      AndersonAC.S2.SignIndex (Torus d m)) ∈ mask) :
    AndersonAC.S2.binarySuffix c h
        (fun kk => AndersonAC.SolS2.flipSigns (Torus d m) mask ε (Sum.inl (s, kk))) =
      - AndersonAC.S2.binarySuffix c h (fun kk => ε (Sum.inl (s, kk))) := by
  simp only [AndersonAC.S2.binarySuffix]
  have hterm : ∀ k : ℕ, c / (2 : ℝ) ^ (h + k + 1) *
      signValue (AndersonAC.SolS2.flipSigns (Torus d m) mask ε (Sum.inl (s, h + k))) =
      -(c / (2 : ℝ) ^ (h + k + 1) * signValue (ε (Sum.inl (s, h + k)))) := by
    intro k
    rw [flipSigns_inside mask ε _ (hmask (h + k)), signValue_not, mul_neg]
  simp_rw [hterm]
  exact (suffix_summable c h (fun kk => ε (Sum.inl (s, h + kk)))).hasSum.neg.tsum_eq

/-- `tileZeta` at a suffix site negates under a flip covering its tail. -/
theorem tileZeta_flip_suffix_neg {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (hact : activeIn P j T x s) (hpend : s ∉ x.pending)
    (hfin : IsFinalSweep m j)
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hmask : ∀ kk, (Sum.inl (s, kk) :
      AndersonAC.S2.SignIndex (Torus d m)) ∈ mask)
    (ω : RandomSources (Torus d m) M) :
    tileZeta P j T M x s (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      - tileZeta P j T M x s ω := by
  have e1 := zeta_form_suffix P j T M x s hact hpend hfin
    (AndersonAC.SolS2.signFlip (Torus d m) mask ω)
  have e2 := zeta_form_suffix P j T M x s hact hpend hfin ω
  rw [e1, e2]
  exact binarySuffix_flip_neg (couplingOf P.u P.n₀) (x.prefixLength s) s _ _ hmask

/-- `tileZeta` away from the flipped site is unchanged (dispatcher over site kinds). -/
theorem tileZeta_flip_irrelevant_of_ne {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s' sstar : Torus d m) (hne : s' ≠ sstar)
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hmask : mask = siteCoords P j T x sstar)
    (ω : RandomSources (Torus d m) M) :
    tileZeta P j T M x s' (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      tileZeta P j T M x s' ω := by
  rcases siteCoords_cases P j T x s' with ⟨hs', hact, hpend, hfin⟩ |
    ⟨hs', hact, hpend, hfin⟩ | ⟨hs', hcon⟩
  · have hdisj : Disjoint mask {Sum.inl (s', x.prefixLength s')} := by
      rw [hmask]
      have h := siteCoords_disjoint P j T x hne
      rw [hs'] at h
      exact h.symm
    exact tileZeta_flip_irrelevant_digit P j T M x s' hact hpend hfin mask hdisj ω
  · have hdisj : Disjoint mask
        {z : AndersonAC.S2.SignIndex (Torus d m) | ∃ kk, z = Sum.inl (s', kk)} := by
      rw [hmask]
      have h := siteCoords_disjoint P j T x hne
      rw [hs'] at h
      exact h.symm
    exact tileZeta_flip_irrelevant_suffix P j T M x s' hact hpend hfin mask hdisj ω
  · have hdisj : Disjoint mask {Sum.inr (tileAuxIndex j T 0 s')} := by
      rw [hmask]
      have h := siteCoords_disjoint P j T x hne
      rw [hs'] at h
      exact h.symm
    by_cases hact' : activeIn P j T x s'
    · have hpend' : s' ∈ x.pending := by
        by_contra hcon'
        exact hcon ⟨hact', hcon'⟩
      have hform : ∀ ω, tileZeta P j T M x s' ω = digitAmp P.u (j - 1) *
          signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 s'))) :=
        zeta_form_aux P j T M x s' hact' hpend'
      exact tileZeta_flip_irrelevant_aux P j T M x s' _ hform mask hdisj ω
    · have hform : ∀ ω, tileZeta P j T M x s' ω =
          Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
            signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 s'))) :=
        zeta_form_dummy P j T M x s' hact'
      exact tileZeta_flip_irrelevant_aux P j T M x s' _ hform mask hdisj ω

/-- `tileZeta` at the flipped site negates (dispatcher over site kinds). -/
theorem tileZeta_flip_neg_target {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (sstar : Torus d m)
    (mask : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hmask : mask = siteCoords P j T x sstar)
    (ω : RandomSources (Torus d m) M) :
    tileZeta P j T M x sstar (AndersonAC.SolS2.signFlip (Torus d m) mask ω) =
      - tileZeta P j T M x sstar ω := by
  rcases siteCoords_cases P j T x sstar with ⟨hs, hact, hpend, hfin⟩ |
    ⟨hs, hact, hpend, hfin⟩ | ⟨hs, hcon⟩
  · -- digit: single negation
    have hform := zeta_form_digit P j T M x sstar hact hpend hfin
    have hz : (Sum.inl (sstar, x.prefixLength sstar) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈ mask := by
      rw [hmask, hs]
      rfl
    exact tileZeta_flip_single_neg P j T M x sstar _ _ hform mask hz ω
  · -- suffix: tail negation
    have hmem : ∀ kk, (Sum.inl (sstar, kk) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈ mask := by
      intro kk
      rw [hmask, hs]
      exact ⟨kk, rfl⟩
    exact tileZeta_flip_suffix_neg P j T M x sstar hact hpend hfin mask hmem ω
  · by_cases hact' : activeIn P j T x sstar
    · have hpend' : sstar ∈ x.pending := by
        by_contra hcon'
        exact hcon ⟨hact', hcon'⟩
      have hform := zeta_form_aux P j T M x sstar hact' hpend'
      have hz : (Sum.inr (tileAuxIndex j T 0 sstar) :
          AndersonAC.S2.SignIndex (Torus d m)) ∈ mask := by
        rw [hmask, hs]
        rfl
      exact tileZeta_flip_single_neg P j T M x sstar _ _ hform mask hz ω
    · have hform := zeta_form_dummy P j T M x sstar hact'
      have hz : (Sum.inr (tileAuxIndex j T 0 sstar) :
          AndersonAC.S2.SignIndex (Torus d m)) ∈ mask := by
        rw [hmask, hs]
        rfl
      exact tileZeta_flip_single_neg P j T M x sstar _ _ hform mask hz ω

/-- Slots hit the remaining set: the `k`-th slot is always unexposed. -/
theorem slot_mem_remaining {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ) (hk : k < slotCount P j T)
    (hM : TileOrderSizes P j T M) (ω : RandomSources (Torus d m) M) :
    tileSlotF P j T M k ω ∈ tileRemaining P j T M k ω := by
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  unfold tileRemaining
  rw [Finset.mem_sdiff]
  constructor
  · exact tileSlotF_mem_image P j T M hM k hk ω
  · intro hcon
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hcon
    rw [Finset.mem_range] at hl
    have hne : l ≠ k := by omega
    have hk1 : k + 1 ≤ slotCount P j T := hk
    have hinj := tileSlotF_injOnRange P j T M hM (k + 1) hk1 ω
    have hlmem : l ∈ {l | l < k + 1} := by
      show l < k + 1
      omega
    have hkmem : k ∈ {l | l < k + 1} := by
      show k < k + 1
      omega
    have := hinj hlmem hkmem heq
    omega

/-- Mean-zero core: the run-free slot-scalar integral vanishes on history preimages. -/
theorem mean_core {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (hM : TileOrderSizes P j T M) (hGood : TileGoodCore C P j T x)
    (k : ℕ) (hk : k < slotCount P j T) (i : Fin (siteCount d m))
    (B₁ : Set (Fin k → ℕ × ℝ)) (hB₁ : MeasurableSet B₁) :
    ∫ ω in tileHist P j T M x k ⁻¹' B₁,
      (if tileSlotF P j T M k ω = i then tileXi P j T M x k ω else 0)
      ∂(sourcesLaw (Torus d m) M) = 0 := by
  classical
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  -- run-free integrand and its bound
  set F₁ : RandomSources (Torus d m) M → ℝ :=
    (fun ω => if tileSlotF P j T M k ω = i then tileXi P j T M x k ω else 0) with hF₁
  have hF₁meas : Measurable F₁ := by
    have heq : F₁ = fun ω => if ω ∈ (tileSlotF P j T M k) ⁻¹' {i}
        then tileXi P j T M x k ω else 0 := by
      funext ω
      simp only [hF₁]
      by_cases h : tileSlotF P j T M k ω = i
      · rw [if_pos h, if_pos (by simpa using h)]
      · rw [if_neg h, if_neg (by simpa using h)]
    rw [heq]
    exact Measurable.ite ((tileSlotF_measurable P j T M k) (measurableSet_singleton i))
      (tileXi_measurable P j T M x k) measurable_const
  have hF₁bound : ∀ ω, ‖F₁ ω‖ ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
    intro ω
    simp only [hF₁]
    by_cases h : tileSlotF P j T M k ω = i
    · simp only [h, if_true]
      rw [Real.norm_eq_abs]
      exact tileXi_bound_pointwise C P j T M x hu hj hjm hM hGood k hk ω
    · simp [h]
  have hF₁int : Integrable F₁ (sourcesLaw (Torus d m) M) :=
    Integrable.of_bound hF₁meas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hF₁bound)
  -- split into remaining / non-remaining
  set R : Set (RandomSources (Torus d m) M) :=
    {ω | i ∈ tileRemaining P j T M k ω} with hR
  set E₁ : Set (RandomSources (Torus d m) M) := tileHist P j T M x k ⁻¹' B₁ with hE₁
  set E' : Set (RandomSources (Torus d m) M) := E₁ ∩ R with hE'
  set E'' : Set (RandomSources (Torus d m) M) := E₁ \ R with hE''
  have hE₁meas : MeasurableSet E₁ := (tileHist_measurable P j T M x k) hB₁
  have hRmeas : MeasurableSet R :=
    (of_hist_comap P j T M x k
      (tileRemaining_measurable_comap P j T M x k hM))
      (measurableSet_finset_all {s | i ∈ s})
  have hE'meas : MeasurableSet E' := hE₁meas.inter hRmeas
  have hE''meas : MeasurableSet E'' := hE₁meas.diff hRmeas
  -- off-remaining part vanishes pointwise
  have hE''0 : ∫ ω in E'', F₁ ω ∂(sourcesLaw (Torus d m) M) = 0 := by
    have hzero : ∀ ω ∈ E'', F₁ ω = 0 := by
      intro ω hω
      have hmem : tileSlotF P j T M k ω ∈ tileRemaining P j T M k ω :=
        slot_mem_remaining P j T M k hk hM ω
      have hni : i ∉ tileRemaining P j T M k ω := hω.2
      have hne : tileSlotF P j T M k ω ≠ i := fun hcon => hni (hcon ▸ hmem)
      simp only [hF₁]
      rw [if_neg hne]
    have hcongr : Set.EqOn F₁ (0 : RandomSources (Torus d m) M → ℝ) E'' :=
      fun ω hω => hzero ω hω
    rw [setIntegral_congr_fun hE''meas hcongr]
    simp
  -- on-remaining part vanishes by the sign flip
  have hE'0 : ∫ ω in E', F₁ ω ∂(sourcesLaw (Torus d m) M) = 0 := by
    -- target site and flip mask
    set sstar : Torus d m := (siteRank d m).symm i with hsstar
    have hrank : siteRank d m sstar = i := (siteRank d m).apply_symm_apply i
    set mask : Set (AndersonAC.S2.SignIndex (Torus d m)) :=
      siteCoords P j T x sstar with hmask
    set Φ : RandomSources (Torus d m) M → RandomSources (Torus d m) M :=
      AndersonAC.SolS2.signFlip (Torus d m) mask with hΦ
    have hΦmeas : Measurable Φ :=
      AndersonAC.SolS2.signFlip_measurable (Torus d m) mask
    have hΦlaw : (sourcesLaw (Torus d m) M).map Φ = sourcesLaw (Torus d m) M :=
      AndersonAC.SolS2.signFlip_law (Torus d m) mask
    have hΦinv : Function.Involutive Φ :=
      AndersonAC.SolS2.signFlip_involutive (Torus d m) mask
    -- slots/orders untouched; scalars of exposed sites untouched on E'
    have hslot_eq : ∀ ω ∈ E', ∀ l : ℕ, l < k →
        tileSlotF P j T M l (Φ ω) = tileSlotF P j T M l ω := by
      intro ω _ l _
      rfl
    have hsite_ne : ∀ ω ∈ E', ∀ l : ℕ, l < k →
        tileSlot P j T M l ω ≠ sstar := by
      intro ω hω l hl
      have hmem : tileSlotF P j T M l ω ∈
          (Finset.range k).image (fun l => tileSlotF P j T M l ω) :=
        Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr hl, rfl⟩
      have hremω : tileRemaining P j T M k ω =
          ((tileSites (P.cover j) T).image (siteRank d m)) \
            ((Finset.range k).image fun l => tileSlotF P j T M l ω) := rfl
      have hri : i ∈ tileRemaining P j T M k ω := hω.2
      rw [hremω] at hri
      have hni : tileSlotF P j T M l ω ≠ i := fun hcon =>
        (Finset.mem_sdiff.mp hri).2 (hcon ▸ hmem)
      intro hcon
      apply hni
      unfold tileSlotF at ⊢
      rw [hcon, hrank]
    have hxi_eq : ∀ ω ∈ E', ∀ l : ℕ, l < k →
        tileXi P j T M x l (Φ ω) = tileXi P j T M x l ω := by
      intro ω hω l hl
      unfold tileXi
      have hsite : tileSlot P j T M l (Φ ω) = tileSlot P j T M l ω := rfl
      rw [hsite]
      congr 1
      exact tileZeta_flip_irrelevant_of_ne P j T M x _ sstar
        (hsite_ne ω hω l hl) mask rfl ω
    have hhist_eq : ∀ ω ∈ E', tileHist P j T M x k (Φ ω) =
        tileHist P j T M x k ω := by
      intro ω hω
      funext lf
      have hl : (↑lf : ℕ) < k := lf.isLt
      have hsF := hslot_eq ω hω (↑lf) hl
      have hx := hxi_eq ω hω (↑lf) hl
      show ((tileSlotF P j T M (↑lf) (Φ ω) : ℕ), tileXi P j T M x (↑lf) (Φ ω)) =
        ((tileSlotF P j T M (↑lf) ω : ℕ), tileXi P j T M x (↑lf) ω)
      rw [hsF, hx]
    have hrem_eq : ∀ ω ∈ E', tileRemaining P j T M k (Φ ω) =
        tileRemaining P j T M k ω :=
      fun ω _ => rfl
    have hfwd : ∀ ω ∈ E', Φ ω ∈ E' := by
      intro ω hω
      refine ⟨?_, ?_⟩
      · show tileHist P j T M x k (Φ ω) ∈ B₁
        rw [hhist_eq ω hω]
        exact hω.1
      · show i ∈ tileRemaining P j T M k (Φ ω)
        rw [hrem_eq ω hω]
        exact hω.2
    have hE'mem : ∀ ω, ω ∈ E' ↔ Φ ω ∈ E' := by
      intro ω
      constructor
      · exact hfwd ω
      · intro hφ
        have h := hfwd (Φ ω) hφ
        rwa [hΦinv ω] at h
    -- integrand negates on E'
    have hslk : ∀ ω, tileSlotF P j T M k (Φ ω) = tileSlotF P j T M k ω :=
      fun ω => rfl
    have hsitek : ∀ ω, tileSlot P j T M k (Φ ω) = tileSlot P j T M k ω :=
      fun ω => rfl
    have hneg : ∀ ω ∈ E', F₁ (Φ ω) = - F₁ ω := by
      intro ω hω
      simp only [hF₁]
      by_cases hs : tileSlotF P j T M k ω = i
      · have hsφ : tileSlotF P j T M k (Φ ω) = i := by
          rw [hslk ω]; exact hs
        have hs2 : siteRank d m (tileSlot P j T M k ω) = i := hs
        have hsk : tileSlot P j T M k ω = sstar :=
          (siteRank d m).injective (hs2.trans hrank.symm)
        rw [if_pos hsφ, if_pos hs]
        unfold tileXi
        rw [hsitek ω, hsk, neg_div']
        congr 1
        exact tileZeta_flip_neg_target P j T M x sstar mask hmask ω
      · have hsφ : tileSlotF P j T M k (Φ ω) ≠ i := by
          rw [hslk ω]; exact hs
        rw [if_neg hsφ, if_neg hs, neg_zero]
    -- integral equals its own negation
    have hGint : Integrable (E'.indicator F₁) (sourcesLaw (Torus d m) M) :=
      hF₁int.indicator hE'meas
    have hmap_eq : (∫ ω, E'.indicator F₁ ω ∂(sourcesLaw (Torus d m) M)) =
        (∫ ω, E'.indicator F₁ (Φ ω) ∂(sourcesLaw (Torus d m) M)) := by
      have hae : AEStronglyMeasurable (E'.indicator F₁)
          ((sourcesLaw (Torus d m) M).map Φ) := by
        rw [hΦlaw]
        exact hGint.aestronglyMeasurable
      have hmap := integral_map hΦmeas.aemeasurable hae
      rw [hΦlaw] at hmap
      exact hmap
    have hneg_int : (∫ ω, E'.indicator F₁ (Φ ω) ∂(sourcesLaw (Torus d m) M)) =
        -(∫ ω, E'.indicator F₁ ω ∂(sourcesLaw (Torus d m) M)) := by
      have hfun : (fun ω => E'.indicator F₁ (Φ ω)) =
          fun ω => -(E'.indicator F₁ ω) := by
        funext ω
        by_cases hω : ω ∈ E'
        · have hφ : Φ ω ∈ E' := (hE'mem ω).mp hω
          rw [Set.indicator_of_mem hφ, Set.indicator_of_mem hω, hneg ω hω]
        · have hφ : Φ ω ∉ E' := fun hcon => hω ((hE'mem ω).mpr hcon)
          rw [Set.indicator_of_notMem hφ, Set.indicator_of_notMem hω, neg_zero]
      rw [hfun, integral_neg]
    have h0 : (∫ ω, E'.indicator F₁ ω ∂(sourcesLaw (Torus d m) M)) = 0 := by
      linarith
    calc ∫ ω in E', F₁ ω ∂(sourcesLaw (Torus d m) M)
        = ∫ ω, E'.indicator F₁ ω ∂(sourcesLaw (Torus d m) M) := by
          rw [integral_indicator hE'meas]
      _ = 0 := h0
  -- combine the two parts
  have hU : E' ∪ E'' = E₁ := by
    ext ω
    simp only [hE', hE'', hE₁, hR, Set.mem_union, Set.mem_inter_iff,
      Set.mem_sdiff, Set.mem_preimage, Set.mem_setOf_eq]
    tauto
  have hdisj : Disjoint E' E'' := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [hE', hE'', hR, Set.mem_inter_iff, Set.mem_sdiff,
      Set.mem_preimage, Set.mem_setOf_eq] at h1 h2
    exact h2.2 h1.2
  calc ∫ ω in E₁, F₁ ω ∂(sourcesLaw (Torus d m) M)
      = ∫ ω in E' ∪ E'', F₁ ω ∂(sourcesLaw (Torus d m) M) := by
        rw [← hU]
    _ = ∫ ω in E', F₁ ω ∂(sourcesLaw (Torus d m) M) +
          ∫ ω in E'', F₁ ω ∂(sourcesLaw (Torus d m) M) :=
        setIntegral_union hdisj hE''meas hF₁int.integrableOn hF₁int.integrableOn
    _ = 0 := by rw [hE'0, hE''0, add_zero]

/-- Conditional mean-zero of the slot scalar. -/
theorem mean_condExp {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (hM : TileOrderSizes P j T M) (hGood : TileGoodCore C P j T x)
    (run : ℕ → RandomSources (Torus d m) M → Bool)
    (hrun : ∀ k < slotCount P j T,
      @Measurable _ Bool (tileFiltration P j T M x k) ⊤ (run k))
    (k : ℕ) (hk : k < slotCount P j T) (i : Fin (siteCount d m)) :
    (sourcesLaw (Torus d m) M)[(fun ω =>
      if run k ω = true ∧ tileSlotF P j T M k ω = i
        then tileXi P j T M x k ω else 0) |
      tileFiltration P j T M x k] =ᵐ[sourcesLaw (Torus d m) M] 0 := by
  classical
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  set F₁ : RandomSources (Torus d m) M → ℝ :=
    (fun ω => if tileSlotF P j T M k ω = i then tileXi P j T M x k ω else 0) with hF₁
  set E_run : Set (RandomSources (Torus d m) M) := (run k) ⁻¹' {true} with hE_run
  have hF₁meas : Measurable F₁ := by
    have heq : F₁ = fun ω => if ω ∈ (tileSlotF P j T M k) ⁻¹' {i}
        then tileXi P j T M x k ω else 0 := by
      funext ω
      simp only [hF₁]
      by_cases h : tileSlotF P j T M k ω = i
      · rw [if_pos h, if_pos (by simpa using h)]
      · rw [if_neg h, if_neg (by simpa using h)]
    rw [heq]
    exact Measurable.ite ((tileSlotF_measurable P j T M k) (measurableSet_singleton i))
      (tileXi_measurable P j T M x k) measurable_const
  have hF₁bound : ∀ ω, ‖F₁ ω‖ ≤ 2 * Real.sqrt (sweepScale P.u m j) := by
    intro ω
    simp only [hF₁]
    by_cases h : tileSlotF P j T M k ω = i
    · simp only [h, if_true, Real.norm_eq_abs]
      exact tileXi_bound_pointwise C P j T M x hu hj hjm hM hGood k hk ω
    · simp [h]
  have hF₁int : Integrable F₁ (sourcesLaw (Torus d m) M) :=
    Integrable.of_bound hF₁meas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hF₁bound)
  have hf_eq : (fun ω => if run k ω = true ∧ tileSlotF P j T M k ω = i
      then tileXi P j T M x k ω else 0) = E_run.indicator F₁ := by
    funext ω
    simp only [hF₁, hE_run]
    by_cases hω : run k ω = true
    · have hm : ω ∈ (run k) ⁻¹' {true} := hω
      by_cases hs : tileSlotF P j T M k ω = i
      · simp [hm, hs, hω]
      · simp [hm, hs, hω]
    · have hm : ω ∉ (run k) ⁻¹' {true} := hω
      simp [hm, hω]
  rw [hf_eq]
  have hm : tileFiltration P j T M x k ≤
      (inferInstance : MeasurableSpace (RandomSources (Torus d m) M)) :=
    (tileFiltration P j T M x).le' k
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm (hF₁int.indicator
    (by
      obtain ⟨Br, hBr, hBrE⟩ := run_preimage P j T M x k run (hrun k hk)
      have hEr : MeasurableSet E_run := by
        rw [hE_run, ← hBrE]
        exact (tileHist_measurable P j T M x k) hBr
      exact hEr)) _ _ _).symm
  · intro s hs _
    exact integrableOn_zero
  · intro s hs _
    have hz : (∫ x in s, (0 : RandomSources (Torus d m) M → ℝ) x
        ∂(sourcesLaw (Torus d m) M)) = 0 := by simp
    rw [hz]
    obtain ⟨B, hB, hBE⟩ := obtain_hist_preimage P j T M x k s hs
    obtain ⟨Br, hBr, hBrE⟩ := run_preimage P j T M x k run (hrun k hk)
    have hinter : s ∩ E_run = tileHist P j T M x k ⁻¹' (B ∩ Br) := by
      rw [← hBE, hE_run, ← hBrE, Set.preimage_inter]
    have hEr : MeasurableSet E_run := by
      rw [hE_run, ← hBrE]
      exact (tileHist_measurable P j T M x k) hBr
    have hzero_ind : ∫ ω in s, E_run.indicator F₁ ω ∂(sourcesLaw (Torus d m) M) = 0 := by
      rw [setIntegral_indicator hEr, hinter]
      exact mean_core C P j T M x hu hj hjm hM hGood k hk i _ (hB.inter hBr)
    exact hzero_ind.symm
  · exact stronglyMeasurable_const.aestronglyMeasurable

/-! ## Variance field: fresh-block independence and moments -/

/-- Coordinate σ-algebras over disjoint index sets are independent. -/
theorem signs_indep_sigma {d m : ℕ}
    (R T : Set (AndersonAC.S2.SignIndex (Torus d m))) (hRT : Disjoint R T) :
    ProbabilityTheory.Indep (⨆ x ∈ R, MeasurableSpace.comap
        (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance)
      (⨆ x ∈ T, MeasurableSpace.comap
        (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance)
      (AndersonAC.S2.signsLaw (Torus d m)) := by
  classical
  have hindep : ProbabilityTheory.iIndepFun
      (fun x : AndersonAC.S2.SignIndex (Torus d m) =>
        fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x)
      (AndersonAC.S2.signsLaw (Torus d m)) :=
    ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
  have hiindep := hindep.iIndep (m := fun _ => inferInstance)
  apply ProbabilityTheory.indep_iSup_of_disjoint _ hiindep hRT
  intro x
  exact (measurable_pi_apply x).comap_le

/-- Fresh-block factorization of integrals. -/
theorem signs_indep_factor {d m : ℕ}
    (R T : Set (AndersonAC.S2.SignIndex (Torus d m))) (hRT : Disjoint R T)
    (X Y : (AndersonAC.S2.SignIndex (Torus d m) → Bool) → ℝ)
    (hX : Measurable[⨆ x ∈ R, MeasurableSpace.comap
      (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance] X)
    (hY : Measurable[⨆ x ∈ T, MeasurableSpace.comap
      (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance] Y)
    (hXint : Integrable X (AndersonAC.S2.signsLaw (Torus d m)))
    (hYint : Integrable Y (AndersonAC.S2.signsLaw (Torus d m))) :
    ∫ ε, X ε * Y ε ∂(AndersonAC.S2.signsLaw (Torus d m)) =
      (∫ ε, X ε ∂(AndersonAC.S2.signsLaw (Torus d m))) *
        (∫ ε, Y ε ∂(AndersonAC.S2.signsLaw (Torus d m))) := by
  classical
  have hIXY : ProbabilityTheory.IndepFun X Y (AndersonAC.S2.signsLaw (Torus d m)) := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro t1 t2 ht1 ht2
    have ht1' : MeasurableSet[⨆ x ∈ R, MeasurableSpace.comap
        (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance] t1 :=
      hX.comap_le _ ht1
    have ht2' : MeasurableSet[⨆ x ∈ T, MeasurableSpace.comap
        (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance] t2 :=
      hY.comap_le _ ht2
    exact (ProbabilityTheory.Indep_iff _ _ _).mp
      (signs_indep_sigma R T hRT) _ _ ht1' ht2'
  exact ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hIXY
    hXint.aestronglyMeasurable hYint.aestronglyMeasurable

/-- Transported suffix second moment: `E[(Z*/√w)²] = t` at final active sites. -/
theorem suffix_second_moment {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (sstar : Torus d m) (hfin : IsFinalSweep m j)
    (hpre : x.prefixLength sstar = m - P.n₀)
    (hw : 0 < sweepW P.u m j) :
    ∫ ε : AndersonAC.S2.SignIndex (Torus d m) → Bool,
      ((AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (x.prefixLength sstar)
        (fun kk => ε (Sum.inl (sstar, kk))) / Real.sqrt (sweepW P.u m j)) ^ 2)
      ∂(AndersonAC.S2.signsLaw (Torus d m)) = sweepScale P.u m j := by
  classical
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  have hj_eq : j = m + 1 := by simp only [IsFinalSweep] at hfin; omega
  subst hj_eq
  have hn0 : P.n₀ ≤ m := by omega
  have hm_eq : P.n₀ + (m - P.n₀) = m := Nat.add_sub_cancel' hn0
  -- tail embedding is injective (unshifted: binarySuffix shifts internally)
  have he : Function.Injective (fun kk : ℕ => (Sum.inl (sstar, kk) :
      AndersonAC.S2.SignIndex (Torus d m))) := by
    intro a b hab
    simp only [Sum.inl.injEq, Prod.mk.injEq] at hab
    exact hab.2
  have hmap : (AndersonAC.S2.signsLaw (Torus d m)).map
      (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool =>
        fun kk : ℕ => ε (Sum.inl (sstar, kk))) =
      Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure) :=
    MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj he
  -- transported second moment of the suffix
  have hE : ∫ ε : AndersonAC.S2.SignIndex (Torus d m) → Bool,
      (AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
        (fun kk => ε (Sum.inl (sstar, kk)))) ^ 2
      ∂(AndersonAC.S2.signsLaw (Torus d m)) =
      (couplingOf P.u P.n₀) ^ 2 / (4 : ℝ) ^ (m - P.n₀) / 3 := by
    have hmom := AndersonAC.S2.binary_suffix_moments (couplingOf P.u P.n₀) (m - P.n₀)
    have hfmeas : Measurable (fun a : ℕ → Bool => (AndersonAC.S2.binarySuffix
        (couplingOf P.u P.n₀) (m - P.n₀) a) ^ 2) :=
      (continuous_id.pow 2).measurable.comp
        (AndersonAC.S2.binarySuffix_measurable _ _)
    have hXmeas : AEMeasurable (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool =>
        fun kk : ℕ => ε (Sum.inl (sstar, kk)))
        (AndersonAC.S2.signsLaw (Torus d m)) :=
      (Measurable.of_eval (fun kk => measurable_pi_apply _)).aemeasurable
    have htrans := integral_map hXmeas hfmeas.aestronglyMeasurable
    rw [hmap] at htrans
    exact htrans.symm.trans hmom.2
  -- scale identity: E[Z²]/w = t
  have hlam : (couplingOf P.u P.n₀) ^ 2 = 3 * P.u / (4 : ℝ) ^ P.n₀ :=
    couplingOf_sq P.u hu0.le P.n₀
  have h4m : (4 : ℝ) ^ m = (4 : ℝ) ^ P.n₀ * (4 : ℝ) ^ (m - P.n₀) := by
    rw [← pow_add, hm_eq]
  have hwt : sweepW P.u m (m + 1) * sweepScale P.u m (m + 1) = P.u / (4 : ℝ) ^ m :=
    wt_final_eq P.u m
  have hEZ : (couplingOf P.u P.n₀) ^ 2 / (4 : ℝ) ^ (m - P.n₀) / 3 =
      sweepW P.u m (m + 1) * sweepScale P.u m (m + 1) := by
    rw [hlam, hwt, h4m]
    field_simp
  simp only [hpre]
  have hdiv : ∀ ε : AndersonAC.S2.SignIndex (Torus d m) → Bool,
      ((AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
        (fun kk => ε (Sum.inl (sstar, kk))) / Real.sqrt (sweepW P.u m (m + 1))) ^ 2) =
        ((AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
          (fun kk => ε (Sum.inl (sstar, kk)))) ^ 2) /
          (sweepW P.u m (m + 1)) := by
    intro ε
    rw [div_pow, Real.sq_sqrt hw.le]
  simp_rw [hdiv]
  rw [integral_div, hE, hEZ]
  have hwne : sweepW P.u m (m + 1) ≠ 0 := ne_of_gt hw
  field_simp

/-! ## Variance field: prefix partition for the suffix case -/

/-- Slot tuple before slot `k` (orders-only). -/
def slotTup {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ)
    (ω : RandomSources (Torus d m) M) : Fin k → Fin (siteCount d m) :=
  fun l => tileSlotF P j T M l.val ω

theorem slotTup_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ) :
    Measurable (slotTup P j T M k) := by
  apply Measurable.of_eval
  intro l
  exact tileSlotF_measurable P j T M l.val

theorem slotTup_injective {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ) (hk : k ≤ slotCount P j T)
    (hM : TileOrderSizes P j T M) (ω : RandomSources (Torus d m) M) :
    Function.Injective (slotTup P j T M k ω) := by
  intro a b hab
  have hinj := tileSlotF_injOnRange P j T M hM k hk ω
  have ha : (a.val : ℕ) ∈ {l | l < k} := a.isLt
  have hb : (b.val : ℕ) ∈ {l | l < k} := b.isLt
  have heq : tileSlotF P j T M a.val ω = tileSlotF P j T M b.val ω := hab
  have := hinj ha hb heq
  exact Fin.ext this

theorem slotTup_mem_image {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ) (hk : k < slotCount P j T)
    (hM : TileOrderSizes P j T M) (ω : RandomSources (Torus d m) M)
    (l : Fin k) : slotTup P j T M k ω l ∈
      (tileSites (P.cover j) T).image (siteRank d m) :=
  tileSlotF_mem_image P j T M hM l.val (lt_trans l.isLt hk) ω

/-- Site values as signs-only functions (orders fixed to `1`). -/
def zsite {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (ε : AndersonAC.S2.SignIndex (Torus d m) → Bool) : ℝ :=
  tileZeta P j T M x s (ε, fun _ => 1)

theorem zsite_eq {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (ω : RandomSources (Torus d m) M) :
    tileZeta P j T M x s ω = zsite P j T M x s ω.1 := rfl

theorem zsite_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) : Measurable (zsite P j T M x s) :=
  (tileZeta_measurable P j T M x s).comp
    (Measurable.prodMk measurable_id measurable_const)

/-- Tonelli factorization over a product piece with signs-only integrand. -/
theorem piece_tonelli {d m : ℕ} (M : ℕ → ℕ)
    (A : Set (AndersonAC.S2.SignIndex (Torus d m) → Bool)) (hA : MeasurableSet A)
    (B : Set ((o : ℕ) → AndersonAC.S2.Order (M o))) (hB : MeasurableSet B)
    (g : (AndersonAC.S2.SignIndex (Torus d m) → Bool) → ℝ)
    (hg_meas : AEStronglyMeasurable g (AndersonAC.S2.signsLaw (Torus d m)))
    (C : ℝ) (hC0 : 0 ≤ C) (hbound : ∀ ε, ‖g ε‖ ≤ C) :
    ∫ ω in A ×ˢ B, g ω.1
      ∂((AndersonAC.S2.signsLaw (Torus d m)).prod (AndersonAC.S2.ordersLaw M)) =
      (∫ ε in A, g ε ∂(AndersonAC.S2.signsLaw (Torus d m))) *
        (AndersonAC.S2.ordersLaw M).real B := by
  classical
  have hfun : (A ×ˢ B).indicator
      (fun ω : (AndersonAC.S2.SignIndex (Torus d m) → Bool) ×
        ((o : ℕ) → AndersonAC.S2.Order (M o)) => g ω.1) =
      fun ω => (A.indicator g ω.1) * (B.indicator 1 ω.2) := by
    funext ⟨ε, π⟩
    by_cases hε : ε ∈ A <;> by_cases hπ : π ∈ B
    · have hmem : (ε, π) ∈ A ×ˢ B := Set.mk_mem_prod hε hπ
      simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hε,
        Set.indicator_of_mem hπ, Pi.one_apply, mul_one]
    · have hmem : (ε, π) ∉ A ×ˢ B := fun h => hπ h.2
      simp only [Set.indicator_of_notMem hmem, Set.indicator_of_mem hε,
        Set.indicator_of_notMem hπ, Pi.one_apply, mul_zero]
    · have hmem : (ε, π) ∉ A ×ˢ B := fun h => hε h.1
      simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hε,
        Pi.one_apply, zero_mul]
    · have hmem : (ε, π) ∉ A ×ˢ B := fun h => hε h.1
      simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hε,
        Pi.one_apply, zero_mul]
  have hInt : Integrable (fun ω : (AndersonAC.S2.SignIndex (Torus d m) → Bool) ×
      ((o : ℕ) → AndersonAC.S2.Order (M o)) =>
      (A.indicator g ω.1) * (B.indicator 1 ω.2))
      ((AndersonAC.S2.signsLaw (Torus d m)).prod (AndersonAC.S2.ordersLaw M)) := by
    have hUae : AEStronglyMeasurable
        (fun ω : (AndersonAC.S2.SignIndex (Torus d m) → Bool) ×
          ((o : ℕ) → AndersonAC.S2.Order (M o)) => A.indicator g ω.1)
        ((AndersonAC.S2.signsLaw (Torus d m)).prod (AndersonAC.S2.ordersLaw M)) :=
      (hg_meas.indicator hA).comp_fst
    have hVmeas : Measurable
        (B.indicator (1 : ((o:ℕ) → AndersonAC.S2.Order (M o)) → ℝ)) :=
      measurable_const.indicator hB
    have hVae : AEStronglyMeasurable
        (fun ω : (AndersonAC.S2.SignIndex (Torus d m) → Bool) ×
          ((o : ℕ) → AndersonAC.S2.Order (M o)) => B.indicator 1 ω.2)
        ((AndersonAC.S2.signsLaw (Torus d m)).prod (AndersonAC.S2.ordersLaw M)) :=
      hVmeas.aestronglyMeasurable.comp_snd
    have hAE : AEStronglyMeasurable (fun ω : (AndersonAC.S2.SignIndex (Torus d m) → Bool) ×
        ((o : ℕ) → AndersonAC.S2.Order (M o)) =>
        (A.indicator g ω.1) * (B.indicator 1 ω.2))
        ((AndersonAC.S2.signsLaw (Torus d m)).prod (AndersonAC.S2.ordersLaw M)) :=
      hUae.mul hVae
    have hbd : ∀ᵐ ω : (AndersonAC.S2.SignIndex (Torus d m) → Bool) ×
        ((o : ℕ) → AndersonAC.S2.Order (M o)) ∂
        ((AndersonAC.S2.signsLaw (Torus d m)).prod (AndersonAC.S2.ordersLaw M)),
        ‖(A.indicator g ω.1) * (B.indicator 1 ω.2)‖ ≤ C := by
      filter_upwards with ⟨ε, π⟩
      have hU : ‖A.indicator g ε‖ ≤ C := by
        by_cases hε : ε ∈ A
        · rw [Set.indicator_of_mem hε]; exact hbound ε
        · rw [Set.indicator_of_notMem hε]; simp; exact hC0
      have hV : ‖B.indicator (1 : ((o:ℕ) → AndersonAC.S2.Order (M o)) → ℝ) π‖ ≤ 1 := by
        by_cases hπ : π ∈ B
        · rw [Set.indicator_of_mem hπ]; simp
        · rw [Set.indicator_of_notMem hπ]; simp
      calc ‖(A.indicator g ε) * (B.indicator 1 π)‖
          = ‖A.indicator g ε‖ * ‖B.indicator 1 π‖ := norm_mul _ _
        _ ≤ C * 1 :=
          mul_le_mul hU hV (norm_nonneg _) hC0
        _ = C := mul_one _
    exact Integrable.of_bound hAE C hbd
  have hVeq : (∫ π, (B.indicator 1) π ∂(AndersonAC.S2.ordersLaw M)) =
      (AndersonAC.S2.ordersLaw M).real B :=
    integral_indicator_one hB
  have hUeq : (∫ ε, (A.indicator g) ε ∂(AndersonAC.S2.signsLaw (Torus d m))) =
      ∫ ε in A, g ε ∂(AndersonAC.S2.signsLaw (Torus d m)) := by
    rw [← integral_indicator hA]
  rw [← integral_indicator (hA.prod hB), hfun, integral_prod _ hInt]
  simp_rw [integral_const_mul]
  rw [integral_mul_const, hUeq, hVeq]

/-- Evaluation at a rest coordinate is measurable w.r.t. the rest σ-algebra. -/
theorem eval_measurable_iSup {d m : ℕ} (R : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (z : AndersonAC.S2.SignIndex (Torus d m)) (hz : z ∈ R) :
    Measurable[⨆ x ∈ R, MeasurableSpace.comap
      (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
      (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε z) :=
  ((comap_measurable
    (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε z)).mono
    (le_biSup (fun x => MeasurableSpace.comap
      (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance) hz)
    le_rfl)

/-- Finite vectors are measurable w.r.t. an iSup from componentwise measurability. -/
theorem measurable_vec_iSup {d m : ℕ} {κ : Type*} {β : κ → Type*}
    [∀ i, MeasurableSpace (β i)]
    (mR : MeasurableSpace (AndersonAC.S2.SignIndex (Torus d m) → Bool))
    (Z : (AndersonAC.S2.SignIndex (Torus d m) → Bool) → ∀ i, β i)
    (hZ : ∀ i, @Measurable _ _ mR _ (fun ε => Z ε i)) :
    @Measurable _ _ mR _ Z := by
  rw [measurable_iff_comap_le]
  show MeasurableSpace.comap (fun b a => Z b a) inferInstance ≤ mR
  rw [MeasurableSpace.comap_process_pi (fun i : κ =>
    fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => Z ε i)]
  exact iSup_le (fun i => (hZ i).comap_le)

/-- A site-Z reading coords inside `R` is measurable w.r.t. the rest σ-algebra. -/
theorem zsite_measurable_of_mem {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (s : Torus d m) (R : Set (AndersonAC.S2.SignIndex (Torus d m)))
    (hR : siteCoords P j T x s ⊆ R) :
    Measurable[⨆ x ∈ R, MeasurableSpace.comap
      (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
      (fun ε => zsite P j T M x s ε) := by
  classical
  rcases siteCoords_cases P j T x s with ⟨hs, hact, hpend, hfin⟩ |
    ⟨hs, hact, hpend, hfin⟩ | ⟨hs, hcon⟩
  · -- digit: single coord
    have hform : ∀ ε, zsite P j T M x s ε = digitAmp P.u (j - 1) *
        signValue (ε (Sum.inl (s, x.prefixLength s))) := by
      intro ε
      have h := zeta_form_digit P j T M x s hact hpend hfin (ε, fun _ => 1)
      simpa [zsite] using h
    have hzR : (Sum.inl (s, x.prefixLength s) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈ R := by
      have hmem : (Sum.inl (s, x.prefixLength s) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈ siteCoords P j T x s := by
        rw [hs]; rfl
      exact hR hmem
    simp_rw [hform]
    exact (measurable_const.mul
      ((measurable_of_finite signValue).comp (eval_measurable_iSup R _ hzR)))
  · -- suffix: whole tail
    have hform : ∀ ε, zsite P j T M x s ε =
        AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (x.prefixLength s)
          (fun kk => ε (Sum.inl (s, kk))) := by
      intro ε
      have h := zeta_form_suffix P j T M x s hact hpend hfin (ε, fun _ => 1)
      simpa [zsite] using h
    have htail : ∀ kk, (Sum.inl (s, kk) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈ R := by
      intro kk
      have hmem : (Sum.inl (s, kk) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈ siteCoords P j T x s := by
        rw [hs]
        exact ⟨kk, rfl⟩
      exact hR hmem
    simp_rw [hform]
    exact (AndersonAC.S2.binarySuffix_measurable _ _).comp
      (measurable_vec_iSup _ (fun ε kk => ε (Sum.inl (s, kk)))
        (fun kk => eval_measurable_iSup R _ (htail kk)))
  · by_cases hact' : activeIn P j T x s
    · have hpend' : s ∈ x.pending := by
        by_contra hcon'
        exact hcon ⟨hact', hcon'⟩
      have hform : ∀ ε, zsite P j T M x s ε = digitAmp P.u (j - 1) *
          signValue (ε (Sum.inr (tileAuxIndex j T 0 s))) := by
        intro ε
        have h := zeta_form_aux P j T M x s hact' hpend' (ε, fun _ => 1)
        simpa [zsite] using h
      have hzR : (Sum.inr (tileAuxIndex j T 0 s) :
          AndersonAC.S2.SignIndex (Torus d m)) ∈ R := by
        have hmem : (Sum.inr (tileAuxIndex j T 0 s) :
          AndersonAC.S2.SignIndex (Torus d m)) ∈ siteCoords P j T x s := by
          rw [hs]; rfl
        exact hR hmem
      simp_rw [hform]
      exact (measurable_const.mul
        ((measurable_of_finite signValue).comp (eval_measurable_iSup R _ hzR)))
    · have hform : ∀ ε, zsite P j T M x s ε =
          Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
            signValue (ε (Sum.inr (tileAuxIndex j T 0 s))) := by
        intro ε
        have h := zeta_form_dummy P j T M x s hact' (ε, fun _ => 1)
        simpa [zsite] using h
      have hzR : (Sum.inr (tileAuxIndex j T 0 s) :
          AndersonAC.S2.SignIndex (Torus d m)) ∈ R := by
        have hmem : (Sum.inr (tileAuxIndex j T 0 s) :
          AndersonAC.S2.SignIndex (Torus d m)) ∈ siteCoords P j T x s := by
          rw [hs]; rfl
        exact hR hmem
      simp_rw [hform]
      exact (measurable_const.mul
        ((measurable_of_finite signValue).comp (eval_measurable_iSup R _ hzR)))

/-- Suffix freshness: `∫_{E'}(ξ*²-t) = 0` for a final active target. -/
def slotTup₂ {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ)
    (π₂ : (o : ℕ) → AndersonAC.S2.Order (M o)) : Fin k → Fin (siteCount d m) :=
  fun l => tileSlotF P j T M l.val ((fun _ => true), π₂)

theorem slotTup_eq {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ)
    (ε : AndersonAC.S2.SignIndex (Torus d m) → Bool)
    (π₂ : (o : ℕ) → AndersonAC.S2.Order (M o)) :
    slotTup P j T M k (ε, π₂) = slotTup₂ P j T M k π₂ := rfl

theorem slotTup₂_measurable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ) :
    Measurable (slotTup₂ P j T M k) :=
  (slotTup_measurable P j T M k).comp
    (Measurable.prodMk measurable_const measurable_id)

theorem suffix_fresh_mean {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (hM : TileOrderSizes P j T M) (hGood : TileGoodCore C P j T x)
    (k : ℕ) (hk : k < slotCount P j T) (i : Fin (siteCount d m))
    (hi : i ∈ (tileSites (P.cover j) T).image (siteRank d m))
    (sstar : Torus d m) (hrs : siteRank d m sstar = i)
    (hact : activeIn P j T x sstar) (hpend : sstar ∉ x.pending)
    (hfin : IsFinalSweep m j)
    (B₁ : Set (Fin k → ℕ × ℝ)) (hB₁ : MeasurableSet B₁) :
    ∫ ω in tileHist P j T M x k ⁻¹' B₁ ∩
        {ω | i ∈ tileRemaining P j T M k ω},
      ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
        sweepScale P.u m j) ∂(sourcesLaw (Torus d m) M) = 0 := by
  classical
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  -- target moment and bound
  have hstar_mem : sstar ∈ tileSites (P.cover j) T := by
    obtain ⟨s, hs, hsi⟩ := Finset.mem_image.mp hi
    have : sstar = s := (siteRank d m).injective (by rw [hrs, hsi])
    rw [this]; exact hs
  have hpre : x.prefixLength sstar = m - P.n₀ :=
    hGood.final_prefix hfin _ hstar_mem hact.2.1
  have hw : 0 < sweepW P.u m j := by
    have hj_eq : j = m + 1 := by simp only [IsFinalSweep] at hfin; omega
    subst hj_eq
    rw [sweepW_final]
    norm_num
  have hform : ∀ ε, zsite P j T M x sstar ε =
      AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
        (fun kk => ε (Sum.inl (sstar, kk))) := by
    intro ε
    have h := zeta_form_suffix P j T M x sstar hact hpend hfin (ε, fun _ => 1)
    simpa [zsite, hpre] using h
  have hEmom : ∫ ε, ((zsite P j T M x sstar ε /
      Real.sqrt (sweepW P.u m j)) ^ 2) ∂(AndersonAC.S2.signsLaw (Torus d m)) =
      sweepScale P.u m j := by
    have h := suffix_second_moment P j T M x hu hj hjm sstar hfin hpre hw
    simpa [hform, hpre] using h
  -- E' and global integrability of the centered square
  set E' : Set (RandomSources (Torus d m) M) :=
    tileHist P j T M x k ⁻¹' B₁ ∩
      (tileRemaining P j T M k) ⁻¹' {s | i ∈ s} with hE'
  have hE'meas : MeasurableSet E' :=
    ((tileHist_measurable P j T M x k) hB₁).inter
      ((of_hist_comap P j T M x k
        (tileRemaining_measurable_comap P j T M x k hM))
        (measurableSet_finset_all {s | i ∈ s}))
  have hYmeas : Measurable (fun ω : RandomSources (Torus d m) M =>
      (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
        sweepScale P.u m j) := by
    have hq : Measurable (fun ω : RandomSources (Torus d m) M =>
        zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) :=
      ((zsite_measurable P j T M x sstar).comp measurable_fst).div_const _
    have hq2 : Measurable (fun ω : RandomSources (Torus d m) M =>
        (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2) := by
      simp_rw [pow_two]
      exact hq.mul hq
    exact hq2.sub measurable_const
  have hYbound : ∀ ω : RandomSources (Torus d m) M,
      ‖(zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
        sweepScale P.u m j‖ ≤
        ((|couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) / Real.sqrt (sweepW P.u m j)) ^ 2 +
          |sweepScale P.u m j|) := by
    intro ω
    have hZb : |zsite P j T M x sstar ω.1| ≤
        |couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) := by
      have hformε := hform ω.1
      have hb := AndersonAC.S2.binarySuffix_bound (couplingOf P.u P.n₀) (m - P.n₀)
        (fun kk => ω.1 (Sum.inl (sstar, kk)))
      rw [hformε]
      exact hb
    calc ‖(zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
          sweepScale P.u m j‖
        ≤ ‖(zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2‖ +
          ‖sweepScale P.u m j‖ := norm_sub_le _ _
      _ = |zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)| ^ 2 +
          |sweepScale P.u m j| := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
      _ ≤ ((|couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) / Real.sqrt (sweepW P.u m j)) ^ 2 +
          |sweepScale P.u m j|) := by
        have hle : |zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)| ≤
            |couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) / Real.sqrt (sweepW P.u m j) := by
          rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact div_le_div_of_nonneg_right hZb (Real.sqrt_nonneg _)
        apply add_le_add _ le_rfl
        exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  have hYint : Integrable (fun ω : RandomSources (Torus d m) M =>
      (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
        sweepScale P.u m j) (sourcesLaw (Torus d m) M) :=
    Integrable.of_bound hYmeas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hYbound)
  -- per-prefix pieces
  have hpiece : ∀ p : Fin k → Fin (siteCount d m),
      ∫ ω in E' ∩ slotTup P j T M k ⁻¹' {p},
        ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
          sweepScale P.u m j) ∂(sourcesLaw (Torus d m) M) = 0 := by
    intro p
    by_cases hinjp : Function.Injective p
    · by_cases himg : ∀ l, p l ∈ (tileSites (P.cover j) T).image (siteRank d m)
      · by_cases hmem : ∃ l, p l = i
        · -- i exposed on this prefix: E' needs i unexposed, so empty
          have hempty : E' ∩ slotTup P j T M k ⁻¹' {p} = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro ω hω
            obtain ⟨hE'ω, hO'ω⟩ := hω
            have hri : i ∈ tileRemaining P j T M k ω := hE'ω.2
            obtain ⟨l, hl⟩ := hmem
            have hpω : slotTup P j T M k ω = p :=
              Set.mem_singleton_iff.mp hO'ω
            have hslot : slotTup P j T M k ω l = i := by
              rw [hpω]; exact hl
            have h2 : tileSlotF P j T M l.val ω = i := hslot
            have hremω : tileRemaining P j T M k ω =
                ((tileSites (P.cover j) T).image (siteRank d m)) \
                  ((Finset.range k).image fun l => tileSlotF P j T M l ω) := rfl
            rw [hremω] at hri
            have hcon : i ∈ (Finset.range k).image
                (fun l => tileSlotF P j T M l ω) :=
              Finset.mem_image.mpr ⟨l.val, Finset.mem_range.mpr l.isLt, h2⟩
            exact (Finset.mem_sdiff.mp hri).2 hcon
          rw [hempty]
          exact setIntegral_empty
        · -- MAIN CASE: product form + Tonelli + independence
          -- exposed sites are distinct and fresh
          have hdist : ∀ l₁ l₂ : Fin k, l₁ ≠ l₂ →
              (siteRank d m).symm (p l₁) ≠ (siteRank d m).symm (p l₂) := by
            intro l₁ l₂ hne hcon
            apply hne
            have h1 := congrArg (siteRank d m) hcon
            simp only [Equiv.apply_symm_apply] at h1
            exact hinjp h1
          have hfresh : ∀ l : Fin k, (siteRank d m).symm (p l) ≠ sstar := by
            intro l hcon
            apply hmem
            refine ⟨l, ?_⟩
            have h1 := congrArg (siteRank d m) hcon
            simp only [Equiv.apply_symm_apply, hrs] at h1
            exact h1
          -- coordinate blocks
          set R : Set (AndersonAC.S2.SignIndex (Torus d m)) :=
            ⋃ l : Fin k, siteCoords P j T x ((siteRank d m).symm (p l)) with hR
          set Tgt : Set (AndersonAC.S2.SignIndex (Torus d m)) :=
            siteCoords P j T x sstar with hTgt
          have hRT : Disjoint R Tgt := by
            rw [Set.disjoint_left]
            intro z hz hzT
            simp only [hR, Set.mem_iUnion] at hz
            obtain ⟨l, hzl⟩ := hz
            exact Set.disjoint_left.mp
              (siteCoords_disjoint P j T x (hfresh l)) hzl hzT
          -- Z vector, section, pieces
          set Zvec : (AndersonAC.S2.SignIndex (Torus d m) → Bool) → (Fin k → ℝ) :=
            fun ε l => zsite P j T M x ((siteRank d m).symm (p l)) ε /
              Real.sqrt (sweepW P.u m j) with hZvec
          have hZvec_meas : Measurable[⨆ x ∈ R, MeasurableSpace.comap
              (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
              Zvec := by
            apply measurable_vec_iSup
            intro l
            have hsub : siteCoords P j T x ((siteRank d m).symm (p l)) ⊆ R :=
              Set.subset_iUnion (fun l =>
                siteCoords P j T x ((siteRank d m).symm (p l))) l
            exact ((zsite_measurable_of_mem P j T M x _ R hsub).div measurable_const)
          set Phi : (Fin k → ℝ) → (Fin k → ℕ × ℝ) :=
            fun v l => ((p l).val, v l) with hPhi
          have hPhi_meas : Measurable Phi := by
            apply Measurable.of_eval
            intro l
            exact Measurable.prodMk measurable_const (measurable_pi_apply l)
          set Sp : Set (Fin k → ℝ) := Phi ⁻¹' B₁ with hSp
          have hSp_meas : MeasurableSet Sp := hPhi_meas hB₁
          set Ap : Set (AndersonAC.S2.SignIndex (Torus d m) → Bool) :=
            Zvec ⁻¹' Sp with hAp
          set Bp : Set ((o : ℕ) → AndersonAC.S2.Order (M o)) :=
            slotTup₂ P j T M k ⁻¹' {p} with hBp
          have hBp_meas : MeasurableSet Bp :=
            (slotTup₂_measurable P j T M k) (measurableSet_singleton p)
          have hAp_amb : MeasurableSet Ap := by
            have hZvec_amb : Measurable Zvec := by
              apply Measurable.of_eval
              intro l
              simp only [hZvec]
              exact ((zsite_measurable P j T M x _).div_const _)
            exact hZvec_amb hSp_meas
          -- X, Y for independence
          set X : (AndersonAC.S2.SignIndex (Torus d m) → Bool) → ℝ :=
            Ap.indicator 1 with hX
          set Y : (AndersonAC.S2.SignIndex (Torus d m) → Bool) → ℝ :=
            fun ε => (zsite P j T M x sstar ε /
              Real.sqrt (sweepW P.u m j)) ^ 2 - sweepScale P.u m j with hY
          have hXmeas : Measurable[⨆ x ∈ R, MeasurableSpace.comap
              (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
              X := by
            have hApR : MeasurableSet[⨆ x ∈ R, MeasurableSpace.comap
                (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
                Ap :=
              hZvec_meas hSp_meas
            simp only [hX]
            exact measurable_const.indicator hApR
          have hYmeasT : Measurable[⨆ x ∈ Tgt, MeasurableSpace.comap
              (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
              Y := by
            have hbase := zsite_measurable_of_mem P j T M x sstar Tgt le_rfl
            have hq : Measurable[⨆ x ∈ Tgt, MeasurableSpace.comap
                (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
                (fun ε => zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) :=
              hbase.div measurable_const
            have hq2 : Measurable[⨆ x ∈ Tgt, MeasurableSpace.comap
                (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
                (fun ε => (zsite P j T M x sstar ε /
                  Real.sqrt (sweepW P.u m j)) ^ 2) := by
              simp_rw [pow_two]
              exact hq.mul hq
            simp only [hY]
            exact hq2.sub measurable_const
          -- Yu (uncentered) for the factor
          set Yu : (AndersonAC.S2.SignIndex (Torus d m) → Bool) → ℝ :=
            fun ε => (zsite P j T M x sstar ε /
              Real.sqrt (sweepW P.u m j)) ^ 2 with hYu
          have hYumeasT : Measurable[⨆ x ∈ Tgt, MeasurableSpace.comap
              (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
              Yu := by
            have hbase := zsite_measurable_of_mem P j T M x sstar Tgt le_rfl
            have hq : Measurable[⨆ x ∈ Tgt, MeasurableSpace.comap
                (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool => ε x) inferInstance]
                (fun ε => zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) :=
              hbase.div measurable_const
            simp only [hYu]
            simp_rw [pow_two]
            exact hq.mul hq
          have hYumeas_amb : Measurable Yu := by
            simp only [hYu]
            have hq : Measurable (fun ε : AndersonAC.S2.SignIndex (Torus d m) → Bool =>
                zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) :=
              (zsite_measurable P j T M x sstar).div_const _
            simp_rw [pow_two]
            exact hq.mul hq
          have hYubound : ∀ ε, ‖Yu ε‖ ≤
              (|couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) /
                Real.sqrt (sweepW P.u m j)) ^ 2 := by
            intro ε
            have hZb : |zsite P j T M x sstar ε| ≤
                |couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) := by
              have hformε := hform ε
              have hb := AndersonAC.S2.binarySuffix_bound (couplingOf P.u P.n₀)
                (m - P.n₀) (fun kk => ε (Sum.inl (sstar, kk)))
              rw [hformε]
              exact hb
            simp only [hYu]
            rw [Real.norm_eq_abs, abs_pow]
            apply pow_le_pow_left₀ (abs_nonneg _) _ 2
            rw [abs_div]
            rw [abs_of_nonneg (Real.sqrt_nonneg _)]
            exact div_le_div_of_nonneg_right hZb (Real.sqrt_nonneg _)
          have hYuint : Integrable Yu (AndersonAC.S2.signsLaw (Torus d m)) :=
            Integrable.of_bound hYumeas_amb.aestronglyMeasurable _
              (Filter.Eventually.of_forall hYubound)
          have hXint : Integrable X (AndersonAC.S2.signsLaw (Torus d m)) := by
            have hXamb : Measurable X := by
              simp only [hX]
              exact measurable_const.indicator hAp_amb
            have hAE : AEStronglyMeasurable X (AndersonAC.S2.signsLaw (Torus d m)) :=
              hXamb.aestronglyMeasurable
            have hbd : ∀ᵐ ε ∂(AndersonAC.S2.signsLaw (Torus d m)), ‖X ε‖ ≤ 1 := by
              filter_upwards with ε
              simp only [hX]
              by_cases h : ε ∈ Ap <;> simp [h, Set.indicator_of_mem, Set.indicator_of_notMem]
            exact Integrable.of_bound hAE 1 hbd
          -- factor: E[X·Yu] = E[X]·t
          have hfactor : ∫ ε, X ε * Yu ε ∂(AndersonAC.S2.signsLaw (Torus d m)) =
              (∫ ε, X ε ∂(AndersonAC.S2.signsLaw (Torus d m))) *
                sweepScale P.u m j := by
            have h := signs_indep_factor R Tgt hRT X Yu hXmeas hYumeasT hXint hYuint
            have hEY : ∫ ε, Yu ε ∂(AndersonAC.S2.signsLaw (Torus d m)) =
                sweepScale P.u m j := hEmom
            rw [h, hEY]
          -- Ap-indicator connection
          have hApYu : ∫ ε in Ap, Yu ε ∂(AndersonAC.S2.signsLaw (Torus d m)) =
              ((AndersonAC.S2.signsLaw (Torus d m)).real Ap) *
                sweepScale P.u m j := by
            have hfun : Ap.indicator Yu = fun ε => X ε * Yu ε := by
              funext ε
              simp only [hX]
              by_cases h : ε ∈ Ap
              · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply,
                  one_mul]
              · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
            have hXmean : ∫ ε, X ε ∂(AndersonAC.S2.signsLaw (Torus d m)) =
                (AndersonAC.S2.signsLaw (Torus d m)).real Ap := by
              have : X = Ap.indicator 1 := rfl
              rw [this]
              exact integral_indicator_one hAp_amb
            calc ∫ ε in Ap, Yu ε ∂(AndersonAC.S2.signsLaw (Torus d m))
                = ∫ ε, Ap.indicator Yu ε ∂(AndersonAC.S2.signsLaw (Torus d m)) := by
                  rw [integral_indicator hAp_amb]
              _ = ∫ ε, X ε * Yu ε ∂(AndersonAC.S2.signsLaw (Torus d m)) := by
                  rw [hfun]
              _ = _ := by rw [hfactor, hXmean]
          -- centered inner integral vanishes
          have hCinner : ∫ ε in Ap, (Yu ε - sweepScale P.u m j)
              ∂(AndersonAC.S2.signsLaw (Torus d m)) = 0 := by
            have h1 : IntegrableOn Yu Ap (AndersonAC.S2.signsLaw (Torus d m)) :=
              hYuint.integrableOn
            have h2 : IntegrableOn (fun _ => sweepScale P.u m j) Ap
                (AndersonAC.S2.signsLaw (Torus d m)) :=
              integrable_const _
            rw [integral_sub h1 h2, hApYu]
            rw [setIntegral_const]
            simp [smul_eq_mul]
          -- product form of the piece
          have hhist_eq : ∀ ω ∈ slotTup P j T M k ⁻¹' {p},
              tileHist P j T M x k ω = Phi (Zvec ω.1) := by
            intro ω hω
            have hslot : slotTup P j T M k ω = p := by
              simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hω
            obtain ⟨ε, π₂⟩ := ω
            funext lf
            have hsl : tileSlotF P j T M lf.val (ε, π₂) = p lf :=
              congrFun hslot lf
            have hsite : tileSlot P j T M lf.val (ε, π₂) =
                (siteRank d m).symm (p lf) := by
              apply (siteRank d m).injective
              have h1 : siteRank d m (tileSlot P j T M lf.val (ε, π₂)) = p lf := hsl
              rw [h1]
              exact (Equiv.apply_symm_apply _ _).symm
            have hxi : tileXi P j T M x lf.val (ε, π₂) = Zvec ε lf := by
              unfold tileXi
              rw [hsite]
              simp only [hZvec]
              congr 1
            simp only [tileHist, hPhi]
            congr 1
            · exact congrArg Fin.val hsl
          have hprod : E' ∩ slotTup P j T M k ⁻¹' {p} = Ap ×ˢ Bp := by
            ext ⟨ε, π₂⟩
            constructor
            · intro hmem
              obtain ⟨hE'ω, hO'ω⟩ := hmem
              have hslot : slotTup P j T M k (ε, π₂) = p := by
                simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hO'ω
              have hBpmem : π₂ ∈ Bp := by
                have h1 : slotTup₂ P j T M k π₂ = p := by
                  have h2 : slotTup₂ P j T M k π₂ = slotTup P j T M k (ε, π₂) :=
                    (slotTup_eq P j T M k ε π₂).symm
                  rw [h2, hslot]
                simpa only [hBp, Set.mem_preimage, Set.mem_singleton_iff] using h1
              have hApmem : ε ∈ Ap := by
                have h1 : Phi (Zvec ε) ∈ B₁ := by
                  have hO' : (ε, π₂) ∈ slotTup P j T M k ⁻¹' {p} := by
                    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hslot
                  have h2 := hhist_eq (ε, π₂) hO'
                  rw [← h2]
                  have hB₁mem : tileHist P j T M x k (ε, π₂) ∈ B₁ := by
                    simpa only [hE', Set.mem_inter_iff, Set.mem_preimage] using hE'ω.1
                  exact hB₁mem
                simpa only [hAp, hSp, Set.mem_preimage] using h1
              exact Set.mk_mem_prod hApmem hBpmem
            · intro hmem
              obtain ⟨hApmem, hBpmem⟩ := hmem
              have hslot : slotTup P j T M k (ε, π₂) = p := by
                have h1 : slotTup₂ P j T M k π₂ = p := by
                  simpa only [hBp, Set.mem_preimage, Set.mem_singleton_iff] using hBpmem
                have h2 : slotTup P j T M k (ε, π₂) = slotTup₂ P j T M k π₂ :=
                  slotTup_eq P j T M k ε π₂
                rw [h2, h1]
              refine ⟨?_, ?_⟩
              · -- E' membership
                have hO' : (ε, π₂) ∈ slotTup P j T M k ⁻¹' {p} := by
                  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hslot
                have hB₁mem : tileHist P j T M x k (ε, π₂) ∈ B₁ := by
                  have h2 := hhist_eq (ε, π₂) hO'
                  rw [h2]
                  have h3 : Phi (Zvec ε) ∈ B₁ := by
                    simpa only [hAp, hSp, Set.mem_preimage] using hApmem
                  exact h3
                have hrem : i ∈ tileRemaining P j T M k (ε, π₂) := by
                  have hremω : tileRemaining P j T M k (ε, π₂) =
                      ((tileSites (P.cover j) T).image (siteRank d m)) \
                        ((Finset.range k).image fun l => tileSlotF P j T M l (ε, π₂)) := rfl
                  rw [hremω]
                  refine Finset.mem_sdiff.mpr ⟨hi, ?_⟩
                  intro hcon
                  obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hcon
                  rw [Finset.mem_range] at hl
                  have hsl : tileSlotF P j T M l (ε, π₂) = p ⟨l, hl⟩ :=
                    congrFun hslot ⟨l, hl⟩
                  rw [hsl] at heq
                  exact hmem ⟨⟨l, hl⟩, heq⟩
                show (ε, π₂) ∈ E'
                simpa only [hE', Set.mem_inter_iff, Set.mem_preimage,
                  Set.mem_singleton_iff, Set.mem_ofPred_eq] using ⟨hB₁mem, hrem⟩
              · -- O' membership
                show (ε, π₂) ∈ slotTup P j T M k ⁻¹' {p}
                simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hslot
          -- Tonelli + conclusion
          have hTon : ∫ ω in Ap ×ˢ Bp,
              ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
                sweepScale P.u m j)
              ∂((AndersonAC.S2.signsLaw (Torus d m)).prod
                (AndersonAC.S2.ordersLaw M)) = 0 := by
            have hgA : AEStronglyMeasurable (fun ε :
                AndersonAC.S2.SignIndex (Torus d m) → Bool =>
                (zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) ^ 2 -
                  sweepScale P.u m j) (AndersonAC.S2.signsLaw (Torus d m)) := by
              exact (hYumeas_amb.sub measurable_const).aestronglyMeasurable
            have hgb : ∀ ε : AndersonAC.S2.SignIndex (Torus d m) → Bool,
                ‖(zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) ^ 2 -
                  sweepScale P.u m j‖ ≤
                ((|couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) /
                  Real.sqrt (sweepW P.u m j)) ^ 2 + |sweepScale P.u m j|) := by
              intro ε
              have hZb : |zsite P j T M x sstar ε| ≤
                  |couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) := by
                have hformε := hform ε
                have hb := AndersonAC.S2.binarySuffix_bound (couplingOf P.u P.n₀)
                  (m - P.n₀) (fun kk => ε (Sum.inl (sstar, kk)))
                rw [hformε]
                exact hb
              have hle : |zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)| ≤
                  |couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) / Real.sqrt (sweepW P.u m j) := by
                rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
                exact div_le_div_of_nonneg_right hZb (Real.sqrt_nonneg _)
              calc ‖(zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) ^ 2 -
                    sweepScale P.u m j‖
                  ≤ ‖(zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) ^ 2‖ +
                    ‖sweepScale P.u m j‖ := norm_sub_le _ _
                _ = |zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)| ^ 2 +
                    |sweepScale P.u m j| := by
                    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
                _ ≤ _ := by
                  apply add_le_add _ le_rfl
                  exact pow_le_pow_left₀ (abs_nonneg _) hle 2
            have hC0 : (0 : ℝ) ≤ ((|couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) /
                Real.sqrt (sweepW P.u m j)) ^ 2 + |sweepScale P.u m j|) := by
              positivity
            rw [piece_tonelli M Ap hAp_amb Bp hBp_meas _ hgA _ hC0
              (fun ε => hgb ε)]
            have hcc : (∫ ε in Ap, ((zsite P j T M x sstar ε /
                Real.sqrt (sweepW P.u m j)) ^ 2 - sweepScale P.u m j)
                ∂(AndersonAC.S2.signsLaw (Torus d m))) =
                ∫ ε in Ap, (Yu ε - sweepScale P.u m j)
                ∂(AndersonAC.S2.signsLaw (Torus d m)) := rfl
            rw [hcc, hCinner, zero_mul]
          -- conclude the piece from the product form
          rw [hprod]
          exact hTon
      · -- a prefix value outside the tile: slots never take it
        have hempty : slotTup P j T M k ⁻¹' ({p} : Set _) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro ω hω
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
          rw [not_forall] at himg
          obtain ⟨l, hl⟩ := himg
          have hmem : slotTup P j T M k ω l ∈
              (tileSites (P.cover j) T).image (siteRank d m) :=
            slotTup_mem_image P j T M k hk hM ω l
          rw [hω] at hmem
          exact hl hmem
        have hempty2 : E' ∩ slotTup P j T M k ⁻¹' {p} = ∅ := by
          rw [hempty, Set.inter_empty]
        rw [hempty2]
        exact setIntegral_empty
    · -- non-injective prefix: slots are always injective
      have hempty : slotTup P j T M k ⁻¹' ({p} : Set _) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro ω hω
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
        have hinjω := slotTup_injective P j T M k (le_of_lt hk) hM ω
        rw [hω] at hinjω
        exact hinjp hinjω
      have hempty2 : E' ∩ slotTup P j T M k ⁻¹' {p} = ∅ := by
        rw [hempty, Set.inter_empty]
      rw [hempty2]
      exact setIntegral_empty
  -- partition assembly
  have hcover : (⋃ p : Fin k → Fin (siteCount d m),
      (E' ∩ slotTup P j T M k ⁻¹' {p})) = E' := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨p, hE'ω, -⟩
      exact hE'ω
    · intro hE'ω
      exact ⟨slotTup P j T M k ω, hE'ω, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun p : Fin k → Fin (siteCount d m) =>
      E' ∩ slotTup P j T M k ⁻¹' {p}) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    have hpω : slotTup P j T M k ω = p := Set.mem_singleton_iff.mp h2
    have hqω : slotTup P j T M k ω = q := Set.mem_singleton_iff.mp h4
    exact hpq (hpω.symm.trans hqω)
  have hmeas : ∀ p : Fin k → Fin (siteCount d m),
      MeasurableSet (E' ∩ slotTup P j T M k ⁻¹' {p}) := by
    intro p
    exact hE'meas.inter ((slotTup_measurable P j T M k) (measurableSet_singleton p))
  have hint : ∀ p : Fin k → Fin (siteCount d m),
      IntegrableOn (fun ω : RandomSources (Torus d m) M =>
        (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
          sweepScale P.u m j) (E' ∩ slotTup P j T M k ⁻¹' {p})
        (sourcesLaw (Torus d m) M) :=
    fun p => hYint.integrableOn
  have hgoal : (∫ ω in E', ((zsite P j T M x sstar ω.1 /
      Real.sqrt (sweepW P.u m j)) ^ 2 - sweepScale P.u m j)
      ∂(sourcesLaw (Torus d m) M)) = 0 := by
    rw [← hcover, integral_iUnion_fintype hmeas hdisj hint]
    exact Finset.sum_eq_zero (fun p _ => hpiece p)
  exact hgoal

/-- Weighted orbit sum: slot-indicator times target square. -/
theorem orbit_sum_weighted {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (k : ℕ) (hk : k < slotCount P j T)
    (hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card)
    (i : Fin (siteCount d m)) (sstar : Torus d m)
    (hrs : siteRank d m sstar = i) (ω : RandomSources (Torus d m) M) :
    (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN (M (tileOrderIndex j T 0)) k,
      (if tileSlotF P j T M k
          (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
        then (tileXi P j T M x k (orderSwap d m M (tileOrderIndex j T 0) k τ ω)) ^ 2
        else 0))
    = (if i ∈ tileRemaining P j T M k ω
        then ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) *
          (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2
        else 0) := by
  classical
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  have hterm : ∀ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
      (M (tileOrderIndex j T 0)) k,
      (if tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
        then (tileXi P j T M x k (orderSwap d m M (tileOrderIndex j T 0) k τ ω)) ^ 2
        else 0)
      = (if tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
        then (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2
        else 0) := by
    intro τ
    by_cases hs : tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
    · have hs2 : siteRank d m
          (tileSlot P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω)) = i := hs
      have hsk : tileSlot P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) =
          sstar :=
        (siteRank d m).injective (hs2.trans hrs.symm)
      rw [if_pos hs, if_pos hs]
      unfold tileXi
      rw [hsk]
      rfl
    · rw [if_neg hs, if_neg hs]
  rw [Finset.sum_congr rfl (fun τ _ => hterm τ)]
  have hfac : (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
      (M (tileOrderIndex j T 0)) k,
      (if tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
        then (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2
        else 0))
      = (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 *
        (∑ τ : AndersonAC.SolS2.OrderCompletionCore.StabN
          (M (tileOrderIndex j T 0)) k,
          (if tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
            then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    by_cases h : tileSlotF P j T M k (orderSwap d m M (tileOrderIndex j T 0) k τ ω) = i
    · simp only [if_pos h, mul_one]
    · simp only [if_neg h, mul_zero]
  rw [hfac, orbit_sum_uniform P j T M x k hk hM0 i ω]
  by_cases hri : i ∈ tileRemaining P j T M k ω <;> simp [hri, mul_comm]

/-- Variance core: run-free conditional second moment on history preimages. -/
theorem variance_core {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (hM : TileOrderSizes P j T M) (hGood : TileGoodCore C P j T x)
    (k : ℕ) (hk : k < slotCount P j T) (i : Fin (siteCount d m))
    (B₁ : Set (Fin k → ℕ × ℝ)) (hB₁ : MeasurableSet B₁) :
    ∫ ω in tileHist P j T M x k ⁻¹' B₁,
      (if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0)
      ∂(sourcesLaw (Torus d m) M) =
      ∫ ω in tileHist P j T M x k ⁻¹' B₁,
      (if i ∈ tileRemaining P j T M k ω
        then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0)
      ∂(sourcesLaw (Torus d m) M) := by
  classical
  have hM0 : M (tileOrderIndex j T 0) = (tileSites (P.cover j) T).card := hM 0
  have hkM : k < M (tileOrderIndex j T 0) := by rw [hM0]; exact hk
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  have htpos : 0 < sweepScale P.u m j :=
    sweepScale_pos' (lt_trans (by norm_num) hu.1) m j
  -- F₂ integrable
  have hxi2meas : Measurable (fun ω : RandomSources (Torus d m) M =>
      (tileXi P j T M x k ω) ^ 2) := by
    simp_rw [pow_two]
    exact (tileXi_measurable P j T M x k).mul (tileXi_measurable P j T M x k)
  have hF₂meas : Measurable (fun ω : RandomSources (Torus d m) M =>
      if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0) := by
    have heq : (fun ω : RandomSources (Torus d m) M =>
        if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0) =
        fun ω => if ω ∈ (tileSlotF P j T M k) ⁻¹' {i}
        then (tileXi P j T M x k ω) ^ 2 else 0 := by
      funext ω
      by_cases h : tileSlotF P j T M k ω = i
      · rw [if_pos h, if_pos (by simpa using h)]
      · rw [if_neg h, if_neg (by simpa using h)]
    rw [heq]
    exact Measurable.ite ((tileSlotF_measurable P j T M k) (measurableSet_singleton i))
      hxi2meas measurable_const
  have hF₂bound : ∀ ω : RandomSources (Torus d m) M,
      ‖(if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0)‖ ≤
        (2 * Real.sqrt (sweepScale P.u m j)) ^ 2 := by
    intro ω
    by_cases h : tileSlotF P j T M k ω = i
    · simp only [h, if_true]
      have hb := tileXi_bound_pointwise C P j T M x hu hj hjm hM hGood k hk ω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    · simp [h]
  have hF₂int : Integrable (fun ω : RandomSources (Torus d m) M =>
      if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0)
      (sourcesLaw (Torus d m) M) :=
    Integrable.of_bound hF₂meas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hF₂bound)
  have hE₁meas : MeasurableSet (tileHist P j T M x k ⁻¹' B₁) :=
    (tileHist_measurable P j T M x k) hB₁
  -- i outside the tile: both sides vanish pointwise
  by_cases hi : i ∈ (tileSites (P.cover j) T).image (siteRank d m)
  · -- main case
    set sstar : Torus d m := (siteRank d m).symm i with hsstar
    have hrs : siteRank d m sstar = i := (siteRank d m).apply_symm_apply i
    have hstar_mem : sstar ∈ tileSites (P.cover j) T := by
      obtain ⟨s, hs, hsi⟩ := Finset.mem_image.mp hi
      have : sstar = s := (siteRank d m).injective (by rw [hrs, hsi])
      rw [this]; exact hs
    -- Step 1: orbit average equals the target-square form
    have hStep1 : ∫ ω in tileHist P j T M x k ⁻¹' B₁,
        (if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0)
        ∂(sourcesLaw (Torus d m) M) =
        ∫ ω in tileHist P j T M x k ⁻¹' B₁,
        (if i ∈ tileRemaining P j T M k ω
          then (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 /
            ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ) else 0)
        ∂(sourcesLaw (Torus d m) M) := by
      have havg := orbit_avg_integral M (tileOrderIndex j T 0) k
        (E := tileHist P j T M x k ⁻¹' B₁) hE₁meas
        (fun τ => histPreimage_swap_invariant P j T M x k hkM τ B₁)
        (fun ω : RandomSources (Torus d m) M =>
          if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0)
        hF₂int
      rw [havg]
      apply setIntegral_congr_ae hE₁meas
      filter_upwards with ω _
      -- pointwise orbit average
      have hS := orbit_sum_weighted P j T M x k hk hM0 i sstar hrs ω
      have hcardG : (Fintype.card
          (AndersonAC.SolS2.OrderCompletionCore.StabN
            (M (tileOrderIndex j T 0)) k) : ℝ) =
          ((M (tileOrderIndex j T 0) - k).factorial : ℝ) := by
        rw [AndersonAC.SolS2.OrderCompletionCore.StabN.card_eq _ _ (le_of_lt hkM)]
      have hfact : ((M (tileOrderIndex j T 0) - k).factorial : ℝ) =
          (((M (tileOrderIndex j T 0) - k : ℕ)) : ℝ) *
            ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) := by
        have hfactN : (M (tileOrderIndex j T 0) - k).factorial =
            (M (tileOrderIndex j T 0) - k) * (M (tileOrderIndex j T 0) - k - 1).factorial := by
          conv_lhs => rw [show M (tileOrderIndex j T 0) - k =
            M (tileOrderIndex j T 0) - k - 1 + 1 by omega]
          rw [Nat.factorial_succ, show M (tileOrderIndex j T 0) - k - 1 + 1 =
            M (tileOrderIndex j T 0) - k by omega]
        rw [hfactN, Nat.cast_mul]
      have hfact0 : ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hratio : ((M (tileOrderIndex j T 0) - k).factorial : ℝ)⁻¹ *
          ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) =
          1 / (((M (tileOrderIndex j T 0) - k : ℕ)) : ℝ) := by
        rw [hfact, mul_inv, mul_assoc, inv_mul_cancel₀ hfact0, mul_one,
          inv_eq_one_div]
      have he : ((M (tileOrderIndex j T 0) - k).factorial : ℝ)⁻¹ *
          (((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) *
            (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2) =
          (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 /
            (((M (tileOrderIndex j T 0) - k : ℕ)) : ℝ) := by
        have e2 : ((M (tileOrderIndex j T 0) - k).factorial : ℝ)⁻¹ *
            (((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ) *
              (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2) =
            ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2) *
              (((M (tileOrderIndex j T 0) - k).factorial : ℝ)⁻¹ *
                ((M (tileOrderIndex j T 0) - k - 1).factorial : ℝ)) := by
          ring
        rw [e2, hratio, mul_one_div]
      -- combine with the orbit sum
      rw [hS]
      by_cases hri : i ∈ tileRemaining P j T M k ω
      · rw [if_pos hri, if_pos hri, hcardG]
        exact he
      · rw [if_neg hri, if_neg hri, mul_zero]
    -- Step 2 setup: E' split
    set E' : Set (RandomSources (Torus d m) M) :=
      tileHist P j T M x k ⁻¹' B₁ ∩ {ω | i ∈ tileRemaining P j T M k ω} with hE'
    have hE'meas : MeasurableSet E' :=
      hE₁meas.inter
        (show MeasurableSet ((tileRemaining P j T M k) ⁻¹' {s | i ∈ s}) from
          (of_hist_comap P j T M x k
            (tileRemaining_measurable_comap P j T M x k hM))
            (measurableSet_finset_all {s | i ∈ s}))
    -- Centered target square: integrable, with vanishing integral over E'.
    -- Single-sign sites (digit/aux/dummy) are pointwise `= t`; the final-sweep
    -- suffix uses fresh-block independence (`suffix_fresh_mean`).
    have hYZ : Integrable (fun ω : RandomSources (Torus d m) M =>
        (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
          sweepScale P.u m j) (sourcesLaw (Torus d m) M)
        ∧ ∫ ω in E',
          ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
            sweepScale P.u m j) ∂(sourcesLaw (Torus d m) M) = 0 := by
      have hwpos_gen : 0 < sweepW P.u m j := by
        by_cases hfin : IsFinalSweep m j
        · have hj_eq : j = m + 1 := by simp only [IsFinalSweep] at hfin; omega
          subst hj_eq
          rw [sweepW_final]
          norm_num
        · have hjm' : j ≤ m := by simp only [IsFinalSweep] at hfin; omega
          have hj0 : 0 < j := by omega
          exact sweepW_pos_of_digit hu hj0 hjm'
      -- pointwise assembly used by the single-sign cases
      have hzero_of : (∀ ε : AndersonAC.S2.SignIndex (Torus d m) → Bool,
          ((zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) ^ 2) =
            sweepScale P.u m j) →
          Integrable (fun ω : RandomSources (Torus d m) M =>
            (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) (sourcesLaw (Torus d m) M)
          ∧ ∫ ω in E',
            ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) ∂(sourcesLaw (Torus d m) M) = 0 := by
        intro hsq
        have h0 : ∀ ω ∈ E',
            ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) = 0 := by
          intro ω _
          rw [hsq ω.1, sub_self]
        have hcongr : Set.EqOn (fun ω : RandomSources (Torus d m) M =>
            (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) 0 E' :=
          fun ω hω => h0 ω hω
        have hYeq : (fun ω : RandomSources (Torus d m) M =>
            (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) = 0 := by
          funext ω
          simp only [Pi.zero_apply]
          rw [hsq ω.1, sub_self]
        rw [hYeq]
        refine ⟨integrable_zero _ _ _, by simp⟩
      rcases siteCoords_cases P j T x sstar with ⟨hs, hact, hpend, hfin⟩ |
        ⟨hs, hact, hpend, hfin⟩ | ⟨hs, hcon⟩
      · -- digit: pointwise square law
        have hjm' : j ≤ m := by simp only [IsFinalSweep] at hfin; omega
        have hj0 : 0 < j := by omega
        apply hzero_of
        intro ε
        have h := Zsq_single P j T M x sstar _ _
          (zeta_form_digit P j T M x sstar hact hpend hfin)
          (digitAmp_sq_eq_wt hu hj0 hjm') hwpos_gen (ε, fun _ => 1)
        simpa [zsite] using h
      · -- suffix: fresh-block independence
        have hpre : x.prefixLength sstar = m - P.n₀ :=
          hGood.final_prefix hfin _ hstar_mem hact.2.1
        have hformS : ∀ ε : AndersonAC.S2.SignIndex (Torus d m) → Bool,
            zsite P j T M x sstar ε =
              AndersonAC.S2.binarySuffix (couplingOf P.u P.n₀) (m - P.n₀)
                (fun kk => ε (Sum.inl (sstar, kk))) := by
          intro ε
          have h := zeta_form_suffix P j T M x sstar hact hpend hfin (ε, fun _ => 1)
          simpa [zsite, hpre] using h
        have hYmeasS : Measurable (fun ω : RandomSources (Torus d m) M =>
            (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) := by
          have hq : Measurable (fun ω : RandomSources (Torus d m) M =>
              zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) :=
            ((zsite_measurable P j T M x sstar).comp measurable_fst).div_const _
          have hq2 : Measurable (fun ω : RandomSources (Torus d m) M =>
              (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2) := by
            simp_rw [pow_two]
            exact hq.mul hq
          exact hq2.sub measurable_const
        have hYboundS : ∀ ω : RandomSources (Torus d m) M,
            ‖(zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j‖ ≤
              ((|couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) / Real.sqrt (sweepW P.u m j)) ^ 2 +
                |sweepScale P.u m j|) := by
          intro ω
          have hZb : |zsite P j T M x sstar ω.1| ≤
              |couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) := by
            have hformε := hformS ω.1
            have hb := AndersonAC.S2.binarySuffix_bound (couplingOf P.u P.n₀) (m - P.n₀)
              (fun kk => ω.1 (Sum.inl (sstar, kk)))
            rw [hformε]
            exact hb
          calc ‖(zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
                sweepScale P.u m j‖
              ≤ ‖(zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2‖ +
                ‖sweepScale P.u m j‖ := norm_sub_le _ _
            _ = |zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)| ^ 2 +
                |sweepScale P.u m j| := by
                rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
            _ ≤ ((|couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) / Real.sqrt (sweepW P.u m j)) ^ 2 +
                |sweepScale P.u m j|) := by
              have hle : |zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)| ≤
                  |couplingOf P.u P.n₀| / 2 ^ (m - P.n₀) / Real.sqrt (sweepW P.u m j) := by
                rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
                exact div_le_div_of_nonneg_right hZb (Real.sqrt_nonneg _)
              apply add_le_add _ le_rfl
              exact pow_le_pow_left₀ (abs_nonneg _) hle 2
        refine ⟨Integrable.of_bound hYmeasS.aestronglyMeasurable _
          (Filter.Eventually.of_forall hYboundS), ?_⟩
        exact suffix_fresh_mean C P j T M x hu hj hjm hM hGood k hk i hi sstar hrs
          hact hpend hfin B₁ hB₁
      · -- aux/dummy: single auxiliary sign, pointwise square law
        have hsq : ∀ ε : AndersonAC.S2.SignIndex (Torus d m) → Bool,
            ((zsite P j T M x sstar ε / Real.sqrt (sweepW P.u m j)) ^ 2) =
              sweepScale P.u m j := by
          by_cases hact' : activeIn P j T x sstar
          · have hpend' : sstar ∈ x.pending := by
              by_contra hc
              exact hcon ⟨hact', hc⟩
            by_cases hfin' : IsFinalSweep m j
            · exfalso
              exact (hGood.final_no_pending hfin' sstar hstar_mem hact'.2.1) hpend'
            · have hjm' : j ≤ m := by simp only [IsFinalSweep] at hfin'; omega
              have hj0 : 0 < j := by omega
              intro ε
              have h := Zsq_single P j T M x sstar _ _
                (zeta_form_aux P j T M x sstar hact' hpend')
                (digitAmp_sq_eq_wt hu hj0 hjm') hwpos_gen (ε, fun _ => 1)
              simpa [zsite] using h
          · intro ε
            have hA : (Real.sqrt (sweepW P.u m j * sweepScale P.u m j)) ^ 2 =
                sweepW P.u m j * sweepScale P.u m j :=
              Real.sq_sqrt (mul_nonneg hwpos_gen.le htpos.le)
            have h := Zsq_single P j T M x sstar _ _
              (zeta_form_dummy P j T M x sstar hact') hA hwpos_gen (ε, fun _ => 1)
            simpa [zsite] using h
        exact hzero_of hsq
    obtain ⟨hYint, hE'zero⟩ := hYZ
    -- Step 2: the remaining-set card is the constant `M - k`; scale out `1/c`.
    have hMk : 0 < M (tileOrderIndex j T 0) - k := by omega
    have hc_pos : (0 : ℝ) < ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ) := by
      exact_mod_cast hMk
    have hcard_eq : ∀ ω : RandomSources (Torus d m) M,
        ((tileRemaining P j T M k ω).card : ℝ) =
          ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ) := by
      intro ω
      have hc := tileRemaining_card_a1 P j T M hM k (le_of_lt hk) ω
      have hN' : slotCount P j T = M (tileOrderIndex j T 0) := by rw [hN, ← hM0]
      rw [hc, hN']
    set S_G : Set (RandomSources (Torus d m) M) :=
      (tileRemaining P j T M k) ⁻¹' {s | i ∈ s} with hS_G
    have hS_Gmeas : MeasurableSet S_G :=
      (of_hist_comap P j T M x k
        (tileRemaining_measurable_comap P j T M x k hM))
        (measurableSet_finset_all {s | i ∈ s})
    have hRHS_int : Integrable (fun ω : RandomSources (Torus d m) M =>
        (if i ∈ tileRemaining P j T M k ω
          then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0))
        (sourcesLaw (Torus d m) M) := by
      have hH_eq : (fun ω : RandomSources (Torus d m) M =>
          (if i ∈ tileRemaining P j T M k ω
            then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0))
          = S_G.indicator (fun _ : RandomSources (Torus d m) M =>
            sweepScale P.u m j / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ)) := by
        funext ω
        by_cases h : i ∈ tileRemaining P j T M k ω
        · have hm : ω ∈ S_G := h
          rw [Set.indicator_of_mem hm, if_pos h, hcard_eq ω]
        · have hm : ω ∉ S_G := h
          rw [Set.indicator_of_notMem hm, if_neg h]
      rw [hH_eq]
      exact (integrable_const _).indicator hS_Gmeas
    have hYdiv_int : Integrable (fun ω : RandomSources (Torus d m) M =>
        ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
          sweepScale P.u m j) / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ))
        (sourcesLaw (Torus d m) M) :=
      hYint.div_const _
    have hYdiv_ind_int : Integrable (S_G.indicator (fun ω : RandomSources (Torus d m) M =>
        ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
          sweepScale P.u m j) / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ)))
        (sourcesLaw (Torus d m) M) :=
      hYdiv_int.indicator hS_Gmeas
    have hfun : ∀ ω : RandomSources (Torus d m) M, ω ∈ tileHist P j T M x k ⁻¹' B₁ →
        (if i ∈ tileRemaining P j T M k ω
          then (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 /
            ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ) else 0)
        = (if i ∈ tileRemaining P j T M k ω
          then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0)
          + S_G.indicator (fun ω : RandomSources (Torus d m) M =>
            ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ)) ω := by
      intro ω _
      by_cases h : i ∈ tileRemaining P j T M k ω
      · have hm : ω ∈ S_G := h
        rw [Set.indicator_of_mem hm, if_pos h, if_pos h, hcard_eq ω]
        ring
      · have hm : ω ∉ S_G := h
        rw [Set.indicator_of_notMem hm, if_neg h, if_neg h, add_zero]
    have hcongr : Set.EqOn (fun ω : RandomSources (Torus d m) M =>
        (if i ∈ tileRemaining P j T M k ω
          then (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 /
            ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ) else 0))
        (fun ω : RandomSources (Torus d m) M =>
          (if i ∈ tileRemaining P j T M k ω
            then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0)
          + S_G.indicator (fun ω : RandomSources (Torus d m) M =>
            ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
              sweepScale P.u m j) / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ)) ω)
        (tileHist P j T M x k ⁻¹' B₁) :=
      fun ω hω => hfun ω hω
    have hYdiv_zero : (∫ ω in tileHist P j T M x k ⁻¹' B₁, S_G.indicator
        (fun ω : RandomSources (Torus d m) M =>
          ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
            sweepScale P.u m j) / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ)) ω
        ∂(sourcesLaw (Torus d m) M)) = 0 := by
      rw [setIntegral_indicator hS_Gmeas]
      have hE'eq : tileHist P j T M x k ⁻¹' B₁ ∩ S_G = E' := by
        rw [hE', hS_G]
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      rw [hE'eq, integral_div, hE'zero]
      exact zero_div _
    have hmid_eq : (∫ ω in tileHist P j T M x k ⁻¹' B₁,
        (if i ∈ tileRemaining P j T M k ω
          then (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 /
            ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ) else 0)
        ∂(sourcesLaw (Torus d m) M))
        = (∫ ω in tileHist P j T M x k ⁻¹' B₁,
          (if i ∈ tileRemaining P j T M k ω
            then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0)
          ∂(sourcesLaw (Torus d m) M)) := by
      calc (∫ ω in tileHist P j T M x k ⁻¹' B₁,
          (if i ∈ tileRemaining P j T M k ω
            then (zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 /
              ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ) else 0)
          ∂(sourcesLaw (Torus d m) M))
          = ∫ ω in tileHist P j T M x k ⁻¹' B₁,
            ((if i ∈ tileRemaining P j T M k ω
              then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0)
            + S_G.indicator (fun ω : RandomSources (Torus d m) M =>
              ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
                sweepScale P.u m j) / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ)) ω)
            ∂(sourcesLaw (Torus d m) M) :=
            setIntegral_congr_fun hE₁meas hcongr
        _ = (∫ ω in tileHist P j T M x k ⁻¹' B₁,
            (if i ∈ tileRemaining P j T M k ω
              then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0)
            ∂(sourcesLaw (Torus d m) M))
            + ∫ ω in tileHist P j T M x k ⁻¹' B₁, S_G.indicator
              (fun ω : RandomSources (Torus d m) M =>
                ((zsite P j T M x sstar ω.1 / Real.sqrt (sweepW P.u m j)) ^ 2 -
                  sweepScale P.u m j) / ((M (tileOrderIndex j T 0) - k : ℕ) : ℝ)) ω
              ∂(sourcesLaw (Torus d m) M) :=
            integral_add hRHS_int.integrableOn hYdiv_ind_int.integrableOn
        _ = (∫ ω in tileHist P j T M x k ⁻¹' B₁,
            (if i ∈ tileRemaining P j T M k ω
              then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0)
            ∂(sourcesLaw (Torus d m) M)) := by
            rw [hYdiv_zero, add_zero]
    exact hStep1.trans hmid_eq
  · -- `i` outside the tile: slot never hits `i` and `i` is never remaining
    have hslot_ne : ∀ ω : RandomSources (Torus d m) M,
        tileSlotF P j T M k ω ≠ i := by
      intro ω hcon
      have hmem := tileSlotF_mem_image P j T M hM k hk ω
      rw [hcon] at hmem
      exact hi hmem
    have hrem_ne : ∀ ω : RandomSources (Torus d m) M,
        i ∉ tileRemaining P j T M k ω := by
      intro ω hmem
      exact hi (Finset.sdiff_subset hmem)
    have hL : ∀ ω ∈ tileHist P j T M x k ⁻¹' B₁,
        (if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0) = 0 := by
      intro ω _
      rw [if_neg (hslot_ne ω)]
    have hR : ∀ ω ∈ tileHist P j T M x k ⁻¹' B₁,
        (if i ∈ tileRemaining P j T M k ω
          then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0) = 0 := by
      intro ω _
      rw [if_neg (hrem_ne ω)]
    have hcongrL : Set.EqOn (fun ω : RandomSources (Torus d m) M =>
        (if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0))
        0 (tileHist P j T M x k ⁻¹' B₁) :=
      fun ω hω => hL ω hω
    have hcongrR : Set.EqOn (fun ω : RandomSources (Torus d m) M =>
        (if i ∈ tileRemaining P j T M k ω
          then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0))
        0 (tileHist P j T M x k ⁻¹' B₁) :=
      fun ω hω => hR ω hω
    rw [setIntegral_congr_fun hE₁meas hcongrL,
      setIntegral_congr_fun hE₁meas hcongrR]

/-- Conditional second moment of the slot scalar. -/
theorem variance_condExp {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (hM : TileOrderSizes P j T M) (hGood : TileGoodCore C P j T x)
    (run : ℕ → RandomSources (Torus d m) M → Bool)
    (hrun : ∀ k < slotCount P j T,
      @Measurable _ Bool (tileFiltration P j T M x k) ⊤ (run k))
    (k : ℕ) (hk : k < slotCount P j T) (i : Fin (siteCount d m)) :
    (sourcesLaw (Torus d m) M)[(fun ω =>
      if run k ω = true ∧ tileSlotF P j T M k ω = i
        then (tileXi P j T M x k ω) ^ 2 else 0) |
      tileFiltration P j T M x k] =ᵐ[sourcesLaw (Torus d m) M]
      (fun ω => if run k ω = true ∧ i ∈ tileRemaining P j T M k ω
        then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0) := by
  classical
  have htpos : 0 < sweepScale P.u m j :=
    sweepScale_pos' (lt_trans (by norm_num) hu.1) m j
  set F₂ : RandomSources (Torus d m) M → ℝ :=
    (fun ω => if tileSlotF P j T M k ω = i then (tileXi P j T M x k ω) ^ 2 else 0) with hF₂
  set G₂ : RandomSources (Torus d m) M → ℝ :=
    (fun ω => if i ∈ tileRemaining P j T M k ω
      then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0) with hG₂
  set E_run : Set (RandomSources (Torus d m) M) := (run k) ⁻¹' {true} with hE_run
  have hF₂meas : Measurable F₂ := by
    have heq : F₂ = fun ω => if ω ∈ (tileSlotF P j T M k) ⁻¹' {i}
        then (tileXi P j T M x k ω) ^ 2 else 0 := by
      funext ω
      simp only [hF₂]
      by_cases h : tileSlotF P j T M k ω = i
      · rw [if_pos h, if_pos (by simpa using h)]
      · rw [if_neg h, if_neg (by simpa using h)]
    rw [heq]
    have hxi2 : Measurable (fun ω : RandomSources (Torus d m) M =>
        (tileXi P j T M x k ω) ^ 2) := by
      simp_rw [pow_two]
      exact (tileXi_measurable P j T M x k).mul (tileXi_measurable P j T M x k)
    exact Measurable.ite ((tileSlotF_measurable P j T M k) (measurableSet_singleton i))
      hxi2 measurable_const
  have hF₂bound : ∀ ω, ‖F₂ ω‖ ≤ (2 * Real.sqrt (sweepScale P.u m j)) ^ 2 := by
    intro ω
    simp only [hF₂]
    by_cases h : tileSlotF P j T M k ω = i
    · simp only [h, if_true]
      have hb := tileXi_bound_pointwise C P j T M x hu hj hjm hM hGood k hk ω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    · simp [h]
  have hF₂int : Integrable F₂ (sourcesLaw (Torus d m) M) :=
    Integrable.of_bound hF₂meas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hF₂bound)
  have hG₂meas : Measurable G₂ := by
    have hval : Measurable (fun ω =>
        sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ)) :=
      measurable_const.div
        ((measurable_of_countable
          (fun s : Finset (Fin (siteCount d m)) => (s.card : ℝ))).comp
          (of_hist_comap P j T M x k
            (tileRemaining_measurable_comap P j T M x k hM)))
    have heq : G₂ = fun ω => if ω ∈ (tileRemaining P j T M k) ⁻¹' {s | i ∈ s}
        then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0 := by
      funext ω
      simp only [hG₂]
      by_cases h : i ∈ tileRemaining P j T M k ω
      · rw [if_pos h, if_pos (by simpa using h)]
      · rw [if_neg h, if_neg (by simpa using h)]
    rw [heq]
    exact Measurable.ite
      ((of_hist_comap P j T M x k
        (tileRemaining_measurable_comap P j T M x k hM))
        (measurableSet_finset_all _)) hval measurable_const
  have hG₂bound : ∀ ω, ‖G₂ ω‖ ≤ sweepScale P.u m j := by
    intro ω
    simp only [hG₂]
    by_cases h : i ∈ tileRemaining P j T M k ω
    · simp only [h, if_true]
      have hcard : (1 : ℝ) ≤ ((tileRemaining P j T M k ω).card : ℝ) := by
        have h0 : 1 ≤ (tileRemaining P j T M k ω).card := by
          have hpos := Finset.card_pos.mpr ⟨i, h⟩
          omega
        exact_mod_cast h0
      rw [Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg htpos.le (Nat.cast_nonneg _))]
      exact div_le_self htpos.le hcard
    · simp [h, htpos.le]
  have hG₂int : Integrable G₂ (sourcesLaw (Torus d m) M) :=
    Integrable.of_bound hG₂meas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hG₂bound)
  have hf_eq : (fun ω => if run k ω = true ∧ tileSlotF P j T M k ω = i
      then (tileXi P j T M x k ω) ^ 2 else 0) = E_run.indicator F₂ := by
    funext ω
    simp only [hF₂, hE_run]
    by_cases hω : run k ω = true
    · have hm : ω ∈ (run k) ⁻¹' {true} := hω
      by_cases hs : tileSlotF P j T M k ω = i
      · simp [hm, hs, hω]
      · simp [hm, hs, hω]
    · have hm : ω ∉ (run k) ⁻¹' {true} := hω
      simp [hm, hω]
  have hg_eq : (fun ω => if run k ω = true ∧ i ∈ tileRemaining P j T M k ω
      then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0) =
      E_run.indicator G₂ := by
    funext ω
    simp only [hG₂, hE_run]
    by_cases hω : run k ω = true
    · have hm : ω ∈ (run k) ⁻¹' {true} := hω
      by_cases hs : i ∈ tileRemaining P j T M k ω
      · simp [hm, hs, hω]
      · simp [hm, hs, hω]
    · have hm : ω ∉ (run k) ⁻¹' {true} := hω
      simp [hm, hω]
  rw [hf_eq, hg_eq]
  have hm : tileFiltration P j T M x k ≤
      (inferInstance : MeasurableSpace (RandomSources (Torus d m) M)) :=
    (tileFiltration P j T M x).le' k
  have hG₂fmeas : StronglyMeasurable[tileFiltration P j T M x k] G₂ := by
    have heq := tileFiltration_eq_comap P j T M x k
    have hrem : @Measurable _ _ (tileFiltration P j T M x k)
        inferInstance (tileRemaining P j T M k) := by
      rw [heq]
      exact tileRemaining_measurable_comap P j T M x k hM
    have hS_Gf : MeasurableSet[tileFiltration P j T M x k]
        ((tileRemaining P j T M k) ⁻¹' {s | i ∈ s}) :=
      hrem (measurableSet_finset_all _)
    have hval : @Measurable _ ℝ (tileFiltration P j T M x k) _ (fun ω =>
        sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ)) :=
      (measurable_const.div
        ((measurable_of_countable
          (fun s : Finset (Fin (siteCount d m)) => (s.card : ℝ))).comp hrem))
    have hmeas : @Measurable _ ℝ (tileFiltration P j T M x k) _ G₂ := by
      have heq2 : G₂ = fun ω => if ω ∈ (tileRemaining P j T M k) ⁻¹' {s | i ∈ s}
          then sweepScale P.u m j / ((tileRemaining P j T M k ω).card : ℝ) else 0 := by
        funext ω
        simp only [hG₂]
        by_cases h : i ∈ tileRemaining P j T M k ω
        · rw [if_pos h, if_pos (by simpa using h)]
        · rw [if_neg h, if_neg (by simpa using h)]
      rw [heq2]
      exact Measurable.ite hS_Gf hval measurable_const
    exact hmeas.stronglyMeasurable
  obtain ⟨Br, hBr, hBrE⟩ := run_preimage P j T M x k run (hrun k hk)
  have hEr : MeasurableSet E_run := by
    rw [hE_run, ← hBrE]
    exact (tileHist_measurable P j T M x k) hBr
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm (hF₂int.indicator hEr) _ _ _).symm
  · intro s hs _
    exact (hG₂int.indicator hEr).integrableOn
  · intro s hs _
    obtain ⟨B, hB, hBE⟩ := obtain_hist_preimage P j T M x k s hs
    have hinter : s ∩ E_run = tileHist P j T M x k ⁻¹' (B ∩ Br) := by
      rw [← hBE, hE_run, ← hBrE, Set.preimage_inter]
    calc ∫ ω in s, E_run.indicator G₂ ω ∂(sourcesLaw (Torus d m) M)
        = ∫ ω in s ∩ E_run, G₂ ω ∂(sourcesLaw (Torus d m) M) := by
          rw [setIntegral_indicator hEr]
      _ = ∫ ω in tileHist P j T M x k ⁻¹' (B ∩ Br), G₂ ω
            ∂(sourcesLaw (Torus d m) M) := by
          rw [hinter]
      _ = ∫ ω in tileHist P j T M x k ⁻¹' (B ∩ Br), F₂ ω
            ∂(sourcesLaw (Torus d m) M) :=
          (variance_core C P j T M x hu hj hjm hM hGood k hk i (B ∩ Br)
            (hB.inter hBr)).symm
      _ = ∫ ω in s ∩ E_run, F₂ ω ∂(sourcesLaw (Torus d m) M) := by
          rw [hinter]
      _ = ∫ ω in s, E_run.indicator F₂ ω ∂(sourcesLaw (Torus d m) M) := by
          rw [setIntegral_indicator hEr]
  · have hErF : MeasurableSet[tileFiltration P j T M x k] E_run :=
      (hrun k hk) (by trivial)
    exact (hG₂fmeas.indicator hErF).aestronglyMeasurable

theorem tileSlotLaw_proof : TileSlotLawStatement := by
  intro d m C P j T M x hu hj hjm hM hab hGood run hrun
  classical
  have hN : slotCount P j T = (tileSites (P.cover j) T).card := rfl
  refine ⟨hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- remaining measurable: rewrite filtration to comap, convert Finset target to ⊤
    intro k hk
    have heq := tileFiltration_eq_comap P j T M x k
    have hmeas := tileRemaining_measurable_comap P j T M x k hM
    rw [heq]
    exact measurable_to_top_finset _ hmeas
  · -- slot adapted: Fin target instance is definitionally ⊤
    intro k hk
    have heq := tileFiltration_eq_comap P j T M x (k + 1)
    have hmeas := tileSlotF_measurable_comap P j T M x k
    rw [heq]
    exact hmeas
  · -- scalar adapted
    intro k hk
    have heq := tileFiltration_eq_comap P j T M x (k + 1)
    have hmeas := tileXi_measurable_comap P j T M x k
    rw [heq]
    exact hmeas
  · -- nonempty from card
    intro k hk ω _
    have hcard := tileRemaining_card_a1 P j T M hM k (le_of_lt hk) ω
    have hpos : 0 < (tileRemaining P j T M k ω).card := by omega
    exact Finset.card_pos.mp hpos
  · -- bounded from pointwise
    intro k hk
    exact ae_of_all _ (fun ω _ => tileXi_bound_pointwise C P j T M x hu hj hjm hM hGood k hk ω)
  · -- uniform from orbit averaging
    intro k hk i
    exact uniform_condExp C P j T M x hM run hrun k hk i
  · -- mean from sign-flip symmetry
    intro k hk i
    exact mean_condExp C P j T M x hu hj hjm hM hGood run hrun k hk i
  · -- variance from the conditional second moment
    intro k hk i
    exact variance_condExp C P j T M x hu hj hjm hM hGood run hrun k hk i

end AndersonAC.AgentS78


