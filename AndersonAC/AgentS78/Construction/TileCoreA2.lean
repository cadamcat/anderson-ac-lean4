import AndersonAC.AgentS78.Construction.TileCore
import AndersonAC.AgentS78.Construction.TileCoreA0
import AndersonAC.AgentS78.Construction.TileCoreA3b
import AndersonAC.AgentS78.Construction.TileCoreAssembly
import AndersonAC.AgentS78.Construction.TileBlockMeasurable
import AndersonAC.AgentS78.PadNorm
import AndersonAC.S45.MatrixProbProof
import AndersonAC.S45.LocalityProof
import AndersonAC.S45.IncrementJoinProof
import AndersonAC.S45.PrefixPrestateProof
import AndersonAC.S45.DuplicationComparisonProof

/-!
# monitored tile increments (monitor bounds)

The adapter from the ordinary S45 increment table to the four padded tile monitors.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw signValue binarySuffix)

section Measurability
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
  (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)

private theorem tileSlot_measurable (k : ℕ) :
    Measurable (tileSlot P j T M k) := by
  unfold tileSlot
  split_ifs with hk
  · have horder : Measurable fun ω : RandomSources (Torus d m) M =>
        (ω.2 (tileOrderIndex j T 0) ⟨k, hk⟩).val :=
      (measurable_of_countable (fun o : AndersonAC.S2.Order (M (tileOrderIndex j T 0)) =>
        (o ⟨k, hk⟩).val)).comp
        ((measurable_pi_apply (tileOrderIndex j T 0)).comp measurable_snd)
    exact (measurable_of_countable fun n : ℕ =>
      (siteAt (tileSites (P.cover j) T) n).getD (site₀ d m)).comp horder
  · exact measurable_const

private theorem tileZeta_measurable (i : Torus d m) :
    Measurable (tileZeta P j T M x i) := by
  classical
  change Measurable (fun ω : RandomSources (Torus d m) M =>
    if activeIn P j T x i then
      if i ∉ x.pending then
        if IsFinalSweep m j then
          binarySuffix (couplingOf P.u P.n₀) (x.prefixLength i)
            (fun k => ω.1 (Sum.inl (i, k)))
        else digitAmp P.u (j - 1) * signValue (ω.1 (Sum.inl (i, x.prefixLength i)))
      else digitAmp P.u (j - 1) * signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 i)))
    else Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
      signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 i))))
  have hsign (z : Sum (Torus d m × ℕ) ℕ) :
      Measurable fun ω : RandomSources (Torus d m) M => signValue (ω.1 z) :=
    (measurable_of_finite signValue).comp ((measurable_pi_apply z).comp measurable_fst)
  by_cases ha : activeIn P j T x i
  · by_cases hp : i ∈ x.pending
    · simp [ha, hp]
      exact measurable_const.mul (hsign (Sum.inr (tileAuxIndex j T 0 i)))
    · by_cases hf : IsFinalSweep m j
      · simp [ha, hp, hf]
        have hbits : Measurable fun ω : RandomSources (Torus d m) M =>
            fun k => ω.1 (Sum.inl (i, k)) :=
          Measurable.of_eval fun n => (measurable_pi_apply (Sum.inl (i, n))).comp measurable_fst
        exact (AndersonAC.S2.binarySuffix_measurable
          (couplingOf P.u P.n₀) (x.prefixLength i)).comp hbits
      · simp [ha, hp, hf]
        exact measurable_const.mul (hsign (Sum.inl (i, x.prefixLength i)))
  · simp [ha]
    exact measurable_const.mul (hsign (Sum.inr (tileAuxIndex j T 0 i)))

private theorem tileXi_measurable (k : ℕ) :
    Measurable (tileXi P j T M x k) := by
  have hs := tileSlot_measurable P j T M k
  have hfixed : ∀ i : Torus d m, Measurable fun ω : RandomSources (Torus d m) M =>
      tileZeta P j T M x i ω / Real.sqrt (sweepW P.u m j) := by
    intro i
    exact (tileZeta_measurable P j T M x i).div measurable_const
  have heq : tileXi P j T M x k = fun ω =>
      tileZeta P j T M x (tileSlot P j T M k ω) ω /
        Real.sqrt (sweepW P.u m j) := by
    funext ω
    rfl
  rw [heq]
  exact measurable_select hs (G := fun i ω =>
    tileZeta P j T M x i ω / Real.sqrt (sweepW P.u m j)) hfixed

private theorem tileSlotF_measurable (k : ℕ) :
    Measurable (tileSlotF P j T M k) :=
  (measurable_of_countable (siteRank d m)).comp (tileSlot_measurable P j T M k)

private theorem tileHist_measurable (k : ℕ) :
    Measurable (tileHist P j T M x k) := by
  apply Measurable.of_eval
  intro l
  change Measurable fun ω =>
    (((tileSlotF P j T M l ω : Fin (siteCount d m)) : ℕ), tileXi P j T M x l ω)
  exact ((measurable_of_countable (fun y : Fin (siteCount d m) => y.val)).comp
    (tileSlotF_measurable P j T M l)).prodMk (tileXi_measurable P j T M x l)

private theorem tileFiltration_eq_comap (k : ℕ) :
    tileFiltration P j T M x k =
      MeasurableSpace.comap (tileHist P j T M x k) inferInstance := by
  apply le_antisymm
  · exact inf_le_left
  · refine le_inf le_rfl ?_
    exact (tileHist_measurable P j T M x k).comap_le

private theorem tileSlotF_adapted (k : ℕ) :
    @Measurable (RandomSources (Torus d m) M) (Fin (siteCount d m))
      (tileFiltration P j T M x (k + 1)) inferInstance (tileSlotF P j T M k) := by
  rw [tileFiltration_eq_comap]
  have hhist : @Measurable (RandomSources (Torus d m) M)
      (Fin (k + 1) → ℕ × ℝ)
      (MeasurableSpace.comap (tileHist P j T M x (k + 1)) inferInstance)
      inferInstance (tileHist P j T M x (k + 1)) := comap_measurable _
  have hcoord := (measurable_pi_apply (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).comp hhist
  have hfirst := measurable_fst.comp hcoord
  let toFin : ℕ → Fin (siteCount d m) := fun n =>
    ⟨n % siteCount d m, Nat.mod_lt _ (siteCount_pos d m)⟩
  have heq : (fun ω => toFin
      ((tileHist P j T M x (k + 1) ω ⟨k, Nat.lt_succ_self k⟩).1)) =
        tileSlotF P j T M k := by
    funext ω
    apply Fin.ext
    change (tileSlotF P j T M k ω).val % siteCount d m =
      (tileSlotF P j T M k ω).val
    exact Nat.mod_eq_of_lt (tileSlotF P j T M k ω).isLt
  rw [← heq]
  exact (measurable_of_countable toFin).comp hfirst

private theorem tileSlot_adapted (k : ℕ) :
    @Measurable (RandomSources (Torus d m) M) (Torus d m)
      (tileFiltration P j T M x (k + 1)) inferInstance (tileSlot P j T M k) := by
  have h := (measurable_of_countable (siteRank d m).symm).comp
    (tileSlotF_adapted P j T M x k)
  have heq : (fun ω => (siteRank d m).symm (tileSlotF P j T M k ω)) =
      tileSlot P j T M k := by
    funext ω
    simp [tileSlotF]
  rw [← heq]
  exact h

private theorem tileXi_adapted (k : ℕ) :
    @Measurable (RandomSources (Torus d m) M) ℝ
      (tileFiltration P j T M x (k + 1)) inferInstance (tileXi P j T M x k) := by
  rw [tileFiltration_eq_comap]
  have hhist : @Measurable (RandomSources (Torus d m) M)
      (Fin (k + 1) → ℕ × ℝ)
      (MeasurableSpace.comap (tileHist P j T M x (k + 1)) inferInstance)
      inferInstance (tileHist P j T M x (k + 1)) := comap_measurable _
  have hcoord := (measurable_pi_apply (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).comp hhist
  have hsecond := measurable_snd.comp hcoord
  have heq : tileXi P j T M x k = fun ω =>
      (tileHist P j T M x (k + 1) ω ⟨k, Nat.lt_succ_self k⟩).2 := by
    funext ω
    rfl
  rw [heq]
  exact hsecond

end Measurability

/-! ## A measurable, stopped prefix recursion -/

section Process
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
  (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)

private abbrev SeqMeasAt {α : Type*} (mΩ : MeasurableSpace α)
    {P : Type} [Fintype P] [DecidableEq P] (Q : α → S45.Sequence P) : Prop :=
  @Measurable α _ mΩ _ (fun a => seqCode (Q a))

private theorem seqMeas_ite {α : Type*} (mΩ : MeasurableSpace α) {p : α → Prop}
    [DecidablePred p]
    (hp : @MeasurableSet α mΩ {a | p a})
    {Q R : α → S45.Sequence (Port d m)}
    (hQ : SeqMeasAt mΩ Q) (hR : SeqMeasAt mΩ R) :
    SeqMeasAt mΩ (fun a => if p a then Q a else R a) := by
  letI : MeasurableSpace α := mΩ
  have hQ' : SeqMeas Q := hQ
  have hR' : SeqMeas R := hR
  change Measurable (fun a => seqCode (if p a then Q a else R a))
  have heq : (fun a => seqCode (if p a then Q a else R a)) = fun a =>
      (if p a then (Q a).length else (R a).length,
        if p a then (fun k => finsetCode ((Q a).state k).live)
          else (fun k => finsetCode ((R a).state k).live),
        if p a then (fun k => ((Q a).state k).g) else (fun k => ((R a).state k).g),
        if p a then (fun k => optionCode ((Q a).pivot k))
          else (fun k => optionCode ((R a).pivot k)),
        if p a then (Q a).scalar else (R a).scalar) := by
    funext a
    by_cases h : p a <;> simp [h, seqCode]
  rw [heq]
  refine Measurable.prodMk (Measurable.ite hp hQ'.length hR'.length) ?_
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.ite hp hQ'.liveFam hR'.liveFam
  · refine Measurable.prodMk ?_ ?_
    · exact Measurable.ite hp hQ'.gFam hR'.gFam
    · refine Measurable.prodMk ?_ ?_
      · exact Measurable.ite hp hQ'.pivotFam hR'.pivotFam
      · exact Measurable.ite hp hQ'.scalarFam hR'.scalarFam

private theorem seqMeas_candidate {α : Type*} (mΩ : MeasurableSpace α)
    {Q : α → S45.Sequence (Port d m)} (hQ : SeqMeasAt mΩ Q)
    {site : α → Torus d m} (hsite : Measurable site)
    {z : α → ℝ} (hz : Measurable z) :
    SeqMeasAt mΩ (fun a => candidate P j x (Q a) (site a) (z a)) := by
  letI : MeasurableSpace α := mΩ
  have hQ' : SeqMeas Q := hQ
  have hr : Measurable fun _ : α => portR (sweepTheta P.u m j) x.r :=
    measurable_portR _ measurable_const
  have hfixed : ∀ i : Torus d m, SeqMeas (fun a => candidate P j x (Q a) i (z a)) := by
    intro i
    have hstate := hQ'.stateAt hQ'.length
    have hb : LiveMeas (fun a => stepLive (sweepScale P.u m j)
        (portR (sweepTheta P.u m j) x.r) ((Q a).state (Q a).length) (i, false) (z a)) :=
      hstate.stepLive (sweepScale P.u m j) hr (i, false) hz
    change SeqMeas (fun a => extendSeq (Q a)
      (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        ((Q a).state (Q a).length) (i, false) (z a)) (i, false) (z a))
    exact hQ'.extend hb (i, false) hz
  change Measurable (fun a => seqCode (candidate P j x (Q a) (site a) (z a)))
  exact measurable_select hsite (G := fun i a =>
    seqCode (candidate P j x (Q a) i (z a))) (fun i => hfixed i)

private theorem measurableSet_processEligible {α : Type*} (mΩ : MeasurableSpace α)
    {Q : α → S45.Sequence (Port d m)} (hQ : SeqMeasAt mΩ Q)
    {site : α → Torus d m} (hsite : Measurable site) :
    @MeasurableSet α mΩ {a | activeIn P j T x (site a) ∧
      ((site a, false) : Port d m) ∈ ((Q a).state (Q a).length).live} := by
  classical
  letI : MeasurableSpace α := mΩ
  have hQ' : SeqMeas Q := hQ
  have hactive : MeasurableSet {a | activeIn P j T x (site a)} := by
    simpa using measurableSet_select hsite
      (Q := fun i : Torus d m => if activeIn P j T x i then Set.univ else ∅)
      (by intro i; by_cases hi : activeIn P j T x i <;> simp [hi])
  have hstate := hQ'.stateAt hQ'.length
  have hlive : Measurable fun a => finsetCode ((Q a).state (Q a).length).live := hstate.live
  have hbit : MeasurableSet {a | ((site a, false) : Port d m) ∈
      ((Q a).state (Q a).length).live} := by
    simpa using measurableSet_select hsite
      (Q := fun i : Torus d m => {a | ((i, false) : Port d m) ∈
        ((Q a).state (Q a).length).live})
      (by intro i; exact measurableSet_mem_of_code hlive (i, false))
  exact hactive.inter hbit

private theorem measurableSet_processTrial {α : Type*} (mΩ : MeasurableSpace α)
    {Q : α → S45.Sequence (Port d m)} (hQ : SeqMeasAt mΩ Q)
    {site : α → Torus d m} (hsite : Measurable site)
    {z : α → ℝ} (hz : Measurable z) :
    @MeasurableSet α mΩ {a | trialOk P j T x
      (candidate P j x (Q a) (site a) (z a))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        ((Q a).state (Q a).length) (site a, false) (z a))} := by
  letI : MeasurableSpace α := mΩ
  have hQ' : SeqMeas Q := hQ
  have hr : Measurable fun _ : α => portR (sweepTheta P.u m j) x.r :=
    measurable_portR _ measurable_const
  have hstate := hQ'.stateAt hQ'.length
  have hden : ∀ i : Torus d m, Measurable fun a =>
      stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        ((Q a).state (Q a).length) (i, false) (z a) := by
    intro i
    have hzC : Measurable fun a => (z a : ℂ) := Complex.measurable_ofReal.comp hz
    have hentry : Measurable fun a => ((Q a).state (Q a).length).g (i, false) (i, false) :=
      hstate.g.eval_matrix
    change Measurable fun a => 1 +
      ((z a : ℂ) + sweepScale P.u m j * (portR (sweepTheta P.u m j) x.r) (i, false)) *
        ((Q a).state (Q a).length).g (i, false) (i, false)
    exact measurable_const.add ((hzC.add measurable_const).mul hentry)
  have htrial : ∀ i : Torus d m, MeasurableSet {a | trialOk P j T x
      (candidate P j x (Q a) i (z a))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        ((Q a).state (Q a).length) (i, false) (z a))} := by
    intro i
    have hcan := seqMeas_candidate P j x mΩ hQ
      (measurable_const : Measurable fun _ : α => i) hz
    exact measurableSet_trialOk P j T (measurable_const : Measurable fun _ : α => x)
      hcan (hden i)
  simpa using measurableSet_select hsite
    (Q := fun i : Torus d m => {a | trialOk P j T x
      (candidate P j x (Q a) i (z a))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        ((Q a).state (Q a).length) (i, false) (z a))}) htrial

private theorem seqMeas_constAt {α : Type*} (mΩ : MeasurableSpace α) :
    SeqMeasAt mΩ fun _ : α => x.sweep := by
  change @Measurable α _ mΩ _ (fun _ => seqCode x.sweep)
  exact measurable_const

open Classical in
private def tilePrefixProcess : ℕ → RandomSources (Torus d m) M →
    Bool × S45.Sequence (Port d m)
  | 0 => fun _ => (true, x.sweep)
  | k + 1 => fun ω =>
      let alive := (tilePrefixProcess k ω).1
      let q := (tilePrefixProcess k ω).2
      if hk : k < slotCount P j T then
        if alive then
          let i := tileSlot P j T M k ω
          let z := tileXi P j T M x k ω
          if he : activeIn P j T x i ∧ ((i, false) : Port d m) ∈ (q.state q.length).live then
            if trialOk P j T x (candidate P j x q i z)
                (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                  (q.state q.length) (i, false) z) then
              (true, candidate P j x q i z)
            else (false, x.sweep)
          else (true, q)
        else (false, x.sweep)
      else if alive then (true, q) else (false, x.sweep)

private theorem tilePrefixProcess_spec : ∀ (k : ℕ) (ω : RandomSources (Torus d m) M),
    slotSeq P j T M x k ω =
      if (tilePrefixProcess P j T M x k ω).1 then
        some (tilePrefixProcess P j T M x k ω).2 else none := by
  classical
  intro k
  induction k with
  | zero => intro ω; simp [slotSeq, tilePrefixProcess]
  | succ k ih =>
    intro ω
    simp only [slotSeq]
    rw [ih ω]
    by_cases hk : k < slotCount P j T
    · simp only [if_pos hk]
      cases hp : tilePrefixProcess P j T M x k ω with
      | mk alive q =>
        simp only [tilePrefixProcess, hp, Prod.fst, Prod.snd, hk]
        cases alive
        · simp [slotStep]
        · by_cases he : activeIn P j T x (tileSlot P j T M k ω) ∧
              ((tileSlot P j T M k ω, false) : Port d m) ∈ (q.state q.length).live
          · by_cases ht : trialOk P j T x
                (candidate P j x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
                (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                  (q.state q.length) (tileSlot P j T M k ω, false)
                  (tileXi P j T M x k ω)) <;>
              simp [slotStep, he, ht]
          · simp [slotStep, he]
    · simp only [if_neg hk]
      cases hp : tilePrefixProcess P j T M x k ω with
      | mk alive q => cases alive <;> simp [tilePrefixProcess, hp, hk]

private theorem tilePrefixProcess_measurable : ∀ k,
    @Measurable (RandomSources (Torus d m) M) Bool
      (tileFiltration P j T M x k) inferInstance (fun ω => (tilePrefixProcess P j T M x k ω).1) ∧
    SeqMeasAt (tileFiltration P j T M x k)
      (fun ω => (tilePrefixProcess P j T M x k ω).2) := by
  classical
  intro k
  induction k with
  | zero =>
    constructor
    · simpa [tilePrefixProcess] using (measurable_const :
        Measurable fun _ : RandomSources (Torus d m) M => (true : Bool))
    · exact seqMeas_constAt (x := x) (mΩ := tileFiltration P j T M x 0)
  | succ k ih =>
    -- The old prefix is predictable at time k and hence measurable at time k + 1.
    have hrun : @Measurable (RandomSources (Torus d m) M) Bool
        (tileFiltration P j T M x (k + 1)) inferInstance
        (fun ω => (tilePrefixProcess P j T M x k ω).1) :=
      ih.1.mono ((tileFiltration P j T M x).mono (Nat.le_succ k)) le_rfl
    have hq : SeqMeasAt (tileFiltration P j T M x (k + 1))
        (fun ω => (tilePrefixProcess P j T M x k ω).2) := by
      change @Measurable (RandomSources (Torus d m) M) _
        (tileFiltration P j T M x (k + 1)) _
        (fun ω => seqCode ((tilePrefixProcess P j T M x k ω).2))
      exact ih.2.mono ((tileFiltration P j T M x).mono (Nat.le_succ k)) le_rfl
    by_cases hk : k < slotCount P j T
    · let Q : RandomSources (Torus d m) M → S45.Sequence (Port d m) :=
        fun ω => (tilePrefixProcess P j T M x k ω).2
      let R : RandomSources (Torus d m) M → Bool :=
        fun ω => (tilePrefixProcess P j T M x k ω).1
      have hRset : @MeasurableSet (RandomSources (Torus d m) M)
          (tileFiltration P j T M x (k + 1)) {ω | R ω = true} :=
        hrun (measurableSet_singleton true)
      have hsite := tileSlot_adapted P j T M x k
      have hz := tileXi_adapted P j T M x k
      have hcan := seqMeas_candidate P j x (tileFiltration P j T M x (k + 1)) hq hsite hz
      have hEligible := measurableSet_processEligible P j T x
        (tileFiltration P j T M x (k + 1)) hq hsite
      have hTrial := measurableSet_processTrial P j T x
        (tileFiltration P j T M x (k + 1)) hq hsite hz
      have hconst := seqMeas_constAt (x := x)
        (mΩ := tileFiltration P j T M x (k + 1))
      have hinner : SeqMeasAt (tileFiltration P j T M x (k + 1)) (fun ω => if trialOk P j T x
          (candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
            ((Q ω).state (Q ω).length) (tileSlot P j T M k ω, false)
            (tileXi P j T M x k ω))
          then candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω)
          else x.sweep) := seqMeas_ite (tileFiltration P j T M x (k + 1)) hTrial hcan hconst
      have houter : SeqMeasAt (tileFiltration P j T M x (k + 1)) (fun ω => if activeIn P j T x (tileSlot P j T M k ω) ∧
          ((tileSlot P j T M k ω, false) : Port d m) ∈ ((Q ω).state (Q ω).length).live
          then (if trialOk P j T x
            (candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω))
            (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
              ((Q ω).state (Q ω).length) (tileSlot P j T M k ω, false)
              (tileXi P j T M x k ω))
            then candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω)
            else x.sweep)
          else Q ω) := seqMeas_ite (tileFiltration P j T M x (k + 1)) hEligible hinner hq
      have hnext : SeqMeasAt (tileFiltration P j T M x (k + 1)) (fun ω => if R ω then
          (if activeIn P j T x (tileSlot P j T M k ω) ∧
            ((tileSlot P j T M k ω, false) : Port d m) ∈ ((Q ω).state (Q ω).length).live
            then (if trialOk P j T x
              (candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω))
              (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                ((Q ω).state (Q ω).length) (tileSlot P j T M k ω, false)
                (tileXi P j T M x k ω))
              then candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω)
              else x.sweep)
            else Q ω)
          else x.sweep) := seqMeas_ite (tileFiltration P j T M x (k + 1)) hRset houter hconst
      let trialBool : RandomSources (Torus d m) M → Bool := fun ω =>
        if trialOk P j T x
          (candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
            ((Q ω).state (Q ω).length) (tileSlot P j T M k ω, false)
            (tileXi P j T M x k ω)) then true else false
      have htrialBool : @Measurable (RandomSources (Torus d m) M) Bool
          (tileFiltration P j T M x (k + 1)) ⊤ trialBool := by
        exact Measurable.ite hTrial measurable_const measurable_const
      let innerRun : RandomSources (Torus d m) M → Bool := fun ω => if
          activeIn P j T x (tileSlot P j T M k ω) ∧
            ((tileSlot P j T M k ω, false) : Port d m) ∈ ((Q ω).state (Q ω).length).live
          then trialBool ω else true
      have hinnerRun : @Measurable (RandomSources (Torus d m) M) Bool
          (tileFiltration P j T M x (k + 1)) ⊤ innerRun := by
        exact Measurable.ite hEligible htrialBool measurable_const
      let nextRun : RandomSources (Torus d m) M → Bool := fun ω =>
        if R ω then innerRun ω else false
      have hnextRun : @Measurable (RandomSources (Torus d m) M) Bool
          (tileFiltration P j T M x (k + 1)) ⊤ nextRun := by
        exact Measurable.ite hRset hinnerRun measurable_const
      have heqRun : nextRun = fun ω =>
          (tilePrefixProcess P j T M x (k + 1) ω).1 := by
        funext ω
        by_cases hR : R ω = true
        · have hAlive : (tilePrefixProcess P j T M x k ω).1 = true := by
            simpa [R] using hR
          have hQeq : (tilePrefixProcess P j T M x k ω).2 = Q ω := rfl
          by_cases he : activeIn P j T x (tileSlot P j T M k ω) ∧
              ((tileSlot P j T M k ω, false) : Port d m) ∈ ((Q ω).state (Q ω).length).live
          · let ok : Prop := trialOk P j T x
                (candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω))
                (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                  ((Q ω).state (Q ω).length) (tileSlot P j T M k ω, false)
                  (tileXi P j T M x k ω))
            by_cases ht : ok
            · simp [nextRun, innerRun, trialBool, tilePrefixProcess, hk, Q, R, hR,
                hAlive, hQeq, he, ok, ht]
            · simp [nextRun, innerRun, trialBool, tilePrefixProcess, hk, Q, R, hR,
                hAlive, hQeq, he, ok, ht]
          · rcases not_and_or.mp he with hactive | hlive
            · simp [nextRun, innerRun, trialBool, tilePrefixProcess, hk, Q, R, hR,
                hAlive, hQeq, hactive]
            · simp [nextRun, innerRun, trialBool, tilePrefixProcess, hk, Q, R, hR,
                hAlive, hQeq, hlive]
        · have hAlive : (tilePrefixProcess P j T M x k ω).1 = false := by
            cases h : (tilePrefixProcess P j T M x k ω).1 <;> simp [R, h] at hR ⊢
          simp [nextRun, tilePrefixProcess, hk, Q, R, hR, hAlive]
      have heqSeq : (fun ω => if R ω then
          (if activeIn P j T x (tileSlot P j T M k ω) ∧
            ((tileSlot P j T M k ω, false) : Port d m) ∈ ((Q ω).state (Q ω).length).live
            then (if trialOk P j T x
              (candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω))
              (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                ((Q ω).state (Q ω).length) (tileSlot P j T M k ω, false)
                (tileXi P j T M x k ω))
              then candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω)
              else x.sweep)
            else Q ω)
          else x.sweep) = fun ω =>
            (tilePrefixProcess P j T M x (k + 1) ω).2 := by
        funext ω
        by_cases hR : R ω = true
        · have hAlive : (tilePrefixProcess P j T M x k ω).1 = true := by
            simpa [R] using hR
          have hQeq : (tilePrefixProcess P j T M x k ω).2 = Q ω := rfl
          by_cases he : activeIn P j T x (tileSlot P j T M k ω) ∧
              ((tileSlot P j T M k ω, false) : Port d m) ∈ ((Q ω).state (Q ω).length).live
          · let ok : Prop := trialOk P j T x
                (candidate P j x (Q ω) (tileSlot P j T M k ω) (tileXi P j T M x k ω))
                (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                  ((Q ω).state (Q ω).length) (tileSlot P j T M k ω, false)
                  (tileXi P j T M x k ω))
            by_cases ht : ok
            · simp [tilePrefixProcess, hk, Q, R, hR, hAlive, hQeq, he, ok, ht]
            · simp [tilePrefixProcess, hk, Q, R, hR, hAlive, hQeq, he, ok, ht]
          · simp [tilePrefixProcess, hk, Q, R, hR, hAlive, hQeq, he]
        · have hAlive : (tilePrefixProcess P j T M x k ω).1 = false := by
            cases h : (tilePrefixProcess P j T M x k ω).1 <;> simp [R, h] at hR ⊢
          simp [tilePrefixProcess, hk, Q, R, hR, hAlive]
      constructor
      · rw [← heqRun]
        exact hnextRun
      · rw [← heqSeq]
        exact hnext
    · let Q : RandomSources (Torus d m) M → S45.Sequence (Port d m) :=
        fun ω => (tilePrefixProcess P j T M x k ω).2
      let R : RandomSources (Torus d m) M → Bool :=
        fun ω => (tilePrefixProcess P j T M x k ω).1
      have hRset : @MeasurableSet (RandomSources (Torus d m) M)
          (tileFiltration P j T M x (k + 1)) {ω | R ω = true} :=
        hrun (measurableSet_singleton true)
      have hconst := seqMeas_constAt (x := x)
        (mΩ := tileFiltration P j T M x (k + 1))
      have heqRun : R = fun ω => (tilePrefixProcess P j T M x (k + 1) ω).1 := by
        funext ω
        by_cases hR : R ω = true <;> simp [tilePrefixProcess, hk, Q, R, hR]
      have heqSeq : (fun ω => if R ω then Q ω else x.sweep) =
          fun ω => (tilePrefixProcess P j T M x (k + 1) ω).2 := by
        funext ω
        by_cases hR : R ω = true <;> simp [tilePrefixProcess, hk, Q, R, hR]
      constructor
      · rw [← heqRun]
        exact hrun
      · have hnext : SeqMeasAt (tileFiltration P j T M x (k + 1))
            (fun ω => if R ω then Q ω else x.sweep) :=
          seqMeas_ite (tileFiltration P j T M x (k + 1)) hRset hq hconst
        rw [← heqSeq]
        exact hnext

private theorem tilePrefixProcess_run (k : ℕ) :
    (fun ω => (tilePrefixProcess P j T M x k ω).1) = tileRun P j T M x k := by
  funext ω
  unfold tileRun
  rw [tilePrefixProcess_spec P j T M x k ω]
  cases h : tilePrefixProcess P j T M x k ω with
  | mk run q => cases run <;> simp [h]

theorem tileRun_predictable (k : ℕ) :
    @Measurable (RandomSources (Torus d m) M) Bool
      (tileFiltration P j T M x k) inferInstance (tileRun P j T M x k) := by
  rw [← tilePrefixProcess_run P j T M x k]
  exact (tilePrefixProcess_measurable P j T M x k).1

end Process

/-! ## Finite-dimensional compression facts for the common padding -/

section Padding

theorem padInto_isHermitian {α : Type} [Fintype α] [DecidableEq α]
    (D : ℕ) (e : α → Fin D) (A : S45.CMat α) (hA : A.IsHermitian) :
    (padInto D e A).IsHermitian := by
  change Matrix.conjTranspose (padInto D e A) = padInto D e A
  ext a b
  simp only [Matrix.conjTranspose_apply, padInto, star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h₁ : e x = a
  · by_cases h₂ : e y = b
    · simpa [h₁, h₂, and_comm] using hA.apply x y
    · simp [h₁, h₂, and_comm]
  · by_cases h₂ : e y = b <;> simp [h₁, h₂, and_comm]

theorem padInto_norm {α : Type} [Fintype α] [DecidableEq α]
    (D : ℕ) (e : α → Fin D) (he : Function.Injective e) (A : S45.CMat α) :
    ‖padInto D e A‖ = ‖A‖ := by
  have hsupp : ∀ a b, (∀ x, e x ≠ a) ∨ (∀ x, e x ≠ b) → padInto D e A a b = 0 := by
    intro a b h
    rcases h with h | h
    · simp [padInto, h]
    · simp [padInto, h]
  calc
    ‖padInto D e A‖ = ‖(padInto D e A).submatrix e e‖ :=
      (norm_submatrix_of_support e he (padInto D e A) hsupp).symm
    _ = ‖A‖ := by rw [padInto_submatrix D e he A]

theorem scalarDilation_isHermitian (u : ℂ) : (scalarDilation u).IsHermitian := by
  change Matrix.conjTranspose (scalarDilation u) = scalarDilation u
  ext a b
  fin_cases a <;> fin_cases b <;> simp [scalarDilation, Matrix.conjTranspose_apply]

theorem scalarBlock_isHermitian (a : ℝ) : (scalarBlock a).IsHermitian := by
  change Matrix.conjTranspose (scalarBlock a) = scalarBlock a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarBlock, Matrix.conjTranspose_apply]

end Padding

section Evaluation
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
  (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)

theorem tileEval_isHermitian (i : Fin (monitorCount P j T)) (k : ℕ)
    (ω : RandomSources (Torus d m) M) (y : Fin (siteCount d m)) (z : ℝ) :
    (tileEval P j T M x i k ω y z).IsHermitian := by
  classical
  unfold tileEval
  dsimp
  split_ifs
  · exact padInto_isHermitian _ _ _ (scalarDilation_isHermitian _)
  · exact padInto_isHermitian _ _ _ (scalarBlock_isHermitian _)
  · exact padInto_isHermitian _ _ _ (scalarBlock_isHermitian _)
  · exact padInto_isHermitian _ _ _
      (AndersonAC.AgentS45.dilation_square_proof _).1
  · exact padInto_isHermitian _ _ _
      (AndersonAC.AgentS45.dilation_square_proof _).1
  · exact Matrix.isHermitian_zero

end Evaluation

/-! ## Joint strong measurability of the evaluated monitor -/

section EvaluationMeasurability
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
  (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)

private theorem tilePrefixProcess_stopped (k : ℕ) (ω : RandomSources (Torus d m) M) :
    (tilePrefixProcess P j T M x k ω).1 = false →
      (tilePrefixProcess P j T M x k ω).2 = x.sweep := by
  induction k with
  | zero => simp [tilePrefixProcess]
  | succ k ih =>
    intro hfalse
    simp only [tilePrefixProcess] at hfalse ⊢
    split_ifs at hfalse ⊢ <;> simp_all

private theorem measurable_padInto {α ι : Type} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] {D : ℕ} (e : ι → Fin D)
    {A : α → S45.CMat ι} (hA : Measurable A) :
    Measurable fun a => padInto D e (A a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [padInto]
  refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ => ?_
  have hentry : Measurable fun a => A a p q :=
    ((measurable_pi_apply q).comp ((measurable_pi_apply p).comp hA))
  by_cases h : e p = i ∧ e q = j
  · simpa [h] using hentry
  · simpa [h] using (measurable_const : Measurable fun _ : α => (0 : ℂ))

private theorem measurable_scalarDilation {α : Type*} [MeasurableSpace α]
    {u : α → ℂ} (hu : Measurable u) :
    Measurable fun a => scalarDilation (u a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [scalarDilation] <;> fun_prop

private theorem measurable_scalarBlock {α : Type*} [MeasurableSpace α]
    {u : α → ℝ} (hu : Measurable u) :
    Measurable fun a => scalarBlock (u a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [scalarBlock] <;>
    first | exact Complex.measurable_ofReal.comp hu | exact measurable_const

private theorem measurable_dilation {α I H : Type} [MeasurableSpace α]
    [Fintype I] [Fintype H] {A : α → Matrix I H ℂ} (hA : Measurable A) :
    Measurable fun a => S45.dilation (A a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [S45.dilation]
    | inr j =>
      have h : Measurable fun a => A a i j :=
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA))
      simpa [S45.dilation] using h
  | inr i =>
    cases j with
    | inl j =>
      have h : Measurable fun a => A a j i :=
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hA))
      have hstar : Measurable fun a => star (A a j i) :=
        continuous_star.measurable.comp h
      simpa [S45.dilation, Matrix.conjTranspose_apply] using hstar
    | inr j => simp [S45.dilation]

private theorem measurable_restrict {α : Type} [MeasurableSpace α]
    {M : α → S45.CMat (Port d m)} (hM : Measurable M) (S : Finset (Port d m)) :
    Measurable fun a => S45.restrict (M a) S := by
  refine Measurable.of_eval_matrix _ fun p q => ?_
  have h : Measurable fun a => M a p.val q.val :=
    ((measurable_pi_apply q.val).comp ((measurable_pi_apply p.val).comp hM))
  simpa [S45.restrict, Matrix.submatrix_apply] using h

private theorem measurable_pullback {α : Type} [MeasurableSpace α] {H : Type}
    [Fintype H] [DecidableEq H]
    (B : Matrix (Port d m) H ℝ) {L : α → S45.RMat (Port d m)} (hL : Measurable L) :
    Measurable fun a => S45.pullback B (L a) := by
  refine Measurable.of_eval_matrix _ fun p q => ?_
  have hentry : ∀ r s : Port d m, Measurable fun a : α => L a r s :=
    fun r s => ((measurable_pi_apply s).comp ((measurable_pi_apply r).comp hL))
  simp only [S45.pullback, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun s _ => ?_
  refine (Finset.measurable_sum _ fun r _ => ?_).mul measurable_const
  exact (measurable_const.mul (hentry r s))

private theorem measurable_pullback_map {α : Type} [MeasurableSpace α] {H : Type}
    [Fintype H] [DecidableEq H]
    (B : Matrix (Port d m) H ℝ) {L : α → S45.RMat (Port d m)} (hL : Measurable L) :
    Measurable fun a => ((S45.pullback B (L a)).map fun r : ℝ => (r : ℂ)) := by
  refine Measurable.of_eval_matrix _ fun p q => ?_
  simp only [Matrix.map_apply]
  exact Complex.measurable_ofReal.comp
    (((measurable_pi_apply q).comp ((measurable_pi_apply p).comp
      (measurable_pullback B hL))))

private theorem tilePrefixProcess_getD (k : ℕ) (ω : RandomSources (Torus d m) M) :
    (slotSeq P j T M x k ω).getD x.sweep = (tilePrefixProcess P j T M x k ω).2 := by
  rw [tilePrefixProcess_spec P j T M x k ω]
  cases h : tilePrefixProcess P j T M x k ω with
  | mk alive q =>
    cases alive with
    | false =>
      have hq : q = x.sweep := by
        have hs := tilePrefixProcess_stopped P j T M x k ω
        have hrun : (tilePrefixProcess P j T M x k ω).1 = false := by rw [h]
        exact (congrArg Prod.snd h).symm.trans (hs hrun)
      simp [h, hq]
    | true => simp [h]

private theorem tileEval_measurable (i : Fin (monitorCount P j T)) (k : ℕ)
    (y : Fin (siteCount d m)) :
    @Measurable (RandomSources (Torus d m) M × ℝ)
      (S45.CMat (Fin (monitorDim P j T)))
      ((tileFiltration P j T M x k).prod (borel ℝ)) _
      (fun a => tileEval P j T M x i k a.1 y a.2) := by
  classical
  let α := RandomSources (Torus d m) M × ℝ
  let mα : MeasurableSpace α := (tileFiltration P j T M x k).prod (borel ℝ)
  letI : MeasurableSpace α := mα
  let Q : α → S45.Sequence (Port d m) := fun a =>
    (slotSeq P j T M x k a.1).getD x.sweep
  let site : α → Torus d m := fun _ => (siteRank d m).symm y
  let z : α → ℝ := fun a => a.2
  have hQ : SeqMeasAt mα Q := by
    change @Measurable α _ mα _ (fun a => seqCode (Q a))
    have hproc := ((tilePrefixProcess_measurable P j T M x k).2).comp
      (@measurable_fst (RandomSources (Torus d m) M) ℝ
        (tileFiltration P j T M x k) (borel ℝ))
    have heq : Q = fun a : α => (tilePrefixProcess P j T M x k a.1).2 := by
      funext a
      exact tilePrefixProcess_getD P j T M x k a.1
    rw [heq]
    exact hproc
  have hqeq : (fun a : α => (slotSeq P j T M x k a.1).getD x.sweep) = Q := by
    funext a
    rfl
  have hsite : Measurable site := measurable_const
  have hz : Measurable z := measurable_snd
  have hcan : SeqMeasAt mα (fun a => candidate P j x (Q a) (site a) (z a)) :=
    seqMeas_candidate P j x mα hQ hsite hz
  have hr : Measurable fun _ : α => portR (sweepTheta P.u m j) x.r :=
    measurable_portR _ measurable_const
  have hQ' : SeqMeas Q := hQ
  have hlen : Measurable fun a : α => (Q a).length := hQ'.length
  have hstate := hQ'.stateAt hlen
  have hliveSet : MeasurableSet {a : α | (site a, false) ∈ ((Q a).state (Q a).length).live} := by
    have hc := hstate.live
    have heq : {a : α | (site a, false) ∈ ((Q a).state (Q a).length).live} =
        {a | ((siteRank d m).symm y, false) ∈ ((Q a).state (Q a).length).live} := by
      ext a
      simp [site]
    rw [heq]
    exact measurableSet_mem_of_code hc ((siteRank d m).symm y, false)
  have hc : SeqMeas (fun a : α => candidate P j x (Q a) (site a) (z a)) := hcan
  have hstepLag : Measurable fun a : α =>
      (candidate P j x (Q a) (site a) (z a)).stepLag (sweepScale P.u m j)
        (portR (sweepTheta P.u m j) x.r) ((Q a).length) := by
    have hfam : Measurable fun a : α => fun l : ℕ =>
        (candidate P j x (Q a) (site a) (z a)).stepLag
          (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) l := by
      apply measurable_pi_iff.mpr
      intro l
      exact (hc.stepLag hr (sweepScale P.u m j) l)
    exact measurable_lookup hfam hlen
  have hstepRow (cols : Finset (Port d m)) : Measurable fun a : α =>
      (candidate P j x (Q a) (site a) (z a)).stepRow (sweepScale P.u m j)
        (portR (sweepTheta P.u m j) x.r) cols ((Q a).length) := by
    have hfam : Measurable fun a : α => fun l : ℕ =>
        (candidate P j x (Q a) (site a) (z a)).stepRow
          (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) cols l := by
      apply measurable_pi_iff.mpr
      intro l
      exact (hc.stepRow hr (sweepScale P.u m j) cols l)
    exact measurable_lookup hfam hlen
  have hstepJ : Measurable fun a : α =>
      (candidate P j x (Q a) (site a) (z a)).stepJ (sweepScale P.u m j)
        (portR (sweepTheta P.u m j) x.r) ((Q a).length) := by
    have hfam : Measurable fun a : α => fun l : ℕ =>
        (candidate P j x (Q a) (site a) (z a)).stepJ
          (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) l := by
      apply measurable_pi_iff.mpr
      intro l
      exact (hc.stepJ hr (sweepScale P.u m j) l)
    exact measurable_lookup hfam hlen
  have hstepL : Measurable fun a : α =>
      (candidate P j x (Q a) (site a) (z a)).stepL (sweepScale P.u m j)
        (portR (sweepTheta P.u m j) x.r) ((Q a).length) := by
    have hfam : Measurable fun a : α => fun l : ℕ =>
        (candidate P j x (Q a) (site a) (z a)).stepL
          (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) l := by
      apply measurable_pi_iff.mpr
      intro l
      exact (hc.stepL hr (sweepScale P.u m j) l)
    exact measurable_lookup hfam hlen
  -- The outer guard splits into the fixed `activeIn` fact and the measurable live test.
  -- For fixed `i` the inner `dite` chain is a single branch.
  have hLagVal : ∀ p : Port d m, Measurable fun a : α =>
      (candidate P j x (Q a) (site a) (z a)).stepLag (sweepScale P.u m j)
        (portR (sweepTheta P.u m j) x.r) ((Q a).length) p :=
    fun p => ((measurable_pi_apply p).comp hstepLag)
  have hRowVal : ∀ (cols : Finset (Port d m)) (p : Port d m),
      Measurable fun a : α =>
        (candidate P j x (Q a) (site a) (z a)).stepRow (sweepScale P.u m j)
          (portR (sweepTheta P.u m j) x.r) cols ((Q a).length) p :=
    fun cols p => ((measurable_pi_apply p).comp (hstepRow cols))
  have hBranchJ : Measurable fun a : α => padInto _ (embJ P j T)
      (S45.dilation (S45.restrict
        ((candidate P j x (Q a) (site a) (z a)).stepJ (sweepScale P.u m j)
          (portR (sweepTheta P.u m j) x.r) ((Q a).length))
        (innerPorts P j T))) :=
    measurable_padInto _ (measurable_dilation (measurable_restrict hstepJ _))
  have hBranchL : Measurable fun a : α => padInto _ (embL P j T)
      (S45.dilation (((S45.pullback ((P.cover j).cover.coords T).B
        ((candidate P j x (Q a) (site a) (z a)).stepL (sweepScale P.u m j)
          (portR (sweepTheta P.u m j) x.r) ((Q a).length))).map fun r : ℝ => (r : ℂ)))) :=
    measurable_padInto _ (measurable_dilation (measurable_pullback_map _ hstepL))
  have hLive : MeasurableSet {a : α |
      (((siteRank d m).symm y, false) : Port d m) ∈ ((Q a).state (Q a).length).live} := by
    have heq : {a : α | (site a, false) ∈ ((Q a).state (Q a).length).live} =
        {a : α | (((siteRank d m).symm y, false) : Port d m) ∈
          ((Q a).state (Q a).length).live} := by
      ext a
      simp [site]
    rw [← heq]
    exact hliveSet
  by_cases hact : activeIn P j T x ((siteRank d m).symm y)
  · by_cases h1 : i.val < (innerPorts P j T).card
    · have hBranch : Measurable fun a : α => padInto _ (embS P j T)
          (scalarDilation ((candidate P j x (Q a) (site a) (z a)).stepLag
            (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) ((Q a).length)
            ((innerPorts P j T).equivFin.symm ⟨i.val, h1⟩ : Port d m))) :=
        measurable_padInto _ (measurable_scalarDilation
          (hLagVal ((innerPorts P j T).equivFin.symm ⟨i.val, h1⟩ : Port d m)))
      have hEq : (fun a : α => tileEval P j T M x i k a.1 y a.2) =
          (fun a : α => if (((siteRank d m).symm y, false) : Port d m) ∈
            ((Q a).state (Q a).length).live then
              padInto _ (embS P j T) (scalarDilation
                ((candidate P j x (Q a) (site a) (z a)).stepLag
                  (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                  ((Q a).length)
                  ((innerPorts P j T).equivFin.symm ⟨i.val, h1⟩ : Port d m)))
            else 0) := by
        funext a
        unfold tileEval
        simp only [hact, true_and, dif_pos h1, Q, site, z]
      rw [hEq]
      exact Measurable.ite hLive hBranch measurable_const
    · by_cases h2 : i.val < 2 * (innerPorts P j T).card
      · have hBranch : Measurable fun a : α => padInto _ (embS P j T)
            (scalarBlock ((candidate P j x (Q a) (site a) (z a)).stepRow
              (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) Finset.univ
              ((Q a).length)
              ((innerPorts P j T).equivFin.symm
                ⟨i.val - (innerPorts P j T).card, by omega⟩ : Port d m))) :=
          measurable_padInto _ (measurable_scalarBlock
            (hRowVal Finset.univ ((innerPorts P j T).equivFin.symm
              ⟨i.val - (innerPorts P j T).card, by omega⟩ : Port d m)))
        have hEq : (fun a : α => tileEval P j T M x i k a.1 y a.2) =
            (fun a : α => if (((siteRank d m).symm y, false) : Port d m) ∈
              ((Q a).state (Q a).length).live then
                padInto _ (embS P j T) (scalarBlock
                  ((candidate P j x (Q a) (site a) (z a)).stepRow
                    (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                    Finset.univ ((Q a).length)
                    ((innerPorts P j T).equivFin.symm
                      ⟨i.val - (innerPorts P j T).card, by omega⟩ : Port d m)))
              else 0) := by
          funext a
          unfold tileEval
          simp only [hact, true_and, dif_neg h1, dif_pos h2, Q, site, z]
        rw [hEq]
        exact Measurable.ite hLive hBranch measurable_const
      · by_cases h3 : i.val < 3 * (innerPorts P j T).card
        · have hBranch : Measurable fun a : α => padInto _ (embS P j T)
              (scalarBlock ((candidate P j x (Q a) (site a) (z a)).stepRow
                (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) S45.reserves
                ((Q a).length)
                ((innerPorts P j T).equivFin.symm
                  ⟨i.val - 2 * (innerPorts P j T).card, by omega⟩ : Port d m))) :=
            measurable_padInto _ (measurable_scalarBlock
              (hRowVal S45.reserves ((innerPorts P j T).equivFin.symm
                ⟨i.val - 2 * (innerPorts P j T).card, by omega⟩ : Port d m)))
          have hEq : (fun a : α => tileEval P j T M x i k a.1 y a.2) =
              (fun a : α => if (((siteRank d m).symm y, false) : Port d m) ∈
                ((Q a).state (Q a).length).live then
                  padInto _ (embS P j T) (scalarBlock
                    ((candidate P j x (Q a) (site a) (z a)).stepRow
                      (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                      S45.reserves ((Q a).length)
                      ((innerPorts P j T).equivFin.symm
                        ⟨i.val - 2 * (innerPorts P j T).card, by omega⟩ : Port d m)))
                else 0) := by
            funext a
            unfold tileEval
            simp only [hact, true_and, dif_neg h1, dif_neg h2, dif_pos h3,
              Q, site, z]
          rw [hEq]
          exact Measurable.ite hLive hBranch measurable_const
        · by_cases h4 : i.val = 3 * (innerPorts P j T).card
          · have hEq : (fun a : α => tileEval P j T M x i k a.1 y a.2) =
                (fun a : α => if (((siteRank d m).symm y, false) : Port d m) ∈
                  ((Q a).state (Q a).length).live then
                    padInto _ (embJ P j T) (S45.dilation (S45.restrict
                      ((candidate P j x (Q a) (site a) (z a)).stepJ
                        (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                        ((Q a).length)) (innerPorts P j T)))
                  else 0) := by
              funext a
              unfold tileEval
              simp only [hact, true_and, dif_neg h1, dif_neg h2, dif_neg h3,
                if_pos h4, Q, site, z]
            rw [hEq]
            exact Measurable.ite hLive hBranchJ measurable_const
          · have hEq : (fun a : α => tileEval P j T M x i k a.1 y a.2) =
                (fun a : α => if (((siteRank d m).symm y, false) : Port d m) ∈
                  ((Q a).state (Q a).length).live then
                    padInto _ (embL P j T) (S45.dilation
                      (((S45.pullback ((P.cover j).cover.coords T).B
                        ((candidate P j x (Q a) (site a) (z a)).stepL
                          (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                          ((Q a).length))).map fun r : ℝ => (r : ℂ))))
                  else 0) := by
              funext a
              unfold tileEval
              simp only [hact, true_and, dif_neg h1, dif_neg h2, dif_neg h3,
                if_neg h4, Q, site, z]
            rw [hEq]
            exact Measurable.ite hLive hBranchL measurable_const
  · have hEq : (fun a : α => tileEval P j T M x i k a.1 y a.2) = fun _ => 0 := by
      funext a
      unfold tileEval
      simp only [hact, false_and, Q, site, z, ↓reduceIte]
    rw [hEq]
    exact measurable_const

theorem tileEval_stronglyMeasurable (i : Fin (monitorCount P j T)) (k : ℕ)
    (y : Fin (siteCount d m)) :
    @StronglyMeasurable (RandomSources (Torus d m) M × ℝ)
      (S45.CMat (Fin (monitorDim P j T))) _
      ((tileFiltration P j T M x k).prod (borel ℝ))
      (fun a => tileEval P j T M x i k a.1 y a.2) := by
  exact (tileEval_measurable P j T M x i k y).stronglyMeasurable

end EvaluationMeasurability

/-! ## Running prefixes are valid (from `trialOk`)

At a running slot the included prefix ending at `slotSeq k` is valid with the
standing data: `trialOk` (the continuation test of `slotStep`) asserts validity
of the extended prefix, and skipped slots keep the old prefix. Uses only
`TileGoodCore.valid` and the definitions; no S45 inventory item is needed.
-/

section RunningValidity
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
  (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)

theorem slotSeq_valid_of_run (C : ℝ) (hx : TileGoodCore C P j T x)
    (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hrun : tileRun P j T M x k ω = true) :
    ∃ q, slotSeq P j T M x k ω = some q ∧
      q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        (stageD0 P j x) q.length := by
  classical
  induction k with
  | zero =>
    refine ⟨x.sweep, by simp only [slotSeq], hx.valid _ le_rfl⟩
  | succ k ih =>
    have hseq : slotSeq P j T M x (k + 1) ω =
        (if k < slotCount P j T then
          (slotSeq P j T M x k ω).bind (fun q =>
            slotStep P j T x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
        else slotSeq P j T M x k ω) := by
      simp only [slotSeq]
    have hrun' : ((if k < slotCount P j T then
          (slotSeq P j T M x k ω).bind (fun q =>
            slotStep P j T x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
        else slotSeq P j T M x k ω)).isSome = true := by
      simpa [tileRun, hseq] using hrun
    by_cases hk : k < slotCount P j T
    · rw [if_pos hk] at hseq hrun'
      have hsome : (slotSeq P j T M x k ω).isSome = true := by
        cases h : slotSeq P j T M x k ω with
        | none => simp [h] at hrun'
        | some _ => simp [h]
      have hrun0 : tileRun P j T M x k ω = true := by
        simpa [tileRun] using hsome
      obtain ⟨q0, hq0, hvalid0⟩ := ih hrun0
      rw [hq0] at hseq hrun'
      simp only [Option.bind_some] at hseq hrun'
      by_cases he : activeIn P j T x (tileSlot P j T M k ω) ∧
          ((tileSlot P j T M k ω, false) : Port d m) ∈ (q0.state q0.length).live
      · have hstep : slotStep P j T x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω) =
            (if trialOk P j T x
              (candidate P j x q0 (tileSlot P j T M k ω) (tileXi P j T M x k ω))
              (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                (q0.state q0.length) (tileSlot P j T M k ω, false)
                (tileXi P j T M x k ω))
            then some (candidate P j x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω)) else none) := by
          simp [slotStep, he]
        rw [hstep] at hseq hrun'
        by_cases ht : trialOk P j T x
            (candidate P j x q0 (tileSlot P j T M k ω) (tileXi P j T M x k ω))
            (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
              (q0.state q0.length) (tileSlot P j T M k ω, false)
              (tileXi P j T M x k ω))
        · rw [if_pos ht] at hseq hrun'
          obtain ⟨-, hvalid, -⟩ := ht
          exact ⟨_, hseq, hvalid⟩
        · rw [if_neg ht] at hrun'
          simp at hrun'
      · have hstep : slotStep P j T x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω) = some q0 := by
          simp [slotStep, he]
        rw [hstep] at hseq hrun'
        exact ⟨q0, hseq, hvalid0⟩
    · rw [if_neg hk] at hseq hrun'
      have hrun0 : tileRun P j T M x k ω = true := by
        simpa [tileRun, hseq] using hrun
      obtain ⟨q0, hq0, hvalid0⟩ := ih hrun0
      exact ⟨q0, by rw [hseq, hq0], hvalid0⟩

end RunningValidity

/-! ## Running prefixes are well formed from the stage start

Same induction as validity: skipped slots keep the prefix, extended slots go
through `candidate`/`extendSeq`, whose well-formedness is `extendSeq_wellFormed`
(the pivot is live by eligibility, the denominator is nonzero by `trialOk`).
`extendSeq` never touches `state 0`, so the start state is the sweep's.
Uses only `TileGoodCore.wellFormed` and the definitions.
-/

section RunningWellFormed
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ)
  (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)

theorem slotSeq_wellFormed_of_run (C : ℝ) (hx : TileGoodCore C P j T x)
    (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hrun : tileRun P j T M x k ω = true) :
    ∃ q, slotSeq P j T M x k ω = some q ∧
      q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) ∧
      q.state 0 = x.sweep.state 0 := by
  classical
  induction k with
  | zero =>
    exact ⟨x.sweep, by simp only [slotSeq], hx.wellFormed, rfl⟩
  | succ k ih =>
    have hseq : slotSeq P j T M x (k + 1) ω =
        (if k < slotCount P j T then
          (slotSeq P j T M x k ω).bind (fun q =>
            slotStep P j T x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
        else slotSeq P j T M x k ω) := by
      simp only [slotSeq]
    have hrun' : ((if k < slotCount P j T then
          (slotSeq P j T M x k ω).bind (fun q =>
            slotStep P j T x q (tileSlot P j T M k ω) (tileXi P j T M x k ω))
        else slotSeq P j T M x k ω)).isSome = true := by
      simpa [tileRun, hseq] using hrun
    by_cases hk : k < slotCount P j T
    · rw [if_pos hk] at hseq hrun'
      have hsome : (slotSeq P j T M x k ω).isSome = true := by
        cases h : slotSeq P j T M x k ω with
        | none => simp [h] at hrun'
        | some _ => simp [h]
      have hrun0 : tileRun P j T M x k ω = true := by
        simpa [tileRun] using hsome
      obtain ⟨q0, hq0, hwf0, hst0⟩ := ih hrun0
      rw [hq0] at hseq hrun'
      simp only [Option.bind_some] at hseq hrun'
      by_cases he : activeIn P j T x (tileSlot P j T M k ω) ∧
          ((tileSlot P j T M k ω, false) : Port d m) ∈ (q0.state q0.length).live
      · have hstep : slotStep P j T x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω) =
            (if trialOk P j T x
              (candidate P j x q0 (tileSlot P j T M k ω) (tileXi P j T M x k ω))
              (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
                (q0.state q0.length) (tileSlot P j T M k ω, false)
                (tileXi P j T M x k ω))
            then some (candidate P j x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω)) else none) := by
          simp [slotStep, he]
        rw [hstep] at hseq hrun'
        by_cases ht : trialOk P j T x
            (candidate P j x q0 (tileSlot P j T M k ω) (tileXi P j T M x k ω))
            (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
              (q0.state q0.length) (tileSlot P j T M k ω, false)
              (tileXi P j T M x k ω))
        · rw [if_pos ht] at hseq hrun'
          obtain ⟨hden, -, -⟩ := ht
          have hwf : (candidate P j x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω)).wellFormed
              (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) :=
            extendSeq_wellFormed _ _ _ hwf0 _ _ he.2 hden
          have hst : (candidate P j x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω)).state 0 = x.sweep.state 0 := by
            unfold candidate
            simp only [extendSeq]
            rw [if_neg (by omega : (0 : ℕ) ≠ q0.length + 1)]
            exact hst0
          exact ⟨_, hseq, hwf, hst⟩
        · rw [if_neg ht] at hrun'
          simp at hrun'
      · have hstep : slotStep P j T x q0 (tileSlot P j T M k ω)
              (tileXi P j T M x k ω) = some q0 := by
          simp [slotStep, he]
        rw [hstep] at hseq hrun'
        exact ⟨q0, hseq, hwf0, hst0⟩
    · rw [if_neg hk] at hseq hrun'
      have hrun0 : tileRun P j T M x k ω = true := by
        simpa [tileRun, hseq] using hrun
      obtain ⟨q0, hq0, hwf0, hst0⟩ := ih hrun0
      exact ⟨q0, by rw [hseq, hq0], hwf0, hst0⟩

end RunningWellFormed

/-! ## Input/Output-constant separation for `OrderedRawBounds` and `TileMonitorBoundsStatement2`

`TileMonitorBoundsStatement` in `TileCore.lean:256` uses the same existential constant `C'` both
as the output monitor factor and in the input scalar bounds (`MomentLaw (ρ y) t C' id`,
`|z y| ≤ C' √t`, `|z| ≤ C' √t`), whereas `TileSlotLawStatement` (tile slot law) supplies `UniformSlotLaw`
with input scalar constant `2` (`|tileXi| ≤ 2 √t`). In `S45.FamilyTable`, the output constant
grows polynomially of degree ≥ 2 in the input scalar constant with zero `t`-slack against
`monitorBias / logFactor`, `monitorVariance / logFactor`, and `monitorJump`.

We provide:
- `ordered_raw_bounds_in_out`: `AgentS45.ordered_raw_bounds_proof` with separate input constant
  `C_in` and output constant `C_out`;
- `TileMonitorBoundsStatement2 d C`: `TileMonitorBoundsStatement d C` with input scalar constant
  `2` matching `TileSlotLawStatement`;
- `tileCrossing_of_pieces2`: drop-in replacement for `tileCrossing_of_pieces` consuming
  `TileMonitorBoundsStatement2 d C`.
-/

theorem sweepScale_pos_a2 {u : ℝ} (hu : 0 < u) (m j : ℕ) : 0 < sweepScale u m j := by
  unfold sweepScale stageScale
  split_ifs <;> positivity

section OrderedRawBoundsInOut

open AndersonAC.AgentS45

theorem ordered_raw_bounds_in_out {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (n s M : ℕ) (t C_in C_out : ℝ) (kind : Fin s → S45.MonitorKind) (dim : Fin s → ℕ)
    (run : ℕ → Ω → Bool) (remaining : ℕ → Ω → Finset (Fin n))
    (slot : ℕ → Ω → Fin n) (ξ : ℕ → Ω → ℝ)
    (eval : ∀ i : Fin s, ℕ → Ω → Fin n → ℝ → S45.CMat (Fin (dim i)))
    (hscale : 0 < t ∧ t < 1) (_hCin : 1 ≤ C_in) (hCout : 1 ≤ C_out)
    (hlaw : S45.UniformSlotLaw μ ℱ M t C_in run remaining slot ξ)
    (hcount : ∀ k < M, ∀ ω, run k ω = true → (remaining k ω).card = M - k)
    (hmeas : ∀ i k x, @StronglyMeasurable (Ω × ℝ) (S45.CMat (Fin (dim i))) _
      ((ℱ k).prod (borel ℝ)) (fun a => eval i k a.1 x a.2))
    (hherm : ∀ i k ω x z, (eval i k ω x z).IsHermitian)
    (hmean : ∀ i k, k < M → ∀ ω, run k ω = true →
      ∀ (ρ : Fin n → Measure ℝ), (∀ x, IsProbabilityMeasure (ρ x)) →
      (∀ x ∈ remaining k ω, S45.MomentLaw (ρ x) t C_in id) →
      ‖∑ x ∈ remaining k ω, ∫ z, eval i k ω x z ∂(ρ x)‖ ≤
        C_out * S45.monitorBias t (kind i) / S45.logFactor t)
    (hstack : ∀ i k, k < M → ∀ ω, run k ω = true → ∀ z : Fin n → ℝ,
      (∀ x ∈ remaining k ω, |z x| ≤ C_in * Real.sqrt t) →
      (∑ x ∈ remaining k ω, (eval i k ω x (z x))^2) ≤
        (C_out * S45.monitorVariance t (kind i) / S45.logFactor t) • (1 : S45.CMat (Fin (dim i))))
    (hjump : ∀ i k, k < M → ∀ ω, run k ω = true → ∀ x ∈ remaining k ω,
      ∀ z, |z| ≤ C_in * Real.sqrt t → ‖eval i k ω x z‖ ≤ C_out * S45.monitorJump t (kind i)) :
    ∃ a : S45.OrderedRawBounds μ ℱ s M t C_out,
      a.kind = kind ∧ a.dimension = dim ∧
      ∀ i k ω, HEq (a.raw i (k + 1) ω)
        (if k < M ∧ run k ω = true then eval i k ω (slot k ω) (ξ k ω) else 0) := by
  obtain ⟨ht, ht1⟩ := hscale
  have hC0 : 0 < C_out := by linarith
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  haveI : Nonempty (Fin n) := ⟨slot 0 (Classical.arbitrary Ω)⟩
  have hL := logFactor_pos ht ht1.le
  have hmon := fun i => monitor_nonneg ht ht1.le (kind i)
  have hJ0 : ∀ i, 0 ≤ C_out * S45.monitorJump t (kind i) := fun i => mul_nonneg hC0.le (hmon i).1
  let F : ∀ i, ℕ → Ω × (Fin n × ℝ) → S45.CMat (Fin (dim i)) := fun i k p =>
    if run k p.1 = true then eval i k p.1 p.2.1 p.2.2 else 0
  have hFsm : ∀ i k, k < M →
      @StronglyMeasurable _ _ _ ((ℱ k : MeasurableSpace Ω).prod inferInstance) (F i k) := by
    intro i k hk
    set m : MeasurableSpace (Ω × (Fin n × ℝ)) := (ℱ k : MeasurableSpace Ω).prod inferInstance
    have hproj : @Measurable (Ω × (Fin n × ℝ)) (Ω × ℝ) m ((ℱ k : MeasurableSpace Ω).prod (borel ℝ))
        (fun p => (p.1, p.2.2)) := by
      have h1 : @Measurable (Ω × (Fin n × ℝ)) Ω m (ℱ k) Prod.fst :=
        @measurable_fst Ω (Fin n × ℝ) (ℱ k) _
      have h2 : @Measurable (Ω × (Fin n × ℝ)) ℝ m (borel ℝ) (fun p => p.2.2) :=
        (@measurable_snd Ω (Fin n × ℝ) (ℱ k) _).snd
      exact h1.prodMk h2
    have hE : @StronglyMeasurable _ _ _ m (fun p : Ω × (Fin n × ℝ) => eval i k p.1 p.2.1 p.2.2) := by
      have hsum : (fun p : Ω × (Fin n × ℝ) => eval i k p.1 p.2.1 p.2.2) =
          fun p => ∑ x, (if p.2.1 = x then eval i k p.1 x p.2.2 else 0) := by
        funext p; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      rw [hsum]
      refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
      have hset : MeasurableSet[m] {p : Ω × (Fin n × ℝ) | p.2.1 = x} :=
        (@measurable_snd Ω (Fin n × ℝ) (ℱ k) _).fst (measurableSet_singleton x)
      exact StronglyMeasurable.ite hset ((hmeas i k x).comp_measurable hproj)
        stronglyMeasurable_const
    have hR : MeasurableSet[m] {p : Ω × (Fin n × ℝ) | run k p.1 = true} :=
      (@measurable_fst Ω (Fin n × ℝ) (ℱ k) _) (measurableSet_run hlaw hk)
    exact StronglyMeasurable.ite hR hE stronglyMeasurable_const
  have hraw : ∀ i k, k < M → rawOf (M := M) run slot ξ eval i (k + 1) =
      fun ω => F i k (ω, pairY slot ξ k ω) := by
    intro i k hk; funext ω; simp [rawOf, F, pairY, hk]
  have hraw0 : ∀ i k, ¬ k < M → rawOf (M := M) run slot ξ eval i (k + 1) = fun _ => 0 := by
    intro i k hk; funext ω; simp [rawOf, hk]
  have hadapt : ∀ i k, StronglyMeasurable[ℱ k] (rawOf (M := M) run slot ξ eval i k) := by
    intro i k
    cases k with
    | zero => exact stronglyMeasurable_const
    | succ k =>
      by_cases hk : k < M
      · rw [hraw i k hk]
        have hg : @Measurable Ω (Ω × (Fin n × ℝ)) (ℱ (k + 1))
            ((ℱ k : MeasurableSpace Ω).prod inferInstance) (fun ω => (ω, pairY slot ξ k ω)) := by
          have h1 : @Measurable Ω Ω (ℱ (k + 1)) (ℱ k) id :=
            fun s hs => ℱ.mono (Nat.le_succ k) s hs
          exact h1.prodMk (measurable_pairY hlaw hk)
        exact (hFsm i k hk).comp_measurable hg
      · rw [hraw0 i k hk]; exact stronglyMeasurable_const
  have hjumpae : ∀ i k, ∀ᵐ ω ∂μ,
      ‖rawOf (M := M) run slot ξ eval i (k + 1) ω‖ ≤ C_out * S45.monitorJump t (kind i) := by
    intro i k
    by_cases hk : k < M
    · filter_upwards [slot_mem_ae hlaw hk, hlaw.bounded k hk] with ω h1 h2
      simp only [rawOf, hk, true_and]
      split
      next hr => exact hjump i k hk ω hr _ (h1 hr) _ (h2 hr)
      next => rw [norm_zero]; exact hJ0 i
    · exact ae_of_all _ fun ω => by rw [hraw0 i k hk, norm_zero]; exact hJ0 i
  have hint : ∀ i k, Integrable (rawOf (M := M) run slot ξ eval i (k + 1)) μ := fun i k =>
    Integrable.of_bound (((hadapt i (k + 1)).mono (ℱ.le _)).aestronglyMeasurable) _ (hjumpae i k)
  have hint2 : ∀ i k, Integrable (fun ω => (rawOf (M := M) run slot ξ eval i (k + 1) ω) ^ 2) μ := by
    intro i k
    refine Integrable.of_bound ((((hadapt i (k + 1)).mono (ℱ.le _)).pow 2).aestronglyMeasurable)
      ((C_out * S45.monitorJump t (kind i)) ^ 2) ?_
    filter_upwards [hjumpae i k] with ω hω
    have h2 : ‖(rawOf (M := M) run slot ξ eval i (k + 1) ω) ^ 2‖ ≤
        ‖rawOf (M := M) run slot ξ eval i (k + 1) ω‖ ^ 2 := by
      rw [pow_two, pow_two]; exact norm_mul_le _ _
    exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) hω 2)
  refine ⟨{ kind := kind
            dimension := dim
            raw := rawOf (M := M) run slot ξ eval
            adapted := fun i k => hadapt i k
            measurable := fun i k => ((hadapt i k).mono (ℱ.le k)).aestronglyMeasurable
            hermitian := fun i k => ae_of_all _ fun ω => ?_
            finite_horizon := fun i k hk ω => ?_
            jump := hjumpae
            mean := fun i k hk => ?_
            square := fun i k hk => ?_ }, rfl, rfl, fun i k ω => ?_⟩
  · simp only [rawOf]
    split
    · exact hherm _ _ _ _ _
    · exact Matrix.isHermitian_zero
  · rw [hraw0 i k (not_lt.2 hk)]
  · have hY : Measurable (pairY slot ξ k) := (measurable_pairY hlaw hk).mono (ℱ.le _) le_rfl
    have hce := condExp_eq_integral_condLaw (m := ℱ k) (μ := μ) (ℱ.le k) hY (hFsm i k hk)
      (by rw [← hraw i k hk]; exact hint i k)
    rw [hraw i k hk]
    filter_upwards [hce, slotHyp_ae hlaw hk] with ω h1 h2
    rw [h1]
    have hrhs : 0 ≤ C_out * S45.monitorBias t (kind i) / S45.logFactor t / ((M - k : ℕ) : ℝ) := by
      have := (hmon i).2.2; positivity
    by_cases hr : run k ω = true
    · have hS := h2 hr
      have hGsm : ∀ x, StronglyMeasurable (fun z => eval i k ω x z) := fun x => by
        have hz : @Measurable ℝ (Ω × ℝ) _ ((ℱ k : MeasurableSpace Ω).prod (borel ℝ))
            (fun z => (ω, z)) := by
          have h1 : @Measurable ℝ Ω _ (ℱ k) (fun _ => ω) := measurable_const
          have h2 : @Measurable ℝ ℝ _ (borel ℝ) (fun z => z) := measurable_id
          exact h1.prodMk h2
        exact (hmeas i k x).comp_measurable hz
      have e1 : ∫ y, F i k (ω, y) ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) =
          ∫ y, eval i k ω y.1 y.2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) := by
        congr 1; funext y; simp [F, hr]
      rw [e1, hS.integral_decomp (fun x z => eval i k ω x z) hGsm (C_out * S45.monitorJump t (kind i))
        (fun x hx z hz => hjump i k hk ω hr x hx z hz)]
      have hm := hmean i k hk ω hr (slotLaw (condLaw (ℱ k) μ (pairY slot ξ k) ω) (remaining k ω))
        hS.isProb (fun x hx => hS.momentLaw hx)
      rw [norm_smul, Real.norm_eq_abs, hcount k hk ω hr]
      have hc : (0 : ℝ) < ((M - k : ℕ) : ℝ) := by
        have := hcount k hk ω hr ▸ hS.card
        exact_mod_cast this
      rw [abs_of_nonneg (by positivity), one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hm hc.le
    · have e1 : ∫ y, F i k (ω, y) ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) = 0 := by
        simp [F, hr]
      rw [e1, norm_zero]; exact hrhs
  · have hY : Measurable (pairY slot ξ k) := (measurable_pairY hlaw hk).mono (ℱ.le _) le_rfl
    have hF2 : @StronglyMeasurable _ _ _ ((ℱ k : MeasurableSpace Ω).prod inferInstance)
        (fun p => (F i k p) ^ 2) := (hFsm i k hk).pow 2
    have hce := condExp_eq_integral_condLaw (m := ℱ k) (μ := μ) (ℱ.le k) hY hF2
      (by
        have := hint2 i k
        rw [hraw i k hk] at this
        exact this)
    rw [hraw i k hk]
    filter_upwards [hce, slotHyp_ae hlaw hk] with ω h1 h2
    rw [h1]
    set σ := C_out * S45.monitorVariance t (kind i) / S45.logFactor t with hσdef
    have hσ : 0 ≤ σ := by have := (hmon i).2.1; positivity
    by_cases hr : run k ω = true
    · have hS := h2 hr
      have hGsm : ∀ x, StronglyMeasurable (fun z => (eval i k ω x z) ^ 2) := fun x => by
        have hz : @Measurable ℝ (Ω × ℝ) _ ((ℱ k : MeasurableSpace Ω).prod (borel ℝ))
            (fun z => (ω, z)) := by
          have h1 : @Measurable ℝ Ω _ (ℱ k) (fun _ => ω) := measurable_const
          have h2 : @Measurable ℝ ℝ _ (borel ℝ) (fun z => z) := measurable_id
          exact h1.prodMk h2
        exact ((hmeas i k x).comp_measurable hz).pow 2
      have hbd2 : ∀ x ∈ remaining k ω, ∀ z, |z| ≤ C_in * Real.sqrt t →
          ‖(eval i k ω x z) ^ 2‖ ≤ (C_out * S45.monitorJump t (kind i)) ^ 2 := by
        intro x hx z hz
        have h := hjump i k hk ω hr x hx z hz
        have h2 : ‖(eval i k ω x z) ^ 2‖ ≤ ‖eval i k ω x z‖ ^ 2 := by
          rw [pow_two, pow_two]; exact norm_mul_le _ _
        exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) h 2)
      have e1 : ∫ y, (F i k (ω, y)) ^ 2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) =
          ∫ y, (eval i k ω y.1 y.2) ^ 2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) := by
        congr 1; funext y; simp [F, hr]
      rw [e1, hS.integral_decomp (fun x z => (eval i k ω x z) ^ 2) hGsm _ hbd2]
      have hst := @stack_integral n (dim i) (slotLaw (condLaw (ℱ k) μ (pairY slot ξ k) ω)
        (remaining k ω)) (fun x => hS.isProb x) (remaining k ω) t C_in σ _
        (fun x hx => hS.ae_bdd hx) (fun x z => (eval i k ω x z) ^ 2) hGsm hbd2
        (fun z hz => hstack i k hk ω hr z hz)
      have hc : (0 : ℝ) < ((M - k : ℕ) : ℝ) := by
        have := hcount k hk ω hr ▸ hS.card
        exact_mod_cast this
      have hmono := smul_le_smul_of_nonneg_left hst
        (by positivity : (0 : ℝ) ≤ 1 / ((remaining k ω).card : ℝ))
      refine hmono.trans (le_of_eq ?_)
      rw [smul_smul, hcount k hk ω hr, one_div_mul_eq_div]
    · have e1 : ∫ y, (F i k (ω, y)) ^ 2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) = 0 := by
        simp [F, hr]
      rw [e1, Matrix.nonneg_iff_posSemidef]
      have hc : (0 : ℝ) ≤ σ / ((M - k : ℕ) : ℝ) := by positivity
      exact Matrix.PosSemidef.one.smul hc
  · exact HEq.rfl

/-- **monitor bounds (repaired input scalar constant `2` matching `TileSlotLawStatement`).** -/
def TileMonitorBoundsStatement2 (d : ℕ) (C : ℝ) : Prop :=
  ∃ C' ≥ 2, ∃ t0 > 0, ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x → sweepScale P.u m j < t0 →
    let t := sweepScale P.u m j
    let N := slotCount P j T
    let ℱ := tileFiltration P j T M x
    let run := tileRun P j T M x
    let remaining := tileRemaining P j T M
    let eval := tileEval P j T M x
    let kind := monitorKind P j T
    (∀ k < N, @Measurable _ Bool (ℱ k) ⊤ (run k)) ∧
    (∀ i k y, @StronglyMeasurable (RandomSources (Torus d m) M × ℝ)
      (S45.CMat (Fin (monitorDim P j T))) _ ((ℱ k).prod (borel ℝ))
      (fun a => eval i k a.1 y a.2)) ∧
    (∀ i k ω y z, (eval i k ω y z).IsHermitian) ∧
    (∀ i k, k < N → ∀ ω, run k ω = true →
      ∀ (ρ : Fin (siteCount d m) → Measure ℝ), (∀ y, IsProbabilityMeasure (ρ y)) →
      (∀ y ∈ remaining k ω, S45.MomentLaw (ρ y) t 2 id) →
      ‖∑ y ∈ remaining k ω, ∫ z, eval i k ω y z ∂(ρ y)‖ ≤
        C' * S45.monitorBias t (kind i) / S45.logFactor t) ∧
    (∀ i k, k < N → ∀ ω, run k ω = true → ∀ z : Fin (siteCount d m) → ℝ,
      (∀ y ∈ remaining k ω, |z y| ≤ 2 * Real.sqrt t) →
      (∑ y ∈ remaining k ω, (eval i k ω y (z y))^2) ≤
        (C' * S45.monitorVariance t (kind i) / S45.logFactor t) •
          (1 : S45.CMat (Fin (monitorDim P j T)))) ∧
    (∀ i k, k < N → ∀ ω, run k ω = true → ∀ y ∈ remaining k ω,
      ∀ z, |z| ≤ 2 * Real.sqrt t → ‖eval i k ω y z‖ ≤ C' * S45.monitorJump t (kind i))

/-- **Assembly of the tile trial core from `TileMonitorBoundsStatement2`.** -/
theorem tileCrossing_of_pieces2 (d : ℕ) (C : ℝ) (hA0 : TileSlotDescriptionStatement)
    (hA1 : TileSlotLawStatement) (hA2 : TileMonitorBoundsStatement2 d C)
    (hA3 : TileFailCrossingStatement d C) : TileCrossingStatement d C := by
  obtain ⟨C₂, hC₂, t2, ht2, hA2⟩ := hA2
  obtain ⟨t3, ht3, hA3⟩ := hA3
  obtain ⟨C', hC', t1, ht1, hinp⟩ :=
    AgentS45.ordered_trial_inputs_proof (2 * d + 1) C₂ (by linarith)
  set K : ℝ := C₂ / (30 * (max C 1) ^ 2) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨max C' 1, le_max_right _ _, min (min t1 t2) (min t3 (min (1 / 2) K)), ?_, ?_⟩
  · exact lt_min (lt_min ht1 ht2) (lt_min ht3 (lt_min (by norm_num) hKpos))
  intro m P j T M x hu hj hjm hM hab hx htsmall
  set t := sweepScale P.u m j with ht_def
  have htpos : 0 < t := sweepScale_pos_a2 (lt_trans (by norm_num) hu.1) m j
  have ht1' : t < t1 := lt_of_lt_of_le htsmall (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht2' : t < t2 := lt_of_lt_of_le htsmall (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht3' : t < t3 := lt_of_lt_of_le htsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hthalf : t < 1 / 2 := lt_of_lt_of_le htsmall
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htK : t < K := lt_of_lt_of_le htsmall
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have htle1 : t ≤ 1 := by linarith
  set ℱ := tileFiltration P j T M x
  by_cases hN : slotCount P j T = 0
  · refine ⟨ℱ, 0, trialInputs_empty _ ℱ (2 * d + 1) t (max C' 1) (by positivity) htpos.le, ?_⟩
    intro ω hω
    rw [(hA0 d m P j T M x hM hab).1] at hω
    simp only [Set.mem_setOf_eq, hN] at hω
    simp [slotSeq] at hω
  have hNpos : 0 < slotCount P j T := Nat.pos_of_ne_zero hN
  obtain ⟨hrun, hmeas, hherm, hmean, hstack, hjump⟩ :=
    hA2 m P j T M x hu hj hjm hM hab hx ht2'
  have hlaw := hA1 d m C P j T M x hu hj hjm hM hab hx (tileRun P j T M x) hrun
  have hcount : ∀ k < slotCount P j T, ∀ ω, tileRun P j T M x k ω = true →
      (tileRemaining P j T M k ω).card = slotCount P j T - k :=
    fun k hk ω _ => (hA0 d m P j T M x hM hab).2 k hk.le ω
  obtain ⟨a, hak, had, haraw⟩ := ordered_raw_bounds_in_out
    (sourcesLaw (Torus d m) M) ℱ (siteCount d m) (monitorCount P j T) (slotCount P j T) t 2 C₂
    (monitorKind P j T) (fun _ => monitorDim P j T) (tileRun P j T M x) (tileRemaining P j T M)
    (tileSlotF P j T M) (tileXi P j T M x) (tileEval P j T M x) ⟨htpos, by linarith⟩
    (by norm_num) (by linarith) hlaw hcount hmeas hherm hmean hstack hjump
  have hC1 : 1 ≤ C := hx.one_le
  have hX := power_split t htpos d
  set X := S45.power t (-6 * (d : ℝ)) with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]; unfold S45.power
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos htpos htle1
      (by nlinarith [(d.cast_nonneg : (0:ℝ) ≤ d)])
  have h6 : 30 * C ^ 2 ≤ C₂ * S45.power t (-6) := by
    have hmax : C ≤ max C 1 := le_max_left _ _
    have ht6 : t ^ 6 ≤ K := by
      have : t ^ 6 ≤ t := pow_le_of_le_one htpos.le htle1 (by norm_num)
      linarith
    have hp6 : S45.power t (-6) = (t ^ 6)⁻¹ := by
      unfold S45.power
      rw [Real.rpow_eq_pow, show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg htpos.le,
        Real.rpow_natCast]
    rw [hp6, hK] at *
    have ht6pos : 0 < t ^ 6 := by positivity
    rw [le_div_iff₀ (by positivity)] at ht6
    rw [← div_eq_mul_inv, le_div_iff₀ ht6pos]
    have : C ^ 2 ≤ (max C 1) ^ 2 := pow_le_pow_left₀ (by linarith) hmax 2
    nlinarith
  have hdims : (∑ i : Fin (monitorCount P j T), (a.dimension i : ℝ)) ≤
      C₂ * S45.power t (-6 * ((2 * d + 1 : ℕ) : ℝ)) := by
    rw [had]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have := monitor_dims_le C P j T x hx htpos htle1
    rw [hX]
    calc (monitorCount P j T : ℝ) * (monitorDim P j T : ℝ) ≤ 30 * C ^ 2 * X ^ 2 := this
      _ ≤ C₂ * S45.power t (-6) * X ^ 2 :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = C₂ * (X ^ 2 * S45.power t (-6)) := by ring
  have hMle : ((slotCount P j T : ℕ) : ℝ) ≤ C₂ * S45.power t (-6 * ((2 * d + 1 : ℕ) : ℝ)) := by
    rw [hX]
    have hcard := hx.tile_card
    have hCX : 1 ≤ C * X := one_le_mul_of_one_le_of_one_le hC1 hX1
    calc ((slotCount P j T : ℕ) : ℝ) ≤ C * X := hcard
      _ ≤ 30 * C ^ 2 * X ^ 2 := by nlinarith
      _ ≤ C₂ * S45.power t (-6) * X ^ 2 := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = C₂ * (X ^ 2 * S45.power t (-6)) := by ring
  obtain ⟨b, hbk, hbd, hbraw⟩ := hinp (RandomSources (Torus d m) M) (sourcesLaw (Torus d m) M) ℱ
    (monitorCount P j T) (slotCount P j T) t a htpos ht1' hNpos hMle hdims
  refine ⟨ℱ, monitorCount P j T, trialInputs_mono b (le_max_left _ _) htpos htle1, ?_⟩
  intro ω hω
  rw [(hA0 d m P j T M x hM hab).1] at hω
  obtain ⟨i, n, hcross⟩ := hA3 m P j T M x hu hj hjm hM hab hx ht3' ω hω
  refine crossing_of_heq (trialInputs_mono b (le_max_left _ _) htpos htle1) (monitorKind P j T)
    (tileRaw P j T M x) (hbk.trans hak) (hbd.trans had) ?_ ω i n hcross
  intro i k ω
  exact (hbraw i (k + 1) ω).trans (haraw i k ω)

end OrderedRawBoundsInOut

section PrestateAndFormsOfSlotSeq

open Matrix
open scoped BigOperators

theorem rowNorm_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix β β ℂ) :
    S45.rowNorm (A.submatrix e e) ≤ S45.rowNorm A := by
  unfold S45.rowNorm
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have hl1 : S45.l1 (A.submatrix e e i) = S45.l1 (A (e i)) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hl1]
  exact norm_le_pi_norm (fun i' : β => S45.l1 (A i')) (e i)

theorem inverse_row_fintype_with_rowNorm (d : ℕ) (C ρ β : ℝ) (hC : 1 ≤ C) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hβ : 0 < β) :
    ∃ C' > 0, ∃ c > 0, ∃ t0 > 0, ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (t : ℝ)
      (s : S45.State ι) (dist : ι → ι → ℝ),
      0 < t → t < t0 → S45.ShellBounds d C dist → ‖s.K t‖ ≤ ρ → s.g.IsSymm →
      (∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C) → s.F t *ᵥ s.p = s.q →
      (∀ i, |s.q i - s.p i| ≤ C * S45.power t β) →
      (∀ i j, ‖s.h t i j‖ ≤ C / Real.sqrt t) →
      (∀ i j, C * S45.power t (-2) < dist i j →
        ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C)) →
      IsUnit (1 - s.K t) ∧ S45.rowNorm (s.P t) ≤ C' * S45.logFactor t ∧
        (∀ i j, ‖s.P t i j‖ ≤ C' * Real.exp (-c * t ^ 3 * dist i j)) := by
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
  obtain ⟨hunit', hrow', hP'⟩ :=
    hfin n t s' dist' ht htt hshell' hK' hsym' hp' hward' hqp' hcrude' hfar'
  have hs_eq : 1 - s.K t = (1 - s'.K t).submatrix e.symm e.symm := by
    ext i j
    simp [s', AgentS45.State.reindex_K, Matrix.sub_apply, Matrix.one_apply]
  have hsub := submatrix_isUnit_and_inv e.symm (1 - s'.K t) hunit'
  rw [← hs_eq] at hsub
  have hP_sub : s.P t = (s'.P t).submatrix e.symm e.symm := hsub.2
  refine ⟨hsub.1, (hP_sub ▸ rowNorm_submatrix_equiv e.symm (s'.P t)).trans hrow', fun i j => ?_⟩
  change ‖(1 - s.K t)⁻¹ i j‖ ≤ _
  rw [hsub.2]
  change ‖s'.P t (e.symm i) (e.symm j)‖ ≤ _
  have hPij := hP' (e.symm i) (e.symm j)
  simpa [dist'] using hPij

theorem D_submatrix_of_pad_schur {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (L : Finset P_port) (D : Matrix L L ℝ) (A : S45.RMat P_port)
    (hpad : S45.pad L D = S45.pad Lᶜᶜ (S45.schur A Lᶜ)) :
    D = (S45.schur A Lᶜ).submatrix (complComplEquiv L) (complComplEquiv L) := by
  ext i j
  have h1 := congrFun (congrFun hpad i.1) j.1
  have hicc : i.1 ∈ Lᶜᶜ := (complComplEquiv L i).2
  have hjcc : j.1 ∈ Lᶜᶜ := (complComplEquiv L j).2
  rw [AgentS45.pad_apply_mem L D i.2 j.2,
    AgentS45.pad_apply_mem Lᶜᶜ (S45.schur A Lᶜ) hicc hjcc] at h1
  simpa [submatrix_apply, complComplEquiv] using h1

theorem qform_schur_le_of_extend {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (D0 L : S45.RMat P_port) (E : Finset P_port) (ε : ℝ) (hε : 0 ≤ ε ∧ ε < 1)
    (hD0 : S45.constantKernel D0) (hL : L.IsSymm) (hLzero : L *ᵥ (fun _ => 1) = 0)
    (hcap : S45.formAbsLe (S45.qform L) (S45.qform D0) ε) (hproper : E ≠ Finset.univ)
    (v : (↑(Eᶜ) : Type _) → ℝ) (f : P_port → ℝ) (hf : ∀ i : (↑(Eᶜ) : Type _), f i.1 = v i) :
    S45.qform (S45.schur (D0 + L) E) v ≤ (1 + ε) * S45.qform D0 f := by
  classical
  let S := S45.schur (D0 + L) E
  obtain ⟨hS_ker, htrans⟩ :=
    AgentS45.schur_dual_transport_proof D0 L E ε hε hD0 hL hLzero hcap hproper
  let y : (↑(Eᶜ) : Type _) → ℝ := S *ᵥ v
  obtain ⟨hy, hbid⟩ := AgentS45.DupComparison.qform_bidual S hS_ker v
  have hy_dot : (∑ i : (↑(Eᶜ) : Type _), y i * v i) = S45.qform S v := by
    simp only [y, S45.qform]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdual_eq : S45.dualForm (S45.qform S) y = S45.qform S v := by
    linarith [hbid, hy_dot]
  let y_pad : P_port → ℝ := fun i => if hi : i ∈ Eᶜ then y ⟨i, hi⟩ else 0
  have hy_pad : S45.neutral y_pad := by
    unfold S45.neutral at hy ⊢
    rw [← Finset.sum_subset (Finset.subset_univ Eᶜ)
        (fun i _ hi => by simp only [y_pad, dif_neg hi]),
      ← Finset.sum_coe_sort Eᶜ]
    have hsum : (∑ i : (↑(Eᶜ) : Type _), y_pad i.1) = ∑ i : (↑(Eᶜ) : Type _), y i :=
      Finset.sum_congr rfl fun i _ => by simp only [y_pad, dif_pos i.2]
    rw [hsum]
    exact hy
  have hpair : (∑ i : P_port, y_pad i * ((1 + ε) • f) i) = (1 + ε) * S45.qform S v := by
    rw [← Finset.sum_subset (Finset.subset_univ Eᶜ)
        (fun i _ hi => by simp only [y_pad, dif_neg hi, zero_mul]),
      ← Finset.sum_coe_sort Eᶜ]
    calc (∑ i : (↑(Eᶜ) : Type _), y_pad i.1 * ((1 + ε) • f) i.1)
        = ∑ i : (↑(Eᶜ) : Type _), (1 + ε) * (y i * v i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [y_pad, dif_pos i.2, Pi.smul_apply, smul_eq_mul, hf i]
          ring
      _ = (1 + ε) * ∑ i : (↑(Eᶜ) : Type _), y i * v i := (Finset.mul_sum _ _ _).symm
      _ = (1 + ε) * S45.qform S v := by rw [hy_dot]
  have hfen := AgentS45.DupComparison.qform_fenchel D0 hD0 y_pad hy_pad ((1 + ε) • f)
  rw [hpair, AgentS45.DupComparison.qform_smul'] at hfen
  have hlo := (htrans y hy).1
  change S45.dualForm (S45.qform D0) y_pad / (1 + ε) ≤ S45.dualForm (S45.qform S) y at hlo
  rw [hdual_eq, div_le_iff₀ (by linarith [hε.1])] at hlo
  have hcomb : 2 * ((1 + ε) * S45.qform S v) - (1 + ε) ^ 2 * S45.qform D0 f ≤
      S45.qform S v * (1 + ε) := hfen.trans hlo
  have h1ε_pos : 0 < 1 + ε := by linarith [hε.1]
  nlinarith

theorem l2sq_transpose_mulVec_le_dualForm {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (D : S45.RMat ι) (hD : S45.constantKernel D) (B : Matrix ι (Fin h) ℝ) (K : ℝ)
    (hK : 0 < K) (hB : ∀ w : Fin h → ℝ, S45.qform D (B *ᵥ w) ≤ K * S45.l2sq w)
    (y : ι → ℝ) (hy : S45.neutral y) :
    S45.l2sq (Bᵀ *ᵥ y) ≤ K * S45.dualForm (S45.qform D) y := by
  let w : Fin h → ℝ := Bᵀ *ᵥ y
  let g : ι → ℝ := K⁻¹ • (B *ᵥ w)
  have hpair : (∑ i : ι, y i * g i) = K⁻¹ * S45.l2sq w := by
    calc (∑ i : ι, y i * g i)
        = K⁻¹ * dotProduct y (B *ᵥ w) := by
          simp only [g, Pi.smul_apply, smul_eq_mul, dotProduct]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = K⁻¹ * dotProduct w (Bᵀ *ᵥ y) := by
          rw [← Matrix.dotProduct_transpose_mulVec B w y]
      _ = K⁻¹ * S45.l2sq w := by
          congr 1
          change dotProduct w w = S45.l2sq w
          simp [dotProduct, S45.l2sq, Real.norm_eq_abs, pow_two]
  have hqg : S45.qform D g ≤ K⁻¹ * S45.l2sq w := by
    rw [AgentS45.DupComparison.qform_smul']
    calc (K⁻¹) ^ 2 * S45.qform D (B *ᵥ w)
        ≤ (K⁻¹) ^ 2 * (K * S45.l2sq w) :=
          mul_le_mul_of_nonneg_left (hB w) (sq_nonneg _)
      _ = K⁻¹ * S45.l2sq w := by field_simp [hK.ne']
  have hfen := AgentS45.DupComparison.qform_fenchel D hD y hy g
  rw [hpair] at hfen
  have hle : K⁻¹ * S45.l2sq w ≤ S45.dualForm (S45.qform D) y := by linarith
  calc S45.l2sq w = K * (K⁻¹ * S45.l2sq w) := by field_simp [hK.ne']
    _ ≤ K * S45.dualForm (S45.qform D) y := mul_le_mul_of_nonneg_left hle hK.le

theorem reserve_port_mem_live_of_bit_pivots {d m : ℕ} {C : ℝ}
    (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (hx : TileGoodCore C P j T x) {q : S45.Sequence (Port d m)}
    (hq_wf : q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r))
    (hq0 : q.state 0 = x.sweep.state 0)
    (hbit : ∀ s < q.length, ∀ z, q.pivot s = some z → z.2 = false) :
    ∀ s ≤ q.length, ∀ a : {i // i ∈ x.endpoint.active},
      ((a.1, true) : Port d m) ∈ (q.state s).live := by
  intro s
  induction s with
  | zero =>
    intro _ a
    let p : Port d m := (a.1, true)
    change p ∈ (q.state 0).live
    rw [hq0, start_live_mem P j T x hx p]
    exact a.2
  | succ s ih =>
    intro hs a
    let p : Port d m := (a.1, true)
    have ih_s : p ∈ (q.state s).live := ih (Nat.le_of_succ_le hs) a
    have hstep := hq_wf.2 s (Nat.lt_of_succ_le hs)
    rcases hpiv : q.pivot s with _ | z
    · rw [hpiv] at hstep
      change p ∈ (q.state (s + 1)).live
      rw [hstep]
      exact ih_s
    · rw [hpiv] at hstep
      change p ∈ (q.state (s + 1)).live
      rw [hstep.survivors, Finset.mem_erase]
      refine ⟨?_, ih_s⟩
      intro heq
      have hz2 : z.2 = false := hbit s (Nat.lt_of_succ_le hs) z hpiv
      have h2 : p.2 = z.2 := congrArg Prod.snd heq
      simp [p, hz2] at h2

theorem inv_card_live_le_of_bit_pivots {d m : ℕ} {C : ℝ}
    (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (hx : TileGoodCore C P j T x) {q : S45.Sequence (Port d m)}
    (hq_wf : q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r))
    (hq0 : q.state 0 = x.sweep.state 0)
    (hbit : ∀ s < q.length, ∀ z, q.pivot s = some z → z.2 = false)
    {s : ℕ} (hs : s ≤ q.length) {u0 : Port d m} (hu0 : u0 ∈ (q.state s).live) :
    1 / (Fintype.card (q.state s).live : ℝ) ≤
      2 * C * S45.power (sweepScale P.u m j) (1 + S45.delta + S45.kappa) := by
  obtain ⟨Λplus0, Wstar0, hpre0, _⟩ := hx.start_prestate
  have hvol0 := hpre0.volume
  let inj : {i // i ∈ x.endpoint.active} → (q.state s).live := fun a =>
    ⟨(a.1, true), reserve_port_mem_live_of_bit_pivots P j T x hx hq_wf hq0 hbit s hs a⟩
  have hinj : Function.Injective inj := by
    intro a b hab
    exact Subtype.ext (Prod.mk.inj (Subtype.mk.inj hab)).1
  have hle_card : Fintype.card {i // i ∈ x.endpoint.active} ≤ Fintype.card (q.state s).live :=
    Fintype.card_le_of_injective inj hinj
  have hinit_card : Fintype.card (S45.initialPorts {i // i ∈ x.endpoint.active}) =
      2 * Fintype.card {i // i ∈ x.endpoint.active} := by
    change Fintype.card ({i // i ∈ x.endpoint.active} × Bool) = _
    rw [Fintype.card_prod, Fintype.card_bool, mul_comm]
  have hu0_start : u0 ∈ (x.sweep.state 0).live :=
    live_mem_start x hq_wf hq0 hs hu0
  have hu0_act : u0.1 ∈ x.endpoint.active :=
    (start_live_mem P j T x hx u0).mp hu0_start
  have hact_pos : 0 < Fintype.card {i // i ∈ x.endpoint.active} :=
    Fintype.card_pos_iff.mpr ⟨⟨u0.1, hu0_act⟩⟩
  have hlive_pos : 0 < (Fintype.card (q.state s).live : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hact_pos hle_card
  have hinit_pos : 0 < (Fintype.card (S45.initialPorts {i // i ∈ x.endpoint.active}) : ℝ) := by
    rw [hinit_card]
    exact_mod_cast Nat.mul_pos (by decide) hact_pos
  have hinit_le : (Fintype.card (S45.initialPorts {i // i ∈ x.endpoint.active}) : ℝ) ≤
      2 * (Fintype.card (q.state s).live : ℝ) := by
    rw [hinit_card]
    exact_mod_cast Nat.mul_le_mul_left 2 hle_card
  have hdiv : 1 / (Fintype.card (q.state s).live : ℝ) ≤
      2 * (1 / (Fintype.card (S45.initialPorts {i // i ∈ x.endpoint.active}) : ℝ)) := by
    rw [mul_one_div, div_le_div_iff₀ hlive_pos hinit_pos]
    linarith
  linarith

theorem restrictLive_start_ambient_eq {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (q : S45.Sequence P_port) (r : P_port → ℂ) :
    (((q.restrictLive (q.state 0).live).state 0).ambient
      (S45.restrictDamping (q.state 0).live r)) = (q.state 0).state r := by
  have hlive0 : ((q.restrictLive (q.state 0).live).state 0).live = Finset.univ :=
    S45.Sequence.restrictLive_start q (q.state 0).live rfl
  apply state_ext
  · ext a b
    have ha : a ∈ ((q.restrictLive (q.state 0).live).state 0).live := hlive0 ▸ Finset.mem_univ a
    have hb : b ∈ ((q.restrictLive (q.state 0).live).state 0).live := hlive0 ▸ Finset.mem_univ b
    change S45.mask ((q.restrictLive (q.state 0).live).state 0).live
      ((q.restrictLive (q.state 0).live).state 0).g a b = _
    simp only [S45.mask, S45.pad, ha, hb, ↓reduceDIte]
    rfl
  · ext a; rfl

abbrev seqStartEquiv {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (hx : TileGoodCore C P j T x)
    {q : S45.Sequence (Port d m)} (hq0 : q.state 0 = x.sweep.state 0) :
    (q.state 0).live ≃ S45.initialPorts {i // i ∈ x.endpoint.active} :=
  activeLiveEquiv x (q.state 0).live (fun p => by
    rw [hq0]; exact start_live_mem P j T x hx p)

theorem seq_start_state_eq_reindex {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (hx : TileGoodCore C P j T x)
    {q : S45.Sequence (Port d m)} (hq0 : q.state 0 = x.sweep.state 0) :
    (q.state 0).state (portR (sweepTheta P.u m j) x.r) =
      AgentS45.State.reindex (seqStartEquiv P j T x hx hq0) (stageStartV3 P j x) := by
  have hg : (q.state 0).g = (sweepStartLiveState (sweepTheta P.u m j) x).g := by
    rw [hq0, hx.start_live]
  apply state_ext
  · ext a b
    change (q.state 0).g a.1 b.1 = _
    rw [hg]
    rfl
  · ext a
    rfl

theorem matrix_eq_of_offDiag_and_mulVec_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M1 M2 : Matrix ι ι ℝ) (h1 : M1 *ᵥ (fun _ => 1) = 0) (h2 : M2 *ᵥ (fun _ => 1) = 0)
    (hoff : ∀ a b : ι, a ≠ b → M1 a b = M2 a b) : M1 = M2 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    have hr1 : M1 a a + ∑ j ∈ Finset.univ.erase a, M1 a j = 0 := by
      have h := congrFun h1 a
      simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] at h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
      exact h
    have hr2 : M2 a a + ∑ j ∈ Finset.univ.erase a, M2 a j = 0 := by
      have h := congrFun h2 a
      simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] at h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
      exact h
    have hsum : (∑ j ∈ Finset.univ.erase a, M1 a j) = ∑ j ∈ Finset.univ.erase a, M2 a j :=
      Finset.sum_congr rfl fun j hj => hoff a j (Finset.ne_of_mem_erase hj).symm
    linarith
  · exact hoff a b hab

theorem restrictLive_stepL_offDiag {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (q : S45.Sequence P_port) (S : Finset P_port) (t : ℝ) (r : P_port → ℂ)
    (hpiv : ∀ k < q.length, ∀ p, q.pivot k = some p → p ∈ S)
    (k : ℕ) (hk : k < q.length) (a b : S) (hab : a ≠ b) :
    q.stepL t r k a.1 b.1 =
      (q.restrictLive S).stepL t (S45.restrictDamping S r) k a b := by
  have hab1 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  cases hq : q.pivot k with
  | none =>
    simp [S45.Sequence.stepL, hq]
  | some x =>
    have hxS : x ∈ S := hpiv k hk x hq
    have hqs : (q.restrictLive S).pivot k = some ⟨x, hxS⟩ := by
      simp [S45.Sequence.restrictLive, hq, hxS]
    simp only [S45.Sequence.stepL, hq, hqs]
    change S45.mask (q.state (k + 1)).live (S45.Linc t ((q.state k).ambient r) x (q.scalar k)) a.1 b.1 =
      S45.mask ((q.restrictLive S).state (k + 1)).live
        (S45.Linc t (((q.restrictLive S).state k).ambient (S45.restrictDamping S r)) ⟨x, hxS⟩ (q.scalar k)) a b
    by_cases ha : a ∈ ((q.restrictLive S).state (k + 1)).live
    · have haP : a.1 ∈ (q.state (k + 1)).live :=
        (S45.LiveState.mem_restrictLive S (q.state (k + 1)) a).mp ha
      by_cases hb : b ∈ ((q.restrictLive S).state (k + 1)).live
      · have hbP : b.1 ∈ (q.state (k + 1)).live :=
          (S45.LiveState.mem_restrictLive S (q.state (k + 1)) b).mp hb
        simp only [S45.mask, S45.pad, ha, hb, haP, hbP, ↓reduceDIte, S45.restrict, submatrix_apply]
        by_cases hpa : a.1 ∈ S45.survivors x
        · have hpa' : a ∈ S45.survivors ⟨x, hxS⟩ :=
            (S45.Sequence.surv_mem_restrictLive S x hxS a).mpr hpa
          by_cases hpb : b.1 ∈ S45.survivors x
          · have hpb' : b ∈ S45.survivors ⟨x, hxS⟩ :=
              (S45.Sequence.surv_mem_restrictLive S x hxS b).mpr hpb
            have hne1 : (⟨a.1, hpa⟩ : S45.survivors x) ≠ ⟨b.1, hpb⟩ :=
              fun h => hab1 (Subtype.mk.inj h)
            have hne2 : (⟨a, hpa'⟩ : S45.survivors ⟨x, hxS⟩) ≠ ⟨b, hpb'⟩ :=
              fun h => hab (Subtype.mk.inj h)
            simp only [S45.Linc, S45.pad, hpa, hpb, hpa', hpb', ↓reduceDIte,
              S45.laplacian, hne1, hne2, ↓reduceIte, neg_inj]
            have hγ := S45.Sequence.gamma_restrictLive q S t r k x hxS (q.scalar k)
            have hh_ab := S45.LiveState.ambient_h_restrictLive S (q.state k) r t a b
            have hh_ax := S45.LiveState.ambient_h_restrictLive S (q.state k) r t a ⟨x, hxS⟩
            have hh_xb := S45.LiveState.ambient_h_restrictLive S (q.state k) r t ⟨x, hxS⟩ b
            have hF_ax := S45.LiveState.ambient_F_restrictLive S (q.state k) r t a ⟨x, hxS⟩
            have hF_xb := S45.LiveState.ambient_F_restrictLive S (q.state k) r t ⟨x, hxS⟩ b
            have hF_xx := S45.LiveState.ambient_F_restrictLive S (q.state k) r t ⟨x, hxS⟩ ⟨x, hxS⟩
            have hq_xx : (((q.state k).restrictLive S).ambient (S45.restrictDamping S r)).q ⟨x, hxS⟩ =
                ((q.state k).ambient r).q x := by
              change ((((q.state k).restrictLive S).ambient (S45.restrictDamping S r)).g ⟨x, hxS⟩ ⟨x, hxS⟩).im =
                (((q.state k).ambient r).g x x).im
              rw [S45.LiveState.restrictLive_ambient_g S (q.state k) r ⟨x, hxS⟩ ⟨x, hxS⟩]
            rw [S45.Sequence.restrictLive_state_eq S q k] at hγ ⊢
            simp only [S45.Ledge, S45.LiveState.ambient_p_restrictLive,
              hγ, hh_ab, hh_ax, hh_xb, hF_ax, hF_xb, hF_xx, hq_xx]
          · have hpb' : b ∉ S45.survivors ⟨x, hxS⟩ :=
              fun h => hpb ((S45.Sequence.surv_mem_restrictLive S x hxS b).mp h)
            simp [S45.Linc, S45.pad, hpa, hpb, hpa', hpb']
        · have hpa' : a ∉ S45.survivors ⟨x, hxS⟩ :=
            fun h => hpa ((S45.Sequence.surv_mem_restrictLive S x hxS a).mp h)
          simp [S45.Linc, S45.pad, hpa, hpa']
      · have hbP : b.1 ∉ (q.state (k + 1)).live :=
          fun h => hb ((S45.LiveState.mem_restrictLive S (q.state (k + 1)) b).mpr h)
        simp [S45.mask, S45.pad, ha, hb, haP, hbP]
    · have haP : a.1 ∉ (q.state (k + 1)).live :=
        fun h => ha ((S45.LiveState.mem_restrictLive S (q.state (k + 1)) a).mpr h)
      simp [S45.mask, S45.pad, ha, haP]

theorem Lrecord_restrictLive_eq {P_port : Type} [Fintype P_port] [DecidableEq P_port]
    (q : S45.Sequence P_port) (t : ℝ) (r : P_port → ℂ)
    (hq_wf : q.wellFormed t r)
    (hsym : ∀ k ≤ q.length, ((q.state k).state r).g.IsSymm) :
    let S := (q.state 0).live
    let r' := S45.restrictDamping S r
    let q' := q.restrictLive S
    S45.restrict (q.Lrecord t r (Finset.range q.length)) S =
      q'.Lrecord t r' (Finset.range q.length) := by
  classical
  set S := (q.state 0).live
  set r' := S45.restrictDamping S r
  set q' := q.restrictLive S
  have hpivS : ∀ k < q.length, ∀ p, q.pivot k = some p → p ∈ S := fun k hk p hp =>
    wellFormed_live_antitone hq_wf (Nat.zero_le k) hk.le (wellFormed_pivot_mem_live hq_wf hk hp).1
  have hq'wf : q'.wellFormed t r' := S45.Sequence.wellFormed_restrictLive q S hq_wf hpivS
  have hsym' : ∀ k ≤ q'.length, ((q'.state k).state r').g.IsSymm := fun k hk =>
    S45.LiveState.restrictLive_state_symm S (q.state k) r (hsym k hk)
  have hstepL_q := AgentS45.stepLLaplacian_proof P_port q t r hq_wf hsym
  have hstepL_q' := AgentS45.stepLLaplacian_proof (↑S : Type) q' t r' hq'wf hsym'
  have hmul1 : S45.restrict (q.Lrecord t r (Finset.range q.length)) S *ᵥ (fun _ => 1) = 0 := by
    ext a
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply, S45.restrict, submatrix_apply]
    have hsum : (∑ b : S, q.Lrecord t r (Finset.range q.length) a.1 b.1) =
        ∑ p : P_port, q.Lrecord t r (Finset.range q.length) a.1 p := by
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun p _ hp =>
          Lrecord_supported hq_wf (Finset.range q.length) subset_rfl a.1 p (Or.inr hp)),
        ← Finset.sum_coe_sort S]
    rw [hsum]
    have h0 : (q.Lrecord t r (Finset.range q.length) *ᵥ (fun _ => 1)) a.1 = 0 := by
      have hvec : q.Lrecord t r (Finset.range q.length) *ᵥ (fun _ => 1) = 0 := by
        unfold S45.Sequence.Lrecord
        rw [Matrix.sum_mulVec]
        exact Finset.sum_eq_zero fun k hk => (hstepL_q k (Finset.mem_range.mp hk)).2
      exact congrFun hvec a.1
    simpa [Matrix.mulVec, dotProduct] using h0
  have hmul2 : q'.Lrecord t r' (Finset.range q.length) *ᵥ (fun _ => 1) = 0 := by
    unfold S45.Sequence.Lrecord
    rw [Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun k hk => (hstepL_q' k (Finset.mem_range.mp hk)).2
  refine matrix_eq_of_offDiag_and_mulVec_one _ _ hmul1 hmul2 (fun a b hab => ?_)
  simp only [S45.restrict, submatrix_apply, S45.Sequence.Lrecord, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun k hk =>
    restrictLive_stepL_offDiag q S t r hpivS k (Finset.mem_range.mp hk) a b hab

theorem qform_Lrecord_and_s0_D {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (hx : TileGoodCore C P j T x)
    {q : S45.Sequence (Port d m)} (htpos : 0 < sweepScale P.u m j)
    (hq_wf : q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r))
    (hq0 : q.state 0 = x.sweep.state 0)
    (hq_val : q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (stageD0 P j x) q.length) :
    S45.formAbsLe
      (S45.qform ((q.restrictLive (q.state 0).live).Lrecord (sweepScale P.u m j)
        (S45.restrictDamping (q.state 0).live (portR (sweepTheta P.u m j) x.r))
        (Finset.range q.length)))
      (S45.qform (((q.state 0).state (portR (sweepTheta P.u m j) x.r)).D (sweepScale P.u m j)))
      (S45.power (sweepScale P.u m j) (S45.delta / 10)) := by
  classical
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set S := (q.state 0).live
  set r' := S45.restrictDamping S r
  set q' := q.restrictLive S
  intro f
  have hsw0 := start_state_isSymm_ward P j T x hq0 hx
  have hsym : ∀ k ≤ q.length, ((q.state k).state r).g.IsSymm :=
    fun k hk => (wellFormed_symm_ward htpos hq_wf hsw0.1 hsw0.2 k hk).1
  let f_ext : Port d m → ℝ := fun p => if hp : p ∈ S then f ⟨p, hp⟩ else 0
  have hL_eq : S45.qform (q.Lrecord t r (Finset.range q.length)) f_ext =
      S45.qform (q'.Lrecord t r' (Finset.range q.length)) f := by
    have hrec := Lrecord_restrictLive_eq q t r hq_wf hsym
    have h1 := qform_of_support_equiv S (Equiv.refl S)
      (q.Lrecord t r (Finset.range q.length)) (q'.Lrecord t r' (Finset.range q.length))
      (fun i k hi hk => congrFun (congrFun hrec ⟨i, hi⟩) ⟨k, hk⟩)
      (fun i k hik => Lrecord_supported hq_wf (Finset.range q.length) subset_rfl i k hik)
      f_ext
    rw [h1]
    congr 1; ext a; simp [f_ext, a.2]
  have hD_eq : S45.qform (stageD0 P j x) f_ext =
      S45.qform (((q.state 0).state r).D t) f := by
    have hstage : stageD0 P j x = ((q.state 0).ambient r).D t := by
      change ((x.sweep.state 0).ambient r).D t = _
      rw [hq0]
    rw [hstage]
    have h1 := qform_of_support_equiv S (Equiv.refl S)
      (((q.state 0).ambient r).D t) (((q.state 0).state r).D t)
      (fun i k hi hk => ambient_D_live (q.state 0) r t hi hk)
      (fun i k hik => ambient_D_dead (q.state 0) r t hik)
      f_ext
    rw [h1]
    congr 1; ext a; simp [f_ext, a.2]
  rw [← hL_eq, ← hD_eq]
  exact hq_val.2.1 f_ext

theorem qform_s0_D_localB_le {d m : ℕ} {C : ℝ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (hx : TileGoodCore C P j T x)
    {q : S45.Sequence (Port d m)} (hq0 : q.state 0 = x.sweep.state 0)
    (w : Fin (localDim P j T) → ℝ) :
    S45.qform (((q.state 0).state (portR (sweepTheta P.u m j) x.r)).D (sweepScale P.u m j))
      (fun a : (q.state 0).live => (((P.cover j).cover.coords T).B *ᵥ w) a.1) ≤
      C ^ 2 * S45.l2sq w := by
  classical
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set S := (q.state 0).live
  set e0 := seqStartEquiv P j T x hx hq0
  set s3 := stageStartV3 P j x
  let f_full : Port d m → ℝ := ((P.cover j).cover.coords T).B *ᵥ w
  let f_S : S → ℝ := fun a => f_full a.1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hx.one_le
  have hb : 0 < (P.cover j).b := hx.cover_b.1
  have : Nonempty (Port d m) := ⟨(site₀ d m, false)⟩
  have hE : ∀ v, 0 ≤ (P.cover j).cover.energy v := fun v =>
    AgentS45.cover_energy_nonneg (P.cover j).cover (TileCover_C_pos (P.cover j).cover) hb v
  have hD_sub : ((q.state 0).state r).D t = (s3.D t).submatrix e0 e0 := by
    rw [seq_start_state_eq_reindex P j T x hx hq0, AgentS45.State.reindex_D]
  have hq_eq : S45.qform (((q.state 0).state r).D t) f_S =
      S45.qform (s3.D t) (f_S ∘ e0.symm) := by
    rw [hD_sub, AgentS45.qform_submatrix]
  change S45.qform (((q.state 0).state r).D t) f_S ≤ C ^ 2 * S45.l2sq w
  rw [hq_eq]
  set site' := fun p => (P.cover j).cover.site (activePort x p)
  have hcomp := (hx.start_comparison (f_S ∘ e0.symm)).2
  obtain ⟨α, v, hsplit, hbound⟩ := (P.cover j).cover.local_split T w
  let α' : S45.initialPorts {i // i ∈ x.endpoint.active} → ℝ := fun a => α (activePort x a)
  have hsplit' : ∀ a, (f_S ∘ e0.symm) a = α' a + v (site' a) := fun a => hsplit (activePort x a)
  have hl2_α' : S45.l2sq α' ≤ S45.l2sq α := by
    unfold S45.l2sq
    have hsum : (∑ a : S45.initialPorts {i // i ∈ x.endpoint.active}, ‖α' a‖ ^ 2) =
        ∑ z : S, ‖α z.1‖ ^ 2 :=
      Fintype.sum_equiv e0.symm _ _ (fun _ => rfl)
    rw [hsum, ← Finset.sum_subtype S (by intro i; rfl) (fun i => ‖α i‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => sq_nonneg _)
  have hsp_le : S45.spatialEnergy site' (P.cover j).b (P.cover j).cover.energy (f_S ∘ e0.symm) ≤
      S45.l2sq α' + (P.cover j).cover.energy v / (P.cover j).b := by
    unfold S45.spatialEnergy
    refine csInf_le ⟨0, ?_⟩ ⟨α', v, hsplit', rfl⟩
    rintro a ⟨α0, v0, -, rfl⟩
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (div_nonneg (hE v0) hb.le)
  have hsp_C : S45.spatialEnergy site' (P.cover j).b (P.cover j).cover.energy (f_S ∘ e0.symm) ≤
      C * S45.l2sq w := by
    calc S45.spatialEnergy site' (P.cover j).b (P.cover j).cover.energy (f_S ∘ e0.symm)
        ≤ S45.l2sq α' + (P.cover j).cover.energy v / (P.cover j).b := hsp_le
      _ ≤ S45.l2sq α + (P.cover j).cover.energy v / (P.cover j).b :=
          add_le_add_left hl2_α' _
      _ ≤ (P.cover j).C * S45.l2sq w := hbound
      _ ≤ C * S45.l2sq w :=
          mul_le_mul_of_nonneg_right hx.cover_C (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc S45.qform (s3.D t) (f_S ∘ e0.symm)
      ≤ C * S45.spatialEnergy site' (P.cover j).b (P.cover j).cover.energy (f_S ∘ e0.symm) := hcomp
    _ ≤ C * (C * S45.l2sq w) := mul_le_mul_of_nonneg_left hsp_C hCpos.le
    _ = C ^ 2 * S45.l2sq w := by ring

theorem shellBounds_subtype {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} {C : ℝ}
    {dist : ι → ι → ℝ} (hs : S45.ShellBounds d C dist) (L : Finset ι) :
    S45.ShellBounds d C (fun i j : L => dist i.1 j.1) := by
  refine ⟨fun i j => hs.nonneg _ _, fun i j => hs.symmetric _ _,
    fun i j k => hs.triangle _ _ _, fun i => hs.self _, ?_, ?_⟩
  · intro u hu hu1 i
    rw [← Finset.sum_subtype L (by intro j; rfl) (fun j => Real.exp (-u * dist i.1 j))]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
      (fun _ _ _ => Real.exp_nonneg _)).trans (hs.count u hu hu1 i.1)
  · intro u hu hu1 i
    rw [← Finset.sum_subtype L (by intro j; rfl)
      (fun j => dist i.1 j ^ 2 * Real.exp (-u * dist i.1 j))]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
      (fun _ _ _ => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))).trans
        (hs.second u hu hu1 i.1)

theorem sum_pad_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (E : Finset β) (Φ : α ≃ (↑(Eᶜ) : Type _)) (f : β → ℝ) (y : α → ℝ)
    (hf : ∀ b : β, f b = if hb : b ∈ Eᶜ then y (Φ.symm ⟨b, hb⟩) else 0) :
    (∑ b : β, f b) = ∑ a : α, y a := by
  have h1 : (∑ b : β, f b) = ∑ b ∈ Eᶜ, f b :=
    (Finset.sum_subset (Finset.subset_univ Eᶜ)
      (fun b _ hb => by rw [hf b, dif_neg hb])).symm
  rw [h1, ← Finset.sum_coe_sort Eᶜ]
  have h2 : (∑ b : (↑(Eᶜ) : Type _), f b.1) = ∑ b : (↑(Eᶜ) : Type _), y (Φ.symm b) :=
    Finset.sum_congr rfl fun b _ => by rw [hf b.1, dif_pos b.2]
  rw [h2]
  exact Fintype.sum_equiv Φ.symm _ _ (fun _ => rfl)

set_option maxHeartbeats 1600000 in
theorem prestate_and_forms_of_slotSeq (d : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    let C_pre : ℝ := 4 * C
    ∃ C_row > 0, ∃ t0_pre > 0, t0_pre ≤ 1 ∧
      ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
        (M : ℕ → ℕ) (x : RunRecord d m),
        P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 →
        TileGoodCore C P j T x → sweepScale P.u m j < t0_pre →
        ∀ (k : ℕ) (ω : RandomSources (Torus d m) M) (q : S45.Sequence (Port d m)),
          slotSeq P j T M x k ω = some q →
          ∀ {u0 : Port d m}, u0 ∈ (q.state q.length).live →
          let t := sweepScale P.u m j
          let r := portR (sweepTheta P.u m j) x.r
          let L_curr := (q.state q.length).live
          let sk := (q.state q.length).state r
          let B_live : Matrix L_curr (Fin (localDim P j T)) ℝ :=
            fun a j_col => ((P.cover j).cover.coords T).B a.1 j_col
          let Wstar_live : S45.Form L_curr := fun y =>
            S45.l2sq y + C_pre * t * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3)
          ∃ Λplus_live : S45.Form L_curr,
            S45.Prestate t C_pre Λplus_live Wstar_live sk ∧
            S45.rowNorm (sk.P t) ≤ C_row * S45.logFactor t ∧
            (∀ v : Fin (localDim P j T) → ℝ,
              S45.qform (sk.D t) (B_live *ᵥ v) ≤ 2 * C ^ 2 * S45.l2sq v) ∧
            (∀ y : L_curr → ℝ, S45.neutral y →
              S45.l2sq (B_liveᵀ *ᵥ y) ≤ 2 * C ^ 4 * (1 + 4 * C) * Wstar_live y) := by
  intro C_pre
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCpre_ge : C ≤ C_pre := by dsimp [C_pre]; linarith
  have hCpre_pos : 0 < C_pre := lt_of_lt_of_le hCpos hCpre_ge
  let B_inv : ℝ := 2 * (1 + C ^ 2)
  have hB_inv : 1 ≤ B_inv := by dsimp [B_inv]; nlinarith
  have hCB_inv : C ≤ B_inv := by dsimp [B_inv]; nlinarith
  have hB_inv_pos : 0 < B_inv := lt_of_lt_of_le zero_lt_one hB_inv
  obtain ⟨t0_schur, ht0_schur, ht0_schur_le, hschur⟩ := exists_schur_den_scale C hC
  obtain ⟨C_row, hC_row, _, _, t0_inv, ht0_inv, hinv_row⟩ :=
    inverse_row_fintype_with_rowNorm d B_inv (1 / 2) S45.beta hB_inv
      (by norm_num) (by norm_num) (by norm_num [S45.beta, S45.delta])
  obtain ⟨t1, ht1, hpow1⟩ := AgentS45.power_small (e := S45.delta / 10)
    (by norm_num [S45.delta]) (a := 1 / 6) (by norm_num)
  obtain ⟨t2, ht2, hpow2⟩ := AgentS45.power_small (e := S45.kappa)
    (by norm_num [S45.kappa, S45.delta]) (a := 1 / 2) (by norm_num)
  let t0_pre : ℝ := min t0_schur (min t0_inv (min t1 t2))
  have ht0_pre : 0 < t0_pre := lt_min ht0_schur (lt_min ht0_inv (lt_min ht1 ht2))
  have ht0_pre_le : t0_pre ≤ 1 := (min_le_left _ _).trans ht0_schur_le
  refine ⟨C_row, hC_row, t0_pre, ht0_pre, ht0_pre_le, ?_⟩
  intro m P j T M x hu _hj _hjm hx htt k ω q hq u0 hu0
  classical
  have hu_pos : 0 < P.u := lt_trans (by norm_num) hu.1
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set S := (q.state 0).live
  set L_curr := (q.state q.length).live
  set sk := (q.state q.length).state r
  set B_live : Matrix L_curr (Fin (localDim P j T)) ℝ :=
    fun a j_col => ((P.cover j).cover.coords T).B a.1 j_col
  set Wstar_live : S45.Form L_curr := fun y =>
    S45.l2sq y + C_pre * t * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3)
  have htpos : 0 < t := sweepScale_pos_a2 hu_pos m j
  have htt_schur : t < t0_schur := lt_of_lt_of_le htt (min_le_left _ _)
  have htt_inv : t < t0_inv :=
    lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt1 : t < t1 :=
    lt_of_lt_of_le htt ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htt2 : t < t2 :=
    lt_of_lt_of_le htt ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ht_lt_one : t < 1 := lt_of_lt_of_le htt ht0_pre_le
  have ht_le_one : t ≤ 1 := ht_lt_one.le
  have inv := slotSeq_inv P j T M x hx ω k q hq
  have hq_wf := inv.wellFormed
  have hq0 := inv.state_prefix 0 (Nat.zero_le _)
  have hq_val := inv.valid q.length le_rfl
  have hbit_q : ∀ s < q.length, ∀ z, q.pivot s = some z → z.2 = false := by
    intro s hs z hpz
    by_cases hs0 : s < x.sweep.length
    · rw [inv.pivot_prefix s hs0] at hpz
      exact hx.bit_pivots s hs0 z hpz
    · obtain ⟨l, _, _, hpiv_l, _⟩ := inv.trial_step s (Nat.le_of_not_lt hs0) hs
      rw [hpz] at hpiv_l
      injection hpiv_l with hz
      rw [hz]
  have hsw0 := start_state_isSymm_ward P j T x hq0 hx
  have hsw := wellFormed_symm_ward htpos hq_wf hsw0.1 hsw0.2
  have hpsb := prefix_schur_and_bounds P j T x hx hq_wf hq0 inv.valid
    ht0_schur_le hschur htpos htt_schur
  have hbroad_S : ∀ p ∈ S, ‖r p‖ ≤ C ∧ 1 / C ≤ (r p).im ∧ (r p).im ≤ C :=
    fun p hp => start_broad P j T x hx (by rw [← hq0]; exact hp)
  have hsub : ∀ s ≤ q.length, (q.state s).live ⊆ S :=
    fun s hs => wellFormed_live_antitone hq_wf (Nat.zero_le s) hs
  have hpivS : ∀ s < q.length, ∀ p, q.pivot s = some p → p ∈ S := fun s hs p hp =>
    hsub s hs.le (wellFormed_pivot_mem_live hq_wf hs hp).1
  let r' : S → ℂ := S45.restrictDamping S r
  let q' := q.restrictLive S
  have hq'wf : q'.wellFormed t r' := S45.Sequence.wellFormed_restrictLive q S hq_wf hpivS
  have hq's : (q'.state 0).live = Finset.univ := S45.Sequence.restrictLive_start q S rfl
  have hp' : ∀ i : S, 0 < (r' i).im := fun i =>
    lt_of_lt_of_le (by positivity) (hbroad_S i.1 i.2).2.1
  have hstep : ∀ s < q.length,
      ((q.state s).state r).g.IsSymm ∧ ((q.state s).state r).ward t ∧
      ∀ p : (q.state s).live, 1 - ((q.state s).state r).K t p p ≠ 0 ∧
        0 < ((q.state s).state r).q p -
          ((q.state s).state r).p p * ((q.state s).state r).F t p p := by
    intro s hs
    obtain ⟨_, hpiv⟩ := hpsb s hs.le
    exact ⟨(hsw s hs.le).1, (hsw s hs.le).2, fun p => ⟨(hpiv p).2.1, (hpiv p).2.2⟩⟩
  have hstep' : ∀ s < q'.length, ((q'.state s).state r').g.IsSymm ∧
      ((q'.state s).state r').ward t ∧
      ∀ y : (q'.state s).live, 1 - ((q'.state s).state r').K t y y ≠ 0 ∧
        0 < ((q'.state s).state r').q y -
          ((q'.state s).state r').p y * ((q'.state s).state r').F t y y := by
    intro s hs
    obtain ⟨hsymm, hward, hK⟩ := hstep s hs
    have hsk : (q.state s).live ⊆ S := hsub s (le_of_lt hs)
    exact ⟨S45.LiveState.restrictLive_state_symm S (q.state s) r hsymm,
      S45.LiveState.restrictLive_state_ward S (q.state s) r t hsk hward,
      S45.Sequence.hstep_restrictLive q S t r s hsk hK⟩
  obtain ⟨hpadK, hpadD⟩ := AgentS45.cumulative_schur_proof q' t r' htpos hp' hq'wf hq's hstep'
  set s0 := (q.state 0).state r
  have hamb0_eq : (q'.state 0).ambient r' = s0 := restrictLive_start_ambient_eq q r
  set L'_curr := (q'.state q.length).live
  set E : Finset S := L'_currᶜ
  set J_S := q'.Jrecord t r' (Finset.range q.length)
  set L_S := q'.Lrecord t r' (Finset.range q.length)
  replace hpadK : S45.pad L'_curr (1 - ((q'.state q.length).state r').K t) =
      S45.pad L'_currᶜᶜ (S45.schur (1 - ((q'.state 0).ambient r').K t - J_S) E) := hpadK
  replace hpadD : S45.pad L'_curr (((q'.state q.length).state r').D t) =
      S45.pad L'_currᶜᶜ (S45.schur (((q'.state 0).ambient r').D t + L_S) E) := hpadD
  have hpadK' : S45.pad L'_curr (1 - ((q'.state q.length).state r').K t) =
      S45.pad L'_currᶜᶜ (S45.schur (1 - (s0.K t + J_S)) E) := by
    rw [hpadK, hamb0_eq, sub_sub]
  have hpadD' : S45.pad L'_curr (((q'.state q.length).state r').D t) =
      S45.pad L'_currᶜᶜ (S45.schur (s0.D t + L_S) E) := by
    rw [hpadD, hamb0_eq]
  have hsub_curr : L_curr ⊆ S := hsub q.length le_rfl
  let e_sub : L'_curr ≃ L_curr := S45.LiveState.subLiveEquiv S (q.state q.length) hsub_curr
  let Φ : L_curr ≃ (↑(Eᶜ) : Type _) := e_sub.symm.trans (complComplEquiv L'_curr)
  have hΦ_val (i : L_curr) : ((Φ i).1 : Port d m) = i.1 := rfl
  have hΦ_symm_val (a : (↑(Eᶜ) : Type _)) : ((Φ.symm a : L_curr) : Port d m) = (a.1 : Port d m) := rfl
  have hK_sub' := K_submatrix_of_pad_schur L'_curr (((q'.state q.length).state r').K t)
    (1 - (s0.K t + J_S)) hpadK'
  have hD_sub' := D_submatrix_of_pad_schur L'_curr (((q'.state q.length).state r').D t)
    (s0.D t + L_S) hpadD'
  have hq'_state_re : (q'.state q.length).state r' = AgentS45.State.reindex e_sub sk := by
    apply state_ext <;> rfl
  have hsk_K_sub : sk.K t = (1 - S45.schur (1 - (s0.K t + J_S)) E).submatrix Φ Φ := by
    have h1 : ((q'.state q.length).state r').K t = (sk.K t).submatrix e_sub e_sub := by
      rw [hq'_state_re, AgentS45.State.reindex_K]
    ext i j
    have h2 := congrFun (congrFun h1 (e_sub.symm i)) (e_sub.symm j)
    simp only [submatrix_apply, Equiv.apply_symm_apply] at h2
    rw [← h2, hK_sub']
    rfl
  have hsk_D_sub : sk.D t = (S45.schur (s0.D t + L_S) E).submatrix Φ Φ := by
    have h1 : ((q'.state q.length).state r').D t = (sk.D t).submatrix e_sub e_sub := by
      rw [hq'_state_re, AgentS45.State.reindex_D]
    ext i j
    have h2 := congrFun (congrFun h1 (e_sub.symm i)) (e_sub.symm j)
    simp only [submatrix_apply, Equiv.apply_symm_apply] at h2
    rw [← h2, hD_sub']
    rfl
  obtain ⟨Λplus0, Wstar0, hpre0, hK0_3, hΛ0_nn, hX0_comp⟩ := hx.start_prestate
  set e0 := seqStartEquiv P j T x hx hq0
  have hs0_re : s0 = AgentS45.State.reindex e0 (stageStartV3 P j x) :=
    seq_start_state_eq_reindex P j T x hx hq0
  have hs0_K : ‖s0.K t‖ ≤ 1 / 3 := by
    rw [hs0_re, AgentS45.State.reindex_K, AgentS45.norm_submatrix_equiv]
    exact hK0_3
  have hs0_D_sub : s0.D t = ((stageStartV3 P j x).D t).submatrix e0 e0 := by
    rw [hs0_re, AgentS45.State.reindex_D]
  have hs0_ker : S45.constantKernel (s0.D t) := by
    rw [hs0_D_sub]
    exact AgentS45.PrefixPrestate.constantKernel_submatrix e0 _ hpre0.kernel
  set ε := S45.power t (S45.delta / 10)
  set a_kap := S45.power t S45.kappa
  have hε0 : 0 ≤ ε := Real.rpow_nonneg htpos.le _
  have hε6 : ε < 1 / 6 := hpow1 t htpos htt1
  have ha2 : a_kap < 1 / 2 := hpow2 t htpos htt2
  have hεa : ε ≤ a_kap :=
    Real.rpow_le_rpow_of_exponent_ge htpos ht_le_one (by norm_num [S45.kappa, S45.delta])
  have hJ_norm : ‖J_S‖ ≤ ε := by
    have hJ_eq : ‖J_S‖ = ‖q.Jrecord t r (Finset.range q.length)‖ := by
      show ‖(q.restrictLive S).Jrecord t (S45.restrictDamping S r) (Finset.range q.length)‖ = _
      rw [← S45.Sequence.Jrecord_restrictLive q S t r hpivS (Finset.range q.length) subset_rfl]
      refine norm_submatrix_of_support (fun a : S => a.1) Subtype.val_injective _ ?_
      intro i l hil
      refine S45.Sequence.Jrecord_supported q S t r hq_wf rfl (Finset.range q.length) subset_rfl i l ?_
      rcases hil with hi | hl
      · exact Or.inl fun h => hi ⟨i, h⟩ rfl
      · exact Or.inr fun h => hl ⟨l, h⟩ rfl
    rw [hJ_eq]
    exact hq_val.1
  have hKJ_norm : ‖s0.K t + J_S‖ ≤ 1 / 3 + ε :=
    (norm_add_le _ _).trans (add_le_add hs0_K hJ_norm)
  have hcon := (AgentS45.schur_contraction_proof (s0.K t + J_S) E (1 / 3 + ε)
    ⟨by linarith, by linarith⟩ hKJ_norm).2
  have hKcap : ‖sk.K t‖ ≤ 1 / 2 := by
    rw [hsk_K_sub, AgentS45.norm_submatrix_equiv]
    linarith
  have hunit : IsUnit (1 - sk.K t) :=
    (Units.oneSub (sk.K t) (by linarith : ‖sk.K t‖ < 1)).isUnit
  have hsym_all : ∀ s ≤ q'.length, ((q'.state s).state r').g.IsSymm := fun s hs =>
    S45.LiveState.restrictLive_state_symm S (q.state s) r (hsw s hs).1
  have hstepL_q' := AgentS45.stepLLaplacian_proof (↑S : Type) q' t r' hq'wf hsym_all
  have hLS_sym : L_S.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    simp only [L_S, S45.Sequence.Lrecord, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun s hs => (hstepL_q' s (Finset.mem_range.mp hs)).1.apply a b
  have hLS_zero : L_S *ᵥ (fun _ => 1) = 0 := by
    dsimp [L_S]
    unfold S45.Sequence.Lrecord
    rw [Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun s hs => (hstepL_q' s (Finset.mem_range.mp hs)).2
  have hLS_cap : S45.formAbsLe (S45.qform L_S) (S45.qform (s0.D t)) ε :=
    qform_Lrecord_and_s0_D P j T x hx htpos hq_wf hq0 hq_val
  have hE_proper : E ≠ Finset.univ := by
    intro hE
    let a0 : S := (e_sub.symm ⟨u0, hu0⟩).1
    have ha0_live : a0 ∈ L'_curr := (e_sub.symm ⟨u0, hu0⟩).2
    have ha0_E : a0 ∈ E := by rw [hE]; exact Finset.mem_univ a0
    exact (Finset.mem_compl.mp ha0_E) ha0_live
  obtain ⟨hschur_ker, hschur_trans⟩ :=
    AgentS45.schur_dual_transport_proof (s0.D t) L_S E ε ⟨hε0, by linarith⟩
      hs0_ker hLS_sym hLS_zero hLS_cap hE_proper
  have hsk_ker : S45.constantKernel (sk.D t) := by
    rw [hsk_D_sub]
    exact AgentS45.PrefixPrestate.constantKernel_submatrix Φ _ hschur_ker
  let y_pad : (L_curr → ℝ) → (S → ℝ) :=
    fun y a => if ha : a ∈ Eᶜ then y (Φ.symm ⟨a, ha⟩) else 0
  let Λplus_live : S45.Form L_curr := fun y => Λplus0 (y_pad y ∘ e0.symm)
  have hy_pad_neutral : ∀ y : L_curr → ℝ, S45.neutral y → S45.neutral (y_pad y) := by
    intro y hy
    unfold S45.neutral at hy ⊢
    rw [sum_pad_equiv E Φ (y_pad y) y (fun _ => rfl)]
    exact hy
  have hy_e0_neutral : ∀ y : L_curr → ℝ, S45.neutral y → S45.neutral (y_pad y ∘ e0.symm) := by
    intro y hy
    unfold S45.neutral
    rw [← hy_pad_neutral y hy]
    exact Fintype.sum_equiv e0.symm _ _ (fun _ => rfl)
  have hy_e0_l1 : ∀ y : L_curr → ℝ, S45.l1 (y_pad y ∘ e0.symm) = S45.l1 y := by
    intro y
    unfold S45.l1
    rw [Fintype.sum_equiv e0.symm (fun u => ‖(y_pad y ∘ e0.symm) u‖)
      (fun a : S => ‖y_pad y a‖) (fun _ => rfl)]
    refine sum_pad_equiv E Φ (fun a => ‖y_pad y a‖) (fun i => ‖y i‖) (fun a => ?_)
    by_cases ha : a ∈ Eᶜ
    · simp only [y_pad, ha, ↓reduceDIte]
    · simp only [y_pad, ha, ↓reduceDIte, norm_zero]
  have hy_e0_l2sq : ∀ y : L_curr → ℝ, S45.l2sq (y_pad y ∘ e0.symm) = S45.l2sq y := by
    intro y
    unfold S45.l2sq
    rw [Fintype.sum_equiv e0.symm (fun u => ‖(y_pad y ∘ e0.symm) u‖ ^ 2)
      (fun a : S => ‖y_pad y a‖ ^ 2) (fun _ => rfl)]
    refine sum_pad_equiv E Φ (fun a => ‖y_pad y a‖ ^ 2) (fun i => ‖y i‖ ^ 2) (fun a => ?_)
    by_cases ha : a ∈ Eᶜ
    · simp only [y_pad, ha, ↓reduceDIte]
    · simp only [y_pad, ha, ↓reduceDIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
  have hy_e0_weighted : ∀ y : L_curr → ℝ,
      (∑ u : S45.initialPorts {i // i ∈ x.endpoint.active},
        (y_pad y ∘ e0.symm) u ^ 2 / (stageStartV3 P j x).p u ^ 2) =
      ∑ i : L_curr, y i ^ 2 / sk.p i ^ 2 := by
    intro y
    have h1 : (∑ u : S45.initialPorts {i // i ∈ x.endpoint.active},
        (y_pad y ∘ e0.symm) u ^ 2 / (stageStartV3 P j x).p u ^ 2) =
        ∑ a : S, (y_pad y a) ^ 2 / s0.p a ^ 2 := by
      refine Fintype.sum_equiv e0.symm _ _ (fun u => ?_)
      have hp_eq : (stageStartV3 P j x).p u = s0.p (e0.symm u) := by
        rw [hs0_re]
        change (stageStartV3 P j x).p u = (stageStartV3 P j x).p (e0 (e0.symm u))
        rw [Equiv.apply_symm_apply]
      rw [hp_eq]; rfl
    rw [h1]
    refine sum_pad_equiv E Φ (fun a => (y_pad y a) ^ 2 / s0.p a ^ 2)
      (fun i => y i ^ 2 / sk.p i ^ 2) (fun a => ?_)
    by_cases ha : a ∈ Eᶜ
    · simp only [y_pad, dif_pos ha]
      have hp_eq : s0.p a = sk.p (Φ.symm ⟨a, ha⟩) := rfl
      rw [hp_eq]
    · simp only [y_pad, ha, ↓reduceDIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div]
  have hΛ_fourier_C : ∀ y : L_curr → ℝ, S45.neutral y →
      Λplus_live y ≤ C * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) := by
    intro y hy
    have hf := hpre0.fourier (y_pad y ∘ e0.symm) (hy_e0_neutral y hy)
    rwa [hy_e0_l1 y, hy_e0_l2sq y] at hf
  have hsharp : ∀ y : L_curr → ℝ, S45.neutral y →
      sk.X t y ≤ (1 + C_pre * S45.power t S45.kappa) * (∑ i : L_curr, y i ^ 2 / sk.p i ^ 2) +
        C_pre * t * Λplus_live y := by
    intro y hy
    have hyΦ : S45.neutral (y ∘ Φ.symm) := by
      unfold S45.neutral at hy ⊢
      rw [← hy]
      exact Fintype.sum_equiv Φ.symm _ _ (fun _ => rfl)
    have hup := (hschur_trans (y ∘ Φ.symm) hyΦ).2
    change S45.dualForm (S45.qform (S45.schur (s0.D t + L_S) E)) (y ∘ Φ.symm) ≤
      S45.dualForm (S45.qform (s0.D t)) (y_pad y) / (1 - ε) at hup
    have hX_eq : sk.X t y =
        S45.dualForm (S45.qform (S45.schur (s0.D t + L_S) E)) (y ∘ Φ.symm) := by
      change S45.dualForm (S45.qform (sk.D t)) y = _
      rw [hsk_D_sub, AgentS45.dualForm_submatrix]
    have hX0_eq : S45.dualForm (S45.qform (s0.D t)) (y_pad y) =
        (stageStartV3 P j x).X t (y_pad y ∘ e0.symm) := by
      rw [hs0_D_sub, AgentS45.dualForm_submatrix]
      rfl
    have h0 := hX0_comp (y_pad y ∘ e0.symm) (hy_e0_neutral y hy)
    rw [hy_e0_weighted y] at h0
    have hX_le : sk.X t y ≤
        ((1 + a_kap) * (∑ i : L_curr, y i ^ 2 / sk.p i ^ 2) + C * t * Λplus_live y) / (1 - ε) := by
      rw [hX_eq]
      refine hup.trans (div_le_div_of_nonneg_right ?_ (by linarith))
      rw [hX0_eq]
      exact h0
    have hΛ_nn : 0 ≤ Λplus_live y := hΛ0_nn (y_pad y ∘ e0.symm) (hy_e0_neutral y hy)
    have hQ_nn : 0 ≤ ∑ i : L_curr, y i ^ 2 / sk.p i ^ 2 :=
      Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsc := AgentS45.PrefixPrestate.sharp_scalar hC htpos.le hQ_nn hΛ_nn hε0 hεa ha2.le hX_le
    simpa [C_pre, a_kap, mul_assoc] using hsc
  have hpre_sk : S45.Prestate t C_pre Λplus_live Wstar_live sk := {
    scale := ⟨htpos, ht_lt_one⟩
    broad := fun i => by
      have hb := hbroad_S i.1 (hsub_curr i.2)
      refine ⟨hb.1.trans hCpre_ge,
        (one_div_le_one_div_of_le hCpos hCpre_ge).trans hb.2.1,
        hb.2.2.trans hCpre_ge⟩
    symmetric := (hsw q.length le_rfl).1
    ward := (hsw q.length le_rfl).2
    K_cap := hKcap
    invertible := hunit
    kernel := hsk_ker
    row_cap := hq_val.2.2.1
    lag_cap := hq_val.2.2.2
    sharp := hsharp
    fourier := fun y hy => by
      refine (hΛ_fourier_C y hy).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCpre_ge
          (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) _))
        (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)
    dual_fourier := fun y _ => le_rfl
    volume := by
      have hvol2 := inv_card_live_le_of_bit_pivots P j T x hx hq_wf hq0 hbit_q le_rfl hu0
      refine hvol2.trans ?_
      have hpow_nn : 0 ≤ S45.power t (1 + S45.delta + S45.kappa) := Real.rpow_nonneg htpos.le _
      have h24 : 2 * C ≤ C_pre := by dsimp [C_pre]; linarith
      exact mul_le_mul_of_nonneg_right h24 hpow_nn
  }
  -- rowNorm bound via inverse_row_fintype_with_rowNorm
  let dist_live : L_curr → L_curr → ℝ := fun a b => (P.cover j).dist a.1 b.1
  have hshell_live : S45.ShellBounds d B_inv dist_live :=
    shellBounds_subtype (ShellBounds_mono hx.shell hCB_inv) L_curr
  have hp_live : ∀ i : L_curr, 1 / B_inv ≤ sk.p i ∧ sk.p i ≤ B_inv := fun i => by
    have hb := hbroad_S i.1 (hsub_curr i.2)
    exact ⟨(one_div_le_one_div_of_le hCpos hCB_inv).trans hb.2.1, hb.2.2.trans hCB_inv⟩
  have hward_vec : sk.F t *ᵥ sk.p = sk.q := by
    ext i
    simpa [S45.State.F, S45.entryAbsSquare, Matrix.mulVec, dotProduct, mul_comm] using
      AgentS45.ward_diag_row t sk (hsw q.length le_rfl).2 i
  have hqp_live : ∀ i : L_curr, |sk.q i - sk.p i| ≤ B_inv * S45.power t S45.beta := by
    intro i
    have hraw := ((hpsb q.length le_rfl).2 i).1
    have him : sk.q i - sk.p i = (sk.rawLag i).im := by
      simp [S45.State.q, S45.State.p, S45.State.rawLag]
    rw [him]
    exact (Complex.abs_im_le_norm _).trans hraw
  obtain ⟨hweak_q, hfar_q⟩ := hx.prefix_decay q hq_wf hq0 hbit_q q.length le_rfl hq_val
  have hcrude_live : ∀ a b : L_curr, ‖sk.h t a b‖ ≤ B_inv / Real.sqrt t := by
    intro a b
    have hw := hweak_q a b
    have hexp1 : Real.exp (-t ^ 3 * (P.cover j).dist a.1 b.1 / C) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hd_nn := hx.shell.nonneg a.1 b.1
      have hpos : 0 ≤ t ^ 3 * (P.cover j).dist a.1 b.1 / C := by positivity
      have hneg : -t ^ 3 * (P.cover j).dist a.1 b.1 / C =
          -(t ^ 3 * (P.cover j).dist a.1 b.1 / C) := by ring
      linarith
    calc ‖sk.h t a b‖
        ≤ C / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist a.1 b.1 / C) := hw
      _ ≤ C / Real.sqrt t * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = C / Real.sqrt t := mul_one _
      _ ≤ B_inv / Real.sqrt t := div_le_div_of_nonneg_right hCB_inv (Real.sqrt_nonneg t)
  have hfar_live : ∀ a b : L_curr, B_inv * S45.power t (-2) < dist_live a b →
      ‖sk.h t a b‖ ≤ B_inv / Real.sqrt t * Real.exp (-t * dist_live a b / B_inv) := by
    intro a b hab
    have habC : C * S45.power t (-2) < (P.cover j).dist a.1 b.1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCB_inv (Real.rpow_nonneg htpos.le _)) hab
    have hf := hfar_q a b habC
    have hexp_le : Real.exp (-t * dist_live a b / C) ≤ Real.exp (-t * dist_live a b / B_inv) := by
      apply Real.exp_le_exp.mpr
      have hd_nn : 0 ≤ t * dist_live a b := mul_nonneg htpos.le (hx.shell.nonneg a.1 b.1)
      have hdiv : t * dist_live a b / B_inv ≤ t * dist_live a b / C :=
        div_le_div_of_nonneg_left hd_nn hCpos hCB_inv
      have hneg1 : -t * dist_live a b / C = -(t * dist_live a b / C) := by ring
      have hneg2 : -t * dist_live a b / B_inv = -(t * dist_live a b / B_inv) := by ring
      linarith
    exact hf.trans (mul_le_mul (div_le_div_of_nonneg_right hCB_inv (Real.sqrt_nonneg t))
      hexp_le (Real.exp_nonneg _) (by positivity))
  have hrowNorm : S45.rowNorm (sk.P t) ≤ C_row * S45.logFactor t :=
    (hinv_row L_curr t sk dist_live htpos htt_inv hshell_live hKcap
      (hsw q.length le_rfl).1 hp_live hward_vec hqp_live hcrude_live hfar_live).2.1
  -- Form bounds on B_live
  have hB_qform : ∀ v : Fin (localDim P j T) → ℝ,
      S45.qform (sk.D t) (B_live *ᵥ v) ≤ 2 * C ^ 2 * S45.l2sq v := by
    intro v
    have hq_sub : S45.qform (sk.D t) (B_live *ᵥ v) =
        S45.qform (S45.schur (s0.D t + L_S) E) ((B_live *ᵥ v) ∘ Φ.symm) := by
      rw [hsk_D_sub, AgentS45.qform_submatrix]
    rw [hq_sub]
    let f_S : S → ℝ := fun a => (((P.cover j).cover.coords T).B *ᵥ v) a.1
    have hf_ext : ∀ a : (↑(Eᶜ) : Type _), f_S a.1 = ((B_live *ᵥ v) ∘ Φ.symm) a := by
      intro a
      change (((P.cover j).cover.coords T).B *ᵥ v) (a.1 : Port d m) =
        (B_live *ᵥ v) (Φ.symm a)
      simp only [Matrix.mulVec, dotProduct, B_live, hΦ_symm_val]
    have hschur_le := qform_schur_le_of_extend (s0.D t) L_S E ε ⟨hε0, by linarith⟩
      hs0_ker hLS_sym hLS_zero hLS_cap hE_proper ((B_live *ᵥ v) ∘ Φ.symm) f_S hf_ext
    have hs0_le := qform_s0_D_localB_le P j T x hx hq0 v
    have h1ε : 1 + ε ≤ 2 := by linarith
    have hs0_nn : 0 ≤ S45.qform (s0.D t) f_S := hs0_ker.2.1 f_S
    calc S45.qform (S45.schur (s0.D t + L_S) E) ((B_live *ᵥ v) ∘ Φ.symm)
        ≤ (1 + ε) * S45.qform (s0.D t) f_S := hschur_le
      _ ≤ 2 * (C ^ 2 * S45.l2sq v) := mul_le_mul h1ε hs0_le hs0_nn (by norm_num)
      _ = 2 * C ^ 2 * S45.l2sq v := by ring
  have hB_dual : ∀ y : L_curr → ℝ, S45.neutral y →
      S45.l2sq (B_liveᵀ *ᵥ y) ≤ 2 * C ^ 4 * (1 + 4 * C) * Wstar_live y := by
    intro y hy
    have hdual1 := l2sq_transpose_mulVec_le_dualForm (sk.D t) hsk_ker B_live (2 * C ^ 2)
      (by positivity) hB_qform y hy
    change S45.l2sq (B_liveᵀ *ᵥ y) ≤ 2 * C ^ 2 * sk.X t y at hdual1
    have hsh := hsharp y hy
    have hQ_le : (∑ i : L_curr, y i ^ 2 / sk.p i ^ 2) ≤ C ^ 2 * S45.l2sq y := by
      unfold S45.l2sq
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hp_lo : 1 / C ≤ sk.p i := (hbroad_S i.1 (hsub_curr i.2)).2.1
      have hp_pos : 0 < sk.p i := lt_of_lt_of_le (by positivity) hp_lo
      rw [Real.norm_eq_abs, sq_abs, div_le_iff₀ (sq_pos_of_pos hp_pos)]
      have h1 : 1 ≤ sk.p i * C := (div_le_iff₀ hCpos).mp hp_lo
      have h2 : 1 ≤ (sk.p i * C) ^ 2 := by nlinarith
      calc y i ^ 2 = y i ^ 2 * 1 := (mul_one _).symm
        _ ≤ y i ^ 2 * (sk.p i * C) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = C ^ 2 * y i ^ 2 * sk.p i ^ 2 := by ring
    have hkap1 : S45.power t S45.kappa ≤ 1 := by linarith [ha2]
    have hcoeff1 : 1 + C_pre * S45.power t S45.kappa ≤ 1 + 4 * C := by
      dsimp [C_pre]; nlinarith
    set F_val := S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3)
    have hF_le : Λplus_live y ≤ C * F_val := by
      simpa [F_val, mul_assoc] using hΛ_fourier_C y hy
    have hF_nn : 0 ≤ F_val :=
      mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) _)
        (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)
    have hL2_nn : 0 ≤ S45.l2sq y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hX_bound : sk.X t y ≤ C ^ 2 * (1 + 4 * C) * Wstar_live y := by
      have hterm1 : (1 + C_pre * S45.power t S45.kappa) * (∑ i : L_curr, y i ^ 2 / sk.p i ^ 2) ≤
          (1 + 4 * C) * (C ^ 2 * S45.l2sq y) :=
        mul_le_mul hcoeff1 hQ_le
          (Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
          (by positivity)
      have hterm2 : C_pre * t * Λplus_live y ≤ C_pre * t * (C * F_val) :=
        mul_le_mul_of_nonneg_left hF_le (by positivity)
      have hC_le : C ≤ C ^ 2 * (1 + 4 * C) := by
        have : 1 ≤ C * (1 + 4 * C) := by nlinarith
        nlinarith
      have hterm2' : C_pre * t * (C * F_val) ≤ C ^ 2 * (1 + 4 * C) * (C_pre * t * F_val) := by
        calc C_pre * t * (C * F_val) = C * (C_pre * t * F_val) := by ring
          _ ≤ C ^ 2 * (1 + 4 * C) * (C_pre * t * F_val) :=
              mul_le_mul_of_nonneg_right hC_le (by positivity)
      dsimp [Wstar_live]
      linarith
    calc S45.l2sq (B_liveᵀ *ᵥ y)
        ≤ 2 * C ^ 2 * sk.X t y := hdual1
      _ ≤ 2 * C ^ 2 * (C ^ 2 * (1 + 4 * C) * Wstar_live y) :=
          mul_le_mul_of_nonneg_left hX_bound (by positivity)
      _ = 2 * C ^ 4 * (1 + 4 * C) * Wstar_live y := by ring
  exact ⟨Λplus_live, hpre_sk, hrowNorm, hB_qform, hB_dual⟩

end PrestateAndFormsOfSlotSeq

end AndersonAC.AgentS78
