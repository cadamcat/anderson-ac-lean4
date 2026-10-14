import AndersonAC.AgentS78.Construction.MachineDef

/-!
# WP10 random construction, C3a′: proof of the explicit machine run

The carried query list is the finite trace of `machineQ`. Its count of each
`nextOrder` query therefore agrees with `S2.orderCount`, which identifies each
`localAnswer` with `S2.answer`. The retained measurability proof follows the
answer recursion. Joint measurability is proved by induction on the run length;
the query and carried-list types are countable discrete spaces.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2

namespace MachineRunProof

local instance listQueryMeasurableSpace {ι : Type} [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (List (Query ι)) := ⊤

local instance listQueryMeasurableSingletonClass {ι : Type} [Fintype ι] [DecidableEq ι] :
    MeasurableSingletonClass (List (Query ι)) := ⟨fun _ => trivial⟩

local instance queryMeasurableSingletonClass {ι : Type} [Fintype ι] [DecidableEq ι] :
    MeasurableSingletonClass (Query ι) := ⟨fun _ => trivial⟩

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}
  {St : Type} [MeasurableSpace St]

theorem machineRun_snd (init : St) (next : St → Query ι)
    (update : St → Answer ι → St) (q : ℕ) (ω : RandomSources ι M) :
    (machineRun ι M init next update q ω).2 =
      (List.range q).map (fun j => machineQ ι M init next update j ω) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [machineRun, List.range_succ, List.map_append, ← ih]
    rfl

theorem card_filter_range_eq_count {α : Type} [DecidableEq α]
    (f : ℕ → α) (c : α) (q : ℕ) :
    ((Finset.range q).filter (fun j => f j = c)).card =
      ((List.range q).map f).count c := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ,
      List.map_append, List.count_append, ← ih]
    by_cases hq : f q = c
    · rw [if_pos hq, Finset.card_insert_of_notMem (by simp)]
      simp [hq]
    · rw [if_neg hq]
      simp [hq]

theorem machineRun_orderCount (init : St) (next : St → Query ι)
    (update : St → Answer ι → St) (q o : ℕ) (ω : RandomSources ι M) :
    (machineRun ι M init next update q ω).2.count (Query.nextOrder o) =
      orderCount ι (machineQ ι M init next update) q ω o := by
  rw [machineRun_snd]
  unfold orderCount
  symm
  exact card_filter_range_eq_count
    (fun j => machineQ ι M init next update j ω) (Query.nextOrder o) q

theorem localAnswer_eq_answer (init : St) (next : St → Query ι)
    (update : St → Answer ι → St) (q : ℕ) (ω : RandomSources ι M) :
    localAnswer ι M (machineRun ι M init next update q ω).2
        (machineQ ι M init next update q ω) ω =
      answer ι (machineQ ι M init next update) q ω := by
  classical
  cases hq : machineQ ι M init next update q ω with
  | trueDigit i k => simp [localAnswer, answer, hq]
  | auxiliary k => simp [localAnswer, answer, hq]
  | trueSuffix i k => simp [localAnswer, answer, hq]
  | nextOrder o =>
    simp [localAnswer, answer, hq,
      machineRun_orderCount (ι := ι) (M := M) init next update q o ω]
  | decision => simp [localAnswer, answer, hq]

theorem machineState_succ (init : St) (next : St → Query ι)
    (update : St → Answer ι → St) (q : ℕ) (ω : RandomSources ι M) :
    machineState ι M init next update (q + 1) ω =
      update (machineState ι M init next update q ω)
        (answer ι (machineQ ι M init next update) q ω) := by
  rw [show machineState ι M init next update (q + 1) ω =
      update (machineState ι M init next update q ω)
        (localAnswer ι M (machineRun ι M init next update q ω).2
          (machineQ ι M init next update q ω) ω) by rfl]
  rw [localAnswer_eq_answer]

theorem machineState_measurable (init : St) (next : St → Query ι)
    (_hnext : Measurable next) (update : St → Answer ι → St)
    (hupdate : Measurable (fun p : St × Answer ι => update p.1 p.2)) :
    ∀ q, @Measurable (RandomSources ι M) _
      (retained ι (machineQ ι M init next update) q) inferInstance
      (machineState ι M init next update q) := by
  classical
  intro q
  induction q with
  | zero => exact measurable_const
  | succ q ih =>
    let Q : ℕ → RandomSources ι M → Query ι := machineQ ι M init next update
    have hprev : @Measurable (RandomSources ι M) _ (retained ι Q (q + 1))
        inferInstance (machineState ι M init next update q) := by
      exact ih.mono (retained_mono ι Q (by omega)) le_rfl
    have hp : @Measurable (RandomSources ι M) _ (retained ι Q (q + 1))
        inferInstance (fun ω => (Q q ω, answer ι Q q ω)) := by
      apply Measurable.of_comap_le
      exact le_sup_right
    have ha : @Measurable (RandomSources ι M) _ (retained ι Q (q + 1))
        inferInstance (fun ω => answer ι Q q ω) := measurable_snd.comp hp
    have hpair : @Measurable (RandomSources ι M) _ (retained ι Q (q + 1))
        inferInstance (fun ω => (machineState ι M init next update q ω,
          answer ι Q q ω)) := hprev.prodMk ha
    have hupd : @Measurable (RandomSources ι M) _ (retained ι Q (q + 1))
        inferInstance (fun ω => update (machineState ι M init next update q ω)
          (answer ι Q q ω)) := hupdate.comp hpair
    have heq : machineState ι M init next update (q + 1) =
        (fun ω => update (machineState ι M init next update q ω)
          (answer ι Q q ω)) := by
      funext ω
      exact machineState_succ init next update q ω
    rw [heq]
    exact hupd

private def queryCode (c : Query ι) :
    (ι × ℕ) ⊕ (ℕ ⊕ ((ι × ℕ) ⊕ (ℕ ⊕ Unit))) :=
  match c with
  | .trueDigit i k => Sum.inl (i, k)
  | .auxiliary k => Sum.inr (Sum.inl k)
  | .trueSuffix i k => Sum.inr (Sum.inr (Sum.inl (i, k)))
  | .nextOrder o => Sum.inr (Sum.inr (Sum.inr (Sum.inl o)))
  | .decision => Sum.inr (Sum.inr (Sum.inr (Sum.inr ())) )

private theorem queryCode_injective : Function.Injective (queryCode (ι := ι)) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [queryCode]

private theorem query_countable : Countable (Query ι) := by
  haveI : Countable ι := inferInstance
  exact queryCode_injective.countable

private theorem localAnswer_measurable_fixed (L : List (Query ι))
    (c : Query ι) : Measurable (fun ω : RandomSources ι M => localAnswer ι M L c ω) := by
  classical
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro x
    change Measurable (fun ω : RandomSources ι M =>
      if x ∈ querySigns ι c then some (ω.1 x) else none)
    by_cases hx : x ∈ querySigns ι c
    · simp only [if_pos hx]
      exact (measurable_of_finite (some : Bool → Option Bool)).comp
        ((measurable_pi_apply x).comp measurable_fst)
    · simp only [if_neg hx]
      exact measurable_const
  · cases c with
    | nextOrder o =>
      by_cases h : L.count (Query.nextOrder o) < M o
      · simp only [localAnswer, h]
        exact (measurable_from_top (f := fun a : Order (M o) =>
          some ((a ⟨L.count (Query.nextOrder o), h⟩).val))).comp
          ((measurable_pi_apply o).comp measurable_snd)
      · simp only [localAnswer, h]
        exact measurable_const
    | trueDigit i k => simp [localAnswer]
    | auxiliary k => simp [localAnswer]
    | trueSuffix i k => simp [localAnswer]
    | decision => simp [localAnswer]

private theorem localAnswer_measurable_joint :
    Measurable (fun p : (List (Query ι) × Query ι) × RandomSources ι M =>
      localAnswer ι M p.1.1 p.1.2 p.2) := by
  classical
  letI : Countable (Query ι) := query_countable (ι := ι)
  apply measurable_from_prod_countable_right
  intro lc
  exact localAnswer_measurable_fixed lc.1 lc.2

private theorem appendSingleton_measurable :
    Measurable (fun p : List (Query ι) × Query ι => p.1 ++ [p.2]) := by
  classical
  letI : Countable (Query ι) := query_countable (ι := ι)
  letI : Countable (List (Query ι)) := inferInstance
  apply measurable_from_prod_countable_right
  intro L
  exact measurable_from_top

theorem machineRun_joint_measurable (P : Type) [MeasurableSpace P]
    (init : P → St) (hinit : Measurable init) (next : St → Query ι)
    (hnext : Measurable next) (update : St → Answer ι → St)
    (hupdate : Measurable (fun p : St × Answer ι => update p.1 p.2)) :
    ∀ q, Measurable (fun p : P × RandomSources ι M =>
      machineRun ι M (init p.1) next update q p.2) := by
  classical
  letI : Countable (Query ι) := query_countable (ι := ι)
  intro q
  induction q with
  | zero =>
    change Measurable (fun p : P × RandomSources ι M => (init p.1, []))
    exact (hinit.comp measurable_fst).prodMk measurable_const
  | succ q ih =>
    have hprev : Measurable (fun p : P × RandomSources ι M =>
        machineRun ι M (init p.1) next update q p.2) := ih
    have hstate := measurable_fst.comp hprev
    have hlist := measurable_snd.comp hprev
    have hquery : Measurable (fun p : P × RandomSources ι M =>
        next (machineRun ι M (init p.1) next update q p.2).1) := hnext.comp hstate
    have ha : Measurable (fun p : P × RandomSources ι M =>
        localAnswer ι M (machineRun ι M (init p.1) next update q p.2).2
          (next (machineRun ι M (init p.1) next update q p.2).1) p.2) := by
      exact localAnswer_measurable_joint (ι := ι) (M := M) |>.comp
        ((hlist.prodMk hquery).prodMk measurable_snd)
    have hstate' : Measurable (fun p : P × RandomSources ι M =>
        update (machineRun ι M (init p.1) next update q p.2).1
          (localAnswer ι M (machineRun ι M (init p.1) next update q p.2).2
            (next (machineRun ι M (init p.1) next update q p.2).1) p.2)) :=
      hupdate.comp (hstate.prodMk ha)
    have hlist' : Measurable (fun p : P × RandomSources ι M =>
        (machineRun ι M (init p.1) next update q p.2).2 ++
          [next (machineRun ι M (init p.1) next update q p.2).1]) :=
      appendSingleton_measurable (ι := ι) |>.comp (hlist.prodMk hquery)
    change Measurable (fun p : P × RandomSources ι M =>
      (update (machineRun ι M (init p.1) next update q p.2).1
        (localAnswer ι M (machineRun ι M (init p.1) next update q p.2).2
          (next (machineRun ι M (init p.1) next update q p.2).1) p.2),
       (machineRun ι M (init p.1) next update q p.2).2 ++
          [next (machineRun ι M (init p.1) next update q p.2).1]))
    exact hstate'.prodMk hlist'

theorem machineState_joint_measurable (P : Type) [MeasurableSpace P]
    (init : P → St) (hinit : Measurable init) (next : St → Query ι)
    (hnext : Measurable next) (update : St → Answer ι → St)
    (hupdate : Measurable (fun p : St × Answer ι => update p.1 p.2)) :
    ∀ q, Measurable (fun p : P × RandomSources ι M =>
      machineState ι M (init p.1) next update q p.2) := by
  intro q
  exact (measurable_fst.comp
    (machineRun_joint_measurable (ι := ι) (M := M) P init hinit next hnext update hupdate q))

end

end MachineRunProof

/-- The explicit machine run satisfies the frozen `MachineRunStatement`. -/
theorem machineRun_proof : MachineRunStatement := by
  intro ι hι hιdec M St hSt next hnext update hupdate
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro init q ω
    exact MachineRunProof.machineState_succ (ι := ι) (M := M) init next update q ω
  · intro init q
    exact MachineRunProof.machineState_measurable (ι := ι) (M := M) init next hnext update hupdate q
  · intro P hP init hinit q
    exact MachineRunProof.machineState_joint_measurable (ι := ι) (M := M)
      P init hinit next hnext update hupdate q

end AndersonAC.AgentS78

end
