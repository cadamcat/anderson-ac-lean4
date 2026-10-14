import AndersonAC.S2.Retained

/-! The generated retained history is contained in the ambient source sigma-field. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace AndersonAC.SolS2
open AndersonAC.S2
section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

theorem orderCount_measurable (Q : ℕ → RandomSources ι M → Query ι) (q o : ℕ)
    (hQ : ∀ j < q, Measurable (Q j)) : Measurable (fun ω => orderCount ι Q q ω o) := by
  classical
  have hm : Measurable (fun ω => ∑ j ∈ Finset.range q,
      if Q j ω = Query.nextOrder o then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro j hj
    apply Measurable.ite _ measurable_const measurable_const
    exact hQ j (Finset.mem_range.mp hj) (show MeasurableSet {Query.nextOrder o} from trivial)
  simpa only [orderCount, Finset.sum_boole, Nat.cast_id] using hm

def orderAnswer (Q : ℕ → RandomSources ι M → Query ι) (q o : ℕ)
    (ω : RandomSources ι M) : Option ℕ :=
  if h : orderCount ι Q q ω o < M o then
    some ((ω.2 o ⟨orderCount ι Q q ω o, h⟩).val) else none

theorem orderAnswer_measurable (Q : ℕ → RandomSources ι M → Query ι) (q o : ℕ)
    (hQ : ∀ j < q, Measurable (Q j)) : Measurable (orderAnswer ι Q q o) := by
  let f : RandomSources ι M × ℕ → Option ℕ := fun p =>
    if h : p.2 < M o then some ((p.1.2 o ⟨p.2, h⟩).val) else none
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro n
    dsimp [f]
    split_ifs with hn
    · exact (measurable_from_top (f := fun a : Order (M o) => some ((a ⟨n, hn⟩).val))).comp
        ((measurable_pi_apply o).comp measurable_snd)
    · exact measurable_const
  exact hf.comp (measurable_id.prodMk (orderCount_measurable ι Q q o hQ))

theorem answer_measurable (Q : ℕ → RandomSources ι M → Query ι) (q : ℕ)
    (hQ : ∀ j ≤ q, Measurable (Q j)) : Measurable (answer ι Q q) := by
  classical
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro x
    change Measurable (fun ω => if x ∈ querySigns ι (Q q ω) then some (ω.1 x) else none)
    apply Measurable.ite
    · exact hQ q le_rfl (show MeasurableSet {c | x ∈ querySigns ι c} from trivial)
    · exact (measurable_of_finite (some : Bool → Option Bool)).comp
        ((measurable_pi_apply x).comp measurable_fst)
    · exact measurable_const
  · let select : Query ι → Option ℕ := fun c => match c with
      | .nextOrder o => some o
      | _ => none
    let f : RandomSources ι M × Option ℕ → Option ℕ := fun p =>
      match p.2 with
      | some o => orderAnswer ι Q q o p.1
      | none => none
    have hf : Measurable f := by
      apply measurable_from_prod_countable_left
      intro o
      cases o with
      | none => exact measurable_const
      | some o => exact orderAnswer_measurable ι Q q o (fun j hj => hQ j hj.le)
    have hs : Measurable (fun ω => select (Q q ω)) :=
      (measurable_from_top (f := select)).comp (hQ q le_rfl)
    convert hf.comp (measurable_id.prodMk hs) using 1
    funext ω
    cases hc : Q q ω <;> simp [f, select, orderAnswer, hc]

end Queries
end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2
section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

theorem retained_le {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ) :
    retained ι Q q ≤ (inferInstance : MeasurableSpace (RandomSources ι M)) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    cases q with
    | zero => exact bot_le
    | succ q =>
      have hprev := ih q (by omega)
      have hglobal : ∀ j ≤ q, Measurable (Q j) := by
        intro j hj
        exact Measurable.of_comap_le ((hQ.1 j).comap_le.trans (ih j (by omega)))
      apply sup_le hprev
      exact ((hglobal q le_rfl).prodMk (answer_measurable ι Q q hglobal)).comap_le

end Queries
end AndersonAC.S2
