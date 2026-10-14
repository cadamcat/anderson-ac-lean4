import AndersonAC.AgentS6Construct.RidgeMeas

/-! The observable part of the trial cursor (active set, retained entries, previous
ridge, running flag, outcome) and a measurable one-step rule on it. -/

noncomputable section

open scoped Matrix

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6 MeasureTheory

@[ext] structure Obs (ι : Type*) where
  active : Finset ι
  H : Matrix ι ι ℂ
  τ : ℝ
  running : Bool
  outcome : TrialOutcome

namespace Obs

variable {ι : Type*}

def toProd (o : Obs ι) : Finset ι × Matrix ι ι ℂ × ℝ × Bool × TrialOutcome :=
  (o.active, o.H, o.τ, o.running, o.outcome)

instance : MeasurableSpace (Obs ι) := MeasurableSpace.comap toProd inferInstance

theorem measurable_toProd : Measurable (toProd (ι := ι)) := comap_measurable _

theorem measurable_of_toProd {α : Type*} [MeasurableSpace α] {f : α → Obs ι}
    (h : Measurable fun a => (f a).toProd) : Measurable f :=
  measurable_comap_iff.2 h

theorem measurable_active : Measurable (Obs.active (ι := ι)) :=
  measurable_fst.comp measurable_toProd

theorem measurable_H : Measurable (Obs.H (ι := ι)) :=
  measurable_fst.comp (measurable_snd.comp measurable_toProd)

theorem measurable_τ : Measurable (Obs.τ (ι := ι)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_toProd))

theorem measurable_running : Measurable (Obs.running (ι := ι)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_toProd)))

theorem measurable_outcome : Measurable (Obs.outcome (ι := ι)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_toProd)))

theorem measurable_mk {α : Type*} [MeasurableSpace α] {A : α → Finset ι}
    {H : α → Matrix ι ι ℂ} {τ : α → ℝ} {b : α → Bool} {c : α → TrialOutcome}
    (hA : Measurable A) (hH : Measurable H) (hτ : Measurable τ) (hb : Measurable b)
    (hc : Measurable c) :
    Measurable fun a => (⟨A a, H a, τ a, b a, c a⟩ : Obs ι) :=
  measurable_of_toProd (hA.prodMk (hH.prodMk (hτ.prodMk (hb.prodMk hc))))

end Obs

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def TrialCursor.obs {core : Finset ι} (q : TrialCursor core) : Obs ι :=
  ⟨q.state.active, q.state.hatG, q.previousRidge, q.running, q.outcome⟩

def obsCross (core : Finset ι) (t : ℝ) (r : ι → ℂ) (o : Obs ι) :
    Matrix ι {b // b ∈ core} ℂ :=
  trialCrossFromHatG t r o.active o.H

def obsRidge (core : Finset ι) (t : ℝ) (r : ι → ℂ) (o : Obs ι) : ℝ :=
  chooseRidge (obsCross core t r o) (leverageScale t) o.τ

def obsPivot (core : Finset ι) (t : ℝ) (r : ι → ℂ)
    (order : ι ≃ Fin (Fintype.card ι)) (o : Obs ι) : ι :=
  leastMaximizerTotal order (leverage (obsCross core t r o) (obsRidge core t r o))

def heatH (t : ℝ) (r : ι → ℂ) (ρ : ℝ) (H : Matrix ι ι ℂ) (x : ι) (A : Finset ι) :
    Matrix ι ι ℂ :=
  fun i j => if i ∈ A then if j ∈ A then shermanMorrisonEntry t r ρ H x i j
    else H i j else H i j

open Classical in
def obsStep (core : Finset ι) (t : ℝ) (N : ℕ) (r : ι → ℂ) (g0 : Matrix ι ι ℂ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (o : Obs ι) (ρ : ℝ) : Obs ι :=
  if o.running = true then
    if BudgetsHold t g0 o.H then
      if k = N then ⟨o.active, o.H, o.τ, false, .fail⟩
      else if 4 * leverageScale t < maxWeight (leverage (obsCross core t r o) o.τ) then
        ⟨o.active, o.H, o.τ, false, .fail⟩
      else if ∀ i, projectionWeight (obsCross core t r o) i ≤ 2 * leverageScale t then
        ⟨o.active, o.H, o.τ, false, .done⟩
      else
        ⟨o.active.erase (obsPivot core t r order o),
          heatH t r ρ o.H (obsPivot core t r order o)
            (o.active.erase (obsPivot core t r order o)),
          obsRidge core t r o, true, o.outcome⟩
    else ⟨o.active, o.H, o.τ, false, .fail⟩
  else o

theorem obsStep_running_indep (core : Finset ι) (t : ℝ) (N : ℕ) (r : ι → ℂ)
    (g0 : Matrix ι ι ℂ) (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (o : Obs ι)
    (ρ : ℝ) :
    (obsStep core t N r g0 order k o ρ).running =
      (obsStep core t N r g0 order k o 0).running := by
  unfold obsStep
  split_ifs <;> rfl

section Meas

variable {α : Type*} [mα : MeasurableSpace α] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem measurable_eval_at {β : Type*} [MeasurableSpace β] {f : α → ι → β}
    (hf : ∀ y, Measurable fun a => f a y) {x : α → ι} (hx : Measurable x) :
    Measurable fun a => f a (x a) := by
  have h : Measurable (fun p : α × ι => f p.1 p.2) :=
    measurable_from_prod_countable_left (fun y => hf y)
  exact h.comp (measurable_id.prodMk hx)

omit [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem measurable_obsCross (core : Finset ι) (t : ℝ) {o : α → Obs ι}
    {R : α → ι → ℂ} (ho : Measurable o) (hR : Measurable R) :
    Measurable fun a => obsCross core t (R a) (o a) :=
  measurable_trialCrossFromHatG t R (fun a => (o a).active) (fun a => (o a).H)
    (fun i => (measurableSet_mem_finset i).preimage (Obs.measurable_active.comp ho))
    hR (Obs.measurable_H.comp ho)

omit [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem measurable_obsRidge (core : Finset ι) (t : ℝ) (hl : 0 < leverageScale t)
    {o : α → Obs ι} {R : α → ι → ℂ} (ho : Measurable o) (hR : Measurable R) :
    Measurable fun a => obsRidge core t (R a) (o a) :=
  measurable_chooseRidge _ hl (measurable_obsCross core t ho hR)
    (Obs.measurable_τ.comp ho)

theorem measurable_obsPivot (core : Finset ι) (t : ℝ) (hl : 0 < leverageScale t)
    (order : ι ≃ Fin (Fintype.card ι)) {o : α → Obs ι} {R : α → ι → ℂ}
    (ho : Measurable o) (hR : Measurable R) :
    Measurable fun a => obsPivot core t (R a) order (o a) :=
  measurable_leastMaximizerTotal order (fun i => measurable_leverage_comp
    (measurable_obsCross core t ho hR) (measurable_obsRidge core t hl ho hR) i)

omit [Nonempty ι] in
theorem measurable_heatH (t : ℝ) {R : α → ι → ℂ} {ρ : α → ℝ}
    {H : α → Matrix ι ι ℂ} {x : α → ι} {A : α → Finset ι}
    (hR : Measurable R) (hρ : Measurable ρ) (hH : Measurable H) (hx : Measurable x)
    (hA : Measurable A) :
    Measurable fun a => heatH t (R a) (ρ a) (H a) (x a) (A a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have hmemi : MeasurableSet {a | i ∈ A a} := (measurableSet_mem_finset i).preimage hA
  have hmemj : MeasurableSet {a | j ∈ A a} := (measurableSet_mem_finset j).preimage hA
  have hHij : Measurable fun a => H a i j := hH.eval_matrix
  have hHix : Measurable fun a => H a i (x a) :=
    measurable_eval_at (f := fun a y => H a i y) (fun _ => hH.eval_matrix) hx
  have hHxj : Measurable fun a => H a (x a) j :=
    measurable_eval_at (f := fun a y => H a y j) (fun _ => hH.eval_matrix) hx
  have hHxx : Measurable fun a => H a (x a) (x a) :=
    measurable_eval_at (f := fun a y => H a y y) (fun _ => hH.eval_matrix) hx
  have hRx : Measurable fun a => R a (x a) :=
    measurable_eval_at (f := fun a y => R a y) (fun y => (measurable_pi_apply y).comp hR) hx
  have hc : Measurable fun a => ((ρ a : ℂ) + (t : ℂ) * R a (x a)) :=
    (Complex.measurable_ofReal.comp hρ).add (measurable_const.mul hRx)
  have hSM : Measurable fun a => shermanMorrisonEntry t (R a) (ρ a) (H a) (x a) i j := by
    unfold shermanMorrisonEntry
    exact hHij.sub (((hc.mul hHix).mul hHxj).div (measurable_const.add (hc.mul hHxx)))
  change Measurable fun a => if i ∈ A a then (if j ∈ A a then
    shermanMorrisonEntry t (R a) (ρ a) (H a) (x a) i j else H a i j) else H a i j
  exact Measurable.ite hmemi (Measurable.ite hmemj hSM hHij) hHij

omit [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem measurableSet_budgetsHold (t : ℝ) {G H : α → Matrix ι ι ℂ}
    (hG : Measurable G) (hH : Measurable H) :
    MeasurableSet {a | BudgetsHold t (G a) (H a)} := by
  have h1 : ∀ i j, Measurable fun a => ‖H a i j - G a i j‖ :=
    fun i j => (hH.eval_matrix.sub hG.eval_matrix).norm
  have hsq : ∀ i, Measurable fun a => sqRow (scaledInverse t (H a - G a)) i := by
    intro i
    unfold sqRow scaledInverse
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_const.mul (hH.eval_matrix.sub hG.eval_matrix)).norm).pow_const 2
  have hhs : Measurable fun a => hsSq (scaledInverse t (H a - G a)) := by
    unfold hsSq
    exact Finset.measurable_sum _ fun i _ => hsq i
  have hEq : {a | BudgetsHold t (G a) (H a)} =
      (⋂ i, ⋂ j, {a | ‖H a i j - G a i j‖ ≤ entryBudget t}) ∩
        ((⋂ i, {a | sqRow (scaledInverse t (H a - G a)) i ≤ rowBudget t}) ∩
          {a | hsSq (scaledInverse t (H a - G a)) ≤ frobeniusBudget t}) := by
    ext a
    simp only [BudgetsHold, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hEq]
  exact (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le (h1 i j) measurable_const).inter
    ((MeasurableSet.iInter fun i => measurableSet_le (hsq i) measurable_const).inter
      (measurableSet_le hhs measurable_const))

theorem measurable_obsStep (core : Finset ι) (t : ℝ) (N : ℕ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (hl : 0 < leverageScale t)
    {o : α → Obs ι} {R : α → ι → ℂ} {G : α → Matrix ι ι ℂ} {ρ : α → ℝ}
    (ho : Measurable o) (hR : Measurable R) (hG : Measurable G) (hρ : Measurable ρ) :
    Measurable fun a => obsStep core t N (R a) (G a) order k (o a) (ρ a) := by
  classical
  have hA := Obs.measurable_active.comp ho
  have hH := Obs.measurable_H.comp ho
  have hτ := Obs.measurable_τ.comp ho
  have hout := Obs.measurable_outcome.comp ho
  have hrun : MeasurableSet {a | (o a).running = true} :=
    (measurableSet_singleton true).preimage (Obs.measurable_running.comp ho)
  have hbud : MeasurableSet {a | BudgetsHold t (G a) (o a).H} :=
    measurableSet_budgetsHold t hG hH
  have hcap : MeasurableSet {a | 4 * leverageScale t <
      maxWeight (leverage (obsCross core t (R a) (o a)) (o a).τ)} :=
    measurableSet_lt measurable_const (measurable_maxWeight _
      (measurable_leverage_comp (measurable_obsCross core t ho hR) hτ))
  have hready : MeasurableSet {a | ∀ i, projectionWeight (obsCross core t (R a) (o a)) i ≤
      2 * leverageScale t} :=
    measurableSet_projectionReady (measurable_obsCross core t ho hR) _ hl
  have hfail : Measurable fun a =>
      (⟨(o a).active, (o a).H, (o a).τ, false, .fail⟩ : Obs ι) :=
    Obs.measurable_mk hA hH hτ measurable_const measurable_const
  have hdone : Measurable fun a =>
      (⟨(o a).active, (o a).H, (o a).τ, false, .done⟩ : Obs ι) :=
    Obs.measurable_mk hA hH hτ measurable_const measurable_const
  have hx := measurable_obsPivot core t hl order ho hR
  have hAe : Measurable fun a => (o a).active.erase (obsPivot core t (R a) order (o a)) := by
    rw [measurable_finset_iff]
    intro j
    have hset : {a | j ∈ (o a).active.erase (obsPivot core t (R a) order (o a))} =
        {a | obsPivot core t (R a) order (o a) = j}ᶜ ∩ {a | j ∈ (o a).active} := by
      ext a
      simp [Finset.mem_erase, eq_comm]
    have hms : MeasurableSet
        {a | j ∈ (o a).active.erase (obsPivot core t (R a) order (o a))} := by
      rw [hset]
      exact ((measurableSet_singleton j).preimage hx).compl.inter
        ((measurableSet_mem_finset j).preimage hA)
    exact measurableSet_setOfPred.mp hms
  have hheat : Measurable fun a =>
      (⟨(o a).active.erase (obsPivot core t (R a) order (o a)),
        heatH t (R a) (ρ a) (o a).H (obsPivot core t (R a) order (o a))
          ((o a).active.erase (obsPivot core t (R a) order (o a))),
        obsRidge core t (R a) (o a), true, (o a).outcome⟩ : Obs ι) :=
    Obs.measurable_mk hAe (measurable_heatH t hR hρ hH hx hAe)
      (measurable_obsRidge core t hl ho hR) measurable_const hout
  unfold obsStep
  exact Measurable.ite hrun (Measurable.ite hbud
    (Measurable.ite (MeasurableSet.const (k = N)) hfail
      (Measurable.ite hcap hfail (Measurable.ite hready hdone hheat))) hfail) ho

end Meas

section Top

/-! Versions that use the discrete σ-algebra on `ι` internally, so that callers need
no measurable-singleton assumption on their own σ-algebra on `ι`. -/

variable {α : Type*} [mα : MeasurableSpace α]

theorem measurable_obsStep_top (core : Finset ι) (t : ℝ) (N : ℕ)
    (order : ι ≃ Fin (Fintype.card ι)) (k : ℕ) (hl : 0 < leverageScale t)
    {o : α → Obs ι} {R : α → ι → ℂ} {G : α → Matrix ι ι ℂ} {ρ : α → ℝ}
    (ho : Measurable o) (hR : Measurable R) (hG : Measurable G) (hρ : Measurable ρ) :
    Measurable fun a => obsStep core t N (R a) (G a) order k (o a) (ρ a) := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact measurable_obsStep core t N order k hl ho hR hG hρ

theorem measurable_obsPivot_top (core : Finset ι) (t : ℝ) (hl : 0 < leverageScale t)
    (order : ι ≃ Fin (Fintype.card ι)) {o : α → Obs ι} {R : α → ι → ℂ}
    (ho : Measurable o) (hR : Measurable R) :
    @Measurable α ι mα ⊤ fun a => obsPivot core t (R a) order (o a) := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact measurable_obsPivot core t hl order ho hR

omit [DecidableEq ι] [Nonempty ι] in
theorem measurable_eval_at_top {β : Type*} [MeasurableSpace β] {f : α → ι → β}
    (hf : ∀ y, Measurable fun a => f a y) {x : α → ι} (hx : @Measurable α ι mα ⊤ x) :
    Measurable fun a => f a (x a) := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact measurable_eval_at hf hx

end Top

end AndersonAC.AgentS6Construct
