import AndersonAC.AgentS78.Construction.TileBlock

/-!
# WP10 random construction, C3b: measurability of the tile block

`TileScratch` carries the comap σ-algebra of its coordinate code (`TileScratch.code`), in the
same format as `RunRecord.code` (Record.lean). `tileBlock_measurable` proves
`Block.IsMeasurable (tileBlock P j T)`.

Route: discrete data (lengths, live sets, pivots, the issued query, …) take countably many
values, so a map is measurable once each of its sections with the discrete data fixed is
(`measurable_select`, `measurable_of_factor`); with the discrete data fixed, every numerical
quantity of `S45` is an arithmetic expression in finitely many matrix entries, a matrix
inverse, an operator norm, or a closed condition (`formAbsLe`).
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open AndersonAC.S78
open AndersonAC.S2 (Query Answer)

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

/-! ## Generic tools -/

section Generic
variable {α D β : Type*} [MeasurableSpace α] [MeasurableSpace D] [Countable D]
  [MeasurableSingletonClass D] [MeasurableSpace β]

/-- A map given piecewise in a countable discrete parameter. -/
theorem measurable_select {c : α → D} (hc : Measurable c) {G : D → α → β}
    (hG : ∀ e, Measurable (G e)) : Measurable (fun a => G (c a) a) :=
  (measurable_from_prod_countable_left (f := fun p : α × D => G p.2 p.1) (fun e => hG e)).comp
    (measurable_id.prodMk hc)

/-- A set given piecewise in a countable discrete parameter. -/
theorem measurableSet_select {c : α → D} (hc : Measurable c) {Q : D → Set α}
    (hQ : ∀ e, MeasurableSet (Q e)) : MeasurableSet {a | a ∈ Q (c a)} := by
  have : {a | a ∈ Q (c a)} = ⋃ e, c ⁻¹' {e} ∩ Q e := by
    ext a; simp
  rw [this]
  exact MeasurableSet.iUnion fun e => (hc (measurableSet_singleton e)).inter (hQ e)

/-- A map that depends only on a countable measurable summary is measurable. -/
theorem measurable_of_factor {c : α → D} (hc : Measurable c) (f : α → β)
    (hf : ∀ a a', c a = c a' → f a = f a') : Measurable f := by
  classical
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · intro s _
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]
    exact MeasurableSet.empty
  · let F : D → β := fun e => if h : ∃ a, c a = e then f h.choose else f a₀
    have hfF : f = F ∘ c := by
      funext a
      have h : ∃ a', c a' = c a := ⟨a, rfl⟩
      simp only [Function.comp, F, dif_pos h]
      exact (hf _ _ h.choose_spec).symm
    rw [hfF]
    exact (measurable_of_countable F).comp hc

/-- Evaluation of a measurable sequence at a measurable index. -/
theorem measurable_lookup {F : α → ℕ → β} (hF : Measurable F) {L : α → ℕ} (hL : Measurable L) :
    Measurable (fun a => F a (L a)) :=
  measurable_select hL (G := fun n a => F a n) fun n => (measurable_pi_apply n).comp hF

/-- Sums over a measurable range of indices. -/
theorem measurable_sum_Ico {β : Type*} [AddCommMonoid β] [MeasurableSpace β]
    {α : Type*} [MeasurableSpace α] {f : ℕ → α → β} (hsum : ∀ K : Finset ℕ, Measurable fun a => ∑ k ∈ K, f k a)
    {L₁ L₂ : α → ℕ} (h₁ : Measurable L₁) (h₂ : Measurable L₂) :
    Measurable fun a => ∑ k ∈ Finset.Ico (L₁ a) (L₂ a), f k a :=
  measurable_select (h₁.prodMk h₂) (G := fun e a => ∑ k ∈ Finset.Ico e.1 e.2, f k a)
    fun e => hsum _

end Generic

theorem measurable_matrix_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable (fun A : Matrix n n ℂ => A⁻¹) := by
  have h : (fun A : Matrix n n ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).smul
    (continuous_id.matrix_adjugate).measurable

theorem continuous_l2_opNorm {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] :
    Continuous (fun A : Matrix n p 𝕜 => ‖A‖) := by
  have : (fun A : Matrix n p 𝕜 => ‖A‖) = fun A =>
      ‖(Matrix.toEuclideanLin (𝕜 := 𝕜) (m := n) (n := p)).trans
        LinearMap.toContinuousLinearMap A‖ := by
    funext A; exact Matrix.l2_opNorm_def A
  rw [this]
  exact continuous_norm.comp (LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanLin (𝕜 := 𝕜) (m := n) (n := p)).trans
      LinearMap.toContinuousLinearMap).toLinearMap)

/-! ## Decoding finite sets and options -/

section Codes
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Inverse of `finsetCode`. -/
def decodeFinset (c : ι → Bool) : Finset ι := Finset.univ.filter fun i => c i = true

theorem decodeFinset_code (s : Finset ι) : decodeFinset (finsetCode s) = s := by
  ext i; simp [decodeFinset, finsetCode]

open Classical in
/-- Inverse of `optionCode`. -/
def decodeOption (c : ι → Bool) : Option ι :=
  if h : ∃ i, c i = true then some h.choose else none

theorem decodeOption_code (o : Option ι) : decodeOption (optionCode o) = o := by
  rcases o with _ | i
  · simp [decodeOption, optionCode]
  · rw [decodeOption]
    split
    · rename_i h
      have hc := h.choose_spec
      generalize h.choose = c at hc ⊢
      simp only [optionCode, decide_eq_true_eq, Option.some.injEq] at hc
      exact congrArg some hc.symm
    · rename_i h
      exact absurd ⟨i, by simp [optionCode]⟩ h

theorem finsetCode_apply (s : Finset ι) (i : ι) : finsetCode s i = true ↔ i ∈ s := by
  simp [finsetCode]

theorem measurableSet_mem_of_code {α : Type*} [MeasurableSpace α] {S : α → Finset ι}
    (hS : Measurable fun a => finsetCode (S a)) (i : ι) : MeasurableSet {a | i ∈ S a} := by
  have : {a | i ∈ S a} = (fun a => finsetCode (S a) i) ⁻¹' {true} := by
    ext a; simp [finsetCode_apply]
  rw [this]
  exact ((measurable_pi_apply i).comp hS) (measurableSet_singleton true)

end Codes

/-! ## Numerical quantities of one state -/

section StateMeas
variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A measurable family of `S45` states. -/
structure StateMeas (s : α → S45.State ι) : Prop where
  g : Measurable fun a => (s a).g
  r : Measurable fun a => (s a).r

variable {s : α → S45.State ι}

theorem StateMeas.g_entry (hs : StateMeas s) (i j : ι) : Measurable fun a => (s a).g i j :=
  hs.g.eval_matrix

theorem StateMeas.r_entry (hs : StateMeas s) (i : ι) : Measurable fun a => (s a).r i :=
  (measurable_pi_apply i).comp hs.r

theorem StateMeas.h_entry (hs : StateMeas s) (t : ℝ) (i j : ι) :
    Measurable fun a => (s a).h t i j := by
  simp only [S45.State.h, Matrix.smul_apply, smul_eq_mul]
  exact (hs.g_entry i j).const_mul _

theorem StateMeas.K_entry (hs : StateMeas s) (t : ℝ) (i j : ι) :
    Measurable fun a => (s a).K t i j := by
  simp only [S45.State.K, S45.entrywiseSquare, AndersonAC.Blueprint.entrywiseSquare]
  exact (hs.h_entry t i j).pow_const 2

theorem StateMeas.F_entry (hs : StateMeas s) (t : ℝ) (i j : ι) :
    Measurable fun a => (s a).F t i j := by
  simp only [S45.State.F, S45.entryAbsSquare]
  exact (continuous_norm.measurable.comp (hs.h_entry t i j)).pow_const 2

theorem StateMeas.p_entry (hs : StateMeas s) (i : ι) : Measurable fun a => (s a).p i :=
  Complex.measurable_im.comp (hs.r_entry i)

theorem StateMeas.q_entry (hs : StateMeas s) (i : ι) : Measurable fun a => (s a).q i :=
  Complex.measurable_im.comp (hs.g_entry i i)

theorem StateMeas.K (hs : StateMeas s) (t : ℝ) : Measurable fun a => (s a).K t :=
  Measurable.of_eval_matrix _ fun i j => hs.K_entry t i j

theorem StateMeas.P (hs : StateMeas s) (t : ℝ) : Measurable fun a => (s a).P t := by
  simp only [S45.State.P]
  refine measurable_matrix_inv.comp ?_
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.sub_apply]
  exact measurable_const.sub (hs.K_entry t i j)

theorem StateMeas.lag_entry (hs : StateMeas s) (t : ℝ) (i : ι) :
    Measurable fun a => (s a).lag t i := by
  simp only [S45.State.lag, Matrix.mulVec, dotProduct, S45.State.rawLag]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (hs.P t).eval_matrix.mul ((hs.g_entry j j).sub (hs.r_entry j))

theorem StateMeas.fourthRow (hs : StateMeas s) (t : ℝ) (C : Finset ι) (i : ι) :
    Measurable fun a => (s a).fourthRow t C i := by
  simp only [S45.State.fourthRow]
  exact Finset.measurable_sum _ fun j _ =>
    (continuous_norm.measurable.comp (hs.h_entry t i j)).pow_const 4

theorem StateMeas.D (hs : StateMeas s) (t : ℝ) : Measurable fun a => (s a).D t := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [S45.State.D, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.mul_apply]
  refine Measurable.sub ?_ ?_
  · by_cases hij : i = j
    · simp only [hij, if_true]; exact (hs.p_entry j).mul (hs.q_entry j)
    · simp only [hij, if_false]; exact measurable_const
  · refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ (hs.F_entry t l k)
      by_cases hil : i = l
      · simp only [hil, if_true]; exact hs.p_entry l
      · simp only [hil, if_false]; exact measurable_const
    · by_cases hkj : k = j
      · simp only [hkj, if_true]; exact hs.p_entry j
      · simp only [hkj, if_false]; exact measurable_const

theorem StateMeas.gamma (hs : StateMeas s) (t : ℝ) (x : ι) {ξ : α → ℝ} (hξ : Measurable ξ) :
    Measurable fun a => S45.gamma t (s a) x (ξ a) := by
  simp only [S45.gamma]
  have hξc : Measurable fun a => ((ξ a : ℝ) : ℂ) := Complex.measurable_ofReal.comp hξ
  have hnum : Measurable fun a => ((ξ a : ℝ) : ℂ) + (t : ℂ) * (s a).r x :=
    hξc.add ((hs.r_entry x).const_mul _)
  exact hnum.div (measurable_const.mul (measurable_const.add (hnum.mul (hs.g_entry x x))))

theorem S45_pad_apply {ι' : Type*} [DecidableEq ι'] {β : Type*} [Zero β] (S : Finset ι')
    (A : Matrix S S β) (i j : ι') :
    S45.pad S A i j = if h : i ∈ S ∧ j ∈ S then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0 := by
  unfold S45.pad
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

theorem Jinc_apply (t : ℝ) (s : S45.State ι) (x : ι) (ξ : ℝ) (i j : ι) :
    S45.Jinc t s x ξ i j = if hi : i ∈ S45.survivors x then if hj : j ∈ S45.survivors x then
      (-2 * S45.gamma t s x ξ * s.h t i x * s.h t i j * s.h t x j +
        ((S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) * s.K t i x * s.K t x j) else 0 else 0 :=
  rfl

theorem StateMeas.Jinc (hs : StateMeas s) (t : ℝ) (x : ι) {ξ : α → ℝ} (hξ : Measurable ξ) :
    Measurable fun a => S45.Jinc t (s a) x (ξ a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Jinc_apply]
  by_cases h : i ∈ S45.survivors x ∧ j ∈ S45.survivors x
  · simp only [dif_pos h.1, dif_pos h.2]
    have hg := hs.gamma t x hξ
    refine Measurable.add ?_ ?_
    · exact (((measurable_const.mul hg).mul (hs.h_entry t i x)).mul
        (hs.h_entry t i j)).mul (hs.h_entry t x j)
    · exact (((hg.pow_const 2).sub (measurable_const.sub (hs.K_entry t x x)).inv).mul
        (hs.K_entry t i x)).mul (hs.K_entry t x j)
  · by_cases hi : i ∈ S45.survivors x
    · have hj : j ∉ S45.survivors x := fun hj => h ⟨hi, hj⟩
      simp only [dif_pos hi, dif_neg hj]; exact measurable_const
    · simp only [dif_neg hi]; exact measurable_const

theorem Linc_apply (t : ℝ) (s : S45.State ι) (x : ι) (ξ : ℝ) (i j : ι) :
    S45.Linc t s x ξ i j = if hi : i ∈ S45.survivors x then if hj : j ∈ S45.survivors x then
      S45.laplacian (S45.Ledge t s x ξ) ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 :=
  rfl

theorem StateMeas.Linc (hs : StateMeas s) (t : ℝ) (x : ι) {ξ : α → ℝ} (hξ : Measurable ξ) :
    Measurable fun a => S45.Linc t (s a) x (ξ a) := by
  have hE : ∀ i j : S45.survivors x, Measurable fun a => S45.Ledge t (s a) x (ξ a) i j := by
    intro i j
    simp only [S45.Ledge]
    have hg := hs.gamma t x hξ
    refine ((hs.p_entry i).mul (hs.p_entry j)).mul (Measurable.add ?_ ?_)
    · refine measurable_const.mul (Complex.measurable_re.comp ?_)
      exact ((hg.mul (continuous_star.measurable.comp (hs.h_entry t i j))).mul
        (hs.h_entry t i x)).mul (hs.h_entry t x j)
    · refine ((Measurable.sub ?_ ?_).mul (hs.F_entry t i x)).mul (hs.F_entry t x j)
      · exact (continuous_norm.measurable.comp hg).pow_const 2
      · exact (hs.p_entry x).div ((hs.q_entry x).sub ((hs.p_entry x).mul (hs.F_entry t x x)))
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Linc_apply]
  by_cases h : i ∈ S45.survivors x ∧ j ∈ S45.survivors x
  · simp only [dif_pos h.1, dif_pos h.2]
    unfold S45.laplacian
    by_cases hij : (⟨i, h.1⟩ : S45.survivors x) = ⟨j, h.2⟩
    · simp only [if_pos hij]
      exact Finset.measurable_sum _ fun k _ => by
        by_cases hk : k = ⟨i, h.1⟩
        · simp only [if_pos hk]; exact measurable_const
        · simp only [if_neg hk]; exact hE _ _
    · simp only [if_neg hij]; exact (hE _ _).neg
  · by_cases hi : i ∈ S45.survivors x
    · have hj : j ∉ S45.survivors x := fun hj => h ⟨hi, hj⟩
      simp only [dif_pos hi, dif_neg hj]; exact measurable_const
    · simp only [dif_neg hi]; exact measurable_const

end StateMeas

/-! ## Live states and sequences on a fixed port space -/

section SeqMeas
variable {α : Type*} [MeasurableSpace α] {P : Type} [Fintype P] [DecidableEq P]

theorem mask_apply {β : Type*} [Zero β] (S : Finset P) (A : Matrix P P β) (i j : P) :
    S45.mask S A i j = if hi : i ∈ S then if hj : j ∈ S then A i j else 0 else 0 := rfl

theorem measurable_mask {S : α → Finset P} (hS : Measurable fun a => finsetCode (S a))
    {A : α → Matrix P P ℂ} (hA : Measurable A) : Measurable fun a => S45.mask (S a) (A a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [mask_apply, dite_eq_ite]
  exact Measurable.ite (measurableSet_mem_of_code hS i)
    (Measurable.ite (measurableSet_mem_of_code hS j) hA.eval_matrix measurable_const)
    measurable_const

theorem measurable_mask_real {S : α → Finset P} (hS : Measurable fun a => finsetCode (S a))
    {A : α → Matrix P P ℝ} (hA : Measurable A) : Measurable fun a => S45.mask (S a) (A a) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [mask_apply, dite_eq_ite]
  exact Measurable.ite (measurableSet_mem_of_code hS i)
    (Measurable.ite (measurableSet_mem_of_code hS j) hA.eval_matrix measurable_const)
    measurable_const

/-- A measurable family of live states (live set through its code). -/
structure LiveMeas (lv : α → S45.LiveState P) : Prop where
  live : Measurable fun a => finsetCode (lv a).live
  g : Measurable fun a => (lv a).g

variable {lv : α → S45.LiveState P} {r : α → P → ℂ}

theorem LiveMeas.ambient (hl : LiveMeas lv) (hr : Measurable r) :
    StateMeas fun a => (lv a).ambient (r a) :=
  ⟨measurable_mask hl.live hl.g, hr⟩

/-- The restricted state on a fixed live set. -/
theorem stateMeas_restrict (S : Finset P) {g : α → Matrix P P ℂ} (hg : Measurable g)
    (hr : Measurable r) :
    StateMeas (ι := ↥S) fun a => (⟨S, g a⟩ : S45.LiveState P).state (r a) := by
  refine ⟨Measurable.of_eval_matrix _ fun i j => ?_, measurable_pi_iff.mpr fun i => ?_⟩
  · exact hg.eval_matrix
  · exact (measurable_pi_apply (i : P)).comp hr

theorem LiveMeas.ambientLag (hl : LiveMeas lv) (hr : Measurable r) (t : ℝ) (i : P) :
    Measurable fun a => (lv a).ambientLag t (r a) i := by
  let G : Finset P → α → ℂ := fun S a =>
    if hi : i ∈ S then ((⟨S, (lv a).g⟩ : S45.LiveState P).state (r a)).lag t ⟨i, hi⟩ else 0
  have hG : ∀ S, Measurable (G S) := by
    intro S
    by_cases hi : i ∈ S
    · simp only [G, dif_pos hi]
      exact (stateMeas_restrict S hl.g hr).lag_entry t ⟨i, hi⟩
    · simp only [G, dif_neg hi]; exact measurable_const
  have he : ∀ a, (lv a).ambientLag t (r a) i = G (decodeFinset (finsetCode (lv a).live)) a := by
    intro a; rw [decodeFinset_code]; rfl
  simp only [he]
  exact measurable_select hl.live (G := fun c a => G (decodeFinset c) a) fun c => hG _

/-- The two caps of the poststate (05:474–477) on its live set, as a measurable set. -/
theorem LiveMeas.measurableSet_caps (hl : LiveMeas lv) (hr : Measurable r) (t c₁ c₂ : ℝ) :
    MeasurableSet {a | (∀ i : (lv a).live, ((lv a).state (r a)).fourthRow t Finset.univ i ≤ c₁) ∧
      (∀ i : (lv a).live, ‖((lv a).state (r a)).lag t i‖ ≤ c₂)} := by
  let Q : Finset P → Set α := fun S =>
    (⋂ i : S, {a | ((⟨S, (lv a).g⟩ : S45.LiveState P).state (r a)).fourthRow t
      Finset.univ i ≤ c₁}) ∩
    (⋂ i : S, {a | ‖((⟨S, (lv a).g⟩ : S45.LiveState P).state (r a)).lag t i‖ ≤ c₂})
  have hQ : ∀ S, MeasurableSet (Q S) := by
    intro S
    have hs := stateMeas_restrict S hl.g hr
    exact (MeasurableSet.iInter fun i =>
        measurableSet_le (hs.fourthRow t Finset.univ i) measurable_const).inter
      (MeasurableSet.iInter fun i =>
        measurableSet_le (continuous_norm.measurable.comp (hs.lag_entry t i)) measurable_const)
  have he : {a | (∀ i : (lv a).live, ((lv a).state (r a)).fourthRow t Finset.univ i ≤ c₁) ∧
      (∀ i : (lv a).live, ‖((lv a).state (r a)).lag t i‖ ≤ c₂)} =
      {a | a ∈ Q (decodeFinset (finsetCode (lv a).live))} := by
    ext a
    simp only [decodeFinset_code, Q, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  exact measurableSet_select hl.live (Q := fun c => Q (decodeFinset c)) fun c => hQ _

/-- Code of a sweep sequence, in the format of `RunRecord.code`. -/
def seqCode (q : S45.Sequence P) :=
  (q.length, fun k => finsetCode (q.state k).live, fun k => (q.state k).g,
    fun k => optionCode (q.pivot k), q.scalar)

variable {Q : α → S45.Sequence P}

/-- A measurable family of sequences. -/
def SeqMeas (Q : α → S45.Sequence P) : Prop := Measurable fun a => seqCode (Q a)

theorem SeqMeas.length (hQ : SeqMeas Q) : Measurable fun a => (Q a).length := hQ.fst

theorem SeqMeas.liveFam (hQ : SeqMeas Q) :
    Measurable fun a => fun k => finsetCode ((Q a).state k).live := hQ.snd.fst

theorem SeqMeas.gFam (hQ : SeqMeas Q) : Measurable fun a => fun k => ((Q a).state k).g :=
  hQ.snd.snd.fst

theorem SeqMeas.pivotFam (hQ : SeqMeas Q) :
    Measurable fun a => fun k => optionCode ((Q a).pivot k) := hQ.snd.snd.snd.fst

theorem SeqMeas.scalarFam (hQ : SeqMeas Q) : Measurable fun a => (Q a).scalar :=
  hQ.snd.snd.snd.snd

theorem SeqMeas.state (hQ : SeqMeas Q) (k : ℕ) : LiveMeas fun a => (Q a).state k :=
  ⟨(measurable_pi_apply k).comp hQ.liveFam, (measurable_pi_apply k).comp hQ.gFam⟩

theorem SeqMeas.stateAt (hQ : SeqMeas Q) {L : α → ℕ} (hL : Measurable L) :
    LiveMeas fun a => (Q a).state (L a) :=
  ⟨measurable_lookup hQ.liveFam hL, measurable_lookup hQ.gFam hL⟩

theorem SeqMeas.scalar (hQ : SeqMeas Q) (k : ℕ) : Measurable fun a => (Q a).scalar k :=
  (measurable_pi_apply k).comp hQ.scalarFam

theorem SeqMeas.pivot (hQ : SeqMeas Q) (k : ℕ) : Measurable fun a => optionCode ((Q a).pivot k) :=
  (measurable_pi_apply k).comp hQ.pivotFam

variable (hr : Measurable r)
include hr

theorem SeqMeas.stepJ (hQ : SeqMeas Q) (t : ℝ) (k : ℕ) :
    Measurable fun a => (Q a).stepJ t (r a) k := by
  let G : Option P → α → S45.CMat P := fun o a => match o with
    | none => 0
    | some x => S45.mask ((Q a).state (k + 1)).live
        (S45.Jinc t (((Q a).state k).ambient (r a)) x ((Q a).scalar k))
  have hG : ∀ o, Measurable (G o) := by
    intro o
    rcases o with _ | x
    · exact measurable_const
    · exact measurable_mask (hQ.state (k + 1)).live
        (((hQ.state k).ambient hr).Jinc t x (hQ.scalar k))
  have he : ∀ a, (Q a).stepJ t (r a) k = G (decodeOption (optionCode ((Q a).pivot k))) a := by
    intro a; rw [decodeOption_code]; rfl
  simp only [he]
  exact measurable_select (hQ.pivot k) (G := fun c a => G (decodeOption c) a) fun c => hG _

theorem SeqMeas.stepL (hQ : SeqMeas Q) (t : ℝ) (k : ℕ) :
    Measurable fun a => (Q a).stepL t (r a) k := by
  let G : Option P → α → S45.RMat P := fun o a => match o with
    | none => 0
    | some x => S45.mask ((Q a).state (k + 1)).live
        (S45.Linc t (((Q a).state k).ambient (r a)) x ((Q a).scalar k))
  have hG : ∀ o, Measurable (G o) := by
    intro o
    rcases o with _ | x
    · exact measurable_const
    · exact measurable_mask_real (hQ.state (k + 1)).live
        (((hQ.state k).ambient hr).Linc t x (hQ.scalar k))
  have he : ∀ a, (Q a).stepL t (r a) k = G (decodeOption (optionCode ((Q a).pivot k))) a := by
    intro a; rw [decodeOption_code]; rfl
  simp only [he]
  exact measurable_select (hQ.pivot k) (G := fun c a => G (decodeOption c) a) fun c => hG _

theorem SeqMeas.stepLag (hQ : SeqMeas Q) (t : ℝ) (k : ℕ) :
    Measurable fun a => (Q a).stepLag t (r a) k := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [S45.Sequence.stepLag]
  exact Measurable.ite (measurableSet_mem_of_code (hQ.state (k + 1)).live i)
    ((((hQ.state (k + 1)).ambientLag hr t i)).sub ((hQ.state k).ambientLag hr t i))
    measurable_const

theorem SeqMeas.stepRow (hQ : SeqMeas Q) (t : ℝ) (cols : Finset P) (k : ℕ) :
    Measurable fun a => (Q a).stepRow t (r a) cols k := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [S45.Sequence.stepRow]
  refine Measurable.ite (measurableSet_mem_of_code (hQ.state (k + 1)).live i)
    (Measurable.div_const ?_ _) measurable_const
  simp only [← Finset.sum_ite_mem]
  refine Finset.measurable_sum _ fun j _ => Measurable.ite
    (measurableSet_mem_of_code (hQ.state (k + 1)).live j) ?_ measurable_const
  exact ((continuous_norm.measurable.comp
      ((((hQ.state (k + 1)).ambient hr).h_entry t i j))).pow_const 4).sub
    ((continuous_norm.measurable.comp (((hQ.state k).ambient hr).h_entry t i j)).pow_const 4)

theorem SeqMeas.Jrecord (hQ : SeqMeas Q) (t : ℝ) {L₁ L₂ : α → ℕ} (h₁ : Measurable L₁)
    (h₂ : Measurable L₂) :
    Measurable fun a => (Q a).Jrecord t (r a) (Finset.Ico (L₁ a) (L₂ a)) := by
  simp only [S45.Sequence.Jrecord]
  refine measurable_sum_Ico (f := fun k a => (Q a).stepJ t (r a) k) (fun K => ?_) h₁ h₂
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.sum_apply]
  exact Finset.measurable_sum _ fun k _ => (hQ.stepJ hr t k).eval_matrix

theorem SeqMeas.Lrecord (hQ : SeqMeas Q) (t : ℝ) {L₁ L₂ : α → ℕ} (h₁ : Measurable L₁)
    (h₂ : Measurable L₂) :
    Measurable fun a => (Q a).Lrecord t (r a) (Finset.Ico (L₁ a) (L₂ a)) := by
  simp only [S45.Sequence.Lrecord]
  refine measurable_sum_Ico (f := fun k a => (Q a).stepL t (r a) k) (fun K => ?_) h₁ h₂
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.sum_apply]
  exact Finset.measurable_sum _ fun k _ => (hQ.stepL hr t k).eval_matrix

theorem SeqMeas.lagRecord (hQ : SeqMeas Q) (t : ℝ) {L₁ L₂ : α → ℕ} (h₁ : Measurable L₁)
    (h₂ : Measurable L₂) :
    Measurable fun a => (Q a).lagRecord t (r a) (Finset.Ico (L₁ a) (L₂ a)) := by
  simp only [S45.Sequence.lagRecord]
  refine measurable_sum_Ico (f := fun k a => (Q a).stepLag t (r a) k) (fun K => ?_) h₁ h₂
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Finset.sum_apply]
  exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply i).comp (hQ.stepLag hr t k)

theorem SeqMeas.rowRecord (hQ : SeqMeas Q) (t : ℝ) (cols : Finset P) {L₁ L₂ : α → ℕ}
    (h₁ : Measurable L₁) (h₂ : Measurable L₂) :
    Measurable fun a => (Q a).rowRecord t (r a) cols (Finset.Ico (L₁ a) (L₂ a)) := by
  simp only [S45.Sequence.rowRecord]
  refine measurable_sum_Ico (f := fun k a => (Q a).stepRow t (r a) cols k) (fun K => ?_) h₁ h₂
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Finset.sum_apply]
  exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply i).comp (hQ.stepRow hr t cols k)

omit hr in
theorem isClosed_formAbsLe (c : ℝ) :
    IsClosed {p : S45.RMat P × S45.RMat P | S45.formAbsLe (S45.qform p.1) (S45.qform p.2) c} := by
  have : {p : S45.RMat P × S45.RMat P | S45.formAbsLe (S45.qform p.1) (S45.qform p.2) c} =
      ⋂ f : P → ℝ, {p | |S45.qform p.1 f| ≤ c * S45.qform p.2 f} := by
    ext p; simp [S45.formAbsLe]
  rw [this]
  refine isClosed_iInter fun f => isClosed_le ?_ ?_
  · refine continuous_abs.comp ?_
    simp only [S45.qform]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul
      ((continuous_apply i).comp (continuous_fst.matrix_mulVec continuous_const))
  · refine continuous_const.mul ?_
    simp only [S45.qform]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul
      ((continuous_apply i).comp (continuous_snd.matrix_mulVec continuous_const))

theorem SeqMeas.measurableSet_valid (hQ : SeqMeas Q) (t : ℝ) {D₀ : α → S45.RMat P}
    (hD : Measurable D₀) :
    MeasurableSet {a | (Q a).valid t (r a) (D₀ a) (Q a).length} := by
  have hJ := hQ.Jrecord hr t (L₁ := fun _ => 0) measurable_const hQ.length
  have hL := hQ.Lrecord hr t (L₁ := fun _ => 0) measurable_const hQ.length
  have he : {a | (Q a).valid t (r a) (D₀ a) (Q a).length} =
      {a | ‖(Q a).Jrecord t (r a) (Finset.Ico 0 (Q a).length)‖ ≤ S45.power t (S45.delta / 10)} ∩
      ((fun a => ((Q a).Lrecord t (r a) (Finset.Ico 0 (Q a).length), D₀ a)) ⁻¹'
        {p | S45.formAbsLe (S45.qform p.1) (S45.qform p.2) (S45.power t (S45.delta / 10))} ∩
      {a | (∀ i : ((Q a).state (Q a).length).live,
          (((Q a).state (Q a).length).state (r a)).fourthRow t Finset.univ i ≤ S45.rowCap t) ∧
        (∀ i : ((Q a).state (Q a).length).live,
          ‖(((Q a).state (Q a).length).state (r a)).lag t i‖ ≤ S45.power t S45.beta)}) := by
    ext a
    simp only [S45.Sequence.valid, Finset.range_eq_Ico, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage]
  rw [he]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le (continuous_l2_opNorm.measurable.comp hJ) measurable_const
  · exact (hL.prodMk hD) (isClosed_formAbsLe _).measurableSet
  · exact (hQ.stateAt hQ.length).measurableSet_caps hr t _ _

end SeqMeas

theorem measurableSet_localBudget {α : Type*} [MeasurableSpace α] {P I : Type} [Fintype P]
    [Fintype I] [DecidableEq P] [DecidableEq I] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cover : S45.TileCover (P := P) (I := I) d t b C dist) (T : Fin cover.count)
    {J : α → S45.CMat P} {L : α → S45.RMat P} {u : α → P → ℂ} {Ra Rr : α → P → ℝ}
    (hJ : Measurable J) (hL : Measurable L) (hu : Measurable u) (hRa : Measurable Ra)
    (hRr : Measurable Rr) :
    MeasurableSet {a | S45.localBudget cover T (J a) (L a) (u a) (Ra a) (Rr a)} := by
  have he : {a | S45.localBudget cover T (J a) (L a) (u a) (Ra a) (Rr a)} =
      (⋂ i ∈ cover.inner T, {a | ‖u a i‖ ≤ S45.power t (11 * S45.delta / 25)}) ∩
      ((⋂ i ∈ cover.inner T, {a | |Ra a i| ≤ S45.power t (S45.delta / 2000) ∧
          |Rr a i| ≤ S45.power t (S45.delta / 2000)}) ∩
      ({a | ‖S45.mask (cover.inner T) (J a)‖ ≤ S45.power t (S45.delta / 8)} ∩
       {a | ‖S45.pullback (cover.coords T).B (L a)‖ ≤ S45.power t (S45.delta / 8)})) := by
    ext a
    simp only [S45.localBudget, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  have hfin := (cover.inner T).countable_toSet
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · exact MeasurableSet.biInter hfin fun i _ => measurableSet_le
      (continuous_norm.measurable.comp ((measurable_pi_apply i).comp hu)) measurable_const
  · exact MeasurableSet.biInter hfin fun i _ =>
      (measurableSet_le (continuous_abs.measurable.comp ((measurable_pi_apply i).comp hRa))
        measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp ((measurable_pi_apply i).comp hRr))
        measurable_const)
  · exact measurableSet_le (continuous_l2_opNorm.measurable.comp
      (measurable_mask (S := fun _ => cover.inner T) measurable_const hJ)) measurable_const
  · refine measurableSet_le (continuous_l2_opNorm.measurable.comp ?_) measurable_const
    simp only [S45.pullback]
    exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable.comp hL

/-! ## Measurable structure of the block state -/

section Instances

/-- Injective encoding of a query. -/
def queryEncode {ι : Type} : Query ι → (ι × ℕ) ⊕ ℕ ⊕ (ι × ℕ) ⊕ ℕ ⊕ Unit
  | .trueDigit i k => Sum.inl (i, k)
  | .auxiliary k => Sum.inr (Sum.inl k)
  | .trueSuffix i h => Sum.inr (Sum.inr (Sum.inl (i, h)))
  | .nextOrder o => Sum.inr (Sum.inr (Sum.inr (Sum.inl o)))
  | .decision => Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

instance {ι : Type} [Fintype ι] [DecidableEq ι] : Countable (Query ι) := by
  refine Function.Injective.countable (f := queryEncode) ?_
  intro a b h
  cases a <;> cases b <;> simp_all [queryEncode]

instance {ι : Type} [Fintype ι] [DecidableEq ι] : MeasurableSingletonClass (Query ι) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : MeasurableSingletonClass (Option ℕ) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end Instances

section Scratch
variable {d m : ℕ}

/-- Coordinate code of the scratch state. -/
def TileScratch.code (sc : TileScratch d m) :=
  (sc.attempt, seqCode sc.seq, optionCode sc.site, sc.added, sc.consumed, sc.halted,
    sc.firstFail, sc.orderCount, sc.auxUsed)

instance : MeasurableSpace (TileScratch d m) :=
  MeasurableSpace.comap TileScratch.code inferInstance

theorem TileScratch.measurable_code : Measurable (TileScratch.code (d := d) (m := m)) :=
  comap_measurable _

variable {α : Type*} [MeasurableSpace α]

theorem measurable_scratch_iff {f : α → TileScratch d m} :
    Measurable f ↔ Measurable fun a => (f a).code := by
  refine ⟨fun h => TileScratch.measurable_code.comp h, fun h s hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hs
  exact h ht

theorem measurable_record_iff {f : α → RunRecord d m} :
    Measurable f ↔ Measurable fun a => (f a).code := by
  refine ⟨fun h => (RunRecord.measurable_code d m).comp h, fun h s hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hs
  exact h ht

/-- Field accessors of a measurable scratch family. -/
structure ScratchMeas (f : α → TileScratch d m) : Prop where
  attempt : Measurable fun a => (f a).attempt
  seq : SeqMeas fun a => (f a).seq
  site : Measurable fun a => optionCode (f a).site
  added : Measurable fun a => (f a).added
  consumed : Measurable fun a => (f a).consumed
  halted : Measurable fun a => (f a).halted
  firstFail : Measurable fun a => (f a).firstFail
  orderCount : Measurable fun a => (f a).orderCount
  auxUsed : Measurable fun a => (f a).auxUsed

theorem ScratchMeas.measurable {f : α → TileScratch d m} (h : ScratchMeas f) : Measurable f :=
  measurable_scratch_iff.mpr (h.attempt.prodMk (h.seq.prodMk (h.site.prodMk (h.added.prodMk
    (h.consumed.prodMk (h.halted.prodMk (h.firstFail.prodMk (h.orderCount.prodMk h.auxUsed))))))))

theorem ScratchMeas.of_measurable {f : α → TileScratch d m} (h : Measurable f) : ScratchMeas f := by
  have hc := TileScratch.measurable_code.comp h
  exact ⟨hc.fst, hc.snd.fst, hc.snd.snd.fst, hc.snd.snd.snd.fst, hc.snd.snd.snd.snd.fst,
    hc.snd.snd.snd.snd.snd.fst, hc.snd.snd.snd.snd.snd.snd.fst,
    hc.snd.snd.snd.snd.snd.snd.snd.fst, hc.snd.snd.snd.snd.snd.snd.snd.snd⟩

/-- Field-group accessors of a measurable record family. -/
structure RecordMeas (f : α → RunRecord d m) : Prop where
  stage : Measurable fun a => (f a).stage
  endpoint : Measurable fun a =>
    (finsetCode (f a).endpoint.active, (f a).endpoint.M, (f a).endpoint.g, (f a).r)
  sweep : SeqMeas fun a => (f a).sweep
  values : Measurable fun a => ((f a).installed, (f a).prefixLength)
  sites : Measurable fun a =>
    (finsetCode (f a).terminal, finsetCode (f a).pending, fun y => labelCode ((f a).latest y))
  components : Measurable fun a => fun B : Finset (Torus d m) => decide (B ∈ (f a).components)
  aborted : Measurable fun a => (f a).aborted

theorem RecordMeas.measurable {f : α → RunRecord d m} (h : RecordMeas f) : Measurable f :=
  measurable_record_iff.mpr (h.stage.prodMk (h.endpoint.prodMk (h.sweep.prodMk (h.values.prodMk
    (h.sites.prodMk (h.components.prodMk h.aborted))))))

theorem RecordMeas.of_measurable {f : α → RunRecord d m} (h : Measurable f) : RecordMeas f := by
  have hc := (RunRecord.measurable_code d m).comp h
  exact ⟨hc.fst, hc.snd.fst, hc.snd.snd.fst, hc.snd.snd.snd.fst, hc.snd.snd.snd.snd.fst,
    hc.snd.snd.snd.snd.snd.fst, hc.snd.snd.snd.snd.snd.snd⟩

theorem RecordMeas.active {f : α → RunRecord d m} (h : RecordMeas f) :
    Measurable fun a => finsetCode (f a).endpoint.active := h.endpoint.fst

theorem RecordMeas.r {f : α → RunRecord d m} (h : RecordMeas f) :
    Measurable fun a => (f a).r := h.endpoint.snd.snd.snd

theorem RecordMeas.pending {f : α → RunRecord d m} (h : RecordMeas f) :
    Measurable fun a => finsetCode (f a).pending := h.sites.snd.fst

theorem RecordMeas.prefixLength {f : α → RunRecord d m} (h : RecordMeas f) :
    Measurable fun a => (f a).prefixLength := h.values.snd

end Scratch

/-! ## Measurability of the block's maps -/

section BlockOps
variable {d m : ℕ} {α : Type*} [MeasurableSpace α]

theorem measurableSet_nat (L : α → ℕ) (hL : Measurable L) (p : ℕ → Prop) :
    MeasurableSet {a | p (L a)} :=
  hL (Set.to_countable {n | p n}).measurableSet

theorem measurable_initScratch : Measurable fun x : RunRecord d m => initScratch x := by
  have hx := RecordMeas.of_measurable (measurable_id (α := RunRecord d m))
  exact ScratchMeas.measurable ⟨measurable_const' fun _ _ => rfl, hx.sweep,
    measurable_const' fun _ _ => rfl, measurable_const' fun _ _ => rfl,
    measurable_const' fun _ _ => rfl, measurable_const' fun _ _ => rfl,
    measurable_const' fun _ _ => rfl, measurable_const' fun _ _ => rfl,
    measurable_const' fun _ _ => rfl⟩

theorem measurable_initScratch_halted :
    Measurable fun x : RunRecord d m => { initScratch x with halted := true } := by
  have hx := RecordMeas.of_measurable (measurable_id (α := RunRecord d m))
  exact ScratchMeas.measurable ⟨measurable_const' fun _ _ => rfl, hx.sweep,
    measurable_const' fun _ _ => rfl, measurable_const' fun _ _ => rfl,
    measurable_const' fun _ _ => rfl, measurable_const' fun _ _ => rfl,
    measurable_const' fun _ _ => rfl, measurable_const' fun _ _ => rfl,
    measurable_const' fun _ _ => rfl⟩

theorem measurable_logQuery (q : Query (Torus d m)) {f : α → TileScratch d m}
    (hf : Measurable f) : Measurable fun a => logQuery q (f a) := by
  have h := ScratchMeas.of_measurable hf
  refine ScratchMeas.measurable ⟨h.attempt, h.seq, h.site, h.added, h.consumed, h.halted,
    h.firstFail, measurable_pi_iff.mpr fun o => ?_, measurable_pi_iff.mpr fun k => ?_⟩
  · exact (measurable_of_countable (fun n : ℕ =>
      n + if q = Query.nextOrder o then 1 else 0)).comp ((measurable_pi_apply o).comp h.orderCount)
  · exact (measurable_of_countable (fun b : Bool => b || decide (q = Query.auxiliary k))).comp
      ((measurable_pi_apply k).comp h.auxUsed)

/-- Commit of an accepted trial. -/
theorem measurable_commitTrial (finalSweep : Bool)
    {f : α → RunRecord d m × TileScratch d m} (hf : Measurable f) :
    Measurable fun a => commitTrial (f a).1 (f a).2 finalSweep := by
  have hx := RecordMeas.of_measurable hf.fst
  have hs := ScratchMeas.of_measurable hf.snd
  refine RecordMeas.measurable ⟨hx.stage, hx.endpoint, hs.seq, ?_, ?_, hx.components,
    hx.aborted⟩
  · refine Measurable.prodMk (measurable_pi_iff.mpr fun i => ?_)
      (measurable_pi_iff.mpr fun i => ?_)
    · exact ((measurable_pi_apply i).comp hx.values.fst).add
        ((measurable_pi_apply i).comp hs.added)
    · exact (measurable_of_countable (fun p : ℕ × Bool =>
        p.1 + if p.2 = true && !finalSweep then 1 else 0)).comp
        (((measurable_pi_apply i).comp hx.prefixLength).prodMk
          ((measurable_pi_apply i).comp hs.consumed))
  · have hterminal : Measurable fun a =>
        finsetCode (commitTrial (f a).1 (f a).2 finalSweep).terminal := by
      refine measurable_of_factor (hx.sites.fst.prodMk hs.consumed) _ ?_
      intro a a' h
      rcases Prod.mk.inj h with ⟨ht, hc⟩
      have ht' := finsetCode_injective ht
      apply congrArg finsetCode
      ext i
      simp [commitTrial, ht', hc]
    exact hterminal.prodMk hx.sites.snd

/-- Whole-tile marking. -/
theorem measurable_markTile (S : Finset (Torus d m)) (label : BirthLabel (Torus d m))
    {f : α → RunRecord d m} (hf : Measurable f) : Measurable fun a => markTile S label (f a) := by
  have hx := RecordMeas.of_measurable hf
  refine RecordMeas.measurable ⟨hx.stage, hx.endpoint, hx.sweep, hx.values, ?_, hx.components,
    hx.aborted⟩
  classical
  let F : ((Torus d m → Bool) × (Torus d m → Bool) × (Torus d m → ℕ × Bool × (Torus d m → Bool)))
      × (Torus d m → Bool) → _ := fun e =>
    (e.1.1, finsetCode (decodeFinset e.1.2.1 ∪ (S ∩ decodeFinset e.2)),
      fun y => if y ∈ S ∧ y ∈ decodeFinset e.2 then labelCode label else e.1.2.2 y)
  have he : (fun a => (finsetCode (markTile S label (f a)).terminal,
      finsetCode (markTile S label (f a)).pending,
      fun y => labelCode ((markTile S label (f a)).latest y))) =
      fun a => F ((finsetCode (f a).terminal, finsetCode (f a).pending,
        fun y => labelCode ((f a).latest y)), finsetCode (f a).endpoint.active) := by
    funext a
    simp only [F, decodeFinset_code, markTile]
    congr 1
    congr 1
    funext y
    split_ifs <;> rfl
  rw [he]
  exact (measurable_of_countable F).comp (hx.sites.prodMk hx.active)

theorem measurable_portR (θ : ℝ) {r : α → Torus d m → ℂ} (hr : Measurable r) :
    Measurable fun a => portR θ (r a) := by
  refine measurable_pi_iff.mpr fun x => ?_
  simp only [portR, S45.PortMap.liftState]
  exact measurable_const.mul ((measurable_pi_apply x.1).comp hr)

end BlockOps

/-! ## One deletion and the continuation test -/

section Trial
variable {d m : ℕ} {α : Type*} [MeasurableSpace α]

theorem LiveMeas.stepLive {lv : α → S45.LiveState (Port d m)} (hl : LiveMeas lv) (t : ℝ)
    {r : α → Port d m → ℂ} (hr : Measurable r) (x : Port d m) {ξ : α → ℝ} (hξ : Measurable ξ) :
    LiveMeas fun a => stepLive t (r a) (lv a) x (ξ a) := by
  have hlive : Measurable fun a => finsetCode ((lv a).live.erase x) := by
    have he : (fun a => finsetCode ((lv a).live.erase x)) =
        fun a => (fun c => finsetCode ((decodeFinset c).erase x)) (finsetCode (lv a).live) := by
      funext a; simp only [decodeFinset_code]
    rw [he]
    exact (measurable_of_countable
      (fun c : Port d m → Bool => finsetCode ((decodeFinset c).erase x))).comp hl.live
  refine ⟨hlive, measurable_mask hlive (Measurable.of_eval_matrix _ fun i j => ?_)⟩
  have hξc : Measurable fun a => ((ξ a : ℝ) : ℂ) := Complex.measurable_ofReal.comp hξ
  have hs : Measurable fun a => ((ξ a : ℝ) : ℂ) + (t : ℂ) * r a x :=
    hξc.add (((measurable_pi_apply x).comp hr).const_mul _)
  exact (hl.g.eval_matrix).sub ((((hs.mul hl.g.eval_matrix).mul hl.g.eval_matrix)).div
    (measurable_const.add (hs.mul hl.g.eval_matrix)))

theorem SeqMeas.extend {Q : α → S45.Sequence (Port d m)} (hQ : SeqMeas Q)
    {b : α → S45.LiveState (Port d m)} (hb : LiveMeas b) (x : Port d m) {ξ : α → ℝ}
    (hξ : Measurable ξ) : SeqMeas fun a => extendSeq (Q a) (b a) x (ξ a) := by
  have hL := hQ.length
  refine hL.add_const 1 |>.prodMk (Measurable.prodMk ?_ (Measurable.prodMk ?_
    (Measurable.prodMk ?_ ?_)))
  · refine measurable_pi_iff.mpr fun k => ?_
    have he : (fun a => finsetCode ((extendSeq (Q a) (b a) x (ξ a)).state k).live) =
        fun a => if k = (Q a).length + 1 then finsetCode (b a).live
          else finsetCode ((Q a).state k).live := by
      funext a; simp only [extendSeq]; split_ifs <;> rfl
    rw [he]
    exact Measurable.ite (measurableSet_nat _ hL fun n => k = n + 1) hb.live
      (hQ.state k).live
  · refine measurable_pi_iff.mpr fun k => ?_
    have he : (fun a => ((extendSeq (Q a) (b a) x (ξ a)).state k).g) =
        fun a => if k = (Q a).length + 1 then (b a).g else ((Q a).state k).g := by
      funext a; simp only [extendSeq]; split_ifs <;> rfl
    rw [he]
    exact Measurable.ite (measurableSet_nat _ hL fun n => k = n + 1) hb.g (hQ.state k).g
  · refine measurable_pi_iff.mpr fun k => ?_
    have he : (fun a => optionCode ((extendSeq (Q a) (b a) x (ξ a)).pivot k)) =
        fun a => if k = (Q a).length then optionCode (some x)
          else optionCode ((Q a).pivot k) := by
      funext a; simp only [extendSeq]; split_ifs <;> rfl
    rw [he]
    exact Measurable.ite (measurableSet_nat _ hL fun n => k = n) measurable_const (hQ.pivot k)
  · refine measurable_pi_iff.mpr fun k => ?_
    have he : (fun a => (extendSeq (Q a) (b a) x (ξ a)).scalar k) =
        fun a => if k = (Q a).length then ξ a else (Q a).scalar k := by
      funext a; simp only [extendSeq]
    rw [he]
    exact Measurable.ite (measurableSet_nat _ hL fun n => k = n) hξ (hQ.scalar k)

variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

theorem measurable_stageD0 {f : α → RunRecord d m} (hf : Measurable f) :
    Measurable fun a => stageD0 P j (f a) := by
  have hx := RecordMeas.of_measurable hf
  exact ((hx.sweep.state 0).ambient (measurable_portR _ hx.r)).D _

theorem measurableSet_trialOk {f : α → RunRecord d m} (hf : Measurable f)
    {Q : α → S45.Sequence (Port d m)} (hQ : SeqMeas Q) {den : α → ℂ} (hden : Measurable den) :
    MeasurableSet {a | trialOk P j T (f a) (Q a) (den a)} := by
  have hx := RecordMeas.of_measurable hf
  have hr := measurable_portR (sweepTheta P.u m j) hx.r
  have h₁ := hx.sweep.length
  have h₂ := hQ.length
  have he : {a | trialOk P j T (f a) (Q a) (den a)} = {a | den a ≠ 0} ∩
      ({a | (Q a).valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) (f a).r)
          (stageD0 P j (f a)) (Q a).length} ∩
      {a | S45.localBudget (P.cover j).cover T
        ((Q a).Jrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) (f a).r)
          (Finset.Ico (f a).sweep.length (Q a).length))
        ((Q a).Lrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) (f a).r)
          (Finset.Ico (f a).sweep.length (Q a).length))
        ((Q a).lagRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) (f a).r)
          (Finset.Ico (f a).sweep.length (Q a).length))
        ((Q a).rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) (f a).r) Finset.univ
          (Finset.Ico (f a).sweep.length (Q a).length))
        ((Q a).rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) (f a).r) S45.reserves
          (Finset.Ico (f a).sweep.length (Q a).length))}) := by
    ext a; simp only [trialOk, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [he]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact (hden (measurableSet_singleton 0)).compl
  · exact hQ.measurableSet_valid hr _ (measurable_stageD0 P j hf)
  · exact measurableSet_localBudget _ _ (hQ.Jrecord hr _ h₁ h₂) (hQ.Lrecord hr _ h₁ h₂)
      (hQ.lagRecord hr _ h₁ h₂) (hQ.rowRecord hr _ _ h₁ h₂) (hQ.rowRecord hr _ _ h₁ h₂)

/-- A failed trial is a measurable operation. -/
theorem measurable_failTrial {f : α → RunRecord d m × TileScratch d m} (hf : Measurable f) :
    Measurable fun a => failTrial P j T (f a) := by
  have hs := ScratchMeas.of_measurable hf.snd
  classical
  have hx' : Measurable fun a => if (f a).2.attempt = 0 then
      markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ (f a).1 else (f a).1 :=
    Measurable.ite (measurableSet_nat _ hs.attempt fun n => n = 0)
      (measurable_markTile _ _ hf.fst) hf.fst
  have hX := RecordMeas.of_measurable hx'
  by_cases hj : m / 2 < j
  · simp only [failTrial, if_pos hj]
    refine Measurable.prodMk ?_ ?_
    · exact RecordMeas.measurable ⟨hX.stage, hX.endpoint, hX.sweep, hX.values, hX.sites,
        hX.components, measurable_const' fun _ _ => rfl⟩
    · exact ScratchMeas.measurable ⟨hs.attempt, hs.seq, measurable_const' fun _ _ => rfl,
        hs.added, hs.consumed, measurable_const' fun _ _ => rfl,
        measurable_const' fun _ _ => rfl, hs.orderCount, hs.auxUsed⟩
  · simp only [failTrial, if_neg hj]
    refine Measurable.prodMk hx' ?_
    exact ScratchMeas.measurable ⟨hs.attempt.add_const 1, hX.sweep,
      measurable_const' fun _ _ => rfl, measurable_const' fun _ _ => rfl,
      measurable_const' fun _ _ => rfl, hs.halted, measurable_const' fun _ _ => rfl,
      hs.orderCount, hs.auxUsed⟩

/-- One active slot is a measurable operation. -/
theorem measurable_scalarStep {f : α → RunRecord d m × TileScratch d m} (hf : Measurable f)
    (i : Torus d m) {ζ : α → ℝ} (hζ : Measurable ζ) :
    Measurable fun a => scalarStep P j T (f a) i (ζ a) := by
  have hx := RecordMeas.of_measurable hf.fst
  have hs := ScratchMeas.of_measurable hf.snd
  have hr := measurable_portR (sweepTheta P.u m j) hx.r
  have hξ : Measurable fun a => ζ a / Real.sqrt (sweepW P.u m j) := hζ.div_const _
  have hlv := hs.seq.stateAt hs.seq.length
  have hb := hlv.stepLive (sweepScale P.u m j) hr ((i, false) : Port d m) hξ
  have hq := hs.seq.extend hb ((i, false) : Port d m) hξ
  have hden : Measurable fun a => stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j)
      (f a).1.r) ((f a).2.seq.state (f a).2.seq.length) ((i, false) : Port d m)
      (ζ a / Real.sqrt (sweepW P.u m j)) := by
    simp only [stepDen]
    exact measurable_const.add (((Complex.measurable_ofReal.comp hξ).add
      (((measurable_pi_apply _).comp hr).const_mul _)).mul hlv.g.eval_matrix)
  simp only [scalarStep]
  refine Measurable.ite (measurableSet_trialOk P j T hf.fst hq hden) ?_
    (measurable_failTrial P j T hf)
  refine Measurable.prodMk hf.fst ?_
  classical
  refine ScratchMeas.measurable ⟨hs.attempt, hq, measurable_const' fun _ _ => rfl, ?_, ?_,
    hs.halted, hs.firstFail, hs.orderCount, hs.auxUsed⟩
  · refine measurable_pi_iff.mpr fun y => ?_
    by_cases hy : y = i
    · subst hy; simp only [Function.update_self]
      exact ((measurable_pi_apply y).comp hs.added).add hζ
    · simp only [Function.update_of_ne hy]; exact (measurable_pi_apply y).comp hs.added
  · refine measurable_pi_iff.mpr fun y => ?_
    by_cases hy : y = i
    · subst hy; simp only [Function.update_self]
      refine measurable_of_factor (hs.attempt.prodMk hx.pending) _ fun a a' h => ?_
      simp only [Prod.mk.injEq] at h
      have h2 := finsetCode_injective h.2
      simp only [usesTrue, h.1, h2]
      exact decide_eq_decide.mpr Iff.rfl
    · simp only [Function.update_of_ne hy]; exact (measurable_pi_apply y).comp hs.consumed

end Trial

/-! ## The block -/

instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section Final
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
variable {α : Type*} [MeasurableSpace α]

theorem tileQuery_congr (s s' : RunRecord d m × TileScratch d m)
    (hsite : s.2.site = s'.2.site) (hatt : s.2.attempt = s'.2.attempt)
    (hoc : s.2.orderCount (tileOrderIndex j T s.2.attempt) =
      s'.2.orderCount (tileOrderIndex j T s'.2.attempt))
    (hau : ∀ i : Torus d m, s.2.auxUsed (tileAuxIndex j T s.2.attempt i) =
      s'.2.auxUsed (tileAuxIndex j T s'.2.attempt i))
    (hpend : s.1.pending = s'.1.pending) (hact : s.1.endpoint.active = s'.1.endpoint.active)
    (hterm : s.1.terminal = s'.1.terminal) (hpl : s.1.prefixLength = s'.1.prefixLength) :
    tileQuery P j T s = tileQuery P j T s' := by
  unfold tileQuery activeIn usesTrue
  rw [hsite]
  cases hs : s'.2.site with
  | none => simp only; rw [hoc, hatt]
  | some i => simp only; rw [hau i, hatt, hpend, hact, hterm, hpl]

theorem measurable_tileQuery {f : α → RunRecord d m × TileScratch d m} (hf : Measurable f) :
    Measurable fun a => tileQuery P j T (f a) := by
  have hx := RecordMeas.of_measurable hf.fst
  have hs := ScratchMeas.of_measurable hf.snd
  have hoc : Measurable fun a => (f a).2.orderCount (tileOrderIndex j T (f a).2.attempt) :=
    measurable_lookup (F := fun a n => (f a).2.orderCount (tileOrderIndex j T n))
      (measurable_pi_iff.mpr fun n => (measurable_pi_apply _).comp hs.orderCount) hs.attempt
  have hau : Measurable fun a => fun i : Torus d m =>
      (f a).2.auxUsed (tileAuxIndex j T (f a).2.attempt i) :=
    measurable_pi_iff.mpr fun i : Torus d m =>
      measurable_lookup (F := fun a n => (f a).2.auxUsed (tileAuxIndex j T n i))
        (measurable_pi_iff.mpr fun n => (measurable_pi_apply _).comp hs.auxUsed) hs.attempt
  refine measurable_of_factor (hs.site.prodMk (hs.attempt.prodMk (hoc.prodMk (hau.prodMk
    (hx.pending.prodMk (hx.active.prodMk (hx.sites.fst.prodMk hx.prefixLength))))))) _ ?_
  intro a a' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine tileQuery_congr P j T _ _ ?_ h2 h3 (fun i => congrFun h4 i) (finsetCode_injective h5)
    (finsetCode_injective h6) (finsetCode_injective h7) h8
  have := congrArg decodeOption h1
  simpa [decodeOption_code] using this

theorem measurable_exposedSite {f : α → RunRecord d m × TileScratch d m} (hf : Measurable f)
    {v : α → Option ℕ} (hv : Measurable v) :
    Measurable fun a => optionCode (exposedSite P j T (f a) (v a)) := by
  have hx := RecordMeas.of_measurable hf.fst
  have hs := ScratchMeas.of_measurable hf.snd
  have hlive := (hs.seq.stateAt hs.seq.length).live
  refine measurable_of_factor (hv.prodMk (hx.active.prodMk hlive)) _ ?_
  intro a a' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h2' := finsetCode_injective h2
  have h3' := finsetCode_injective h3
  unfold exposedSite
  rw [h1, h2', h3']

theorem measurable_answeredSign (z : AndersonAC.S2.SignIndex (Torus d m)) :
    Measurable fun a : Answer (Torus d m) => answeredSign a z :=
  (measurable_of_countable (fun o : Option Bool => o.getD false)).comp
    ((measurable_pi_apply z).comp measurable_fst)

theorem measurable_tileIncrement (q : Query (Torus d m)) :
    Measurable fun a : Answer (Torus d m) => tileIncrement P j q a := by
  cases q with
  | trueDigit i h =>
    simp only [tileIncrement]
    exact measurable_const.mul ((measurable_of_countable AndersonAC.S2.signValue).comp
      (measurable_answeredSign _))
  | auxiliary k =>
    simp only [tileIncrement]
    exact measurable_const.mul ((measurable_of_countable AndersonAC.S2.signValue).comp
      (measurable_answeredSign _))
  | trueSuffix i h =>
    simp only [tileIncrement]
    exact (AndersonAC.S2.binarySuffix_measurable _ h).comp
      (measurable_pi_iff.mpr fun k => measurable_answeredSign _)
  | nextOrder o => exact measurable_const
  | decision => exact measurable_const

abbrev BlockArg (d m : ℕ) := (RunRecord d m × TileScratch d m) × Answer (Torus d m)

theorem measurable_logged (q0 : Query (Torus d m)) :
    Measurable fun p : BlockArg d m =>
      ((p.1.1, logQuery q0 p.1.2) : RunRecord d m × TileScratch d m) :=
  measurable_fst.fst.prodMk (measurable_logQuery q0 measurable_fst.snd)

theorem measurable_scalarCase (q0 : Query (Torus d m))
    (h : ∀ s a, tileStep P j T s q0 a = match s.2.site with
      | none => s
      | some i => scalarStep P j T s i (tileIncrement P j q0 a)) :
    Measurable fun p : BlockArg d m => tileStep P j T (p.1.1, logQuery q0 p.1.2) q0 p.2 := by
  have hs0 := measurable_logged q0
  have hS := ScratchMeas.of_measurable hs0.snd
  let G : (Torus d m → Bool) → BlockArg d m → RunRecord d m × TileScratch d m := fun c p =>
    match decodeOption c with
    | none => (p.1.1, logQuery q0 p.1.2)
    | some i => scalarStep P j T (p.1.1, logQuery q0 p.1.2) i (tileIncrement P j q0 p.2)
  have he : (fun p : BlockArg d m => tileStep P j T (p.1.1, logQuery q0 p.1.2) q0 p.2) =
      fun p => G (optionCode (logQuery q0 p.1.2).site) p := by
    funext p
    rw [h]
    simp only [G, decodeOption_code]
  rw [he]
  refine measurable_select hS.site fun c => ?_
  simp only [G]
  cases decodeOption c with
  | none => exact hs0
  | some i =>
    exact measurable_scalarStep P j T hs0 i ((measurable_tileIncrement P j q0).comp measurable_snd)

theorem measurable_tileStep (q0 : Query (Torus d m)) :
    Measurable fun p : BlockArg d m => tileStep P j T (p.1.1, logQuery q0 p.1.2) q0 p.2 := by
  have hs0 := measurable_logged q0
  have hS := ScratchMeas.of_measurable hs0.snd
  cases q0 with
  | trueDigit i h => exact measurable_scalarCase P j T _ fun s a => rfl
  | auxiliary k => exact measurable_scalarCase P j T _ fun s a => rfl
  | trueSuffix i h => exact measurable_scalarCase P j T _ fun s a => rfl
  | nextOrder o =>
    simp only [tileStep]
    exact hs0.fst.prodMk (ScratchMeas.measurable ⟨hS.attempt, hS.seq,
      measurable_exposedSite P j T hs0 measurable_snd.snd, hS.added, hS.consumed, hS.halted,
      hS.firstFail, hS.orderCount, hS.auxUsed⟩)
  | decision =>
    have he : (fun p : BlockArg d m =>
        tileStep P j T (p.1.1, logQuery Query.decision p.1.2) Query.decision p.2) =
        fun p => if optionCode (logQuery Query.decision p.1.2).site = optionCode none then
          (commitTrial p.1.1 (logQuery Query.decision p.1.2) (decide (IsFinalSweep m j)),
            { logQuery Query.decision p.1.2 with halted := true })
        else (p.1.1, { logQuery Query.decision p.1.2 with site := none }) := by
      funext p
      simp only [tileStep]
      cases hsite : (logQuery Query.decision p.1.2).site with
      | none => simp
      | some i =>
        have hne : optionCode (some i) ≠ optionCode (none : Option (Torus d m)) := by
          intro hc; have := congrFun hc i; simp [optionCode] at this
        simp [hne]
    rw [he]
    refine Measurable.ite (hS.site (measurableSet_singleton _)) ?_ ?_
    · exact (measurable_commitTrial (decide (IsFinalSweep m j)) hs0).prodMk
        (ScratchMeas.measurable ⟨hS.attempt, hS.seq,
        hS.site, hS.added, hS.consumed, measurable_const' fun _ _ => rfl, hS.firstFail,
        hS.orderCount, hS.auxUsed⟩)
    · exact hs0.fst.prodMk (ScratchMeas.measurable ⟨hS.attempt, hS.seq,
        measurable_const' fun _ _ => rfl, hS.added, hS.consumed, hS.halted, hS.firstFail,
        hS.orderCount, hS.auxUsed⟩)

/-- **Measurability of the tile block** (`Block.IsMeasurable`). -/
theorem tileBlock_measurable : (tileBlock P j T).IsMeasurable where
  enter := by
    have hx := RecordMeas.of_measurable (measurable_id (α := RunRecord d m))
    exact Measurable.ite (hx.aborted (measurableSet_singleton true))
      (measurable_id.prodMk measurable_initScratch_halted)
      (measurable_id.prodMk measurable_initScratch)
  next := by
    have hS := ScratchMeas.of_measurable (measurable_snd (α := RunRecord d m)
      (β := TileScratch d m))
    exact Measurable.ite (hS.halted (measurableSet_singleton true)) measurable_const
      (measurable_tileQuery P j T measurable_id)
  update := by
    have hS := ScratchMeas.of_measurable
      ((measurable_snd.comp measurable_fst) : Measurable fun p : BlockArg d m => p.1.2)
    have hq := measurable_tileQuery P j T (measurable_fst (α := RunRecord d m × TileScratch d m)
      (β := Answer (Torus d m)))
    have he : (fun p : BlockArg d m => (tileBlock P j T).update p.1 p.2) =
        fun p => if p.1.2.halted = true then p.1 else
          (fun q0 (p : BlockArg d m) => tileStep P j T (p.1.1, logQuery q0 p.1.2) q0 p.2)
            (tileQuery P j T p.1) p := rfl
    rw [he]
    exact Measurable.ite (hS.halted (measurableSet_singleton true)) measurable_fst
      (measurable_select hq (measurable_tileStep P j T))
  halted := (ScratchMeas.of_measurable (measurable_snd (α := RunRecord d m)
    (β := TileScratch d m))).halted
  exit := measurable_fst
  firstFail := (ScratchMeas.of_measurable (measurable_snd (α := RunRecord d m)
    (β := TileScratch d m))).firstFail

/-- The fresh pattern is a measurable function of the entering record
(`BlockRun.pattern_measurable`). -/
theorem tilePattern_measurable : Measurable (tilePattern P j T) := by
  have hx := RecordMeas.of_measurable (measurable_id (α := RunRecord d m))
  refine measurable_of_factor
    (hx.aborted.prodMk (hx.active.prodMk
      (hx.sites.fst.prodMk (hx.pending.prodMk hx.prefixLength)))) _ ?_
  intro x x' h
  simp only [Prod.mk.injEq, id] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have h1' := finsetCode_injective h1
  have h2' := finsetCode_injective h2
  have h3' := finsetCode_injective h3
  unfold tilePattern
  rw [h0, h1', h2', h3', h4]

end Final

end AndersonAC.AgentS78
