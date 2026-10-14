import AndersonAC.AgentS6.Margins

/-! Reduction of Proposition 6.6 (06-clearing.tex:826–850, proof 852–1123) to its three
failure modes. `fail_reason` of `StoppedTrial` says a failing trial stopped at the heat limit,
with a broken distortion budget, or with a leverage above `4 l_*` at the last heat ridge.
Each mode is stated below as a `ModeTail` proposition: it is contained in a measurable event
whose conditional probability given the trial-start history is at most a third of the target.
The propositions are not assumed anywhere; `preparation_of_modes` consumes them explicitly.

The §2 finite Ward identity enters only as the explicit hypothesis `Blueprint.WardInput`
(as for the accepted `S6.range_localization`). -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace AndersonAC.AgentS6

open AndersonAC.S6

variable {Ω : Type*} [MeasurableSpace Ω]

/-! `AndersonAC.S6.onRunning` restricts weights to the running event and sets them to zero
after stopping. `StoppedTrial` constrains only running prestates, so the drift input uses
these restricted weights. Unrestricted integrability can fail because the ridge is
unconstrained after stopping. -/

theorem totalWeight_onRunning {ι : Type*} [Fintype ι] (run : ℕ → Set Ω) (w : ℕ → Ω → ι → ℝ)
    (k : ℕ) : (fun ω => totalWeight (onRunning run w k ω)) =
      (run k).indicator (fun ω => totalWeight (w k ω)) := by
  funext ω; unfold onRunning; by_cases h : ω ∈ run k <;> simp [h, totalWeight]

theorem squareWeight_onRunning {ι : Type*} [Fintype ι] (run : ℕ → Set Ω) (w : ℕ → Ω → ι → ℝ)
    (k : ℕ) : (fun ω => squareWeight (onRunning run w k ω)) =
      (run k).indicator (fun ω => squareWeight (w k ω)) := by
  funext ω; unfold onRunning; by_cases h : ω ∈ run k <;> simp [h, squareWeight]

/-- The unrestricted drift input implies the restricted one. -/
theorem drift_onRunning {ι : Type*} [Fintype ι] (μ : Measure Ω)
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (ε : ℝ) (run : ℕ → Set Ω)
    (pre post : ℕ → Ω → ι → ℝ) (hrun : ∀ k, MeasurableSet[F k] (run k))
    (h : LeverageDriftInput μ F ε run pre post) :
    LeverageDriftInput μ F ε run (onRunning run pre) (onRunning run post) := by
  have hm : ∀ k, MeasurableSet (run k) := fun k => F.le k _ (hrun k)
  have hsubA : ∀ k, (fun ω => totalWeight (onRunning run post k ω) -
      totalWeight (onRunning run pre k ω)) =
      (run k).indicator (fun ω => totalWeight (post k ω) - totalWeight (pre k ω)) := by
    intro k; funext ω; unfold onRunning; by_cases hω : ω ∈ run k <;> simp [hω, totalWeight]
  have hsubP : ∀ k, (fun ω => squareWeight (onRunning run post k ω) -
      squareWeight (onRunning run pre k ω)) =
      (run k).indicator (fun ω => squareWeight (post k ω) - squareWeight (pre k ω)) := by
    intro k; funext ω; unfold onRunning; by_cases hω : ω ∈ run k <;> simp [hω, squareWeight]
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [totalWeight_onRunning]; exact (h.integrable_preA k).indicator (hm k)
  · rw [totalWeight_onRunning]; exact (h.integrable_postA k).indicator (hm k)
  · rw [squareWeight_onRunning]; exact (h.integrable_preP k).indicator (hm k)
  · rw [squareWeight_onRunning]; exact (h.integrable_postP k).indicator (hm k)
  · rw [hsubA]
    have hi : Integrable (fun ω => totalWeight (post k ω) - totalWeight (pre k ω)) μ :=
      (h.integrable_postA k).sub (h.integrable_preA k)
    filter_upwards [condExp_indicator hi (hrun k), h.total_drift k] with ω h1 h2 hω
    rw [h1, Set.indicator_of_mem hω]
    have : onRunning run pre k ω = pre k ω := by simp [onRunning, hω]
    rw [this]; exact h2 hω
  · rw [hsubP]
    have hi : Integrable (fun ω => squareWeight (post k ω) - squareWeight (pre k ω)) μ :=
      (h.integrable_postP k).sub (h.integrable_preP k)
    filter_upwards [condExp_indicator hi (hrun k), h.square_drift k] with ω h1 h2 hω
    rw [h1, Set.indicator_of_mem hω]
    have : onRunning run pre k ω = pre k ω := by simp [onRunning, hω]
    rw [this]; exact h2 hω

/-- All hypotheses of `Planned.preparation_of_small_component` at one scale `t`. -/
structure PrepHyp (d : ℕ) (c K Cloc cConc : ℝ) (μ : Measure Ω) (qlag ε : ℝ → ℝ)
    {n : ℕ} (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
    (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
    (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ) : Prop where
  t_pos : 0 < t
  core_one : 1 ≤ core.card
  core_cap : (core.card : ℝ) ≤ coreCap d t
  broad : ∀ ω, BroadBounds c K (r ω)
  start_fourth : ∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t
  start_lag : ∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW
  local_input : TrialLocalInput q μ d c K Cloc dist collapsed ell
  concentration : VectorConcentrationInput μ q.history cConc
  drift : LeverageDriftInput μ q.history (ε t) (fun k => {ω | k < q.stop ω})
    (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω)))
    (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω)))

/-- A failure mode: a predicate on a trial and an outcome point. -/
abbrev TrialMode (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  (n : ℕ) → (core : Finset (Fin n)) → (t : ℝ) → (r : Ω → Fin n → ℂ) →
    (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) → (order : Fin n ≃ Fin (Fintype.card (Fin n))) →
    StoppedTrial (Ω := Ω) core t r g0 order → Ω → Prop

/-- Stopped at the heat limit `n_h` (Lemma 6.5, 06-clearing.tex:742–747, 1112–1115). -/
def countMode : TrialMode Ω := fun _ _ t _ _ _ q ω => q.stop ω = heatLimit t

/-- A distortion budget fails at the stop (06-clearing.tex:788–800, 852–960, 1060–1110). -/
def budgetMode : TrialMode Ω := fun _ _ t _ g0 _ q ω =>
  ¬ BudgetsHold t (g0 ω) (q.state (q.stop ω) ω).hatG

/-- A leverage exceeds `4 l_*` at the ridge of the last heat
(06-clearing.tex:962–1056, 1060–1110). -/
def capMode : TrialMode Ω := fun _ _ t r _ _ q ω =>
  4 * leverageScale t < maxWeight
    (trialWeights t (r ω) (q.state (q.stop ω) ω) (q.ridge (q.stop ω - 1) ω))

/-- Failure-mode tail: for all sufficiently small `t`, uniformly in the torus,
component and trial, the mode lies in a measurable event of conditional probability
at most `exp(-t^{-κ_d})/3` given the trial-start history. -/
def ModeTail (d : ℕ) (c K Cloc cConc : ℝ) (μ : Measure Ω) (qlag ε : ℝ → ℝ)
    (mode : TrialMode Ω) : Prop :=
  AndersonAC.Blueprint.WardInput →
  ∃ t0 : ℝ, 0 < t0 ∧
    ∀ (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
    t < t0 → PrepHyp d c K Cloc cConc μ qlag ε core t r g0 order q dist collapsed ell →
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ ω, mode n core t r g0 order q ω → ω ∈ G) ∧
      ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) G ω ≤
        (1 / 3) * Real.exp (-t ^ (-clearingExponent d))

theorem clearingExponent_pos (d : ℕ) (hd : 3 ≤ d) : 0 < clearingExponent d := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := AndersonAC.S6.parameter_margins d hd
  unfold clearingExponent
  linarith

/-- Conditional probability is subadditive along a measurable three-set cover. -/
theorem condProb_le_three (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (k : ℕ) {A G1 G2 G3 : Set Ω} (hG1 : MeasurableSet G1) (hG2 : MeasurableSet G2)
    (hG3 : MeasurableSet G3) (hA : MeasurableSet A) (hcover : A ⊆ G1 ∪ G2 ∪ G3) :
    ∀ᵐ ω ∂μ, conditionalProbability μ (F k) A ω ≤
      conditionalProbability μ (F k) G1 ω + conditionalProbability μ (F k) G2 ω +
        conditionalProbability μ (F k) G3 ω := by
  unfold conditionalProbability
  have hi : ∀ {S : Set Ω}, MeasurableSet S → Integrable (S.indicator (fun _ => (1 : ℝ))) μ :=
    fun hS => (integrable_const (1 : ℝ)).indicator hS
  have hle : A.indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ]
      G1.indicator (fun _ => (1 : ℝ)) + G2.indicator (fun _ => (1 : ℝ)) +
        G3.indicator (fun _ => (1 : ℝ)) := by
    refine Eventually.of_forall fun ω => ?_
    simp only [Pi.add_apply]
    by_cases hω : ω ∈ A
    · have hω' := hcover hω
      rw [Set.indicator_of_mem hω]
      rcases hω' with (h | h) | h
      · rw [Set.indicator_of_mem h]
        have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G2) (f := fun _ => (1 : ℝ)) ω
        have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G3) (f := fun _ => (1 : ℝ)) ω
        linarith
      · rw [Set.indicator_of_mem h]
        have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G1) (f := fun _ => (1 : ℝ)) ω
        have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G3) (f := fun _ => (1 : ℝ)) ω
        linarith
      · rw [Set.indicator_of_mem h]
        have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G1) (f := fun _ => (1 : ℝ)) ω
        have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G2) (f := fun _ => (1 : ℝ)) ω
        linarith
    · rw [Set.indicator_of_notMem hω]
      have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G1) (f := fun _ => (1 : ℝ)) ω
      have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G2) (f := fun _ => (1 : ℝ)) ω
      have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := G3) (f := fun _ => (1 : ℝ)) ω
      linarith
  have hmono := condExp_mono (m := F k) (hi hA) (((hi hG1).add (hi hG2)).add (hi hG3)) hle
  have hadd1 := condExp_add ((hi hG1).add (hi hG2)) (hi hG3) (F k)
  have hadd2 := condExp_add (hi hG1) (hi hG2) (F k)
  filter_upwards [hmono, hadd1, hadd2] with ω h1 h2 h3
  rw [h2, Pi.add_apply, h3, Pi.add_apply] at h1
  exact h1

theorem running_measurableSet {n : ℕ} {core : Finset (Fin n)} {t : ℝ} {r : Ω → Fin n → ℂ}
    {g0 : Ω → Matrix (Fin n) (Fin n) ℂ} {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    MeasurableSet[q.history k] {ω | k < q.stop ω} := by
  have h := (q.stopping k).compl
  convert h using 1
  ext ω; simp

/-- Every heat erases one distinct active site: the number of removed sites is the stop. -/
theorem removed_card {n : ℕ} {core : Finset (Fin n)} {t : ℝ} {r : Ω → Fin n → ℂ}
    {g0 : Ω → Matrix (Fin n) (Fin n) ℂ} {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) :
    ((q.state 0 ω).active \ (q.state (q.stop ω) ω).active).card = q.stop ω := by
  have key : ∀ k, k ≤ q.stop ω → (q.state k ω).active.card + k = n := by
    intro k
    induction k with
    | zero => intro _; rw [q.initial_active ω]; simp
    | succ k ih =>
      intro hk
      have hk' : k < q.stop ω := hk
      obtain ⟨hx, -, hact, -⟩ := q.heat k ω hk'
      rw [hact, Finset.card_erase_of_mem hx]
      have h1 := ih hk'.le
      have h2 : 1 ≤ (q.state k ω).active.card := Finset.card_pos.mpr ⟨_, hx⟩
      omega
  have h := key (q.stop ω) le_rfl
  rw [q.initial_active ω, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

end AndersonAC.AgentS6

namespace AndersonAC.S6

open AndersonAC.AgentS6

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Proposition 6.6 from its three failure-mode tails and the §2 Ward input. -/
theorem preparation_of_modes (hWard : AndersonAC.Blueprint.WardInput)
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t)
    (hcount : ModeTail d c K Cloc cConc μ qlag ε countMode)
    (hbudget : ModeTail d c K Cloc cConc μ qlag ε budgetMode)
    (hcap : ModeTail d c K Cloc cConc μ qlag ε capMode) :
    Planned.preparation_of_small_component d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε
      hqlag hε hεpos := by
  obtain ⟨t1, ht1, h1⟩ := hcount hWard
  obtain ⟨t2, ht2, h2⟩ := hbudget hWard
  obtain ⟨t3, ht3, h3⟩ := hcap hWard
  refine ⟨clearingExponent_pos d hd, min t1 (min t2 t3), lt_min ht1 (lt_min ht2 ht3), ?_⟩
  intro n core t r g0 order q dist collapsed ell ht htt hcore1 hcore hb hfourth hlag hloc hconc
    hdrift
  have hyp : PrepHyp d c K Cloc cConc μ qlag ε core t r g0 order q dist collapsed ell :=
    ⟨ht, hcore1, hcore, hb, hfourth, hlag, hloc, hconc,
      hdrift⟩
  have htt1 : t < t1 := lt_of_lt_of_le htt (min_le_left _ _)
  have htt2 : t < t2 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt3 : t < t3 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨G1, hG1, hm1, hp1⟩ := h1 n core t r g0 order q dist collapsed ell htt1 hyp
  obtain ⟨G2, hG2, hm2, hp2⟩ := h2 n core t r g0 order q dist collapsed ell htt2 hyp
  obtain ⟨G3, hG3, hm3, hp3⟩ := h3 n core t r g0 order q dist collapsed ell htt3 hyp
  refine ⟨?_, ?_⟩
  · have hA : MeasurableSet {ω | q.outcome ω = .fail} :=
      q.outcome_measurable (MeasurableSpace.measurableSet_top (s := {TrialOutcome.fail}))
    have hcover : {ω | q.outcome ω = .fail} ⊆ G1 ∪ G2 ∪ G3 := by
      intro ω hω
      rcases q.fail_reason ω hω with h | h | h
      · exact Or.inl (Or.inl (hm1 ω h))
      · exact Or.inl (Or.inr (hm2 ω h))
      · exact Or.inr (hm3 ω h)
    filter_upwards [condProb_le_three μ q.history 0 hG1 hG2 hG3 hA hcover, hp1, hp2, hp3]
      with ω h h1 h2 h3
    linarith
  · intro ω hdone
    obtain ⟨hs, hbud, hproj⟩ := (q.done_iff ω).mp hdone
    exact ⟨hs, hbud, hproj, removed_card q ω⟩

end AndersonAC.S6

#print axioms AndersonAC.AgentS6.condProb_le_three
#print axioms AndersonAC.AgentS6.removed_card
#print axioms AndersonAC.S6.preparation_of_modes
