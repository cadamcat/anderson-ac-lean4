import AndersonAC.AgentS78.Construction.StagePhaseHInv
import AndersonAC.AgentS78Geo.Geo

/-!
# The DONE exit of a clearing attempt. A DONE exit of `clearingBlock n₀ j u y` from a record `x` carrying
clearing-phase data `D` commits one clearing: `ClearingStepFacts D.I exit.endpoint y`
(07-assembly.tex:390–433: §6 DONE output, Lemma 6.1 core completion, Lemma 7.2 clearing
geometry, Lemma locality / Corollary core-decay, Combes–Thomas).

* `ClearRec Ctr n₀ u j x anchor`: the record-level clauses of the clearing phase used by the
  DONE step (snapshot components, terminal/active bookkeeping, and a Lemma 7.2 trace `T` of all
  earlier successful groups whose edits are the terminal set and whose index-`j` anchors include
  the committed anchors of the stage).
* `ClearingDoneStatement d`: **the DONE step facts** (all fields of `ClearingStepFacts`).
* `ClearingDoneAnalyticStatement d`: its analytic part (Combes–Thomas decay of the new endpoint
  and the four distortion bounds `entryChange`, `rowChange`, `totalChange`, `decay`), with the
  structural facts proved here (`physical`, the new terminal metric, the hop structure of the
  committed matrix) as hypotheses.
* `ClearingDoneHopsStatement d`: the Schur support of the committed matrix (mechanical).

Constants: the broad damping `cP ≤ Im r ≤ CP` of the run, the trace constant `Ctr`; then the
assembly constants `CA ≥ CA₀`, `cA ∈ (0, cA₀]`, `PA ≥ PA₀`; the scale radius `Ds` of the stage
lies in `[2 clearRadius, Ctr · clearRadius]` (the hand-over chooses it).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf)
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-- **Record-level clauses of the clearing phase of stage `j`** (entering record `x`, committed
anchors `anchor` of the stage). -/
structure ClearRec (Ctr : ℝ) (n₀ : ℕ) (u : ℝ) (j : ℕ) (x : RunRecord d m) {k : ℕ}
    (anchor : Fin k → Torus d m) : Prop where
  coupled : ∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i + n₀ = j
  activeCompl : x.endpoint.active = Finset.univ \ x.terminal
  pendingActive : x.pending ⊆ x.endpoint.active
  compClass : ∀ C ∈ x.components, C ⊆ x.pending ∨ C ⊆ x.terminal
  compSep : ∀ C ∈ x.components, ∀ C' ∈ x.components, C ≠ C' → ∀ z ∈ C, ∀ w ∈ C',
    separationRadius j < physicalDistance d m z w
  componentDiam : ∀ C ∈ x.components, ∀ y ∈ C, ∀ z ∈ C,
    physicalDistance d m y z ≤ (C.card : ℝ) * separationRadius j
  trace : ∃ l, ∃ T : ClearingGeometry d m n₀ j l u Ctr, ClearingTraceOf x T ∧
    geometryTerminals T = x.terminal ∧ ∀ a, ∃ b, T.index b = j ∧ T.anchor b = anchor a

/-- **Schur support of the committed matrix after a DONE clearing** (sub-statement,
mechanical): the hop structure of `ClearingTraceOf.hops` persists with the new terminal set. -/
def ClearingDoneHopsStatement (d : ℕ) : Prop :=
  ∀ {m : ℕ} (n₀ j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m)
    (J : Matrix (Torus d m) (Torus d m) ℝ),
    (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) →
    IsDampedEndpoint x.endpoint x.r (stageScale u j m) →
    (∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active, x.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
      terminalDistance (nnGraph d m) x.terminal a b = 0) →
    x.endpoint.active = Finset.univ \ x.terminal → x.aborted = false →
    ∀ s : RunRecord d m × ClearScratch d m,
      BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s →
      s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
      ∀ a ∈ (clearingDoneExit x s.2).endpoint.active, ∀ b ∈ (clearingDoneExit x s.2).endpoint.active,
        (clearingDoneExit x s.2).endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
        terminalDistance (nnGraph d m) (clearingDoneExit x s.2).terminal a b = 0

/-- The DONE step facts (07-assembly.tex:390–433). -/
def ClearingDoneStatement (d : ℕ) : Prop :=
  ∀ cP CP : ℝ, 0 < cP → cP ≤ CP → ∀ Ctr : ℝ, 2 ≤ Ctr →
  ∃ CA₀ cA₀ PA₀ : ℝ, 1 ≤ CA₀ ∧ 0 < cA₀ ∧ 0 ≤ PA₀ ∧
  ∀ CA cA PA : ℝ, CA₀ ≤ CA → 0 < cA → cA ≤ cA₀ → PA₀ ≤ PA →
  ∃ N : ℕ, ∃ t₀ : ℝ, 0 < t₀ ∧
  ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (y : Torus d m) (x : RunRecord d m)
    (D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
    N ≤ n₀ → n₀ < j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    stageScale u j m < t₀ →
    2 * clearRadius d m j u ≤ D.I.Ds → D.I.Ds ≤ Ctr * clearRadius d m j u →
    (∀ i, cP ≤ (x.r i).im ∧ ‖x.r i‖ ≤ CP) →
    ClearRec Ctr n₀ u j x D.I.anchor → x.aborted = false →
    ∀ s : RunRecord d m × ClearScratch d m,
      BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s →
      s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
      ClearingStepFacts D.I (clearingDoneExit x s.2).endpoint y

/-- The analytic part of the DONE step facts: Combes–Thomas
decay of the committed endpoint and the distortion/decay bounds of the committed clearing
(07-assembly.tex:390–433), given the structural facts `physical`, the new terminal metric and the
hop structure of the committed matrix (`ClearingTraceOf.hops` for the new terminal set). -/
def ClearingDoneAnalyticStatement (d : ℕ) : Prop :=
  ∀ cP CP : ℝ, 0 < cP → cP ≤ CP → ∀ Ctr : ℝ, 2 ≤ Ctr →
  ∃ CA₀ cA₀ PA₀ : ℝ, 1 ≤ CA₀ ∧ 0 < cA₀ ∧ 0 ≤ PA₀ ∧
  ∀ CA cA PA : ℝ, CA₀ ≤ CA → 0 < cA → cA ≤ cA₀ → PA₀ ≤ PA →
  ∃ N : ℕ, ∃ t₀ : ℝ, 0 < t₀ ∧
  ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (y : Torus d m) (x : RunRecord d m)
    (D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
    N ≤ n₀ → n₀ < j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    stageScale u j m < t₀ →
    2 * clearRadius d m j u ≤ D.I.Ds → D.I.Ds ≤ Ctr * clearRadius d m j u →
    (∀ i, cP ≤ (x.r i).im ∧ ‖x.r i‖ ≤ CP) →
    ClearRec Ctr n₀ u j x D.I.anchor → x.aborted = false →
    ∀ s : RunRecord d m × ClearScratch d m,
      BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s →
      s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
      IsDampedEndpoint (clearingDoneExit x s.2).endpoint x.r (stageScale u j m) →
      (∀ v w, physicalDistance d m v w / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        terminalDistance (nnGraph d m) (Finset.univ \ (clearingDoneExit x s.2).endpoint.active) v w) →
      (∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
        (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
        ∀ a ∈ (clearingDoneExit x s.2).endpoint.active, ∀ b ∈ (clearingDoneExit x s.2).endpoint.active,
          (clearingDoneExit x s.2).endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
          terminalDistance (nnGraph d m) (Finset.univ \ (clearingDoneExit x s.2).endpoint.active) a b = 0) →
      let s' := (clearingDoneExit x s.2).endpoint
      let s₀ := D.I.state (Fin.last D.k)
      let t := stageScale u j m
      (∀ i k, ‖normalizedInverse s' t i k‖ ≤
        CA / Real.sqrt t * Real.exp (-cA * t * max (physicalDistance d m i k / 2 - t ^ (-1.03 : ℝ)) 0)) ∧
      (∀ i k, ‖survivorDifference s₀ s' t i k‖ ≤ CA * Real.sqrt t * t ^ (0.42 * delta)) ∧
      (∀ i, rowTwo (survivorDifference s₀ s' t) i ≤ CA * t ^ (0.25 * delta)) ∧
      frobeniusSq (survivorDifference s₀ s' t) ≤ CA * t ^ (-1 - 0.47 * delta) ∧
      (∀ i k, ‖survivorDifference s₀ s' t i k‖ ≤ t ^ (-PA) * Real.exp (-cA * t *
        (max (distanceTo (physicalDistance d m) (s₀.active \ s'.active) i - CA * t ^ (-1.03 : ℝ)) 0 +
         max (distanceTo (physicalDistance d m) (s₀.active \ s'.active) k - CA * t ^ (-1.03 : ℝ)) 0)))

/-- `ClearingDoneFacts` (the hypothesis of `clearOp_hInv`) from the DONE statement. -/
theorem clearingDoneFacts_of_statement {cP CP Ctr CA cA PA : ℝ} {N : ℕ} {t₀ : ℝ}
    (h : ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (y : Torus d m) (x : RunRecord d m)
      (D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
      N ≤ n₀ → n₀ < j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      stageScale u j m < t₀ →
      2 * clearRadius d m j u ≤ D.I.Ds → D.I.Ds ≤ Ctr * clearRadius d m j u →
      (∀ i, cP ≤ (x.r i).im ∧ ‖x.r i‖ ≤ CP) →
      ClearRec Ctr n₀ u j x D.I.anchor → x.aborted = false →
      ∀ s : RunRecord d m × ClearScratch d m,
        BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s →
        s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
        ClearingStepFacts D.I (clearingDoneExit x s.2).endpoint y)
    {n₀ j : ℕ} {u E : ℝ} {ρ : ℂ} {C : ℝ} (y : Torus d m) (x : RunRecord d m)
    (hN : N ≤ n₀) (hj : n₀ < j) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (ht : stageScale u j m < t₀)
    (hbroad : x.aborted = false → ∀ i, cP ≤ (x.r i).im ∧ ‖x.r i‖ ≤ CP)
    (hrec : x.aborted = false → ∀ D : ClearPhaseData n₀ u E ρ C CA cA PA j x,
      2 * clearRadius d m j u ≤ D.I.Ds ∧ D.I.Ds ≤ Ctr * clearRadius d m j u ∧
      ClearRec Ctr n₀ u j x D.I.anchor) :
    ClearingDoneFacts n₀ u E ρ C CA cA PA j y x := by
  intro D s hs hab hsch hne hf hd
  obtain ⟨h1, h2, h3⟩ := hrec hab D
  exact h n₀ j u E ρ C y x D hN hj hsch hu ht h1 h2 (hbroad hab) h3 hab s hs hne hf hd

end AndersonAC.AgentS78
